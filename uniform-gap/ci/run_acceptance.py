#!/usr/bin/env python3
"""Operator-side CI runner. A prepared workflow is not an executed acceptance.

Candidate Lean compilation/export runs only in real Landrun sandboxes, under
an unprivileged systemd user unit that disallows AF_UNIX sockets.
"""
from pathlib import Path
import argparse,base64,ctypes,datetime,hashlib,io,json,os,platform,re,shutil
import signal,subprocess,sys,tarfile,time,zipfile,importlib.util
_control_spec=importlib.util.spec_from_file_location("lrc_reviewed_controls",Path(__file__).resolve().parent/"controls.py")
_control_module=importlib.util.module_from_spec(_control_spec);_control_spec.loader.exec_module(_control_module)
TARGETS=_control_module.TARGETS;NEGATIVES=_control_module.NEGATIVES
classify=_control_module.classify;negative_source=_control_module.negative_source

SOURCE_FP="befdb0a4d53dd27f1a62e01f7e9c6ad5be3ae91569fde001bd3cca2040cb4c78"
TRUST_ZIP_SHA="50e0a83e99154095e4cb42d0a43df9076a40dee3cc735a608ab8fc46e060f7b1"
TRUST_MANIFEST_SHA="58caccd663f20dc987be5b769f4fd348aeb2f81f28b2b1058645a5b923df91c7"
LEAN_COMMIT="5045d0056413266e57c625dcd7c365b10e377c52"
LEAN_SHA="47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4"
PINS={"comparator":("https://github.com/leanprover/comparator.git","d03acab154d269c06e60e4de7e4cc85deebff94b"),
      "exporter":("https://github.com/leanprover/lean4export.git","076e8e57707e813375e8f9da8bf989799ace9680"),
      "nanoda":("https://github.com/ammkrn/nanoda_lib.git","8de7e0c4ed3052745a7f8725164efd9e76d84c56"),
      "landrun":("https://github.com/Zouuup/landrun.git","ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a")}
RUST={"rustc":"2ff05ff9c08a90861e7f6e4065b40a8b87463b4576186fd613871c3e37f2091f",
      "cargo":"53f3521949404d595efb06a55c12c5658d4ed1c75566f33d3d514eaebe70bd8a",
      "rust-std":"109b074225bf5b9ea3820890876bfdf4ed161adbfaf94b2b4b5984c85ee5d958"}

class Blocked(RuntimeError):pass
class Failed(RuntimeError):pass
def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as f:
        for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
    return h.hexdigest()
def write_json(path,data):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_name(path.name+".new");tmp.write_text(json.dumps(data,indent=2)+"\n")
    os.replace(tmp,path)
def trusted_files(assets):
    data=base64.b64decode((Path(assets)/"trusted-inputs.zip.b64").read_bytes())
    if sha(data)!=TRUST_ZIP_SHA:raise Failed("Trusted archive checksum mismatch")
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        raw=z.read("frozen-v1.sha256.json")
        if sha(raw)!=TRUST_MANIFEST_SHA:raise Failed("Independent frozen manifest checksum mismatch")
        hashes=json.loads(raw)
        if len(hashes)!=16:raise Failed("Expected exactly 16 frozen inputs")
        result={}
        for name,expected in hashes.items():
            if Path(name).is_absolute() or ".." in Path(name).parts:raise Failed("Invalid frozen path")
            b=z.read("trusted/"+name)
            if sha(b)!=expected:raise Failed("Trusted input mismatch: "+name)
            result[name]=b
    return result,hashes
def resource_config(base,acceptance=False):
    needle=b'version = "0.1.0"'
    if base.count(needle)!=1:raise Failed("Unexpected frozen project configuration")
    addition=b'\nweakLeanArgs = ["-j1", "-M6144", "-DElab.async=false"]'
    data=base.replace(needle,needle+addition,1)
    if acceptance:data+=b'\n[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Solution"\n\n[[lean_lib]]\nname = "AllSource"\n'
    return data
def check_final_axioms(output,targets):
    checked={}
    for target in targets:
        found=re.search("'"+re.escape(target)+r"' depends on axioms:\s*\[([^\]]*)\]",output)
        if not found:raise Failed("Missing final axiom output: "+target)
        names={re.sub(r"\.\{[^}]*\}","",a.strip()) for a in found[1].split(",") if a.strip()}
        if not names<={"propext","Classical.choice","Quot.sound"}:
            raise Failed("Unpermitted final axiom: "+target+" "+repr(sorted(names)))
        checked[target]=sorted(names)
    return checked
def inspect_source(project,frozen_hashes):
    project=Path(project)
    manifest=json.loads((project/"candidate-source-version.json").read_text())
    actual=sha(json.dumps(manifest["source_files"],sort_keys=True,separators=(",",":")).encode())
    if actual!=SOURCE_FP or manifest["source_version_sha256"]!=SOURCE_FP:
        raise Failed("Unreviewed candidate source fingerprint")
    if len(manifest["source_files"])!=263 or manifest["frozen_files"]!=frozen_hashes:
        raise Failed("Candidate or frozen manifest changed")
    combined=manifest["source_files"]|frozen_hashes
    for name,expected in combined.items():
        path=project/name
        if Path(name).is_absolute() or ".." in Path(name).parts or path.is_symlink():
            raise Failed("Invalid candidate input path: "+name)
        if file_sha(path)!=expected:raise Failed("Candidate bytes changed: "+name)
    return manifest

class Context:
    def __init__(self,project,work,assets):
        self.project=Path(project).resolve();self.work=Path(work).resolve();self.assets=Path(assets).resolve()
        self.logs=self.work/"logs";self.logs.mkdir(parents=True,exist_ok=True)
        self.state_path=self.work/"STATE.json"
        self.state=json.loads(self.state_path.read_text()) if self.state_path.exists() else {
            "schema":1,"source_version_sha256":SOURCE_FP,"positive_targets":{t:"NOT_RUN" for t in TARGETS},
            "negatives":{k:{"status":"NOT_RUN"} for k in NEGATIVES},
            "fresh":{"status":"NOT_RUN"},"source_build":{"status":"NOT_RUN"},"final_types":{"status":"NOT_RUN"},
            "final_acceptance_completed":False,"independent_human_review":"NOT_COMPLETED","commands":[]}
        self.env=os.environ.copy();self.env["LEAN_NUM_THREADS"]="1"
        self.prefix=self.work/"tools/lean-4.34.1-linux"
        self.toolsrc=self.work/"tools/src"
        self.deps=self.work/"trusted-dependencies"
        self.env["PATH"]=str(self.work/"tools/launch")+os.pathsep+str(self.prefix/"bin")+os.pathsep+self.env["PATH"]
        uid=os.getuid()
        self.env["XDG_RUNTIME_DIR"]="/run/user/"+str(uid)
        self.env["DBUS_SESSION_BUS_ADDRESS"]="unix:path=/run/user/"+str(uid)+"/bus"
        self.frozen,self.frozen_hashes=trusted_files(self.assets)
    def save(self):
        self.state["updated_utc"]=datetime.datetime.now(datetime.timezone.utc).isoformat()
        write_json(self.state_path,self.state)
        write_json(self.logs/"CURRENT_STATUS.json",self.state)
    def run(self,label,cmd,cwd=None,timeout=9000,check=True,env=None):
        index=len(self.state["commands"]);name=f"{index:03d}-{label}"
        log=self.logs/(name+".log");receipt=self.logs/(name+".json")
        result={"label":label,"command":list(map(str,cmd)),"cwd":str(cwd or self.work),
                "status":"RUNNING","start_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "log":log.name}
        self.state["commands"].append(result);self.save();write_json(receipt,result)
        start=time.monotonic();term=None
        with log.open("wb") as out:
            p=subprocess.Popen(result["command"],cwd=cwd or self.work,env=env or self.env,
                               stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                term="TIME_LIMIT";os.killpg(p.pid,signal.SIGTERM)
                try:p.wait(timeout=10)
                except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
                code=p.returncode
        result.update(exit_code=code,elapsed_seconds=time.monotonic()-start,
                      status=term or ("PASS" if code==0 else "FAILED"),
                      log_sha256=file_sha(log),termination=term)
        write_json(receipt,result);self.save()
        if check and (code!=0 or term):raise Failed(label+" failed; see "+log.name)
        return result,log.read_text(errors="replace")
    def verify(self):
        manifest=inspect_source(self.project,self.frozen_hashes)
        snapshot=self.work/"source-snapshot"
        if snapshot.exists():raise Failed("Use a new work directory for a new source snapshot")
        for name,expected in (manifest["source_files"]|self.frozen_hashes).items():
            path=snapshot/name;path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes((self.project/name).read_bytes())
        write_json(snapshot/"candidate-source-version.json",manifest)
        trusted=self.work/"trusted-reference"
        for name,data in self.frozen.items():
            path=trusted/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
        self.state["source_check"]={"status":"PASS","source_inputs":263,"frozen_files":16,
                                    "math_lean_modules":sum(n.endswith(".lean") for n in manifest["source_files"]|self.frozen_hashes)}
        self.save()
    def require(self,key):
        if self.state.get(key,{}).get("status")!="PASS":raise Blocked("Prerequisite incomplete: "+key)
    def probe(self,initialize):
        self.require("source_check")
        data={"uid":os.getuid(),"platform":platform.platform(),"machine":platform.machine(),
              "free_disk_bytes":shutil.disk_usage(self.work).free}
        libc=ctypes.CDLL(None,use_errno=True);ret=libc.syscall(444,0,0,1)
        data["landlock_abi"]=ret;data["landlock_errno"]=ctypes.get_errno()
        data["mem_total_kib"]=int(re.search(r"(?m)^MemTotal:\s+(\d+)",Path("/proc/meminfo").read_text())[1])
        write_json(self.logs/"HOST_PROBE.json",data)
        if data["uid"]==0:raise Blocked("Official Comparator must run as an unprivileged user")
        if data["machine"] not in {"x86_64","amd64"}:raise Blocked("This pinned toolchain targets x86-64 Linux")
        if ret<6:raise Blocked("Landlock ABI >=6 unavailable")
        if data["free_disk_bytes"]<12*1024**3:raise Blocked("Less than 12 GiB of free disk")
        if data["mem_total_kib"]<12*1024**2:raise Blocked("Less than 12 GiB RAM")
        if os.environ.get("LD_PRELOAD"):raise Blocked("CI does not accept a runtime preload adapter")
        if initialize:
            if os.environ.get("GITHUB_ACTIONS")!="true":raise Blocked("User-manager setup is limited to the ephemeral CI VM")
            uid=str(os.getuid())
            self.run("user-manager",["sudo","systemctl","start","user-runtime-dir@"+uid+".service","user@"+uid+".service"],timeout=120)
        result,_=self.run("systemd-user",["systemd-run","--user","--wait","--pipe","--quiet","true"],timeout=120,check=False)
        if result["exit_code"]:raise Blocked("systemd user session unavailable")
        self.state["host_probe"]={"status":"PASS",**data};self.save()
    def download(self,name,url,expected):
        dest=self.work/"tools/downloads"/name;dest.parent.mkdir(parents=True,exist_ok=True)
        self.run("download-"+name,["curl","--fail","--location","--retry","3","--max-time","900","--output",str(dest),url])
        if file_sha(dest)!=expected:raise Failed("Downloaded checksum mismatch: "+name)
        return dest
    def setup_lean(self):
        archive=self.download("lean-4.34.1-linux.tar.zst",
            "https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst",LEAN_SHA)
        self.run("extract-lean",["tar","--no-same-owner","--zstd","-xf",str(archive),"-C",str(self.work/"tools")])
        launch=self.work/"tools/launch";launch.mkdir(exist_ok=True)
        code='#include <stdlib.h>\n#include <unistd.h>\n#include <stdio.h>\nint main(int n,char **v){(void)n;if(setenv("LEAN_NUM_THREADS","1",1))return 125;execv('+json.dumps(str(self.prefix/"bin/lake"))+',v);perror("lake resource launcher");return 126;}\n'
        (launch/"lake_resource.c").write_text(code)
        self.run("build-lake-resource-launcher",["cc","-O2","-Wall","-Wextra",str(launch/"lake_resource.c"),"-o",str(launch/"lake")])
        self.run("lean-version",[str(self.prefix/"bin/lean"),"--version"])
        write_json(self.logs/"TOOLCHAIN_HASHES.json",{
            "release_sha256":LEAN_SHA,"lean_binary_sha256":file_sha(self.prefix/"bin/lean"),
            "official_lake_binary_sha256":file_sha(self.prefix/"bin/lake"),
            "lake_resource_launcher_sha256":file_sha(launch/"lake"),
            "launcher_source":code,"scope":"Sets LEAN_NUM_THREADS=1 and execs the unchanged official Lake binary; no proof or isolation replacement."})
    def clone(self,name):
        url,commit=PINS[name];dest=self.toolsrc/name;dest.parent.mkdir(parents=True,exist_ok=True)
        self.run("clone-"+name,["git","clone","--filter=blob:none","--no-checkout",url,str(dest)])
        self.run("checkout-"+name,["git","checkout","--detach",commit],cwd=dest)
        head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=dest,text=True).strip()
        if head!=commit:raise Failed("Tool commit mismatch: "+name)
        return dest
    def setup(self):
        self.require("host_probe")
        self.setup_lean()
        for name in ["lakefile.toml","lake-manifest.json","lean-toolchain"]:
            p=self.deps/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(self.frozen[name])
        (self.deps/"lakefile.toml").write_bytes(resource_config(self.frozen["lakefile.toml"]))
        imports=set()
        for p in (self.work/"source-snapshot").rglob("*.lean"):
            for line in p.read_text().splitlines():
                if line.startswith("import "):
                    imports.update(x for x in line.split()[1:] if x.startswith("Mathlib."))
        if not imports or any(not re.fullmatch(r"[A-Za-z0-9_.]+",x) for x in imports):
            raise Failed("Invalid external cache module list")
        self.run("external-cache",["lake","exe","cache","get",*sorted(imports)],cwd=self.deps)
        mathlib=self.deps/".lake/packages/mathlib"
        actual=subprocess.check_output(["git","rev-parse","HEAD"],cwd=mathlib,text=True).strip()
        if actual!="d13f23b723b8a846827a245b89c10fc7d3f11612":raise Failed("Mathlib commit changed")
        self.toolsrc.mkdir(parents=True,exist_ok=True)
        for name in PINS:self.clone(name)
        comp=self.toolsrc/"comparator";pkg=comp/".lake/packages";pkg.mkdir(parents=True,exist_ok=True)
        (pkg/"lean4export").symlink_to(self.toolsrc/"exporter",target_is_directory=True)
        config=(comp/"lakefile.toml").read_bytes().replace(b'version = "0.1.0"',b'version = "0.1.0"\nweakLeanArgs = ["-j1", "-M6144", "-DElab.async=false"]',1)
        (comp/"lakefile.resource.toml").write_bytes(config)
        self.run("build-comparator",["lake","-f","lakefile.resource.toml","build","comparator","lean4export"],cwd=comp)
        goenv=self.env.copy();goenv["GOTOOLCHAIN"]="local"
        goenv["GOMODCACHE"]=str(self.work/"tools/go-modules")
        self.run("go-version",["go","version"],env=goenv)
        self.run("build-landrun",["go","build","-trimpath","-o",str(self.work/"tools/landrun"),"."],cwd=self.toolsrc/"landrun",env=goenv)
        ruststage=self.work/"tools/rust-components";ruststage.mkdir(exist_ok=True)
        rustprefix=self.work/"tools/rust-local";rustprefix.mkdir(exist_ok=True)
        for name,h in RUST.items():
            filename=name+"-1.99.1-x86_64-unknown-linux-gnu.tar.xz"
            archive=self.download(filename,"https://static.rust-lang.org/dist/2026-10-15/"+filename,h)
            self.run("extract-"+name,["tar","--no-same-owner","-xJf",str(archive),"-C",str(ruststage)])
            sub=ruststage/filename.removesuffix(".tar.xz")/("rust-std-x86_64-unknown-linux-gnu" if name=="rust-std" else name)
            shutil.copytree(sub,rustprefix,dirs_exist_ok=True)
        renv=self.env.copy();renv["PATH"]=str(rustprefix/"bin")+os.pathsep+renv["PATH"];renv["CARGO_HOME"]=str(self.work/"tools/cargo-home")
        self.run("rust-version",[str(rustprefix/"bin/rustc"),"--version"],env=renv)
        self.run("build-nanoda",["cargo","build","--release","--locked","--bin","nanoda_bin","--jobs","1"],cwd=self.toolsrc/"nanoda",env=renv)
        pins={}
        for name,(_,commit) in PINS.items():
            dirty=subprocess.check_output(["git","diff","--name-only","HEAD"],cwd=self.toolsrc/name,text=True).strip()
            if dirty:raise Failed("Tracked tool source changed: "+name)
            pins[name]=commit
        self.state["tool_setup"]={"status":"PASS","pins":pins,"mathlib":actual,"cache_modules":len(imports)}
        self.save()
        self.isolation_probe()
    def lean_path(self,case=None,extra=None):
        paths=[]
        if extra:paths.append(Path(extra))
        if case:paths.append(Path(case)/".lake/build/lib/lean")
        packages=self.deps/".lake/packages"
        if packages.exists():
            paths.extend(p/".lake/build/lib/lean" for p in sorted(packages.iterdir()) if p.is_dir())
        paths.append(self.prefix/"lib/lean")
        return os.pathsep.join(str(p) for p in paths)
    def unit(self,cmd,cwd,lean_path=""):
        variables={"PATH":self.env["PATH"],"LEAN_PATH":lean_path,"LEAN_NUM_THREADS":"1",
          "COMPARATOR_LANDRUN":str(self.work/"tools/landrun"),
          "COMPARATOR_LEAN4EXPORT":str(self.toolsrc/"comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"),
          "COMPARATOR_NANODA":str(self.toolsrc/"nanoda/target/release/nanoda_bin")}
        args=["systemd-run","--user","--wait","--pipe","--quiet",
              "--property=RestrictAddressFamilies=~AF_UNIX","--working-directory="+str(cwd)]
        for k,v in variables.items():args.append("--setenv="+k+"="+v)
        return args+["--",*map(str,cmd)]
    def sandbox(self,cmd,cwd,writable=(),lean_path=""):
        args=[str(self.work/"tools/landrun"),"--best-effort","--ro","/","--rw","/dev","-ldd","-add-exec"]
        for k in ["PATH","HOME","LEAN_PATH","LEAN_NUM_THREADS"]:args+=["--env",k]
        for p in writable:args+=["--rwx",str(p)]
        args+=["--rox",str(self.prefix),"--rox",str(self.work/"tools/launch"),"--",*map(str,cmd)]
        return self.unit(args,cwd,lean_path)
    def isolation_probe(self):
        self.require("tool_setup")
        area=self.work/"isolation-probe";area.mkdir(exist_ok=True)
        protected=area/"protected.txt";protected.write_text("trusted-reference\n")
        writable=area/"writable";writable.mkdir(exist_ok=True)
        python=shutil.which("python3")
        if not python:raise Blocked("python3 unavailable")
        deny="import pathlib,sys\np=pathlib.Path("+repr(str(protected))+")\ntry:p.write_text('BAD')\nexcept PermissionError:sys.exit(0)\nsys.exit(42)\n"
        self.run("landrun-write-denial",self.sandbox([python,"-c",deny],area,[writable]),timeout=120)
        if protected.read_text()!="trusted-reference\n":raise Failed("Sandbox changed protected reference")
        import socket
        with socket.socket(socket.AF_UNIX):pass
        af="import socket,sys,errno\ntry:s=socket.socket(socket.AF_UNIX)\nexcept OSError as e:sys.exit(0 if e.errno in {errno.EAFNOSUPPORT,errno.EPERM,errno.EACCES} else 43)\ns.close();sys.exit(42)\n"
        self.run("af-unix-denial",self.unit([python,"-c",af],area),timeout=120)
        self.state["isolation_probe"]={"status":"PASS","protected_write_denied":True,"af_unix_denied":True};self.save()
    def case(self,kind):
        case=self.work/"cases"/kind
        if case.exists():raise Failed("Refusing to reuse a prior Comparator project: "+kind)
        case.mkdir(parents=True)
        if kind=="positive":
            snapshot=self.work/"source-snapshot"
            for p in snapshot.rglob("*.lean"):
                dest=case/p.relative_to(snapshot);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
            modules=sorted(".".join(p.relative_to(snapshot).with_suffix("").parts)
                           for p in snapshot.rglob("*.lean"))
            if len(modules)!=261:raise Failed("Unexpected source module inventory")
            (case/"AllSource.lean").write_text("".join("import "+m+"\n" for m in modules))
            solution=self.frozen["validation/comparator/Solution.lean.in"]
        else:
            solution=negative_source(kind,self.frozen["validation/comparator/Challenge.lean.in"].decode()).encode()
        (case/"Challenge.lean").write_bytes(self.frozen["validation/comparator/Challenge.lean.in"])
        (case/"Solution.lean").write_bytes(solution)
        runtime=resource_config(self.frozen["lakefile.toml"],acceptance=True)
        (case/"lakefile.toml").write_bytes(runtime)
        for name in ["lake-manifest.json","lean-toolchain"]:(case/name).write_bytes(self.frozen[name])
        dot=case/".lake";dot.mkdir()
        (dot/"packages").symlink_to(self.deps/".lake/packages",target_is_directory=True)
        config=json.loads(self.frozen["validation/comparator/config.json"])
        if config["theorem_names"]!=TARGETS or config["permitted_axioms"]!=["propext","Classical.choice","Quot.sound"] or config["definition_names"]!=[]:
            raise Failed("Unexpected frozen comparison policy")
        config["enable_nanoda"]=True
        write_json(case/"config.json",config)
        write_json(self.logs/("case-"+kind+"-inputs.json"),{
          "challenge_sha256":file_sha(case/"Challenge.lean"),
          "solution_sha256":file_sha(case/"Solution.lean"),
          "runtime_config_sha256":file_sha(case/"lakefile.toml"),
          "runtime_config_derivation":"Frozen root TOML plus resource arguments and Challenge/Solution/AllSource libraries, only in execution tree",
          "comparison_policy_derivation":"Frozen config plus enable_nanoda=true; theorem names, definitions and permitted axioms unchanged",
          "source_math_bytes_unchanged":kind=="positive"})
        return case
    def compare(self,kind):
        self.require("isolation_probe")
        if kind!="positive" and any(v!="PASS" for v in self.state["positive_targets"].values()):
            raise Blocked("Positive targets must pass before negative controls")
        case=self.case(kind)
        comparator=self.toolsrc/"comparator/.lake/build/bin/comparator"
        result,text=self.run("comparator-"+kind,self.unit([comparator,case/"config.json"],case,self.lean_path(case)),cwd=case,timeout=10800,check=False)
        outcome=classify(kind,result["exit_code"],text,result["termination"])
        outcome["command_receipt"]=self.state["commands"][-1]
        if kind=="positive":
            self.state["positive"]=outcome
            self.state["positive_targets"]={t:outcome["status"] for t in TARGETS}
        else:self.state["negatives"][kind]=outcome
        self.save()
        expected="PASS" if kind=="positive" else "EXPECTED_REJECTION"
        if outcome["status"]!=expected:raise Failed(kind+" did not meet the required acceptance condition")
    def fresh(self):
        if any(v!="PASS" for v in self.state["positive_targets"].values()):raise Blocked("Positive comparison incomplete")
        case=self.work/"cases/positive"
        lp=self.lean_path(case)
        self.run("all-source-build",self.sandbox(["lake","build","AllSource"],case,[case/".lake"],lp),cwd=case,timeout=5400)
        self.run("original-source-root-build",self.sandbox(["lake","build"],case,[case/".lake"],lp),cwd=case,timeout=5400)
        self.state["source_build"]={"status":"PASS","source_modules":261,"scope":"All 261 source and validation modules via operator-generated AllSource, then the original default target; documented temporary acceptance configuration"};self.save()
        before={str(p.relative_to(case)):file_sha(p) for p in (case/".lake/build").rglob("*.olean")}
        result,text=self.run("leanchecker-fresh",self.sandbox([self.prefix/"bin/leanchecker","--fresh","-v","LonelyRunnerValidation.FinalSolution"],case,(),lp),cwd=case,timeout=5400,check=False)
        after={str(p.relative_to(case)):file_sha(p) for p in (case/".lake/build").rglob("*.olean")}
        passed=result["exit_code"]==0 and not result["termination"] and before==after
        self.state["fresh"]={"status":"PASS" if passed else "INCOMPLETE","exit_code":result["exit_code"],"termination":result["termination"],"validated_olean_files_unchanged":before==after}
        inspect=self.work/"InspectFinalTypes.lean"
        targets=["LonelyRunnerNew.lonely_runner_gap","LonelyRunnerNew.frozen_target_proved",*TARGETS]
        inspect.write_text("import LonelyRunnerValidation.FinalSolution\nset_option pp.all true\n"+
          "\n".join("#check @"+t+"\n#print axioms "+t for t in targets)+"\n")
        _,printed=self.run("print-final-types",self.sandbox([self.prefix/"bin/lean","-j1",inspect],case,(),lp),cwd=case,timeout=600)
        checked=check_final_axioms(printed,targets)
        self.state["final_types"]={"status":"PASS","axioms":checked,"raw_output":"print-final-types command log; pp.all=true and explicit @ declarations"}
        self.save()
        if not passed:raise Failed("Full-environment fresh replay did not complete")
    def finalize(self):
        source_ok=self.state.get("source_check",{}).get("status")=="PASS"
        pos=all(v=="PASS" for v in self.state["positive_targets"].values())
        neg=all(v.get("status")=="EXPECTED_REJECTION" for v in self.state["negatives"].values())
        fresh=self.state["fresh"].get("status")=="PASS"
        build=self.state["source_build"].get("status")=="PASS"
        types=self.state.get("final_types",{}).get("status")=="PASS"
        self.state["machine_acceptance_completed"]=source_ok and pos and neg and fresh and build and types
        self.state["final_acceptance_completed"]=False
        self.state["remaining"]=["Independent human semantic/manuscript review","Author and license confirmation"]
        if not self.state["machine_acceptance_completed"]:self.state["remaining"].insert(0,"Incomplete machine gates")
        self.save()
        lines=["# Uniform-gap CI acceptance","",
          "Machine gates completed: "+str(self.state["machine_acceptance_completed"]),
          "Final acceptance including independent human review: False","",
          "Source: "+SOURCE_FP,"","## Positive targets"]
        lines += ["- "+t+": "+v for t,v in self.state["positive_targets"].items()]
        lines += ["","## Negative controls"]+["- "+k+": "+v["status"] for k,v in self.state["negatives"].items()]
        lines += ["","Fresh: "+self.state["fresh"]["status"],"Final types and axiom whitelist: "+self.state.get("final_types",{}).get("status","NOT_RUN"),"","## Remaining"]+["- "+s for s in self.state["remaining"]]
        (self.logs/"REPORT.md").write_text("\n".join(lines)+"\n")
        return self.state["machine_acceptance_completed"]

def main():
    if not sys.flags.isolated:
        print("Run the operator entry point with python3 -I",file=sys.stderr)
        return 2
    parser=argparse.ArgumentParser()
    parser.add_argument("--project",type=Path,required=True)
    parser.add_argument("--work",type=Path,required=True)
    parser.add_argument("--stage",choices=["verify","probe","setup","positive",*NEGATIVES,"fresh","finalize"],required=True)
    parser.add_argument("--initialize-user-manager",action="store_true")
    args=parser.parse_args()
    ctx=Context(args.project,args.work,Path(__file__).resolve().parent)
    try:
        if args.stage=="verify":ctx.verify()
        elif args.stage=="probe":ctx.probe(args.initialize_user_manager)
        elif args.stage=="setup":ctx.setup()
        elif args.stage in ["positive",*NEGATIVES]:ctx.compare(args.stage)
        elif args.stage=="fresh":ctx.fresh()
        elif args.stage=="finalize" and not ctx.finalize():raise Failed("Machine acceptance incomplete")
        return 0
    except Blocked as e:
        ctx.state["last_block"]={"stage":args.stage,"status":"BLOCKED_NOT_RUN","reason":str(e)}
        ctx.save();print(str(e),file=sys.stderr);return 2
    except Exception as e:
        ctx.state["last_error"]={"stage":args.stage,"reason":str(e)}
        ctx.save();print(str(e),file=sys.stderr);return 1

if __name__=="__main__":raise SystemExit(main())
