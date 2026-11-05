"""Local regression checks only; not official Comparator or final acceptance."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / "logs" / "acceptance-v1-preflight"
FROZEN = ROOT / "validation" / "frozen-v1.sha256.json"


def verify_frozen():
    for name, expected in json.loads(FROZEN.read_text(encoding="utf-8-sig")).items():
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f"Frozen file changed: {name}")
    cfg = json.loads((ROOT / "validation/comparator/config.json").read_text())
    assert cfg["theorem_names"] == [
        "LonelyRunnerAcceptance.explicit_gap", "LonelyRunnerAcceptance.uniform_gap"]
    assert cfg["definition_names"] == []
    assert set(cfg["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}


def main():
    verify_frozen()
    LOGS.mkdir(parents=True, exist_ok=True)
    results = []
    fixtures = [
        ("positive_control", None),
        ("weak_target", "TARGET_REJECT"),
        ("changed_definition", "TARGET_REJECT"),
        ("sorry_dependency", "AXIOM_REJECT"),
        ("conditional_as_final", "TARGET_REJECT")]
    with tempfile.TemporaryDirectory(prefix="lonelyrunner-preflight-") as tmp:
        for name, rejection in fixtures:
            source = ROOT / "validation/preflight" / f"{name}.lean.in"
            target = Path(tmp) / f"{name}.lean"
            target.write_bytes(source.read_bytes())
            command = ["lake", "env", "lean", str(target)]
            proc = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT)
            raw = proc.stdout.decode("utf-8", errors="replace")
            (LOGS / f"{name}.log").write_bytes(proc.stdout)
            ok = (proc.returncode == 0 if rejection is None else
                  proc.returncode != 0 and rejection in raw)
            results.append(dict(case=name, command=command, exit_code=proc.returncode,
                                expected_rejection=rejection, expectation_met=ok))
            print(f"{name}: exit={proc.returncode}, expectation_met={ok}")
    verify_frozen()
    report = dict(scope="local preflight only; Comparator and final theorem not checked",
                  utc=datetime.now(timezone.utc).isoformat(), results=results)
    (LOGS / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if not all(r["expectation_met"] for r in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
