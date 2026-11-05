"""Record real command output and exit status, without interpreting it as a proof."""
from datetime import datetime, timezone
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    if len(sys.argv) < 3:
        raise SystemExit("usage: record_command.py LABEL COMMAND [ARGS...]")
    label, command = sys.argv[1], sys.argv[2:]
    if not label.replace("-", "").replace("_", "").isalnum():
        raise SystemExit("invalid label")
    logs = ROOT / "logs" / "acceptance-v1"
    logs.mkdir(parents=True, exist_ok=True)
    start = datetime.now(timezone.utc).isoformat()
    with (logs / f"{label}.log").open("wb") as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT)
        assert process.stdout is not None
        while chunk := process.stdout.read1(65536):
            log.write(chunk)
            log.flush()
            sys.stdout.buffer.write(chunk)
            sys.stdout.buffer.flush()
        code = process.wait()
    result = dict(command=command, cwd=str(ROOT), exit_code=code,
                  start_utc=start, end_utc=datetime.now(timezone.utc).isoformat())
    (logs / f"{label}.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    raise SystemExit(code)


if __name__ == "__main__":
    main()
