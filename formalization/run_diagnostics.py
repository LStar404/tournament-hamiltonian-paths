"""Rerun the four published entry points and preserve machine-readable evidence.

Finite diagnostics do not certify the asymptotic theorem or Lean proofs.
Invoke from any directory with Python 3.11+ and numpy installed.
"""

import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = {
    "operator-packing": "verify_operator_packing_path_constant.py",
    "uniform-permanent": "verify_uniform_permanent_zeroth_audit.py",
    "nonprincipal-deletion": "verify_nonprincipal_gaussian_deletion.py",
    "global-reduction": "verify_standalone_linear_energy_reduction.py",
}


def main():
    import numpy

    output_dir = ROOT / "formalization" / "audit"
    output_dir.mkdir(parents=True, exist_ok=True)
    source_dir = ROOT / "materials" / "verification"
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    source_hashes = {
        path.name: hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(source_dir.glob("*.py"))
    }
    failed = False
    for name, script in SCRIPTS.items():
        process = subprocess.run(
            [sys.executable, "-B", str(source_dir / script)],
            cwd=source_dir, text=True, encoding="utf-8", capture_output=True,
        )
        records = [json.loads(line.removeprefix("RECORD "))
                   for line in process.stdout.splitlines()
                   if line.startswith("RECORD ")]
        success = process.returncode == 0 and len(records) == 1
        result = {
            "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
            "source_revision": revision,
            "source_sha256": source_hashes,
            "python": platform.python_version(),
            "numpy": numpy.__version__,
            "script": script,
            "returncode": process.returncode,
            "success": success,
            "scope": "Published finite diagnostics only; not all-order or formal certification.",
            "record": records[0] if len(records) == 1 else records,
            "stdout": process.stdout,
            "stderr": process.stderr,
        }
        (output_dir / f"{name}.json").write_text(
            json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n"
        )
        print(f"{name}: {'PASS' if success else 'FAIL'} (exit {process.returncode})")
        failed |= not success
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
