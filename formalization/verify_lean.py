"""Build the project, audit axioms, and record exactly which sources were checked.

Use --require-main for the final submission gate. A build of the current
components is useful evidence but does not certify the full research result.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def audited_project_sources():
    """Follow project imports, so unfinished files cannot inherit a build PASS."""
    pending = [ROOT / "TournamentHamiltonian.lean", ROOT / "Audit.lean"]
    reached = set()
    while pending:
        path = pending.pop()
        if path in reached:
            continue
        reached.add(path)
        for line in path.read_text(encoding="utf-8").splitlines():
            match = re.match(r"^\s*import\s+(.+)$", line)
            if match is None:
                continue
            for module in match.group(1).split("--", 1)[0].split():
                if module == "TournamentHamiltonian" or module.startswith("TournamentHamiltonian."):
                    pending.append(ROOT.joinpath(*module.split(".")).with_suffix(".lean"))
    all_sources = set((ROOT / "TournamentHamiltonian").rglob("*.lean"))
    return sorted(reached), sorted(all_sources - reached)


def sanitized_output(value, *extra_paths):
    for path, label in [(ROOT, "<formalization>"), *extra_paths]:
        value = value.replace(str(path), label).replace(path.as_posix(), label)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-main", action="store_true")
    args = parser.parse_args()
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("lake is not on PATH; install the pinned Lean toolchain first")
    commands = [[lake, "build"], [lake, "env", "lean", "Audit.lean"]]
    records = []
    for command in commands:
        process = subprocess.run(command, cwd=ROOT, text=True, encoding="utf-8",
                                 errors="replace", capture_output=True)
        records.append({"command": ["lake", *command[1:]],
                        "returncode": process.returncode,
                        "stdout": sanitized_output(process.stdout),
                        "stderr": sanitized_output(process.stderr)})
        print(f"{' '.join(command[1:])}: exit {process.returncode}")
        if process.returncode:
            break
    components_ok = len(records) == len(commands) and all(r["returncode"] == 0 for r in records)
    main_proved = False
    if components_ok:
        # Check the actual theorem type in Lean, independently of a status file.
        with tempfile.TemporaryDirectory(prefix="tournament-main-") as directory:
            source = Path(directory) / "MainCheck.lean"
            source.write_text("import TournamentHamiltonian\n"
                              "example : TournamentHamiltonian.MainBound := "
                              "TournamentHamiltonian.mainBound\n", encoding="utf-8")
            process = subprocess.run([lake, "env", "lean", str(source)], cwd=ROOT,
                                     text=True, encoding="utf-8", errors="replace",
                                     capture_output=True)
        records.append({"command": ["lake", "env", "lean", "<main-theorem-check>"],
                        "returncode": process.returncode,
                        "stdout": sanitized_output(process.stdout, (source, "<main-theorem-check>")),
                        "stderr": sanitized_output(process.stderr, (source, "<main-theorem-check>"))})
        main_proved = process.returncode == 0
        print(f"full MainBound proof: {'PASS' if main_proved else 'NOT YET PROVED'}")
    source_paths, unimported_sources = audited_project_sources()
    source_paths += [ROOT / filename for filename in
                     ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify_lean.py")]
    result = {
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "components_build_and_axiom_audit_pass": components_ok,
        "main_theorem_proved": main_proved,
        "all_project_sources_imported_for_audit": not unimported_sources,
        "project_sources_not_imported_for_audit": [path.relative_to(ROOT).as_posix()
                                                   for path in unimported_sources],
        "require_main": args.require_main,
        "source_sha256": {str(path.relative_to(ROOT)).replace("\\", "/"):
                          hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in source_paths},
        "commands": records,
        "scope": "Only the imported and checked declarations are certified; MainBound is checked independently, and submission also requires every project source to be imported for audit.",
    }
    output = ROOT / "audit" / "lean-verification.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    return int(not components_ok or
               (args.require_main and (not main_proved or bool(unimported_sources))))


if __name__ == "__main__":
    sys.exit(main())
