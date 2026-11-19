"""Run the computational checks published with the research notes."""

from pathlib import Path
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parents[1]
    checks = sorted((root / "results").glob("*/*/verify.py"))
    if not checks:
        raise SystemExit("No verification scripts found under results/.")

    failures = []
    for check in checks:
        name = check.parent.name
        print(f"\nChecking {name}", flush=True)
        # Some verifiers use assert. Ignore PYTHONOPTIMIZE in the child process.
        result = subprocess.run([sys.executable, "-E", "-B", check.name], cwd=check.parent)
        if result.returncode:
            failures.append(name)

    print(f"\n{len(checks) - len(failures)} of {len(checks)} checks passed.")
    if failures:
        raise SystemExit("Failed checks: " + ", ".join(failures))


if __name__ == "__main__":
    main()
