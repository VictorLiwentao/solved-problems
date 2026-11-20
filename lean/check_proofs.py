"""Compare all configured statements, replay the proofs, and print their axiom dependencies."""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--con-ron", type=Path, help="also replay with this con-ron executable")
    args = parser.parse_args()

    project = Path(__file__).resolve().parent
    config = json.loads((project / "comparator.json").read_text())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if set(config["permitted_axioms"]) != allowed:
        raise SystemExit("The comparator configuration must list the three standard Lean axioms.")

    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=project, text=True).strip()
    kernels = {"nanoda": [str(Path(prefix) / "bin" / "nanoda_bin")]}
    if args.con_ron:
        kernels["con-ron"] = [str(args.con_ron.resolve(strict=True))]

    # Palomar supplies its own kernel paths when it reads the committed configuration.
    with tempfile.TemporaryDirectory() as tmp:
        local_config = Path(tmp) / "comparator.json"
        local_config.write_text(json.dumps({**config, "external_kernels": kernels}))
        subprocess.run(["lake", "comparator", "--config", local_config], cwd=project, check=True)

    commands = [f"import {config['solution_module']}"]
    commands.extend(f"#print axioms {name}" for name in config["theorem_names"])
    subprocess.run(
        ["lake", "env", "lean", "--stdin"], input="\n".join(commands) + "\n",
        cwd=project, text=True, check=True,
    )


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from error
