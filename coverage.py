"""Run nextest with branch coverage and retain reports even when tests fail."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-p", "--package", action="append", default=[])
    parser.add_argument("--test", action="append", default=[])
    parser.add_argument("-E", "--filter-expr")
    parser.add_argument("--release", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    output = root / "target" / "coverage"
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env.pop("RUSTUP_TOOLCHAIN", None)
    cargo = subprocess.check_output(
        ["rustup", "which", "cargo"], cwd=root, env=env, text=True
    ).strip()
    env["PATH"] = os.pathsep.join([str(Path(cargo).parent), *os.get_exec_path(env)])
    env["RUSTC_BOOTSTRAP"] = "1"
    env["CARGO_LLVM_COV_TARGET_DIR"] = str(output / "build")
    clean = subprocess.run(
        ["cargo", "llvm-cov", "clean", "--workspace"], cwd=root, env=env
    )
    if clean.returncode:
        return clean.returncode
    selection = []
    for package in args.package:
        selection.extend(["--package", package])
    if not args.package:
        selection.append("--workspace")
    for target in args.test:
        selection.extend(["--test", target])
    if args.filter_expr:
        selection.extend(["--filter-expr", args.filter_expr])
    profile = ["--release"] if args.release else []
    command = [
        "cargo", "llvm-cov", "nextest", "--branch", "--no-report",
        "--no-fail-fast", *profile, *selection,
    ]
    tests = subprocess.run(command, cwd=root, env=env)
    report = [
        "cargo", "llvm-cov", "report", "--package", "*", "--branch", *profile,
        "--ignore-filename-regex", r"(^|/)(tests|fixtures)/|/build\.rs$",
    ]
    html = subprocess.run(
        [*report, "--html", "--output-dir", str(output)], cwd=root, env=env
    )
    data = subprocess.run(
        [*report, "--json", "--output-path", str(output / "coverage.json")],
        cwd=root, env=env,
    )
    status = {
        "command": command,
        "tests": tests.returncode,
        "html": html.returncode,
        "json": data.returncode,
    }
    (output / "run.json").write_text(json.dumps(status, indent=2) + "\n")
    print(json.dumps(status, indent=2), flush=True)
    print(f"Coverage reports: {output}", flush=True)
    return tests.returncode or html.returncode or data.returncode


if __name__ == "__main__":
    sys.exit(main())
