"""Package both Shapelint binaries with the Rust runtime they were linked against."""

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib


def main(target, output):
    config = tomllib.loads(Path("rust-toolchain.toml").read_text())
    version = config["toolchain"]["channel"]
    toolchain = f"{version}-{target}"
    sysroot = Path(subprocess.check_output(
        ["rustup", "run", toolchain, "rustc", "--print", "sysroot"], text=True
    ).strip())
    package = tomllib.loads(Path("Cargo.toml").read_text())["workspace"]["package"]
    if os.environ.get("GITHUB_REF_TYPE") == "tag":
        expected = f"v{package['version']}"
        if os.environ["GITHUB_REF_NAME"] != expected:
            raise SystemExit(f"release tag must match the workspace version ({expected})")

    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    windows = target.endswith("-windows-msvc")
    extension = ".exe" if windows else ""
    archive_name = f"shapelint-{target}"

    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        build = scratch / "build"
        subprocess.run(
            ["rustup", "run", toolchain, "cargo", "build", "--workspace", "--bins", "--release",
             "--locked", "--target-dir", str(build)],
            env={
                **os.environ,
                "RUSTC": str(sysroot / "bin" / f"rustc{extension}"),
                "SHAPELINT_BUNDLED_RUNTIME": "1",
                "PATH": f"{sysroot / 'bin'}{os.pathsep}{os.environ['PATH']}",
            },
            check=True,
        )

        root = scratch / archive_name
        (root / "bin").mkdir(parents=True)
        for name in ("shapelint", "shapelint-driver"):
            binary = f"{name}{extension}"
            shutil.copy2(build / "release" / binary, root / "bin" / binary)

        manifests = sysroot / "lib/rustlib"
        for component in ("rustc", "rust-std"):
            for line in (manifests / f"manifest-{component}-{target}").read_text().splitlines():
                kind, _, name = line.partition(":")
                relative = Path(name)
                runtime = (
                    component == "rust-std"
                    or relative.parent == Path("lib")
                    or (relative.parent == Path("bin") and relative.suffix == ".dll")
                    or relative.is_relative_to("share/doc/rust")
                    or relative.is_relative_to(f"lib/rustlib/{target}/bin")
                )
                if kind == "file" and runtime:
                    destination = root / relative
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(sysroot / relative, destination)

        source = scratch / "smoke.rs"
        source.write_text("pub const SMOKE: usize = std::mem::size_of::<usize>();\n")
        subprocess.run(
            [root / "bin" / f"shapelint{extension}", "check", source],
            cwd=scratch, check=True,
        )
        driver = root / "bin" / f"shapelint-driver{extension}"
        reported_sysroot = subprocess.check_output(
            [driver, "--print=sysroot"], cwd=scratch, text=True
        ).strip()
        if not root.samefile(reported_sysroot):
            raise SystemExit("packaged driver did not select its bundled sysroot")
        subprocess.run(
            [driver, "--crate-type=lib",
             "--emit=dep-info,metadata", "--cargo-check-only",
             "--out-dir", scratch, source],
            cwd=scratch, check=True,
        )
        if not (scratch / "libsmoke.rmeta").is_file():
            raise SystemExit("packaged driver did not create compiler metadata")

        archive = Path(shutil.make_archive(
            str(output / archive_name), "zip" if windows else "gztar", scratch, archive_name
        ))
        with archive.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        archive.with_name(f"{archive.name}.sha256").write_text(
            f"{digest}  {archive.name}\n", encoding="ascii", newline="\n"
        )


if __name__ == "__main__":
    main(*sys.argv[1:])
