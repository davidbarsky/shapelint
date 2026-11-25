# Builds and releases

GitHub Actions builds Windows x86-64 and ARM64, macOS ARM64, and Linux x86-64 and ARM64. Pull requests and pushes to `main` produce workflow artifacts. A version tag publishes the same archives and their SHA-256 checksums to GitHub Releases after all builds pass.

Update the workspace version in `Cargo.toml` and refresh `Cargo.lock` before tagging the release commit. The tag must match the workspace version. To release version 0.0.1 from `main`:

```sh
jj tag set v0.0.1 -r main
jj git push --remote origin --tag v0.0.1
```

Extract the archive and add its `bin` directory to your PATH. Keep it alongside the included `lib` directory. Both binaries use the bundled Rust compiler runtime, and the driver uses the bundled host standard library unless you pass `--sysroot` explicitly.
