use std::error::Error;
use std::process::Command;

fn main() -> Result<(), Box<dyn Error>> {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");
    let rustc = std::env::var_os("RUSTC").ok_or("Cargo did not set RUSTC")?;
    let output = Command::new(rustc).args(["--print", "sysroot"]).output()?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned().into());
    }
    let sysroot = String::from_utf8(output.stdout)?;
    let sysroot = sysroot.trim();
    println!("cargo:rustc-env=SHAPELINT_SYSROOT={sysroot}");
    match std::env::var("CARGO_CFG_TARGET_OS")?.as_str() {
        "macos" | "linux" => println!("cargo:rustc-link-arg=-Wl,-rpath,{sysroot}/lib"),
        target => return Err(format!("unsupported compiler-driver host: {target}").into()),
    }
    Ok(())
}
