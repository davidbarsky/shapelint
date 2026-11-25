use std::error::Error;
use std::process::Command;

fn main() -> Result<(), Box<dyn Error>> {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-env-changed=SHAPELINT_BUNDLED_RUNTIME");
    let rustc = std::env::var_os("RUSTC").ok_or("Cargo did not set RUSTC")?;
    let output = Command::new(rustc).args(["--print", "sysroot"]).output()?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned().into());
    }
    let sysroot = String::from_utf8(output.stdout)?;
    let sysroot = sysroot.trim();
    println!("cargo:rustc-env=SHAPELINT_SYSROOT={sysroot}");
    println!("cargo:rustc-env=SHAPELINT_HOST={}", std::env::var("HOST")?);
    let runtime = match std::env::var("CARGO_CFG_TARGET_OS")?.as_str() {
        "macos" => Some("@loader_path/../lib"),
        "linux" => Some("$ORIGIN/../lib"),
        "windows" => None,
        target => return Err(format!("unsupported compiler-driver host: {target}").into()),
    };
    if let Some(runtime) = runtime {
        println!("cargo:rustc-link-search=native={sysroot}/lib");
        println!("cargo:rustc-link-arg=-Wl,-rpath,{runtime}");
        if let None = std::env::var_os("SHAPELINT_BUNDLED_RUNTIME") {
            println!("cargo:rustc-link-arg=-Wl,-rpath,{sysroot}/lib");
        }
    }
    Ok(())
}
