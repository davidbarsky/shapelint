#![feature(rustc_private)]

use std::process::Command;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Boundary {
    PrivateLibrary,
    PublicLibrary,
    PublicTarget,
    MixedTarget,
    ExportedTarget,
    TargetExportedCallback,
    PublicStaticCallback,
    TargetExportedStaticCallback,
    ForeignAbiTarget,
    KnownCallback,
    EscapedCallback,
    ForeignCallback,
}

#[derive(Clone, Copy)]
enum Compilation {
    Library,
    Target,
}

#[hegel::test]
fn signature_findings_require_a_complete_caller_boundary(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Boundary>());
    struct Fixture {
        source: &'static str,
        compilation: Compilation,
        findings: usize,
    }
    let Fixture {
        source,
        compilation,
        findings,
    } = match case {
        Boundary::PrivateLibrary => Fixture {
            source: "fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} pub fn run(value:u32)->u32{render(value,None)}",
            compilation: Compilation::Library,
            findings: 1,
        },
        Boundary::PublicLibrary => Fixture {
            source: "pub fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} pub fn run(value:u32)->u32{render(value,None)}",
            compilation: Compilation::Library,
            findings: 0,
        },
        Boundary::PublicTarget => Fixture {
            source: "pub fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} fn main(){let _=render(0,None);}",
            compilation: Compilation::Target,
            findings: 1,
        },
        Boundary::MixedTarget => Fixture {
            source: "pub fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} fn main(){let _=render(0,None);let _=render(0,Some(1));}",
            compilation: Compilation::Target,
            findings: 0,
        },
        Boundary::ExportedTarget => Fixture {
            source: "#[unsafe(no_mangle)] pub fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} fn main(){let _=render(0,None);}",
            compilation: Compilation::Target,
            findings: 0,
        },
        Boundary::TargetExportedCallback => Fixture {
            source: "fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} #[unsafe(no_mangle)] pub fn export()->fn(u32,Option<u32>)->u32{render} fn main(){let _=render(0,None);}",
            compilation: Compilation::Target,
            findings: 0,
        },
        Boundary::PublicStaticCallback => Fixture {
            source: "fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} pub static CALLBACK:fn(u32,Option<u32>)->u32=render; pub fn run()->u32{render(0,None)}",
            compilation: Compilation::Library,
            findings: 0,
        },
        Boundary::TargetExportedStaticCallback => Fixture {
            source: "fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} #[unsafe(no_mangle)] pub static CALLBACK:fn(u32,Option<u32>)->u32=render; fn main(){let _=render(0,None);}",
            compilation: Compilation::Target,
            findings: 0,
        },
        Boundary::ForeignAbiTarget => Fixture {
            source: "pub extern \"C\" fn render(value:u32,basis:bool)->u32 {if basis{value.wrapping_add(1)}else{value}} fn main(){let _=render(0,false);}",
            compilation: Compilation::Target,
            findings: 0,
        },
        Boundary::KnownCallback => Fixture {
            source: "fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} fn apply(f:fn(u32,Option<u32>)->u32,value:u32)->u32{f(value,None)} pub fn run(value:u32)->u32{apply(render,value)}",
            compilation: Compilation::Library,
            findings: 1,
        },
        Boundary::EscapedCallback => Fixture {
            source: "fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} pub fn run(value:u32)->u32{render(value,None)} pub fn export()->fn(u32,Option<u32>)->u32{render}",
            compilation: Compilation::Library,
            findings: 0,
        },
        Boundary::ForeignCallback => Fixture {
            source: "fn render(value:u32,basis:Option<u32>)->u32 {match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} unsafe extern \"Rust\" {fn register(f:fn(u32,Option<u32>)->u32);} fn main(){let _=render(0,None);unsafe{register(render)}}",
            compilation: Compilation::Target,
            findings: 0,
        },
    };
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join("boundary.rs");
    std::fs::write(&path, source).expect("write source");
    let mut command = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    command.args(["--format=json", "--edition=2024", "--emit=metadata"]);
    match compilation {
        Compilation::Library => {
            command.arg("--crate-type=lib");
        }
        Compilation::Target => {
            command.args(["--crate-type=bin", "--analysis-scope=target"]);
        }
    }
    let output = command
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&path)
        .output()
        .expect("analysis");
    assert!(
        output.status.success(),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).expect("UTF-8 diagnostics");
    let actual = output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("finding"))
        .filter(|finding| finding["rule"] == "unused-capability" && finding["item"] == "render")
        .count();
    assert_eq!(actual, findings, "{case:?}: {output}");
}

#[test]
fn a_library_cannot_claim_a_closed_executable_boundary() {
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join("library.rs");
    std::fs::write(&path, "pub fn run() {}").expect("write source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--analysis-scope=target",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
        ])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(path)
        .output()
        .expect("analysis");
    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).expect("UTF-8 error");
    assert!(error.contains("executable"), "{error}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum DependencyBoundary {
    Target,
    TargetCallback,
    CallbackThroughProducer,
    Library,
    EscapedLocalCallback,
    MixedProducer,
    UncalledMixedProducer,
    RecursiveCallback,
    EscapedProducer,
    UncalledProducer,
    MissingProducer,
    MissingDependent,
}

#[hegel::test]
fn target_findings_include_dependency_callers_and_declarations(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<DependencyBoundary>());
    let directory = tempfile::tempdir().expect("source directory");
    let dependency = directory.path().join("dependency.rs");
    let artifact = directory.path().join("dependency.json");
    let addition = match case {
        DependencyBoundary::CallbackThroughProducer => {
            "pub fn invoke(f:fn(u32,Option<u32>)->u32)->u32 {f(0,None)}"
        }
        DependencyBoundary::EscapedLocalCallback => {
            "unsafe extern \"Rust\" {fn register(f:fn(u32,Option<u32>)->u32);} pub fn install(f:fn(u32,Option<u32>)->u32){unsafe{register(f)}}"
        }
        DependencyBoundary::MixedProducer | DependencyBoundary::UncalledMixedProducer => {
            "pub fn also()->u32 {render(0,Some(1))}"
        }
        DependencyBoundary::RecursiveCallback => {
            "pub fn drive(f:fn(usize),n:usize) {if n>0 {f(n-1)} else {let _=render(0,Some(1));}}"
        }
        DependencyBoundary::EscapedProducer => {
            "#[unsafe(no_mangle)] pub fn export()->fn(u32,Option<u32>)->u32 {render}"
        }
        DependencyBoundary::UncalledProducer => "pub fn also()->u32 {render(0,None)}",
        DependencyBoundary::Target
        | DependencyBoundary::TargetCallback
        | DependencyBoundary::Library
        | DependencyBoundary::MissingProducer
        | DependencyBoundary::MissingDependent => "",
    };
    std::fs::write(&dependency, format!("pub fn render(value:u32,basis:Option<u32>)->u32 {{match basis{{Some(basis)=>value.wrapping_add(basis),None=>value}}}} {addition}")).expect("write dependency");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name=dependency",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&artifact)
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&dependency)
        .output()
        .expect("analyze dependency");
    assert!(
        output.status.success(),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let dependency_metadata = directory.path().join("libdependency.rmeta");
    let mut command = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    command
        .args([
            "--format=json",
            "--edition=2024",
            "--emit=metadata",
            "--extern",
        ])
        .arg(format!("dependency={}", dependency_metadata.display()))
        .arg("--out-dir")
        .arg(directory.path());
    match case {
        DependencyBoundary::Library | DependencyBoundary::EscapedLocalCallback => {
            command.arg("--crate-type=lib");
        }
        _ => {
            command.args(["--crate-type=bin", "--analysis-scope=target"]);
        }
    }
    match case {
        DependencyBoundary::MissingProducer => {}
        _ => {
            command.arg("--summary-input").arg(&artifact);
        }
    }
    let consumer = match case {
        DependencyBoundary::Library => "pub fn run()->u32{dependency::render(0,None)}",
        DependencyBoundary::EscapedLocalCallback => {
            "fn local(n:u32,basis:Option<u32>)->u32{match basis{Some(v)=>v,None=>n}} pub fn run()->u32{dependency::install(local);local(0,None)}"
        }
        DependencyBoundary::TargetCallback => {
            "fn invoke(f:fn(u32,Option<u32>)->u32)->u32{f(0,None)} fn main(){let _=invoke(dependency::render);}"
        }
        DependencyBoundary::CallbackThroughProducer => {
            "fn main(){let _=dependency::invoke(dependency::render);}"
        }
        DependencyBoundary::UncalledProducer => "fn main(){}",
        DependencyBoundary::MixedProducer => {
            "fn main(){let _=dependency::render(0,None);let _=dependency::also();}"
        }
        DependencyBoundary::RecursiveCallback => {
            "fn again(n:usize){dependency::drive(again,n)} fn main(){let _=dependency::render(0,None);again(std::env::args().len());}"
        }
        DependencyBoundary::Target
        | DependencyBoundary::UncalledMixedProducer
        | DependencyBoundary::EscapedProducer
        | DependencyBoundary::MissingProducer => "fn main(){let _=dependency::render(0,None);}",
        DependencyBoundary::MissingDependent => {
            let dependent = directory.path().join("dependent.rs");
            std::fs::write(
                &dependent,
                "pub fn call()->u32{dependency::render(0,Some(1))}",
            )
            .expect("write dependent");
            let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
                .args([
                    "--format=json",
                    "--crate-name=dependent",
                    "--crate-type=lib",
                    "--edition=2024",
                    "--emit=metadata",
                    "--extern",
                ])
                .arg(format!("dependency={}", dependency_metadata.display()))
                .arg("--summary-output")
                .arg(directory.path().join("dependent.json"))
                .arg("--out-dir")
                .arg(directory.path())
                .arg(dependent)
                .output()
                .expect("analyze dependent");
            assert!(
                output.status.success(),
                "{case:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(
                output.stderr.is_empty(),
                "{case:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            command
                .arg("--extern")
                .arg(format!(
                    "dependent={}",
                    directory.path().join("libdependent.rmeta").display()
                ))
                .arg("-L")
                .arg(format!("dependency={}", directory.path().display()));
            "fn main(){let _=dependency::render(0,None);let _=dependent::call();}"
        }
    };
    let source = directory.path().join("consumer.rs");
    std::fs::write(&source, consumer).expect("write consumer");
    let output = command.arg(&source).output().expect("analyze consumer");
    assert!(
        output.status.success(),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).expect("UTF-8 diagnostics");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "unused-capability")
        .collect();
    match case {
        DependencyBoundary::Target | DependencyBoundary::TargetCallback => {
            assert_eq!(findings.len(), 1, "{case:?}: {output}");
            let finding = &findings[0];
            assert_eq!(finding["item"], "main", "{output}");
            let locations = finding["related"].as_array().expect("related locations");
            let declaration = locations.iter().find(|location| {
                location["label"]["message"]
                    .as_str()
                    .expect("label")
                    .contains("declared in")
            });
            let declaration = declaration.expect("imported parameter declaration");
            assert!(
                declaration["input"]["name"]
                    .as_str()
                    .expect("source name")
                    .ends_with("dependency.rs"),
                "{output}"
            );
        }
        DependencyBoundary::Library
        | DependencyBoundary::CallbackThroughProducer
        | DependencyBoundary::EscapedLocalCallback
        | DependencyBoundary::MixedProducer
        | DependencyBoundary::UncalledMixedProducer
        | DependencyBoundary::RecursiveCallback
        | DependencyBoundary::EscapedProducer
        | DependencyBoundary::UncalledProducer
        | DependencyBoundary::MissingProducer
        | DependencyBoundary::MissingDependent => {
            assert!(findings.is_empty(), "{case:?}: {output}")
        }
    }
}
