use std::process::Command;

pub(crate) struct Fixture {
    directory: tempfile::TempDir,
    summary: std::path::PathBuf,
    metadata: std::path::PathBuf,
}

impl Fixture {
    pub(crate) fn produce() -> (Self, Vec<u8>) {
        let directory = tempfile::tempdir().expect("source directory");
        let producer = directory.path().join("dependency.rs");
        let metadata = directory.path().join("libdependency.rmeta");
        let summary = directory.path().join("dependency.summary.json");
        std::fs::write(&producer, "pub fn value() -> usize { 7 }").expect("producer source");
        let produced = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args([
                "--format=json",
                "--crate-name=dependency",
                "--crate-type=lib",
                "--edition=2024",
                "--emit=metadata",
                "--summary-output",
            ])
            .arg(&summary)
            .arg("-o")
            .arg(&metadata)
            .arg(&producer)
            .output()
            .expect("producer compilation");
        assert!(
            produced.status.success(),
            "{}",
            String::from_utf8_lossy(&produced.stderr)
        );
        let artifact = std::fs::read(&summary).expect("producer summary");
        let fixture = Self {
            directory,
            summary,
            metadata,
        };
        (fixture, artifact)
    }

    pub(crate) fn import(&self, artifact: &serde_json::Value) -> std::process::Output {
        std::fs::write(
            &self.summary,
            serde_json::to_vec(artifact).expect("modified summary bytes"),
        )
        .expect("modified summary");
        let consumer = self.directory.path().join("consumer.rs");
        std::fs::write(&consumer, "pub fn run() {}").expect("consumer source");
        Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args([
                "--format=json",
                "--crate-name=consumer",
                "--crate-type=lib",
                "--edition=2024",
                "--emit=metadata",
                "--summary-input",
            ])
            .arg(&self.summary)
            .arg("--summary-output")
            .arg(self.directory.path().join("consumer.summary.json"))
            .arg("--extern")
            .arg(format!("dependency={}", self.metadata.display()))
            .arg("--out-dir")
            .arg(self.directory.path())
            .arg(&consumer)
            .output()
            .expect("consumer compilation")
    }

    pub(crate) fn exported(&self) -> Vec<u8> {
        let path = self.directory.path().join("consumer.summary.json");
        std::fs::read(&path).unwrap_or_else(|error| panic!("reading {}: {error}", path.display()))
    }
}
