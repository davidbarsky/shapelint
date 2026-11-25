#!/usr/bin/env python3

import argparse
import fcntl
from functools import cmp_to_key
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import uuid


def freeze_json(value, ordered=False):
    if isinstance(value, dict):
        items = value.items() if ordered else sorted(value.items())
        return ("object", tuple((key, freeze_json(item, ordered)) for key, item in items))
    if isinstance(value, list):
        return ("array", tuple(freeze_json(item, ordered) for item in value))
    if isinstance(value, str):
        return ("string", value)
    return ("scalar", json.dumps(value))


def json_chunks(value, shared):
    cached = shared.get(id(value))
    if cached is not None:
        yield from cached
    elif isinstance(value, dict):
        yield "{"
        for index, (key, item) in enumerate(sorted(value.items())):
            if index:
                yield ", "
            yield json.dumps(key)
            yield ": "
            yield from json_chunks(item, shared)
        yield "}"
    elif isinstance(value, list):
        yield "["
        for index, item in enumerate(value):
            if index:
                yield ", "
            yield from json_chunks(item, shared)
        yield "]"
    else:
        yield json.dumps(value)


def compare_json(left, right, shared=None):
    shared = {} if shared is None else shared
    streams = [iter(json_chunks(value, shared)) for value in (left, right)]
    chunks = ["", ""]
    positions = [0, 0]
    ended = [False, False]
    while True:
        for index in (0, 1):
            while positions[index] == len(chunks[index]) and not ended[index]:
                chunks[index] = next(streams[index], "")
                positions[index] = 0
                ended[index] = not chunks[index]
        if ended[0] or ended[1]:
            return int(ended[1]) - int(ended[0])
        length = min(len(chunks[0]) - positions[0], len(chunks[1]) - positions[1])
        a = chunks[0][positions[0]:positions[0] + length]
        b = chunks[1][positions[1]:positions[1] + length]
        if a != b:
            return -1 if a < b else 1
        positions[0] += length
        positions[1] += length


def compare_records(left, right, shared=None):
    def prefix(record):
        finding = record["finding"]
        return finding["path"], finding["primary"]["span"]["start"], finding["rule"]
    a, b = prefix(left), prefix(right)
    if a != b:
        return -1 if a < b else 1
    return compare_json(left["finding"], right["finding"], shared)


def report(reports, format, output=None):
    if output is None:
        output = sys.stdout
    findings = {}
    sources = {}
    wire_sources = {}
    source_keys = {}
    encoded_sources = {}
    trait_locations = {}
    implementations = {}
    finding_locations = {}

    def workspace_path(directory, path):
        path = Path(path)
        if not path.is_absolute():
            path = directory / path
        return str(path.resolve())

    def workspace_facts(directory, facts):
        for trait in facts.get("traits", []):
            location = trait["span"]
            key = (workspace_path(directory, trait["path"]),
                   location["start"], location["end"])
            trait_locations.setdefault(key, set()).add(tuple(trait["identity"]))
        for implementation in facts.get("implementations", []):
            location = implementation["span"]
            identity = tuple(implementation["trait_identity"])
            key = (identity, workspace_path(directory, implementation["path"]),
                   location["start"], location["end"])
            implementations.setdefault(identity, set()).add(key)

    def source_identity(directory, original):
        cached = source_keys.get((str(directory), id(original)))
        if cached is not None:
            return cached
        wire = wire_sources.setdefault(freeze_json(original, ordered=True), original)
        source = dict(wire)
        source["name"] = str((directory / source["name"]).resolve())
        frozen = freeze_json(source)
        source_id = sources.setdefault(frozen, len(sources))
        if id(wire) not in encoded_sources:
            encoded_sources[id(wire)] = tuple(json.JSONEncoder(sort_keys=True).iterencode(wire))
        result = (wire, source_id)
        # The wire object remains owned here; table inputs also remain owned until their stream ends.
        source_keys[(str(directory), id(wire))] = result
        return result

    for directory, path in reports:
        source_table = {}
        with path.open() as stream:
            for line in stream:
                record = json.loads(line)
                if record.get("record") == "header":
                    if record["version"] != 2:
                        raise ValueError("unsupported shapelint report stream version")
                    continue
                if record.get("record") == "workspace":
                    workspace_facts(directory, record["facts"])
                    continue
                if record.get("record") == "source":
                    source_table[record["id"]] = source_identity(directory, record["input"])
                    continue
                if record.get("record") == "finding":
                    related = [{"input": source_table[item["source"]][0], "label": item["label"]}
                               for item in record["related"]]
                    if related:
                        record["finding"]["related"] = related
                if "finding" not in record:
                    record = {"finding": record}
                finding = record["finding"]
                identity = dict(finding)
                identity.pop("fingerprint")
                identity["path"] = str((directory / finding["path"]).resolve())
                related = finding.get("related", [])
                related_key = None
                if related:
                    identity.pop("related")
                    locations = []
                    for location in related:
                        wire, source_id = source_identity(directory, location["input"])
                        location["input"] = wire
                        locations.append((source_id, json.dumps(location["label"], sort_keys=True)))
                    related_key = tuple(locations)
                key = (json.dumps(identity, sort_keys=True), related_key)
                findings.setdefault(key, record)
                finding_locations.setdefault(key, identity["path"])
    for key, record in list(findings.items()):
        finding = record["finding"]
        if finding.get("rule") != "single-impl-trait":
            continue
        span = finding.get("primary", {}).get("span", {})
        location = (finding_locations[key],
                    span.get("start"), span.get("end"))
        identities = trait_locations.get(location, ())
        if any(len(implementations.get(identity, ())) > 1 for identity in identities):
            del findings[key]
    records = sorted(findings.values(), key=cmp_to_key(
        lambda left, right: compare_records(left, right, encoded_sources)))
    for record in records:
        if format == "json":
            print(json.dumps(record["finding"]), file=output)
        else:
            print(record["rendered"], end="", file=output)


def emit_report(reports, format, cache, output):
    # Run report paths are immutable and identify the generation Cargo selected.
    identities = sorted({(str(directory.resolve()), str(path.resolve()))
                         for directory, path in reports})
    key = hashlib.sha256(json.dumps(identities).encode()).hexdigest()
    destination = cache / (key + ".txt")
    if not destination.exists():
        temporary = cache / (key + "." + uuid.uuid4().hex + ".tmp")
        with temporary.open("w") as stream:
            report([(Path(directory), Path(path)) for directory, path in identities], format, stream)
        temporary.replace(destination)
    with destination.open() as stream:
        shutil.copyfileobj(stream, output)


def configuration_identity(driver, script, options):
    identity = hashlib.sha256()
    for value in (driver.read_bytes(), script.read_bytes(),
                  json.dumps(options, sort_keys=True).encode()):
        identity.update(len(value).to_bytes(8, "big"))
        identity.update(value)
    return identity.hexdigest()


def artifact_key(path):
    return hashlib.sha256(str(Path(path).resolve()).encode()).hexdigest()


def publish_reports(output, name, suffix, reports, report_path, directory, invocation):
    # Match complete rustc output names; substring matches can steal another unit's report.
    extensions = ("", ".exe", ".rmeta", ".rlib", ".so", ".dylib", ".dll")
    candidates = [output / (prefix + name + suffix + extension)
                  for prefix in ("", "lib") for extension in extensions]
    artifacts = [artifact for artifact in candidates if artifact.is_file()]
    if name == "build_script_build":
        # Cargo creates this alias after rustc returns.
        artifacts.append(output / ("build-script-build.exe" if os.name == "nt" else "build-script-build"))
    for artifact in artifacts:
        destination = reports / (artifact_key(artifact) + ".json")
        temporary = destination.with_name(destination.name + "." + invocation)
        temporary.write_text(json.dumps({"directory": str(directory), "report": str(report_path)}))
        temporary.replace(destination)


def select_reports(messages, root, reports, run=None):
    selected = set()
    missing = []
    root = root.resolve()
    for message in messages:
        if message.get("reason") != "compiler-artifact":
            continue
        source = Path(message["target"]["src_path"]).resolve()
        if not source.is_relative_to(root):
            continue
        matches = [reports / (artifact_key(path) + ".json")
                   for path in message["filenames"]]
        matches = [path for path in matches if path.is_file()]
        if matches:
            entry = json.loads(matches[0].read_text())
            report_path = Path(entry["report"])
            if (not report_path.is_file() or
                    (run is not None and not message.get("fresh", False) and report_path.parent != run)):
                missing.append(str(source))
                continue
            selected.add((Path(entry["directory"]), report_path))
        else:
            missing.append(str(source))
    return sorted(selected), missing


def cargo_messages(stream, stderr):
    messages = []
    for line in stream:
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            print(line, end="", file=stderr)
            continue
        if message.get("reason") == "compiler-message":
            rendered = message.get("message", {}).get("rendered")
            if rendered:
                print(rendered, end="", file=stderr)
        elif message.get("reason") == "compiler-artifact":
            messages.append(message)
    return messages


def check_workspace(command, root, environment, directory, cached_reports, configuration, stderr):
    # Cargo and the artifact indexes must describe the same invocation.
    with (configuration / "lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        result = subprocess.run(command, cwd=root, env=environment, stdout=subprocess.PIPE, text=True)
        messages = cargo_messages(result.stdout.splitlines(keepends=True), stderr)
        reports, missing = select_reports(messages, root, cached_reports, directory)
        reports.extend((Path(path.with_suffix(".cwd").read_text()), path)
                       for path in sorted(directory.glob("*.failed.jsonl")))
        return result.returncode, reports, missing


def main():
    driver = os.environ.get("SHAPELINT_CARGO_DRIVER")
    if driver is not None:
        compiler, *arguments = sys.argv[1:]
        # Cargo nests the workspace wrapper inside the global wrapper.
        if compiler == os.environ.get("RUSTC_WORKSPACE_WRAPPER"):
            return subprocess.run([compiler, *arguments], close_fds=False).returncode
        for index, argument in enumerate(arguments):
            if argument in {"--crate-type", "--extern", "--crate-name", "-o"} and index + 1 == len(arguments):
                return subprocess.run([compiler, *arguments], close_fds=False).returncode
        root = Path(os.environ["SHAPELINT_CARGO_ROOT"])
        sources = [Path(argument).resolve() for argument in arguments if argument.endswith(".rs")]
        if "--crate-name" not in arguments or not any(source.is_relative_to(root) for source in sources):
            return subprocess.run([compiler, *arguments], close_fds=False).returncode
        emits = [argument.removeprefix("--emit=") for argument in arguments if argument.startswith("--emit=")]
        check_only = (len(emits) == 1 and set(emits[0].split(",")) == {"dep-info", "metadata"}
                      and not any(argument == "--print" or argument.startswith("--print=") for argument in arguments)
                      and not any(argument.startswith("-o") for argument in arguments))
        if not check_only:
            result = subprocess.run([compiler, *arguments], close_fds=False)
            if result.returncode:
                return result.returncode
        crate_types = []
        for index, argument in enumerate(arguments):
            if argument == "--crate-type":
                crate_types.extend(arguments[index + 1].split(","))
            elif argument.startswith("--crate-type="):
                crate_types.extend(argument.removeprefix("--crate-type=").split(","))
        importable = "--test" not in arguments and any(kind in {"lib", "rlib", "dylib", "proc-macro"} for kind in crate_types)
        command = [driver, "--format=" + os.environ["SHAPELINT_CARGO_FORMAT"]]
        if check_only:
            command.append("--cargo-check-only")
        summaries = Path(os.environ["SHAPELINT_CARGO_SUMMARIES"])
        for index, argument in enumerate(arguments):
            if argument == "--extern":
                _, separator, dependency = arguments[index + 1].partition("=")
                if separator:
                    identity = hashlib.sha256(str(Path(dependency).resolve()).encode()).hexdigest()
                    entry = summaries / (identity + ".json")
                    if entry.exists():
                        command.extend(["--summary-input", str(entry)])
        invocation = uuid.uuid4().hex
        summary = None
        if importable:
            summary = Path(os.environ["SHAPELINT_CARGO_REPORTS"]) / (invocation + ".summary.json")
            command.extend(["--summary-output", str(summary)])
        path = Path(os.environ["SHAPELINT_CARGO_RUN"]) / (invocation + ".jsonl")
        command.extend(["--diagnostics-output", str(path)])
        result = subprocess.run([*command, *arguments], stdout=None if check_only else subprocess.DEVNULL, close_fds=False)
        if result.returncode:
            if path.exists():
                failed = path.with_suffix(".failed.jsonl")
                path.rename(failed)
                failed.with_suffix(".cwd").write_text(str(Path.cwd()))
            return result.returncode
        if "--out-dir" in arguments:
            output = Path(arguments[arguments.index("--out-dir") + 1])
            name = arguments[arguments.index("--crate-name") + 1]
            suffix = next((argument.removeprefix("extra-filename=") for argument in arguments
                           if argument.startswith("extra-filename=")), "")
            publish_reports(output, name, suffix, Path(os.environ["SHAPELINT_CARGO_REPORTS"]),
                            path, Path.cwd(), invocation)
        if summary is not None and "--out-dir" in arguments:
            output = Path(arguments[arguments.index("--out-dir") + 1])
            name = arguments[arguments.index("--crate-name") + 1]
            suffix = ""
            for argument in arguments:
                if argument.startswith("extra-filename="):
                    suffix = argument.removeprefix("extra-filename=")
            for extension in ("rmeta", "rlib"):
                artifact = output / ("lib" + name + suffix + "." + extension)
                if artifact.exists():
                    identity = hashlib.sha256(str(artifact.resolve()).encode()).hexdigest()
                    destination = summaries / (identity + ".json")
                    temporary = summaries / (identity + "." + invocation + ".json")
                    shutil.copyfile(summary, temporary)
                    temporary.replace(destination)
        return 0

    parser = argparse.ArgumentParser(
        description="Run MIR shapelint on a Cargo workspace, including test targets, without running tests."
    )
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.add_argument("--color", choices=("auto", "always", "never"), default="auto")
    parser.add_argument("--manifest-path", type=Path,
                        help="Cargo manifest to analyze (defaults to Shapelint's workspace)")
    options = parser.parse_args()

    script = Path(__file__).resolve()
    compiler = script.parent
    root = compiler.parent
    manifest = (options.manifest_path or root / "Cargo.toml").resolve()
    environment = os.environ.copy()
    color = options.color
    if color == "auto":
        if environment.get("NO_COLOR"):
            color = "never"
        elif environment.get("CLICOLOR_FORCE") or sys.stdout.isatty():
            color = "always"
        else:
            color = "never"
    # Cargo captures the wrapper's stdout, so terminal detection must happen here.
    environment["SHAPELINT_CARGO_COLOR"] = color
    environment["SHAPELINT_CARGO_FORMAT"] = "record-json" if options.format == "json" else "record"
    for key in ("RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN"):
        environment.pop(key, None)
    rustup = shutil.which("rustup")
    if rustup is None:
        parser.error("rustup must be on PATH")

    # Resolve tools in compiler/ so rustup reads the checked-in toolchain file.
    tools = {}
    for name in ("cargo", "rustc", "rustdoc"):
        tools[name] = subprocess.check_output(
            [rustup, "which", name], cwd=compiler, env=environment, text=True
        ).strip()
    environment["RUSTC"] = tools["rustc"]
    environment["RUSTDOC"] = tools["rustdoc"]
    environment["RUSTC_BOOTSTRAP"] = "1"
    metadata = json.loads(subprocess.check_output(
        [tools["cargo"], "metadata", "--no-deps", "--format-version=1",
         "--manifest-path", str(manifest)], cwd=manifest.parent, env=environment, text=True,
    ))
    workspace = Path(metadata["workspace_root"])
    target = compiler / "target"
    subprocess.run(
        [tools["cargo"], "build", "--release", "--manifest-path", str(compiler / "Cargo.toml"),
         "--target-dir", str(target)],
        cwd=root, env=environment, check=True,
    )

    environment["SHAPELINT_CARGO_DRIVER"] = str(target / "release" / "shapelint-driver")
    artifacts = compiler / "artifacts"
    invocation = artifacts / "runs" / uuid.uuid4().hex
    invocation.mkdir(parents=True)
    identity = configuration_identity(Path(environment["SHAPELINT_CARGO_DRIVER"]), script, {
        "format": environment["SHAPELINT_CARGO_FORMAT"], "color": color,
    })
    configuration = artifacts / "configurations" / identity
    configuration.mkdir(parents=True, exist_ok=True)
    wrapper = configuration / "wrapper.py"
    try:
        wrapper.symlink_to(script)
    except FileExistsError:
        pass
    # Cargo hashes this path for workspace crates, leaving dependency artifacts reusable.
    environment["CARGO_TARGET_DIR"] = str(artifacts / "target")
    environment["RUSTC_WORKSPACE_WRAPPER"] = str(wrapper)
    environment["RUSTC_WRAPPER"] = str(script)
    environment["SHAPELINT_CARGO_ROOT"] = str(workspace)
    summaries = configuration / "summaries"
    summaries.mkdir(parents=True, exist_ok=True)
    environment["SHAPELINT_CARGO_SUMMARIES"] = str(summaries)
    cached_reports = configuration / "reports"
    cached_reports.mkdir(parents=True, exist_ok=True)
    environment["SHAPELINT_CARGO_REPORTS"] = str(cached_reports)
    directory = invocation / "workspace"
    directory.mkdir()
    environment["SHAPELINT_CARGO_RUN"] = str(directory)
    command = [tools["cargo"], "check", "--workspace", "--all-targets",
               "--manifest-path", str(manifest),
               "--message-format=json-diagnostic-rendered-ansi" if color == "always" else "--message-format=json"]
    returncode, reports, missing = check_workspace(
        command, workspace, environment, directory, cached_reports, configuration, sys.stderr
    )
    for source in missing:
        print(f"shapelint-check: no cached report for Cargo target {source}", file=sys.stderr)
    aggregate_cache = configuration / "aggregates"
    aggregate_cache.mkdir(parents=True, exist_ok=True)
    emit_report(reports, options.format, aggregate_cache, sys.stdout)
    status = int(bool(returncode or missing))
    return status


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"shapelint-check: {error}", file=sys.stderr)
        sys.exit(1)
