import contextlib
import importlib.util
import io
import json
import random
from pathlib import Path
import tempfile
import unittest
from unittest import mock


spec = importlib.util.spec_from_file_location("shapelint_check", Path(__file__).parents[1] / "check.py")
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class ReportTest(unittest.TestCase):
    def test_single_impl_finding_is_removed_when_another_target_has_an_impl(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first = root / "first.jsonl"
            second = root / "second.jsonl"
            identity = [11, 22]
            finding = {
                "path": "src/lib.rs",
                "fingerprint": "single",
                "rule": "single-impl-trait",
                "primary": {"span": {"start": 4, "end": 8}},
            }
            header = {"record": "header", "version": 2}
            trait = {"identity": identity, "path": "src/lib.rs",
                     "span": {"start": 4, "end": 8}}
            first.write_text("".join([
                json.dumps(header) + "\n",
                json.dumps({"record": "workspace", "facts": {
                    "traits": [trait],
                    "implementations": [{"trait_identity": identity, "path": "src/lib.rs",
                                          "span": {"start": 20, "end": 40}},
                                         ],
                }}) + "\n",
                json.dumps(finding) + "\n",
            ]))
            second.write_text("".join([
                json.dumps(header) + "\n",
                json.dumps({"record": "workspace", "facts": {
                    "traits": [],
                    "implementations": [{"trait_identity": identity, "path": "tests/fake.rs",
                                          "span": {"start": 10, "end": 30}},
                                         ],
                }}) + "\n",
            ]))
            output = io.StringIO()
            check.report([(root, first), (root, second)], "json", output)
            self.assertEqual("", output.getvalue())

    def test_single_impl_finding_remains_for_one_workspace_implementation(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            report = root / "report.jsonl"
            identity = [11, 22]
            finding = {
                "path": "src/lib.rs",
                "fingerprint": "single",
                "rule": "single-impl-trait",
                "primary": {"span": {"start": 4, "end": 8}},
            }
            report.write_text("".join([
                json.dumps({"record": "header", "version": 2}) + "\n",
                json.dumps({"record": "workspace", "facts": {
                    "traits": [{"identity": identity, "path": "src/lib.rs",
                                "span": {"start": 4, "end": 8}}],
                    "implementations": [{"trait_identity": identity, "path": "src/lib.rs",
                                          "span": {"start": 20, "end": 40}},
                                         ],
                }}) + "\n",
                json.dumps(finding) + "\n",
            ]))
            output = io.StringIO()
            check.report([(root, report)], "json", output)
            self.assertEqual([finding], [json.loads(output.getvalue())])

    def test_transports_deduplicate_normalized_paths_and_preserve_output(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first = root / "first"
            second = root / "second"
            first.mkdir()
            second.mkdir()
            finding = {
                "path": "../source.rs",
                "fingerprint": "first",
                "primary": {"span": {"start": 2}},
                "rule": "example",
                "related": [{"input": {"name": "../other.rs", "text": "first\nsecond\n"}, "label": "related"}],
            }
            duplicate = dict(finding, fingerprint="second")
            rendered = "\x1b[31mexample\x1b[0m\nfirst\nsecond\n"
            reports = []
            for format in ("json", "text"):
                paths = []
                for index, (directory, item) in enumerate(((first, finding), (second, duplicate))):
                    path = root / f"{format}-{index}.jsonl"
                    record = item if format == "json" else {"finding": item, "rendered": rendered}
                    path.write_text(json.dumps(record) + "\n")
                    paths.append((directory, path))
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    check.report(paths, format)
                reports.append(output.getvalue())
            self.assertEqual([finding], [json.loads(line) for line in reports[0].splitlines()])
            self.assertEqual(rendered, reports[1])

    def test_optimized_report_matches_full_serialization_oracle(self):
        rng = random.Random(84)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directories = [root / "one", root / "two"]
            for directory in directories:
                directory.mkdir()
            reports = []
            findings = []
            texts = ["", "prefix", "prefix\nlate", "unicode λ\n\"slash\\", "line\n" * 30]
            for index in range(80):
                directory = directories[index % 2]
                finding = {"path": "../shared.rs", "fingerprint": str(index % 9),
                           "primary": {"span": {"start": index % 2}}, "rule": "example",
                           "detail": rng.choice(texts)}
                if index % 3:
                    finding["related"] = [{"input": {"name": "../other.rs", "text": rng.choice(texts),
                                                        "extra": {"n": index % 2}},
                                           "label": {"message": rng.choice(texts)}}]
                elif index % 2:
                    finding["related"] = []
                findings.append((directory, finding))
                path = root / (str(index) + ".jsonl")
                item = finding if index % 2 else {"finding": finding, "rendered": "unused"}
                path.write_text(json.dumps(item) + "\n")
                reports.append((directory, path))
            for index, source in enumerate((
                {"name": "../other.rs", "text": "same", "extra": {"a": 1, "b": 2}},
                {"extra": {"b": 2, "a": 1}, "text": "same", "name": "../other.rs"},
            )):
                finding = {"path": "../shared.rs", "fingerprint": "ordered", "rule": "ordered",
                           "primary": {"span": {"start": index + 10}},
                           "related": [{"input": source, "label": "label"}]}
                path = root / ("ordered" + str(index) + ".jsonl")
                path.write_text(json.dumps(finding) + "\n")
                findings.append((directories[0], finding))
                reports.append((directories[0], path))
            expected = {}
            for directory, finding in findings:
                identity = dict(finding)
                identity.pop("fingerprint")
                identity["path"] = str((directory / finding["path"]).resolve())
                if finding.get("related"):
                    related = []
                    for location in finding["related"]:
                        source = dict(location["input"])
                        source["name"] = str((directory / source["name"]).resolve())
                        related.append({"input": source, "label": location["label"]})
                    identity["related"] = related
                expected.setdefault(json.dumps(identity, sort_keys=True), finding)
            expected = sorted(expected.values(), key=lambda finding: (
                finding["path"], finding["primary"]["span"]["start"], finding["rule"],
                json.dumps(finding, sort_keys=True)))
            output = io.StringIO()
            check.report(reports, "json", output)
            self.assertEqual("".join(json.dumps(item) + "\n" for item in expected), output.getvalue())

    def test_shared_source_stream_preserves_related_sources(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = {"name": "other.rs", "text": "λ\n" * 1000}
            findings = [{"path": "main.rs", "fingerprint": str(index), "rule": "example",
                         "primary": {"span": {"start": index}}} for index in range(32)]
            records = [{"record": "header", "version": 2},
                       {"record": "source", "id": 0, "input": source}]
            records.extend({"record": "finding", "finding": item,
                            "related": [{"source": 0, "label": "origin"}]}
                           for item in findings)
            path = root / "report.jsonl"
            path.write_text("".join(json.dumps(record) + "\n" for record in records))
            output = io.StringIO()
            with mock.patch.object(check, "freeze_json", wraps=check.freeze_json) as freeze:
                check.report([(root, path)], "json", output)
                # Source traversal happens at declaration, never once per reference.
                self.assertLess(freeze.call_count, len(findings))
            expected = [dict(item, related=[{"input": source, "label": "origin"}]) for item in findings]
            self.assertEqual(expected, [json.loads(line) for line in output.getvalue().splitlines()])

    def test_stream_comparator_matches_full_json_order(self):
        values = ["", "a", "a\n", "a\"", "λ", "a" * 10000 + "x", "a" * 10000 + "y",
                  {"a": ["x", {"b": "\\"}]}, {"a": ["x", {"b": "\n"}]}]
        for left in values:
            for right in values:
                a, b = json.dumps(left, sort_keys=True), json.dumps(right, sort_keys=True)
                expected = (a > b) - (a < b)
                self.assertEqual(expected, check.compare_json(left, right))


class CargoReuseTest(unittest.TestCase):
    def test_configuration_identity_tracks_driver_wrapper_and_options(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            driver, wrapper = root / "driver", root / "wrapper"
            driver.write_bytes(b"driver")
            wrapper.write_bytes(b"wrapper")
            options = {"format": "json", "color": "never", "scope": "library",
                       "enforcement": "report", "analysis_gaps": "hide"}
            original = check.configuration_identity(driver, wrapper, options)
            self.assertEqual(original, check.configuration_identity(driver, wrapper, options))
            for key in options:
                changed = dict(options, **{key: "different"})
                self.assertNotEqual(original, check.configuration_identity(driver, wrapper, changed))
            wrapper.write_bytes(b"changed")
            self.assertNotEqual(original, check.configuration_identity(driver, wrapper, options))
            wrapper.write_bytes(b"wrapper")
            driver.write_bytes(b"changed")
            self.assertNotEqual(original, check.configuration_identity(driver, wrapper, options))

    def test_current_artifacts_only_and_missing_reports(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            reports = root / "reports"
            reports.mkdir()
            artifact = root / "current.rmeta"
            cached = root / "cached.jsonl"
            cached.write_text("cached")
            index = reports / (check.artifact_key(artifact) + ".json")
            index.write_text(json.dumps({"directory": str(root / "producer"), "report": str(cached)}))
            (reports / "removed.jsonl").write_text("stale")
            message = {"reason": "compiler-artifact", "fresh": True,
                       "target": {"src_path": str(root / "lib.rs")},
                       "filenames": [str(artifact)]}
            selected, missing = check.select_reports([message], root, reports)
            self.assertEqual([(root / "producer", cached)], selected)
            self.assertEqual([], missing)
            self.assertEqual(([], []), check.select_reports([], root, reports))
            index.unlink()
            selected, missing = check.select_reports([message], root, reports)
            self.assertEqual([], selected)
            self.assertEqual([str((root / "lib.rs").resolve())], missing)
            message["target"]["src_path"] = str(root.parent / "dependency.rs")
            self.assertEqual(([], []), check.select_reports([message], root, reports))

    def test_rebuilt_target_rejects_old_report(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            reports = root / "reports"
            reports.mkdir()
            run = root / "run"
            run.mkdir()
            artifact = root / "unit.rmeta"
            old = root / "old.jsonl"
            old.write_text("stale")
            index = reports / (check.artifact_key(artifact) + ".json")
            index.write_text(json.dumps({"directory": str(root), "report": str(old)}))
            message = {"reason": "compiler-artifact", "fresh": False,
                       "target": {"src_path": str(root / "lib.rs")}, "filenames": [str(artifact)]}
            self.assertEqual(([], [str((root / "lib.rs").resolve())]),
                             check.select_reports([message], root, reports, run))
            message["fresh"] = True
            self.assertEqual(([(root, old)], []), check.select_reports([message], root, reports, run))

    def test_symlinked_root_and_missing_report_are_handled(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            actual = root / "actual"
            actual.mkdir()
            alias = root / "alias"
            alias.symlink_to(actual, target_is_directory=True)
            reports = root / "reports"
            reports.mkdir()
            artifact = root / "unit.rmeta"
            index = reports / (check.artifact_key(artifact) + ".json")
            index.write_text(json.dumps({"directory": str(actual), "report": str(root / "missing")}))
            message = {"reason": "compiler-artifact", "target": {"src_path": str(actual / "lib.rs")},
                       "filenames": [str(artifact)]}
            selected, missing = check.select_reports([message], alias, reports)
            self.assertEqual([], selected)
            self.assertEqual([str((actual / "lib.rs").resolve())], missing)

    def test_workspace_lock_covers_cargo_and_report_selection(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            run = root / "run"
            run.mkdir()
            reports = root / "reports"
            reports.mkdir()
            artifact = root / "unit.rmeta"
            report = run / "unit.jsonl"
            report.write_text("")
            artifact.touch()
            check.publish_reports(root, "unit", "", reports, report, root, "two")
            message = {"reason": "compiler-artifact", "fresh": False,
                       "target": {"src_path": str(root / "lib.rs")}, "filenames": [str(artifact)]}
            original_select = check.select_reports

            def assert_locked():
                with (root / "lock").open("a") as competing:
                    with self.assertRaises(BlockingIOError):
                        check.fcntl.flock(competing, check.fcntl.LOCK_EX | check.fcntl.LOCK_NB)

            def cargo(*args, **kwargs):
                assert_locked()
                return mock.Mock(stdout=json.dumps(message) + "\n", returncode=0)

            def select(*args, **kwargs):
                assert_locked()
                return original_select(*args, **kwargs)

            with mock.patch.object(check.subprocess, "run", side_effect=cargo), \
                 mock.patch.object(check, "select_reports", side_effect=select):
                self.assertEqual((0, [(root, report)], []),
                                 check.check_workspace(["cargo"], root, {}, run, reports, root, io.StringIO()))
            with (root / "lock").open("a") as competing:
                check.fcntl.flock(competing, check.fcntl.LOCK_EX | check.fcntl.LOCK_NB)

    def test_publication_matches_exact_artifact_and_preserves_producer(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            output = root / "output"
            output.mkdir()
            reports = root / "reports"
            reports.mkdir()
            report = root / "empty.jsonl"
            report.write_text("")
            owned = output / "libfoo.rmeta"
            other = output / "libbarfoo.rmeta"
            depfile = output / "libfoo.d"
            for path in (owned, other, depfile):
                path.touch()
            check.publish_reports(output, "foo", "", reports, report, root / "producer", "one")
            entry = json.loads((reports / (check.artifact_key(owned) + ".json")).read_text())
            self.assertEqual({"directory": str(root / "producer"), "report": str(report)}, entry)
            self.assertFalse((reports / (check.artifact_key(other) + ".json")).exists())
            self.assertFalse((reports / (check.artifact_key(depfile) + ".json")).exists())
            check.publish_reports(output, "build_script_build", "-hash", reports, report, root, "two")
            alias = output / ("build-script-build.exe" if check.os.name == "nt" else "build-script-build")
            self.assertTrue((reports / (check.artifact_key(alias) + ".json")).exists())

    def test_aggregate_cache_reuses_selected_immutable_generations(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            cache = root / "cache"
            cache.mkdir()
            report = root / "report.jsonl"
            finding = {"path": "source.rs", "fingerprint": "example",
                       "primary": {"span": {"start": 0}}, "rule": "example"}
            report.write_text(json.dumps(finding) + "\n")
            first = io.StringIO()
            check.emit_report([(root, report)], "json", cache, first)
            report.unlink()
            second = io.StringIO()
            check.emit_report([(root, report)], "json", cache, second)
            self.assertEqual(first.getvalue(), second.getvalue())
            empty = io.StringIO()
            check.emit_report([], "json", cache, empty)
            self.assertEqual("", empty.getvalue())
            self.assertEqual(2, len(list(cache.iterdir())))

    def test_cargo_diagnostics_are_forwarded_and_artifacts_selected(self):
        rendered = "\x1b[31merror\x1b[0m\n"
        artifact = {"reason": "compiler-artifact", "fresh": True}
        lines = [json.dumps({"reason": "compiler-message", "message": {"rendered": rendered}}),
                 json.dumps(artifact), "plain output\n"]
        output = io.StringIO()
        self.assertEqual([artifact], check.cargo_messages(lines, output))
        self.assertEqual(rendered + "plain output\n", output.getvalue())


if __name__ == "__main__":
    unittest.main()
