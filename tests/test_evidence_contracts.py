"""Source identity checks keep missing history and changed Ada observable."""
from conftest import protected_history_intact, reference_inputs_intact
import hashlib
import json
from pathlib import Path
import subprocess
from subprocess import CalledProcessError, TimeoutExpired
import sys

import deal
import pytest

from conftest import ROOT
from verification import verify_evidence as auditor


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr")
def test_current_source_returns_its_nonempty_absolute_path(tmp_path):
    relative = "verification/verify_evidence.py"
    current = ROOT.joinpath(relative)
    expected = hashlib.sha256(current.read_bytes()).hexdigest()
    result = auditor.evidence_source(relative, expected, tmp_path.joinpath("unused.json"))
    assert result == str(current)
    assert Path(result).is_absolute()


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr")
def test_changed_ada_cannot_use_historical_python_fallback(tmp_path):
    with pytest.raises(ValueError, match="Proof source changed"):
        auditor.evidence_source("analyses/hoeflin-ferguson/ada/src/hoeflin_core.ads",
                                "0" * 64, tmp_path.joinpath("unused.json"))


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_missing_historical_git_object_has_an_explicit_error(tmp_path):
    relative = "verification/verify_evidence.py"
    history = tmp_path.joinpath("history.json")
    history.write_text(json.dumps({"files": [{"path": relative, "sha256": "0" * 64,
                                             "git_blob": "0" * 40}]}))
    with pytest.raises(ValueError, match="Historical Git object is missing"):
        auditor.evidence_source(relative, "0" * 64, history, tmp_path.joinpath("missing.git"))


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_malformed_source_history_preserves_json_decode_error(tmp_path):
    history = tmp_path.joinpath("history.json")
    history.write_text("{")
    with pytest.raises(json.JSONDecodeError):
        auditor.evidence_source("verification/verify_evidence.py", "0" * 64, history)


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_optimized_auditor_cli_keeps_json_failure_observable(tmp_path):
    history = tmp_path.joinpath("history.json")
    history.write_text("{")
    source_root = tmp_path.joinpath("historical-source")
    runner = source_root.joinpath("verification/run_computer10.py")
    runner.parent.mkdir(parents=True)
    runner.write_text("historical_runner_marker = True\n")
    process = subprocess.run([sys.executable, "-O", str(ROOT.joinpath("verification/verify_evidence.py")),
                              str(ROOT.joinpath("verification/evidence/computer10-20261031")),
                              "--source-history", str(history), "--source-root", str(source_root)],
                              capture_output=True, text=True, timeout=15)
    assert process.returncode != 0
    assert "JSONDecodeError" in process.stderr
    assert "RaisesContractError" not in process.stderr


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_historical_ada_requires_an_explicit_matching_source_tree(tmp_path):
    relative = "historical_kernel.ads"
    source = tmp_path.joinpath(relative)
    source.write_text("package Historical_Kernel with SPARK_Mode is end Historical_Kernel;\n")
    expected = hashlib.sha256(source.read_bytes()).hexdigest()
    result = auditor.evidence_source(relative, expected, tmp_path.joinpath("unused.json"),
                                     source_root=tmp_path)
    assert result == str(source)
    with pytest.raises(ValueError, match="Proof source is missing"):
        auditor.evidence_source(relative, expected, tmp_path.joinpath("unused.json"))


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_explicit_source_tree_does_not_allow_an_ada_hash_mismatch(tmp_path):
    relative = "historical_kernel.ads"
    tmp_path.joinpath(relative).write_text("package Historical_Kernel is end Historical_Kernel;\n")
    with pytest.raises(ValueError, match="Proof source changed"):
        auditor.evidence_source(relative, "0" * 64, tmp_path.joinpath("unused.json"),
                                source_root=tmp_path)


@deal.pre(protected_history_intact)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.post(lambda result: isinstance(result, dict)
           and set(result["projects"]) == set(auditor.PROJECTS)
           and result["coverage_schema"] == "gnat13-sloc-v1")
@deal.raises()
@deal.has("read")
def coverage_manifest() -> dict:
    return {"symbolic_schema": auditor.SYMBOLIC_SCHEMA,
            "symbolic_report": "symbolic/result.json", "symbolic_report_sha256": "5" * 64,
            "symbolic_checker_sha256": "6" * 64,
            "contract_floor_schema": auditor.CONTRACT_SCHEMA, "minimum_contracts": 5,
            "python_contracts_sha256": "2" * 64, "contract_checker_sha256": "3" * 64,
            "python_checker_sha256": "4" * 64, "coverage_schema": "gnat13-sloc-v1", "ghost_boundary_schema": auditor.GHOST_SCHEMA,
            "ghost_registry_sha256": "1" * 64, "ghost_negative_control": {}, "projects": {
        name: {"portfolio": {"coverage": {}, "ghost_boundaries": {}, "contract_floor": {"complete": True}, "required_full_entities": sorted(required)}}
        for name, required in auditor.REQUIRED_BODIES.items()}}


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_complete_policy_requires_both_projects_and_all_required_bodies():
    assert auditor.campaign_policy(coverage_manifest(), "expanded-campaign", False)
    return None


@pytest.mark.parametrize("campaign,explicit", [
    ("computer10-20261031", False), ("deal-spark-computer10-20261031", False),
    ("deal-lint-spark-computer10-20261031", False),
    ("spark-expanded-computer10-20261031", False),
    ("spark-expanded-computer10-20261031", True), ("unknown-campaign", True)])
@deal.pre(lambda campaign, explicit: protected_history_intact())
@deal.ensure(lambda campaign, explicit, *, result: protected_history_intact())
@deal.ensure(lambda campaign, explicit, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_schema_downgrade_cannot_pass_for_current_or_unrecognized_campaign(campaign, explicit):
    with pytest.raises(ValueError, match="coverage schema is required"):
        auditor.campaign_policy({"projects": {}}, campaign, explicit)
    return None


@pytest.mark.parametrize("campaign", sorted(auditor.LEGACY_CAMPAIGNS))
@deal.pre(lambda campaign: protected_history_intact())
@deal.ensure(lambda campaign, *, result: protected_history_intact())
@deal.ensure(lambda campaign, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_known_legacy_campaign_allows_only_explicit_historical_context(campaign):
    assert auditor.campaign_policy({"projects": {}}, campaign, True) is False
    return None


@pytest.mark.parametrize("change", ["omit", "add"])
@deal.pre(lambda change: protected_history_intact())
@deal.ensure(lambda change, *, result: protected_history_intact())
@deal.ensure(lambda change, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_coverage_campaign_cannot_change_production_project_inventory(change):
    manifest = coverage_manifest()
    if change == "omit":
        del manifest["projects"]["towers"]
    else:
        manifest["projects"]["unrelated"] = manifest["projects"]["towers"]
    with pytest.raises(ValueError, match="Production project inventory"):
        auditor.campaign_policy(manifest, "expanded-campaign", False)
    return None


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_coverage_campaign_requires_a_portfolio_for_each_project():
    manifest = coverage_manifest()
    manifest["projects"]["towers"] = {}
    with pytest.raises(ValueError, match="Required portfolio is missing"):
        auditor.campaign_policy(manifest, "expanded-campaign", False)
    return None


@pytest.mark.parametrize("change", ["omit", "replace", "duplicate"])
@deal.pre(lambda change: protected_history_intact())
@deal.ensure(lambda change, *, result: protected_history_intact())
@deal.ensure(lambda change, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_coverage_campaign_cannot_weaken_required_body_inventory(change):
    manifest = coverage_manifest()
    required = manifest["projects"]["hoeflin"]["portfolio"]["required_full_entities"]
    if change == "omit":
        required.pop()
    elif change == "replace":
        required[-1] = "Unrelated.Body"
    else:
        required[-1] = required[0]
    with pytest.raises(ValueError, match="Required-body inventory differs"):
        auditor.campaign_policy(manifest, "expanded-campaign", False)
    return None


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_coverage_campaign_cannot_omit_raw_coverage_record():
    manifest = coverage_manifest()
    del manifest["projects"]["hoeflin"]["portfolio"]["coverage"]
    with pytest.raises(ValueError, match="Native SPARK coverage is missing"):
        auditor.campaign_policy(manifest, "expanded-campaign", False)
    return None


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_unknown_coverage_schema_cannot_pass_even_for_legacy_campaign():
    manifest = coverage_manifest()
    manifest["coverage_schema"] = "unknown"
    with pytest.raises(ValueError, match="Unknown native coverage schema"):
        auditor.campaign_policy(manifest, "computer10-20261031", True)
    return None


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_expanded_historical_policy_requires_explicit_context_and_original_bodies():
    manifest = coverage_manifest()
    del manifest["ghost_boundary_schema"]
    for name, required in auditor.BASE_REQUIRED_BODIES.items():
        manifest["projects"][name]["portfolio"]["required_full_entities"] = sorted(required)
    assert auditor.campaign_policy(manifest, "spark-expanded-computer10-20261031", True)
    with pytest.raises(ValueError, match="Ghost boundary schema is required"):
        auditor.campaign_policy(manifest, "spark-expanded-computer10-20261031", False)
    with pytest.raises(ValueError, match="Ghost boundary schema is required"):
        auditor.campaign_policy(manifest, "new-campaign", True)
    return None


@pytest.mark.parametrize("change,message", [
    ("missing-schema", "Ghost boundary schema is required"),
    ("unknown-schema", "Unknown ghost boundary schema"),
    ("missing-hash", "Ghost registry hash is invalid"),
    ("missing-control", "Ghost negative control is missing"),
    ("missing-result", "Ghost boundary result is missing")])
@deal.pre(lambda change, message: protected_history_intact())
@deal.ensure(lambda change, message, *, result: protected_history_intact())
@deal.ensure(lambda change, message, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_ghost_campaign_policy_cannot_drop_modeling_evidence(change, message):
    manifest = coverage_manifest()
    if change == "missing-schema":
        del manifest["ghost_boundary_schema"]
    elif change == "unknown-schema":
        manifest["ghost_boundary_schema"] = "unknown"
    elif change == "missing-hash":
        del manifest["ghost_registry_sha256"]
    elif change == "missing-control":
        del manifest["ghost_negative_control"]
    else:
        del manifest["projects"]["towers"]["portfolio"]["ghost_boundaries"]
    with pytest.raises(ValueError, match=message):
        auditor.campaign_policy(manifest, "ghost-campaign", False)
    return None


@pytest.mark.parametrize("change,message", [
    ("schema", "coverage schema is required"),
    ("project", "Production project inventory"),
    ("body", "Required-body inventory differs")])
@deal.pre(lambda tmp_path, change, message: protected_history_intact())
@deal.ensure(lambda tmp_path, change, message, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, change, message, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("import", "read", "write", "syscall")
def test_full_auditor_rejects_incomplete_policy_before_source_checks(tmp_path, change, message):
    manifest = coverage_manifest()
    if change == "schema":
        del manifest["coverage_schema"]
    elif change == "project":
        del manifest["projects"]["towers"]
    else:
        manifest["projects"]["hoeflin"]["portfolio"]["required_full_entities"].pop()
    tmp_path.joinpath("manifest.json").write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match=message):
        auditor.verify(tmp_path)


@pytest.mark.parametrize("key", ["contract_floor_schema", "python_contracts_sha256", "contract_checker_sha256", "python_checker_sha256"])
@deal.pre(lambda key: protected_history_intact())
@deal.ensure(lambda key, *, result: protected_history_intact())
@deal.ensure(lambda key, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_current_campaign_requires_contract_floor_identity(key):
    manifest = coverage_manifest()
    del manifest[key]
    with pytest.raises(ValueError, match="[Cc]ontract|Five-contract"):
        auditor.campaign_policy(manifest, "five-contracts-current", False)
    return None


@deal.pre(protected_history_intact)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_current_campaign_rejects_missing_spark_contract_floor():
    manifest = coverage_manifest()
    del manifest["projects"]["hoeflin"]["portfolio"]["contract_floor"]
    with pytest.raises(ValueError, match="SPARK contract floor"):
        auditor.campaign_policy(manifest, "five-contracts-current", False)
    return None


@pytest.mark.parametrize("key", ["symbolic_schema", "symbolic_report", "symbolic_report_sha256", "symbolic_checker_sha256"])
@deal.pre(lambda key: protected_history_intact())
@deal.ensure(lambda key, *, result: protected_history_intact())
@deal.ensure(lambda key, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_current_campaign_requires_symbolic_proof_identity(key):
    manifest = coverage_manifest()
    del manifest[key]
    with pytest.raises(ValueError, match="[Ss]ymbolic"):
        auditor.campaign_policy(manifest, "symbolic-current", False)
    return None


@pytest.mark.parametrize("change", ["unknown-schema", "path", "hash"])
@deal.pre(lambda change: protected_history_intact())
@deal.ensure(lambda change, *, result: protected_history_intact())
@deal.ensure(lambda change, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_symbolic_campaign_rejects_unknown_or_unsafe_metadata(change):
    manifest = coverage_manifest()
    if change == "unknown-schema":
        manifest["symbolic_schema"] = "unknown"
    elif change == "path":
        manifest["symbolic_report"] = "../escape.json"
    else:
        manifest["symbolic_checker_sha256"] = "x" * 64
    with pytest.raises(ValueError, match="[Ss]ymbolic"):
        auditor.campaign_policy(manifest, "symbolic-current", False)
    return None


@deal.pre(protected_history_intact)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_five_contract_snapshot_requires_explicit_context_without_symbolic_schema():
    manifest = coverage_manifest()
    del manifest["symbolic_schema"]
    assert auditor.campaign_policy(manifest, "five-contracts-computer10-20261104", True)
    with pytest.raises(ValueError, match="Symbolic verification schema"):
        auditor.campaign_policy(manifest, "five-contracts-computer10-20261104", False)
    with pytest.raises(ValueError, match="Symbolic verification schema"):
        auditor.campaign_policy(manifest, "unknown-current", True)
    return None


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_native_origin_matches_retained_invocation_records(tmp_path):
    original = {"projects": {"hoeflin": {"portfolio": {"native": {"report_sha256": "1" * 64}}}},
                "negative_control": {}, "ghost_negative_control": {}, "toolchain": {},
                "provers_requested": ["z3"], "prover_config_sha256": "2" * 64,
                "runner_sha256": "3" * 64}
    folder = tmp_path.joinpath("verification/evidence/original")
    folder.mkdir(parents=True)
    source = folder.joinpath("manifest.json")
    source.write_text(json.dumps(original))
    manifest = {**original, "native_proof_origin": {
        "campaign": "verification/evidence/original", "revision": "4" * 40,
        "manifest_sha256": auditor.sha(source), "native_reports": {"hoeflin": "1" * 64}}}
    assert auditor.verify_native_origin(manifest, tmp_path) is None
    manifest["provers_requested"] = ["cvc5"]
    with pytest.raises(ValueError, match="differs from its origin"):
        auditor.verify_native_origin(manifest, tmp_path)
    return None


@pytest.mark.parametrize("change,message", [
    ("unsafe", "Unsafe native proof origin"),
    ("hash", "origin manifest changed"),
    ("revision", "origin revision is invalid"),
    ("reports", "origin report inventory differs")])
@deal.pre(lambda tmp_path, change, message: protected_history_intact())
@deal.ensure(lambda tmp_path, change, message, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, change, message, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_native_origin_rejects_unsafe_or_changed_provenance(tmp_path, change, message):
    original = {"projects": {}, "negative_control": {}, "ghost_negative_control": {},
                "toolchain": {}, "provers_requested": [], "prover_config_sha256": "1" * 64,
                "runner_sha256": "2" * 64}
    folder = tmp_path.joinpath("verification/evidence/original")
    folder.mkdir(parents=True)
    source = folder.joinpath("manifest.json")
    source.write_text(json.dumps(original))
    origin = {"campaign": "verification/evidence/original", "revision": "3" * 40,
              "manifest_sha256": auditor.sha(source), "native_reports": {}}
    manifest = {**original, "native_proof_origin": origin}
    if change == "unsafe":
        origin["campaign"] = "verification/evidence/../../../escape"
    elif change == "hash":
        origin["manifest_sha256"] = "0" * 64
    elif change == "revision":
        origin["revision"] = "bad"
    else:
        origin["native_reports"] = {"unexpected": "1" * 64}
    with pytest.raises(ValueError, match=message):
        auditor.verify_native_origin(manifest, tmp_path)
    return None


@pytest.mark.parametrize("change,message", [
    ("valid", None), ("checker", "Symbolic checker source changed"),
    ("report", "Symbolic report changed"), ("input", "Symbolic input source changed"),
    ("outcomes", "Symbolic verification outcomes"), ("flag", "Symbolic verification outcomes"),
    ("normalization", "Symbolic normalized source differs")])
@deal.pre(lambda tmp_path, change, message: protected_history_intact())
@deal.ensure(lambda tmp_path, change, message, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, change, message, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import", "global")
def test_symbolic_record_binds_actual_outcomes_to_selected_sources(tmp_path, change, message):
    from verification.check_symbolic import run
    symbolic = run(ROOT)
    assert symbolic["complete"]
    selected = tmp_path.joinpath("selected")
    for relative in ["verification/check_symbolic.py", "verification/proof_gate.py",
                     "tests/fixtures/contract_negative_control.py"]:
        target = selected.joinpath(relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(ROOT.joinpath(relative).read_bytes())
    folder = tmp_path.joinpath("evidence")
    folder.joinpath("symbolic").mkdir(parents=True)
    path = folder.joinpath("symbolic/result.json")
    if change == "outcomes":
        negative = next(row for item in symbolic["files"] for row in item["theorems"]
                        if row["name"] == "negative_probability")
        negative["conclusion"] = "SKIP"
    if change == "flag":
        symbolic["complete"] = False
    elif change == "normalization":
        symbolic["files"][0]["normalized_sha256"] = "0" * 64
    path.write_text(json.dumps(symbolic))
    manifest = {"symbolic_checker_sha256": auditor.sha(selected.joinpath("verification/check_symbolic.py")),
                "symbolic_report": "symbolic/result.json", "symbolic_report_sha256": auditor.sha(path)}
    if change == "checker":
        selected.joinpath("verification/check_symbolic.py").write_text("changed checker\n")
    elif change == "report":
        path.write_text(path.read_text() + " ")
    elif change == "input":
        selected.joinpath("verification/proof_gate.py").write_text("changed proof input\n")
    if message is None:
        assert auditor.verify_symbolic_record(folder, manifest, selected) is None
    else:
        with pytest.raises(ValueError, match=message):
            auditor.verify_symbolic_record(folder, manifest, selected)
    return None
