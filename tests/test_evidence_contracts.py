"""Source identity checks keep missing history and changed Ada observable."""
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


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr")
def test_current_source_returns_its_nonempty_absolute_path(tmp_path):
    relative = "verification/verify_evidence.py"
    current = ROOT.joinpath(relative)
    expected = hashlib.sha256(current.read_bytes()).hexdigest()
    result = auditor.evidence_source(relative, expected, tmp_path.joinpath("unused.json"))
    assert result == str(current)
    assert Path(result).is_absolute()


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr")
def test_changed_ada_cannot_use_historical_python_fallback(tmp_path):
    with pytest.raises(ValueError, match="Proof source changed"):
        auditor.evidence_source("analyses/hoeflin-ferguson/ada/src/hoeflin_core.ads",
                                "0" * 64, tmp_path.joinpath("unused.json"))


@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_missing_historical_git_object_has_an_explicit_error(tmp_path):
    relative = "verification/verify_evidence.py"
    history = tmp_path.joinpath("history.json")
    history.write_text(json.dumps({"files": [{"path": relative, "sha256": "0" * 64,
                                             "git_blob": "0" * 40}]}))
    with pytest.raises(ValueError, match="Historical Git object is missing"):
        auditor.evidence_source(relative, "0" * 64, history, tmp_path.joinpath("missing.git"))


@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_malformed_source_history_preserves_json_decode_error(tmp_path):
    history = tmp_path.joinpath("history.json")
    history.write_text("{")
    with pytest.raises(json.JSONDecodeError):
        auditor.evidence_source("verification/verify_evidence.py", "0" * 64, history)


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


@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_explicit_source_tree_does_not_allow_an_ada_hash_mismatch(tmp_path):
    relative = "historical_kernel.ads"
    tmp_path.joinpath(relative).write_text("package Historical_Kernel is end Historical_Kernel;\n")
    with pytest.raises(ValueError, match="Proof source changed"):
        auditor.evidence_source(relative, "0" * 64, tmp_path.joinpath("unused.json"),
                                source_root=tmp_path)


@deal.post(lambda result: isinstance(result, dict)
           and set(result["projects"]) == set(auditor.PROJECTS)
           and result["coverage_schema"] == "gnat13-sloc-v1")
@deal.raises()
@deal.has()
def coverage_manifest() -> dict:
    return {"coverage_schema": "gnat13-sloc-v1", "projects": {
        name: {"portfolio": {"coverage": {}, "required_full_entities": sorted(required)}}
        for name, required in auditor.REQUIRED_BODIES.items()}}


@deal.post(lambda result: result is None)
@deal.has()
def test_complete_policy_requires_both_projects_and_all_required_bodies():
    assert auditor.campaign_policy(coverage_manifest(), "expanded-campaign", False)
    return None


@pytest.mark.parametrize("campaign,explicit", [
    ("computer10-20261031", False), ("deal-spark-computer10-20261031", False),
    ("deal-lint-spark-computer10-20261031", False),
    ("spark-expanded-computer10-20261031", False),
    ("spark-expanded-computer10-20261031", True), ("unknown-campaign", True)])
@deal.post(lambda result: result is None)
@deal.has()
def test_schema_downgrade_cannot_pass_for_current_or_unrecognized_campaign(campaign, explicit):
    with pytest.raises(ValueError, match="coverage schema is required"):
        auditor.campaign_policy({"projects": {}}, campaign, explicit)
    return None


@pytest.mark.parametrize("campaign", sorted(auditor.LEGACY_CAMPAIGNS))
@deal.post(lambda result: result is None)
@deal.has()
def test_known_legacy_campaign_allows_only_explicit_historical_context(campaign):
    assert auditor.campaign_policy({"projects": {}}, campaign, True) is False
    return None


@pytest.mark.parametrize("change", ["omit", "add"])
@deal.post(lambda result: result is None)
@deal.has()
def test_coverage_campaign_cannot_change_production_project_inventory(change):
    manifest = coverage_manifest()
    if change == "omit":
        del manifest["projects"]["towers"]
    else:
        manifest["projects"]["unrelated"] = manifest["projects"]["towers"]
    with pytest.raises(ValueError, match="Production project inventory"):
        auditor.campaign_policy(manifest, "expanded-campaign", False)
    return None


@deal.post(lambda result: result is None)
@deal.has()
def test_coverage_campaign_requires_a_portfolio_for_each_project():
    manifest = coverage_manifest()
    manifest["projects"]["towers"] = {}
    with pytest.raises(ValueError, match="Required portfolio is missing"):
        auditor.campaign_policy(manifest, "expanded-campaign", False)
    return None


@pytest.mark.parametrize("change", ["omit", "replace", "duplicate"])
@deal.post(lambda result: result is None)
@deal.has()
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


@deal.post(lambda result: result is None)
@deal.has()
def test_coverage_campaign_cannot_omit_raw_coverage_record():
    manifest = coverage_manifest()
    del manifest["projects"]["hoeflin"]["portfolio"]["coverage"]
    with pytest.raises(ValueError, match="Native SPARK coverage is missing"):
        auditor.campaign_policy(manifest, "expanded-campaign", False)
    return None


@deal.post(lambda result: result is None)
@deal.has()
def test_unknown_coverage_schema_cannot_pass_even_for_legacy_campaign():
    manifest = coverage_manifest()
    manifest["coverage_schema"] = "unknown"
    with pytest.raises(ValueError, match="Unknown native coverage schema"):
        auditor.campaign_policy(manifest, "computer10-20261031", True)
    return None


@pytest.mark.parametrize("change,message", [
    ("schema", "coverage schema is required"),
    ("project", "Production project inventory"),
    ("body", "Required-body inventory differs")])
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall")
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
