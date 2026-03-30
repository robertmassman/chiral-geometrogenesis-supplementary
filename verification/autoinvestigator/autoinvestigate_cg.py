#!/usr/bin/env python3
"""
AutoInvestigator-CG: Autonomous Finding Resolution
=====================================================

Reads FAIL findings from AutoVerifier audit reports, then for each finding:
  1. Investigate — understand the root cause
  2. Fix — make minimal changes to resolve the inconsistency
  3. Verify — confirm the fix resolves the finding without regressions
  4. Keep/Revert — commit if verification passes, revert if not

This tool MODIFIES proof documents. It uses git branch isolation so that
failed fixes can be safely reverted.

Usage:
  python3 verification/autoinvestigator/autoinvestigate_cg.py --group G1 --layer 1
  python3 verification/autoinvestigator/autoinvestigate_cg.py --group G1 --layer 1 --module M9
  python3 verification/autoinvestigator/autoinvestigate_cg.py --group G1 --layer 1 --dry-run
  python3 verification/autoinvestigator/autoinvestigate_cg.py --group G1 --layer 1 --max-parallel 3
  python3 verification/autoinvestigator/autoinvestigate_cg.py --status --group G1 --layer 1
"""

import argparse
import concurrent.futures
import json
import logging
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from pathlib import Path
from typing import Optional

# ── Paths ─────────────────────────────────────────────────────
ROOT = Path(__file__).resolve().parent.parent.parent
AUTOINVESTIGATOR_DIR = Path(__file__).resolve().parent
CONFIG_PATH = AUTOINVESTIGATOR_DIR / "config.json"
PROGRAM_PATH = AUTOINVESTIGATOR_DIR / "program.md"
RESULTS_PATH = AUTOINVESTIGATOR_DIR / "results.tsv"
LOG_PATH = AUTOINVESTIGATOR_DIR / "campaign.log"
REVIEWS_DIR = ROOT / "docs" / "proofs" / "reviews"

# ── Group Metadata (shared with AutoVerifier) ────────────────
GROUP_METADATA = {
    "G1":  {"name": "Geometric Foundation",        "short": "Geometric-Foundation"},
    "G2":  {"name": "Gauge Theory & Confinement",  "short": "Gauge-Confinement"},
    "G3":  {"name": "Time & Entropy",              "short": "Time-Entropy"},
    "G4":  {"name": "Chirality & CP Violation",    "short": "Chirality-CP"},
    "G5":  {"name": "Mass Generation",             "short": "Mass-Generation"},
    "G6":  {"name": "QCD Scale Derivation",        "short": "QCD-Scale"},
    "G7":  {"name": "Quantum Foundations",          "short": "Quantum-Foundations"},
    "G8":  {"name": "Emergent Gravity",            "short": "Emergent-Gravity"},
    "G9":  {"name": "Electroweak Sector",          "short": "Electroweak-Sector"},
    "G10": {"name": "Renormalization & Yang-Mills", "short": "Renorm-YM"},
    "G11": {"name": "Bootstrap & Uniqueness",      "short": "Bootstrap-Uniqueness"},
    "G12": {"name": "Predictions & Falsifiability", "short": "Predictions-Falsifiability"},
}


class ResolutionResult(Enum):
    RESOLVED = "RESOLVED"
    PARTIAL = "PARTIAL"
    SKIPPED = "SKIPPED"
    FAILED = "FAILED"
    ERROR = "ERROR"


@dataclass
class Finding:
    """A single FAIL finding from an audit report."""
    group: str
    layer: int
    module: str
    check_id: str
    description: str
    evidence: str
    severity: str
    report_file: str


@dataclass
class ResolutionOutcome:
    """Result of attempting to resolve a finding."""
    finding: Finding
    result: ResolutionResult = ResolutionResult.ERROR
    summary: str = ""
    files_modified: list = field(default_factory=list)
    duration_seconds: float = 0
    commit_sha: str = ""


# ── Config & Logging ──────────────────────────────────────────

def load_config() -> dict:
    with open(CONFIG_PATH) as f:
        return json.load(f)


def load_program() -> str:
    if PROGRAM_PATH.exists():
        with open(PROGRAM_PATH) as f:
            return f.read()
    return ""


def setup_logging(config: dict) -> logging.Logger:
    logger = logging.getLogger("autoinvestigate-cg")
    logger.setLevel(getattr(logging, config["logging"]["level"].upper()))

    fh = logging.FileHandler(LOG_PATH)
    fh.setLevel(logging.DEBUG)
    fh.setFormatter(logging.Formatter(
        "%(asctime)s [%(levelname)s] %(message)s", datefmt="%Y-%m-%d %H:%M:%S"
    ))
    logger.addHandler(fh)

    ch = logging.StreamHandler()
    ch.setLevel(logging.INFO)
    ch.setFormatter(logging.Formatter(
        "\033[90m%(asctime)s\033[0m %(message)s", datefmt="%H:%M:%S"
    ))
    logger.addHandler(ch)

    return logger


# ── Finding Extraction ────────────────────────────────────────

def extract_json_from_file(filepath: Path) -> Optional[dict]:
    """Extract the last JSON block from a markdown file."""
    if not filepath.exists():
        return None
    text = filepath.read_text()
    json_blocks = re.findall(r'```json\s*\n(.*?)\n\s*```', text, re.DOTALL)
    if json_blocks:
        try:
            return json.loads(json_blocks[-1])
        except json.JSONDecodeError:
            pass
    return None


def _severity_rank(severity: str) -> int:
    """Return numeric rank for severity (lower = more severe)."""
    return {"CRITICAL": 0, "MAJOR": 1, "MODERATE": 2, "MINOR": 3}.get(severity, 99)


def _passes_severity_gate(result: str, severity: str, config: dict) -> bool:
    """Check whether a finding's severity meets the minimum threshold for its result type.

    FAIL findings use min_severity_for_fail (default: MINOR — investigate all).
    WEAK/SMUGGLED/CRACKED findings use per-type thresholds (default: MAJOR —
    only investigate substantive issues, skip cosmetic ones).
    """
    selection = config["finding_selection"]

    # Per-result-type severity gates
    key = f"min_severity_for_{result.lower()}"
    min_sev = selection.get(key, selection.get("min_severity", "MINOR"))

    return _severity_rank(severity) <= _severity_rank(min_sev)


def scan_findings(group_id: str, layer: int, module_filter: Optional[str],
                  config: dict, logger: logging.Logger) -> list[Finding]:
    """Scan all audit reports for a group/layer and extract actionable findings.

    Includes FAIL findings at any severity, plus WEAK/SMUGGLED/CRACKED findings
    that meet the per-type severity threshold (default: MAJOR or above).
    """
    group_dir = REVIEWS_DIR / group_id
    if not group_dir.exists():
        logger.error(f"No reviews directory found: {group_dir}")
        return []

    include_results = set(config["finding_selection"]["include_results"])
    findings = []

    # Find all module report files for this layer
    report_files = sorted(group_dir.glob("*.md"))
    meta = GROUP_METADATA[group_id]

    for rpt in report_files:
        # Match report files by layer
        if layer == 1 and "Coherence" not in rpt.name:
            continue
        if layer == 2 and "Validity" not in rpt.name:
            continue
        if layer == 3 and "Adversarial" not in rpt.name:
            continue

        # Skip synthesis/summary files
        if "Audit" in rpt.name and "Findings" not in rpt.name:
            continue

        # Extract module ID from filename
        module_id = None
        m = re.search(r'-(M\d+|V\d+|A\d+)-', rpt.name)
        if m:
            module_id = m.group(1)
        else:
            continue

        # Apply module filter
        if module_filter and module_id != module_filter:
            continue

        result_json = extract_json_from_file(rpt)
        if not result_json:
            logger.warning(f"  Could not parse JSON from {rpt.name}")
            continue

        for f in result_json.get("findings", []):
            result = f.get("result", "")
            severity = f.get("severity", "MODERATE")
            if result in include_results and _passes_severity_gate(result, severity, config):
                findings.append(Finding(
                    group=group_id,
                    layer=layer,
                    module=module_id,
                    check_id=f.get("check_id", "?"),
                    description=f.get("description", ""),
                    evidence=f.get("evidence", ""),
                    severity=severity,
                    report_file=rpt.name,
                ))

    # Sort by severity (CRITICAL > MAJOR > MODERATE > MINOR)
    findings.sort(key=lambda f: _severity_rank(f.severity))

    return findings


# ── Agent Invocation ──────────────────────────────────────────

def invoke_agent(prompt: str, config: dict, logger: logging.Logger,
                 timeout_minutes: float) -> tuple[str, bool]:
    """Invoke Claude Code CLI. Returns (output, success)."""
    cmd = [config["agent"]["command"]]
    if config["agent"].get("model"):
        cmd.extend(["--model", config["agent"]["model"]])
    for flag in config["agent"].get("flags", []):
        cmd.append(flag)
    cmd.extend(["--max-turns", str(config["agent"].get("max_turns", 50))])
    cmd.extend(["-p", prompt])

    timeout_seconds = int(timeout_minutes * 60)
    logger.debug(f"Invoking agent with timeout={timeout_minutes}min")

    try:
        result = subprocess.run(
            cmd, cwd=ROOT, capture_output=True, text=True,
            timeout=timeout_seconds
        )
        output = result.stdout + result.stderr
        return output, result.returncode == 0
    except subprocess.TimeoutExpired:
        logger.warning(f"Agent timed out after {timeout_minutes} minutes")
        return "TIMEOUT", False
    except FileNotFoundError:
        logger.error("Claude CLI not found")
        return "ERROR: claude CLI not found", False


def extract_json_from_output(output: str) -> Optional[dict]:
    """Extract the last JSON block from agent output."""
    json_blocks = re.findall(r'```json\s*\n(.*?)\n\s*```', output, re.DOTALL)
    if json_blocks:
        try:
            return json.loads(json_blocks[-1])
        except json.JSONDecodeError:
            pass
    # Try raw JSON at end
    lines = output.strip().split('\n')
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()
        if line.startswith('{'):
            depth = 0
            candidate = '\n'.join(lines[i:])
            for j, ch in enumerate(candidate):
                if ch == '{':
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0:
                        try:
                            return json.loads(candidate[:j + 1])
                        except json.JSONDecodeError:
                            break
            break
    return None


# ── Git Operations ────────────────────────────────────────────

def git_current_branch() -> str:
    r = subprocess.run(["git", "rev-parse", "--abbrev-ref", "HEAD"],
                       cwd=ROOT, capture_output=True, text=True)
    return r.stdout.strip()


def git_create_branch(branch_name: str) -> bool:
    r = subprocess.run(["git", "checkout", "-b", branch_name],
                       cwd=ROOT, capture_output=True, text=True)
    return r.returncode == 0


def git_checkout(branch: str) -> bool:
    r = subprocess.run(["git", "checkout", branch],
                       cwd=ROOT, capture_output=True, text=True)
    return r.returncode == 0


def git_has_changes() -> bool:
    r = subprocess.run(["git", "diff", "--name-only"],
                       cwd=ROOT, capture_output=True, text=True)
    return bool(r.stdout.strip())


def git_commit_all(message: str) -> str:
    """Stage all changes and commit. Returns commit SHA."""
    subprocess.run(["git", "add", "-A"], cwd=ROOT, capture_output=True, text=True)
    r = subprocess.run(
        ["git", "commit", "-m", message],
        cwd=ROOT, capture_output=True, text=True
    )
    if r.returncode == 0:
        sha = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                             cwd=ROOT, capture_output=True, text=True)
        return sha.stdout.strip()
    return ""



# ── Prompt Building ───────────────────────────────────────────

def build_investigate_prompt(finding: Finding, program: str) -> str:
    """Build prompt for investigating and fixing a single finding."""
    return f"""You are an autonomous investigation agent resolving audit findings
for the Chiral Geometrogenesis framework.

## Resolution Direction
{program}

## Finding to Resolve
**Group:** {finding.group} — {GROUP_METADATA[finding.group]['name']}
**Layer:** {finding.layer} (Coherence)
**Module:** {finding.module}
**Check ID:** {finding.check_id}
**Severity:** {finding.severity}
**Description:** {finding.description}
**Evidence:** {finding.evidence}
**Source report:** docs/proofs/reviews/{finding.group}/{finding.report_file}

## Instructions

1. **Investigate**: Read the affected files mentioned in the evidence. Understand
   the root cause of the inconsistency. Read the source report for full context.

2. **Identify the canonical source**: For geometry, Def 0.1.1 is canonical.
   For axioms, Def 0.0.0 is canonical. For status markers, follow CLAUDE.md rules.

3. **Fix**: Make the minimal change needed to resolve the finding. Fix ONLY
   the specific inconsistency — do not refactor surrounding text.

4. **Verify**: After fixing, re-read the affected files to confirm the fix
   resolves the finding without introducing new inconsistencies.

## Status marker rules (if applicable):
- 🔶 NOVEL must persist when ✅ VERIFIED is added — novelty is orthogonal to verification
- 🔶 NOVEL ✅ VERIFIED requires both multi-agent adversarial review AND Lean 4 formalization
- ✅ ESTABLISHED is for textbook/peer-reviewed physics only
- Format: `## Status: [MARKER] — [SHORT DESCRIPTION IN CAPS]`

## Output

After making changes, output a JSON summary:

```json
{{
  "check_id": "{finding.check_id}",
  "result": "RESOLVED|PARTIAL|SKIPPED",
  "summary": "what was done",
  "files_modified": ["path/to/file1.md", "path/to/file2.md"],
  "root_cause": "brief description of what was wrong",
  "fix_description": "brief description of what was changed"
}}
```

IMPORTANT:
- Make MINIMAL changes — fix only this finding
- If the fix requires new physics content, output result "SKIPPED" with explanation
- If you cannot determine the correct resolution, output "SKIPPED"
- Do NOT create new files — only modify existing ones
- Do NOT modify the audit report files in docs/proofs/reviews/"""


def build_verify_prompt(finding: Finding, fix_summary: str,
                        files_modified: list[str]) -> str:
    """Build prompt for verifying a fix."""
    files_list = "\n".join(f"  - {f}" for f in files_modified)
    return f"""You are a verification agent checking whether a fix for an audit finding
is correct and complete.

## Original Finding
**Check ID:** {finding.check_id}
**Description:** {finding.description}
**Evidence:** {finding.evidence}

## Fix Applied
{fix_summary}

## Files Modified
{files_list}

## Instructions

1. Read each modified file
2. Check that the original inconsistency is resolved
3. Check that no new inconsistencies were introduced
4. Check that the fix is minimal (no unnecessary changes)

## Output

```json
{{
  "check_id": "{finding.check_id}",
  "verification": "PASS|FAIL",
  "notes": "any issues found"
}}
```

IMPORTANT: Do NOT modify any files. This is a READ-ONLY verification."""


# ── Resolution Logic ──────────────────────────────────────────

def resolve_finding(finding: Finding, config: dict, program: str,
                    logger: logging.Logger, dry_run: bool = False) -> ResolutionOutcome:
    """Resolve a single finding via agent invocation.

    All work happens on the current branch (the review branch).
    Each successful fix is committed as its own atomic commit.
    Failed fixes are reverted to keep the branch clean.
    """
    start_time = time.time()
    outcome = ResolutionOutcome(finding=finding)

    if dry_run:
        outcome.result = ResolutionResult.SKIPPED
        outcome.summary = "Dry run"
        logger.info(
            f"    [DRY] {finding.check_id} ({finding.severity}): "
            f"{finding.description[:80]}..."
        )
        return outcome

    logger.info(
        f"    [>>>] {finding.check_id} ({finding.severity}): "
        f"{finding.description[:80]}..."
    )

    # Investigate and fix
    prompt = build_investigate_prompt(finding, program)
    timeout = config["time_budgets"]["per_finding_minutes"]
    output, success = invoke_agent(prompt, config, logger, timeout)

    # Parse the resolution result
    result_json = extract_json_from_output(output)

    if result_json:
        result_str = result_json.get("result", "FAILED")
        outcome.summary = result_json.get("summary", "")
        outcome.files_modified = result_json.get("files_modified", [])

        if result_str == "RESOLVED":
            outcome.result = ResolutionResult.RESOLVED
        elif result_str == "PARTIAL":
            outcome.result = ResolutionResult.PARTIAL
        elif result_str == "SKIPPED":
            outcome.result = ResolutionResult.SKIPPED
        else:
            outcome.result = ResolutionResult.FAILED
    else:
        # Agent didn't produce JSON — check if it made changes
        if success and git_has_changes():
            outcome.result = ResolutionResult.PARTIAL
            outcome.summary = "Agent completed but did not produce structured results"
        else:
            outcome.result = ResolutionResult.FAILED
            outcome.summary = "Could not parse agent output"

    # Commit or revert
    if outcome.result in (ResolutionResult.RESOLVED, ResolutionResult.PARTIAL):
        if git_has_changes() and config["git"]["auto_commit"]:
            commit_msg = (
                f"Fix {finding.check_id}: {finding.description[:60]}\n\n"
                f"Resolution: {outcome.summary}\n"
                f"Severity: {finding.severity}\n"
                f"Source: {finding.report_file}\n\n"
                f"Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
            )
            sha = git_commit_all(commit_msg)
            outcome.commit_sha = sha
            logger.info(f"    [OK ] Committed: {sha}")
        elif not git_has_changes():
            logger.info(f"    [OK ] No file changes needed (metadata-only fix?)")
    else:
        # Revert any uncommitted changes on failure
        if git_has_changes() and config["git"]["revert_on_failure"]:
            subprocess.run(["git", "checkout", "."], cwd=ROOT,
                           capture_output=True, text=True)
            logger.debug(f"    Reverted uncommitted changes")

    outcome.duration_seconds = time.time() - start_time

    status_icon = {
        ResolutionResult.RESOLVED: "+++",
        ResolutionResult.PARTIAL:  " ~ ",
        ResolutionResult.SKIPPED:  "SKP",
        ResolutionResult.FAILED:   "---",
        ResolutionResult.ERROR:    "ERR",
    }

    logger.info(
        f"    [{status_icon[outcome.result]}] {finding.check_id}: "
        f"{outcome.summary[:60]} ({outcome.duration_seconds:.0f}s)"
    )

    return outcome


# ── Results Recording ─────────────────────────────────────────

def write_results_header():
    """Write TSV header if file doesn't exist."""
    if not RESULTS_PATH.exists() or RESULTS_PATH.stat().st_size == 0:
        with open(RESULTS_PATH, "w") as f:
            f.write(
                "timestamp\tgroup\tlayer\tmodule\tcheck_id\tseverity\t"
                "result\tduration_s\tcommit\tsummary\n"
            )


def record_outcome(outcome: ResolutionOutcome):
    """Append a resolution outcome to results.tsv."""
    f = outcome.finding
    with open(RESULTS_PATH, "a") as fh:
        fh.write(
            f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\t"
            f"{f.group}\t{f.layer}\t{f.module}\t{f.check_id}\t"
            f"{f.severity}\t{outcome.result.value}\t"
            f"{outcome.duration_seconds:.1f}\t{outcome.commit_sha}\t"
            f"{outcome.summary}\n"
        )


# ── Resolution Report ─────────────────────────────────────────

def generate_resolution_report(group_id: str, layer: int,
                               outcomes: list[ResolutionOutcome],
                               logger: logging.Logger):
    """Write a summary resolution report."""
    group_dir = REVIEWS_DIR / group_id
    group_dir.mkdir(parents=True, exist_ok=True)
    meta = GROUP_METADATA[group_id]

    layer_names = {1: "Coherence", 2: "Validity", 3: "Adversarial"}
    layer_name = layer_names.get(layer, f"Layer-{layer}")

    report_path = group_dir / f"{group_id}-{meta['short']}-{layer_name}-Resolution-Report.md"

    resolved = [o for o in outcomes if o.result == ResolutionResult.RESOLVED]
    partial = [o for o in outcomes if o.result == ResolutionResult.PARTIAL]
    failed = [o for o in outcomes if o.result == ResolutionResult.FAILED]
    skipped = [o for o in outcomes if o.result == ResolutionResult.SKIPPED]

    lines = [
        f"# {group_id} {layer_name} — Resolution Report",
        f"",
        f"**Date:** {datetime.now().strftime('%Y-%m-%d')}",
        f"**Group:** {group_id} — {meta['name']}",
        f"**Layer:** {layer} ({layer_name})",
        f"**Tool:** AutoInvestigator-CG",
        f"",
        f"## Summary",
        f"",
        f"| Status | Count |",
        f"|--------|-------|",
        f"| Resolved | {len(resolved)} |",
        f"| Partial | {len(partial)} |",
        f"| Failed | {len(failed)} |",
        f"| Skipped | {len(skipped)} |",
        f"| **Total** | **{len(outcomes)}** |",
        f"",
        f"## Findings",
        f"",
    ]

    for outcome in outcomes:
        f = outcome.finding
        icon = {
            ResolutionResult.RESOLVED: "✅",
            ResolutionResult.PARTIAL: "🔶",
            ResolutionResult.FAILED: "❌",
            ResolutionResult.SKIPPED: "⏭️",
            ResolutionResult.ERROR: "🔴",
        }.get(outcome.result, "?")

        lines.append(f"### {icon} {f.check_id} — {f.severity}")
        lines.append(f"")
        lines.append(f"**Finding:** {f.description}")
        lines.append(f"**Evidence:** {f.evidence}")
        lines.append(f"**Result:** {outcome.result.value}")
        lines.append(f"**Summary:** {outcome.summary}")
        if outcome.files_modified:
            lines.append(f"**Files modified:** {', '.join(outcome.files_modified)}")
        if outcome.commit_sha:
            lines.append(f"**Commit:** {outcome.commit_sha}")
        lines.append(f"**Duration:** {outcome.duration_seconds:.0f}s")
        lines.append(f"")

    report_path.write_text("\n".join(lines))
    logger.info(f"Resolution report written to: {report_path.relative_to(ROOT)}")


# ── Status Display ────────────────────────────────────────────

def show_status(group_id: str, layer: int, config: dict, logger: logging.Logger):
    """Show current finding status for a group/layer."""
    findings = scan_findings(group_id, layer, None, config, logger)

    if not findings:
        print(f"\n  No FAIL findings found for {group_id} Layer {layer}")
        return

    print(f"\n  {group_id} Layer {layer} — {len(findings)} FAIL findings:\n")
    print(f"  {'Check ID':<12} {'Severity':<10} {'Module':<8} Description")
    print(f"  {'─'*12} {'─'*10} {'─'*8} {'─'*50}")

    for f in findings:
        desc = f.description[:55] + "..." if len(f.description) > 55 else f.description
        print(f"  {f.check_id:<12} {f.severity:<10} {f.module:<8} {desc}")

    # Check for existing resolutions
    if RESULTS_PATH.exists():
        existing = set()
        with open(RESULTS_PATH) as fh:
            for line in fh:
                parts = line.strip().split("\t")
                if len(parts) >= 7 and parts[1] == group_id and parts[6] == "RESOLVED":
                    existing.add(parts[4])  # check_id

        if existing:
            print(f"\n  Already resolved: {', '.join(sorted(existing))}")

    remaining = len(findings)
    print(f"\n  {remaining} findings to investigate\n")


# ── Main Campaign ─────────────────────────────────────────────

def run_campaign(group_id: str, layer: int, module_filter: Optional[str],
                 config: dict, logger: logging.Logger,
                 dry_run: bool = False, max_parallel: int = 1):
    """Run the investigation campaign.

    All fixes are committed on a single review branch. Nothing touches main
    until you review the diff and merge manually.
    """
    logger.info(f"AutoInvestigator-CG starting — {group_id} Layer {layer}")
    logger.info(f"  Mode: {'dry-run' if dry_run else 'live'}")

    # Scan for findings
    findings = scan_findings(group_id, layer, module_filter, config, logger)

    if not findings:
        logger.info("No FAIL findings found — nothing to investigate")
        return

    logger.info(f"  Found {len(findings)} FAIL findings to investigate")

    # Check for already-resolved findings
    already_resolved = set()
    if RESULTS_PATH.exists():
        with open(RESULTS_PATH) as fh:
            for line in fh:
                parts = line.strip().split("\t")
                if (len(parts) >= 7 and parts[1] == group_id
                        and parts[6] == "RESOLVED"):
                    already_resolved.add(parts[4])

    # Filter out already-resolved
    remaining = [f for f in findings if f.check_id not in already_resolved]
    if len(remaining) < len(findings):
        logger.info(
            f"  Skipping {len(findings) - len(remaining)} already-resolved findings"
        )
    findings = remaining

    if not findings:
        logger.info("All findings already resolved")
        return

    # Show what we're about to do
    for f in findings:
        logger.info(f"  [{f.severity:>8}] {f.check_id}: {f.description[:70]}")

    logger.info(f"\nLaunching {len(findings)} investigations "
                f"({max_parallel} parallel)\n")

    # Create a review branch (all fixes land here, not on main)
    base_branch = git_current_branch()
    review_branch = None
    if not dry_run:
        layer_names = {1: "coherence", 2: "validity", 3: "adversarial"}
        layer_name = layer_names.get(layer, f"layer-{layer}")
        review_branch = (
            f"{config['git']['branch_prefix']}/"
            f"{group_id}-L{layer}-{layer_name}-fixes"
        )
        if base_branch == "main":
            if git_create_branch(review_branch):
                logger.info(f"  Created review branch: {review_branch}")
                logger.info(f"  All fixes will be committed here (main is untouched)")
            else:
                logger.warning(
                    f"  Could not create branch {review_branch} "
                    f"(may already exist — continuing on current branch)"
                )
                # Try to check it out if it exists
                git_checkout(review_branch)
                review_branch = git_current_branch()
        else:
            logger.info(f"  Already on branch {base_branch} — committing here")
            review_branch = base_branch

    program = load_program()
    write_results_header()

    outcomes = []
    consecutive_failures = 0
    campaign_start = time.time()
    campaign_limit = config["time_budgets"]["campaign_hours"] * 3600

    if max_parallel <= 1:
        # Sequential execution
        for finding in findings:
            # Check campaign time limit
            if time.time() - campaign_start > campaign_limit:
                logger.warning("Campaign time limit reached")
                break

            # Check consecutive failure limit
            if (consecutive_failures >=
                    config["early_exit"]["max_consecutive_failures"]):
                logger.warning(
                    f"Early exit: {consecutive_failures} consecutive failures"
                )
                break

            outcome = resolve_finding(
                finding, config, program, logger, dry_run=dry_run
            )
            outcomes.append(outcome)
            record_outcome(outcome)

            if outcome.result in (ResolutionResult.RESOLVED,
                                  ResolutionResult.PARTIAL,
                                  ResolutionResult.SKIPPED):
                consecutive_failures = 0
            else:
                consecutive_failures += 1
    else:
        # Parallel execution
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=max_parallel
        ) as executor:
            futures = {
                executor.submit(
                    resolve_finding, finding, config, program, logger, dry_run
                ): finding
                for finding in findings
            }
            for future in concurrent.futures.as_completed(futures):
                outcome = future.result()
                outcomes.append(outcome)
                record_outcome(outcome)

    # Generate resolution report
    if outcomes and not dry_run:
        generate_resolution_report(group_id, layer, outcomes, logger)

    # Summary
    resolved = sum(1 for o in outcomes if o.result == ResolutionResult.RESOLVED)
    partial = sum(1 for o in outcomes if o.result == ResolutionResult.PARTIAL)
    failed = sum(1 for o in outcomes if o.result == ResolutionResult.FAILED)
    skipped = sum(1 for o in outcomes if o.result == ResolutionResult.SKIPPED)
    total_time = time.time() - campaign_start

    logger.info(f"\n{'='*60}")
    logger.info(f"CAMPAIGN COMPLETE — {group_id} Layer {layer}")
    logger.info(f"  Resolved: {resolved}")
    logger.info(f"  Partial:  {partial}")
    logger.info(f"  Failed:   {failed}")
    logger.info(f"  Skipped:  {skipped}")
    logger.info(f"  Time:     {total_time/60:.1f} min")
    logger.info(f"{'='*60}")

    # Print review instructions
    if not dry_run and review_branch and resolved + partial > 0:
        logger.info(f"")
        logger.info(f"  HOW TO REVIEW:")
        logger.info(f"  ─────────────────────────────────────────────")
        logger.info(f"  See all changes:    git diff main..{review_branch}")
        logger.info(f"  See each fix:       git log --oneline main..{review_branch}")
        logger.info(f"  Review one commit:  git show <sha>")
        logger.info(f"  Resolution report:  docs/proofs/reviews/{group_id}/{group_id}-*-Resolution-Report.md")
        logger.info(f"  ─────────────────────────────────────────────")
        logger.info(f"  To accept all:      git checkout main && git merge {review_branch}")
        logger.info(f"  To reject all:      git checkout main && git branch -D {review_branch}")
        logger.info(f"  Cherry-pick one:    git checkout main && git cherry-pick <sha>")
        logger.info(f"")


# ── CLI ───────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="AutoInvestigator-CG: Resolve audit findings autonomously"
    )
    parser.add_argument("--group", required=True,
                        help="Group ID (e.g., G1)")
    parser.add_argument("--layer", type=int, required=True,
                        help="Audit layer (1=Coherence, 2=Validity, 3=Adversarial)")
    parser.add_argument("--module", default=None,
                        help="Filter to a specific module (e.g., M9)")
    parser.add_argument("--dry-run", action="store_true",
                        help="List findings without resolving them")
    parser.add_argument("--status", action="store_true",
                        help="Show finding status and exit")
    parser.add_argument("--max-parallel", type=int, default=1,
                        help="Max parallel investigations (default: 1 = sequential)")

    args = parser.parse_args()

    if args.group not in GROUP_METADATA:
        print(f"Unknown group: {args.group}")
        print(f"Valid groups: {', '.join(GROUP_METADATA.keys())}")
        sys.exit(1)

    config = load_config()
    logger = setup_logging(config)

    if args.status:
        show_status(args.group, args.layer, config, logger)
        return

    run_campaign(
        group_id=args.group,
        layer=args.layer,
        module_filter=args.module,
        config=config,
        logger=logger,
        dry_run=args.dry_run,
        max_parallel=args.max_parallel,
    )


if __name__ == "__main__":
    main()
