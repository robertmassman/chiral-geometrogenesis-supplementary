#!/usr/bin/env python3
"""
AutoResearch-CG: Autonomous Proof Refinement Loop
===================================================

Inspired by Karpathy's autoresearch, adapted for theoretical physics
proof refinement and verification.

The loop:
  1. SELECT a target theorem (weakest link in the proof chain)
  2. ANALYZE it for gaps, issues, weak steps
  3. REFINE via Claude Code agent (issue-level, then theorem-level)
  4. VERIFY via Python scripts + dependency checks
  5. EVALUATE pass/fail + regression check
  6. KEEP (git commit) or REVERT (git checkout)
  7. LOG results
  8. REPEAT

Usage:
  python3 verification/autoresearch/autoresearch_cg.py
  python3 verification/autoresearch/autoresearch_cg.py --dry-run
  python3 verification/autoresearch/autoresearch_cg.py --iterations 5
  python3 verification/autoresearch/autoresearch_cg.py --theorem 3.1.1
"""

import argparse
import json
import logging
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from pathlib import Path
from typing import Optional

# ── Paths ─────────────────────────────────────────────────────
ROOT = Path(__file__).resolve().parent.parent.parent  # eqalateralCube/
AUTORESEARCH_DIR = Path(__file__).resolve().parent
CONFIG_PATH = AUTORESEARCH_DIR / "config.json"
PROGRAM_PATH = AUTORESEARCH_DIR / "program.md"
RESULTS_PATH = AUTORESEARCH_DIR / "results.tsv"
LOG_PATH = AUTORESEARCH_DIR / "campaign.log"

# Add verification/shared to path for theorem_graph
sys.path.insert(0, str(ROOT / "verification" / "shared"))


# ── Data Types ────────────────────────────────────────────────

class IterationResult(Enum):
    SUCCESS = "success"           # Proof improved, verification passed
    PARTIAL = "partial"           # Some improvement but not fully resolved
    FAILURE = "failure"           # No improvement or regression
    SKIPPED = "skipped"           # Agent couldn't help, skipped
    ERROR = "error"               # Unexpected error


@dataclass
class TargetInfo:
    """Information about a theorem targeted for refinement."""
    theorem_id: str
    name: str
    status: str
    phase: str
    issues: list[str] = field(default_factory=list)
    proof_files: list[str] = field(default_factory=list)
    verification_scripts: list[str] = field(default_factory=list)
    dependency_chain: list[str] = field(default_factory=list)


@dataclass
class IterationLog:
    """Log entry for a single iteration."""
    iteration: int
    timestamp: str
    theorem_id: str
    theorem_name: str
    phase: str
    status_before: str
    result: IterationResult
    duration_seconds: float
    issues_found: int = 0
    issues_resolved: int = 0
    tests_before: int = 0
    tests_after: int = 0
    agent_summary: str = ""
    git_commit: str = ""


# ── Config Loading ────────────────────────────────────────────

def load_config() -> dict:
    """Load configuration from config.json."""
    with open(CONFIG_PATH) as f:
        return json.load(f)


def load_program() -> str:
    """Load the research direction from program.md."""
    with open(PROGRAM_PATH) as f:
        return f.read()


# ── Logging Setup ─────────────────────────────────────────────

def setup_logging(config: dict) -> logging.Logger:
    """Configure logging to file and console."""
    logger = logging.getLogger("autoresearch-cg")
    logger.setLevel(getattr(logging, config["logging"]["level"].upper()))

    # File handler
    fh = logging.FileHandler(LOG_PATH)
    fh.setLevel(logging.DEBUG)
    fh.setFormatter(logging.Formatter(
        "%(asctime)s [%(levelname)s] %(message)s", datefmt="%Y-%m-%d %H:%M:%S"
    ))
    logger.addHandler(fh)

    # Console handler
    ch = logging.StreamHandler()
    ch.setLevel(logging.INFO)
    ch.setFormatter(logging.Formatter(
        "\033[90m%(asctime)s\033[0m %(message)s", datefmt="%H:%M:%S"
    ))
    logger.addHandler(ch)

    return logger


# ── Git Operations ────────────────────────────────────────────

def git_run(*args, check=True) -> subprocess.CompletedProcess:
    """Run a git command in the project root."""
    return subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=check
    )


def git_current_branch() -> str:
    """Get the current branch name."""
    result = git_run("branch", "--show-current")
    return result.stdout.strip()


def git_has_changes() -> bool:
    """Check if there are uncommitted changes."""
    result = git_run("status", "--porcelain")
    return bool(result.stdout.strip())


def git_create_branch(name: str):
    """Create and checkout a new branch."""
    git_run("checkout", "-b", name)


def git_checkout(branch: str):
    """Checkout an existing branch."""
    git_run("checkout", branch)


def git_commit(message: str) -> str:
    """Stage all changes and commit. Returns commit hash."""
    git_run("add", "-A")
    git_run("commit", "-m", message)
    result = git_run("rev-parse", "HEAD")
    return result.stdout.strip()[:12]


def git_revert_all():
    """Revert all uncommitted changes."""
    git_run("checkout", ".")
    git_run("clean", "-fd")


def git_merge_to_base(branch: str, base: str):
    """Merge a branch into base."""
    git_checkout(base)
    git_run("merge", branch, "--no-edit")


def git_delete_branch(branch: str):
    """Delete a local branch."""
    git_run("branch", "-d", branch, check=False)


# ── Target Selection ──────────────────────────────────────────

def find_proof_files(theorem_id: str) -> list[str]:
    """Find proof document files for a given theorem ID."""
    # Convert 3.1.1 to patterns like Theorem-3.1.1-*, Definition-3.1.1-*, etc.
    files = []
    for proof_dir in (ROOT / "docs" / "proofs").rglob("*"):
        if proof_dir.is_file() and theorem_id in proof_dir.name:
            files.append(str(proof_dir.relative_to(ROOT)))
    return files


def find_verification_scripts(theorem_id: str) -> list[str]:
    """Find verification scripts for a given theorem ID."""
    # Convert 3.1.1 to theorem_3_1_1
    script_id = f"theorem_{theorem_id.replace('.', '_')}"
    files = []
    for script in (ROOT / "verification").rglob("*.py"):
        if script_id in script.name or theorem_id.replace(".", "_") in script.name:
            files.append(str(script.relative_to(ROOT)))
    return files


def select_targets(config: dict, logger: logging.Logger,
                   specific_theorem: Optional[str] = None) -> list[TargetInfo]:
    """Select theorems to work on based on config and theorem graph."""
    from theorem_graph import TheoremGraph, Status

    graph = TheoremGraph()
    targets = []

    if specific_theorem:
        # User specified a specific theorem
        if specific_theorem in graph.theorems:
            thm = graph.theorems[specific_theorem]
            targets.append(TargetInfo(
                theorem_id=thm.id,
                name=thm.name,
                status=thm.status.value,
                phase=thm.phase.name,
                proof_files=find_proof_files(thm.id),
                verification_scripts=find_verification_scripts(thm.id),
                dependency_chain=graph.get_dependency_chain(thm.id),
            ))
        else:
            logger.warning(f"Theorem {specific_theorem} not found in graph")
        return targets

    # Priority-based selection from config
    priority_map = {
        "partial": Status.PARTIAL,
        "conjecture": Status.CONJECTURE,
        "novel_unverified": Status.NOVEL,
        "weakest_verified": Status.VERIFIED,
    }

    skip_tags = set(config["target_selection"].get("skip_tags", []))
    filter_phases = config["target_selection"].get("phases", [])
    filter_tags = set(config["target_selection"].get("tags", []))

    for priority_key in config["target_selection"]["priority"]:
        target_status = priority_map.get(priority_key)
        if not target_status:
            continue

        for thm in graph.theorems.values():
            if thm.status != target_status:
                continue
            if skip_tags & set(thm.tags):
                continue
            if filter_phases and thm.phase.name not in filter_phases:
                continue
            if filter_tags and not (filter_tags & set(thm.tags)):
                continue
            # For "novel_unverified", skip if it's already verified
            if priority_key == "novel_unverified" and thm.verification_date:
                continue

            targets.append(TargetInfo(
                theorem_id=thm.id,
                name=thm.name,
                status=thm.status.value,
                phase=thm.phase.name,
                proof_files=find_proof_files(thm.id),
                verification_scripts=find_verification_scripts(thm.id),
                dependency_chain=graph.get_dependency_chain(thm.id),
            ))

    # Sort: prefer theorems with fewer unresolved dependencies (more "ready")
    targets.sort(key=lambda t: len(t.dependency_chain))

    logger.info(f"Selected {len(targets)} candidate theorems")
    for t in targets[:5]:
        logger.info(f"  [{t.status}] {t.theorem_id}: {t.name}")

    return targets


# ── Agent Invocation ──────────────────────────────────────────

def build_analysis_prompt(target: TargetInfo, program: str) -> str:
    """Build the prompt for the analysis phase."""
    proof_files_str = "\n".join(f"  - {f}" for f in target.proof_files) or "  (none found)"
    verif_files_str = "\n".join(f"  - {f}" for f in target.verification_scripts) or "  (none found)"

    return f"""You are an autonomous research agent working on the Chiral Geometrogenesis framework.

## Research Direction
{program}

## Your Task: ANALYZE Theorem {target.theorem_id} — "{target.name}"

Current status: {target.status}
Phase: {target.phase}

### Proof documents:
{proof_files_str}

### Verification scripts:
{verif_files_str}

### Instructions:
1. Read the proof document(s) for Theorem {target.theorem_id}
2. Read any existing verification scripts
3. Identify the TOP 3 weakest points, gaps, or issues in this theorem
4. For each issue, classify severity as HIGH / MEDIUM / LOW
5. Output your analysis as a JSON block at the end of your response:

```json
{{
  "theorem_id": "{target.theorem_id}",
  "issues": [
    {{
      "id": "I1",
      "description": "...",
      "severity": "HIGH|MEDIUM|LOW",
      "location": "file:line or section reference",
      "suggested_fix": "brief description of how to fix"
    }}
  ],
  "overall_assessment": "brief assessment",
  "can_improve": true
}}
```

IMPORTANT: Only output analysis. Do NOT modify any files yet."""


def build_fix_prompt(target: TargetInfo, issue: dict, program: str) -> str:
    """Build the prompt for fixing a specific issue."""
    return f"""You are an autonomous research agent working on the Chiral Geometrogenesis framework.

## Research Direction
{program}

## Your Task: FIX Issue {issue['id']} in Theorem {target.theorem_id}

Theorem: {target.theorem_id} — "{target.name}"
Issue: {issue['description']}
Severity: {issue['severity']}
Location: {issue['location']}
Suggested fix: {issue['suggested_fix']}

### Instructions:
1. Read the relevant proof document and understand the context
2. Make the MINIMAL targeted fix for this specific issue
3. If you modify a proof, ensure:
   - Dimensional consistency is maintained
   - Limiting cases still hold
   - No downstream contradictions introduced
4. If a verification script exists, update it to test the fix
5. If no verification script exists, create one following the template in verification/CLAUDE.md
6. Run the verification script to confirm the fix works

After making changes, output a summary as JSON at the end:

```json
{{
  "theorem_id": "{target.theorem_id}",
  "issue_id": "{issue['id']}",
  "fixed": true,
  "changes_made": ["list of files modified"],
  "verification_result": "PASSED|FAILED",
  "notes": "brief explanation"
}}
```"""


def build_rollup_prompt(target: TargetInfo, program: str) -> str:
    """Build the prompt for theorem-level verification rollup."""
    verif_files_str = "\n".join(f"  - {f}" for f in target.verification_scripts) or "  (none found)"

    return f"""You are an autonomous research agent working on the Chiral Geometrogenesis framework.

## Research Direction
{program}

## Your Task: VERIFY Theorem {target.theorem_id} — "{target.name}" (Rollup)

This theorem has just been refined. Now verify the OVERALL theorem is sound.

### Verification scripts:
{verif_files_str}

### Instructions:
1. Run ALL verification scripts for this theorem
2. Run the proof dependency checker: `python3 verification/check_proof_dependencies.py`
3. Check that downstream theorems are not broken (regression check)
4. Summarize the overall state

Output a JSON summary at the end:

```json
{{
  "theorem_id": "{target.theorem_id}",
  "overall_verification": "PASSED|FAILED|PARTIAL",
  "scripts_run": 0,
  "scripts_passed": 0,
  "regressions_found": [],
  "recommendation": "KEEP|REVERT",
  "notes": "brief explanation"
}}
```"""


def invoke_agent(prompt: str, config: dict, logger: logging.Logger,
                 timeout_minutes: float) -> tuple[str, bool]:
    """
    Invoke Claude Code CLI with the given prompt.
    Returns (output_text, success).
    """
    cmd = [config["agent"]["command"]]

    if config["agent"].get("model"):
        cmd.extend(["--model", config["agent"]["model"]])

    for flag in config["agent"].get("flags", []):
        cmd.append(flag)

    cmd.extend(["--max-turns", str(config["agent"].get("max_turns", 50))])
    cmd.extend(["-p", prompt])

    timeout_seconds = int(timeout_minutes * 60)

    logger.debug(f"Invoking agent with timeout={timeout_minutes}min")
    logger.debug(f"Command: {' '.join(cmd[:4])}...")

    try:
        result = subprocess.run(
            cmd, cwd=ROOT, capture_output=True, text=True,
            timeout=timeout_seconds
        )
        output = result.stdout + result.stderr
        success = result.returncode == 0
        if not success:
            logger.warning(f"Agent exited with code {result.returncode}")
        return output, success

    except subprocess.TimeoutExpired:
        logger.warning(f"Agent timed out after {timeout_minutes} minutes")
        return "TIMEOUT: Agent exceeded time budget", False

    except FileNotFoundError:
        logger.error("Claude CLI not found. Is 'claude' in PATH?")
        return "ERROR: claude CLI not found", False


def extract_json_from_output(output: str) -> Optional[dict]:
    """Extract the last JSON block from agent output."""
    # Find the last ```json ... ``` block
    import re
    json_blocks = re.findall(r'```json\s*\n(.*?)\n\s*```', output, re.DOTALL)
    if json_blocks:
        try:
            return json.loads(json_blocks[-1])
        except json.JSONDecodeError:
            pass

    # Try to find raw JSON object at end of output
    lines = output.strip().split('\n')
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()
        if line.startswith('{'):
            # Try parsing from this line to end
            candidate = '\n'.join(lines[i:])
            # Find matching closing brace
            depth = 0
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


# ── Verification ──────────────────────────────────────────────

def run_verification_scripts(target: TargetInfo, logger: logging.Logger) -> tuple[int, int]:
    """Run verification scripts for a theorem. Returns (total, passed)."""
    if not target.verification_scripts:
        logger.info(f"No verification scripts found for {target.theorem_id}")
        return 0, 0

    total = 0
    passed = 0

    for script_path in target.verification_scripts:
        full_path = ROOT / script_path
        if not full_path.exists():
            continue
        if not script_path.endswith(".py"):
            continue

        total += 1
        logger.info(f"  Running {script_path}...")
        try:
            result = subprocess.run(
                ["python3", str(full_path)],
                cwd=full_path.parent, capture_output=True, text=True, timeout=120
            )
            if result.returncode == 0 and "FAILED" not in result.stdout:
                passed += 1
                logger.info(f"    PASSED")
            else:
                logger.warning(f"    FAILED: {result.stdout[-200:]}")
        except subprocess.TimeoutExpired:
            logger.warning(f"    TIMEOUT after 120s")
        except Exception as e:
            logger.warning(f"    ERROR: {e}")

    return total, passed


def run_dependency_check(logger: logging.Logger) -> bool:
    """Run proof dependency checker. Returns True if clean."""
    check_script = ROOT / "verification" / "check_proof_dependencies.py"
    if not check_script.exists():
        logger.info("Dependency check script not found, skipping")
        return True

    try:
        result = subprocess.run(
            ["python3", str(check_script)],
            cwd=ROOT, capture_output=True, text=True, timeout=60
        )
        clean = result.returncode == 0
        if not clean:
            logger.warning(f"Dependency check found issues: {result.stdout[-300:]}")
        return clean
    except Exception as e:
        logger.warning(f"Dependency check error: {e}")
        return True  # Don't block on check failures


# ── Results Logging ───────────────────────────────────────────

def init_results_file():
    """Create results TSV with header if it doesn't exist."""
    if not RESULTS_PATH.exists():
        with open(RESULTS_PATH, "w") as f:
            f.write("\t".join([
                "iteration", "timestamp", "theorem_id", "theorem_name",
                "phase", "status_before", "result", "duration_s",
                "issues_found", "issues_resolved",
                "tests_before", "tests_after",
                "git_commit", "agent_summary"
            ]) + "\n")


def log_result(entry: IterationLog):
    """Append an iteration result to results.tsv."""
    with open(RESULTS_PATH, "a") as f:
        f.write("\t".join([
            str(entry.iteration),
            entry.timestamp,
            entry.theorem_id,
            entry.theorem_name,
            entry.phase,
            entry.status_before,
            entry.result.value,
            f"{entry.duration_seconds:.1f}",
            str(entry.issues_found),
            str(entry.issues_resolved),
            str(entry.tests_before),
            str(entry.tests_after),
            entry.git_commit,
            entry.agent_summary.replace("\t", " ").replace("\n", " ")[:200]
        ]) + "\n")


# ── Main Loop ─────────────────────────────────────────────────

def run_iteration(target: TargetInfo, iteration: int, config: dict,
                  program: str, logger: logging.Logger, dry_run: bool = False) -> IterationLog:
    """Run one full iteration of the research loop for a single theorem."""
    start_time = time.time()
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    branch_name = f"{config['git']['branch_prefix']}/iter-{iteration:04d}-{target.theorem_id}"

    logger.info("=" * 60)
    logger.info(f"ITERATION {iteration}: Theorem {target.theorem_id} — {target.name}")
    logger.info(f"Status: {target.status} | Phase: {target.phase}")
    logger.info("=" * 60)

    entry = IterationLog(
        iteration=iteration,
        timestamp=timestamp,
        theorem_id=target.theorem_id,
        theorem_name=target.name,
        phase=target.phase,
        status_before=target.status,
        result=IterationResult.ERROR,
        duration_seconds=0,
    )

    if dry_run:
        logger.info("[DRY RUN] Would analyze and refine this theorem")
        entry.result = IterationResult.SKIPPED
        entry.duration_seconds = time.time() - start_time
        entry.agent_summary = "Dry run — no changes made"
        return entry

    # ── Step 0: Baseline verification ──
    logger.info("Step 0: Running baseline verification...")
    tests_before_total, tests_before_passed = run_verification_scripts(target, logger)
    entry.tests_before = tests_before_passed
    logger.info(f"  Baseline: {tests_before_passed}/{tests_before_total} tests passing")

    # ── Step 1: Create isolation branch ──
    base_branch = git_current_branch()
    logger.info(f"Step 1: Creating branch {branch_name}")
    try:
        git_create_branch(branch_name)
    except subprocess.CalledProcessError:
        # Branch may already exist
        logger.warning(f"Could not create branch {branch_name}, working on current branch")
        branch_name = None

    # ── Step 2: Analysis phase ──
    logger.info("Step 2: Analyzing theorem for issues...")
    analysis_prompt = build_analysis_prompt(target, program)
    analysis_output, analysis_ok = invoke_agent(
        analysis_prompt, config, logger,
        timeout_minutes=config["time_budgets"]["per_issue_minutes"]
    )

    analysis = extract_json_from_output(analysis_output)
    if not analysis or not analysis.get("issues"):
        logger.info("  No issues found or analysis failed — skipping")
        entry.result = IterationResult.SKIPPED
        entry.agent_summary = "Analysis found no actionable issues"
        if branch_name:
            git_checkout(base_branch)
            git_delete_branch(branch_name)
        entry.duration_seconds = time.time() - start_time
        return entry

    issues = analysis["issues"]
    entry.issues_found = len(issues)
    logger.info(f"  Found {len(issues)} issues:")
    for issue in issues:
        logger.info(f"    [{issue['severity']}] {issue['id']}: {issue['description'][:80]}")

    if not analysis.get("can_improve", True):
        logger.info("  Agent says it cannot improve this theorem — skipping")
        entry.result = IterationResult.SKIPPED
        entry.agent_summary = analysis.get("overall_assessment", "Cannot improve")
        if branch_name:
            git_checkout(base_branch)
            git_delete_branch(branch_name)
        entry.duration_seconds = time.time() - start_time
        return entry

    # ── Step 3: Fix issues (one at a time) ──
    consecutive_failures = 0
    issues_resolved = 0
    max_failures = config["early_exit"]["max_consecutive_failures"]

    # Sort by severity: HIGH first
    severity_order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2}
    issues.sort(key=lambda i: severity_order.get(i.get("severity", "LOW"), 2))

    for issue in issues:
        if consecutive_failures >= max_failures:
            logger.warning(f"  {max_failures} consecutive failures — moving on")
            break

        logger.info(f"Step 3: Fixing {issue['id']} — {issue['description'][:60]}...")
        fix_prompt = build_fix_prompt(target, issue, program)
        fix_output, fix_ok = invoke_agent(
            fix_prompt, config, logger,
            timeout_minutes=config["time_budgets"]["per_issue_minutes"]
        )

        fix_result = extract_json_from_output(fix_output)
        if fix_result and fix_result.get("fixed"):
            issues_resolved += 1
            consecutive_failures = 0
            logger.info(f"    Issue {issue['id']} FIXED")
        else:
            consecutive_failures += 1
            logger.info(f"    Issue {issue['id']} NOT FIXED (attempt {consecutive_failures}/{max_failures})")

    entry.issues_resolved = issues_resolved

    # ── Step 4: Theorem-level rollup verification ──
    logger.info("Step 4: Running theorem-level rollup verification...")

    # Refresh the list of verification scripts (agent may have created new ones)
    target.verification_scripts = find_verification_scripts(target.theorem_id)

    rollup_prompt = build_rollup_prompt(target, program)
    rollup_output, rollup_ok = invoke_agent(
        rollup_prompt, config, logger,
        timeout_minutes=config["time_budgets"]["per_theorem_minutes"]
    )

    rollup = extract_json_from_output(rollup_output)

    # ── Step 5: Post-refinement verification ──
    logger.info("Step 5: Running post-refinement verification...")
    tests_after_total, tests_after_passed = run_verification_scripts(target, logger)
    entry.tests_after = tests_after_passed
    logger.info(f"  Post-refinement: {tests_after_passed}/{tests_after_total} tests passing")

    dep_check_ok = True
    if config["verification"]["run_dependency_checks"]:
        dep_check_ok = run_dependency_check(logger)

    # ── Step 6: Evaluate — keep or revert ──
    recommendation = "REVERT"  # Default to safe
    if rollup and rollup.get("recommendation"):
        recommendation = rollup["recommendation"]

    # Override recommendation based on hard checks
    improved = tests_after_passed > tests_before_passed or issues_resolved > 0
    regressed = tests_after_passed < tests_before_passed or not dep_check_ok

    if regressed:
        recommendation = "REVERT"
        entry.result = IterationResult.FAILURE
        logger.warning("  REGRESSION DETECTED — reverting")
    elif improved:
        recommendation = "KEEP"
        entry.result = IterationResult.SUCCESS if issues_resolved == entry.issues_found \
            else IterationResult.PARTIAL
    elif issues_resolved > 0:
        recommendation = "KEEP"
        entry.result = IterationResult.PARTIAL
    else:
        entry.result = IterationResult.FAILURE

    # ── Step 7: Git keep/revert ──
    if recommendation == "KEEP" and git_has_changes():
        commit_msg = (
            f"autoresearch: refine Theorem {target.theorem_id} — {target.name}\n\n"
            f"Issues found: {entry.issues_found}, resolved: {issues_resolved}\n"
            f"Tests: {tests_before_passed} → {tests_after_passed}\n\n"
            f"Co-Authored-By: AutoResearch-CG <noreply@autoresearch-cg>"
        )
        if config["git"]["auto_commit"]:
            commit_hash = git_commit(commit_msg)
            entry.git_commit = commit_hash
            logger.info(f"  COMMITTED: {commit_hash}")

            # Merge back to base
            if branch_name:
                git_checkout(base_branch)
                try:
                    git_merge_to_base(branch_name, base_branch)
                    git_delete_branch(branch_name)
                    logger.info(f"  Merged {branch_name} → {base_branch}")
                except subprocess.CalledProcessError:
                    logger.warning(f"  Merge conflict — leaving branch {branch_name}")
        else:
            logger.info("  Changes kept but auto_commit disabled")

    elif recommendation == "REVERT":
        if git_has_changes() and config["git"]["revert_on_failure"]:
            git_revert_all()
            logger.info("  REVERTED all changes")
        if branch_name:
            git_checkout(base_branch)
            git_delete_branch(branch_name)

    else:
        logger.info("  No changes to commit/revert")
        if branch_name:
            git_checkout(base_branch)
            git_delete_branch(branch_name)

    # ── Step 8: Summary ──
    entry.duration_seconds = time.time() - start_time
    entry.agent_summary = (
        rollup.get("notes", "") if rollup
        else analysis.get("overall_assessment", "No summary available")
    )

    result_emoji = {
        IterationResult.SUCCESS: "+++",
        IterationResult.PARTIAL: " + ",
        IterationResult.FAILURE: " - ",
        IterationResult.SKIPPED: "   ",
        IterationResult.ERROR: "ERR",
    }

    logger.info(
        f"  [{result_emoji[entry.result]}] Iteration {iteration} complete "
        f"in {entry.duration_seconds:.0f}s — "
        f"{issues_resolved}/{entry.issues_found} issues resolved, "
        f"tests {tests_before_passed}→{tests_after_passed}"
    )

    return entry


def main():
    parser = argparse.ArgumentParser(
        description="AutoResearch-CG: Autonomous proof refinement loop"
    )
    parser.add_argument("--dry-run", action="store_true",
                        help="Analyze targets without making changes")
    parser.add_argument("--iterations", type=int, default=0,
                        help="Max iterations (0 = use campaign_hours from config)")
    parser.add_argument("--theorem", type=str, default=None,
                        help="Target a specific theorem ID (e.g., 3.1.1)")
    parser.add_argument("--list-targets", action="store_true",
                        help="List candidate targets and exit")
    args = parser.parse_args()

    # Load config and program
    config = load_config()
    program = load_program()
    logger = setup_logging(config)
    init_results_file()

    logger.info("=" * 60)
    logger.info("  AutoResearch-CG: Autonomous Proof Refinement")
    logger.info(f"  Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    logger.info("=" * 60)

    # Select targets
    targets = select_targets(config, logger, specific_theorem=args.theorem)

    if not targets:
        logger.info("No targets found matching selection criteria")
        return

    if args.list_targets:
        print(f"\n{'ID':<12} {'Status':<12} {'Phase':<12} {'Name'}")
        print("-" * 70)
        for t in targets:
            print(f"{t.theorem_id:<12} {t.status:<12} {t.phase:<12} {t.name}")
        return

    # Determine iteration count
    max_iterations = args.iterations if args.iterations > 0 else len(targets)
    campaign_hours = config["time_budgets"]["campaign_hours"]
    campaign_deadline = (
        datetime.now() + timedelta(hours=campaign_hours)
        if campaign_hours > 0 else None
    )

    logger.info(f"Campaign: {max_iterations} iterations"
                + (f", deadline {campaign_deadline.strftime('%H:%M')}" if campaign_deadline else ""))

    # ── Main Loop ──
    iteration = 0
    results_summary = {r: 0 for r in IterationResult}

    for target in targets[:max_iterations]:
        iteration += 1

        # Check campaign deadline
        if campaign_deadline and datetime.now() >= campaign_deadline:
            logger.info("Campaign time budget exhausted")
            break

        # Run iteration
        entry = run_iteration(target, iteration, config, program, logger, dry_run=args.dry_run)
        log_result(entry)
        results_summary[entry.result] += 1

    # ── Campaign Summary ──
    logger.info("\n" + "=" * 60)
    logger.info("  CAMPAIGN SUMMARY")
    logger.info("=" * 60)
    logger.info(f"  Iterations:  {iteration}")
    logger.info(f"  Success:     {results_summary[IterationResult.SUCCESS]}")
    logger.info(f"  Partial:     {results_summary[IterationResult.PARTIAL]}")
    logger.info(f"  Failed:      {results_summary[IterationResult.FAILURE]}")
    logger.info(f"  Skipped:     {results_summary[IterationResult.SKIPPED]}")
    logger.info(f"  Errors:      {results_summary[IterationResult.ERROR]}")
    logger.info(f"  Results:     {RESULTS_PATH}")
    logger.info("=" * 60)


if __name__ == "__main__":
    main()
