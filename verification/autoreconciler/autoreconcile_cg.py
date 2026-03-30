#!/usr/bin/env python3
"""
AutoReconciler-CG: Update Tracking After Audit Cycles
=======================================================

After AutoVerifier + AutoInvestigator complete a clean audit cycle,
this tool updates all tracking artifacts:

  1. THEMATIC-GROUPS.md coherence checklists   ([ ] → [x])
  2. THEMATIC-GROUPS.md audit progress tracker (— → 87/87 ✅)
  3. Mathematical-Proof-Plan.md verification dates
  4. Verification record in docs/proofs/verification-records/

Usage:
  python3 verification/autoreconciler/autoreconcile_cg.py --group G2 --layer 1
  python3 verification/autoreconciler/autoreconcile_cg.py --group G2 --all-layers
  python3 verification/autoreconciler/autoreconcile_cg.py --group G2 --layer 1 --dry-run
  python3 verification/autoreconciler/autoreconcile_cg.py --status
"""

import argparse
import json
import logging
import re
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Optional

# ── Paths ─────────────────────────────────────────────────────
ROOT = Path(__file__).resolve().parent.parent.parent
RECONCILER_DIR = Path(__file__).resolve().parent
CONFIG_PATH = RECONCILER_DIR / "config.json"
RESULTS_PATH = RECONCILER_DIR / "results.tsv"
LOG_PATH = RECONCILER_DIR / "campaign.log"
REVIEWS_DIR = ROOT / "docs" / "proofs" / "reviews"
THEMATIC_GROUPS_PATH = ROOT / "docs" / "proofs" / "THEMATIC-GROUPS.md"
PROOF_PLAN_PATH = ROOT / "docs" / "Mathematical-Proof-Plan.md"
VERIFICATION_RECORDS_DIR = ROOT / "docs" / "proofs" / "verification-records"

# Import group metadata from autoverifier
sys.path.insert(0, str(ROOT / "verification" / "autoverifier"))
from autoverify_cg import (
    GROUP_METADATA, extract_group_section, extract_coherence_checklist,
    extract_json_from_output
)


# ── Config & Logging ──────────────────────────────────────────

def load_config() -> dict:
    with open(CONFIG_PATH) as f:
        return json.load(f)


def setup_logging(config: dict) -> logging.Logger:
    logger = logging.getLogger("autoreconcile-cg")
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


# ── Audit Report Parsing ─────────────────────────────────────

def collect_layer_results(group: str, layer: int) -> dict:
    """Collect all module results for a group/layer from report files."""
    group_dir = REVIEWS_DIR / group
    if not group_dir.exists():
        return {}

    layer_patterns = {
        1: "Coherence",
        2: "Validity",
        3: "Adversarial",
    }
    pattern = layer_patterns.get(layer, "")

    results = {
        "modules": {},
        "total_checks": 0,
        "total_passed": 0,
        "total_failed": 0,
        "total_noted": 0,
    }

    for report_file in sorted(group_dir.glob(f"*{pattern}*Findings.md")):
        content = report_file.read_text()

        # Extract JSON from report
        json_blocks = re.findall(r'```json\s*\n(.*?)\n\s*```', content, re.DOTALL)
        report_json = None
        for block in reversed(json_blocks):
            try:
                report_json = json.loads(block)
                break
            except json.JSONDecodeError:
                continue

        if not report_json:
            continue

        module_id = report_json.get("module", "")
        if not module_id:
            continue

        if layer == 1:
            checks = report_json.get("checks_total", 0)
            passed = report_json.get("checks_passed", 0)
            failed = report_json.get("checks_failed", 0)
            noted = report_json.get("checks_noted", 0)
            overall = report_json.get("overall_result", "PENDING")
        elif layer == 2:
            sound = report_json.get("sound", 0)
            qualified = report_json.get("qualified", 0)
            weak = report_json.get("weak", 0)
            invalid = report_json.get("invalid", 0)
            smuggled = report_json.get("smuggled", 0)
            checks = report_json.get("checks_total", sound + qualified + weak + invalid)
            passed = sound + qualified
            failed = weak + invalid
            noted = smuggled
            overall = "FAIL" if invalid > 0 else "PASS"
        elif layer == 3:
            survived = report_json.get("survived", 0)
            dented = report_json.get("dented", 0)
            cracked = report_json.get("cracked", 0)
            broken = report_json.get("broken", 0)
            checks = report_json.get("attacks_total", survived + dented + cracked + broken)
            passed = survived
            failed = cracked + broken
            noted = dented
            overall = "FAIL" if broken > 0 else "PASS"
        else:
            continue

        results["modules"][module_id] = {
            "checks": checks,
            "passed": passed,
            "failed": failed,
            "noted": noted,
            "overall": overall,
            "file": report_file.name,
        }
        results["total_checks"] += checks
        results["total_passed"] += passed
        results["total_failed"] += failed
        results["total_noted"] += noted

    return results


def compute_layer_summary(results: dict, layer: int) -> str:
    """Compute the summary string for the audit progress tracker."""
    if not results["modules"]:
        return "—"

    total = results["total_checks"]
    passed = results["total_passed"]
    failed = results["total_failed"]

    if layer == 3:
        # Adversarial: compute resilience score
        noted = results["total_noted"]  # dented
        if total > 0:
            resilience = (passed * 3 + noted) / (total * 3) * 100
            return f"{total}/{total} ({resilience:.0f}%) ✅" if failed == 0 else f"{passed}/{total} ({resilience:.0f}%)"
        return "—"

    # Layer 1 & 2
    if failed == 0:
        return f"{passed}/{total} ✅"
    else:
        return f"{passed}/{total} ({failed} FAIL)"


# ── Update: Coherence Checklist ───────────────────────────────

def update_coherence_checklist(group: str, results: dict,
                               logger: logging.Logger, dry_run: bool) -> bool:
    """Update the coherence checklist in THEMATIC-GROUPS.md based on results."""
    if not results["modules"]:
        logger.info("  No coherence results to reconcile")
        return False

    all_pass = results["total_failed"] == 0
    content = THEMATIC_GROUPS_PATH.read_text()

    # Find the group's coherence checklist section
    # Pattern: ### Coherence checklist (possibly with completion annotation)
    group_section_start = content.find(f"## {group}:")
    if group_section_start == -1:
        logger.warning(f"  Could not find {group} section in THEMATIC-GROUPS.md")
        return False

    # Find next group or appendix
    next_group = re.search(r'^## G\d+:|^## Appendix', content[group_section_start + 1:], re.MULTILINE)
    group_end = group_section_start + 1 + next_group.start() if next_group else len(content)
    group_text = content[group_section_start:group_end]

    # Find checklist header within group
    checklist_match = re.search(r'### Coherence checklist.*\n', group_text)
    if not checklist_match:
        logger.warning(f"  No coherence checklist found for {group}")
        return False

    checklist_start = group_section_start + checklist_match.start()

    # Build updated checklist header
    if all_pass:
        date_str = datetime.now().strftime("%Y-%m-%d")
        new_header = f"### Coherence checklist — [COMPLETE ({date_str})](reviews/{group}/{group}-{GROUP_METADATA[group]['short']}-Coherence-Audit.md)\n"
    else:
        new_header = f"### Coherence checklist — {results['total_passed']}/{results['total_checks']} PASS\n"

    # Replace the header line
    header_end = group_section_start + checklist_match.end()
    old_header = content[checklist_start:header_end]

    if dry_run:
        logger.info(f"  [DRY RUN] Would update checklist header:")
        logger.info(f"    OLD: {old_header.strip()}")
        logger.info(f"    NEW: {new_header.strip()}")
    else:
        content = content[:checklist_start] + new_header + content[header_end:]

    # If all pass, mark all checklist items as [x]
    if all_pass:
        # Find all "- [ ]" in the checklist area (between header and next ---)
        checklist_area_start = checklist_start + len(new_header)
        next_section = content.find("---", checklist_area_start)
        if next_section == -1:
            next_section = group_end

        checklist_area = content[checklist_area_start:next_section]
        updated_area = checklist_area.replace("- [ ]", "- [x]")

        if checklist_area != updated_area:
            if dry_run:
                unchecked = checklist_area.count("- [ ]")
                logger.info(f"  [DRY RUN] Would check {unchecked} checklist items")
            else:
                content = content[:checklist_area_start] + updated_area + content[next_section:]

    if not dry_run:
        THEMATIC_GROUPS_PATH.write_text(content)
        logger.info(f"  Updated coherence checklist for {group}")

    return True


# ── Update: Progress Tracker ─────────────────────────────────

def update_progress_tracker(group: str, layer: int, summary: str,
                            logger: logging.Logger, dry_run: bool) -> bool:
    """Update the audit progress tracker table in THEMATIC-GROUPS.md."""
    content = THEMATIC_GROUPS_PATH.read_text()

    # Find the tracker table row for this group
    # Pattern: | G2 | — | — | — | Paper 2 | Not started |
    row_pattern = rf'(\| {re.escape(group)} \|)(.*?)(\|[^|]*\|[^|]*\|)\s*$'
    match = re.search(row_pattern, content, re.MULTILINE)

    if not match:
        logger.warning(f"  Could not find {group} row in progress tracker")
        return False

    # Parse existing columns
    full_match = match.group(0)
    prefix = match.group(1)  # | G2 |
    middle = match.group(2)  # layer columns
    suffix = match.group(3)  # Paper + Status columns

    # Split middle into 3 layer columns
    cols = [c.strip() for c in middle.split("|")]
    # cols should be: ['', 'layer1', 'layer2', 'layer3', '']
    # Remove empty strings from split
    cols = [c for c in cols if c or cols.index(c) == 0]

    # Pad if needed
    while len(cols) < 3:
        cols.append("—")

    # Map layer to column index
    layer_idx = layer - 1  # 0-based
    if layer_idx < len(cols):
        old_val = cols[layer_idx]
        cols[layer_idx] = summary

    # Reconstruct row
    new_middle = " | ".join(cols)
    new_row = f"{prefix} {new_middle} {suffix}"

    if dry_run:
        logger.info(f"  [DRY RUN] Progress tracker {group} Layer {layer}:")
        logger.info(f"    OLD: {old_val}")
        logger.info(f"    NEW: {summary}")
    else:
        content = content.replace(full_match, new_row)

        # Update status column if all layers have results
        all_done = all(c != "—" and "FAIL" not in c for c in cols)
        if all_done:
            content = content.replace(
                new_row,
                new_row.replace("Not started", "**AUDIT COMPLETE**")
            )

        THEMATIC_GROUPS_PATH.write_text(content)
        logger.info(f"  Updated progress tracker: {group} Layer {layer} → {summary}")

    return True


# ── Update: Verification Record ───────────────────────────────

def generate_verification_record(group: str, layer: int, results: dict,
                                 logger: logging.Logger, dry_run: bool) -> bool:
    """Generate a verification record for the completed audit layer."""
    meta = GROUP_METADATA[group]
    layer_names = {1: "Coherence", 2: "Validity", 3: "Adversarial"}
    layer_name = layer_names[layer]
    date_str = datetime.now().strftime("%Y-%m-%d")

    summary = compute_layer_summary(results, layer)

    record = f"""# {group} {meta['name']} — Layer {layer} ({layer_name}) Verification Record

> **Date:** {date_str}
> **Tool:** AutoVerifier-CG + AutoReconciler-CG
> **Group:** {group} — {meta['name']}
> **Layer:** {layer} ({layer_name})
> **Result:** {summary}

---

## Summary

| Metric | Value |
|--------|-------|
| Total checks | {results['total_checks']} |
| Passed | {results['total_passed']} |
| Failed | {results['total_failed']} |
| Noted | {results['total_noted']} |
| Modules completed | {len(results['modules'])} |

## Module Results

| Module | Checks | Passed | Failed | Result | Report |
|--------|--------|--------|--------|--------|--------|
"""

    for mid, mod in sorted(results["modules"].items()):
        record += (
            f"| {mid} | {mod['checks']} | {mod['passed']} | {mod['failed']} "
            f"| {mod['overall']} | [{mod['file']}](../reviews/{group}/{mod['file']}) |\n"
        )

    record += f"""
## Findings Requiring Attention

"""
    has_issues = False
    for mid, mod in sorted(results["modules"].items()):
        if mod["failed"] > 0:
            has_issues = True
            record += f"- **{mid}**: {mod['failed']} failed checks — see [{mod['file']}](../reviews/{group}/{mod['file']})\n"

    if not has_issues:
        record += "None — all checks passed.\n"

    record += f"""
---

*Generated by AutoReconciler-CG on {date_str}*
"""

    record_filename = f"{group}-Layer{layer}-{layer_name}-Verification-Record-{date_str}.md"
    record_path = VERIFICATION_RECORDS_DIR / record_filename

    if dry_run:
        logger.info(f"  [DRY RUN] Would write verification record: {record_filename}")
    else:
        VERIFICATION_RECORDS_DIR.mkdir(parents=True, exist_ok=True)
        record_path.write_text(record)
        logger.info(f"  Verification record: {record_path.relative_to(ROOT)}")

    return True


# ── Status Overview ───────────────────────────────────────────

def show_status(logger: logging.Logger):
    """Show current audit status across all groups."""
    print(f"\n{'Group':<8} {'Name':<30} {'L1 (Coherence)':<20} {'L2 (Validity)':<20} {'L3 (Adversarial)':<20}")
    print("-" * 100)

    for gid, meta in GROUP_METADATA.items():
        l1 = collect_layer_results(gid, 1)
        l2 = collect_layer_results(gid, 2)
        l3 = collect_layer_results(gid, 3)

        s1 = compute_layer_summary(l1, 1) if l1.get("modules") else "—"
        s2 = compute_layer_summary(l2, 2) if l2.get("modules") else "—"
        s3 = compute_layer_summary(l3, 3) if l3.get("modules") else "—"

        print(f"{gid:<8} {meta['name']:<30} {s1:<20} {s2:<20} {s3:<20}")

    print()


# ── Main ──────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="AutoReconciler-CG: Update tracking after audit cycles"
    )
    parser.add_argument("--group", type=str,
                        help="Group to reconcile (e.g., G2)")
    parser.add_argument("--layer", type=int, choices=[1, 2, 3],
                        help="Reconcile this layer (1=Coherence, 2=Validity, 3=Adversarial)")
    parser.add_argument("--all-layers", action="store_true",
                        help="Reconcile all layers that have results")
    parser.add_argument("--status", action="store_true",
                        help="Show audit status across all groups and exit")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be updated without making changes")
    args = parser.parse_args()

    config = load_config()
    logger = setup_logging(config)

    if args.status:
        show_status(logger)
        return

    if not args.group:
        parser.print_help()
        return

    group = args.group.upper()
    if group not in GROUP_METADATA:
        logger.error(f"Unknown group: {group}")
        return

    logger.info("=" * 60)
    logger.info("  AutoReconciler-CG: Update Tracking")
    logger.info(f"  Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    logger.info(f"  Group: {group}")
    logger.info("=" * 60)

    # Determine layers to reconcile
    if args.all_layers:
        layers = [1, 2, 3]
    elif args.layer:
        layers = [args.layer]
    else:
        layers = [1, 2, 3]

    layer_names = {1: "Coherence", 2: "Validity", 3: "Adversarial"}

    for layer in layers:
        logger.info(f"\nLayer {layer} ({layer_names[layer]})")
        logger.info("-" * 40)

        results = collect_layer_results(group, layer)

        if not results["modules"]:
            logger.info(f"  No results found for {group} Layer {layer} — skipping")
            continue

        summary = compute_layer_summary(results, layer)
        logger.info(f"  Results: {summary}")
        logger.info(f"  Modules: {', '.join(sorted(results['modules'].keys()))}")

        # Update coherence checklist (Layer 1 only)
        if layer == 1 and config["updates"]["thematic_groups_checklist"]:
            update_coherence_checklist(group, results, logger, args.dry_run)

        # Update progress tracker
        if config["updates"]["thematic_groups_tracker"]:
            update_progress_tracker(group, layer, summary, logger, args.dry_run)

        # Generate verification record
        if config["updates"]["verification_record"]:
            generate_verification_record(group, layer, results, logger, args.dry_run)

    logger.info(f"\n{'=' * 60}")
    logger.info("  RECONCILIATION COMPLETE")
    logger.info(f"{'=' * 60}")


if __name__ == "__main__":
    main()
