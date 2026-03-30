#!/usr/bin/env python3
"""
AutoCycle-CG: Full Audit-Fix-Verify-Reconcile Pipeline
========================================================

Orchestrates the complete audit cycle for a thematic group:

  1. AutoVerifier   — audit the group (produces findings)
  2. AutoInvestigator — fix FAIL findings (commits on review branch)
  3. AutoVerifier   — re-audit to confirm fixes (produces clean reports)
  4. AutoReconciler — update tracking artifacts

Each phase only runs if the previous phase warrants it:
  - Phase 2 skipped if Phase 1 finds no FAILs
  - Phase 3 skipped if Phase 2 resolved nothing
  - Phase 4 runs regardless (updates tracking to current state)

Usage:
  python3 verification/autocycle_cg.py --group G1 --layer 1
  python3 verification/autocycle_cg.py --group G1 --layer 1 --max-parallel 6
  python3 verification/autocycle_cg.py --group G1 --all-layers
  python3 verification/autocycle_cg.py --group G1 --layer 1 --skip-investigate
  python3 verification/autocycle_cg.py --group G1 --layer 1 --start-from 2
  python3 verification/autocycle_cg.py --group G1 --layer 1 --dry-run
  python3 verification/autocycle_cg.py --status
"""

import argparse
import json
import logging
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

# ── Paths ─────────────────────────────────────────────────────
ROOT = Path(__file__).resolve().parent.parent
VERIFICATION_DIR = Path(__file__).resolve().parent
AUTOVERIFIER = VERIFICATION_DIR / "autoverifier" / "autoverify_cg.py"
AUTOINVESTIGATOR = VERIFICATION_DIR / "autoinvestigator" / "autoinvestigate_cg.py"
AUTORECONCILER = VERIFICATION_DIR / "autoreconciler" / "autoreconcile_cg.py"
LOG_PATH = VERIFICATION_DIR / "autocycle_campaign.log"

GROUP_METADATA = {
    "G1":  "Geometric Foundation",
    "G2":  "Gauge Theory & Confinement",
    "G3":  "Time & Entropy",
    "G4":  "Chirality & CP Violation",
    "G5":  "Mass Generation",
    "G6":  "QCD Scale Derivation",
    "G7":  "Quantum Foundations",
    "G8":  "Emergent Gravity",
    "G9":  "Electroweak Sector",
    "G10": "Renormalization & Yang-Mills",
    "G11": "Bootstrap & Uniqueness",
    "G12": "Predictions & Falsifiability",
}

LAYER_NAMES = {1: "Coherence", 2: "Validity", 3: "Adversarial"}


# ── Logging ───────────────────────────────────────────────────

def setup_logging() -> logging.Logger:
    logger = logging.getLogger("autocycle-cg")
    logger.setLevel(logging.DEBUG)

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


# ── Phase Runners ─────────────────────────────────────────────

def run_phase(phase_name: str, cmd: list[str], logger: logging.Logger,
              dry_run: bool = False) -> tuple[int, str]:
    """Run a phase subprocess. Returns (returncode, stdout+stderr)."""
    cmd_str = " ".join(cmd)
    logger.info(f"  Command: python3 {cmd_str}")

    if dry_run:
        logger.info(f"  [DRY RUN] Would execute: python3 {cmd_str}")
        return 0, ""

    try:
        result = subprocess.run(
            ["python3"] + cmd,
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=8 * 3600,  # 8 hour max per phase
        )
        output = result.stdout + result.stderr

        # Stream the output to the logger
        for line in output.strip().split("\n"):
            if line.strip():
                logger.info(f"  │ {line.rstrip()}")

        return result.returncode, output

    except subprocess.TimeoutExpired:
        logger.error(f"  {phase_name} timed out after 8 hours")
        return 1, "TIMEOUT"
    except Exception as e:
        logger.error(f"  {phase_name} failed: {e}")
        return 1, str(e)


def count_fails_in_output(output: str) -> int:
    """Count FAIL modules from verifier output."""
    import re
    # Look for the autoverifier summary line: "Layer N has X FAIL(s)"
    m = re.search(r'Layer \d+ has (\d+) FAIL', output)
    if m:
        return int(m.group(1))
    # Fallback: count [---] markers (one per FAIL module)
    return output.count("[---]")


def count_check_failures_in_output(output: str) -> int:
    """Count total individual check failures across all modules.

    Handles two output formats:
      Layer 1/2: [+++] V5: 25/30 passed, 5 failed, 0 noted (552s)
      Layer 3:   [+++] A1: Resilience: 85% (5S 2D 1C 0B) (300s)

    For Layer 1/2, sums the 'N failed' counts.
    For Layer 3, sums cracked (C) + broken (B) counts.
    """
    import re
    total = 0
    # Layer 1/2 format: "N failed"
    for m in re.finditer(r'\[\+\+\+\].*?(\d+) failed|\[---\].*?(\d+) failed', output):
        total += int(m.group(1) or m.group(2))
    # Layer 3 format: "(XS YD ZC WB)" — count cracked + broken
    for m in re.finditer(r'\(\d+S\s+\d+D\s+(\d+)C\s+(\d+)B\)', output):
        total += int(m.group(1)) + int(m.group(2))
    return total


def count_resolved_in_output(output: str) -> int:
    """Count resolved findings from investigator output."""
    import re
    m = re.search(r'Resolved:\s+(\d+)', output)
    if m:
        return int(m.group(1))
    return output.count("[+++]")


# ── Main Cycle ────────────────────────────────────────────────

def run_cycle(group: str, layer: int, max_parallel: int,
              logger: logging.Logger, dry_run: bool = False,
              skip_investigate: bool = False, start_from: int = 1,
              max_rounds: int = 3):
    """Run the full audit cycle for one group/layer."""

    layer_name = LAYER_NAMES[layer]
    logger.info(f"")
    logger.info(f"{'='*60}")
    logger.info(f"  AUDIT CYCLE: {group} Layer {layer} ({layer_name})")
    logger.info(f"  Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    logger.info(f"  Max parallel: {max_parallel}")
    if start_from > 1:
        logger.info(f"  Starting from phase {start_from}")
    logger.info(f"{'='*60}")

    cycle_start = time.time()
    round_num = 0

    while round_num < max_rounds:
        round_num += 1
        logger.info(f"\n{'─'*60}")
        logger.info(f"  ROUND {round_num}/{max_rounds}")
        logger.info(f"{'─'*60}")

        # ── Phase 1: Verify ──────────────────────────────────
        if start_from <= 1:
            logger.info(f"\n  ▶ PHASE 1: AutoVerifier ({group} Layer {layer})")
            logger.info(f"  {'─'*50}")

            cmd = [
                str(AUTOVERIFIER),
                "--group", group,
                "--layer", str(layer),
                "--max-parallel", str(max_parallel),
            ]

            rc, output = run_phase("AutoVerifier", cmd, logger, dry_run)

            if rc != 0 and not dry_run:
                logger.error(f"  AutoVerifier failed (exit code {rc})")
                logger.info(f"  Cycle aborted — fix the error and re-run")
                return

            fail_count = count_fails_in_output(output) if not dry_run else 0
            check_fail_count = count_check_failures_in_output(output) if not dry_run else 0
            logger.info(f"\n  Phase 1 result: {fail_count} FAIL module(s), "
                        f"{check_fail_count} individual check failure(s)")

            if fail_count == 0 and check_fail_count == 0:
                logger.info(f"  All clear — skipping investigation, proceeding to reconcile")
                start_from = 1  # reset for next round
                break  # skip to reconcile
            elif fail_count == 0:
                logger.info(f"  No module FAILs, but {check_fail_count} sub-module findings "
                            f"(WEAK/SMUGGLED) — running investigator")
        else:
            logger.info(f"\n  ▶ PHASE 1: Skipped (--start-from {start_from})")
            fail_count = 1  # assume there are findings to investigate

        # ── Phase 2: Investigate ─────────────────────────────
        if start_from <= 2 and not skip_investigate:
            logger.info(f"\n  ▶ PHASE 2: AutoInvestigator ({group} Layer {layer})")
            logger.info(f"  {'─'*50}")

            cmd = [
                str(AUTOINVESTIGATOR),
                "--group", group,
                "--layer", str(layer),
            ]

            rc, output = run_phase("AutoInvestigator", cmd, logger, dry_run)

            if rc != 0 and not dry_run:
                logger.error(f"  AutoInvestigator failed (exit code {rc})")
                logger.info(f"  Continuing to re-verify anyway...")

            resolved_count = count_resolved_in_output(output) if not dry_run else 0
            logger.info(f"\n  Phase 2 result: {resolved_count} findings resolved")

            if resolved_count == 0 and not dry_run:
                logger.info(f"  Nothing resolved — stopping cycle (manual intervention needed)")
                break
        elif skip_investigate:
            logger.info(f"\n  ▶ PHASE 2: Skipped (--skip-investigate)")
        else:
            logger.info(f"\n  ▶ PHASE 2: Skipped (--start-from {start_from})")

        # Reset start_from after first round
        start_from = 1

        # ── Phase 3: Re-verify ───────────────────────────────
        logger.info(f"\n  ▶ PHASE 3: AutoVerifier RE-AUDIT ({group} Layer {layer})")
        logger.info(f"  {'─'*50}")

        cmd = [
            str(AUTOVERIFIER),
            "--group", group,
            "--layer", str(layer),
            "--max-parallel", str(max_parallel),
        ]

        rc, output = run_phase("AutoVerifier (re-audit)", cmd, logger, dry_run)

        fail_count = count_fails_in_output(output) if not dry_run else 0
        check_fail_count = count_check_failures_in_output(output) if not dry_run else 0
        logger.info(f"\n  Phase 3 result: {fail_count} FAIL module(s), "
                    f"{check_fail_count} individual check failure(s)")

        if fail_count == 0 and check_fail_count == 0:
            logger.info(f"  All clear — proceeding to reconcile")
            break
        elif fail_count == 0:
            logger.info(f"  No module FAILs, {check_fail_count} sub-module findings remain — "
                        f"{'will retry' if round_num < max_rounds else 'proceeding to reconcile'}")
            if round_num >= max_rounds:
                break
        else:
            logger.info(f"  {fail_count} FAILs remain — "
                        f"{'will retry' if round_num < max_rounds else 'max rounds reached'}")

    # ── Phase 4: Reconcile ───────────────────────────────────
    logger.info(f"\n  ▶ PHASE 4: AutoReconciler ({group} Layer {layer})")
    logger.info(f"  {'─'*50}")

    cmd = [
        str(AUTORECONCILER),
        "--group", group,
        "--layer", str(layer),
    ]

    rc, output = run_phase("AutoReconciler", cmd, logger, dry_run)

    # ── Summary ──────────────────────────────────────────────
    total_time = time.time() - cycle_start

    logger.info(f"\n{'='*60}")
    logger.info(f"  CYCLE COMPLETE: {group} Layer {layer} ({layer_name})")
    logger.info(f"  Rounds: {round_num}")
    logger.info(f"  Time: {total_time/60:.1f} min")
    logger.info(f"  Remaining FAILs: {fail_count}")
    logger.info(f"{'='*60}")

    if fail_count > 0:
        logger.info(f"")
        logger.info(f"  ⚠ Some findings could not be auto-resolved.")
        logger.info(f"  Review the reports in docs/proofs/reviews/{group}/")
        logger.info(f"  Then re-run: python3 verification/autocycle_cg.py --group {group} --layer {layer}")


# ── Status ────────────────────────────────────────────────────

def show_status(logger: logging.Logger):
    """Delegate to AutoReconciler --status."""
    subprocess.run(
        ["python3", str(AUTORECONCILER), "--status"],
        cwd=ROOT,
    )


# ── CLI ───────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="AutoCycle-CG: Full Audit-Fix-Verify-Reconcile Pipeline"
    )
    parser.add_argument("--group", type=str,
                        help="Group to audit (e.g., G1)")
    parser.add_argument("--layer", type=int, choices=[1, 2, 3],
                        help="Layer to audit (1=Coherence, 2=Validity, 3=Adversarial)")
    parser.add_argument("--all-layers", action="store_true",
                        help="Run cycle for all 3 layers in sequence")
    parser.add_argument("--max-parallel", type=int, default=6,
                        help="Max parallel modules in verifier (default: 6)")
    parser.add_argument("--max-rounds", type=int, default=3,
                        help="Max verify-fix-verify rounds before stopping (default: 3)")
    parser.add_argument("--skip-investigate", action="store_true",
                        help="Skip Phase 2 (investigation) — verify and reconcile only")
    parser.add_argument("--start-from", type=int, default=1, choices=[1, 2, 3, 4],
                        help="Start from this phase (1=verify, 2=investigate, 3=re-verify, 4=reconcile)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would run without executing")
    parser.add_argument("--status", action="store_true",
                        help="Show audit status and exit")

    args = parser.parse_args()
    logger = setup_logging()

    if args.status:
        show_status(logger)
        return

    if not args.group:
        parser.print_help()
        return

    group = args.group.upper()
    if group not in GROUP_METADATA:
        print(f"Unknown group: {group}")
        print(f"Valid: {', '.join(GROUP_METADATA.keys())}")
        sys.exit(1)

    if args.all_layers:
        layers = [1, 2, 3]
    elif args.layer:
        layers = [args.layer]
    else:
        print("Specify --layer or --all-layers")
        sys.exit(1)

    logger.info(f"AutoCycle-CG Pipeline")
    logger.info(f"  Group: {group} — {GROUP_METADATA[group]}")
    logger.info(f"  Layers: {', '.join(LAYER_NAMES[l] for l in layers)}")
    logger.info(f"  Max rounds: {args.max_rounds}")
    logger.info(f"  Parallel: {args.max_parallel}")

    for layer in layers:
        run_cycle(
            group=group,
            layer=layer,
            max_parallel=args.max_parallel,
            logger=logger,
            dry_run=args.dry_run,
            skip_investigate=args.skip_investigate,
            start_from=args.start_from,
            max_rounds=args.max_rounds,
        )

    logger.info(f"\nAll layers complete for {group}.")


if __name__ == "__main__":
    main()
