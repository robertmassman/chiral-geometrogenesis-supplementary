#!/usr/bin/env python3
"""
N-Scaling Multi-Seed Simulation Campaign
=========================================

Implements §3.5.3 of Lemma 0.0.XXe-NP: multi-seed simulation campaign
to determine T_emerge(N) scaling and distinguish Model A (Poisson, T∝1/N)
from Model B (cooperative, T∝N^{η-1}).

Architecture:
  - Uses soup_multi_stella_wf with --lattice-size 2 --cross-rate 0
  - Each run has 4 independent stellae (FCC lattice L=2, no inter-stella coupling)
  - Per-stella census every 100K epochs detects emergence time per stella
  - 4 N values × 2 pairing modes × 5 seeds = 40 runs → 160 nucleation experiments

Related Documents:
  - Lemma: docs/proofs/supporting/Lemma-0.0.XXe-Nucleation-Probability-Proof.md §3.5.3
  - Binary: stella_lang/soup_multi_stella_wf

Usage:
  python3 stella_lang/n_scaling_campaign.py                  # launch all
  python3 stella_lang/n_scaling_campaign.py --dry-run        # show commands
  python3 stella_lang/n_scaling_campaign.py --resume         # skip existing logs
  python3 stella_lang/n_scaling_campaign.py --parallel 4     # run 4 at a time (4 threads each)
  python3 stella_lang/n_scaling_campaign.py --nsub 100       # single n_sub
  python3 stella_lang/n_scaling_campaign.py --pairing local  # single mode
  python3 stella_lang/n_scaling_campaign.py --threads 16     # total CPU threads to use
"""

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

# ============================================================================
# CAMPAIGN PARAMETERS (from §3.5.3)
# ============================================================================

# n_sub values and their corresponding N (total tiles per stella)
# N = 2 * floor((2*n_sub^2 + 2) / 24)
NSUB_VALUES = [100, 123, 134, 157]
N_TILES = {100: 1666, 123: 2520, 134: 2992, 157: 4108}

SEEDS = [42, 123, 456, 789, 1024]
PAIRING_MODES = ["local", "global"]
EPOCHS = 5_000_000

# Census and logging intervals
CENSUS_INTERVAL = 100_000   # per-stella full replicator count
CHECK_INTERVAL = 100_000    # global replicator check
LOG_INTERVAL = 100_000      # metrics logging

# Cross rate = 0 to isolate stellae
CROSS_RATE = 0.0
LATTICE_SIZE = 2  # 4 stellae per run (minimum even value)

# ============================================================================
# PATHS
# ============================================================================

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
BINARY = REPO_ROOT / "verification" / "stella_lang" / "soup_multi_stella_wf"
LOG_DIR = REPO_ROOT / "verification" / "stella_lang" / "n_scaling_logs"


def compute_n_tiles(n_sub):
    """Compute total tiles per stella for a given n_sub."""
    n_sites = 2 * n_sub * n_sub + 2
    tiles_per_tetra = n_sites // 24
    return 2 * tiles_per_tetra


def log_filename(n_sub, pairing, seed):
    """Generate log filename for a given run configuration."""
    return LOG_DIR / f"nsub{n_sub}_{pairing}_s{seed}.log"


def build_command(n_sub, pairing, seed, threads_per_run=16):
    """Build the command line for a single run."""
    cmd = [
        str(BINARY),
        "--lattice-size", str(LATTICE_SIZE),
        "--n-sub", str(n_sub),
        "--epochs", str(EPOCHS),
        "--cross-rate", str(CROSS_RATE),
        "--mutation-rate", "0.001",
        "--census-interval", str(CENSUS_INTERVAL),
        "--check-interval", str(CHECK_INTERVAL),
        "--log-interval", str(LOG_INTERVAL),
        "--seed", str(seed),
        "--threads", str(threads_per_run),
    ]
    if pairing == "global":
        cmd.append("--global")
    return cmd


def run_single(n_sub, pairing, seed, dry_run=False, threads_per_run=16):
    """Run a single simulation, writing output to log file."""
    logfile = log_filename(n_sub, pairing, seed)
    cmd = build_command(n_sub, pairing, seed, threads_per_run)

    N = compute_n_tiles(n_sub)
    label = f"n_sub={n_sub} N={N} {pairing} seed={seed}"

    if dry_run:
        print(f"[DRY] {label} (threads={threads_per_run})")
        print(f"  cmd: {' '.join(cmd)}")
        print(f"  log: {logfile}")
        return label, "DRY_RUN", 0

    print(f"[START] {label} (threads={threads_per_run}) -> {logfile.name}")
    sys.stdout.flush()

    t0 = time.time()
    with open(logfile, "w") as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT)
    elapsed = time.time() - t0

    status = "OK" if proc.returncode == 0 else f"FAIL(rc={proc.returncode})"
    print(f"[DONE]  {label} — {status} in {elapsed:.0f}s ({elapsed/60:.1f}m)")
    sys.stdout.flush()
    return label, status, elapsed


def get_pending_runs(args):
    """Get list of (n_sub, pairing, seed) tuples to run."""
    nsub_list = [args.nsub] if args.nsub else NSUB_VALUES
    pairing_list = [args.pairing] if args.pairing else PAIRING_MODES

    runs = []
    for n_sub in nsub_list:
        for pairing in pairing_list:
            for seed in SEEDS:
                logfile = log_filename(n_sub, pairing, seed)
                if args.resume and logfile.exists():
                    # Check if log has completion marker
                    try:
                        text = logfile.read_text()
                        if "Completed" in text and "epochs in" in text:
                            print(f"[SKIP] n_sub={n_sub} {pairing} seed={seed} (already complete)")
                            continue
                    except Exception:
                        pass
                runs.append((n_sub, pairing, seed))
    return runs


def main():
    parser = argparse.ArgumentParser(description="N-scaling multi-seed simulation campaign (§3.5.3)")
    parser.add_argument("--dry-run", action="store_true", help="Print commands without running")
    parser.add_argument("--resume", action="store_true", help="Skip runs with existing complete logs")
    parser.add_argument("--parallel", type=int, default=1, help="Number of concurrent runs (default: 1)")
    parser.add_argument("--threads", type=int, default=16,
                        help="Total CPU threads to distribute across parallel runs (default: 16)")
    parser.add_argument("--nsub", type=int, choices=NSUB_VALUES, help="Run only this n_sub value")
    parser.add_argument("--pairing", choices=PAIRING_MODES, help="Run only this pairing mode")
    args = parser.parse_args()

    # Compute threads per run: split total threads evenly across parallel workers
    threads_per_run = max(1, args.threads // max(1, args.parallel))

    # Verify binary exists
    if not BINARY.exists():
        print(f"ERROR: Binary not found: {BINARY}")
        print("Compile with: cc -O3 -march=native -ffast-math -flto -o soup_multi_stella_wf soup_multi_stella.c -lm -lpthread")
        sys.exit(1)

    # Create log directory
    LOG_DIR.mkdir(parents=True, exist_ok=True)

    # Show campaign summary
    runs = get_pending_runs(args)
    n_total = len(runs)
    n_stellae = n_total * (LATTICE_SIZE**3 // 2)  # 4 stellae per run

    print("=" * 70)
    print("N-Scaling Multi-Seed Campaign (Lemma 0.0.XXe-NP §3.5.3)")
    print("=" * 70)
    print(f"  N values:     {[N_TILES[n] for n in (args.nsub and [args.nsub] or NSUB_VALUES)]}")
    print(f"  Pairing:      {args.pairing or 'local + global'}")
    print(f"  Seeds:        {SEEDS}")
    print(f"  Epochs/run:   {EPOCHS:,}")
    print(f"  Runs pending: {n_total}")
    print(f"  Stellae:      {n_stellae} independent nucleation experiments")
    print(f"  Parallelism:  {args.parallel} runs × {threads_per_run} threads = {args.parallel * threads_per_run} total")
    print(f"  Log dir:      {LOG_DIR}")
    print("=" * 70)

    if n_total == 0:
        print("\nAll runs already complete!")
        return

    if args.dry_run:
        print()
        for n_sub, pairing, seed in runs:
            run_single(n_sub, pairing, seed, dry_run=True, threads_per_run=threads_per_run)
        return

    # Execute runs
    t_campaign_start = time.time()

    if args.parallel <= 1:
        # Sequential execution
        results = []
        for i, (n_sub, pairing, seed) in enumerate(runs):
            print(f"\n--- Run {i+1}/{n_total} ---")
            result = run_single(n_sub, pairing, seed, threads_per_run=threads_per_run)
            results.append(result)
    else:
        # Parallel execution
        results = []
        with ProcessPoolExecutor(max_workers=args.parallel) as executor:
            futures = {
                executor.submit(run_single, n_sub, pairing, seed,
                                threads_per_run=threads_per_run): (n_sub, pairing, seed)
                for n_sub, pairing, seed in runs
            }
            for future in as_completed(futures):
                result = future.result()
                results.append(result)

    t_campaign_end = time.time()
    campaign_elapsed = t_campaign_end - t_campaign_start

    # Summary
    print("\n" + "=" * 70)
    print("CAMPAIGN COMPLETE")
    print("=" * 70)
    n_ok = sum(1 for _, s, _ in results if s == "OK")
    n_fail = sum(1 for _, s, _ in results if s != "OK")
    print(f"  Successful: {n_ok}/{len(results)}")
    if n_fail > 0:
        print(f"  Failed:     {n_fail}")
        for label, status, _ in results:
            if status != "OK":
                print(f"    {label}: {status}")
    print(f"  Total time: {campaign_elapsed:.0f}s ({campaign_elapsed/3600:.1f}h)")
    print(f"\nRun analysis with:")
    print(f"  python3 stella_lang/n_scaling_analysis.py")


if __name__ == "__main__":
    main()
