#!/usr/bin/env python3
"""
N-Scaling Large-N Campaign (Priority 4): N = 50k and 100k
==========================================================

Extends the n_scaling campaign to N ≈ 50,000 and N ≈ 100,000 to:
  1. Confirm power-law scaling T ~ N^(-η) holds over 2+ decades
  2. Measure η to higher precision (currently η_global ≈ 0.675, η_local ≈ 0.487)
  3. Look for logarithmic corrections (expected from asymptotic freedom analog)

Architecture:
  - Same as prior campaigns: soup_multi_stella_wf, lattice-size 2, cross-rate 0
  - 2 N values × 2 pairing modes × 5 seeds × 4 stellae = 80 nucleation experiments
  - Reduced epochs (2M) since emergence is fast at large N
    (N=26,666 median T_emerge ≈ 200k–500k, so 2M gives 4–10× headroom)

Runtime estimates (from extrapolation of wall times):
  n_sub=548 (N=50,050): ~56h per run at 5M epochs → ~22h at 2M epochs
  n_sub=775 (N=100,104): ~118h per run at 5M epochs → ~47h at 2M epochs

Related Documents:
  - INVESTIGATION-R_STELLA.md, Priority 4
  - Base campaign: n_scaling_campaign.py
  - Extension campaign: n_scaling_extension_campaign.py

Usage:
  python3 stella_lang/n_scaling_large_n_campaign.py --dry-run
  python3 stella_lang/n_scaling_large_n_campaign.py --parallel 2 --threads 16
  python3 stella_lang/n_scaling_large_n_campaign.py --resume --parallel 2 --threads 16
  python3 stella_lang/n_scaling_large_n_campaign.py --nsub 548  # Run only N≈50k
"""

import argparse
import subprocess
import sys
import time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

# ============================================================================
# CAMPAIGN PARAMETERS
# ============================================================================

# Large-N probe values
# N = 2 * floor((2 * n_sub^2 + 2) / 24)
NSUB_VALUES = [548, 775]
N_TILES = {548: 50050, 775: 100104}

SEEDS = [42, 123, 456, 789, 1024]
PAIRING_MODES = ["local", "global"]
EPOCHS = 2_000_000  # Reduced from 5M — emergence is fast at large N

CENSUS_INTERVAL = 50_000   # Finer census for better T_emerge resolution
CHECK_INTERVAL = 50_000
LOG_INTERVAL = 100_000
CROSS_RATE = 0.0
LATTICE_SIZE = 2

# ============================================================================
# PATHS
# ============================================================================

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
BINARY = REPO_ROOT / "verification" / "stella_lang" / "soup_multi_stella_wf"
LOG_DIR = REPO_ROOT / "verification" / "stella_lang" / "n_scaling_logs"


def compute_n_tiles(n_sub):
    n_sites = 2 * n_sub * n_sub + 2
    return 2 * (n_sites // 24)


def log_filename(n_sub, pairing, seed):
    return LOG_DIR / f"nsub{n_sub}_{pairing}_s{seed}.log"


def build_command(n_sub, pairing, seed, threads_per_run=16):
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
    print(f"[DONE]  {label} — {status} in {elapsed:.0f}s ({elapsed/3600:.1f}h)")
    sys.stdout.flush()
    return label, status, elapsed


def get_pending_runs(args):
    nsub_list = [args.nsub] if args.nsub else NSUB_VALUES
    pairing_list = [args.pairing] if args.pairing else PAIRING_MODES
    seed_list = SEEDS[:args.seeds] if args.seeds else SEEDS

    runs = []
    for n_sub in nsub_list:
        for pairing in pairing_list:
            for seed in seed_list:
                logfile = log_filename(n_sub, pairing, seed)
                if args.resume and logfile.exists():
                    try:
                        text = logfile.read_text()
                        if "Completed" in text and "epochs in" in text:
                            print(f"[SKIP] n_sub={n_sub} {pairing} seed={seed} (already complete)")
                            continue
                    except Exception:
                        pass
                runs.append((n_sub, pairing, seed))
    return runs


def estimate_runtime(runs, threads_per_run):
    """Estimate total wall time based on prior campaign benchmarks."""
    # Empirical: wall_time ≈ k * N^1.1 * epochs/5M, from prior runs
    # N=26666 at 5M epochs: ~100,000s with 16 threads
    k = 100_000 / (26666 ** 1.1)  # calibration constant

    total_seconds = 0
    for n_sub, _, _ in runs:
        N = compute_n_tiles(n_sub)
        est = k * (N ** 1.1) * (EPOCHS / 5_000_000)
        total_seconds += est

    return total_seconds


def main():
    parser = argparse.ArgumentParser(
        description="N-scaling large-N campaign (Priority 4): N ≈ 50k, 100k")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--parallel", type=int, default=1)
    parser.add_argument("--threads", type=int, default=16,
                        help="Total CPU threads to distribute (default: 16)")
    parser.add_argument("--nsub", type=int, choices=NSUB_VALUES,
                        help="Run only a specific n_sub value")
    parser.add_argument("--pairing", choices=PAIRING_MODES,
                        help="Run only a specific pairing mode")
    parser.add_argument("--seeds", type=int, default=None,
                        help="Use first N seeds only (default: all 5)")
    args = parser.parse_args()

    threads_per_run = max(1, args.threads // max(1, args.parallel))

    if not BINARY.exists():
        print(f"ERROR: Binary not found: {BINARY}")
        print(f"Compile with:")
        print(f"  cc -O3 -march=native -ffast-math -flto -o {BINARY} "
              f"{BINARY.parent / 'soup_multi_stella.c'} -lm -lpthread")
        sys.exit(1)

    LOG_DIR.mkdir(parents=True, exist_ok=True)

    runs = get_pending_runs(args)
    n_total = len(runs)
    n_stellae = n_total * (LATTICE_SIZE ** 3 // 2)

    # Estimate runtime
    est_serial = estimate_runtime(runs, threads_per_run)
    est_parallel = est_serial / max(1, args.parallel)

    nsub_display = [args.nsub] if args.nsub else NSUB_VALUES

    print("=" * 70)
    print("N-Scaling Large-N Campaign (Priority 4)")
    print("=" * 70)
    print(f"  N values:     {[N_TILES[n] for n in nsub_display]}")
    print(f"  Pairing:      {args.pairing or 'local + global'}")
    print(f"  Seeds:        {SEEDS[:args.seeds] if args.seeds else SEEDS}")
    print(f"  Epochs/run:   {EPOCHS:,}")
    print(f"  Census:       every {CENSUS_INTERVAL:,} epochs")
    print(f"  Runs pending: {n_total}")
    print(f"  Stellae:      {n_stellae} independent nucleation experiments")
    print(f"  Parallelism:  {args.parallel} runs × {threads_per_run} threads = {args.parallel * threads_per_run} total")
    print(f"  Est. runtime: {est_parallel/3600:.0f}h ({est_parallel/86400:.1f} days) "
          f"at {args.parallel}× parallel")
    print(f"  Log dir:      {LOG_DIR}")
    print("=" * 70)

    if n_total == 0:
        print("\nAll runs already complete!")
        print(f"\nRun combined analysis with:")
        print(f"  python3 stella_lang/n_scaling_analysis.py --plot")
        return

    if args.dry_run:
        print()
        for n_sub, pairing, seed in runs:
            run_single(n_sub, pairing, seed, dry_run=True,
                       threads_per_run=threads_per_run)
        print(f"\n  Total: {n_total} runs, {n_stellae} stellae")
        print(f"  Est. runtime: {est_parallel/3600:.0f}h ({est_parallel/86400:.1f} days)")
        return

    t_start = time.time()

    if args.parallel <= 1:
        results = []
        for i, (n_sub, pairing, seed) in enumerate(runs):
            print(f"\n--- Run {i+1}/{n_total} ---")
            result = run_single(n_sub, pairing, seed,
                                threads_per_run=threads_per_run)
            results.append(result)
    else:
        results = []
        with ProcessPoolExecutor(max_workers=args.parallel) as executor:
            futures = {
                executor.submit(run_single, n_sub, pairing, seed,
                                threads_per_run=threads_per_run): (n_sub, pairing, seed)
                for n_sub, pairing, seed in runs
            }
            for future in as_completed(futures):
                results.append(future.result())

    elapsed = time.time() - t_start

    print("\n" + "=" * 70)
    print("LARGE-N CAMPAIGN COMPLETE")
    print("=" * 70)
    n_ok = sum(1 for _, s, _ in results if s == "OK")
    n_fail = sum(1 for _, s, _ in results if s != "OK")
    print(f"  Successful: {n_ok}/{len(results)}")
    if n_fail > 0:
        print(f"  Failed:     {n_fail}")
        for label, status, _ in results:
            if status != "OK":
                print(f"    {label}: {status}")
    print(f"  Total time: {elapsed:.0f}s ({elapsed/3600:.1f}h)")
    print(f"\nRun combined analysis with:")
    print(f"  python3 stella_lang/n_scaling_analysis.py --plot")


if __name__ == "__main__":
    main()
