#!/usr/bin/env python3
"""
Priority 6: η Precision Campaign (P2 follow-up)
=================================================

Goal: Measure η_global and η_local to <1% precision; confirm or reject
η_global = 2/3 and η_local = 1/2 as exact values.

Strategy: Add seeds at N values where we currently have only 12 stellae
(3 seeds × 4 stellae) to bring all N values up to 20 stellae (5 seeds × 4).

Current inventory vs target:
  N = 1,666  (n_sub=100):  20 stellae — complete
  N = 2,520  (n_sub=123):  20 stellae — complete
  N = 2,992  (n_sub=134):  20 stellae — complete
  N = 4,108  (n_sub=157):  20 stellae — complete
  N = 6,666  (n_sub=200):  12 stellae — ADD seeds 789, 1024
  N = 13,348 (n_sub=283):  12 stellae — ADD seeds 789, 1024
  N = 26,666 (n_sub=400):  12 stellae — ADD seeds 789, 1024
  N = 50,050 (n_sub=548):  12 stellae — ADD seeds 789, 1024

New runs: 4 N-values × 2 seeds × 2 pairing modes = 16 simulation runs
New stellae: 4 × 2 × 4 = 32 per pairing mode (64 total)

After campaign: 160 stellae per pairing mode across 8 N values (1.48 decades).

Usage:
  python3 stella_lang/eta_precision_campaign.py --dry-run
  python3 stella_lang/eta_precision_campaign.py --parallel 2 --threads 16
  python3 stella_lang/eta_precision_campaign.py --resume --parallel 2 --threads 16
  python3 stella_lang/eta_precision_campaign.py --nsub 200  # single N value
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

# N values that need additional seeds (currently 12 stellae, target 20)
NSUB_VALUES = [200, 283, 400, 548]
N_TILES = {200: 6666, 283: 13348, 400: 26666, 548: 50050}

# Seeds to add (existing runs used seeds 42, 123, 456)
NEW_SEEDS = [789, 1024]

PAIRING_MODES = ["local", "global"]

# Epoch counts: match original campaigns
# N <= 26,666 used 5M epochs; N = 50,050 used 2M epochs
EPOCHS_BY_NSUB = {200: 5_000_000, 283: 5_000_000, 400: 5_000_000, 548: 2_000_000}

CENSUS_INTERVAL = 50_000
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
    epochs = EPOCHS_BY_NSUB.get(n_sub, 5_000_000)
    cmd = [
        str(BINARY),
        "--lattice-size", str(LATTICE_SIZE),
        "--n-sub", str(n_sub),
        "--epochs", str(epochs),
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
    epochs = EPOCHS_BY_NSUB.get(n_sub, 5_000_000)
    label = f"n_sub={n_sub} N={N} {pairing} seed={seed} ({epochs/1e6:.0f}M ep)"

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
    seed_list = NEW_SEEDS

    runs = []
    for n_sub in nsub_list:
        for pairing in pairing_list:
            for seed in seed_list:
                logfile = log_filename(n_sub, pairing, seed)
                if args.resume and logfile.exists():
                    try:
                        text = logfile.read_text()
                        if "Completed" in text and "epochs in" in text:
                            print(f"[SKIP] n_sub={n_sub} {pairing} seed={seed} "
                                  f"(already complete)")
                            continue
                    except Exception:
                        pass
                runs.append((n_sub, pairing, seed))
    return runs


def estimate_runtime(runs):
    """Estimate total wall time from prior benchmarks."""
    # Empirical: wall_time ~ k * N^1.1 * epochs/5M
    # N=26666 at 5M epochs: ~100,000s with 16 threads
    k = 100_000 / (26666 ** 1.1)
    total = 0
    for n_sub, _, _ in runs:
        N = compute_n_tiles(n_sub)
        epochs = EPOCHS_BY_NSUB.get(n_sub, 5_000_000)
        total += k * (N ** 1.1) * (epochs / 5_000_000)
    return total


def main():
    parser = argparse.ArgumentParser(
        description="Priority 6: η precision campaign — add seeds to reach "
                    "20 stellae per N value")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--resume", action="store_true",
                        help="Skip runs with existing complete logs")
    parser.add_argument("--parallel", type=int, default=1,
                        help="Number of runs to execute in parallel")
    parser.add_argument("--threads", type=int, default=16,
                        help="Total CPU threads to distribute (default: 16)")
    parser.add_argument("--nsub", type=int, choices=NSUB_VALUES,
                        help="Run only a specific n_sub value")
    parser.add_argument("--pairing", choices=PAIRING_MODES,
                        help="Run only a specific pairing mode")
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

    est_serial = estimate_runtime(runs)
    est_parallel = est_serial / max(1, args.parallel)

    print("=" * 70)
    print("Priority 6: η Precision Campaign")
    print("=" * 70)
    print(f"  N values:     {[N_TILES[n] for n in (([args.nsub] if args.nsub else NSUB_VALUES))]}")
    print(f"  New seeds:    {NEW_SEEDS}")
    print(f"  Pairing:      {args.pairing or 'local + global'}")
    print(f"  Runs pending: {n_total}")
    print(f"  New stellae:  {n_stellae} nucleation experiments")
    print(f"  Parallelism:  {args.parallel} runs × {threads_per_run} threads "
          f"= {args.parallel * threads_per_run} total")
    print(f"  Est. runtime: {est_parallel/3600:.0f}h ({est_parallel/86400:.1f} days) "
          f"at {args.parallel}× parallel")
    print(f"  Log dir:      {LOG_DIR}")
    print()
    print("  After completion, run analysis with:")
    print("    # First update n_scaling_results.json with new data")
    print("    python3 stella_lang/n_scaling_analysis.py")
    print("    # Then run C analysis:")
    print("    cc -O2 -o priority6_analysis priority6_analysis.c -lm")
    print("    ./priority6_analysis n_scaling_results.json")
    print("=" * 70)

    if n_total == 0:
        print("\nAll runs already complete!")
        return

    if args.dry_run:
        print()
        for n_sub, pairing, seed in runs:
            run_single(n_sub, pairing, seed, dry_run=True,
                       threads_per_run=threads_per_run)
        print(f"\n  Total: {n_total} runs, {n_stellae} stellae")
        print(f"  Est. runtime: {est_parallel/3600:.0f}h "
              f"({est_parallel/86400:.1f} days)")
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
                                threads_per_run=threads_per_run):
                    (n_sub, pairing, seed)
                for n_sub, pairing, seed in runs
            }
            for future in as_completed(futures):
                results.append(future.result())

    elapsed = time.time() - t_start

    print("\n" + "=" * 70)
    print("η PRECISION CAMPAIGN COMPLETE")
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
    print(f"\nNext steps:")
    print(f"  1. Re-run n_scaling_analysis.py to incorporate new data")
    print(f"  2. Compile and run priority6_analysis.c for η precision analysis")


if __name__ == "__main__":
    main()
