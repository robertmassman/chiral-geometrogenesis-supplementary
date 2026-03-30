#!/usr/bin/env python3
"""
Priority 5: Sigmoid Midpoint Campaign (P1 follow-up)
=====================================================

Goal: Determine whether the sigmoid midpoint N₅₀ coincides with 3⁶ = 729.

Strategy: Run 13 seeds × 4 stellae = 52 nucleation experiments per N value
across the transition region (N ≈ 170–1,066). This gives ±7% binomial error
at P_nuc ≈ 50%, sufficient to locate N₅₀ within ±50 tiles.

Campaign parameters:
  n_sub values: 32, 40, 45, 50, 55, 58, 60, 62, 65, 70, 75, 80
  Seeds: 42, 123, 456, 789, 1024, 2025, 3141, 4269, 5555, 6174, 7777, 8888, 9999
  Pairing: global only (to match P1 scan conditions)
  Epochs: 5M (same as original scan)
  Stellae per run: 4 (lattice-size=2, FCC)

Total: 12 n_sub × 13 seeds = 156 runs → 624 nucleation experiments
Estimated runtime: ~20h at parallel=4

Usage:
  python3 stella_lang/sigmoid_midpoint_campaign.py --dry-run
  python3 stella_lang/sigmoid_midpoint_campaign.py --parallel 4 --threads 12
  python3 stella_lang/sigmoid_midpoint_campaign.py --resume --parallel 4 --threads 12
  python3 stella_lang/sigmoid_midpoint_campaign.py --nsub 55  # single N value
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

# Dense sampling across the sigmoid transition region
NSUB_VALUES = [32, 40, 45, 50, 55, 58, 60, 62, 65, 70, 75, 80]

# 13 seeds × 4 stellae = 52 experiments per N value
SEEDS = [42, 123, 456, 789, 1024, 2025, 3141, 4269, 5555, 6174, 7777, 8888, 9999]

# Global pairing only (matching P1 scan conditions)
PAIRING_MODES = ["global"]

EPOCHS = 5_000_000
CENSUS_INTERVAL = 50_000
CHECK_INTERVAL = 50_000
LOG_INTERVAL = 100_000
CROSS_RATE = 0.0
MUTATION_RATE = 0.001
LATTICE_SIZE = 2  # FCC lattice → 4 stellae

# ============================================================================
# PATHS
# ============================================================================

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
BINARY = REPO_ROOT / "verification" / "stella_lang" / "soup_multi_stella_wf"
LOG_DIR = REPO_ROOT / "verification" / "stella_lang" / "sigmoid_midpoint_logs"


def compute_n_tiles(n_sub):
    """Tiles per stella for given mesh subdivision."""
    n_sites = 2 * n_sub * n_sub + 2
    return 2 * (n_sites // 24)


def log_filename(n_sub, pairing, seed):
    return LOG_DIR / f"nsub{n_sub}_{pairing}_s{seed}.log"


def build_command(n_sub, pairing, seed, threads_per_run=4):
    cmd = [
        str(BINARY),
        "--lattice-size", str(LATTICE_SIZE),
        "--n-sub", str(n_sub),
        "--epochs", str(EPOCHS),
        "--cross-rate", str(CROSS_RATE),
        "--mutation-rate", str(MUTATION_RATE),
        "--census-interval", str(CENSUS_INTERVAL),
        "--check-interval", str(CHECK_INTERVAL),
        "--log-interval", str(LOG_INTERVAL),
        "--seed", str(seed),
        "--threads", str(threads_per_run),
    ]
    if pairing == "global":
        cmd.append("--global")
    return cmd


def run_single(n_sub, pairing, seed, dry_run=False, threads_per_run=4):
    logfile = log_filename(n_sub, pairing, seed)
    cmd = build_command(n_sub, pairing, seed, threads_per_run)

    N = compute_n_tiles(n_sub)
    label = f"n_sub={n_sub} N={N} {pairing} seed={seed}"

    if dry_run:
        print(f"[DRY] {label} (threads={threads_per_run})")
        return label, "DRY_RUN", 0

    print(f"[START] {label} (threads={threads_per_run}) -> {logfile.name}")
    sys.stdout.flush()

    t0 = time.time()
    with open(logfile, "w") as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT)
    elapsed = time.time() - t0

    status = "OK" if proc.returncode == 0 else f"FAIL(rc={proc.returncode})"
    print(f"[DONE]  {label} — {status} in {elapsed:.0f}s ({elapsed/60:.0f}min)")
    sys.stdout.flush()
    return label, status, elapsed


def get_pending_runs(args):
    nsub_list = [args.nsub] if args.nsub else NSUB_VALUES
    seed_list = SEEDS

    runs = []
    for n_sub in nsub_list:
        for pairing in PAIRING_MODES:
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
    """Estimate total wall time based on N scaling."""
    # At N=1666 (n_sub=100), 5M epochs takes ~7500s with 16 threads.
    # Scale linearly with N and inversely with thread ratio.
    ref_N = 1666
    ref_time = 7500  # seconds at 16 threads
    total = 0
    for n_sub, _, _ in runs:
        N = compute_n_tiles(n_sub)
        total += ref_time * (N / ref_N)
    return total


def main():
    parser = argparse.ArgumentParser(
        description="Priority 5: Sigmoid midpoint campaign — determine N₅₀")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--resume", action="store_true",
                        help="Skip runs with existing complete logs")
    parser.add_argument("--parallel", type=int, default=1,
                        help="Number of runs to execute in parallel")
    parser.add_argument("--threads", type=int, default=12,
                        help="Total CPU threads to distribute (default: 12)")
    parser.add_argument("--nsub", type=int, choices=NSUB_VALUES,
                        help="Run only a specific n_sub value")
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
    n_stellae = n_total * 4  # 4 stellae per run (lattice_size=2 FCC)

    # Print N table
    print("=" * 70)
    print("Priority 5: Sigmoid Midpoint Campaign")
    print("=" * 70)
    print()
    print("  N value table:")
    print(f"  {'n_sub':>5}  {'N (tiles/stella)':>16}  {'3⁶=729?':>8}")
    print(f"  {'-----':>5}  {'----------------':>16}  {'--------':>8}")
    for ns in NSUB_VALUES:
        N = compute_n_tiles(ns)
        marker = " ← near 729" if abs(N - 729) < 100 else ""
        print(f"  {ns:>5}  {N:>16}{marker}")
    print()
    print(f"  Seeds:        {len(SEEDS)} ({SEEDS})")
    print(f"  Pairing:      global only")
    print(f"  Epochs:       {EPOCHS/1e6:.0f}M per run")
    print(f"  Runs pending: {n_total}")
    print(f"  Experiments:  {n_stellae} nucleation experiments")
    print(f"  Parallelism:  {args.parallel} runs × {threads_per_run} threads "
          f"= {args.parallel * threads_per_run} total CPU")

    est_serial = estimate_runtime(runs)
    # Adjust for reduced threads: time scales ~inversely with threads (roughly)
    thread_factor = 16.0 / threads_per_run  # ref was 16 threads
    est_serial *= thread_factor
    est_parallel = est_serial / max(1, args.parallel)

    print(f"  Est. runtime: {est_parallel/3600:.0f}h ({est_parallel/86400:.1f} days) "
          f"at {args.parallel}× parallel")
    print(f"  Log dir:      {LOG_DIR}")
    print()
    print("  After completion, run sigmoid analysis with:")
    print("    python3 stella_lang/sigmoid_midpoint_analysis.py")
    print("=" * 70)

    if n_total == 0:
        print("\nAll runs already complete!")
        return

    if args.dry_run:
        print()
        for n_sub, pairing, seed in runs:
            run_single(n_sub, pairing, seed, dry_run=True,
                       threads_per_run=threads_per_run)
        print(f"\n  Total: {n_total} runs, {n_stellae} experiments")
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
    print("SIGMOID MIDPOINT CAMPAIGN COMPLETE")
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
    print(f"  python3 stella_lang/sigmoid_midpoint_analysis.py")


if __name__ == "__main__":
    main()
