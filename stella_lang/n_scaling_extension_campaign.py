#!/usr/bin/env python3
"""
N-Scaling Extension Campaign: Large-N Transition Probe
======================================================

Tests whether the rate-limited regime (Model C, T ≈ const) found in §3.5.4
transitions to Poisson scaling (T ∝ 1/N) at larger population sizes.

The rigorous bounds (§2.3) predict Poisson scaling for N >> 10^7. This
campaign probes N ∈ {6,666, 13,348, 26,666} to search for the transition.

Architecture:
  - Same as §3.5.3 campaign: soup_multi_stella_wf, lattice-size 2, cross-rate 0
  - 3 N values × 2 pairing modes × 3 seeds × 4 stellae = 72 nucleation experiments
  - Reduced seed set (3 vs 5) to keep runtime manageable

Related Documents:
  - Lemma 0.0.XXe-NP §3.5.5, §7 Refinement 2
  - Base campaign: stella_lang/n_scaling_campaign.py

Usage:
  python3 stella_lang/n_scaling_extension_campaign.py --dry-run
  python3 stella_lang/n_scaling_extension_campaign.py --parallel 4 --threads 16
  python3 stella_lang/n_scaling_extension_campaign.py --resume --parallel 4 --threads 16
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
# N = 2 * floor((2*n_sub^2 + 2) / 24)
NSUB_VALUES = [200, 283, 400]
N_TILES = {200: 6666, 283: 13348, 400: 26666}

SEEDS = [42, 123, 456]
PAIRING_MODES = ["local", "global"]
EPOCHS = 5_000_000

CENSUS_INTERVAL = 100_000
CHECK_INTERVAL = 100_000
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

    runs = []
    for n_sub in nsub_list:
        for pairing in pairing_list:
            for seed in SEEDS:
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


def main():
    parser = argparse.ArgumentParser(
        description="N-scaling extension: large-N transition probe")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--parallel", type=int, default=1)
    parser.add_argument("--threads", type=int, default=16,
                        help="Total CPU threads to distribute (default: 16)")
    parser.add_argument("--nsub", type=int, choices=NSUB_VALUES)
    parser.add_argument("--pairing", choices=PAIRING_MODES)
    args = parser.parse_args()

    threads_per_run = max(1, args.threads // max(1, args.parallel))

    if not BINARY.exists():
        print(f"ERROR: Binary not found: {BINARY}")
        sys.exit(1)

    LOG_DIR.mkdir(parents=True, exist_ok=True)

    runs = get_pending_runs(args)
    n_total = len(runs)
    n_stellae = n_total * (LATTICE_SIZE ** 3 // 2)

    print("=" * 70)
    print("N-Scaling Extension: Large-N Transition Probe")
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
            run_single(n_sub, pairing, seed, dry_run=True,
                       threads_per_run=threads_per_run)
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
    print("EXTENSION CAMPAIGN COMPLETE")
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
