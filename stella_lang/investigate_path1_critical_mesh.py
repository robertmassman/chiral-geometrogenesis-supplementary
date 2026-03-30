#!/usr/bin/env python3
"""
Investigation Path 1: Critical Mesh Resolution
================================================

Can the minimum n_sub* for replicator emergence encode a dimensionless
number that constrains R_stella?

Known data (from RERUN_PLAN 2026-03-11):
  n_sub=16  (N=42 tiles):   No replicators (either mode)
  n_sub=32  (N=170 tiles):  No replicators (either mode)
  n_sub=100 (N=1666 tiles): Replicators (global), stochastic (local ~50%)
  n_sub=120 (N=2400 tiles): Reliable replicators (local)

This script:
  1. Scans n_sub = 40, 50, 60, 70, 80, 90 with global pairing to find
     the critical threshold n_sub* (global) more precisely
  2. For each, runs multiple seeds to estimate nucleation probability
  3. Computes N* = 2 * floor((2*n_sub*^2 + 2) / 24) at the transition
  4. Compares N* and related ratios against known dimensionless constants:
     - b_0 = 9/(4π) ≈ 0.716 (1-loop QCD beta function coefficient)
     - exp(128π/9) ≈ 1.53e19 (R_stella/l_P ratio from Prop 0.0.17q)
     - α_s(√σ) ≈ 1/64 (coupling at confinement scale)
     - 3^L = 3^24 = 2.82e11 (total program space)
     - Various geometric ratios from the stella octangula

Usage:
  python3 stella_lang/investigate_path1_critical_mesh.py
  python3 stella_lang/investigate_path1_critical_mesh.py --scan   # Run new simulations
  python3 stella_lang/investigate_path1_critical_mesh.py --analyze # Analyze only
"""

import argparse
import json
import math
import os
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
BINARY = REPO_ROOT / "verification" / "stella_lang" / "soup_2d_tile"
LOG_DIR = REPO_ROOT / "verification" / "stella_lang" / "path1_critical_mesh_logs"

# Scan parameters
SCAN_NSUB_VALUES = [40, 50, 55, 60, 65, 70, 75, 80, 85, 90]
SEEDS = [42, 123, 456, 789, 1024]
EPOCHS = 5_000_000
PAIRING = "global"  # global is faster to nucleate, gives cleaner threshold

# Known results from RERUN_PLAN
KNOWN_RESULTS = {
    16:  {"N": 42,   "global": {"nucleation_prob": 0.0}},
    32:  {"N": 170,  "global": {"nucleation_prob": 0.0}},
    100: {"N": 1666, "global": {"nucleation_prob": 1.0},
                     "local":  {"nucleation_prob": 0.5}},
    120: {"N": 2400, "local":  {"nucleation_prob": 1.0}},
    140: {"N": 3266, "local":  {"nucleation_prob": 1.0}},
    157: {"N": 4108, "local":  {"nucleation_prob": 1.0}},
}

# Physical constants for comparison
PHYSICAL_CONSTANTS = {
    "b_0 (1-loop QCD beta)": 9 / (4 * math.pi),
    "N_c (colors)": 3,
    "N_f (light flavors)": 3,
    "11/3 * N_c": 11 / 3 * 3,
    "2/3 * N_f": 2 / 3 * 3,
    "beta_0 = 11 - 2N_f/3": 11 - 2 * 3 / 3,
    "4π/beta_0": 4 * math.pi / (11 - 2),
    "128π/9": 128 * math.pi / 9,
    "exp(128π/9)": math.exp(128 * math.pi / 9),
    "Z3 modulus": 3,
    "stella vertices": 8,
    "stella edges": 12,
    "stella faces": 8,
    "stella χ": 4,
    "3^12 (half program space)": 3**12,
    "3^24 (full program space)": 3**24,
    "program_size": 24,
    "instruction_pairs": 12,
    "opcodes": 9,
    "log2(3^24)": 24 * math.log2(3),
    "log2(9^12)": 12 * math.log2(9),
}


def compute_n_tiles(n_sub):
    """N = 2 * floor((2*n_sub^2 + 2) / 24)"""
    n_sites = 2 * n_sub * n_sub + 2
    return 2 * (n_sites // 24)


def compute_n_sites(n_sub):
    """Total sites on one tetrahedron surface."""
    return 2 * n_sub * n_sub + 2


def parse_log_for_replicators(log_path):
    """Parse a soup_2d_tile log file for replicator emergence."""
    if not os.path.exists(log_path):
        return None

    with open(log_path, 'r') as f:
        text = f.read()

    # Look for replicator count in census lines
    # Format varies; look for "replicators" or dominant program percentage
    has_replicators = False
    first_epoch = None
    final_dominant_pct = 0.0

    # Search for patterns like "epoch NNNN ... replicators: N" or dominant %
    for line in text.split('\n'):
        # Look for "REPLICATORS" or significant dominant percentage
        if 'REPLICATOR' in line.upper() or 'replicat' in line.lower():
            has_replicators = True
            m = re.search(r'epoch\s+(\d+)', line, re.IGNORECASE)
            if m and first_epoch is None:
                first_epoch = int(m.group(1))

        # Look for dominant program percentage > 5%
        m = re.search(r'(\d+\.?\d*)%', line)
        if m:
            pct = float(m.group(1))
            if pct > 5.0:
                has_replicators = True
                final_dominant_pct = max(final_dominant_pct, pct)
                if first_epoch is None:
                    m2 = re.search(r'epoch\s+(\d+)', line, re.IGNORECASE)
                    if m2:
                        first_epoch = int(m2.group(1))

    return {
        "has_replicators": has_replicators,
        "first_epoch": first_epoch,
        "final_dominant_pct": final_dominant_pct,
    }


def run_scan():
    """Run simulations at each n_sub value with multiple seeds."""
    LOG_DIR.mkdir(parents=True, exist_ok=True)

    results = {}

    for n_sub in SCAN_NSUB_VALUES:
        n_tiles = compute_n_tiles(n_sub)
        print(f"\n{'='*60}")
        print(f"n_sub={n_sub}, N={n_tiles} tiles")
        print(f"{'='*60}")

        seed_results = []
        for seed in SEEDS:
            log_file = LOG_DIR / f"nsub{n_sub}_global_s{seed}.log"

            if log_file.exists():
                print(f"  Seed {seed}: log exists, parsing...")
                result = parse_log_for_replicators(str(log_file))
                if result:
                    seed_results.append(result)
                    status = "REPLICATORS" if result["has_replicators"] else "none"
                    print(f"    -> {status}")
                continue

            if not BINARY.exists():
                print(f"  Seed {seed}: binary not found, skipping")
                continue

            print(f"  Seed {seed}: running... (this may take several minutes)")
            cmd = [
                str(BINARY),
                "--n-sub", str(n_sub),
                "--epochs", str(EPOCHS),
                "--seed", str(seed),
                "--global",  # global pairing
            ]

            try:
                with open(log_file, 'w') as log_f:
                    proc = subprocess.run(
                        cmd, stdout=log_f, stderr=subprocess.STDOUT,
                        timeout=3600,  # 1 hour timeout per run
                        cwd=str(BINARY.parent),
                    )
                result = parse_log_for_replicators(str(log_file))
                if result:
                    seed_results.append(result)
                    status = "REPLICATORS" if result["has_replicators"] else "none"
                    print(f"    -> {status} (exit code {proc.returncode})")
            except subprocess.TimeoutExpired:
                print(f"    -> TIMEOUT (1h)")
            except Exception as e:
                print(f"    -> ERROR: {e}")

        if seed_results:
            n_emerged = sum(1 for r in seed_results if r["has_replicators"])
            n_total = len(seed_results)
            nuc_prob = n_emerged / n_total
            results[n_sub] = {
                "N": n_tiles,
                "n_seeds_run": n_total,
                "n_emerged": n_emerged,
                "nucleation_prob": nuc_prob,
                "seed_results": seed_results,
            }
            print(f"  => Nucleation probability: {n_emerged}/{n_total} = {nuc_prob:.1%}")

    return results


def analyze(scan_results=None):
    """Analyze results to find critical threshold and compare to physical constants."""

    print("\n" + "="*70)
    print("PATH 1 ANALYSIS: Critical Mesh Resolution")
    print("="*70)

    # Combine known results with scan results
    all_data = []

    # Add known results
    for n_sub, data in sorted(KNOWN_RESULTS.items()):
        N = compute_n_tiles(n_sub)
        nuc_prob = data.get("global", {}).get("nucleation_prob")
        if nuc_prob is not None:
            all_data.append({
                "n_sub": n_sub, "N": N, "nucleation_prob": nuc_prob,
                "source": "known"
            })

    # Add scan results
    if scan_results:
        for n_sub, data in sorted(scan_results.items()):
            all_data.append({
                "n_sub": n_sub, "N": data["N"],
                "nucleation_prob": data["nucleation_prob"],
                "source": "scan"
            })

    # Also parse any existing log files
    if LOG_DIR.exists():
        for log_file in sorted(LOG_DIR.glob("*.log")):
            m = re.match(r"nsub(\d+)_global_s(\d+)\.log", log_file.name)
            if m:
                n_sub_val = int(m.group(1))
                # Skip if already in scan_results
                if scan_results and n_sub_val in scan_results:
                    continue
                result = parse_log_for_replicators(str(log_file))
                if result:
                    # Collect by n_sub
                    existing = [d for d in all_data if d["n_sub"] == n_sub_val and d["source"] == "parsed"]
                    if not existing:
                        all_data.append({
                            "n_sub": n_sub_val,
                            "N": compute_n_tiles(n_sub_val),
                            "nucleation_prob": 1.0 if result["has_replicators"] else 0.0,
                            "source": "parsed",
                        })

    # Sort by n_sub
    all_data.sort(key=lambda d: d["n_sub"])

    # Print transition table
    print("\n## Nucleation Probability vs System Size (global pairing)")
    print(f"{'n_sub':>6} {'N_tiles':>8} {'n_sites':>8} {'P_nuc':>8} {'Source':>8}")
    print("-" * 45)
    for d in all_data:
        n_sites = compute_n_sites(d["n_sub"])
        print(f"{d['n_sub']:>6} {d['N']:>8} {n_sites:>8} {d['nucleation_prob']:>8.2f} {d['source']:>8}")

    # Identify critical threshold
    # Find the transition region where P_nuc goes from 0 to >0
    transition_low = None
    transition_high = None
    for i in range(len(all_data) - 1):
        if all_data[i]["nucleation_prob"] == 0 and all_data[i+1]["nucleation_prob"] > 0:
            transition_low = all_data[i]
            transition_high = all_data[i+1]
            break

    if transition_low and transition_high:
        print(f"\n## Critical Threshold (global pairing)")
        print(f"  Below threshold: n_sub={transition_low['n_sub']} "
              f"(N={transition_low['N']} tiles)")
        print(f"  Above threshold: n_sub={transition_high['n_sub']} "
              f"(N={transition_high['N']} tiles)")

        # Midpoint estimate
        n_sub_crit = (transition_low['n_sub'] + transition_high['n_sub']) / 2
        N_crit = compute_n_tiles(int(n_sub_crit))
        n_sites_crit = compute_n_sites(int(n_sub_crit))
        print(f"  Midpoint estimate: n_sub* ≈ {n_sub_crit:.0f} (N* ≈ {N_crit})")
    else:
        print("\n  Could not identify clean transition (need more data points)")
        # Use the first point with replicators as upper bound
        first_success = next((d for d in all_data if d["nucleation_prob"] > 0), None)
        if first_success:
            n_sub_crit = first_success["n_sub"]
            N_crit = first_success["N"]
            n_sites_crit = compute_n_sites(n_sub_crit)
            print(f"  Upper bound: n_sub* ≤ {n_sub_crit} (N* ≤ {N_crit})")
        else:
            n_sub_crit = 100
            N_crit = 1666
            n_sites_crit = 20002

    # Dimensionless ratios from N*
    print(f"\n## Dimensionless Ratios from Critical Threshold")
    print(f"  N* = {N_crit} tiles")
    print(f"  n_sub* ≈ {n_sub_crit}")
    print(f"  n_sites* = {n_sites_crit}")
    print()

    ratios_to_check = {
        # Ratios involving N*
        "N* / program_size (24)": N_crit / 24,
        "N* / opcodes (9)": N_crit / 9,
        "N* / stella_vertices (8)": N_crit / 8,
        "N* / stella_faces (8)": N_crit / 8,
        "N* / stella_edges (12)": N_crit / 12,
        "N* / stella_χ (4)": N_crit / 4,
        "log_3(N*)": math.log(N_crit) / math.log(3),
        "log_2(N*)": math.log2(N_crit),
        "N* × program_size / 3^12": N_crit * 24 / 3**12,
        "n_sub* / program_size": n_sub_crit / 24,
        "n_sub*^2 / 3^L (L=24)": n_sub_crit**2 / 3**24,
        "sqrt(N*)": math.sqrt(N_crit),
        "N* / (9 × 24)": N_crit / (9 * 24),
        "N* / (3^5 = 243)": N_crit / 243,
        "N* / (3^6 = 729)": N_crit / 729,
        "N* / (3^7 = 2187)": N_crit / 2187,

        # Ratios with QCD constants
        "N* × b_0": N_crit * 9 / (4 * math.pi),
        "N* / (4π/b_0)": N_crit / (4 * math.pi * 4 * math.pi / 9),
        "N* × α_s(√σ) (≈1/64)": N_crit / 64,
        "log(N*) / (128π/9)": math.log(N_crit) / (128 * math.pi / 9),
        "N* / (128π/9)^(1/2)": N_crit / math.sqrt(128 * math.pi / 9),

        # Information-theoretic
        "N* × log_2(3) / log_2(3^24)": N_crit * math.log2(3) / (24 * math.log2(3)),
        "N* / 3^(L/2) = N*/3^12": N_crit / 3**12,
        "log_3(N*) / L": math.log(N_crit) / math.log(3) / 24,
    }

    print(f"  {'Ratio':50s} {'Value':>12s}")
    print(f"  {'-'*50} {'-'*12}")

    interesting = []
    for name, value in sorted(ratios_to_check.items(), key=lambda x: abs(x[1])):
        print(f"  {name:50s} {value:>12.4f}")

        # Flag ratios close to simple numbers or known constants
        for const_name, const_val in PHYSICAL_CONSTANTS.items():
            if const_val > 0 and abs(value - const_val) / const_val < 0.05:
                interesting.append((name, value, const_name, const_val))
            if const_val > 0 and abs(value / const_val - round(value / const_val)) < 0.05:
                ratio = round(value / const_val)
                if 1 < ratio < 20:
                    interesting.append((name, value, f"{ratio}×{const_name}", const_val * ratio))

    if interesting:
        print(f"\n## Potentially Interesting Coincidences")
        for ratio_name, ratio_val, const_name, const_val in interesting:
            rel_err = abs(ratio_val - const_val) / const_val * 100
            print(f"  {ratio_name} = {ratio_val:.4f} ≈ {const_name} = {const_val:.4f} "
                  f"({rel_err:.1f}% off)")

    # Summary
    print(f"\n## Summary")
    print(f"  Critical threshold: n_sub* ≈ {n_sub_crit:.0f}")
    print(f"  Critical tile count: N* ≈ {N_crit}")
    print(f"  Critical site count: n_sites* ≈ {n_sites_crit}")
    print(f"  Program space: 3^24 = {3**24:,}")
    print(f"  N*/3^24 = {N_crit / 3**24:.2e}")
    print(f"  The ratio N*/total_program_space is extremely small,")
    print(f"  suggesting the threshold is NOT about covering program space.")
    print(f"  It likely reflects a geometric/topological constraint on the")
    print(f"  mesh resolution needed for the copy mechanism to function.")

    return {
        "n_sub_crit": n_sub_crit,
        "N_crit": N_crit,
        "n_sites_crit": n_sites_crit,
        "all_data": all_data,
        "ratios": ratios_to_check,
        "interesting_coincidences": [
            {"ratio": n, "value": v, "constant": c, "constant_value": cv}
            for n, v, c, cv in interesting
        ],
    }


def main():
    parser = argparse.ArgumentParser(description="Path 1: Critical mesh resolution investigation")
    parser.add_argument("--scan", action="store_true",
                        help="Run new simulations to fill in the threshold")
    parser.add_argument("--analyze", action="store_true",
                        help="Analyze only (no new simulations)")
    args = parser.parse_args()

    if not args.scan and not args.analyze:
        # Default: analyze with whatever data we have
        args.analyze = True

    scan_results = None
    if args.scan:
        print("Running critical mesh resolution scan...")
        print(f"This will run {len(SCAN_NSUB_VALUES)} × {len(SEEDS)} = "
              f"{len(SCAN_NSUB_VALUES) * len(SEEDS)} simulations")
        print(f"Each run: {EPOCHS:,} epochs, {PAIRING} pairing")
        print(f"Binary: {BINARY}")
        scan_results = run_scan()

    analysis = analyze(scan_results)

    # Save results
    output = {
        "investigation": "Path 1: Critical Mesh Resolution",
        "timestamp": datetime.now().isoformat(),
        "question": "Does N* encode a dimensionless number constraining R_stella?",
        "scan_params": {
            "nsub_values": SCAN_NSUB_VALUES,
            "seeds": SEEDS,
            "epochs": EPOCHS,
            "pairing": PAIRING,
        },
        "analysis": {
            "n_sub_crit": analysis["n_sub_crit"],
            "N_crit": analysis["N_crit"],
            "n_sites_crit": analysis["n_sites_crit"],
            "all_data": analysis["all_data"],
            "interesting_coincidences": analysis["interesting_coincidences"],
        },
    }

    output_path = Path(__file__).parent / "path1_critical_mesh_results.json"
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
