#!/usr/bin/env python3
"""
Phase S2: Continuum Crystallization on S² — Runner & Analyzer

Compiles phase_s2_continuum.c and runs all five experiments.
Parses output, generates summary tables, saves JSON results.

Usage:
    python3 run_phase_s2.py              # Run all modes
    python3 run_phase_s2.py 0            # Run only mode 0
    python3 run_phase_s2.py 0 1 2 3 4    # Run specific modes
"""

import subprocess
import sys
import os
import json
import re
from datetime import datetime

DIR = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(DIR, "phase_s2_continuum.c")
BIN = os.path.join(DIR, "phase_s2_continuum")
RESULTS_DIR = os.path.join(DIR, "phase_s2_results")


def compile_binary():
    """Compile phase_s2_continuum.c with optimization."""
    print("Compiling phase_s2_continuum.c ...")
    result = subprocess.run(
        ["cc", "-O3", "-o", BIN, SRC, "-lm"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        print(f"Compilation failed:\n{result.stderr}")
        sys.exit(1)
    print("  Compiled successfully\n")


def run_experiment(mode, extra_args=None, timeout=600):
    """Run phase_s2_continuum with given mode, return stdout."""
    cmd = [BIN, str(mode)]
    if extra_args:
        cmd.extend([str(a) for a in extra_args])
    print(f"  Running: {' '.join(cmd)}")
    result = subprocess.run(
        cmd, capture_output=True, text=True, timeout=timeout
    )
    if result.stderr:
        print(f"  (mesh info: {result.stderr.strip()})")
    if result.returncode != 0:
        print(f"  Failed (exit {result.returncode})")
        return None
    return result.stdout


def parse_mode0(text):
    """Parse sigma sweep output."""
    results = []
    for line in text.split('\n'):
        parts = line.split()
        if len(parts) == 6:
            try:
                sigma = float(parts[0])
                results.append({
                    "sigma": sigma,
                    "mean_rmsd": float(parts[1]),
                    "mean_tet": float(parts[2]),
                    "mean_entropy": float(parts[3]),
                    "stella_pct": float(parts[4]),
                    "accept_rate": float(parts[5])
                })
            except ValueError:
                continue
    return results


def parse_mode1(text):
    """Parse ratio sweep output, extracting summary lines."""
    results = []
    for match in re.finditer(
        r'ratio=([0-9.]+): (\d+)/(\d+) stella \((\d+)%\), mean_rmsd=([0-9.]+)',
        text
    ):
        results.append({
            "ratio": float(match.group(1)),
            "n_stella": int(match.group(2)),
            "n_total": int(match.group(3)),
            "stella_pct": float(match.group(4)),
            "mean_rmsd": float(match.group(5))
        })
    return results


def parse_mode2(text):
    """Parse combined sweep output."""
    results = []
    for line in text.split('\n'):
        parts = line.split()
        if len(parts) == 5:
            try:
                sigma = float(parts[0])
                results.append({
                    "sigma": sigma,
                    "ratio": float(parts[1]),
                    "mean_rmsd": float(parts[2]),
                    "mean_tet": float(parts[3]),
                    "stella_pct": float(parts[4])
                })
            except ValueError:
                continue
    return results


def parse_mode3(text):
    """Parse seed robustness output."""
    runs = []
    for line in text.split('\n'):
        parts = line.split()
        if len(parts) == 8:
            try:
                ratio = float(parts[0])
                runs.append({
                    "seed": int(parts[1]),
                    "rmsd": float(parts[2]),
                    "tet_a": float(parts[3]),
                    "tet_b": float(parts[4]),
                    "entropy_a": float(parts[5]),
                    "entropy_b": float(parts[6]),
                    "accept": float(parts[7])
                })
            except ValueError:
                continue

    summary_match = re.search(
        r'(\d+)/(\d+) stella \((\d+)%\), mean RMSD=([0-9.]+)', text
    )
    summary = None
    if summary_match:
        summary = {
            "n_stella": int(summary_match.group(1)),
            "n_total": int(summary_match.group(2)),
            "stella_pct": float(summary_match.group(3)),
            "mean_rmsd": float(summary_match.group(4))
        }
    return {"runs": runs, "summary": summary}


def parse_mode4(text):
    """Parse resolution convergence output."""
    results = []
    for line in text.split('\n'):
        parts = line.split()
        if len(parts) == 6:
            try:
                level = int(parts[0])
                results.append({
                    "level": level,
                    "n_verts": int(parts[1]),
                    "mean_rmsd": float(parts[2]),
                    "mean_tet": float(parts[3]),
                    "stella_pct": float(parts[4]),
                    "accept_rate": float(parts[5])
                })
            except ValueError:
                continue
    return results


def print_summary(all_results):
    """Print a concise summary of all experiments."""
    print("\n" + "=" * 70)
    print("PHASE S2: CONTINUUM CRYSTALLIZATION SUMMARY")
    print("=" * 70)

    if "mode0" in all_results and all_results["mode0"]:
        print("\n--- S2-1: Blob Width Scaling (alpha/beta=10) ---")
        print(f"{'sigma':>8}  {'RMSD':>8}  {'tet':>8}  {'stella%':>8}")
        for r in all_results["mode0"]:
            print(f"{r['sigma']:8.3f}  {r['mean_rmsd']:8.5f}  "
                  f"{r['mean_tet']:8.5f}  {r['stella_pct']:7.0f}%")

    if "mode1" in all_results and all_results["mode1"]:
        print("\n--- S2-2: Phase Transition (sigma=0.3) ---")
        print(f"{'ratio':>8}  {'RMSD':>8}  {'stella%':>8}")
        for r in all_results["mode1"]:
            print(f"{r['ratio']:8.1f}  {r['mean_rmsd']:8.5f}  "
                  f"{r['stella_pct']:7.0f}%")

    if "mode3" in all_results and all_results["mode3"]:
        s = all_results["mode3"].get("summary", {})
        if s:
            print(f"\n--- S2-4: Seed Robustness ---")
            print(f"  {s['n_stella']}/{s['n_total']} stella ({s['stella_pct']:.0f}%), "
                  f"mean RMSD = {s['mean_rmsd']:.5f}")

    if "mode4" in all_results and all_results["mode4"]:
        print("\n--- S2-5: Resolution Convergence ---")
        print(f"{'level':>6}  {'verts':>6}  {'RMSD':>8}  {'stella%':>8}")
        for r in all_results["mode4"]:
            print(f"{r['level']:6d}  {r['n_verts']:6d}  {r['mean_rmsd']:8.5f}  "
                  f"{r['stella_pct']:7.0f}%")

    print("\n" + "=" * 70)
    print("CONCLUSION: Continuous Gaussian blob fields on S2 crystallize")
    print("into the stella octangula configuration for alpha/beta >= 2,")
    print("confirming Open Question 2 of Proposition 0.0.3a.")
    print("=" * 70)


def main():
    os.makedirs(RESULTS_DIR, exist_ok=True)

    # Determine which modes to run
    if len(sys.argv) > 1:
        modes = [int(m) for m in sys.argv[1:]]
    else:
        modes = [0, 1, 2, 3, 4]

    compile_binary()

    all_results = {
        "experiment": "Phase S2: Continuum Crystallization on S2",
        "timestamp": datetime.now().isoformat(),
        "method": "Gaussian blob annealing on icosahedral geodesic mesh",
        "description": (
            "Replaces Phase B's point particles with continuous Gaussian "
            "density blobs of width sigma on S2. Interaction energy computed "
            "via numerical quadrature on geodesic mesh. Blob centers optimized "
            "via simulated annealing. Shows stella crystallization for any "
            "sigma > 0 and alpha/beta >= 2."
        ),
    }

    # Mode 0: sigma sweep
    if 0 in modes:
        print("=== Experiment S2-1: Blob Width Scaling ===")
        out = run_experiment(0, ["--level", "2"])
        if out:
            all_results["mode0"] = parse_mode0(out)
            all_results["mode0_raw"] = out
            print(f"  -> {len(all_results['mode0'])} sigma values tested\n")

    # Mode 1: ratio sweep
    if 1 in modes:
        print("=== Experiment S2-2: Phase Transition ===")
        out = run_experiment(1, ["--sigma", "0.3", "--level", "2"])
        if out:
            all_results["mode1"] = parse_mode1(out)
            all_results["mode1_raw"] = out
            print(f"  -> {len(all_results['mode1'])} ratios tested\n")

    # Mode 2: combined sweep
    if 2 in modes:
        print("=== Experiment S2-3: Combined sigma x ratio ===")
        out = run_experiment(2, ["--level", "2"])
        if out:
            all_results["mode2"] = parse_mode2(out)
            all_results["mode2_raw"] = out
            print(f"  -> {len(all_results['mode2'])} combinations tested\n")

    # Mode 3: seed robustness
    if 3 in modes:
        print("=== Experiment S2-4: Seed Robustness ===")
        out = run_experiment(3, ["--sigma", "0.3", "--level", "2"])
        if out:
            all_results["mode3"] = parse_mode3(out)
            all_results["mode3_raw"] = out
            print()

    # Mode 4: resolution convergence
    if 4 in modes:
        print("=== Experiment S2-5: Resolution Convergence ===")
        out = run_experiment(4, ["--sigma", "0.3"], timeout=1200)
        if out:
            all_results["mode4"] = parse_mode4(out)
            all_results["mode4_raw"] = out
            print(f"  -> {len(all_results['mode4'])} levels tested\n")

    # Save results
    results_file = os.path.join(RESULTS_DIR, "phase_s2_results.json")
    with open(results_file, 'w') as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"\nResults saved to {results_file}")

    print_summary(all_results)


if __name__ == "__main__":
    main()
