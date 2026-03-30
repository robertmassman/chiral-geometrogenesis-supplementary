#!/usr/bin/env python3
"""
Phase B: Z₃ Color Crystallization — C Implementation Runner

Compiles and runs the C version of Phase B, then parses the JSON output
and displays results in the same format as the Python version.

Usage:
  python3 run_phase_b_c.py [--quick]
"""

import subprocess
import json
import os
import sys
import numpy as np

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
C_SOURCE = os.path.join(SCRIPT_DIR, "phase_b.c")
C_BINARY = os.path.join(SCRIPT_DIR, "phase_b")


def compile_c():
    """Compile the C source."""
    cmd = ["cc", "-O3", "-o", C_BINARY, C_SOURCE, "-lm"]
    print(f"Compiling: {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"Compilation failed:\n{result.stderr}")
        sys.exit(1)
    print("Compilation successful.\n")


def run_c(quick=False):
    """Run the C binary and capture JSON output."""
    cmd = [C_BINARY]
    if quick:
        cmd.append("--quick")

    print(f"Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)

    # Print stderr (progress info)
    if result.stderr:
        print(result.stderr)

    if result.returncode != 0:
        print(f"Execution failed (exit code {result.returncode})")
        sys.exit(1)

    return json.loads(result.stdout)


def print_b1_results(b1_data):
    """Print ratio sweep results as markdown table."""
    print("\n## B1: α/β Ratio Sweep Results")
    print()
    print("| α/β | tet_quality | stella_RMSD | cross_d_ratio | "
          "stella_ratio_err | intra_std |")
    print("|:---:|:----------:|:-----------:|:-------------:|"
          ":----------------:|:---------:|")

    stella_ref = np.sqrt(3.0)

    for r in b1_data:
        ratio = r['ratio']
        tet = r['avg_tet_quality']
        rmsd = r['avg_stella_rmsd']
        d_ratio = r['avg_cross_d_ratio']
        ratio_err = r['avg_stella_ratio_err']
        intra = r['avg_intra_std']

        print(f"| {ratio:5.1f} | {tet:.4f} | "
              f"{rmsd:.4f} | {d_ratio:.3f} | "
              f"{ratio_err:.4f} | {intra:.4f} |")

    # Find transition point
    for r in b1_data:
        if r['avg_stella_rmsd'] < 0.05:
            print(f"\n**Stella crystallization threshold: α/β ≈ {r['ratio']:.1f}**")
            print(f"  (RMSD drops below 0.05 — configuration is stella)")
            break
    else:
        best = min(b1_data, key=lambda r: r['avg_stella_rmsd'])
        print(f"\n**Best RMSD = {best['avg_stella_rmsd']:.4f} at α/β = {best['ratio']:.1f}**")

    print(f"\nStella reference: cross_d_ratio = √3 ≈ 1.732, "
          f"tet_quality = 1.000, RMSD = 0.000")
    print(f"Thomson (α/β=1): expected square antiprism (RMSD >> 0)")


def print_b2_results(b2_data, b2_summary):
    """Print seed robustness results."""
    print(f"\n## B2: Seed Robustness (α/β = 10.0, {b2_summary['n_seeds']} seeds)")
    print()

    rmsds = [r['stella_rmsd'] for r in b2_data]
    tet_qs = [r['tet_quality_avg'] for r in b2_data]
    d_ratios = [r['cross_d_ratio'] for r in b2_data]

    print(f"  Stella RMSD:    {np.mean(rmsds):.4f} ± {np.std(rmsds):.4f}  "
          f"(min={np.min(rmsds):.4f}, max={np.max(rmsds):.4f})")
    print(f"  Tet quality:    {np.mean(tet_qs):.4f} ± {np.std(tet_qs):.4f}")
    print(f"  Cross d ratio:  {np.mean(d_ratios):.3f} ± {np.std(d_ratios):.3f}  "
          f"(stella = 1.732)")

    converged = b2_summary['converged']
    total = b2_summary['n_seeds']
    print(f"  Converged to stella (RMSD < 0.05): {converged}/{total} "
          f"({100*converged/total:.0f}%)")


def print_analysis(b1_data, b2_summary):
    """Print analysis section."""
    print("\n## Analysis")

    thomson = b1_data[0]  # α/β = 1
    best = min(b1_data, key=lambda r: r['avg_stella_rmsd'])

    print(f"\n### Thomson (α/β=1) vs Best Stella")
    print(f"  Thomson:  tet_quality={thomson['avg_tet_quality']:.4f}, "
          f"RMSD={thomson['avg_stella_rmsd']:.4f}")
    print(f"  Best:     tet_quality={best['avg_tet_quality']:.4f}, "
          f"RMSD={best['avg_stella_rmsd']:.4f}  (α/β={best['ratio']:.1f})")

    print(f"\n### Key Findings")
    print()

    # Check for transition
    for r in b1_data:
        if r['avg_stella_rmsd'] < 0.05:
            print(f"1. **Stella crystallization occurs at α/β ≥ {r['ratio']:.1f}.**")
            print(f"   When same-component repulsion is {r['ratio']:.0f}× stronger than")
            print(f"   cross-component, the 8 points spontaneously form the stella.")
            break
    else:
        print(f"1. **Best RMSD = {best['avg_stella_rmsd']:.4f} at α/β = {best['ratio']:.1f}.**")

    # Tetrahedral quality
    high_tet = [r for r in b1_data if r['avg_tet_quality'] > 0.99]
    if high_tet:
        print(f"\n2. **Perfect tetrahedra form at α/β ≥ {high_tet[0]['ratio']:.1f}.**")
        print(f"   Tetrahedral quality > 0.99 (all intra-group distances equal).")
    else:
        best_tet = max(b1_data, key=lambda r: r['avg_tet_quality'])
        print(f"\n2. **Best tetrahedral quality: {best_tet['avg_tet_quality']:.4f} "
              f"at α/β = {best_tet['ratio']:.1f}.**")

    # Cross-distance ratio
    stella_ratio = np.sqrt(3)
    close_ratio = [r for r in b1_data
                   if abs(r['avg_cross_d_ratio'] - stella_ratio) / stella_ratio < 0.05]
    if close_ratio:
        print(f"\n3. **Cross-distance ratio matches stella (√3 ≈ 1.732) at "
              f"α/β ≥ {close_ratio[0]['ratio']:.1f}.**")
        print(f"   The characteristic 12-near / 4-far distance pattern emerges.")

    # Seed robustness
    converged = b2_summary['converged']
    total = b2_summary['n_seeds']
    print(f"\n4. **Seed robustness: {converged}/{total} seeds converge "
          f"to stella ({100*converged/total:.0f}%).**")
    if converged < total:
        print(f"   Some seeds find local minima (other polyhedra).")


def save_results(data):
    """Save results to JSON."""
    path = os.path.join(SCRIPT_DIR, "phase_b_results.json")

    # Restructure to match the Python version's format
    output = {
        "experiment": "Phase B: Z₃ Color Crystallization (C implementation)",
    }

    if 'b1' in data:
        sweep = []
        for r in data['b1']:
            entry = {
                'ratio': r['ratio'],
                'tet_quality': r['avg_tet_quality'],
                'stella_rmsd': r['avg_stella_rmsd'],
                'cross_d_ratio': r['avg_cross_d_ratio'],
                'stella_ratio_err': r['avg_stella_ratio_err'],
                'intra_std': r['avg_intra_std'],
                'seeds': r['seeds'],
            }
            sweep.append(entry)
        output['sweep'] = sweep

    if 'b2' in data:
        output['seed_study'] = data['b2']

    if 'b2_summary' in data:
        output['seed_study_summary'] = data['b2_summary']

    with open(path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {path}")


def main():
    quick = "--quick" in sys.argv

    compile_c()
    data = run_c(quick)

    print(f"\n{'=' * 70}")
    print("RESULTS")
    print(f"{'=' * 70}")

    if 'b1' in data:
        print_b1_results(data['b1'])

    if 'b2' in data and 'b2_summary' in data:
        print_b2_results(data['b2'], data['b2_summary'])

    if 'b1' in data and 'b2_summary' in data:
        print_analysis(data['b1'], data['b2_summary'])

    save_results(data)


if __name__ == "__main__":
    main()
