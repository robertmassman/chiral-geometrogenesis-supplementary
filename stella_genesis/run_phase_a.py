#!/usr/bin/env python3
"""
Phase A: Polyhedra Competition — Does the stella octangula maximize Z₃ coherence?

Runs the crystallization experiment across multiple geometries:
1. Rotation sweep: Rz(θ) from 0° to 180° — stella at θ=90°
2. Discrete geometries: separated, nested, random controls

If the stella is the optimal Z₃ substrate, coherence should peak at θ=90°.

Usage: python3 run_phase_a.py [--epochs N] [--quick]
"""

import subprocess
import json
import os
import sys
import math

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
C_SOURCE = os.path.join(SCRIPT_DIR, "crystallization.c")
BINARY = os.path.join(SCRIPT_DIR, "crystallization")

# ── Defaults ──────────────────────────────────────────────────────────

DEFAULT_EPOCHS = 1_000_000
QUICK_EPOCHS = 200_000      # --quick mode for fast iteration
SEED = 42
CS = 0.5
N_SUB = 16
MU = 0.001
EPS = 0.1


def compile_c():
    """Compile crystallization.c"""
    cmd = ["cc", "-O3", "-o", BINARY, C_SOURCE, "-lm"]
    print(f"Compiling: {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"Compilation failed:\n{result.stderr}")
        sys.exit(1)
    print("Compiled successfully.\n")


def run_geometry(epochs, seed, cs, n_sub, mu, eps, param, geometry):
    """Run a single geometry and return parsed JSON results."""
    cmd = [BINARY, str(epochs), str(seed), str(cs), str(n_sub),
           str(mu), str(eps), str(param), geometry]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"ERROR running {geometry} param={param}: {result.stderr}")
        return None
    # Print progress from stderr
    lines = result.stderr.strip().split('\n')
    for line in lines[:3]:  # header only
        print(f"  {line}")
    # Parse JSON from stdout
    try:
        data = json.loads(result.stdout.strip())
    except json.JSONDecodeError:
        print(f"  Failed to parse JSON: {result.stdout[:200]}")
        return None
    return data


def run_sweep(epochs):
    """Run the rotation sweep: θ from 0° to 180° in 5° steps."""
    print("=" * 70)
    print("EXPERIMENT 1: Rotation Sweep (Rz(θ) · T₊)")
    print("  θ=0°: aligned (T₋=T₊), θ=90°: stella, θ=180°: aligned again")
    print("=" * 70)

    angles = list(range(0, 181, 5))
    results = []

    for theta in angles:
        print(f"\n--- θ = {theta}° ---")
        data = run_geometry(epochs, SEED, CS, N_SUB, MU, EPS, theta, "sweep")
        if data:
            results.append(data)
            corr = data['corr']
            couplings = data['couplings_tp_tm'] + data['couplings_tm_tp']
            print(f"  corr={corr:.4f}  couplings={couplings:,}  "
                  f"p_contrast={data['pressure_contrast']:.3f}")

    return results


def run_discrete(epochs):
    """Run discrete geometry comparisons."""
    print("\n" + "=" * 70)
    print("EXPERIMENT 2: Discrete Geometry Comparisons")
    print("=" * 70)

    configs = [
        # (param, geometry, description)
        (0,     "stella",    "Stella octangula (T₋ = -T₊)"),
        (0,     "aligned",   "Aligned (T₋ = T₊, zero contrast)"),
        (1.0,   "separated", "Separated (T₋ shifted z+1.0)"),
        (2.0,   "separated", "Separated (T₋ shifted z+2.0)"),
        (4.0,   "separated", "Separated (T₋ shifted z+4.0)"),
        (0.3,   "nested",    "Nested (T₋ = 0.3·T₊)"),
        (0.5,   "nested",    "Nested (T₋ = 0.5·T₊)"),
        (0.7,   "nested",    "Nested (T₋ = 0.7·T₊)"),
        (1.5,   "nested",    "Nested (T₋ = 1.5·T₊, T₊ inside)"),
        (2.0,   "nested",    "Nested (T₋ = 2.0·T₊, T₊ inside)"),
        (100,   "random",    "Random tetrahedron (seed=100)"),
        (200,   "random",    "Random tetrahedron (seed=200)"),
        (300,   "random",    "Random tetrahedron (seed=300)"),
        (400,   "random",    "Random tetrahedron (seed=400)"),
        (500,   "random",    "Random tetrahedron (seed=500)"),
    ]

    results = []
    for param, geometry, desc in configs:
        print(f"\n--- {desc} ---")
        data = run_geometry(epochs, SEED, CS, N_SUB, MU, EPS, param, geometry)
        if data:
            data['description'] = desc
            results.append(data)
            corr = data['corr']
            couplings = data['couplings_tp_tm'] + data['couplings_tm_tp']
            print(f"  corr={corr:.4f}  couplings={couplings:,}  "
                  f"vertex_sep={data['vertex_sep']:.3f}")

    return results


def print_sweep_table(results):
    """Print the rotation sweep results as a markdown table."""
    print("\n## Rotation Sweep Results")
    print()
    print("| θ (°) | corr | auto_tp | auto_tm | H(T₊) | H(T₋) | "
          "repl | p_contrast | couplings |")
    print("|:-----:|:----:|:-------:|:-------:|:------:|:------:|"
          ":----:|:----------:|:---------:|")

    peak_corr = 0.0
    peak_theta = 0.0
    for r in results:
        theta = r['param']
        total_c = r['couplings_tp_tm'] + r['couplings_tm_tp']
        print(f"| {theta:5.0f} | {r['corr']:.3f} | {r['auto_tp']:.3f} | "
              f"{r['auto_tm']:.3f} | {r['h_tp']:.3f} | {r['h_tm']:.3f} | "
              f"{r['local_repl']:.3f} | {r['pressure_contrast']:.3f} | "
              f"{total_c/1e6:.1f}M |")
        if r['corr'] > peak_corr:
            peak_corr = r['corr']
            peak_theta = theta

    print(f"\n**Peak coherence: corr={peak_corr:.4f} at θ={peak_theta:.0f}°**")
    if abs(peak_theta - 90) < 10:
        print("**→ The stella octangula (θ=90°) is the optimal geometry!**")
    else:
        print(f"**→ Peak at θ={peak_theta:.0f}°, not at stella (90°)**")


def print_discrete_table(results):
    """Print discrete geometry comparison as a markdown table."""
    print("\n## Discrete Geometry Comparison")
    print()
    print("| Geometry | corr | auto_tp | H(T₊) | repl | "
          "vertex_sep | p_contrast | couplings |")
    print("|:---------|:----:|:-------:|:------:|:----:|"
          ":---------:|:----------:|:---------:|")

    for r in results:
        desc = r.get('description', r['geometry'])
        total_c = r['couplings_tp_tm'] + r['couplings_tm_tp']
        couplings_str = f"{total_c/1e6:.1f}M" if total_c > 100000 else f"{total_c:,}"
        print(f"| {desc} | {r['corr']:.3f} | {r['auto_tp']:.3f} | "
              f"{r['h_tp']:.3f} | {r['local_repl']:.3f} | "
              f"{r['vertex_sep']:.3f} | {r['pressure_contrast']:.3f} | "
              f"{couplings_str} |")


def print_analysis(sweep_results, discrete_results):
    """Print analysis section."""
    print("\n## Analysis")
    print()

    # Find stella in discrete results
    stella = next((r for r in discrete_results if r['geometry'] == 'stella'), None)
    aligned = next((r for r in discrete_results if r['geometry'] == 'aligned'), None)

    if stella and aligned:
        print(f"**Stella vs Aligned control:**")
        print(f"  Stella corr = {stella['corr']:.4f}, "
              f"Aligned corr = {aligned['corr']:.4f}")
        print(f"  Δcorr = {stella['corr'] - aligned['corr']:.4f} "
              f"({(stella['corr'] - aligned['corr'])/(aligned['corr'] - 0.333)*100:.0f}% "
              f"above random)")

    # Find best random
    randoms = [r for r in discrete_results if r['geometry'] == 'random']
    if randoms and stella:
        best_rand = max(randoms, key=lambda r: r['corr'])
        print(f"\n**Stella vs best random tetrahedron:**")
        print(f"  Stella corr = {stella['corr']:.4f}, "
              f"Best random corr = {best_rand['corr']:.4f}")
        print(f"  Stella advantage: "
              f"{(stella['corr']-best_rand['corr'])/(best_rand['corr']-0.333)*100:.1f}%")

    # Find best nested
    nesteds = [r for r in discrete_results if r['geometry'] == 'nested']
    if nesteds and stella:
        best_nested = max(nesteds, key=lambda r: r['corr'])
        print(f"\n**Stella vs best nested configuration:**")
        print(f"  Stella corr = {stella['corr']:.4f}, "
              f"Best nested corr = {best_nested['corr']:.4f} "
              f"(scale={best_nested['param']:.1f})")

    # Sweep analysis
    if sweep_results:
        corrs = [(r['param'], r['corr']) for r in sweep_results]
        peak = max(corrs, key=lambda x: x[1])
        print(f"\n**Rotation sweep peak: θ={peak[0]:.0f}°, corr={peak[1]:.4f}**")

        # Check symmetry around 90°
        pairs = {}
        for theta, corr in corrs:
            mirror = 180 - theta
            if mirror != theta:
                pairs.setdefault(min(theta, mirror), []).append(corr)

        max_asym = 0
        for theta, vals in pairs.items():
            if len(vals) == 2:
                asym = abs(vals[0] - vals[1])
                max_asym = max(max_asym, asym)
        print(f"  Max asymmetry in θ ↔ (180-θ) pairs: {max_asym:.4f}")


def save_results(sweep_results, discrete_results):
    """Save all results to JSON."""
    output = {
        "experiment": "Phase A: Polyhedra Competition",
        "parameters": {
            "seed": SEED, "cs": CS, "n_sub": N_SUB,
            "mu": MU, "eps": EPS
        },
        "sweep": sweep_results,
        "discrete": discrete_results
    }
    path = os.path.join(SCRIPT_DIR, "phase_a_results.json")
    with open(path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {path}")


def main():
    quick = "--quick" in sys.argv
    epochs = QUICK_EPOCHS if quick else DEFAULT_EPOCHS

    if quick:
        print(f"*** QUICK MODE: {epochs:,} epochs (use without --quick for full run) ***\n")
    else:
        print(f"Running with {epochs:,} epochs per geometry\n")

    compile_c()

    # Run experiments
    sweep_results = run_sweep(epochs)
    discrete_results = run_discrete(epochs)

    # Print results
    print("\n" + "=" * 70)
    print("RESULTS")
    print("=" * 70)

    print_sweep_table(sweep_results)
    print_discrete_table(discrete_results)
    print_analysis(sweep_results, discrete_results)

    save_results(sweep_results, discrete_results)


if __name__ == "__main__":
    main()
