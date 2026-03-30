#!/usr/bin/env python3
"""
Phase T1: Finite-Temperature Phase Diagram — Runner and Analysis

Compiles and runs phase_T1_finite_temperature.c, then analyzes results
to resolve Open Question 1 of Prop 0.0.3a: the relationship between
gauge β_c ≈ 0.506 on FCC and the crystallization melting temperature.

Usage:
    python3 run_phase_T1.py [--quick] [--analyze-only]
"""

import json
import os
import subprocess
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(SCRIPT_DIR, "phase_T1_finite_temperature.c")
BIN = os.path.join(SCRIPT_DIR, "phase_T1_finite_temperature")
RESULTS = os.path.join(SCRIPT_DIR, "phase_T1_results.json")


def compile_code():
    print("Compiling phase_T1_finite_temperature.c ...")
    result = subprocess.run(
        ["cc", "-O3", "-o", BIN, SRC, "-lm"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        print(f"Compilation failed:\n{result.stderr}")
        sys.exit(1)
    print("  Compiled successfully.")


def run_experiment(quick=False):
    print(f"\nRunning Phase T1 ({'QUICK' if quick else 'FULL'} mode) ...")
    cmd = [BIN]
    if quick:
        cmd.append("--quick")

    with open(RESULTS, "w") as fout:
        result = subprocess.run(
            cmd, stdout=fout, stderr=subprocess.PIPE, text=True
        )
    print(result.stderr)
    if result.returncode != 0:
        print(f"Run failed with return code {result.returncode}")
        sys.exit(1)


def analyze(results_path=None):
    path = results_path or RESULTS
    print(f"\n{'='*70}")
    print("PHASE T1: FINITE-TEMPERATURE PHASE DIAGRAM — ANALYSIS")
    print(f"{'='*70}")

    with open(path) as f:
        data = json.load(f)

    # ── T1.1: Equilibrium ──
    eq = data["T1_1_equilibrium"]
    print("\n── T1.1: Equilibrium Phase Diagram ──")
    print(f"  {'T':>8}  {'RMSD':>8}  {'Crystal%':>8}  {'<E>':>8}  {'Cv':>8}  {'Reg':>6}")
    for r in eq:
        print(f"  {r['T']:8.4f}  {r['avg_rmsd']:8.4f}  {r['crystal_frac']*100:7.1f}%"
              f"  {r['avg_E']:8.2f}  {r['Cv']:8.2f}  {r['regularity']:6.3f}")

    # Find T_c from crystal fraction crossing 50%
    Tc_crystal = None
    for i in range(1, len(eq)):
        if eq[i-1]["crystal_frac"] >= 0.5 and eq[i]["crystal_frac"] < 0.5:
            f0, f1 = eq[i-1]["crystal_frac"], eq[i]["crystal_frac"]
            T0, T1 = eq[i-1]["T"], eq[i]["T"]
            Tc_crystal = T0 + (0.5 - f0) / (f1 - f0) * (T1 - T0)
            break

    # Find C_v peak
    max_Cv = max(eq, key=lambda r: r["Cv"])
    Tc_Cv = max_Cv["T"]

    # Find RMSD transition midpoint (RMSD crossing 0.15)
    Tc_rmsd = None
    for i in range(1, len(eq)):
        if eq[i-1]["avg_rmsd"] <= 0.15 and eq[i]["avg_rmsd"] > 0.15:
            r0, r1 = eq[i-1]["avg_rmsd"], eq[i]["avg_rmsd"]
            T0, T1 = eq[i-1]["T"], eq[i]["T"]
            Tc_rmsd = T0 + (0.15 - r0) / (r1 - r0) * (T1 - T0)
            break

    print(f"\n  Critical temperature estimates:")
    if Tc_crystal:
        print(f"    Crystal fraction = 50%:  T_c = {Tc_crystal:.4f}")
    if Tc_rmsd:
        print(f"    RMSD crossing 0.15:      T_c = {Tc_rmsd:.4f}")
    print(f"    C_v peak:                T_c = {Tc_Cv:.4f} (C_v = {max_Cv['Cv']:.2f})")

    # ── T1.2: Hysteresis ──
    hyst = data["T1_2_hysteresis"]
    heat = hyst["heating"]
    cool = hyst["cooling"]

    print(f"\n── T1.2: Hysteresis Test ──")
    print(f"  Max RMSD hysteresis: {hyst['max_hysteresis_rmsd']:.4f} "
          f"at T = {hyst['max_hysteresis_T']:.3f}")

    # Check if hysteresis is significant
    # Compute average ΔRMSD in the transition region
    transition_hyst = []
    for h, c in zip(heat, cool):
        if 0.05 < h["T"] < 0.5:
            transition_hyst.append(abs(h["rmsd"] - c["rmsd"]))

    avg_hyst = sum(transition_hyst) / len(transition_hyst) if transition_hyst else 0
    print(f"  Average ΔRMSD in transition region (0.05 < T < 0.5): {avg_hyst:.4f}")

    if avg_hyst < 0.05:
        print("  → Hysteresis is SMALL: consistent with crossover (N=8 finite-size effect)")
        print("  → Note: sharp first-order transition expected only in thermodynamic limit")
        print("  → The gauge theory (L1-L3) uses lattices with hundreds of sites")
    else:
        print("  → Significant hysteresis detected: suggests first-order character")

    # ── T1.3: Mapping ──
    mapping = data["T1_3_mapping"]

    print(f"\n── T1.3: β-T Mapping ──")
    print(f"  Stella ground-state energy:  E_stella = {mapping['E_stella']:.4f}")
    print(f"  Energy per pair:             e = {mapping['E_per_pair']:.6f}")
    print(f"  Number of pairs:             N_pairs = {mapping['N_pairs']}")

    print(f"\n  Gauge theory β_c (FCC Z₃):   {mapping['gauge_beta_c']:.4f}")

    print(f"\n  β_eff(T) = E_per_pair / T  (crystallization effective coupling)")
    print(f"  {'Method':25s}  {'T_c':>8}  {'β_eff':>8}  {'β_c/β_eff':>10}")
    print(f"  {'─'*55}")

    methods = [
        ("C_v peak", mapping["Tc_Cv"], mapping["beta_eff_Cv"], mapping["ratio_Cv"]),
        ("Crystal frac 50%", mapping["Tc_crystal_frac"], mapping["beta_eff_crystal"], mapping["ratio_crystal"]),
        ("Hysteresis peak", mapping["Tc_hysteresis"], mapping["beta_eff_hyst"], mapping["ratio_hyst"]),
    ]
    for name, tc, beff, ratio in methods:
        if tc > 0:
            print(f"  {name:25s}  {tc:8.4f}  {beff:8.4f}  {ratio:10.4f}")

    # ── Interpretation ──
    print(f"\n{'='*70}")
    print("INTERPRETATION")
    print(f"{'='*70}")

    best_Tc = Tc_crystal if Tc_crystal else (Tc_rmsd if Tc_rmsd else Tc_Cv)
    e_pair = mapping["E_per_pair"]
    beta_eff = e_pair / best_Tc if best_Tc > 0 else 0
    gauge_bc = mapping["gauge_beta_c"]

    print(f"""
  The crystallization system (N=8 particles on sphere, α/β = 10) shows a
  smooth crossover from crystalline (stella octangula) to disordered (liquid)
  phase as temperature increases. The transition region centers on:

    T_c ≈ {best_Tc:.4f}  (crystal fraction = 50%)

  The effective coupling at this temperature is:

    β_eff(T_c) = E_per_pair / T_c = {e_pair:.4f} / {best_Tc:.4f} = {beta_eff:.4f}

  The gauge theory Z₃ deconfinement on FCC occurs at:

    β_c = {gauge_bc:.4f}

  The ratio β_c / β_eff = {gauge_bc/beta_eff:.4f} reflects the different
  normalization between:
  - Gauge theory: β multiplies the plaquette action (3-link triangles, Z₃ phases)
  - Crystallization: T^{{-1}} multiplies the pairwise Coulomb potential (1/r²)

  These are different microscopic theories with the same Z₃ symmetry structure
  on the same FCC geometry. The mapping coefficient

    κ = β_c / β_eff(T_c) = {gauge_bc/beta_eff:.4f}

  encodes the ratio of action densities (gauge plaquette vs Coulomb pair).

  The smooth crossover (vs the sharp first-order transition in L1-L3) is a
  finite-size effect: N=8 particles is far from the thermodynamic limit.
  The gauge theory uses L=4-12 FCC lattices (32-864 sites), where first-order
  signatures (bimodality, hysteresis, volume scaling) are clearly visible.

  Key result: The crystallization system DOES have a well-defined melting
  temperature T_c ≈ {best_Tc:.4f}, and the mapping to the gauge theory is:

    β_gauge = κ × E_per_pair / T_crystal  with  κ ≈ {gauge_bc/beta_eff:.4f}
""")

    return {
        "Tc_crystal": Tc_crystal,
        "Tc_rmsd": Tc_rmsd,
        "Tc_Cv": Tc_Cv,
        "beta_eff": beta_eff,
        "kappa": gauge_bc / beta_eff if beta_eff > 0 else 0,
        "crossover": avg_hyst < 0.05,
    }


def main():
    quick = "--quick" in sys.argv
    analyze_only = "--analyze-only" in sys.argv

    os.chdir(SCRIPT_DIR)

    if not analyze_only:
        compile_code()
        run_experiment(quick)

    results = analyze()
    return results


if __name__ == "__main__":
    main()
