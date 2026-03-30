#!/usr/bin/env python3
"""
Investigation Path 3: Transition Dynamics
==========================================

Can the replicator transition probability/dynamics encode α_s at the
confinement scale?

The idea: the transition from random soup to replicator-dominated state
is a non-equilibrium phase transition. The transition probability P(N, T)
as a function of system size N and time T may encode a dimensionless
"coupling constant" analogous to α_s.

From the n_scaling data:
  - T_emerge ∝ N^(-η) with η ≈ 0.49-0.67
  - Nucleation probability varies with N
  - ~75% nucleation at 5M epochs for N=1666

Analysis:
  1. Extract the scaling exponent η from T_emerge(N)
  2. Compute the nucleation rate Γ = 1/T_emerge and its N-dependence
  3. Define a dimensionless "coupling" g² = Γ × N × T_char
  4. Compare g², η, and derived quantities to α_s(√σ) ≈ 1/64

Related:
  - Prop 0.0.17w: α_s(√σ) ≈ 0.0156 ≈ 1/64
  - N-scaling results: n_scaling_results.json

Usage:
  python3 stella_lang/investigate_path3_transition_dynamics.py
"""

import json
import math
from datetime import datetime
from pathlib import Path

import numpy as np

# ============================================================================
# LOAD N-SCALING DATA
# ============================================================================

DATA_PATH = Path(__file__).parent / "n_scaling_results.json"


def load_scaling_data():
    """Load the n_scaling campaign results."""
    with open(DATA_PATH, 'r') as f:
        data = json.load(f)
    return data


def extract_emergence_data(data):
    """Extract T_emerge values organized by (N, pairing)."""
    results = {}

    for entry in data.get("summary", []):
        N = entry["N"]
        pairing = entry["pairing"]
        key = (N, pairing)
        results[key] = {
            "N": N,
            "pairing": pairing,
            "n_total": entry["n_total"],
            "n_emerged": entry["n_emerged"],
            "n_censored": entry["n_censored"],
            "median_T": entry.get("median_T"),
            "mean_T": entry.get("mean_T"),
            "std_T": entry.get("std_T"),
            "min_T": entry.get("min_T"),
            "max_T": entry.get("max_T"),
        }

    return results


# ============================================================================
# SCALING ANALYSIS
# ============================================================================

def fit_power_law(N_values, T_values):
    """Fit T = C × N^(-η) using log-log regression."""
    log_N = np.log(N_values)
    log_T = np.log(T_values)

    # Linear fit: log(T) = log(C) - η × log(N)
    coeffs = np.polyfit(log_N, log_T, 1)
    eta = -coeffs[0]  # negative slope = η
    log_C = coeffs[1]
    C = np.exp(log_C)

    # Residuals
    T_pred = C * N_values**(-eta)
    residuals = (T_values - T_pred) / T_values
    rms_residual = np.sqrt(np.mean(residuals**2))

    return {
        "eta": eta,
        "C": C,
        "rms_residual": rms_residual,
        "log_C": log_C,
    }


def compute_nucleation_rate(emergence_data):
    """Compute nucleation rate Γ = n_emerged / (n_total × T_cutoff)."""
    # For each (N, pairing), compute the nucleation probability and rate
    rates = {}
    T_cutoff = 5_000_000  # 5M epoch cutoff

    for key, data in sorted(emergence_data.items()):
        N, pairing = key
        if data["n_total"] == 0:
            continue

        P_nuc = data["n_emerged"] / data["n_total"]
        # Nucleation rate per stella per epoch
        if data["median_T"] and data["median_T"] > 0:
            Gamma = 1.0 / data["median_T"]
        elif P_nuc > 0:
            # Use censoring correction: -ln(1-P)/T_cutoff
            Gamma = -math.log(1 - min(P_nuc, 0.999)) / T_cutoff
        else:
            Gamma = 0.0

        rates[key] = {
            "N": N,
            "pairing": pairing,
            "P_nuc": P_nuc,
            "Gamma": Gamma,
            "Gamma_N": Gamma * N,  # dimensionless rate × size
            "median_T": data["median_T"],
        }

    return rates


def extract_dimensionless_coupling(rates):
    """
    Define and extract dimensionless couplings from the transition data.

    Several definitions to try:
    1. g² = Γ × N  (nucleation rate × system size)
    2. g² = P_nuc × (N/N_ref)  (probability × relative size)
    3. g² = 1 / (T_emerge × Γ_0) where Γ_0 is the single-site rate
    4. g² = η (the scaling exponent itself)
    """

    # Collect N and T for power law fit
    N_vals_global = []
    T_vals_global = []
    N_vals_local = []
    T_vals_local = []

    for key, data in sorted(rates.items()):
        N, pairing = key
        if data["median_T"] and data["median_T"] > 0 and data["P_nuc"] > 0:
            if pairing == "global":
                N_vals_global.append(data["N"])
                T_vals_global.append(data["median_T"])
            else:
                N_vals_local.append(data["N"])
                T_vals_local.append(data["median_T"])

    results = {}

    # Fit power laws
    if len(N_vals_global) >= 2:
        N_arr = np.array(N_vals_global, dtype=float)
        T_arr = np.array(T_vals_global, dtype=float)
        fit_g = fit_power_law(N_arr, T_arr)
        results["global_fit"] = fit_g

        # The scaling exponent η
        eta_g = fit_g["eta"]
        results["eta_global"] = eta_g

    if len(N_vals_local) >= 2:
        N_arr = np.array(N_vals_local, dtype=float)
        T_arr = np.array(T_vals_local, dtype=float)
        fit_l = fit_power_law(N_arr, T_arr)
        results["local_fit"] = fit_l
        results["eta_local"] = fit_l["eta"]

    return results


# ============================================================================
# PHYSICAL COMPARISONS
# ============================================================================

# QCD coupling at confinement scale
ALPHA_S_CONFINEMENT = 1 / 64  # ≈ 0.0156 from Prop 0.0.17w
ALPHA_S_MZ = 0.1179           # PDG 2024 at M_Z
ALPHA_S_TAU = 0.330           # at m_τ scale

# Beta function coefficients
B_0 = 9 / (4 * math.pi)      # ≈ 0.716
BETA_0 = 9                    # 11N_c - 2N_f for N_c=N_f=3

# Other dimensionless QCD numbers
LAMBDA_QCD_OVER_SQRT_SIGMA = 0.6  # Λ_QCD/√σ ≈ 250/440


def compare_to_physics(analysis):
    """Compare extracted couplings to known QCD parameters."""

    comparisons = []

    # 1. Scaling exponent η
    if "eta_global" in analysis:
        eta = analysis["eta_global"]
        comparisons.append({
            "quantity": "η (global scaling exponent)",
            "value": eta,
            "comparisons": {
                "η vs 1/2": abs(eta - 0.5),
                "η vs 2/3": abs(eta - 2/3),
                "η vs b_0 (0.716)": abs(eta - B_0),
                "η vs 1-1/N_c (2/3)": abs(eta - 2/3),
                "η vs 1-b_0 (0.284)": abs(eta - (1 - B_0)),
                "2η vs 1": abs(2 * eta - 1),
                "1/η": 1 / eta if eta > 0 else None,
            }
        })

    # 2. Nucleation probability at N=1666
    # P_nuc = fraction of stellae that nucleate in 5M epochs
    # From known data: P_nuc(global, N=1666) ≈ 15/20 = 0.75

    P_nuc_1666 = 15 / 20  # from n_scaling_results
    comparisons.append({
        "quantity": "P_nuc(N=1666, 5M epochs)",
        "value": P_nuc_1666,
        "comparisons": {
            "P vs 3/4": abs(P_nuc_1666 - 3/4),
            "P vs e^(-1/4)": abs(P_nuc_1666 - math.exp(-1/4)),
            "1-P vs 1/4": abs(1 - P_nuc_1666 - 1/4),
            "-ln(1-P)": -math.log(1 - P_nuc_1666),
        }
    })

    # 3. Dimensionless product Γ × N at threshold
    # Γ = 1/T_emerge ≈ 1/1.8M epochs for N=1666 global
    T_median = 1_800_000
    Gamma = 1 / T_median
    Gamma_N = Gamma * 1666

    comparisons.append({
        "quantity": "Γ × N (dimensionless nucleation rate)",
        "value": Gamma_N,
        "comparisons": {
            "Γ×N vs 1": abs(Gamma_N - 1),
            "Γ×N vs α_s(√σ) (1/64)": abs(Gamma_N - ALPHA_S_CONFINEMENT),
            "1/Γ×N": 1 / Gamma_N if Gamma_N > 0 else None,
            "Γ×N vs b_0": abs(Gamma_N - B_0),
        }
    })

    # 4. The ratio T_emerge / N
    T_over_N = T_median / 1666
    comparisons.append({
        "quantity": "T_emerge / N",
        "value": T_over_N,
        "comparisons": {
            "T/N vs 3^L/N (max_steps)": T_over_N / 729,
            "T/N vs 1000": abs(T_over_N - 1000) / 1000,
            "log(T/N)": math.log(T_over_N),
        }
    })

    return comparisons


# ============================================================================
# TRANSITION DYNAMICS ANALYSIS
# ============================================================================

def analyze_transition_character(emergence_data):
    """
    Analyze whether the transition is:
    - 1st order (nucleation + growth, bimodal distribution)
    - 2nd order (continuous, power-law fluctuations)
    - Crossover (smooth, no sharp transition)

    The character constrains what kind of physics it could map to.
    """

    # From the data: T_emerge has large variance (std ≈ mean)
    # This suggests stochastic nucleation (1st order-like)
    # But the N-scaling is NOT simple Poisson (T ∝ 1/N)

    analysis = {
        "observations": [],
        "character": None,
        "implications": [],
    }

    # Check variance/mean ratio for each configuration
    for key, data in sorted(emergence_data.items()):
        N, pairing = key
        if data["mean_T"] and data["std_T"] and data["mean_T"] > 0:
            cv = data["std_T"] / data["mean_T"]  # coefficient of variation
            analysis["observations"].append({
                "N": N, "pairing": pairing,
                "mean_T": data["mean_T"],
                "std_T": data["std_T"],
                "CV": cv,
                "censored_fraction": data["n_censored"] / data["n_total"],
            })

    if analysis["observations"]:
        cvs = [obs["CV"] for obs in analysis["observations"]]
        mean_cv = np.mean(cvs)

        if mean_cv > 0.8:
            analysis["character"] = "stochastic_nucleation"
            analysis["implications"].append(
                "CV > 0.8: consistent with rare nucleation event (1st order-like)")
        elif mean_cv < 0.3:
            analysis["character"] = "continuous_transition"
            analysis["implications"].append(
                "CV < 0.3: consistent with continuous (2nd order-like) transition")
        else:
            analysis["character"] = "intermediate"
            analysis["implications"].append(
                f"CV ≈ {mean_cv:.2f}: intermediate between nucleation and continuous")

        analysis["mean_CV"] = mean_cv

    # Physical mapping
    analysis["physics_mapping"] = {
        "if_1st_order": (
            "Maps to QCD confinement/deconfinement transition. "
            "The nucleation rate Γ ∝ exp(-S_bounce/g²) would give "
            "g² from Γ(N) data. However, requires bounce action S_bounce."
        ),
        "if_2nd_order": (
            "Maps to a continuous phase transition with critical exponents. "
            "The scaling exponent η would be a universal quantity related "
            "to the symmetry class of the transition."
        ),
        "if_cooperative": (
            "Maps to cooperative nucleation (intermediate between 1st/2nd order). "
            "The sub-Poisson scaling T ∝ N^(-η) with η < 1 suggests "
            "correlated fluctuations."
        ),
    }

    return analysis


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("="*70)
    print("PATH 3 ANALYSIS: Transition Dynamics")
    print("="*70)

    # Load data
    try:
        data = load_scaling_data()
    except FileNotFoundError:
        print(f"\n  ERROR: {DATA_PATH} not found.")
        print("  Run n_scaling_campaign.py first to generate data.")
        return

    emergence = extract_emergence_data(data)

    # 1. Nucleation rates
    print("\n## 1. Nucleation Rates")
    rates = compute_nucleation_rate(emergence)
    print(f"  {'N':>6} {'Mode':>7} {'P_nuc':>7} {'Γ (per epoch)':>14} {'Γ×N':>10} {'T_med':>10}")
    print(f"  {'-'*6} {'-'*7} {'-'*7} {'-'*14} {'-'*10} {'-'*10}")
    for key, r in sorted(rates.items()):
        T_str = f"{r['median_T']:.0f}" if r['median_T'] else "N/A"
        print(f"  {r['N']:>6} {r['pairing']:>7} {r['P_nuc']:>7.2f} "
              f"{r['Gamma']:>14.2e} {r['Gamma_N']:>10.4f} {T_str:>10}")

    # 2. Power law fits
    print("\n## 2. Scaling Exponents")
    couplings = extract_dimensionless_coupling(rates)
    if "global_fit" in couplings:
        fit = couplings["global_fit"]
        print(f"  Global: T ∝ N^(-{couplings['eta_global']:.3f}), "
              f"C = {fit['C']:.2e}, RMS residual = {fit['rms_residual']:.3f}")
    if "local_fit" in couplings:
        fit = couplings["local_fit"]
        print(f"  Local:  T ∝ N^(-{couplings.get('eta_local', 0):.3f}), "
              f"C = {fit['C']:.2e}, RMS residual = {fit['rms_residual']:.3f}")

    # 3. Physical comparisons
    print("\n## 3. Comparison to QCD Parameters")
    comparisons = compare_to_physics(couplings)
    for comp in comparisons:
        print(f"\n  {comp['quantity']} = {comp['value']:.6f}")
        for name, diff in comp["comparisons"].items():
            if diff is not None:
                if isinstance(diff, float) and diff < 0.1:
                    marker = " ←"
                else:
                    marker = ""
                print(f"    {name}: {diff:.6f}{marker}")

    # 4. Transition character
    print("\n## 4. Transition Character")
    trans = analyze_transition_character(emergence)
    print(f"  Character: {trans['character']}")
    if "mean_CV" in trans:
        print(f"  Mean CV (std/mean): {trans['mean_CV']:.3f}")
    for imp in trans["implications"]:
        print(f"  → {imp}")

    if trans["observations"]:
        print(f"\n  Per-configuration CV:")
        for obs in trans["observations"]:
            print(f"    N={obs['N']:>5}, {obs['pairing']:>7}: "
                  f"CV={obs['CV']:.3f}, censored={obs['censored_fraction']:.1%}")

    # 5. Key dimensionless numbers
    print(f"\n## 5. Key Dimensionless Numbers Extracted")

    # The most physically meaningful extracted quantity
    if "eta_global" in couplings:
        eta = couplings["eta_global"]
        print(f"  η (scaling exponent) = {eta:.4f}")
        print(f"    If η = 1: pure Poisson (independent nucleation)")
        print(f"    If η = 0: no size dependence (collective)")
        print(f"    Observed: intermediate → cooperative nucleation")
        print(f"")
        print(f"    η vs QCD constants:")
        print(f"      η ≈ {eta:.3f}")
        print(f"      1/2 = 0.500")
        print(f"      2/3 = 0.667 (= 1 - 1/N_c)")
        print(f"      b_0 = {B_0:.3f} (1-loop beta)")
        print(f"      1 - b_0 = {1-B_0:.3f}")
        print(f"")
        # Check if η ≈ 1 - 1/N_c = 2/3
        if abs(eta - 2/3) < 0.1:
            print(f"    *** η ≈ 2/3 = 1 - 1/N_c ***")
            print(f"    This would mean the transition is controlled by the")
            print(f"    number of colors. The 1/N_c correction to pure Poisson")
            print(f"    is exactly what you'd expect from color correlations.")
        elif abs(eta - 0.5) < 0.1:
            print(f"    *** η ≈ 1/2 ***")
            print(f"    This would correspond to diffusive nucleation")
            print(f"    (random walk in program space).")

    # 6. Summary
    print(f"\n## SUMMARY")
    print(f"  The transition dynamics yield several dimensionless numbers:")
    if "eta_global" in couplings:
        print(f"  1. Scaling exponent η ≈ {couplings['eta_global']:.3f}")
    print(f"  2. Nucleation probability P(N=1666, 5M) ≈ 0.75")
    print(f"  3. Dimensionless rate Γ×N ≈ {1666/1_800_000:.4f}")
    print(f"")
    print(f"  None of these directly give α_s(√σ) = 1/64 = 0.0156.")
    print(f"  However, the scaling exponent η encodes information about")
    print(f"  the COOPERATION structure of nucleation — how correlated")
    print(f"  the trit fluctuations are. If η = 1-1/N_c = 2/3, this")
    print(f"  would be a striking structural connection to SU(3).")
    print(f"")
    print(f"  To connect to R_stella, one would need:")
    print(f"  - A theoretical prediction for η from CG framework")
    print(f"  - A mapping from η to a physical observable")
    print(f"  - Currently both are missing; this remains speculative")

    # Save results
    output = {
        "investigation": "Path 3: Transition Dynamics",
        "timestamp": datetime.now().isoformat(),
        "question": "Does the transition probability encode α_s?",
        "nucleation_rates": {
            f"N={r['N']}_{r['pairing']}": {
                "P_nuc": r["P_nuc"],
                "Gamma": r["Gamma"],
                "Gamma_N": r["Gamma_N"],
            }
            for r in rates.values()
        },
        "scaling_fits": {
            k: float(v) if isinstance(v, (int, float, np.floating)) else v
            for k, v in couplings.items()
            if k in ("eta_global", "eta_local")
        },
        "transition_character": trans["character"],
        "mean_CV": trans.get("mean_CV"),
        "comparisons": [
            {"quantity": c["quantity"], "value": c["value"]}
            for c in comparisons
        ],
        "verdict": (
            "Scaling exponent η is the most interesting extracted number. "
            "If η = 2/3 = 1 - 1/N_c, it would connect to SU(3) color structure. "
            "Cannot independently fix R_stella without theoretical framework for η."
        ),
    }

    output_path = Path(__file__).parent / "path3_transition_dynamics_results.json"
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
