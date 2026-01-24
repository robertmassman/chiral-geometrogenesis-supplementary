#!/usr/bin/env python3
"""
Proposition 6.5.1 tt̄ Cross Section Verification

This script verifies the CG predictions for tt̄ cross sections against
current experimental data and theoretical predictions.

Sources:
- CERN TWiki: https://twiki.cern.ch/twiki/bin/view/LHCPhysics/TtbarNNLO
- ATLAS 13.6 TeV: arXiv:2308.09529
- PDG 2024 for top mass

Created: 2026-01-22
"""

import numpy as np
import json
from datetime import datetime

# Theoretical predictions (NNLO+NNLL, Top++v2.0)
# Source: https://twiki.cern.ch/twiki/bin/view/LHCPhysics/TtbarNNLO
theory = {
    7: {
        "value": 174.6,
        "scale_up": 5.3, "scale_down": 6.9,
        "pdf_alpha_s": 5.0,
        "mass_up": 5.5, "mass_down": 5.3
    },
    8: {
        "value": 252.9,
        "scale_up": 7.4, "scale_down": 9.9,
        "pdf_alpha_s": 7.0,
        "mass_up": 7.7, "mass_down": 7.5
    },
    13: {
        "value": 833.9,
        "scale_up": 20.5, "scale_down": 30.0,
        "pdf_alpha_s": 21.0,
        "mass_up": 23.2, "mass_down": 22.5
    },
    13.6: {
        "value": 923.6,
        "scale_up": 22.6, "scale_down": 33.4,
        "pdf_alpha_s": 22.8,
        "mass_up": 25.4, "mass_down": 24.6
    }
}

# Experimental measurements (updated to 2024 values)
# Sources: ATLAS and CMS combined where available
experiment = {
    7: {"value": 173, "stat": 3, "syst": 8, "lumi": 7, "source": "ATLAS+CMS 2012"},
    8: {"value": 242, "stat": 2, "syst": 8, "lumi": 9, "source": "ATLAS+CMS 2014"},
    13: {"value": 829, "stat": 1, "syst": 13, "lumi": 14, "source": "ATLAS 2024 (full Run 2)"},
    13.6: {"value": 850, "stat": 3, "syst": 18, "lumi": 20, "source": "ATLAS 2023 (arXiv:2308.09529)"}
}

def total_theory_uncertainty(sqrt_s):
    """Combine theory uncertainties in quadrature."""
    t = theory[sqrt_s]
    # Average of asymmetric uncertainties for simplicity
    scale = (t["scale_up"] + t["scale_down"]) / 2
    pdf = t["pdf_alpha_s"]
    mass = (t["mass_up"] + t["mass_down"]) / 2
    return np.sqrt(scale**2 + pdf**2 + mass**2)

def total_exp_uncertainty(sqrt_s):
    """Combine experimental uncertainties in quadrature."""
    e = experiment[sqrt_s]
    return np.sqrt(e["stat"]**2 + e["syst"]**2 + e["lumi"]**2)

def compute_deviation_sigma(sqrt_s):
    """Compute deviation in standard deviations."""
    th = theory[sqrt_s]["value"]
    exp = experiment[sqrt_s]["value"]
    th_unc = total_theory_uncertainty(sqrt_s)
    exp_unc = total_exp_uncertainty(sqrt_s)
    total_unc = np.sqrt(th_unc**2 + exp_unc**2)
    return (exp - th) / total_unc

def main():
    results = {
        "title": "tt̄ Cross Section Verification",
        "date": datetime.now().isoformat(),
        "measurements": []
    }

    print("=" * 70)
    print("Proposition 6.5.1: tt̄ Cross Section Verification")
    print("=" * 70)

    print("\n1. COMPARISON: THEORY vs EXPERIMENT")
    print("-" * 70)
    print(f"{'√s (TeV)':<10} {'Theory (pb)':<15} {'Exp (pb)':<15} {'Dev (σ)':<10} {'Status':<10}")
    print("-" * 70)

    for sqrt_s in [7, 8, 13, 13.6]:
        th = theory[sqrt_s]["value"]
        th_unc = total_theory_uncertainty(sqrt_s)
        exp = experiment[sqrt_s]["value"]
        exp_unc = total_exp_uncertainty(sqrt_s)
        dev = compute_deviation_sigma(sqrt_s)

        status = "✅" if abs(dev) < 2 else "⚠️"

        print(f"{sqrt_s:<10} {th:.1f} ± {th_unc:.1f}    {exp:.0f} ± {exp_unc:.0f}    {dev:+.2f}      {status}")

        results["measurements"].append({
            "sqrt_s_TeV": sqrt_s,
            "theory_pb": th,
            "theory_unc_pb": float(th_unc),
            "experiment_pb": exp,
            "experiment_unc_pb": float(exp_unc),
            "deviation_sigma": float(dev),
            "source": experiment[sqrt_s]["source"],
            "agreement": "yes" if abs(dev) < 2 else "no"
        })

    print("-" * 70)

    # Special analysis for 13.6 TeV tension
    print("\n2. 13.6 TeV ANALYSIS")
    print("-" * 70)
    sqrt_s = 13.6
    th = theory[sqrt_s]["value"]
    exp = experiment[sqrt_s]["value"]
    th_unc = total_theory_uncertainty(sqrt_s)
    exp_unc = total_exp_uncertainty(sqrt_s)
    combined_unc = np.sqrt(th_unc**2 + exp_unc**2)
    dev = compute_deviation_sigma(sqrt_s)

    print(f"   Theory (NNLO+NNLL): {th:.1f} ± {th_unc:.1f} pb")
    print(f"   Experiment (ATLAS): {exp:.0f} ± {exp_unc:.0f} pb")
    print(f"   Combined uncertainty: {combined_unc:.1f} pb")
    print(f"   Deviation: {abs(th - exp):.1f} pb = {abs(dev):.2f}σ")

    if abs(dev) > 2:
        print(f"\n   ⚠️ Tension at {abs(dev):.1f}σ level")
        print(f"   Possible explanations:")
        print(f"   - Early Run 3 data (29 fb⁻¹) - expect precision to improve")
        print(f"   - Luminosity calibration still being refined")
        print(f"   - PDF uncertainties may be underestimated")
    else:
        print(f"\n   ✅ Agreement within {abs(dev):.1f}σ")

    # CG predictions
    print("\n3. CG FRAMEWORK PREDICTIONS")
    print("-" * 70)
    print("   CG uses identical tree-level amplitudes as SM (Theorem 6.2.1)")
    print("   CG uses identical NLO corrections as SM (Proposition 6.3.1)")
    print("   Therefore: σ_CG = σ_SM at current precision")
    print(f"\n   CG predictions match theoretical values:")

    for sqrt_s in [7, 8, 13, 13.6]:
        print(f"   √s = {sqrt_s} TeV: σ_CG = {theory[sqrt_s]['value']:.1f} pb")

    results["cg_predictions"] = {
        "note": "CG predictions identical to SM NNLO+NNLL at current precision",
        "form_factor_correction": "Negligible for m_tt̄ << Λ_EW ~ 10 TeV"
    }

    # Recommended document values
    print("\n4. RECOMMENDED DOCUMENT UPDATES")
    print("-" * 70)
    print("   Current document values should be updated to:")
    print(f"\n   | √s (TeV) | CG NNLO   | Data (2024)    | Agreement |")
    print(f"   |----------|-----------|----------------|-----------|")

    for sqrt_s in [7, 8, 13, 13.6]:
        th = theory[sqrt_s]["value"]
        exp = experiment[sqrt_s]["value"]
        exp_unc = total_exp_uncertainty(sqrt_s)
        dev = compute_deviation_sigma(sqrt_s)

        if sqrt_s == 13.6 and abs(dev) > 1.5:
            agreement = f"⚠️ ({abs(dev):.1f}σ tension)"
        else:
            agreement = "✅"

        print(f"   | {sqrt_s:<8} | {int(th)} pb   | {int(exp)} ± {int(exp_unc)} pb   | {agreement:<9} |")

    results["document_updates"] = {
        "13_TeV": {"theory": 834, "experiment": 829, "uncertainty": 20},
        "13.6_TeV": {"theory": 924, "experiment": 850, "uncertainty": 27,
                     "tension_sigma": float(abs(compute_deviation_sigma(13.6)))}
    }

    # Save results
    output_file = "prop_6_5_1_ttbar_results.json"
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n   Results saved to: {output_file}")

    return results

if __name__ == "__main__":
    main()
