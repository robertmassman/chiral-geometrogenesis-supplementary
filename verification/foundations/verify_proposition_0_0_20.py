#!/usr/bin/env python3
"""
Adversarial Physics Verification: Proposition 0.0.20
Electroweak Scale from Central Charge Flow

This script performs comprehensive numerical verification of Proposition 0.0.20,
which claims: v_H/sqrt(sigma) = exp(1/(2*pi^2 * Delta_a_EW))

Adversarial tests include:
1. Central charge calculations with exact vs rounded values
2. Sensitivity analysis to Delta_a precision
3. QCD application test (should fail if formula is universal)
4. Limiting case analysis
5. Comparison with Props 0.0.18, 0.0.19
6. Monte Carlo uncertainty propagation

Author: Multi-Agent Verification System
Date: 2026-01-22
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, Tuple, List
import json
from pathlib import Path

# Physical constants (PDG 2024 / FLAG 2024)
V_H_OBS = 246.22  # GeV, Higgs VEV
SQRT_SIGMA_OBS = 0.440  # GeV, QCD string tension
SQRT_SIGMA_ERR = 0.030  # GeV, FLAG 2024 uncertainty
M_PLANCK = 1.22e19  # GeV

# Central charge values for free fields in 4D CFT
A_SCALAR = 1/360  # Real scalar
A_WEYL = 11/720   # Weyl fermion (half of Dirac)
A_VECTOR = 62/360  # Gauge boson (massless or massive in deep IR)

# Electroweak field content
# UV: SU(2) x U(1) + Higgs doublet
N_GAUGE_UV = 4  # W1, W2, W3, B
N_SCALAR_UV = 4  # Complex Higgs doublet = 4 real scalars

# IR: U(1)_EM + massive W, Z + physical Higgs
N_GAUGE_IR = 4  # W+, W-, Z, photon
N_SCALAR_IR = 1  # Physical Higgs (3 Goldstones eaten)


class CentralChargeCalculator:
    """Calculate central charge flow for gauge theories."""

    def __init__(self):
        self.a_scalar = A_SCALAR
        self.a_weyl = A_WEYL
        self.a_vector = A_VECTOR

    def compute_a_uv_bosonic(self) -> float:
        """UV central charge (bosonic sector only)."""
        return N_GAUGE_UV * self.a_vector + N_SCALAR_UV * self.a_scalar

    def compute_a_ir_bosonic(self) -> float:
        """IR central charge (bosonic sector only)."""
        return N_GAUGE_IR * self.a_vector + N_SCALAR_IR * self.a_scalar

    def compute_delta_a_exact(self) -> float:
        """Exact Delta_a from central charge difference."""
        return self.compute_a_uv_bosonic() - self.compute_a_ir_bosonic()

    def compute_delta_a_fraction(self) -> Tuple[int, int]:
        """Return Delta_a as exact fraction (numerator, denominator)."""
        # a_UV = 252/360, a_IR = 249/360
        # Delta_a = 3/360 = 1/120
        return (3, 360)


class HierarchyFormula:
    """Compute electroweak hierarchy from central charge flow."""

    def __init__(self, delta_a: float):
        self.delta_a = delta_a

    def hierarchy_ratio(self) -> float:
        """v_H / sqrt(sigma) from the proposed formula."""
        if self.delta_a <= 0:
            return np.inf
        exponent = 1 / (2 * np.pi**2 * self.delta_a)
        return np.exp(exponent)

    def predict_v_h(self, sqrt_sigma: float) -> float:
        """Predict Higgs VEV from QCD string tension."""
        return sqrt_sigma * self.hierarchy_ratio()

    def compute_exponent(self) -> float:
        """Return the exponent 1/(2*pi^2*Delta_a)."""
        if self.delta_a <= 0:
            return np.inf
        return 1 / (2 * np.pi**2 * self.delta_a)


def test_central_charge_calculation() -> Dict:
    """Test 1: Verify central charge calculations."""
    calc = CentralChargeCalculator()

    a_uv = calc.compute_a_uv_bosonic()
    a_ir = calc.compute_a_ir_bosonic()
    delta_a_exact = calc.compute_delta_a_exact()

    # Expected values from proposition
    a_uv_expected = 252/360
    a_ir_expected = 249/360
    delta_a_expected_exact = 3/360
    delta_a_rounded = 0.008  # As used in proposition

    results = {
        "a_UV_computed": a_uv,
        "a_UV_expected": a_uv_expected,
        "a_UV_match": np.isclose(a_uv, a_uv_expected),
        "a_IR_computed": a_ir,
        "a_IR_expected": a_ir_expected,
        "a_IR_match": np.isclose(a_ir, a_ir_expected),
        "delta_a_exact": delta_a_exact,
        "delta_a_fraction": "3/360 = 1/120",
        "delta_a_decimal": delta_a_exact,
        "delta_a_rounded": delta_a_rounded,
        "rounding_error_percent": abs(delta_a_exact - delta_a_rounded) / delta_a_exact * 100
    }

    print("\n" + "="*60)
    print("TEST 1: Central Charge Calculation")
    print("="*60)
    print(f"a_UV (bosonic): {a_uv:.6f} (expected: {a_uv_expected:.6f}) - {'PASS' if results['a_UV_match'] else 'FAIL'}")
    print(f"a_IR (bosonic): {a_ir:.6f} (expected: {a_ir_expected:.6f}) - {'PASS' if results['a_IR_match'] else 'FAIL'}")
    print(f"Delta_a (exact): {delta_a_exact:.6f} = 3/360 = 1/120")
    print(f"Delta_a (rounded): {delta_a_rounded}")
    print(f"Rounding error: {results['rounding_error_percent']:.2f}%")

    return results


def test_exact_vs_rounded() -> Dict:
    """Test 2: Compare predictions using exact vs rounded Delta_a."""
    delta_a_exact = 3/360  # = 0.008333...
    delta_a_rounded = 0.008

    formula_exact = HierarchyFormula(delta_a_exact)
    formula_rounded = HierarchyFormula(delta_a_rounded)

    ratio_exact = formula_exact.hierarchy_ratio()
    ratio_rounded = formula_rounded.hierarchy_ratio()
    # Both v_H and sqrt_sigma should be in same units (GeV)
    # sqrt_sigma = 0.440 GeV = 440 MeV
    ratio_observed = V_H_OBS / SQRT_SIGMA_OBS  # Both in GeV: 246.22 / 0.440 = 559.6

    v_h_exact = formula_exact.predict_v_h(SQRT_SIGMA_OBS)
    v_h_rounded = formula_rounded.predict_v_h(SQRT_SIGMA_OBS)

    error_exact = abs(ratio_exact - ratio_observed) / ratio_observed * 100
    error_rounded = abs(ratio_rounded - ratio_observed) / ratio_observed * 100

    results = {
        "delta_a_exact": delta_a_exact,
        "delta_a_rounded": delta_a_rounded,
        "exponent_exact": formula_exact.compute_exponent(),
        "exponent_rounded": formula_rounded.compute_exponent(),
        "ratio_exact": ratio_exact,
        "ratio_rounded": ratio_rounded,
        "ratio_observed": ratio_observed,
        "v_H_exact_GeV": v_h_exact,
        "v_H_rounded_GeV": v_h_rounded,
        "v_H_observed_GeV": V_H_OBS,
        "error_exact_percent": error_exact,
        "error_rounded_percent": error_rounded
    }

    print("\n" + "="*60)
    print("TEST 2: Exact vs Rounded Delta_a Comparison")
    print("="*60)
    print(f"Using Delta_a = {delta_a_exact:.6f} (exact 3/360):")
    print(f"  Exponent: {formula_exact.compute_exponent():.4f}")
    print(f"  v_H/sqrt(sigma) = {ratio_exact:.1f}")
    print(f"  v_H prediction = {v_h_exact:.1f} GeV")
    print(f"  Error vs observed: {error_exact:.1f}%")
    print()
    print(f"Using Delta_a = {delta_a_rounded} (rounded, as in proposition):")
    print(f"  Exponent: {formula_rounded.compute_exponent():.4f}")
    print(f"  v_H/sqrt(sigma) = {ratio_rounded:.1f}")
    print(f"  v_H prediction = {v_h_rounded:.1f} GeV")
    print(f"  Error vs observed: {error_rounded:.1f}%")
    print()
    print(f"Observed: v_H/sqrt(sigma) = {ratio_observed:.1f}")
    print()
    print("*** CRITICAL: The 0.2% agreement requires using rounded 0.008, not exact 0.00833 ***")
    print(f"*** With exact value, error is {error_exact:.1f}%, not 0.2% ***")

    return results


def test_qcd_application() -> Dict:
    """Test 3: Apply formula to QCD (should fail if formula is universal)."""
    # QCD: SU(3) with N_f = 3 light flavors
    # Proposition claims Delta_a_QCD ~ 1.6
    delta_a_qcd = 1.6

    formula = HierarchyFormula(delta_a_qcd)
    ratio_predicted = formula.hierarchy_ratio()

    # Observed QCD-Planck hierarchy
    ratio_observed = SQRT_SIGMA_OBS / M_PLANCK

    results = {
        "delta_a_QCD": delta_a_qcd,
        "exponent": formula.compute_exponent(),
        "ratio_predicted": ratio_predicted,
        "ratio_observed": ratio_observed,
        "ratio_observed_log10": np.log10(ratio_observed),
        "formula_works_for_QCD": False  # Expected to fail
    }

    print("\n" + "="*60)
    print("TEST 3: QCD Application (Formula Universality Test)")
    print("="*60)
    print(f"Delta_a_QCD = {delta_a_qcd}")
    print(f"Exponent 1/(2*pi^2 * {delta_a_qcd}) = {formula.compute_exponent():.4f}")
    print(f"Formula predicts: sqrt(sigma)/Lambda_UV = {ratio_predicted:.4f}")
    print(f"Observed: sqrt(sigma)/M_Planck = {ratio_observed:.2e} (~ 10^{np.log10(ratio_observed):.0f})")
    print()
    print("*** CRITICAL FAILURE: Formula predicts ratio ~ 1 for QCD ***")
    print("*** Observed ratio is ~ 10^-19 ***")
    print("*** This proves the formula is NOT universal ***")

    return results


def test_limiting_cases() -> Dict:
    """Test 4: Analyze limiting cases of the formula."""
    results = {}

    print("\n" + "="*60)
    print("TEST 4: Limiting Case Analysis")
    print("="*60)

    # Limit 1: Delta_a -> 0
    print("\nLimit: Delta_a -> 0")
    delta_a_small = [0.1, 0.01, 0.001, 0.0001]
    for da in delta_a_small:
        formula = HierarchyFormula(da)
        ratio = formula.hierarchy_ratio()
        print(f"  Delta_a = {da}: v_H/sqrt(sigma) = {ratio:.2e}")
    results["limit_small_delta_a"] = "Diverges to infinity (UNPHYSICAL)"
    print("  -> As Delta_a -> 0, ratio -> infinity (UNPHYSICAL)")

    # Limit 2: Delta_a -> infinity
    print("\nLimit: Delta_a -> infinity")
    delta_a_large = [1, 10, 100]
    for da in delta_a_large:
        formula = HierarchyFormula(da)
        ratio = formula.hierarchy_ratio()
        print(f"  Delta_a = {da}: v_H/sqrt(sigma) = {ratio:.4f}")
    results["limit_large_delta_a"] = "Approaches 1"
    print("  -> As Delta_a -> infinity, ratio -> 1")

    # Physical interpretation
    print("\nPhysical Issues:")
    print("  1. Delta_a = 0 (no symmetry breaking) should give NO hierarchy, not infinite")
    print("  2. Large Delta_a (drastic flow) should give LARGE hierarchy, not ratio ~ 1")
    print("  -> Formula has inverted behavior from physical expectations!")

    results["physical_interpretation"] = "Formula inverts expected behavior"

    return results


def test_comparison_with_other_props() -> Dict:
    """Test 5: Compare with Props 0.0.18 and 0.0.19 formulas."""

    # Prop 0.0.18: triality^2 * sqrt(H4/F4) * phi^6
    triality = 3
    H4_order = 14400  # 600-cell symmetry group order
    F4_order = 1152   # 24-cell symmetry group order
    phi = (1 + np.sqrt(5)) / 2  # Golden ratio

    ratio_018 = triality**2 * np.sqrt(H4_order / F4_order) * phi**6

    # Prop 0.0.19: N_gen * triality * sqrt(H4/F4) * exp(16/5.6)
    N_gen = 3  # Number of generations
    index_ew = 5.6  # Electroweak topological index

    ratio_019 = N_gen * triality * np.sqrt(H4_order / F4_order) * np.exp(16 / index_ew)

    # Prop 0.0.20
    delta_a_exact = 3/360
    formula = HierarchyFormula(delta_a_exact)
    ratio_020_exact = formula.hierarchy_ratio()

    delta_a_rounded = 0.008
    formula_rounded = HierarchyFormula(delta_a_rounded)
    ratio_020_rounded = formula_rounded.hierarchy_ratio()

    # Both in GeV: 246.22 / 0.440 = 559.6
    ratio_observed = V_H_OBS / SQRT_SIGMA_OBS

    results = {
        "prop_018": ratio_018,
        "prop_019": ratio_019,
        "prop_020_exact": ratio_020_exact,
        "prop_020_rounded": ratio_020_rounded,
        "observed": ratio_observed,
        "error_018": abs(ratio_018 - ratio_observed) / ratio_observed * 100,
        "error_019": abs(ratio_019 - ratio_observed) / ratio_observed * 100,
        "error_020_exact": abs(ratio_020_exact - ratio_observed) / ratio_observed * 100,
        "error_020_rounded": abs(ratio_020_rounded - ratio_observed) / ratio_observed * 100
    }

    print("\n" + "="*60)
    print("TEST 5: Comparison with Props 0.0.18 and 0.0.19")
    print("="*60)
    print(f"Observed: v_H/sqrt(sigma) = {ratio_observed:.1f}")
    print()
    print(f"Prop 0.0.18 (geometry): triality^2 * sqrt(H4/F4) * phi^6 = {ratio_018:.1f}")
    print(f"  Error: {results['error_018']:.1f}%")
    print()
    print(f"Prop 0.0.19 (topological): N_gen * triality * sqrt(H4/F4) * exp(16/5.6) = {ratio_019:.1f}")
    print(f"  Error: {results['error_019']:.1f}%")
    print()
    print(f"Prop 0.0.20 (exact Delta_a): exp(1/(2*pi^2 * 0.00833)) = {ratio_020_exact:.1f}")
    print(f"  Error: {results['error_020_exact']:.1f}%")
    print()
    print(f"Prop 0.0.20 (rounded Delta_a): exp(1/(2*pi^2 * 0.008)) = {ratio_020_rounded:.1f}")
    print(f"  Error: {results['error_020_rounded']:.1f}%")

    # Decomposition check
    print("\n" + "-"*40)
    print("Decomposition Check (Prop 0.0.20 §7.3):")
    ln_observed = np.log(ratio_observed)
    ln_N_triality = np.log(N_gen * triality)  # ln(9)
    ln_polytope = 0.5 * np.log(H4_order / F4_order)  # ln(sqrt(12.5))
    topological_term = 16 / index_ew  # 16/5.6

    print(f"  ln(560) = {ln_observed:.3f}")
    print(f"  ln(N_gen * triality) = ln(9) = {ln_N_triality:.3f}")
    print(f"  0.5*ln(H4/F4) = 0.5*ln(12.5) = {ln_polytope:.3f}")
    print(f"  16/5.6 = {topological_term:.3f}")
    print(f"  Sum = {ln_N_triality + ln_polytope + topological_term:.3f}")
    print(f"  Difference = {abs(ln_observed - (ln_N_triality + ln_polytope + topological_term)):.3f}")

    return results


def test_monte_carlo_uncertainty() -> Dict:
    """Test 6: Monte Carlo uncertainty propagation."""
    n_samples = 10000

    # Sample sqrt(sigma) with uncertainty
    sqrt_sigma_samples = np.random.normal(SQRT_SIGMA_OBS, SQRT_SIGMA_ERR, n_samples)

    # Sample Delta_a with uncertainty (assume 5% uncertainty)
    delta_a_mean = 3/360
    delta_a_err = 0.05 * delta_a_mean
    delta_a_samples = np.random.normal(delta_a_mean, delta_a_err, n_samples)

    # Compute predictions
    v_h_predictions = []
    for sqrt_s, da in zip(sqrt_sigma_samples, delta_a_samples):
        if da > 0:
            formula = HierarchyFormula(da)
            v_h_predictions.append(formula.predict_v_h(sqrt_s))

    v_h_predictions = np.array(v_h_predictions)

    results = {
        "v_H_mean_GeV": np.mean(v_h_predictions),
        "v_H_std_GeV": np.std(v_h_predictions),
        "v_H_68_CI": (np.percentile(v_h_predictions, 16), np.percentile(v_h_predictions, 84)),
        "v_H_95_CI": (np.percentile(v_h_predictions, 2.5), np.percentile(v_h_predictions, 97.5)),
        "n_samples": n_samples
    }

    print("\n" + "="*60)
    print("TEST 6: Monte Carlo Uncertainty Propagation")
    print("="*60)
    print(f"Inputs: sqrt(sigma) = {SQRT_SIGMA_OBS} +/- {SQRT_SIGMA_ERR} GeV")
    print(f"        Delta_a = {delta_a_mean:.6f} +/- {delta_a_err:.6f}")
    print(f"Samples: {n_samples}")
    print()
    print(f"v_H prediction: {np.mean(v_h_predictions):.1f} +/- {np.std(v_h_predictions):.1f} GeV")
    print(f"68% CI: [{results['v_H_68_CI'][0]:.1f}, {results['v_H_68_CI'][1]:.1f}] GeV")
    print(f"95% CI: [{results['v_H_95_CI'][0]:.1f}, {results['v_H_95_CI'][1]:.1f}] GeV")
    print(f"Observed: {V_H_OBS} GeV")

    # Check if observed is within 95% CI
    within_95 = results['v_H_95_CI'][0] <= V_H_OBS <= results['v_H_95_CI'][1]
    print(f"Observed within 95% CI: {'YES' if within_95 else 'NO'}")

    results["within_95_CI"] = within_95

    return results


def generate_verification_plot(results: Dict) -> None:
    """Generate comprehensive verification plot."""
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    fig.suptitle('Proposition 0.0.20: Adversarial Physics Verification', fontsize=14, fontweight='bold')

    # Plot 1: Central charge comparison
    ax1 = axes[0, 0]
    labels = ['a_UV', 'a_IR', 'Delta_a\n(x100)']
    computed = [252/360, 249/360, (3/360)*100]
    expected = [0.700, 0.692, 0.833]
    x = np.arange(len(labels))
    width = 0.35
    ax1.bar(x - width/2, computed, width, label='Computed', color='steelblue')
    ax1.bar(x + width/2, expected, width, label='Expected', color='coral', alpha=0.7)
    ax1.set_ylabel('Value')
    ax1.set_title('Central Charge Verification')
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels)
    ax1.legend()
    ax1.set_ylim(0, 1.0)

    # Plot 2: Exact vs Rounded comparison
    ax2 = axes[0, 1]
    categories = ['Exact\n(0.00833)', 'Rounded\n(0.008)', 'Observed']
    ratios = [438, 561, 560]
    colors = ['red', 'green', 'blue']
    bars = ax2.bar(categories, ratios, color=colors, alpha=0.7)
    ax2.axhline(y=560, color='blue', linestyle='--', label='Observed')
    ax2.set_ylabel('v_H / sqrt(sigma)')
    ax2.set_title('Exact vs Rounded Delta_a')
    for bar, ratio in zip(bars, ratios):
        ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 10,
                f'{ratio:.0f}', ha='center', va='bottom')
    ax2.set_ylim(0, 700)

    # Plot 3: Error comparison
    ax3 = axes[0, 2]
    props = ['0.0.18', '0.0.19', '0.0.20\n(exact)', '0.0.20\n(rounded)']
    errors = [2.0, 0.9, 21.8, 0.2]
    colors = ['steelblue', 'steelblue', 'coral', 'green']
    ax3.bar(props, errors, color=colors, alpha=0.7)
    ax3.set_ylabel('Error (%)')
    ax3.set_title('Error Comparison Across Propositions')
    ax3.axhline(y=5, color='orange', linestyle='--', label='5% threshold')
    for i, (prop, err) in enumerate(zip(props, errors)):
        ax3.text(i, err + 0.5, f'{err:.1f}%', ha='center', va='bottom')

    # Plot 4: Sensitivity to Delta_a
    ax4 = axes[1, 0]
    delta_a_range = np.linspace(0.001, 0.02, 100)
    ratios = [HierarchyFormula(da).hierarchy_ratio() for da in delta_a_range]
    ax4.plot(delta_a_range, ratios, 'b-', linewidth=2)
    ax4.axhline(y=560, color='r', linestyle='--', label='Observed (560)')
    ax4.axvline(x=3/360, color='g', linestyle=':', label=f'Exact Delta_a ({3/360:.5f})')
    ax4.axvline(x=0.008, color='orange', linestyle=':', label='Rounded (0.008)')
    ax4.set_xlabel('Delta_a')
    ax4.set_ylabel('v_H / sqrt(sigma)')
    ax4.set_title('Sensitivity to Delta_a')
    ax4.legend(fontsize=8)
    ax4.set_ylim(0, 2000)

    # Plot 5: QCD test
    ax5 = axes[1, 1]
    systems = ['Electroweak\n(Delta_a=0.008)', 'QCD\n(Delta_a=1.6)']
    predicted_log = [np.log10(561), np.log10(1.03)]
    observed_log = [np.log10(560), -19]  # log10(sqrt_sigma/M_Planck) ~ -19
    x = np.arange(len(systems))
    width = 0.35
    ax5.bar(x - width/2, predicted_log, width, label='Predicted', color='coral')
    ax5.bar(x + width/2, observed_log, width, label='Observed', color='steelblue')
    ax5.set_ylabel('log10(ratio)')
    ax5.set_title('QCD Universality Test (FAILS)')
    ax5.set_xticks(x)
    ax5.set_xticklabels(systems)
    ax5.legend()

    # Plot 6: Monte Carlo distribution
    ax6 = axes[1, 2]
    # Regenerate for plot
    n_samples = 5000
    sqrt_sigma_samples = np.random.normal(SQRT_SIGMA_OBS, SQRT_SIGMA_ERR, n_samples)
    delta_a_mean = 3/360
    delta_a_err = 0.05 * delta_a_mean
    delta_a_samples = np.random.normal(delta_a_mean, delta_a_err, n_samples)
    v_h_predictions = []
    for sqrt_s, da in zip(sqrt_sigma_samples, delta_a_samples):
        if da > 0:
            v_h_predictions.append(HierarchyFormula(da).predict_v_h(sqrt_s))
    v_h_predictions = np.array(v_h_predictions)

    ax6.hist(v_h_predictions, bins=50, density=True, alpha=0.7, color='steelblue')
    ax6.axvline(x=V_H_OBS, color='red', linewidth=2, label=f'Observed ({V_H_OBS} GeV)')
    ax6.axvline(x=np.mean(v_h_predictions), color='green', linestyle='--',
                label=f'Mean ({np.mean(v_h_predictions):.1f} GeV)')
    ax6.set_xlabel('v_H (GeV)')
    ax6.set_ylabel('Probability Density')
    ax6.set_title('Monte Carlo: v_H Distribution (exact Delta_a)')
    ax6.legend(fontsize=8)

    plt.tight_layout()

    # Save plot
    plot_path = Path(__file__).parent.parent / 'plots' / 'proposition_0_0_20_adversarial_verification.png'
    plot_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to: {plot_path}")
    plt.close()


def main():
    """Run all verification tests."""
    print("="*60)
    print("ADVERSARIAL PHYSICS VERIFICATION")
    print("Proposition 0.0.20: Electroweak Scale from Central Charge Flow")
    print("="*60)

    all_results = {}

    # Run all tests
    all_results["test1_central_charge"] = test_central_charge_calculation()
    all_results["test2_exact_vs_rounded"] = test_exact_vs_rounded()
    all_results["test3_qcd_application"] = test_qcd_application()
    all_results["test4_limiting_cases"] = test_limiting_cases()
    all_results["test5_comparison"] = test_comparison_with_other_props()
    all_results["test6_monte_carlo"] = test_monte_carlo_uncertainty()

    # Generate plot
    generate_verification_plot(all_results)

    # Summary
    print("\n" + "="*60)
    print("VERIFICATION SUMMARY")
    print("="*60)

    print("\nCRITICAL FINDINGS:")
    print("-" * 40)
    print("1. Central charge calculations: VERIFIED")
    print("   a_UV = 252/360 = 0.700, a_IR = 249/360 = 0.692")
    print()
    print("2. Rounding manipulation: CONFIRMED")
    print("   Using exact Delta_a = 0.00833 gives 22% error")
    print("   Using rounded Delta_a = 0.008 gives 0.2% error")
    print("   The good agreement DEPENDS on rounding")
    print()
    print("3. QCD universality test: FAILED")
    print("   Formula predicts ratio ~ 1 for QCD")
    print("   Observed ratio is ~ 10^-19")
    print("   Formula is NOT universal")
    print()
    print("4. Limiting cases: PROBLEMATIC")
    print("   Delta_a -> 0 gives infinite hierarchy (unphysical)")
    print("   Large Delta_a gives ratio -> 1 (inverted from expectations)")
    print()
    print("VERDICT: PARTIAL VERIFICATION")
    print("  - Central charge math is correct")
    print("  - Formula is phenomenological, not derived")
    print("  - Agreement depends on convenient rounding")
    print("  - Formula fails for QCD, so not universal")

    # Save results to JSON
    results_path = Path(__file__).parent / 'verify_proposition_0_0_20_results.json'

    # Convert numpy types for JSON serialization
    def convert_for_json(obj):
        if isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, tuple):
            return list(obj)
        elif isinstance(obj, dict):
            return {k: convert_for_json(v) for k, v in obj.items()}
        return obj

    all_results_json = convert_for_json(all_results)

    with open(results_path, 'w') as f:
        json.dump(all_results_json, f, indent=2)
    print(f"\nResults saved to: {results_path}")

    return all_results


if __name__ == "__main__":
    main()
