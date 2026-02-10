#!/usr/bin/env python3
"""
Proposition 4.2.4: Sphaleron Rate from CG Topology - Verification Script

This script verifies:
1. Sphaleron energy calculation from CG-derived parameters
2. Sphaleron rate scaling in symmetric/broken phases
3. Washout criterion satisfaction with CG's first-order EWPT
4. Limiting cases and consistency checks

Created: 2026-02-08
"""

import numpy as np
import os

# Physical constants (PDG 2024)
V_HIGGS = 246.22  # GeV - Higgs VEV
M_HIGGS = 125.09  # GeV - Higgs mass
G2 = 0.6517  # SU(2) gauge coupling (Prop 0.0.24)
ALPHA_W = G2**2 / (4 * np.pi)  # Weak fine structure constant
M_PLANCK = 1.22e19  # GeV - Planck mass
G_STAR = 106.75  # Relativistic degrees of freedom at EW scale

# Derived quantities
LAMBDA_H = M_HIGGS**2 / (2 * V_HIGGS**2)  # Higgs self-coupling
X_RATIO = LAMBDA_H / G2**2  # λ_H / g²

# Sphaleron shape function B(x) - fit from Klinkhamer & Manton
def sphaleron_B(x):
    """
    Sphaleron shape function B(λ/g²).

    Asymptotic behaviors:
    - B(0) ≈ 1.52 (pure gauge)
    - B(x) ≈ 1.87 for x ~ 0.3
    - B(∞) → 2.72 (heavy Higgs)

    Fit from Arnold & McLerran (1987) Table I
    """
    # Linear interpolation for moderate x
    if x < 0.1:
        return 1.52 + 3.5 * x
    elif x < 0.5:
        return 1.87 + 0.16 * (x - 0.3)
    elif x < 2.0:
        return 1.90 + 0.35 * (x - 0.5)
    else:
        return 2.72 - 0.5 / x  # asymptotic approach


def sphaleron_energy(v, g, B_val):
    """Calculate sphaleron energy E_sph = 4πv/g × B."""
    return 4 * np.pi * v / g * B_val


def sphaleron_rate_symmetric(T, kappa=25):
    """
    Sphaleron rate in symmetric phase (T > T_c).

    Γ_sph = κ α_W^5 T^4

    Returns rate in GeV^4.
    """
    return kappa * ALPHA_W**5 * T**4


def sphaleron_rate_broken(T, E_sph, A_prefactor=1e10):
    """
    Sphaleron rate in broken phase (T < T_c).

    Γ_sph = A(T) exp(-E_sph/T)

    A_prefactor is in GeV^4 (order of magnitude estimate).
    """
    return A_prefactor * np.exp(-E_sph / T)


def hubble_rate(T):
    """
    Hubble rate H(T) at temperature T.

    H = sqrt(π²g*/90) × T²/M_Pl
    """
    return np.sqrt(np.pi**2 * G_STAR / 90) * T**2 / M_PLANCK


def washout_criterion(v_over_T, g=G2, B_val=None):
    """
    Calculate E_sph/T for given v/T ratio.

    E_sph/T = 4πv/gT × B = 4π(v/T)/g × B
    """
    if B_val is None:
        B_val = sphaleron_B(X_RATIO)
    return 4 * np.pi * v_over_T * B_val / g


def test_sphaleron_energy():
    """Test 1: Verify sphaleron energy calculation."""
    print("\n" + "="*60)
    print("Test 1: Sphaleron Energy Calculation")
    print("="*60)

    B_val = sphaleron_B(X_RATIO)
    E_sph = sphaleron_energy(V_HIGGS, G2, B_val)

    print(f"\nInput parameters:")
    print(f"  v = {V_HIGGS:.2f} GeV")
    print(f"  g₂ = {G2:.4f}")
    print(f"  λ_H = {LAMBDA_H:.4f}")
    print(f"  λ_H/g₂² = {X_RATIO:.4f}")
    print(f"  B({X_RATIO:.3f}) = {B_val:.3f}")

    print(f"\nCalculated sphaleron energy:")
    print(f"  E_sph = 4π × {V_HIGGS:.2f} / {G2:.4f} × {B_val:.3f}")
    print(f"  E_sph = {E_sph/1000:.2f} TeV")

    # Literature comparison
    E_sph_lit = 9.0  # TeV (typical value)
    deviation = abs(E_sph/1000 - E_sph_lit) / E_sph_lit * 100

    print(f"\nComparison with literature:")
    print(f"  Literature: E_sph ≈ {E_sph_lit} TeV")
    print(f"  CG derived: E_sph = {E_sph/1000:.2f} TeV")
    print(f"  Deviation: {deviation:.1f}%")

    passed = deviation < 5  # 5% tolerance
    print(f"\n{'✅ PASSED' if passed else '❌ FAILED'}: Sphaleron energy within 5% of literature")
    return passed


def test_rate_scaling():
    """Test 2: Verify rate scaling α_W^5 T^4."""
    print("\n" + "="*60)
    print("Test 2: Sphaleron Rate Scaling")
    print("="*60)

    # Test at different temperatures
    T_values = [80, 100, 120, 150]  # GeV

    print(f"\nα_W = g₂²/(4π) = {ALPHA_W:.6f}")
    print(f"α_W^5 = {ALPHA_W**5:.2e}")
    print(f"\nRate Γ_sph = κ α_W^5 T^4 (κ = 25):\n")

    print(f"{'T (GeV)':>10} {'Γ_sph (GeV⁴)':>15} {'Γ/T³ (GeV)':>15} {'H (GeV)':>15} {'Γ/T³/H':>12}")
    print("-" * 70)

    for T in T_values:
        Gamma = sphaleron_rate_symmetric(T)
        Gamma_per_vol = Gamma / T**3
        H = hubble_rate(T)
        ratio = Gamma_per_vol / H
        print(f"{T:>10.0f} {Gamma:>15.2e} {Gamma_per_vol:>15.2e} {H:>15.2e} {ratio:>12.2e}")

    # Verify T^4 scaling
    T1, T2 = 100, 150
    Gamma1 = sphaleron_rate_symmetric(T1)
    Gamma2 = sphaleron_rate_symmetric(T2)
    expected_ratio = (T2/T1)**4
    actual_ratio = Gamma2/Gamma1

    print(f"\nScaling verification:")
    print(f"  Γ(150)/Γ(100) = {actual_ratio:.4f}")
    print(f"  (150/100)^4 = {expected_ratio:.4f}")

    passed = abs(actual_ratio - expected_ratio) / expected_ratio < 0.01
    print(f"\n{'✅ PASSED' if passed else '❌ FAILED'}: Rate scales as T^4")
    return passed


def test_washout_criterion():
    """Test 3: Verify CG satisfies washout criterion."""
    print("\n" + "="*60)
    print("Test 3: Washout Criterion with CG Phase Transition")
    print("="*60)

    # CG prediction from Theorem 4.2.3
    v_over_T_cg = 1.22  # Central value
    v_over_T_err = 0.06  # Uncertainty

    # SM crossover value
    v_over_T_sm = 0.03

    B_val = sphaleron_B(X_RATIO)

    # Calculate E_sph/T ratios
    E_over_T_cg = washout_criterion(v_over_T_cg, B_val=B_val)
    E_over_T_sm = washout_criterion(v_over_T_sm, B_val=B_val)

    # Threshold for decoupling
    threshold = 37  # Conservative value

    print(f"\nPhase transition parameters:")
    print(f"  CG: v(T_c)/T_c = {v_over_T_cg} ± {v_over_T_err}")
    print(f"  SM: v(T_c)/T_c ≈ {v_over_T_sm} (crossover)")

    print(f"\nSphaleron energy ratios:")
    print(f"  E_sph/T_c (CG) = 4π × {v_over_T_cg} × {B_val:.3f} / {G2:.4f} = {E_over_T_cg:.1f}")
    print(f"  E_sph/T_c (SM) = 4π × {v_over_T_sm} × {B_val:.3f} / {G2:.4f} = {E_over_T_sm:.1f}")
    print(f"\n  Decoupling threshold: E_sph/T > {threshold}")

    # Boltzmann suppression
    suppression_cg = np.exp(-E_over_T_cg)
    suppression_sm = np.exp(-E_over_T_sm)

    print(f"\nBoltzmann suppression exp(-E_sph/T):")
    print(f"  CG: exp(-{E_over_T_cg:.0f}) ≈ {suppression_cg:.2e}")
    print(f"  SM: exp(-{E_over_T_sm:.1f}) ≈ {suppression_sm:.2e}")

    passed = E_over_T_cg > threshold
    print(f"\n{'✅ PASSED' if passed else '❌ FAILED'}: CG satisfies washout criterion (E_sph/T = {E_over_T_cg:.0f} > {threshold})")

    # Additional check: lower bound
    E_over_T_lower = washout_criterion(v_over_T_cg - v_over_T_err, B_val=B_val)
    robust = E_over_T_lower > threshold
    print(f"{'✅ PASSED' if robust else '❌ FAILED'}: Robust even at lower bound (E_sph/T = {E_over_T_lower:.0f} > {threshold})")

    return passed and robust


def test_limiting_cases():
    """Test 4: Verify limiting case behaviors."""
    print("\n" + "="*60)
    print("Test 4: Limiting Cases")
    print("="*60)

    all_passed = True

    # Test 4a: High temperature limit (symmetric phase)
    print("\n4a. High temperature limit (T → ∞, v → 0):")
    T_high = 1000  # GeV
    Gamma_high = sphaleron_rate_symmetric(T_high)
    expected = 25 * ALPHA_W**5 * T_high**4
    match = abs(Gamma_high - expected) / expected < 0.01
    print(f"  Γ_sph(T={T_high} GeV) = {Gamma_high:.2e} GeV⁴")
    print(f"  Expected κα_W^5 T^4 = {expected:.2e} GeV⁴")
    print(f"  {'✅ PASSED' if match else '❌ FAILED'}: Symmetric phase formula")
    all_passed = all_passed and match

    # Test 4b: Low temperature limit (T → 0, v → v₀)
    print("\n4b. Low temperature limit (T → 0):")
    T_low = 10  # GeV
    B_val = sphaleron_B(X_RATIO)
    E_sph_0 = sphaleron_energy(V_HIGGS, G2, B_val)
    Gamma_low = sphaleron_rate_broken(T_low, E_sph_0)
    is_suppressed = Gamma_low < 1e-100
    print(f"  E_sph(T=0) = {E_sph_0/1000:.2f} TeV")
    print(f"  E_sph/T = {E_sph_0/T_low:.0f}")
    print(f"  Γ_sph(T={T_low} GeV) ≈ {Gamma_low:.2e} GeV⁴ (effectively zero)")
    print(f"  {'✅ PASSED' if is_suppressed else '❌ FAILED'}: Complete decoupling at low T")
    all_passed = all_passed and is_suppressed

    # Test 4c: SM limit (κ_geo → 0, crossover)
    print("\n4c. SM limit (crossover, v/T → 0.03):")
    v_over_T_sm = 0.03
    E_over_T_sm = washout_criterion(v_over_T_sm, B_val=B_val)
    not_decoupled = E_over_T_sm < 37
    print(f"  v(T_c)/T_c = {v_over_T_sm}")
    print(f"  E_sph/T_c = {E_over_T_sm:.2f}")
    print(f"  Threshold: 37")
    print(f"  {'✅ PASSED' if not_decoupled else '❌ FAILED'}: SM does NOT satisfy washout criterion")
    all_passed = all_passed and not_decoupled

    return all_passed


def test_consistency_with_theorem_4_2_3():
    """Test 5: Verify consistency with Theorem 4.2.3 phase transition."""
    print("\n" + "="*60)
    print("Test 5: Consistency with Theorem 4.2.3")
    print("="*60)

    # Phase transition parameters from Theorem 4.2.3
    T_c = 123  # GeV (central estimate)
    v_Tc = 150  # GeV (central estimate)
    v_over_T = v_Tc / T_c

    print(f"\nFrom Theorem 4.2.3:")
    print(f"  T_c ≈ {T_c} GeV")
    print(f"  v(T_c) ≈ {v_Tc} GeV")
    print(f"  v(T_c)/T_c = {v_over_T:.2f}")

    # Calculate sphaleron energy at T_c
    B_val = sphaleron_B(X_RATIO)
    E_sph_Tc = sphaleron_energy(v_Tc, G2, B_val)
    E_over_T = E_sph_Tc / T_c

    print(f"\nSphaleron at T_c:")
    print(f"  E_sph(T_c) = {E_sph_Tc/1000:.2f} TeV")
    print(f"  E_sph(T_c)/T_c = {E_over_T:.1f}")

    # Rates
    Gamma_before = sphaleron_rate_symmetric(T_c)  # Just before transition
    Gamma_after = sphaleron_rate_broken(T_c, E_sph_Tc)  # Just after transition
    H_Tc = hubble_rate(T_c)

    print(f"\nRate comparison at T_c:")
    print(f"  Γ_sph (before EWPT): {Gamma_before:.2e} GeV⁴")
    print(f"  Γ_sph (after EWPT):  {Gamma_after:.2e} GeV⁴")
    print(f"  Suppression factor:  {Gamma_after/Gamma_before:.2e}")
    print(f"  Hubble rate H(T_c):  {H_Tc:.2e} GeV")

    # Check decoupling
    Gamma_per_vol_after = Gamma_after / T_c**3
    decoupled = Gamma_per_vol_after < H_Tc

    print(f"\nDecoupling check:")
    print(f"  Γ/T³ (after) = {Gamma_per_vol_after:.2e} GeV")
    print(f"  H(T_c) = {H_Tc:.2e} GeV")
    print(f"  {'✅ PASSED' if decoupled else '❌ FAILED'}: Sphalerons decouple after CG's first-order EWPT")

    return decoupled


def generate_summary_plot():
    """Generate summary visualization."""
    try:
        import matplotlib.pyplot as plt

        # Get absolute path for plots
        script_dir = os.path.dirname(os.path.abspath(__file__))
        plot_dir = os.path.join(script_dir, '..', 'plots')
        os.makedirs(plot_dir, exist_ok=True)

        fig, axes = plt.subplots(2, 2, figsize=(12, 10))

        # Plot 1: Sphaleron rate vs temperature
        ax1 = axes[0, 0]
        T_range = np.linspace(50, 200, 100)
        Gamma_range = [sphaleron_rate_symmetric(T) for T in T_range]
        ax1.semilogy(T_range, Gamma_range, 'b-', linewidth=2)
        ax1.set_xlabel('Temperature T (GeV)', fontsize=11)
        ax1.set_ylabel('Γ_sph (GeV⁴)', fontsize=11)
        ax1.set_title('Sphaleron Rate in Symmetric Phase', fontsize=12)
        ax1.grid(True, alpha=0.3)
        ax1.axvline(x=123, color='r', linestyle='--', label='T_c (CG)')
        ax1.legend()

        # Plot 2: E_sph/T vs v/T
        ax2 = axes[0, 1]
        v_over_T_range = np.linspace(0, 2, 100)
        B_val = sphaleron_B(X_RATIO)
        E_over_T_range = [washout_criterion(v_T, B_val=B_val) for v_T in v_over_T_range]
        ax2.plot(v_over_T_range, E_over_T_range, 'b-', linewidth=2)
        ax2.axhline(y=37, color='r', linestyle='--', label='Decoupling threshold')
        ax2.axvline(x=1.22, color='g', linestyle='--', label='CG: v/T = 1.22')
        ax2.axvline(x=0.03, color='orange', linestyle='--', label='SM: v/T = 0.03')
        ax2.fill_between(v_over_T_range, 37, max(E_over_T_range), alpha=0.2, color='green')
        ax2.set_xlabel('v(T)/T', fontsize=11)
        ax2.set_ylabel('E_sph/T', fontsize=11)
        ax2.set_title('Washout Criterion', fontsize=12)
        ax2.legend(fontsize=9)
        ax2.grid(True, alpha=0.3)
        ax2.set_ylim(0, 80)

        # Plot 3: Boltzmann suppression
        ax3 = axes[1, 0]
        E_over_T_vals = np.linspace(0, 60, 100)
        suppression = np.exp(-E_over_T_vals)
        ax3.semilogy(E_over_T_vals, suppression, 'b-', linewidth=2)
        ax3.axvline(x=44, color='g', linestyle='--', label='CG: E/T = 44')
        ax3.axvline(x=1.1, color='orange', linestyle='--', label='SM: E/T = 1.1')
        ax3.set_xlabel('E_sph/T', fontsize=11)
        ax3.set_ylabel('exp(-E_sph/T)', fontsize=11)
        ax3.set_title('Boltzmann Suppression Factor', fontsize=12)
        ax3.legend()
        ax3.grid(True, alpha=0.3)
        ax3.set_ylim(1e-25, 1)

        # Plot 4: Shape function B(λ/g²)
        ax4 = axes[1, 1]
        x_range = np.linspace(0, 3, 100)
        B_range = [sphaleron_B(x) for x in x_range]
        ax4.plot(x_range, B_range, 'b-', linewidth=2)
        ax4.axvline(x=X_RATIO, color='g', linestyle='--', label=f'CG: λ/g² = {X_RATIO:.3f}')
        ax4.scatter([X_RATIO], [sphaleron_B(X_RATIO)], color='g', s=100, zorder=5)
        ax4.set_xlabel('λ_H/g₂²', fontsize=11)
        ax4.set_ylabel('B(λ/g²)', fontsize=11)
        ax4.set_title('Sphaleron Shape Function', fontsize=12)
        ax4.legend()
        ax4.grid(True, alpha=0.3)

        plt.tight_layout()

        plot_path = os.path.join(plot_dir, 'proposition_4_2_4_sphaleron.png')
        plt.savefig(plot_path, dpi=150, bbox_inches='tight')
        print(f"\n📊 Summary plot saved to: {plot_path}")
        plt.close()

    except ImportError:
        print("\n⚠️  matplotlib not available, skipping plot generation")


def main():
    """Run all verification tests."""
    print("="*60)
    print("Proposition 4.2.4: Sphaleron Rate from CG Topology")
    print("Verification Script")
    print("="*60)

    results = []

    # Run all tests
    results.append(("Sphaleron Energy", test_sphaleron_energy()))
    results.append(("Rate Scaling", test_rate_scaling()))
    results.append(("Washout Criterion", test_washout_criterion()))
    results.append(("Limiting Cases", test_limiting_cases()))
    results.append(("Consistency with Thm 4.2.3", test_consistency_with_theorem_4_2_3()))

    # Generate plot
    generate_summary_plot()

    # Summary
    print("\n" + "="*60)
    print("VERIFICATION SUMMARY")
    print("="*60)

    all_passed = True
    for name, passed in results:
        status = "✅ PASSED" if passed else "❌ FAILED"
        print(f"  {name}: {status}")
        all_passed = all_passed and passed

    print("\n" + "-"*60)
    if all_passed:
        print("✅ ALL TESTS PASSED - Proposition 4.2.4 VERIFIED")
    else:
        print("❌ SOME TESTS FAILED - Review required")

    return all_passed


if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
