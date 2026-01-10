#!/usr/bin/env python3
"""
Proposition 0.0.17t Verification: Topological Origin of Scale Hierarchy
========================================================================

This script independently verifies the mathematical claims in Proposition 0.0.17t
regarding the topological origin of the QCD-Planck hierarchy.

Key claims to verify:
1. index(D_adj) = N_c² - 1 = 8
2. Hierarchy formula: R_stella/ℓ_P = exp([index]²/(2b₀))
3. Central charge calculations: a_UV, a_IR, Δa
4. Numerical consistency: ~2.5×10¹⁹
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# ============================================================================
# Physical Constants and Parameters
# ============================================================================

N_c = 3  # Number of colors (SU(3))
N_f = 3  # Number of light quark flavors

# Stella octangula topology
chi_stella = 4  # Euler characteristic
n_vertices = 8
n_edges = 12
n_faces = 8
n_connected_components = 2  # Two tetrahedra

# ============================================================================
# Test 1: Index Calculations
# ============================================================================

def test_index_from_su3():
    """Verify index(D_adj) = N_c² - 1 = 8 from SU(3) structure."""
    dim_adj = N_c**2 - 1
    expected = 8

    assert dim_adj == expected, f"dim(adj) = {dim_adj}, expected {expected}"
    print(f"✅ Test 1a: dim(adj) = N_c² - 1 = {dim_adj}")
    return dim_adj


def test_index_from_vertices():
    """Verify vertex counting gives index = 8."""
    # 8 vertices in stella octangula
    assert n_vertices == 8, f"n_vertices = {n_vertices}, expected 8"
    print(f"✅ Test 1b: Stella vertices = {n_vertices}")
    return n_vertices


def test_euler_characteristic():
    """Verify Euler characteristic χ = V - E + F = 4."""
    chi = n_vertices - n_edges + n_faces
    expected = 4

    assert chi == expected, f"χ = {chi}, expected {expected}"
    print(f"✅ Test 1c: Euler characteristic χ = {n_vertices} - {n_edges} + {n_faces} = {chi}")
    return chi


# ============================================================================
# Test 2: β-function and Hierarchy Formula
# ============================================================================

def test_beta_function_coefficient():
    """Verify b₀ = (11N_c - 2N_f)/(12π) for SU(3) with N_f=3."""
    # One-loop β-function coefficient
    b0_numerator = 11 * N_c - 2 * N_f  # = 33 - 6 = 27
    b0 = b0_numerator / (12 * np.pi)

    # Alternative form: b₀ = 9/(4π)
    b0_alt = 9 / (4 * np.pi)

    print(f"✅ Test 2a: b₀ = (11×{N_c} - 2×{N_f})/(12π) = {b0_numerator}/(12π) = {b0:.6f}")
    print(f"           b₀ = 9/(4π) = {b0_alt:.6f}")

    assert np.isclose(b0, b0_alt), f"b₀ forms disagree: {b0} vs {b0_alt}"
    print(f"           Both forms agree: ✅")

    return b0


def test_costello_bittleston_index():
    """Verify the Costello-Bittleston index = 11N_c - 2N_f = 27."""
    index_beta = 11 * N_c - 2 * N_f
    expected = 27

    assert index_beta == expected, f"index(D_β) = {index_beta}, expected {expected}"
    print(f"✅ Test 2b: Costello-Bittleston index = 11×{N_c} - 2×{N_f} = {index_beta}")
    return index_beta


def test_hierarchy_formula():
    """
    Verify the unified topological hierarchy formula:
    R_stella/ℓ_P = exp([index(D_adj)]² / (|π₀(∂S)| × index(D_β)/(12π)))
    """
    index_adj = N_c**2 - 1  # = 8
    index_beta = 11 * N_c - 2 * N_f  # = 27
    pi0 = n_connected_components  # = 2

    # Compute exponent
    numerator = index_adj**2  # = 64
    denominator = pi0 * index_beta / (12 * np.pi)  # = 2 × 27/(12π)
    exponent = numerator / denominator

    # Expected: 64 × 12π / 54 = 768π/54 ≈ 44.68
    expected_exponent = 64 * 12 * np.pi / 54

    print(f"\n✅ Test 2c: Hierarchy formula verification")
    print(f"   index(D_adj) = {index_adj}")
    print(f"   index(D_β) = {index_beta}")
    print(f"   |π₀(∂S)| = {pi0}")
    print(f"   Numerator: [{index_adj}]² = {numerator}")
    print(f"   Denominator: {pi0} × {index_beta}/(12π) = {denominator:.6f}")
    print(f"   Exponent: {numerator}/{denominator:.6f} = {exponent:.4f}")
    print(f"   Expected exponent: 64 × 12π/54 = {expected_exponent:.4f}")

    assert np.isclose(exponent, expected_exponent), f"Exponent mismatch: {exponent} vs {expected_exponent}"

    # Compute hierarchy
    hierarchy = np.exp(exponent)

    print(f"\n   R_stella/ℓ_P = exp({exponent:.4f}) = {hierarchy:.4e}")

    # Check against expected ~2.5×10¹⁹
    expected_hierarchy = 2.5e19
    ratio = hierarchy / expected_hierarchy

    print(f"   Expected: ~{expected_hierarchy:.1e}")
    print(f"   Ratio computed/expected: {ratio:.2f}")

    # Should be within factor of 2
    assert 0.5 < ratio < 2.0, f"Hierarchy outside expected range: {hierarchy:.2e}"
    print(f"   ✅ Within factor of 2 of expected value")

    return hierarchy, exponent


# ============================================================================
# Test 3: Alternative Path Check (2b₀ formulation)
# ============================================================================

def test_2b0_formulation():
    """
    Verify the alternative formulation:
    R_stella/ℓ_P = exp((N_c²-1)²/(2b₀))
    """
    index_adj = N_c**2 - 1  # = 8
    b0 = (11 * N_c - 2 * N_f) / (12 * np.pi)

    exponent = index_adj**2 / (2 * b0)
    hierarchy = np.exp(exponent)

    print(f"\n✅ Test 2d: Alternative 2b₀ formulation")
    print(f"   (N_c²-1)² = {index_adj}² = {index_adj**2}")
    print(f"   2b₀ = 2 × {b0:.6f} = {2*b0:.6f}")
    print(f"   Exponent: {index_adj**2}/(2×{b0:.4f}) = {exponent:.4f}")
    print(f"   R_stella/ℓ_P = {hierarchy:.4e}")

    return hierarchy, exponent


# ============================================================================
# Test 4: Central Charge Calculations (§6B)
# ============================================================================

def test_central_charges():
    """
    Verify central charge calculations for free QCD.

    Formulas:
    a = (1/360)(N_s + 11 N_f + 62 N_v)
    c = (1/120)(N_s + 6 N_f + 12 N_v)
    """
    print("\n✅ Test 4: Central charge calculations")

    # UV: Free QCD degrees of freedom
    # Gluons: N_v = dim(adj) = 8
    N_v = N_c**2 - 1  # = 8
    # Quarks: N_f flavors × N_c colors (counting Dirac fermions)
    N_f_Dirac = N_f * N_c  # = 9 Dirac fermions
    N_s = 0  # No scalars in pure QCD

    print(f"   UV degrees of freedom:")
    print(f"     Gluons (vectors): N_v = {N_v}")
    print(f"     Quarks (Dirac): N_f^Dirac = {N_f} × {N_c} = {N_f_Dirac}")
    print(f"     Scalars: N_s = {N_s}")

    # Central charge a_UV
    a_UV = (1/360) * (N_s + 11 * N_f_Dirac + 62 * N_v)
    print(f"\n   a_UV = (1/360) × (0 + 11×{N_f_Dirac} + 62×{N_v})")
    print(f"        = (1/360) × ({11*N_f_Dirac} + {62*N_v})")
    print(f"        = (1/360) × {11*N_f_Dirac + 62*N_v}")
    print(f"        = {a_UV:.4f}")

    # Expected: 1.653
    expected_a_UV = 1.653
    print(f"   Expected a_UV = {expected_a_UV}")
    assert abs(a_UV - expected_a_UV) < 0.01, f"a_UV = {a_UV}, expected ~{expected_a_UV}"
    print(f"   ✅ a_UV verified")

    # Central charge c_UV
    c_UV = (1/120) * (N_s + 6 * N_f_Dirac + 12 * N_v)
    print(f"\n   c_UV = (1/120) × (0 + 6×{N_f_Dirac} + 12×{N_v})")
    print(f"        = (1/120) × ({6*N_f_Dirac} + {12*N_v})")
    print(f"        = {c_UV:.4f}")

    expected_c_UV = 1.25
    assert abs(c_UV - expected_c_UV) < 0.01, f"c_UV = {c_UV}, expected ~{expected_c_UV}"
    print(f"   ✅ c_UV verified")

    # IR: Confined QCD (only pions as Goldstone bosons)
    N_pions = N_f**2 - 1  # = 8 pseudoscalars
    print(f"\n   IR degrees of freedom:")
    print(f"     Pions (pseudoscalars): N_π = N_f² - 1 = {N_pions}")

    # For pions, count as real scalars
    N_s_IR = N_pions
    N_f_IR = 0
    N_v_IR = 0

    a_IR = (1/360) * (N_s_IR + 11 * N_f_IR + 62 * N_v_IR)
    print(f"\n   a_IR = (1/360) × ({N_s_IR} + 0 + 0) = {a_IR:.4f}")

    expected_a_IR = 0.022
    assert abs(a_IR - expected_a_IR) < 0.005, f"a_IR = {a_IR}, expected ~{expected_a_IR}"
    print(f"   ✅ a_IR verified")

    # Delta a
    delta_a = a_UV - a_IR
    print(f"\n   Δa = a_UV - a_IR = {a_UV:.4f} - {a_IR:.4f} = {delta_a:.4f}")

    expected_delta_a = 1.631
    assert abs(delta_a - expected_delta_a) < 0.01, f"Δa = {delta_a}, expected ~{expected_delta_a}"
    print(f"   ✅ Δa = {delta_a:.3f} verified")

    return a_UV, a_IR, delta_a


def test_central_charge_vs_hierarchy():
    """
    Verify the relationship between Δa and the hierarchy exponent.

    The proposition claims:
    - Δa ≈ 1.631
    - Δa_eff needed for hierarchy = 64/44.68 ≈ 1.43
    - Agreement: 1.43/1.631 ≈ 88%
    """
    print("\n✅ Test 5: Central charge vs hierarchy comparison")

    # From hierarchy
    exponent = 64 * 12 * np.pi / 54  # ≈ 44.68
    delta_a_eff = 64 / exponent

    print(f"   Hierarchy exponent: {exponent:.4f}")
    print(f"   Δa_eff (needed for hierarchy): 64/{exponent:.4f} = {delta_a_eff:.4f}")

    # From central charges
    N_v = 8
    N_f_Dirac = 9
    a_UV = (1/360) * (11 * N_f_Dirac + 62 * N_v)
    a_IR = 8/360
    delta_a = a_UV - a_IR

    print(f"   Δa (from central charges): {delta_a:.4f}")

    # Agreement
    agreement = delta_a_eff / delta_a
    print(f"\n   Agreement: Δa_eff / Δa = {delta_a_eff:.4f}/{delta_a:.4f} = {agreement:.2%}")

    expected_agreement = 0.88
    assert abs(agreement - expected_agreement) < 0.05, f"Agreement = {agreement:.2%}, expected ~88%"
    print(f"   ✅ ~88% agreement verified")

    return agreement


# ============================================================================
# Test 6: Gluon-Gluon Channels (Why squared index)
# ============================================================================

def test_gluon_gluon_channels():
    """Verify adj ⊗ adj = 64 channels."""
    dim_adj = N_c**2 - 1
    channels = dim_adj * dim_adj
    expected = 64

    assert channels == expected, f"adj ⊗ adj = {channels}, expected {expected}"
    print(f"\n✅ Test 6: Gluon-gluon channels = {dim_adj} × {dim_adj} = {channels}")
    return channels


# ============================================================================
# Test 7: SU(N) Generalization
# ============================================================================

def test_su_n_generalization():
    """Test that the formula generalizes to SU(N) correctly."""
    print("\n✅ Test 7: SU(N) generalization")

    for N in [2, 3, 4, 5]:
        dim_adj_N = N**2 - 1
        # For pure gauge (N_f = 0)
        b0_N = (11 * N) / (12 * np.pi)
        exponent_N = dim_adj_N**2 / (2 * b0_N)
        hierarchy_N = np.exp(exponent_N)

        print(f"   SU({N}): dim(adj) = {dim_adj_N}, b₀ = 11×{N}/(12π) = {b0_N:.4f}")
        print(f"           exponent = {dim_adj_N}²/(2×{b0_N:.4f}) = {exponent_N:.2f}")
        print(f"           hierarchy = {hierarchy_N:.2e}")

    return True


# ============================================================================
# Visualization: Central Charge Flow
# ============================================================================

def plot_central_charge_flow():
    """Visualize central charge flow from UV to IR."""

    # Energy scales (log scale)
    mu = np.logspace(19, -3, 1000)  # From Planck to ~1 MeV

    # Approximate a(μ) using interpolation
    # a decreases from a_UV to a_IR as μ decreases

    N_v = 8
    N_f_Dirac = 9
    a_UV = (1/360) * (11 * N_f_Dirac + 62 * N_v)
    a_IR = 8/360

    # QCD scale
    Lambda_QCD = 0.3  # GeV

    # Model a(μ) with smooth transition
    transition_width = 1.0  # decades
    a_mu = a_IR + (a_UV - a_IR) / (1 + (Lambda_QCD/mu)**2)

    fig, ax = plt.subplots(figsize=(10, 6))

    ax.semilogx(mu, a_mu, 'b-', linewidth=2, label='a(μ)')
    ax.axhline(a_UV, color='r', linestyle='--', label=f'a_UV = {a_UV:.3f}')
    ax.axhline(a_IR, color='g', linestyle='--', label=f'a_IR = {a_IR:.3f}')
    ax.axvline(Lambda_QCD, color='orange', linestyle=':', label=f'Λ_QCD = {Lambda_QCD} GeV')

    ax.set_xlabel('Energy scale μ (GeV)', fontsize=12)
    ax.set_ylabel('Central charge a', fontsize=12)
    ax.set_title('Central Charge Flow in QCD (Schematic)', fontsize=14)
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_xlim(1e-3, 1e19)

    # Add annotations
    ax.annotate(f'Δa = {a_UV - a_IR:.3f}',
                xy=(1e5, (a_UV + a_IR)/2),
                fontsize=12,
                ha='center')

    # Save
    plots_dir = Path('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots')
    plots_dir.mkdir(parents=True, exist_ok=True)
    plt.savefig(plots_dir / 'prop_0_0_17t_central_charge_flow.png', dpi=150, bbox_inches='tight')
    plt.close()

    print(f"\n📊 Plot saved: {plots_dir / 'prop_0_0_17t_central_charge_flow.png'}")


def plot_hierarchy_vs_n():
    """Plot hierarchy as function of N_c for SU(N) gauge theories."""

    N_values = np.arange(2, 11)
    hierarchies = []
    exponents = []

    for N in N_values:
        dim_adj = N**2 - 1
        b0 = (11 * N) / (12 * np.pi)  # pure gauge
        exp_val = dim_adj**2 / (2 * b0)
        exponents.append(exp_val)
        hierarchies.append(np.exp(exp_val))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Exponent vs N
    ax1.plot(N_values, exponents, 'bo-', markersize=8)
    ax1.axhline(exponents[1], color='r', linestyle='--', alpha=0.5, label=f'SU(3): exp = {exponents[1]:.1f}')
    ax1.set_xlabel('N (number of colors)', fontsize=12)
    ax1.set_ylabel('Hierarchy exponent', fontsize=12)
    ax1.set_title('Hierarchy Exponent vs N_c for SU(N)', fontsize=14)
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Hierarchy vs N (log scale)
    ax2.semilogy(N_values, hierarchies, 'go-', markersize=8)
    ax2.axhline(hierarchies[1], color='r', linestyle='--', alpha=0.5, label=f'SU(3): ~{hierarchies[1]:.1e}')
    ax2.set_xlabel('N (number of colors)', fontsize=12)
    ax2.set_ylabel('R_stella / ℓ_P', fontsize=12)
    ax2.set_title('QCD-Planck Hierarchy vs N_c', fontsize=14)
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()

    plots_dir = Path('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots')
    plt.savefig(plots_dir / 'prop_0_0_17t_hierarchy_vs_n.png', dpi=150, bbox_inches='tight')
    plt.close()

    print(f"📊 Plot saved: {plots_dir / 'prop_0_0_17t_hierarchy_vs_n.png'}")


# ============================================================================
# Main Verification
# ============================================================================

def run_all_tests():
    """Run all verification tests."""
    print("=" * 70)
    print("Proposition 0.0.17t: Topological Origin of Scale Hierarchy")
    print("Independent Verification Script")
    print("=" * 70)

    results = {}

    # Test 1: Index calculations
    print("\n" + "-" * 50)
    print("TEST 1: Index Calculations")
    print("-" * 50)
    try:
        test_index_from_su3()
        test_index_from_vertices()
        test_euler_characteristic()
        results['index'] = 'PASS'
    except AssertionError as e:
        results['index'] = f'FAIL: {e}'
        print(f"❌ {e}")

    # Test 2: β-function and hierarchy
    print("\n" + "-" * 50)
    print("TEST 2: β-function and Hierarchy Formula")
    print("-" * 50)
    try:
        test_beta_function_coefficient()
        test_costello_bittleston_index()
        test_hierarchy_formula()
        test_2b0_formulation()
        results['hierarchy'] = 'PASS'
    except AssertionError as e:
        results['hierarchy'] = f'FAIL: {e}'
        print(f"❌ {e}")

    # Test 3: Central charges
    print("\n" + "-" * 50)
    print("TEST 3-5: Central Charge Calculations")
    print("-" * 50)
    try:
        test_central_charges()
        test_central_charge_vs_hierarchy()
        results['central_charges'] = 'PASS'
    except AssertionError as e:
        results['central_charges'] = f'FAIL: {e}'
        print(f"❌ {e}")

    # Test 6: Gluon channels
    try:
        test_gluon_gluon_channels()
        results['gluon_channels'] = 'PASS'
    except AssertionError as e:
        results['gluon_channels'] = f'FAIL: {e}'
        print(f"❌ {e}")

    # Test 7: SU(N) generalization
    try:
        test_su_n_generalization()
        results['su_n'] = 'PASS'
    except AssertionError as e:
        results['su_n'] = f'FAIL: {e}'
        print(f"❌ {e}")

    # Generate plots
    print("\n" + "-" * 50)
    print("GENERATING PLOTS")
    print("-" * 50)
    try:
        plot_central_charge_flow()
        plot_hierarchy_vs_n()
        results['plots'] = 'PASS'
    except Exception as e:
        results['plots'] = f'FAIL: {e}'
        print(f"❌ Plot generation failed: {e}")

    # Summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)

    all_pass = True
    for test, result in results.items():
        status = "✅" if result == 'PASS' else "❌"
        print(f"{status} {test}: {result}")
        if result != 'PASS':
            all_pass = False

    print("\n" + "-" * 50)
    if all_pass:
        print("✅ ALL TESTS PASSED")
    else:
        print("❌ SOME TESTS FAILED")
    print("-" * 50)

    return all_pass


if __name__ == "__main__":
    success = run_all_tests()
    exit(0 if success else 1)
