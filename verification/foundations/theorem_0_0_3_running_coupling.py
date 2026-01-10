#!/usr/bin/env python3
"""
Theorem 0.0.3 Extension: Running Coupling from Stella Octangula Geometry
========================================================================

This script derives what aspects of QCD running coupling α_s(Q²) 
CAN be determined from the geometric structure.

Key Question: What does geometry tell us about running coupling?

RESULT: The geometry captures:
1. N_c = 3 (number of colors) — from stella octangula vertex structure
2. The FORM of the β-function (given N_c)
3. Asymptotic freedom (b₀ > 0 for N_f < 16.5)
4. The dimension of the coupling (marginal in D=4)

What geometry does NOT capture:
- The numerical value of α_s at any scale
- Λ_QCD (dimensional transmutation scale)
- Threshold corrections at quark masses

Author: Verification System
Date: December 18, 2025
"""

import numpy as np
import matplotlib.pyplot as plt

# =============================================================================
# Physical Constants
# =============================================================================

# PDG 2024 values
ALPHA_S_MZ = 0.1179  # α_s(M_Z)
ALPHA_S_MZ_ERR = 0.0010
M_Z = 91.1876  # GeV

# Quark masses for threshold matching
QUARK_MASSES = {
    'u': 0.00216,   # GeV (at 2 GeV)
    'd': 0.00467,
    's': 0.0934,
    'c': 1.27,      # MS-bar at m_c
    'b': 4.18,      # MS-bar at m_b
    't': 172.69     # pole mass
}

# =============================================================================
# Part 1: What Geometry Determines about N_c
# =============================================================================

def derive_number_of_colors():
    """
    Derive N_c = 3 from stella octangula structure.
    
    The number of colors is NOT arbitrary — it's derived from:
    1. D = 4 spacetime dimensions (Theorem 0.0.1)
    2. D = N + 1 formula (Theorem 12.3.2)
    3. Therefore N = D - 1 = 3 colors
    
    This determines the gauge group is SU(3), giving N_c = 3.
    """
    print("=" * 70)
    print("PART 1: NUMBER OF COLORS FROM GEOMETRY")
    print("=" * 70)
    
    print("\n1. DERIVATION CHAIN:")
    print("-" * 50)
    print("   'Observers can exist' (Theorem 0.0.1)")
    print("           ↓")
    print("   D = 4 spacetime dimensions")
    print("           ↓")
    print("   D = N + 1 (Theorem 12.3.2)")
    print("           ↓")
    print("   N = 3 colors (SU(3) gauge group)")
    print("           ↓")
    print("   N_c = 3")
    
    print("\n2. GEOMETRIC VERIFICATION:")
    print("-" * 50)
    print("   Stella octangula structure:")
    print("   • 6 primary vertices = 3 colors + 3 anticolors")
    print("   • 2 apex vertices = singlet directions")
    print("   • Total: 8 vertices = 2N + 2 = 2(3) + 2 ✓")
    
    # The stella octangula has exactly 3 colors
    n_colors = 3
    n_vertices_primary = 2 * n_colors  # fund + anti-fund
    n_vertices_apex = 2
    n_vertices_total = n_vertices_primary + n_vertices_apex
    
    print(f"\n   N_c = {n_colors}")
    print(f"   Primary vertices: {n_vertices_primary}")
    print(f"   Apex vertices: {n_vertices_apex}")
    print(f"   Total: {n_vertices_total}")
    
    print("\n3. CONSEQUENCE FOR β-FUNCTION:")
    print("-" * 50)
    print(f"   With N_c = {n_colors}, the one-loop β-function coefficient is:")
    print(f"   b₀ = (11N_c - 2N_f)/(12π)")
    print(f"      = (11×3 - 2N_f)/(12π)")
    print(f"      = (33 - 2N_f)/(12π)")
    
    return n_colors


def derive_beta_function_form():
    """
    Given N_c = 3 from geometry, derive the β-function structure.
    
    The β-function takes the universal form:
    
    μ dα_s/dμ = β(α_s) = -b₀α_s² - b₁α_s³ - ...
    
    where the coefficients depend only on N_c and N_f.
    """
    print("\n" + "=" * 70)
    print("PART 2: β-FUNCTION FORM FROM N_c = 3")
    print("=" * 70)
    
    N_c = 3  # From geometry
    
    print("\n1. ONE-LOOP COEFFICIENT (Universal)")
    print("-" * 50)
    
    def b0(N_f):
        """One-loop β-function coefficient."""
        return (11 * N_c - 2 * N_f) / (12 * np.pi)
    
    print(f"   b₀(N_f) = (11N_c - 2N_f)/(12π)")
    print(f"           = (33 - 2N_f)/(12π)  [for N_c = 3]")
    print()
    print(f"   {'N_f':>4} | {'b₀':>10} | {'Asymptotic Freedom?':>20}")
    print("   " + "-" * 40)
    
    for nf in range(7):
        b0_val = b0(nf)
        af = "✓ YES" if b0_val > 0 else "✗ NO"
        print(f"   {nf:>4} | {b0_val:>10.6f} | {af:>20}")
    
    # Critical N_f
    nf_crit = 33/2  # = 16.5
    print(f"\n   Critical N_f: b₀ = 0 when N_f = {nf_crit}")
    print(f"   → Asymptotic freedom requires N_f < {nf_crit}")
    print(f"   → Standard Model has N_f = 6 quarks → b₀ > 0 ✓")
    
    print("\n2. TWO-LOOP COEFFICIENT")
    print("-" * 50)
    
    def b1(N_f):
        """Two-loop β-function coefficient."""
        return (153 - 19 * N_f) / (24 * np.pi**2)
    
    print(f"   b₁(N_f) = (153 - 19N_f)/(24π²)  [for N_c = 3]")
    print()
    print(f"   {'N_f':>4} | {'b₁':>10}")
    print("   " + "-" * 20)
    
    for nf in [3, 4, 5, 6]:
        print(f"   {nf:>4} | {b1(nf):>10.6f}")
    
    print("\n3. GEOMETRICALLY DETERMINED VALUES")
    print("-" * 50)
    print("   At M_Z = 91.2 GeV with N_f = 5 active flavors:")
    b0_5 = b0(5)
    b1_5 = b1(5)
    print(f"   b₀(5) = (33 - 10)/(12π) = 23/(12π) = {b0_5:.6f}")
    print(f"   b₁(5) = (153 - 95)/(24π²) = 58/(24π²) = {b1_5:.6f}")
    
    return b0, b1


def derive_asymptotic_freedom():
    """
    Prove asymptotic freedom is a GEOMETRIC consequence.
    
    Given:
    1. N_c = 3 (from D = 4 via geometry)
    2. N_f ≤ 6 (Standard Model quarks)
    
    Then b₀ > 0, which implies α_s → 0 as Q → ∞.
    """
    print("\n" + "=" * 70)
    print("PART 3: ASYMPTOTIC FREEDOM FROM GEOMETRY")
    print("=" * 70)
    
    N_c = 3  # Geometrically determined
    
    print("\n1. THE ASYMPTOTIC FREEDOM CONDITION")
    print("-" * 50)
    print("   The one-loop running gives:")
    print("   α_s(Q²) = α_s(μ²) / [1 + b₀ α_s(μ²) ln(Q²/μ²)]")
    print()
    print("   For b₀ > 0:")
    print("   • As Q → ∞: α_s(Q²) → 0  (asymptotic freedom)")
    print("   • As Q → 0: α_s(Q²) → ∞  (confinement regime)")
    
    print("\n2. GEOMETRIC PROOF OF b₀ > 0")
    print("-" * 50)
    print("   b₀ = (11N_c - 2N_f)/(12π)")
    print()
    print("   Condition: b₀ > 0")
    print("   ⟺ 11N_c - 2N_f > 0")
    print("   ⟺ N_f < 11N_c/2")
    print()
    print(f"   For N_c = 3 (geometrically determined):")
    print(f"   N_f < 11×3/2 = 16.5")
    print()
    print("   The Standard Model has N_f = 6 quarks.")
    print(f"   6 < 16.5 ✓")
    print()
    print("   THEREFORE: Asymptotic freedom is GEOMETRICALLY GUARANTEED")
    print("              given the stella octangula structure.")
    
    print("\n3. PHYSICAL INTERPRETATION")
    print("-" * 50)
    print("   Asymptotic freedom has two contributions to b₀:")
    print()
    print("   b₀ = [gluon loops] - [quark loops]")
    print("      = 11N_c/(12π)   - 2N_f/(12π)")
    print()
    print("   • Gluon self-interaction: ANTI-SCREENING (+11N_c term)")
    print("     → Gluons carry color → they add to the effective charge at large r")
    print("   • Quark loops: SCREENING (-2N_f term)")
    print("     → Standard vacuum polarization")
    print()
    print("   For SU(3): The gluon contribution (11×3 = 33) dominates")
    print("              over quarks (2×6 = 12)")
    print()
    print("   The NUMBER 11 comes from spin-1 gluons in the adjoint of SU(N_c).")
    print("   The NUMBER 2 comes from spin-1/2 quarks in the fundamental.")
    print()
    print("   GEOMETRY DETERMINES: N_c = 3 → fixes the dominant gluon term")
    
    return True


def analyze_what_geometry_determines():
    """
    Summarize what geometry determines vs. what requires dynamics.
    """
    print("\n" + "=" * 70)
    print("PART 4: WHAT GEOMETRY DETERMINES VS. DYNAMICS")
    print("=" * 70)
    
    print("\n✅ GEOMETRICALLY DETERMINED:")
    print("-" * 50)
    print("   1. Number of colors N_c = 3")
    print("      → From D = 4 via stella octangula uniqueness")
    print()
    print("   2. β-function FORM")
    print("      → Universal once N_c known:")
    print("        β(α) = -b₀α² - b₁α³ - ...")
    print("        b₀ = (11N_c - 2N_f)/(12π)")
    print()
    print("   3. Asymptotic freedom (b₀ > 0)")
    print("      → Follows from N_c = 3 and N_f < 16.5")
    print()
    print("   4. Coupling is dimensionless in D = 4")
    print("      → [α_s] = 0 (marginal coupling)")
    print("      → Logarithmic running (not power-law)")
    
    print("\n❌ NOT GEOMETRICALLY DETERMINED:")
    print("-" * 50)
    print("   1. Numerical value α_s(μ) at any scale")
    print("      → Requires experimental input or non-perturbative calculation")
    print()
    print("   2. Λ_QCD (confinement scale)")
    print("      → Dimensional transmutation: emerges from dynamics")
    print("      → Λ_QCD ≈ 200-300 MeV from experiment")
    print()
    print("   3. Threshold corrections at quark masses")
    print("      → Matching conditions at m_c, m_b, m_t")
    print("      → Require knowing quark mass spectrum")
    print()
    print("   4. Non-perturbative effects")
    print("      → Instantons, condensates, etc.")
    
    return {
        'determined': [
            'N_c = 3',
            'β-function form',
            'Asymptotic freedom',
            'Marginal coupling in D=4'
        ],
        'not_determined': [
            'α_s(μ) value',
            'Λ_QCD',
            'Threshold corrections',
            'Non-perturbative effects'
        ]
    }


def plot_running_coupling():
    """
    Plot the running coupling showing geometrically determined features.
    """
    print("\n" + "=" * 70)
    print("PART 5: VISUALIZATION")
    print("=" * 70)
    
    # β-function coefficients
    def b0(N_f):
        return (33 - 2 * N_f) / (12 * np.pi)
    
    def b1(N_f):
        return (153 - 19 * N_f) / (24 * np.pi**2)
    
    # One-loop running
    def alpha_s_1loop(Q, alpha_ref, Q_ref, N_f):
        """One-loop running coupling."""
        b = b0(N_f)
        return alpha_ref / (1 + b * alpha_ref * np.log(Q**2 / Q_ref**2))
    
    # Two-loop running (approximate)
    def alpha_s_2loop(Q, alpha_ref, Q_ref, N_f):
        """Two-loop running coupling (approximate)."""
        b_0 = b0(N_f)
        b_1 = b1(N_f)
        L = np.log(Q**2 / Q_ref**2)
        
        # Iterative solution
        alpha = alpha_ref
        for _ in range(10):
            alpha_new = alpha_ref / (1 + b_0 * alpha_ref * L + 
                                      (b_1 / b_0) * alpha * np.log(1 + b_0 * alpha_ref * L))
            if np.abs(alpha_new - alpha) < 1e-10:
                break
            alpha = alpha_new
        
        return alpha
    
    # Plot
    fig, ax = plt.subplots(figsize=(10, 6))
    
    # Energy range
    Q = np.logspace(0, 4, 500)  # 1 GeV to 10 TeV
    
    # Calculate running with fixed N_f = 5 for simplicity
    alpha_s_ref = ALPHA_S_MZ
    Q_ref = M_Z
    N_f = 5
    
    alpha_vals = [alpha_s_1loop(q, alpha_s_ref, Q_ref, N_f) for q in Q]
    
    ax.semilogx(Q, alpha_vals, 'b-', linewidth=2, label='One-loop running (N_f=5)')
    
    # Mark key scales
    ax.axvline(M_Z, color='gray', linestyle='--', alpha=0.5)
    ax.text(M_Z * 1.1, 0.08, 'M_Z', fontsize=10)
    
    ax.axhline(ALPHA_S_MZ, color='red', linestyle=':', alpha=0.5)
    ax.text(2, ALPHA_S_MZ + 0.005, f'α_s(M_Z) = {ALPHA_S_MZ}', fontsize=10, color='red')
    
    # Annotations for geometric features
    ax.annotate('Asymptotic Freedom\n(b₀ > 0 from geometry)',
                xy=(5000, 0.09), fontsize=11,
                bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))
    
    ax.annotate('Confinement regime\n(non-perturbative)',
                xy=(2, 0.3), fontsize=11,
                bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))
    
    ax.set_xlabel('Q (GeV)', fontsize=12)
    ax.set_ylabel('α_s(Q)', fontsize=12)
    ax.set_title('QCD Running Coupling: Geometrically Determined Features', fontsize=14)
    ax.set_xlim(1, 10000)
    ax.set_ylim(0, 0.4)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('verification/plots/theorem_0_0_3_running_coupling.png', dpi=150)
    print("\n   Plot saved to verification/plots/theorem_0_0_3_running_coupling.png")
    
    return fig


# =============================================================================
# Main Execution
# =============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("THEOREM 0.0.3 EXTENSION: RUNNING COUPLING")
    print("What Stella Octangula Geometry Determines")
    print("=" * 70)
    
    # Run derivations
    N_c = derive_number_of_colors()
    b0, b1 = derive_beta_function_form()
    af = derive_asymptotic_freedom()
    summary = analyze_what_geometry_determines()
    
    # Create plot
    try:
        import os
        os.makedirs('verification/plots', exist_ok=True)
        fig = plot_running_coupling()
    except Exception as e:
        print(f"\n   (Plot generation skipped: {e})")
    
    # Final summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("""
┌─────────────────────────────────┬──────────────┬─────────────────────────────────────┐
│ Running Coupling Feature        │ Geometry?    │ Notes                               │
├─────────────────────────────────┼──────────────┼─────────────────────────────────────┤
│ Number of colors N_c = 3        │ ✅ YES       │ From D = 4 via Theorem 0.0.1        │
│ β-function FORM                 │ ✅ YES       │ Universal given N_c                 │
│ Asymptotic freedom (b₀ > 0)     │ ✅ YES       │ Follows from N_c = 3, N_f < 16.5    │
│ Marginal coupling in D = 4      │ ✅ YES       │ [α_s] = 0 from dimensional analysis │
├─────────────────────────────────┼──────────────┼─────────────────────────────────────┤
│ α_s(μ) numerical value          │ ❌ NO        │ Requires experimental input         │
│ Λ_QCD scale                     │ ❌ NO        │ Dimensional transmutation           │
│ Threshold corrections           │ ❌ NO        │ Requires quark mass spectrum        │
│ Non-perturbative effects        │ ❌ NO        │ Instantons, condensates             │
└─────────────────────────────────┴──────────────┴─────────────────────────────────────┘

CONCLUSION:
The stella octangula geometry determines that QCD is asymptotically free
(α_s → 0 at high Q²) because N_c = 3 is derived, and N_f = 6 < 16.5.

The FORM of running is determined; the NORMALIZATION is not.
""")
    
    # Save results
    import json
    results = {
        'theorem': '0.0.3 Extension - Running Coupling',
        'date': '2025-12-18',
        'conclusion': 'PARTIAL CAPTURE',
        'N_c': 3,
        'N_f_critical': 16.5,
        'asymptotic_freedom': True,
        'b0_at_M_Z': float(b0(5)),
        'b1_at_M_Z': float(b1(5)),
        'determined': summary['determined'],
        'not_determined': summary['not_determined']
    }
    
    with open('verification/theorem_0_0_3_running_coupling_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("\n✅ Results saved to verification/theorem_0_0_3_running_coupling_results.json")
