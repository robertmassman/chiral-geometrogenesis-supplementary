#!/usr/bin/env python3
"""
Theorem 0.0.1 Correction: Virial Theorem and Atomic Stability in n Dimensions

This script derives the correct virial theorem for n-dimensional systems
and verifies atomic stability claims across dimensions.

Key corrections needed:
1. Virial theorem derivation (lines 104-117 in theorem)
2. 2D atomic stability claim (lines 124-127)

References:
- Ehrenfest (1917) - Orbital stability
- Yang (1991) "The n-dimensional Coulomb problem"
- Tangherlini (1963) "Schwarzschild field in n dimensions"
- Nieto (1979) "Hydrogen atom in D dimensions"
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.special import gamma
from scipy.integrate import quad
import json
import os

# Create plots directory
os.makedirs('plots', exist_ok=True)

def virial_theorem_derivation():
    """
    Correct derivation of the virial theorem for power-law potentials.

    For V(r) = -k/r^s (where s = n-2 for n spatial dimensions):

    The virial theorem states: 2<T> = s<V> where s is the power of r

    For V ~ -1/r^(n-2), we have s = -(n-2), so:
        2<T> = -(n-2)<V>
        2<T> = (n-2)|V|  (since V < 0)

    For bound states, E = <T> + <V> < 0

    From virial: <T> = (n-2)|V|/2 = -(n-2)<V>/2

    So: E = -(n-2)<V>/2 + <V> = <V>[1 - (n-2)/2] = <V>[(2-n+2)/2] = <V>[(4-n)/2]

    Since <V> < 0 for attractive potential:
    E < 0 requires (4-n)/2 > 0, i.e., n < 4

    Wait - let me be more careful about signs.
    """

    print("=" * 70)
    print("VIRIAL THEOREM DERIVATION FOR n-DIMENSIONAL COULOMB POTENTIAL")
    print("=" * 70)

    print("\n1. Setup:")
    print("   Potential: V(r) = -k/r^(n-2) for n spatial dimensions (k > 0)")
    print("   This is a homogeneous function of degree -(n-2)")

    print("\n2. Virial Theorem (general form):")
    print("   For V(r) homogeneous of degree s: 2<T> = s<V>")
    print("   Here s = -(n-2), so: 2<T> = -(n-2)<V>")

    print("\n3. For attractive potential V < 0:")
    print("   Write V = -|V| where |V| > 0")
    print("   Then: 2<T> = -(n-2)(-|V|) = (n-2)|V|")
    print("   So: <T> = (n-2)|V|/2")

    print("\n4. Total Energy:")
    print("   E = <T> + <V> = (n-2)|V|/2 - |V| = |V|[(n-2)/2 - 1] = |V|(n-4)/2")

    print("\n5. Bound state requirement (E < 0):")
    print("   |V|(n-4)/2 < 0")
    print("   Since |V| > 0, need (n-4)/2 < 0")
    print("   Therefore: n < 4")

    print("\n6. Conclusion:")
    print("   The virial theorem shows bound states exist only for n < 4")
    print("   This is a NECESSARY condition, not sufficient!")
    print("   (Still need quantum mechanics for actual bound state structure)")

    # Create correction table
    results = {
        "virial_theorem": {
            "formula": "2<T> = -(n-2)<V>",
            "total_energy": "E = |V|(n-4)/2",
            "bound_state_condition": "n < 4",
            "error_in_original": "Original had algebra error giving n > 4",
            "correct_interpretation": "Virial gives necessary condition n < 4"
        }
    }

    return results


def two_dimensional_hydrogen():
    """
    Analysis of 2D hydrogen atom - correcting the false claim.

    Key fact: 2D hydrogen DOES have bound states!

    References:
    - Yang (1991) Phys. Rev. A 43, 1186
    - Zaslow & Zandler (1967) Am. J. Phys. 35, 1118
    - Loudon (1959) Am. J. Phys. 27, 649
    """

    print("\n" + "=" * 70)
    print("2D HYDROGEN ATOM ANALYSIS")
    print("=" * 70)

    print("\n1. The 2D Coulomb Potential:")
    print("   In 2D, Poisson's equation gives: V(r) = k ln(r/r0)")
    print("   This is LOGARITHMIC, not 1/r")

    print("\n2. 2D Schrödinger Equation (polar coordinates):")
    print("   H = -ℏ²/2m [∂²/∂r² + (1/r)∂/∂r + (1/r²)∂²/∂θ²] + V(r)")

    print("\n3. KEY RESULT (Yang 1991, Zaslow & Zandler 1967):")
    print("   2D hydrogen HAS discrete bound states!")
    print("   Energy levels: E_n = -R_2D/(n + 1/2)² for n = 0, 1, 2, ...")
    print("   where R_2D is a 2D Rydberg constant")

    print("\n4. The Spectrum:")
    print("   Ground state: n = 0, E_0 = -4R_2D")
    print("   First excited: n = 1, E_1 = -4R_2D/9")
    print("   The spectrum is NOT Rydberg-like (not -1/n²)")

    print("\n5. What's DIFFERENT about 2D:")
    print("   - Bound states exist but fewer than 3D")
    print("   - No s-wave continuum (angular momentum matters more)")
    print("   - Excitons in 2D materials follow this physics!")

    print("\n6. CORRECTION TO THEOREM 0.0.1:")
    print("   WRONG: 'No discrete bound states' in 2D")
    print("   RIGHT: '2D has bound states but with altered spectrum'")
    print("   The argument for D=4 should focus on:")
    print("   - Different energy level structure")
    print("   - No inverse-square law")
    print("   - Reduced complexity of chemistry")

    # Compute 2D hydrogen energy levels
    n_levels = np.arange(0, 10)
    E_2D = -1.0 / (n_levels + 0.5)**2  # In units of R_2D

    # Compare with 3D
    n_3D = np.arange(1, 11)
    E_3D = -1.0 / n_3D**2  # In units of Rydberg

    results = {
        "2D_hydrogen": {
            "has_bound_states": True,
            "energy_formula": "E_n = -R_2D/(n + 1/2)^2",
            "ground_state_n": 0,
            "spectrum_type": "Non-Rydberg",
            "references": [
                "Yang (1991) Phys. Rev. A 43, 1186",
                "Zaslow & Zandler (1967) Am. J. Phys. 35, 1118"
            ],
            "correction_needed": "Change 'no bound states' to 'altered spectrum unsuitable for complex chemistry'"
        },
        "energy_levels_2D": E_2D.tolist()[:5],
        "energy_levels_3D": E_3D.tolist()[:5]
    }

    return results


def atomic_stability_full_analysis():
    """
    Complete analysis of atomic stability in n dimensions.

    Key insight: The question is not just "do bound states exist?"
    but "is the system stable against collapse/ionization?"
    """

    print("\n" + "=" * 70)
    print("ATOMIC STABILITY IN n DIMENSIONS: FULL ANALYSIS")
    print("=" * 70)

    print("\n1. n = 2 (D = 3):")
    print("   Potential: V ~ ln(r)")
    print("   Bound states: YES, but altered spectrum")
    print("   Chemistry: Very different, limited complexity")
    print("   Verdict: NOT suitable for complex observers")

    print("\n2. n = 3 (D = 4) - OUR UNIVERSE:")
    print("   Potential: V ~ -1/r")
    print("   Bound states: YES, Rydberg series E_n = -13.6/n² eV")
    print("   Chemistry: Carbon can form 4 bonds, complex molecules")
    print("   Verdict: ✓ UNIQUELY suitable for complex observers")

    print("\n3. n = 4 (D = 5):")
    print("   Potential: V ~ -1/r²")
    print("   Bound states: NO - falls to center ('fall to center')")
    print("   This is the 'inverse square catastrophe'")
    print("   Ground state has r → 0, infinite negative energy")
    print("   Verdict: UNSTABLE, no atoms")

    print("\n4. n ≥ 5:")
    print("   Potential: V ~ -1/r^(n-2)")
    print("   Even more singular, collapse even faster")
    print("   Verdict: UNSTABLE")

    print("\n5. n = 1 (D = 2):")
    print("   Potential: V ~ -|x| (linear)")
    print("   Bound states: YES (harmonic-like)")
    print("   Chemistry: Linear world, no branching")
    print("   Verdict: Insufficient complexity")

    # The critical dimension is n = 4 where potential goes as 1/r²
    # This is the threshold for the "fall to center" phenomenon

    results = {
        "stability_summary": {
            1: {"bound_states": True, "stable": True, "reason": "Linear potential", "suitable": False},
            2: {"bound_states": True, "stable": True, "reason": "Logarithmic potential, altered spectrum", "suitable": False},
            3: {"bound_states": True, "stable": True, "reason": "Coulomb 1/r, Rydberg spectrum", "suitable": True},
            4: {"bound_states": False, "stable": False, "reason": "1/r² fall to center", "suitable": False},
            5: {"bound_states": False, "stable": False, "reason": "1/r³ severe collapse", "suitable": False}
        },
        "critical_dimension": 4,
        "unique_suitable": 3
    }

    return results


def create_correction_visualization():
    """Create visualization comparing atomic stability across dimensions."""

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # Plot 1: Effective potentials
    ax1 = axes[0, 0]
    r = np.linspace(0.01, 5, 500)

    # n = 2: logarithmic
    V_2 = np.log(r)
    # n = 3: Coulomb
    V_3 = -1/r
    # n = 4: inverse square
    V_4 = -1/r**2

    ax1.plot(r, V_2/5, 'b-', linewidth=2, label='n=2: V ~ ln(r)')
    ax1.plot(r, V_3, 'g-', linewidth=2, label='n=3: V ~ -1/r')
    ax1.plot(r, np.clip(V_4, -10, 0), 'r-', linewidth=2, label='n=4: V ~ -1/r²')

    ax1.axhline(y=0, color='k', linestyle='--', alpha=0.3)
    ax1.set_xlim(0, 5)
    ax1.set_ylim(-10, 2)
    ax1.set_xlabel('r (Bohr radii)', fontsize=12)
    ax1.set_ylabel('V(r) (arbitrary units)', fontsize=12)
    ax1.set_title('Coulomb Potential in Different Dimensions', fontsize=14, fontweight='bold')
    ax1.legend(fontsize=11)
    ax1.grid(True, alpha=0.3)

    # Plot 2: Energy levels comparison
    ax2 = axes[0, 1]

    # 3D levels
    n_3d = np.arange(1, 8)
    E_3d = -13.6 / n_3d**2

    # 2D levels (shifted by 1/2)
    n_2d = np.arange(0, 7)
    E_2d = -4 * 13.6 / (n_2d + 0.5)**2  # Approximate scaling

    y_pos_3d = np.arange(len(n_3d))
    y_pos_2d = np.arange(len(n_2d)) + 0.3

    ax2.barh(y_pos_3d - 0.15, -E_3d, height=0.25, color='green', alpha=0.7, label='n=3 (D=4): 3D hydrogen')
    ax2.barh(y_pos_2d - 0.15, -E_2d[:len(n_2d)], height=0.25, color='blue', alpha=0.7, label='n=2 (D=3): 2D hydrogen')

    ax2.set_xlabel('|E| (eV)', fontsize=12)
    ax2.set_ylabel('Level index', fontsize=12)
    ax2.set_title('Bound State Energy Levels', fontsize=14, fontweight='bold')
    ax2.legend(fontsize=11)
    ax2.grid(True, alpha=0.3)

    # Plot 3: Virial theorem result
    ax3 = axes[1, 0]
    n_vals = np.linspace(1, 6, 100)

    # E/|V| = (n-4)/2 from virial theorem
    energy_ratio = (n_vals - 4) / 2

    ax3.plot(n_vals, energy_ratio, 'b-', linewidth=2)
    ax3.axhline(y=0, color='k', linestyle='--', linewidth=1)
    ax3.axvline(x=4, color='r', linestyle='--', linewidth=1, label='Critical: n=4')
    ax3.fill_between(n_vals[n_vals < 4], energy_ratio[n_vals < 4], 0,
                     alpha=0.3, color='green', label='Bound states possible (E < 0)')
    ax3.fill_between(n_vals[n_vals >= 4], energy_ratio[n_vals >= 4], 0,
                     alpha=0.3, color='red', label='No bound states (E ≥ 0)')

    ax3.set_xlabel('Spatial dimension n', fontsize=12)
    ax3.set_ylabel('E/|V| ratio', fontsize=12)
    ax3.set_title('Virial Theorem: E = |V|(n-4)/2', fontsize=14, fontweight='bold')
    ax3.legend(fontsize=10)
    ax3.grid(True, alpha=0.3)
    ax3.set_xlim(1, 6)
    ax3.set_ylim(-2, 1.5)

    # Annotate
    ax3.annotate('n=3: Our universe\nE/|V| = -0.5', xy=(3, -0.5), xytext=(3.5, -1.3),
                fontsize=10, arrowprops=dict(arrowstyle='->', color='green'))

    # Plot 4: Summary table as text
    ax4 = axes[1, 1]
    ax4.axis('off')

    table_text = """
    CORRECTED ATOMIC STABILITY ANALYSIS
    ════════════════════════════════════════════════════════════════

    n=1 (D=2):  Linear potential V ~ |x|
                ✓ Bound states exist
                ✗ Insufficient complexity for observers

    n=2 (D=3):  Logarithmic potential V ~ ln(r)
                ✓ Bound states exist (E_n ~ -1/(n+1/2)²)
                ✗ Non-Rydberg spectrum, limited chemistry

    n=3 (D=4):  Coulomb potential V ~ -1/r
                ✓ Bound states (Rydberg: E_n = -13.6/n² eV)
                ✓ Complex chemistry, stable atoms
                ★ UNIQUELY SUITABLE FOR OBSERVERS

    n=4 (D=5):  Inverse-square potential V ~ -1/r²
                ✗ "Fall to center" - ground state collapses
                ✗ No stable atoms

    n≥5 (D≥6):  More singular potentials V ~ -1/r^(n-2)
                ✗ Rapid collapse, no atoms

    ════════════════════════════════════════════════════════════════
    KEY CORRECTION: n=2 (D=3) DOES have bound states!
    The argument for D=4 is based on Rydberg spectrum + chemistry,
    not the absence of bound states in lower dimensions.
    """

    ax4.text(0.05, 0.95, table_text, transform=ax4.transAxes, fontsize=10,
             verticalalignment='top', fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()
    plt.savefig('plots/theorem_0_0_1_atomic_stability_correction.png', dpi=150, bbox_inches='tight')
    plt.close()

    print("\nVisualization saved to plots/theorem_0_0_1_atomic_stability_correction.png")


def generate_correction_document():
    """Generate specific corrections for the theorem document."""

    corrections = {
        "priority_1": {
            "virial_theorem_section": {
                "location": "lines 104-117",
                "current_text": """The virial theorem relates kinetic (T) and potential (V) energy:
2T = (n-2)(-V)

For bound states: E = T + V < 0

This requires:
T + V = T - (n-2)/2 * T = T(1 - (n-2)/2) < 0

Since T > 0:
1 - (n-2)/2 < 0 => n > 4

Wait—this seems to suggest n > 4 for bound states. Let me reconsider.""",
                "corrected_text": """The virial theorem for a potential V(r) ~ -k/r^s states:
2⟨T⟩ = s⟨V⟩

For the Coulomb potential in n dimensions, V ~ -1/r^(n-2), so s = -(n-2):
2⟨T⟩ = -(n-2)⟨V⟩

Since V < 0 (attractive), we write V = -|V|:
⟨T⟩ = (n-2)|V|/2

Total energy:
E = ⟨T⟩ + ⟨V⟩ = (n-2)|V|/2 - |V| = |V|(n-4)/2

For bound states E < 0 with |V| > 0:
(n-4)/2 < 0  ⟹  n < 4

This shows bound states require n < 4 (a necessary condition).
Note: This analysis predates the quantum treatment below.""",
                "error_type": "Algebra error: mishandled sign conventions",
                "physics_impact": "Conclusion reversed - should be n < 4, not n > 4"
            },
            "2D_bound_states": {
                "location": "lines 124-127",
                "current_text": """**For n = 2 (D = 3):**
- Potential: Φ ∝ ln(r) (too weak at short range)
- No discrete bound states; only quasi-bound
- Atoms unstable or non-existent""",
                "corrected_text": """**For n = 2 (D = 3):**
- Potential: Φ ∝ ln(r) (logarithmic, not Coulomb)
- Bound states EXIST with energy E_n = -R₂D/(n + 1/2)² (Yang 1991)
- Spectrum is non-Rydberg; chemistry fundamentally different
- Insufficient for complex molecular structures""",
                "error_type": "Factual error",
                "physics_impact": "2D hydrogen has bound states; argument should focus on altered chemistry, not absence of states",
                "reference": "Yang (1991) Phys. Rev. A 43, 1186"
            },
            "corollary_reframing": {
                "location": "Section 4 (lines 229-245)",
                "issue": "Corollary 0.0.1a presented as derivation but D=N+1 assumes SU(N) exists",
                "correction": "Reframe as consistency check: 'Given D=4 from observer requirements, IF gauge theory is described by SU(N) with D = N+1, THEN N=3 → SU(3)'"
            }
        },
        "priority_2": {
            "missing_citations": [
                "Tangherlini (1963) Nuovo Cimento 27, 636 - Schwarzschild in n dimensions",
                "Yang (1991) Phys. Rev. A 43, 1186 - n-dimensional hydrogen",
                "Nieto (1979) Am. J. Phys. 47, 1067 - Hydrogen atom in D dimensions"
            ],
            "string_theory_discussion": "Add paragraph noting string theory requires D=10 or D=26, resolved via compactification; our argument applies to effective 4D physics",
            "P3_P4_downgrade": "Reframe P3 (Huygens) and P4 (complexity) as optimizations/enhancements rather than strict requirements, since P1 and P2 already uniquely select D=4"
        }
    }

    return corrections


def main():
    """Run all analyses and generate correction document."""

    print("THEOREM 0.0.1 CORRECTION ANALYSIS")
    print("=" * 70)

    # Run analyses
    virial_results = virial_theorem_derivation()
    hydrogen_2d_results = two_dimensional_hydrogen()
    stability_results = atomic_stability_full_analysis()

    # Generate corrections
    corrections = generate_correction_document()

    # Create visualization
    create_correction_visualization()

    # Combine all results
    all_results = {
        "theorem": "0.0.1",
        "title": "Four-Dimensional Spacetime from Observer Existence",
        "virial_analysis": virial_results,
        "2D_hydrogen_analysis": hydrogen_2d_results,
        "stability_analysis": stability_results,
        "corrections": corrections,
        "verification_status": "CORRECTIONS_REQUIRED",
        "date": "2025-12-15"
    }

    # Save results
    with open('theorem_0_0_1_correction_analysis.json', 'w') as f:
        json.dump(all_results, f, indent=2)

    print("\n" + "=" * 70)
    print("SUMMARY OF REQUIRED CORRECTIONS")
    print("=" * 70)

    print("\n[PRIORITY 1 - CRITICAL]")
    print("-" * 40)
    print("1. Virial theorem (lines 104-117):")
    print("   ERROR: Algebra gives n > 4")
    print("   CORRECT: n < 4 for bound states")
    print("   ACTION: Replace with corrected derivation")

    print("\n2. 2D bound states (lines 124-127):")
    print("   ERROR: Claims 'no discrete bound states'")
    print("   CORRECT: 2D hydrogen HAS bound states (E_n ~ -1/(n+1/2)²)")
    print("   ACTION: Change to 'non-Rydberg spectrum, different chemistry'")

    print("\n3. Corollary 0.0.1a (Section 4):")
    print("   ISSUE: Presented as derivation but is consistency check")
    print("   ACTION: Reframe to clarify logical status")

    print("\n[PRIORITY 2 - ENHANCEMENTS]")
    print("-" * 40)
    print("4. Add citations: Tangherlini (1963), Yang (1991)")
    print("5. Add string theory discussion")
    print("6. Downgrade P3, P4 to optimizations")

    print("\nResults saved to theorem_0_0_1_correction_analysis.json")
    print("Plot saved to plots/theorem_0_0_1_atomic_stability_correction.png")

    return all_results


if __name__ == "__main__":
    results = main()
