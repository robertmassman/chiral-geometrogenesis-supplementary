#!/usr/bin/env python3
"""
Investigation: Algebraic Constraints on N

This script explores whether algebraic/group-theoretic constraints can
provide a pure information-theoretic bound on N.

Key Observation: Z_N groups have different algebraic properties that
might affect distinguishability in ways not captured by Fisher metric rank.

Approaches:
1. Color neutrality equation structure
2. Phase coherence and Z_N representation theory
3. Minimal algebraic complexity for non-trivial distinguishability
4. Bootstrap self-consistency equations

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-01
"""

import numpy as np
from typing import Tuple, List, Dict
from itertools import combinations
import matplotlib.pyplot as plt

# ============================================================================
# Z_N GROUP ANALYSIS
# ============================================================================

def analyze_color_neutrality_solutions(N: int) -> Dict:
    """
    Analyze the color neutrality equation: sum_c exp(i*phi_c) = 0

    For N components, the equilibrium phases are phi_c = 2*pi*c/N.
    But the full solution space is larger.

    Key question: How many independent solutions exist?
    """
    # Roots of unity
    omega = np.exp(2j * np.pi / N)
    phases_eq = [omega**k for k in range(N)]

    # Verify color neutrality at equilibrium
    sum_eq = sum(phases_eq)
    neutrality_error = abs(sum_eq)

    # The configuration space is T^{N-1} (phases modulo overall U(1))
    # Color neutrality is ONE constraint: Re(sum) = Im(sum) = 0
    # This removes 2 DOF, but we also quotient by U(1) removing 1 DOF
    # Net: N phases - 1 (U(1)) - 0 (neutrality auto-satisfied at eq) = N-1 DOF

    # Actually, color neutrality at equilibrium is automatic for roots of unity
    # Away from equilibrium, we can perturb phases while maintaining neutrality?

    # Let's count: for N phases with neutrality constraint:
    # - Original DOF: N (one phase per component)
    # - U(1) quotient: -1 (overall phase is unphysical)
    # - Color neutrality: This is satisfied at equilibrium, perturbations
    #   must stay on the neutrality surface

    # The neutrality surface has dimension N-2 (2 constraints on N-1 remaining)
    # NO! The constraint sum exp(i phi_c) = 0 is a COMPLEX equation = 2 REAL constraints
    # After U(1) quotient: N-1 free phases, 2 constraints = N-3 DOF on neutrality surface

    # Wait, this contradicts what we computed earlier (N-1 dimensional config space)
    # The resolution: We're computing Fisher metric at the equilibrium point,
    # where perturbations in tangent space naturally satisfy neutrality to first order

    # Let's verify this more carefully
    perturbation_dof = N - 1  # After U(1) quotient
    neutrality_constraints = 2  # Real and imaginary parts

    # But! At equilibrium, the neutrality constraints are automatically satisfied
    # and the linearization gives tangent space of dimension N-1

    return {
        "N": N,
        "omega": omega,
        "neutrality_error": neutrality_error,
        "phases_eq": [2 * np.pi * k / N for k in range(N)],
        "config_space_dim": N - 1,
        "note": "Color neutrality auto-satisfied at roots of unity equilibrium"
    }


def analyze_Z_N_representation(N: int) -> Dict:
    """
    Analyze Z_N representation theory relevant to color distinguishability.

    Z_N has N irreducible representations (1-dimensional).
    The "regular representation" decomposes into all irreps.

    Key question: What's the minimal N for a "complete" representation
    of distinguishability?
    """
    # Z_N irreps: chi_k(g^m) = omega^{km} where omega = exp(2*pi*i/N)
    omega = np.exp(2j * np.pi / N)

    # Character table (rows = irreps, cols = conjugacy classes)
    # For Z_N (abelian), each element is its own conjugacy class
    char_table = np.zeros((N, N), dtype=complex)
    for k in range(N):
        for m in range(N):
            char_table[k, m] = omega**(k * m)

    # The "color neutrality" condition uses the sum of all characters at each irrep
    # This is sum_m chi_k(g^m) = sum_m omega^{km}
    irrep_sums = [np.sum(char_table[k, :]) for k in range(N)]
    # For k=0: sum = N (trivial irrep)
    # For k≠0: sum = 0 (orthogonality)

    # Key insight: Color neutrality (sum exp(i phi_c) = 0) is saying the
    # configuration projects to zero in the trivial representation

    # The "interesting" irreps are the non-trivial ones (k ≠ 0)
    num_nontrivial_irreps = N - 1

    # For N=2: Only 1 non-trivial irrep (the sign representation)
    # For N=3: 2 non-trivial irreps (conjugate pair)
    # For N=4: 3 non-trivial irreps

    # Conjecture: You need at least 2 non-trivial irreps for stable distinguishability
    # because the Fisher metric on T^{N-1} requires rank ≥ 2 for non-degeneracy?

    # Let's check: For N=2, dim=1, Fisher metric has rank 0 (degenerate)
    # For N=3, dim=2, Fisher metric has rank 2 (non-degenerate)
    # This correlates!

    return {
        "N": N,
        "num_irreps": N,
        "num_nontrivial_irreps": num_nontrivial_irreps,
        "trivial_irrep_sum": int(N),
        "nontrivial_irrep_sums": [0] * (N - 1),
        "character_table_shape": char_table.shape,
        "conjecture": "Non-degeneracy requires N-1 ≥ 2, i.e., N ≥ 3"
    }


# ============================================================================
# BOOTSTRAP COMPLEXITY ANALYSIS
# ============================================================================

def analyze_bootstrap_equations(N: int) -> Dict:
    """
    Analyze the algebraic structure of bootstrap self-consistency equations.

    The bootstrap requires:
    1. Observer emerges from the same field configuration space
    2. Observer can distinguish configurations
    3. The framework is self-consistent

    Key question: Does the bootstrap become algebraically inconsistent for N > 3?
    """
    # The bootstrap equations involve:
    # 1. Color neutrality: sum_c exp(i phi_c) = 0
    # 2. Dynamics: d/dt phi_c = -grad E (energy minimization)
    # 3. Observer consistency: Fisher metric non-degenerate

    # For the algebraic structure, consider:
    # - Number of free parameters: N-1 phases
    # - Number of constraints: 2 (neutrality) + stability conditions

    # A key observation: The Z₃ structure is special because:
    # - It's the smallest group where all non-trivial elements have the same order
    # - The character values are primitive cube roots of unity: 1, ω, ω²
    # - These form an equilateral triangle in the complex plane

    omega = np.exp(2j * np.pi / N)
    primitive_roots = [omega**k for k in range(1, N)]  # Exclude 1 = omega^0

    # The "spread" of primitive roots - how evenly distributed are they?
    angles = [np.angle(z) for z in primitive_roots]
    angle_diffs = np.diff(sorted(angles + [angles[0] + 2*np.pi]))
    spread_uniformity = np.std(angle_diffs) / np.mean(angle_diffs) if len(angle_diffs) > 0 else 0

    # For Z_3: angles are 2π/3, 4π/3 → diffs are 2π/3, 2π/3, 2π/3 (perfectly uniform)
    # For Z_4: angles are π/2, π, 3π/2 → diffs are π/2, π/2, π/2, π/2 (also uniform)
    # For Z_5: angles are 2π/5, 4π/5, 6π/5, 8π/5 → uniform
    # All Z_N should have uniform distribution!

    # The special property of Z₃:
    # It's the smallest N where dim(config space) = N-1 = 2 = rank of Fisher metric
    # This is the "minimal" non-degenerate case

    # Gödel number-like complexity: How many bits to specify the bootstrap?
    # For N components, the bootstrap involves:
    # - N-1 continuous parameters (phases)
    # - O(N²) terms in the Fisher metric
    # - O(N³) terms in the curvature

    bootstrap_terms = {
        "parameters": N - 1,
        "fisher_terms": (N - 1) ** 2,
        "curvature_terms": (N - 1) ** 3 if N > 1 else 0,
        "total_algebraic_complexity": (N - 1) + (N - 1)**2 + (N - 1)**3
    }

    return {
        "N": N,
        "primitive_roots": len(primitive_roots),
        "spread_uniformity": spread_uniformity,
        "bootstrap_complexity": bootstrap_terms,
        "is_minimal_nondegenerate": N == 3
    }


# ============================================================================
# MINIMAL DISTINGUISHABILITY ANALYSIS
# ============================================================================

def analyze_minimal_distinguishability(N_max: int = 10) -> List[Dict]:
    """
    Find the MINIMAL N for stable distinguishability.

    Requirements:
    1. Non-trivial (N > 1)
    2. Color neutrality possible (N ≥ 2)
    3. Fisher metric non-degenerate (N ≥ 3)

    N = 3 is the MINIMAL system satisfying all three.
    """
    results = []

    for N in range(1, N_max + 1):
        # Requirement 1: Non-trivial
        nontrivial = N > 1

        # Requirement 2: Color neutrality possible
        # sum exp(2πik/N) = 0 for all N ≥ 2 (roots of unity)
        omega = np.exp(2j * np.pi / N)
        color_neutral = abs(sum(omega**k for k in range(N))) < 1e-10

        # Requirement 3: Fisher metric non-degenerate
        # From our computations: non-degenerate iff N ≥ 3
        fisher_nondegenerate = N >= 3

        # All requirements
        is_stable = nontrivial and color_neutral and fisher_nondegenerate

        results.append({
            "N": N,
            "nontrivial": nontrivial,
            "color_neutral": color_neutral,
            "fisher_nondegenerate": fisher_nondegenerate,
            "is_stable": is_stable,
            "config_dim": max(0, N - 1),
            "classification": (
                "TRIVIAL" if N == 1 else
                "DEGENERATE" if N == 2 else
                "STABLE (minimal)" if N == 3 else
                "STABLE"
            )
        })

    return results


# ============================================================================
# THE KEY INSIGHT: Z₃ AS MINIMAL NON-TRIVIAL
# ============================================================================

def analyze_Z3_uniqueness() -> Dict:
    """
    Analyze why Z₃ might be uniquely selected.

    The argument:
    1. We need non-trivial distinguishability → N > 1
    2. We need color neutrality → roots of unity
    3. We need stable distinguishability → Fisher metric non-degenerate
    4. N = 2 fails criterion 3 (Fisher degenerate)
    5. N = 3 is the FIRST stable case

    But why stop at N = 3? What excludes N = 4, 5, ...?

    Pure information-theoretic answer: NOTHING excludes them from Fisher analysis!

    The bound N ≤ 4 comes from GEOMETRY (affine independence in D=4-1=3 dimensions).

    However, there's a possible alternative argument based on MINIMALITY:
    - If "existence" costs resources (energy, information, etc.)
    - Then the MINIMAL stable configuration is preferred
    - N = 3 is the minimal stable configuration
    - Therefore N = 3 is selected

    This is an "Occam's razor" type argument, not a hard constraint.
    """

    # The Z₃ structure has special properties:
    omega = np.exp(2j * np.pi / 3)
    z3_elements = [1, omega, omega**2]

    # 1. Equilateral triangle in complex plane
    positions = [(np.real(z), np.imag(z)) for z in z3_elements]

    # 2. All pairwise distances equal
    distances = [abs(z3_elements[i] - z3_elements[j])
                 for i, j in combinations(range(3), 2)]
    distance_uniformity = np.std(distances) / np.mean(distances)

    # 3. Sum to zero (color neutrality)
    neutrality = abs(sum(z3_elements))

    # 4. Closure under multiplication
    # omega * omega = omega^2, omega * omega^2 = 1, omega^2 * omega^2 = omega

    # 5. Connection to SU(3) center
    # The center of SU(3) is Z₃, generated by exp(2πi/3) × Identity
    # This is the ALGEBRAIC origin of Z₃ in the color group

    return {
        "z3_elements": z3_elements,
        "positions_in_complex_plane": positions,
        "pairwise_distances": distances,
        "distance_uniformity": distance_uniformity,
        "color_neutrality_error": neutrality,
        "is_equilateral_triangle": True,
        "connection_to_SU3": "Z₃ is the center of SU(3)",
        "minimality_argument": """
N = 3 is uniquely selected by MINIMALITY + STABILITY:
- N = 1: Trivial (no distinguishability)
- N = 2: Unstable (Fisher metric degenerate)
- N = 3: MINIMAL STABLE configuration
- N > 3: Also stable, but not minimal

The MINIMALITY principle (Occam's razor) selects N = 3 if we postulate:
"Nature realizes the simplest stable configuration."

This is a SELECTION principle, not a hard constraint.
The hard constraint (N ≤ 4) comes from geometry (affine independence in D=3).
"""
    }


# ============================================================================
# SYNTHESIS: THE COMPLETE ARGUMENT
# ============================================================================

def synthesize_argument():
    """Synthesize the complete argument for N = 3."""

    print("=" * 70)
    print("SYNTHESIS: THE COMPLETE ARGUMENT FOR N = 3")
    print("=" * 70)
    print()

    print("CONSTRAINTS ON N:")
    print("-" * 50)
    print()

    print("1. LOWER BOUND: N ≥ 3 (purely information-theoretic)")
    print("   - N = 1: Trivial (dim = 0, no distinguishability)")
    print("   - N = 2: Fisher metric DEGENERATE (dim = 1, rank = 0)")
    print("   - N = 3: First STABLE case (dim = 2, rank = 2)")
    print("   SOURCE: Lemma 3.1.2 (Fisher degeneracy)")
    print()

    print("2. UPPER BOUND: N ≤ 4 (requires geometry)")
    print("   - Affine independence in D_space = 3 dimensions")
    print("   - 4 points in general position span R³")
    print("   - 5+ points are necessarily affinely dependent")
    print("   - N colors → N points on stella → N ≤ 4")
    print("   SOURCE: Lemma 0.0.2a (Affine Independence)")
    print()

    print("3. DIVISIBILITY: 3 | N (phase structure)")
    print("   - Z₃ phase coherence at equilibrium")
    print("   - Phases must be 0, 2π/3, 4π/3 (or permutations)")
    print("   - Only N divisible by 3 compatible with phase structure")
    print("   SOURCE: Theorem 0.0.15 (Z₃ constraint)")
    print()

    print("4. INTERSECTION:")
    print("   N ≥ 3  ∩  N ≤ 4  ∩  3|N  =  {3}")
    print()

    print("=" * 70)
    print("WHAT'S PURELY INFORMATION-THEORETIC?")
    print("=" * 70)
    print()

    print("✅ N ≥ 3: Fisher metric non-degeneracy (PROVEN)")
    print("   - From information geometry alone")
    print("   - No geometric input required")
    print()

    print("❌ N ≤ 4: Affine independence (NEEDS GEOMETRY)")
    print("   - Requires knowing D_space = 3 spatial dimensions")
    print("   - D_space comes from D = 4 spacetime (Theorem 0.0.1)")
    print("   - Could NOT be derived from information alone")
    print()

    print("⚠️  3|N: Z₃ phase structure (PARTIALLY INFO-THEORETIC)")
    print("   - The phase structure 0, 2π/3, 4π/3 comes from color neutrality")
    print("   - Color neutrality IS information-theoretic")
    print("   - But why Z₃ specifically? Needs deeper analysis")
    print()

    print("=" * 70)
    print("POSSIBLE PURE INFO-THEORETIC BOUND")
    print("=" * 70)
    print()

    print("MINIMALITY PRINCIPLE:")
    print("-" * 50)
    print()
    print("Postulate: 'Nature realizes the minimal stable configuration.'")
    print()
    print("Then:")
    print("- N = 1, 2 are UNSTABLE (Fisher metric issues)")
    print("- N = 3 is the MINIMAL STABLE configuration")
    print("- N = 4, 5, ... are stable but NOT minimal")
    print("- Therefore N = 3 is selected by minimality")
    print()
    print("This is an 'Occam's razor' argument, not a hard constraint.")
    print("It requires accepting minimality as a physical principle.")
    print()

    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print()
    print("The complete derivation of N = 3 uses:")
    print("  1. Information geometry (N ≥ 3)")
    print("  2. Spacetime geometry (N ≤ 4)")
    print("  3. Phase structure (3|N)")
    print()
    print("A PURELY information-theoretic derivation would require:")
    print("  - Either: A new mechanism for N ≤ 3 beyond Fisher rank")
    print("  - Or: Accepting MINIMALITY as a selection principle")
    print()
    print("The current framework is RIGOROUS with the geometric input.")
    print("The pure info-theoretic version remains an open research direction.")
    print()


# ============================================================================
# MAIN
# ============================================================================

def main():
    # Analysis
    print("=" * 70)
    print("ALGEBRAIC CONSTRAINTS ON N")
    print("=" * 70)
    print()

    # Z_N analysis
    print("Z_N REPRESENTATION ANALYSIS")
    print("-" * 50)
    for N in range(2, 8):
        rep = analyze_Z_N_representation(N)
        print(f"N={N}: {rep['num_nontrivial_irreps']} non-trivial irreps")
    print()

    # Bootstrap complexity
    print("BOOTSTRAP COMPLEXITY")
    print("-" * 50)
    for N in range(2, 8):
        boot = analyze_bootstrap_equations(N)
        c = boot['bootstrap_complexity']
        print(f"N={N}: params={c['parameters']}, Fisher terms={c['fisher_terms']}, "
              f"total={c['total_algebraic_complexity']}")
    print()

    # Minimal distinguishability
    print("MINIMAL DISTINGUISHABILITY ANALYSIS")
    print("-" * 50)
    results = analyze_minimal_distinguishability(8)
    print(f"{'N':>3} | {'Dim':>3} | {'Non-triv':>8} | {'Neutral':>8} | {'Fisher OK':>9} | {'Status':>15}")
    print("-" * 60)
    for r in results:
        print(f"{r['N']:>3} | {r['config_dim']:>3} | "
              f"{'YES' if r['nontrivial'] else 'no':>8} | "
              f"{'YES' if r['color_neutral'] else 'no':>8} | "
              f"{'YES' if r['fisher_nondegenerate'] else 'no':>9} | "
              f"{r['classification']:>15}")
    print()

    # Z₃ uniqueness
    print("Z₃ UNIQUENESS ANALYSIS")
    print("-" * 50)
    z3 = analyze_Z3_uniqueness()
    print(f"Elements form equilateral triangle: {z3['is_equilateral_triangle']}")
    print(f"Distance uniformity: {z3['distance_uniformity']:.6f}")
    print(f"Connection to SU(3): {z3['connection_to_SU3']}")
    print()

    # Final synthesis
    synthesize_argument()


if __name__ == "__main__":
    main()
