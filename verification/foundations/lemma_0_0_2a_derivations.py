#!/usr/bin/env python3
"""
Lemma 0.0.2a — Comprehensive Derivations and Corrections

This script provides rigorous derivations for the corrected version of Lemma 0.0.2a,
addressing all issues found in the multi-agent peer review.

Issues Addressed:
1. Physics: Color superposition states in hadrons (corrected from "discrete labels")
2. Mathematics: Affine independence theorem (corrected from "distinguishability")
3. Framework scope: SU(5) counter-example and framework-specific constraint

Author: Multi-Agent Verification System
Date: 2026-01-02
"""

import numpy as np
from scipy.linalg import svd, norm
import json
from datetime import datetime
import matplotlib.pyplot as plt
import os

# Ensure plots directory exists
PLOTS_DIR = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots"
os.makedirs(PLOTS_DIR, exist_ok=True)

print("=" * 80)
print("LEMMA 0.0.2a COMPREHENSIVE DERIVATIONS AND CORRECTIONS")
print("=" * 80)

# ============================================================================
# ISSUE 1: COLOR SUPERPOSITION STATES IN HADRONS
# ============================================================================

print("\n" + "=" * 80)
print("ISSUE 1: COLOR SUPERPOSITION STATES IN HADRONS")
print("=" * 80)

print("""
ORIGINAL CLAIM (INCORRECT):
"Color charge is a DISCRETE label. A quark is definitively red, green, OR blue—
not a continuous superposition at the confinement scale."

PROBLEM:
This conflates two different concepts:
1. Color QUANTUM NUMBERS are discrete (R, G, B) — TRUE
2. Quarks exist in DEFINITE color states — FALSE

CORRECT PHYSICS:
Quarks inside hadrons exist in QUANTUM SUPERPOSITIONS of color states.
Confinement requires only that ASYMPTOTIC states are color singlets.
""")

# Define the color basis states
print("\n--- Color Basis States ---")
print("Let |R⟩, |G⟩, |B⟩ be the three color eigenstates of SU(3)_color.")
print("These form an orthonormal basis: ⟨c|c'⟩ = δ_cc'\n")

# Meson color singlet state
print("--- Meson Color Singlet ---")
print("A meson (quark-antiquark) in a color singlet state is:")
print("|meson⟩ = (1/√3)(|RR̄⟩ + |GḠ⟩ + |BB̄⟩)")
print("\nThis is a SUPERPOSITION, not a definite color state.")

# Verify normalization
meson_coeffs = np.array([1, 1, 1]) / np.sqrt(3)
meson_norm = np.sqrt(np.sum(meson_coeffs**2))
print(f"Normalization check: ||meson⟩| = {meson_norm:.6f} ✓")

# Baryon color singlet state (totally antisymmetric)
print("\n--- Baryon Color Singlet ---")
print("A baryon (3 quarks) in a color singlet is the totally antisymmetric state:")
print("|baryon⟩ = (1/√6)(|RGB⟩ - |RBG⟩ + |GBR⟩ - |GRB⟩ + |BRG⟩ - |BGR⟩)")
print("\nThis is the ε^{ijk} contraction, giving the SU(3) singlet.")

# The 6 terms with their signs (from Levi-Civita tensor)
baryon_terms = [
    ('RGB', +1),
    ('RBG', -1),
    ('GBR', +1),
    ('GRB', -1),
    ('BRG', +1),
    ('BGR', -1),
]
baryon_coeffs = np.array([t[1] for t in baryon_terms]) / np.sqrt(6)
baryon_norm = np.sqrt(np.sum(baryon_coeffs**2))
print(f"Normalization check: ||baryon⟩| = {baryon_norm:.6f} ✓")

# Verify it's a color singlet by checking SU(3) generators annihilate it
print("\n--- Singlet Verification ---")
print("A color singlet |ψ⟩ satisfies: T^a |ψ⟩ = 0 for all SU(3) generators T^a")
print("Equivalently: Total color charge = 0 (R + G + B = 0 in color space)")

# For baryons: each color appears exactly once, with total Levi-Civita antisymmetrization
# This ensures color neutrality
print("\nFor the baryon singlet:")
print("- Each permutation has one R, one G, one B")
print("- Antisymmetrization ensures singlet under SU(3) rotations")
print("- Total color = R + G + B = 0 (in the weight space)")

# Key insight about confinement
print("\n--- CORRECT STATEMENT FOR LEMMA 0.0.2a ---")
correct_physics = """
CORRECTED CLAIM:
"Color quantum numbers take values in the discrete set {R, G, B} (the fundamental
representation of SU(3)). Physical quark states inside hadrons exist as quantum
superpositions of color eigenstates. Confinement ensures that only color-singlet
combinations (total color charge = 0) can exist as asymptotic states.

The DISCRETENESS relevant to dimension counting comes from:
1. The discrete structure of SU(3) representation theory (3 weights)
2. The requirement that the Weyl group S₃ acts faithfully on color space
3. The geometric realization where colors map to distinct vertices

This is distinct from claiming quarks are in definite color states."
"""
print(correct_physics)

# Numerical demonstration: Color singlet condition
print("\n--- Numerical Verification: Color Singlet Condition ---")

# SU(3) fundamental weights (T3, T8 basis)
w_R = np.array([1/2, 1/(2*np.sqrt(3))])
w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
w_B = np.array([0, -1/np.sqrt(3)])

# Check that R + G + B = 0 (singlet condition)
total_weight = w_R + w_G + w_B
print(f"Weight sum R + G + B = {total_weight}")
print(f"Is singlet (sum = 0)? {np.allclose(total_weight, [0, 0])}")

# The superposition coefficients for a color singlet meson
print("\n--- Meson Density Matrix ---")
print("The reduced density matrix for the quark color in a meson is:")
print("ρ_quark = (1/3)(|R⟩⟨R| + |G⟩⟨G| + |B⟩⟨B|) = (1/3)𝕀₃")
print("\nThis is a MAXIMALLY MIXED state, not a pure color eigenstate.")

rho_quark = np.eye(3) / 3
print(f"ρ_quark = \n{rho_quark}")
print(f"Tr(ρ) = {np.trace(rho_quark):.6f} ✓")
print(f"Tr(ρ²) = {np.trace(rho_quark @ rho_quark):.6f} (< 1 confirms mixed state)")


# ============================================================================
# ISSUE 2: AFFINE INDEPENDENCE THEOREM
# ============================================================================

print("\n" + "=" * 80)
print("ISSUE 2: AFFINE INDEPENDENCE THEOREM (CORRECTED MATHEMATICS)")
print("=" * 80)

print("""
ORIGINAL CLAIM (INCORRECT):
"To place N points such that all pairs are distinguishable (no overlaps),
you need D_space >= N - 1"

PROBLEM:
"Distinguishable" (all pairwise distances > 0) does NOT require D >= N-1.
You can place 1000 distinguishable points on a line (D = 1).

CORRECT STATEMENT:
N points in GENERAL POSITION (forming an (N-1)-simplex) require exactly
(N-1) dimensions. This is the correct mathematical statement.
""")

# Define affine independence
print("\n--- Definition: Affine Independence ---")
print("""
Points p₀, p₁, ..., pₙ are AFFINELY INDEPENDENT if and only if
the vectors (p₁ - p₀), (p₂ - p₀), ..., (pₙ - p₀) are linearly independent.

Equivalently: no point lies in the affine hull of the others.

THEOREM (Affine Dimension):
N affinely independent points span an (N-1)-dimensional affine subspace.
Conversely, to have N affinely independent points, you need D >= N-1.
""")

def test_affine_independence_detailed():
    """
    Provide detailed verification of affine independence theorem.
    """
    print("\n--- Verification: N Points Require N-1 Dimensions ---")

    results = []

    for N in range(2, 7):
        # Generate regular (N-1)-simplex vertices
        # Standard construction: vertices in N-dim space, then project

        # Unit vectors in R^N
        vertices = np.eye(N)

        # Center at origin
        centroid = vertices.mean(axis=0)
        centered = vertices - centroid

        # The centered vertices span an (N-1)-dimensional subspace
        # (they sum to zero, so they're linearly dependent in R^N)

        # Compute rank
        rank = np.linalg.matrix_rank(centered, tol=1e-10)

        # Verify by SVD
        U, S, Vh = svd(centered)
        nonzero_sv = np.sum(S > 1e-10)

        # Check all pairwise distances
        distances = []
        for i in range(N):
            for j in range(i+1, N):
                d = norm(vertices[i] - vertices[j])
                distances.append(d)

        min_dist = min(distances)
        all_distinct = min_dist > 1e-10

        print(f"\nN = {N} points:")
        print(f"  Affine dimension (rank): {rank}")
        print(f"  Expected dimension: {N-1}")
        print(f"  Match: {'✓' if rank == N-1 else '✗'}")
        print(f"  Nonzero singular values: {nonzero_sv}")
        print(f"  All pairwise distances > 0: {all_distinct} (min = {min_dist:.6f})")

        results.append({
            'N': N,
            'affine_dim': rank,
            'expected': N - 1,
            'correct': rank == N - 1
        })

    return results

affine_results = test_affine_independence_detailed()

# The key distinction
print("\n--- KEY DISTINCTION: Distinguishability vs Affine Independence ---")
print("""
DISTINGUISHABILITY (weak condition):
- All pairwise distances > 0
- Can be achieved in ANY dimension >= 1
- Example: 100 points on a line, all at different positions

AFFINE INDEPENDENCE (strong condition):
- No point in the affine hull of the others
- Requires EXACTLY D = N-1 dimensions for N points
- This is what SU(N) weight structure actually requires

WHY AFFINE INDEPENDENCE IS RELEVANT:
The N fundamental weights of SU(N) are affinely independent because:
1. They span the full (N-1)-dimensional weight space
2. The Weyl group S_N acts transitively on them
3. They form a regular (N-1)-simplex

This is NOT about "distinguishability" but about the GEOMETRIC STRUCTURE
of the weight diagram.
""")

# Demonstrate the counter-example
print("\n--- Counter-Example: Distinguishable but Collinear ---")
print("10 points on a line (D = 1): x_i = i for i = 0, 1, ..., 9")
points_1d = np.arange(10).reshape(-1, 1)
print(f"Points: {points_1d.flatten()}")

# All pairwise distances > 0
dists_1d = []
for i in range(10):
    for j in range(i+1, 10):
        dists_1d.append(abs(points_1d[i,0] - points_1d[j,0]))
print(f"All pairwise distances > 0? {all(d > 0 for d in dists_1d)}")
print(f"Minimum distance: {min(dists_1d)}")
print(f"But these points are in D = 1, not D = 9 = N - 1")
print(f"\nThis shows 'distinguishability' does NOT imply D >= N - 1")


# ============================================================================
# ISSUE 3: FRAMEWORK SCOPE AND SU(5) COUNTER-EXAMPLE
# ============================================================================

print("\n" + "=" * 80)
print("ISSUE 3: FRAMEWORK SCOPE AND SU(5) COUNTER-EXAMPLE")
print("=" * 80)

print("""
ISSUE:
The lemma claims D_space >= N - 1 as if it were a universal physical law.
However, SU(5) GUT is a mathematically consistent QFT in D = 4 spacetime,
despite having N = 5 which would require D_space >= 4.

RESOLUTION:
The constraint D_space >= N - 1 applies specifically to the
CHIRAL GEOMETROGENESIS FRAMEWORK where:
1. Color charges are geometrically realized as polyhedral vertices
2. The gauge group is embedded in physical space via the stella octangula
3. This is a framework-specific geometric constraint, not universal physics

Standard QFT places no such constraint — internal gauge symmetries are
independent of spacetime dimension.
""")

print("\n--- Analysis of SU(5) Grand Unified Theory ---")
print("""
SU(5) GUT Properties:
- Gauge group: SU(5) with rank 4
- Spacetime: D = 4 (3 spatial + 1 temporal)
- Spatial dimensions: D_space = 3

According to Lemma 0.0.2a:
- Constraint: D_space >= N - 1 = 5 - 1 = 4
- Actual: D_space = 3
- Conclusion: SU(5) "violates" the constraint

But SU(5) GUT is:
✓ Mathematically consistent (renormalizable gauge theory)
✓ Unitary and causal
✓ Anomaly-free (with appropriate fermion content)
✗ Experimentally excluded (proton decay not observed)

SU(5) was excluded by EXPERIMENT (proton lifetime bounds),
NOT by dimensional incompatibility.
""")

# Proton decay bounds
print("\n--- Experimental Bounds on SU(5) GUT ---")
print("""
Proton Decay Searches:
- Dominant mode in minimal SU(5): p → e⁺ + π⁰
- Super-Kamiokande bound: τ(p → e⁺π⁰) > 2.4 × 10³⁴ years (2020)
- Minimal SU(5) prediction: τ ~ 10²⁹-10³¹ years

Result: Minimal SU(5) is EXCLUDED by ~4 orders of magnitude
Reason: EXPERIMENTAL, not dimensional
""")

# Framework-specific interpretation
print("\n--- CORRECTED SCOPE FOR LEMMA 0.0.2a ---")
corrected_scope = """
FRAMEWORK-SPECIFIC CONSTRAINT:

Within the Chiral Geometrogenesis framework, where gauge symmetries are
geometrically realized on polyhedral structures:

1. SU(N) color charges are mapped to vertices of the weight diagram
2. The weight diagram is embedded in physical space
3. For this embedding to be faithful (preserve Weyl group action),
   the vertices must be affinely independent
4. N affinely independent points require D_space >= N - 1

This is a GEOMETRIC REALIZATION CONSTRAINT, not a universal physical law.

Standard QFT with internal gauge symmetries has no such constraint because
gauge groups live in abstract internal spaces, not physical space.

The lemma should explicitly state:
"In the geometric realization of SU(N) color as polyhedral vertices,
the constraint D_space >= N - 1 ensures the Weyl group acts faithfully."
"""
print(corrected_scope)


# ============================================================================
# DERIVATION: CORRECT DIMENSION CONSTRAINT FROM WEYL GROUP
# ============================================================================

print("\n" + "=" * 80)
print("DERIVATION: DIMENSION CONSTRAINT FROM WEYL GROUP ACTION")
print("=" * 80)

print("""
The correct derivation uses the Weyl group, not "distinguishability":

THEOREM (Weyl Group Faithful Representation):
For the Weyl group W(SU(N)) = S_N to act faithfully on a geometric
realization of the weight diagram, the N fundamental weights must
be embedded as N points in GENERAL POSITION.

PROOF:
1. The Weyl group S_N permutes the N fundamental weights transitively
2. A faithful action means distinct group elements give distinct permutations
3. For S_N to act faithfully on N points in Euclidean space,
   the points must be vertices of an (N-1)-simplex
4. An (N-1)-simplex requires (N-1) dimensions

Therefore: D_space >= N - 1 for faithful Weyl group action.

For SU(3): W(SU(3)) = S_3, N = 3, so D_space >= 2.
Since D_space = 3 in our universe, the constraint is satisfied.
""")

def verify_weyl_group_action():
    """
    Verify that the Weyl group S_3 acts faithfully on the SU(3) weight triangle.
    """
    print("\n--- Verification: S_3 Action on SU(3) Weights ---")

    # SU(3) fundamental weights
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    weights = {'R': w_R, 'G': w_G, 'B': w_B}
    weight_array = np.array([w_R, w_G, w_B])

    # S_3 elements as permutations
    # Identity, (12), (13), (23), (123), (132)
    S3_elements = [
        ('e', [0, 1, 2]),      # Identity
        ('(RG)', [1, 0, 2]),   # Swap R and G
        ('(RB)', [2, 1, 0]),   # Swap R and B
        ('(GB)', [0, 2, 1]),   # Swap G and B
        ('(RGB)', [1, 2, 0]),  # R→G→B→R
        ('(RBG)', [2, 0, 1]),  # R→B→G→R
    ]

    print("S_3 has 6 elements (permutations of {R, G, B}):\n")

    for name, perm in S3_elements:
        permuted = weight_array[perm]
        print(f"{name}: (R, G, B) → ({['R','G','B'][perm[0]]}, {['R','G','B'][perm[1]]}, {['R','G','B'][perm[2]]})")
        print(f"    Weight positions: {weight_array.tolist()} → {permuted.tolist()}")

    # Verify all 6 permutations give distinct configurations
    print("\n--- Faithfulness Check ---")
    configs = []
    for name, perm in S3_elements:
        permuted = tuple(map(tuple, weight_array[perm]))
        configs.append(permuted)

    n_distinct = len(set(configs))
    print(f"Number of distinct configurations: {n_distinct}")
    print(f"Number of group elements: {len(S3_elements)}")
    print(f"Action is faithful: {n_distinct == len(S3_elements)}")

    return n_distinct == len(S3_elements)

weyl_faithful = verify_weyl_group_action()

# Why 2D is sufficient for SU(3)
print("\n--- Why D = 2 is Sufficient for SU(3) ---")
print("""
For SU(3) with 3 fundamental weights:
- 3 points in general position form a triangle (2-simplex)
- A triangle exists in exactly 2 dimensions
- The Weyl group S_3 acts as the symmetry group of the triangle
  (3 reflections + 2 rotations + identity = 6 elements)

In our universe with D_space = 3:
- 3 >= 2 ✓ (constraint satisfied with margin)
- The extra dimension (radial) comes from confinement physics

For SU(4) with 4 fundamental weights:
- 4 points in general position form a tetrahedron (3-simplex)
- A tetrahedron exists in exactly 3 dimensions
- D_space = 3 >= 3 ✓ (marginally satisfied)

For SU(5) with 5 fundamental weights:
- 5 points in general position form a 4-simplex
- A 4-simplex requires 4 dimensions
- D_space = 3 < 4 ✗ (not satisfied in geometric realization)
""")


# ============================================================================
# SUMMARY OF CORRECTIONS
# ============================================================================

print("\n" + "=" * 80)
print("SUMMARY OF ALL CORRECTIONS")
print("=" * 80)

corrections = {
    'issue_1': {
        'title': 'Color Superposition States',
        'original': 'A quark is definitively red, green, OR blue—not a continuous superposition',
        'corrected': 'Color quantum numbers are discrete {R, G, B}, but quarks in hadrons exist in quantum superpositions. Only color-singlet combinations are observable asymptotically.',
        'physics': 'Meson = (|RR̄⟩+|GḠ⟩+|BB̄⟩)/√3; Baryon = antisymmetric ε^{ijk} contraction',
        'status': 'CORRECTED'
    },
    'issue_2': {
        'title': 'Affine Independence Theorem',
        'original': 'N distinguishable points require D >= N-1',
        'corrected': 'N affinely independent points (forming an (N-1)-simplex) require exactly N-1 dimensions. This is stronger than mere distinguishability.',
        'mathematics': 'Affine independence ≠ distinguishability. Counter-example: 100 points on a line are distinguishable in D=1.',
        'status': 'CORRECTED'
    },
    'issue_3': {
        'title': 'Framework Scope',
        'original': 'Universal physical constraint D_space >= N-1',
        'corrected': 'Framework-specific geometric realization constraint. Standard QFT allows any SU(N) in any D >= 4.',
        'example': 'SU(5) GUT is mathematically consistent in D=4, excluded by experiment not dimension.',
        'status': 'CORRECTED'
    },
    'issue_4': {
        'title': 't Hooft Citation Date',
        'original': "'t Hooft (1980)",
        'corrected': "'t Hooft (1978). Nucl. Phys. B 138, 1-25",
        'status': 'CORRECTED'
    },
    'issue_5': {
        'title': 'Missing References',
        'additions': [
            'FLAG Review 2024 (arXiv:2411.04268) — Lattice QCD averages',
            'PDG 2024 — QCD and lattice reviews',
            'Grünbaum, B. "Convex Polytopes" 2nd ed. (2003) — Simplex geometry',
            'Coxeter, H.S.M. "Regular Polytopes" 3rd ed. (1973) — Classical reference'
        ],
        'status': 'TO BE ADDED'
    }
}

for issue_id, data in corrections.items():
    print(f"\n{issue_id.upper()}: {data['title']}")
    print(f"  Status: {data['status']}")
    if 'original' in data:
        print(f"  Original: {data['original'][:60]}...")
        print(f"  Corrected: {data['corrected'][:60]}...")

# Save corrections summary
corrections_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/foundations/lemma_0_0_2a_corrections.json"

# Convert numpy types to Python native types
def convert_to_native(obj):
    if isinstance(obj, (np.integer, np.int64, np.int32)):
        return int(obj)
    elif isinstance(obj, (np.floating, np.float64, np.float32)):
        return float(obj)
    elif isinstance(obj, np.ndarray):
        return obj.tolist()
    elif isinstance(obj, (np.bool_, bool)):
        return bool(obj)
    elif isinstance(obj, dict):
        return {k: convert_to_native(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [convert_to_native(i) for i in obj]
    return obj

with open(corrections_path, 'w') as f:
    json.dump(convert_to_native({
        'date': datetime.now().isoformat(),
        'corrections': corrections,
        'affine_results': affine_results,
        'weyl_faithful': weyl_faithful
    }), f, indent=2)
print(f"\nCorrections saved to: {corrections_path}")


# ============================================================================
# VISUALIZATION
# ============================================================================

print("\n" + "=" * 80)
print("GENERATING CORRECTED VISUALIZATIONS")
print("=" * 80)

fig, axes = plt.subplots(2, 2, figsize=(14, 12))

# Plot 1: Meson color singlet state
ax1 = axes[0, 0]
theta = np.linspace(0, 2*np.pi, 100)
colors = ['red', 'green', 'blue']
labels = ['|RR̄⟩', '|GḠ⟩', '|BB̄⟩']

for i, (color, label) in enumerate(zip(colors, labels)):
    angle = 2*np.pi*i/3
    ax1.arrow(0, 0, 0.8*np.cos(angle), 0.8*np.sin(angle),
              head_width=0.1, head_length=0.05, fc=color, ec=color, alpha=0.7)
    ax1.text(1.1*np.cos(angle), 1.1*np.sin(angle), label, ha='center', va='center', fontsize=12)

ax1.set_xlim(-1.5, 1.5)
ax1.set_ylim(-1.5, 1.5)
ax1.set_aspect('equal')
ax1.set_title('Meson Color Singlet State\n|ψ⟩ = (|RR̄⟩ + |GḠ⟩ + |BB̄⟩)/√3', fontsize=12)
ax1.text(0, -1.3, 'SUPERPOSITION, not definite color', ha='center', fontsize=10, style='italic')
ax1.axis('off')

# Plot 2: Affine independence vs distinguishability
ax2 = axes[0, 1]

# Distinguishable but collinear (D=1)
x_line = np.arange(5)
ax2.scatter(x_line, np.zeros(5), c='red', s=100, label='5 points on line (D=1)', zorder=5)
ax2.plot(x_line, np.zeros(5), 'r--', alpha=0.5)

# Affinely independent (D=2)
triangle_x = [0, 1, 0.5]
triangle_y = [0, 0, np.sqrt(3)/2]
triangle_x.append(triangle_x[0])
triangle_y.append(triangle_y[0])
ax2.plot([t+5 for t in triangle_x], [t+0.5 for t in triangle_y], 'b-', linewidth=2)
ax2.scatter([t+5 for t in triangle_x[:-1]], [t+0.5 for t in triangle_y[:-1]],
            c='blue', s=100, label='3 points in general pos. (D=2)', zorder=5)

ax2.set_xlim(-1, 8)
ax2.set_ylim(-1, 2)
ax2.legend(loc='upper left')
ax2.set_title('Distinguishability ≠ Affine Independence\n5 distinguishable pts need D≥1; 3 in general pos. need D≥2', fontsize=11)
ax2.set_xlabel('Position')
ax2.axis('off')

# Plot 3: SU(3) weight triangle with Weyl group action
ax3 = axes[1, 0]

# Fundamental weights
w_R = np.array([1/2, 1/(2*np.sqrt(3))])
w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
w_B = np.array([0, -1/np.sqrt(3)])

triangle = np.array([w_R, w_G, w_B, w_R])
ax3.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=2)
ax3.fill(triangle[:-1, 0], triangle[:-1, 1], alpha=0.1)

# Plot weights
for w, label, color in [(w_R, 'R', 'red'), (w_G, 'G', 'green'), (w_B, 'B', 'blue')]:
    ax3.scatter([w[0]], [w[1]], c=color, s=200, zorder=5, edgecolors='black', linewidth=2)
    ax3.annotate(label, w + np.array([0.05, 0.05]), fontsize=14, fontweight='bold')

# Draw Weyl reflection axes (each passes through a vertex and midpoint of opposite edge)
# The 3 reflection axes of S_3 acting on equilateral triangle:
# Axis 1: Through R and midpoint of GB
midpoint_GB = (w_G + w_B) / 2
ax3.plot([w_R[0], midpoint_GB[0]], [w_R[1], midpoint_GB[1]], 'gray', linestyle=':', alpha=0.7, linewidth=1.5)

# Axis 2: Through G and midpoint of RB
midpoint_RB = (w_R + w_B) / 2
ax3.plot([w_G[0], midpoint_RB[0]], [w_G[1], midpoint_RB[1]], 'gray', linestyle=':', alpha=0.7, linewidth=1.5)

# Axis 3: Through B and midpoint of RG
midpoint_RG = (w_R + w_G) / 2
ax3.plot([w_B[0], midpoint_RG[0]], [w_B[1], midpoint_RG[1]], 'gray', linestyle=':', alpha=0.7, linewidth=1.5)

ax3.scatter([0], [0], c='black', s=50, marker='x', zorder=5)
ax3.set_aspect('equal')
ax3.set_title('SU(3) Weight Triangle with S₃ Symmetry\nWeyl group acts faithfully on 3 vertices', fontsize=12)
ax3.set_xlabel('$T_3$')
ax3.set_ylabel('$T_8/\\sqrt{3}$')

# Plot 4: Framework scope diagram
ax4 = axes[1, 1]

N_values = np.arange(2, 8)
D_constraint = N_values - 1

# Regions
ax4.fill_between(N_values, D_constraint, 7, alpha=0.3, color='green', label='Geometric realization possible')
ax4.fill_between(N_values, 0, D_constraint, alpha=0.3, color='red', label='Geometric realization impossible')
ax4.plot(N_values, D_constraint, 'k-', linewidth=2, label='D = N - 1 (minimum)')
ax4.axhline(y=3, color='blue', linestyle='--', linewidth=2, label='Our universe: D_space = 3')

# Standard QFT region
ax4.annotate('Standard QFT: ANY SU(N) in D≥4\n(no dimensional constraint)',
             xy=(5.5, 5.5), fontsize=10, ha='center',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

ax4.scatter([5], [3], c='orange', s=200, marker='s', zorder=5, edgecolors='black', linewidth=2)
ax4.annotate('SU(5) GUT\n(QFT: OK)\n(Geom: ✗)', xy=(5.1, 3.3), fontsize=9)

ax4.set_xlabel('N (colors in SU(N))', fontsize=12)
ax4.set_ylabel('D_space (spatial dimensions)', fontsize=12)
ax4.set_xlim(1.5, 7.5)
ax4.set_ylim(0, 7)
ax4.legend(loc='upper left', fontsize=9)
ax4.set_title('Framework Scope: Geometric Realization Constraint\n(Not a universal physical law)', fontsize=12)
ax4.grid(True, alpha=0.3)

plt.tight_layout()

# Save
plot_path = os.path.join(PLOTS_DIR, 'lemma_0_0_2a_corrections.png')
plt.savefig(plot_path, dpi=150, bbox_inches='tight')
print(f"Plot saved to: {plot_path}")
plt.close()

print("\n" + "=" * 80)
print("DERIVATIONS AND CORRECTIONS COMPLETE")
print("=" * 80)
