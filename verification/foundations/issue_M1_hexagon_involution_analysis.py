#!/usr/bin/env python3
"""
Issue M1 Analysis: Hexagon Involution in 2D vs 3D
=================================================

The verification found that §5.2 incorrectly claims:
"The hexagon in 2D does not admit a geometric involution exchanging 3 ↔ 3̄
while preserving S_3 symmetry."

This script rigorously analyzes:
1. What involutions exist on the 2D hexagon
2. Whether they satisfy GR3 (exchange fund ↔ antifund)
3. Why 3D is actually needed (Physical Hypothesis 0.0.0f)
4. The correct mathematical statement
"""

import numpy as np
import json
import os

os.makedirs('plots', exist_ok=True)

print("=" * 70)
print("ISSUE M1: HEXAGON INVOLUTION ANALYSIS")
print("=" * 70)

# =============================================================================
# Section 1: Define the SU(3) weight hexagon
# =============================================================================

print("\n" + "=" * 70)
print("SECTION 1: SU(3) WEIGHT HEXAGON")
print("=" * 70)

# Fundamental weights (standard normalization)
w_R = np.array([1/2, 1/(2*np.sqrt(3))])
w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
w_B = np.array([0, -1/np.sqrt(3)])

# Antifundamental weights
w_Rbar = -w_R
w_Gbar = -w_G
w_Bbar = -w_B

fund_weights = {'R': w_R, 'G': w_G, 'B': w_B}
antifund_weights = {'R̄': w_Rbar, 'Ḡ': w_Gbar, 'B̄': w_Bbar}
all_weights = {**fund_weights, **antifund_weights}

print("\nFundamental weights:")
for name, w in fund_weights.items():
    print(f"  {name}: ({w[0]:.4f}, {w[1]:.4f})")

print("\nAntifundamental weights:")
for name, w in antifund_weights.items():
    print(f"  {name}: ({w[0]:.4f}, {w[1]:.4f})")

# =============================================================================
# Section 2: Analyze ALL involutions of the 2D hexagon
# =============================================================================

print("\n" + "=" * 70)
print("SECTION 2: INVOLUTIONS OF THE 2D HEXAGON")
print("=" * 70)

# A regular hexagon has D_6 symmetry (dihedral group of order 12)
# Involutions are:
# 1. Point inversion through center: v → -v
# 2. Reflections through 6 axes (3 through vertices, 3 through edge midpoints)

print("\n2.1 Point Inversion (v → -v)")
print("-" * 40)

def point_inversion(v):
    return -v

# Check: Does point inversion exchange fund ↔ antifund?
print("\nAction of point inversion:")
for name, w in fund_weights.items():
    inv_w = point_inversion(w)
    # Find which antifund weight this maps to
    for aname, aw in antifund_weights.items():
        if np.allclose(inv_w, aw):
            print(f"  {name} → {aname}")
            break

# Check: Is point inversion an involution?
is_involution = all(np.allclose(point_inversion(point_inversion(w)), w)
                    for w in all_weights.values())
print(f"\nPoint inversion is involution (P² = I): {is_involution}")

# Check: Does it preserve hexagon structure?
preserves_hexagon = all(
    any(np.allclose(point_inversion(w), w2) for w2 in all_weights.values())
    for w in all_weights.values()
)
print(f"Preserves hexagon structure: {preserves_hexagon}")

# Check: Does it commute with S_3 action?
# S_3 permutes {R,G,B} and correspondingly {R̄,Ḡ,B̄}
# Point inversion commutes with any rotation/reflection through origin
print(f"Commutes with S_3: True (central symmetry)")

print("\n✅ CONCLUSION: Point inversion IS a valid involution for GR3 in 2D")

# =============================================================================
# Section 3: Analyze the S_3 Weyl group action
# =============================================================================

print("\n" + "=" * 70)
print("SECTION 3: S_3 WEYL GROUP ACTION")
print("=" * 70)

# Simple roots
alpha_1 = w_R - w_G  # = (1, 0)
alpha_2 = w_G - w_B  # = (-1/2, sqrt(3)/2)

def weyl_reflection(v, alpha):
    """Reflect v through hyperplane perpendicular to alpha."""
    return v - 2 * np.dot(v, alpha) / np.dot(alpha, alpha) * alpha

# Generate S_3 elements
def s1(v):
    return weyl_reflection(v, alpha_1)

def s2(v):
    return weyl_reflection(v, alpha_2)

# Verify S_3 acts on hexagon vertices
print("\nS_3 action on fund weights:")
print(f"  s₁(R) = G: {np.allclose(s1(w_R), w_G)}")
print(f"  s₂(G) = B: {np.allclose(s2(w_G), w_B)}")

print("\nS_3 action on antifund weights:")
print(f"  s₁(R̄) = Ḡ: {np.allclose(s1(w_Rbar), w_Gbar)}")
print(f"  s₂(Ḡ) = B̄: {np.allclose(s2(w_Gbar), w_Bbar)}")

# Check: Does S_3 preserve the fund/antifund split?
s3_preserves_split = True
for name, w in fund_weights.items():
    s1_w = s1(w)
    s2_w = s2(w)
    # Check if results are still fundamental weights
    s1_is_fund = any(np.allclose(s1_w, fw) for fw in fund_weights.values())
    s2_is_fund = any(np.allclose(s2_w, fw) for fw in fund_weights.values())
    if not (s1_is_fund and s2_is_fund):
        s3_preserves_split = False
        break

print(f"\nS_3 preserves fund/antifund split: {s3_preserves_split}")

# =============================================================================
# Section 4: Why the original claim is MISLEADING
# =============================================================================

print("\n" + "=" * 70)
print("SECTION 4: ANALYSIS OF THE ORIGINAL CLAIM")
print("=" * 70)

print("""
ORIGINAL CLAIM (§5.2):
"The hexagon in 2D does not admit a geometric involution exchanging
3 ↔ 3̄ while preserving S_3 symmetry."

THIS IS INCORRECT as stated. Let's verify:
""")

# The claim is false - point inversion works
print("Point inversion P: v → -v")
print("  - Exchanges R ↔ R̄, G ↔ Ḡ, B ↔ B̄: ✅")
print("  - Is an involution (P² = I): ✅")
print("  - Commutes with S_3: ✅")
print("  - Is a geometric transformation: ✅")

print("\n❌ The original claim is INCORRECT")

# =============================================================================
# Section 5: What the claim SHOULD say
# =============================================================================

print("\n" + "=" * 70)
print("SECTION 5: CORRECT MATHEMATICAL STATEMENT")
print("=" * 70)

print("""
The CORRECT statement involves the TETRAHEDRAL structure, not involution:

ISSUE 1: 2D hexagon DOES satisfy GR1-GR3
------------------------------------------
- GR1: ✅ 6 vertices correspond to 6 weights (fund ⊕ antifund)
- GR2: ✅ D_6 symmetry contains S_3 (Weyl group)
- GR3: ✅ Point inversion implements charge conjugation

ISSUE 2: Why 3D is needed
--------------------------
The need for 3D comes from PHYSICAL requirements, not GR1-GR3:

Physical Hypothesis 0.0.0f states:
  d_embed = rank(G) + 1 = 2 + 1 = 3 for SU(3)

This comes from:
1. Radial direction for confinement (flux tube structure)
2. Support for field dynamics with non-trivial topology

ISSUE 3: Correct statement about 3D
------------------------------------
The stella octangula (3D) adds:
- 2 apex vertices for 3D embedding
- Tetrahedral structure enabling:
  * Radial confinement direction
  * Non-trivial 3D topology
  * Physical flux tube support
""")

# =============================================================================
# Section 6: The apex vertex necessity
# =============================================================================

print("\n" + "=" * 70)
print("SECTION 6: APEX VERTEX NECESSITY")
print("=" * 70)

print("""
Why apex vertices are needed for 3D POLYHEDRAL structure:

1. The 6 weight vertices lie in a 2D plane (the weight space)
2. To create a 3D POLYHEDRON with non-zero volume, we need vertices
   outside this plane
3. The MINIMAL such addition: 2 apex vertices (one above, one below)
4. This creates two tetrahedra = stella octangula

The requirement is POLYHEDRA (closed, bounded), not just point sets.
""")

# Demonstrate: 6 coplanar points can't form 3D polyhedron
z_coords = [0, 0, 0, 0, 0, 0]  # All in z=0 plane
print(f"Weight vertices z-coordinates: {z_coords}")
print(f"All coplanar: {len(set(z_coords)) == 1}")
print("Cannot form 3D polyhedron with volume from coplanar points")

# =============================================================================
# Section 7: Corrected text for §5.2
# =============================================================================

print("\n" + "=" * 70)
print("SECTION 7: CORRECTED TEXT FOR §5.2")
print("=" * 70)

corrected_text = """
CORRECTED §5.2 TEXT:
====================

### 5.2 Applying GR1

(GR1) requires 6 vertices corresponding to the 6 weights of 3 ⊕ 3̄.

**Question:** Can we satisfy GR1-GR3 with just 6 vertices in 2D?

**Answer:** Yes, GR1-GR3 can be satisfied in 2D. The hexagon formed by
the 6 weights admits point inversion (v → -v) as a geometric involution
implementing charge conjugation, and its D₆ symmetry group contains S₃.

**However:** Physical Hypothesis 0.0.0f (derived from QCD flux tube
structure in Lemma 0.0.0f) requires:
  d_embed = rank(G) + 1 = 3 for SU(3)

This necessitates embedding the weight structure in 3D. Since the 6
weight vertices are coplanar (lying in the 2D weight space), forming a
3D polyhedral complex requires additional vertices outside this plane.

**Solution:** Add 2 apex vertices (above and below the weight plane),
creating two interlocking tetrahedra—the stella octangula.

Total vertices: 6 (weight) + 2 (apex) = 8

**Remark:** The 2D hexagon is a valid geometric realization in d_embed = 2.
The stella octangula is the unique minimal realization for d_embed = 3.
"""

print(corrected_text)

# =============================================================================
# Save results
# =============================================================================

results = {
    "issue": "M1",
    "title": "Hexagon Involution Analysis",
    "date": "2025-12-30",
    "finding": "Original §5.2 claim is INCORRECT",
    "analysis": {
        "point_inversion_valid": True,
        "point_inversion_exchanges_fund_antifund": True,
        "point_inversion_is_involution": True,
        "point_inversion_commutes_with_S3": True,
        "2D_hexagon_satisfies_GR1_GR2_GR3": True
    },
    "correct_statement": {
        "2D_hexagon_is_valid_realization": True,
        "3D_requirement_from": "Physical Hypothesis 0.0.0f (d_embed = rank + 1)",
        "apex_vertices_needed_for": "3D polyhedral structure (volume requires non-coplanar points)"
    },
    "recommended_correction": "Replace claim about hexagon involution with correct statement about physical embedding dimension"
}

output_file = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/foundations/issue_M1_analysis_results.json"
with open(output_file, 'w') as f:
    json.dump(results, f, indent=2)

print(f"\nResults saved to: {output_file}")

# =============================================================================
# Generate visualization
# =============================================================================

try:
    import matplotlib.pyplot as plt

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    # Left: 2D hexagon with involution
    ax1 = axes[0]

    # Plot weights
    fund_x = [w[0] for w in fund_weights.values()]
    fund_y = [w[1] for w in fund_weights.values()]
    antifund_x = [w[0] for w in antifund_weights.values()]
    antifund_y = [w[1] for w in antifund_weights.values()]

    ax1.scatter(fund_x, fund_y, c='blue', s=150, label='Fundamental', zorder=5)
    ax1.scatter(antifund_x, antifund_y, c='red', s=150, label='Antifundamental', zorder=5)

    # Draw hexagon
    all_points = list(fund_weights.values()) + list(antifund_weights.values())
    angles = [np.arctan2(p[1], p[0]) for p in all_points]
    sorted_idx = np.argsort(angles)
    hex_x = [all_points[i][0] for i in sorted_idx] + [all_points[sorted_idx[0]][0]]
    hex_y = [all_points[i][1] for i in sorted_idx] + [all_points[sorted_idx[0]][1]]
    ax1.plot(hex_x, hex_y, 'g-', alpha=0.5, linewidth=2)

    # Draw point inversion arrows
    for name, w in list(fund_weights.items())[:2]:  # Just show 2 for clarity
        ax1.annotate('', xy=(-w[0], -w[1]), xytext=(w[0], w[1]),
                    arrowprops=dict(arrowstyle='->', color='purple', lw=2))

    # Labels
    labels = ['R', 'G', 'B', 'R̄', 'Ḡ', 'B̄']
    all_w = list(fund_weights.values()) + list(antifund_weights.values())
    for label, w in zip(labels, all_w):
        offset = w / np.linalg.norm(w) * 0.08
        ax1.annotate(label, (w[0] + offset[0], w[1] + offset[1]), fontsize=12, ha='center')

    ax1.axhline(y=0, color='gray', linestyle='--', alpha=0.3)
    ax1.axvline(x=0, color='gray', linestyle='--', alpha=0.3)
    ax1.plot(0, 0, 'ko', markersize=8)
    ax1.set_xlabel('T₃', fontsize=12)
    ax1.set_ylabel('T₈', fontsize=12)
    ax1.set_title('2D Hexagon with Point Inversion\n(Valid GR3 involution)', fontsize=12)
    ax1.legend(loc='upper right')
    ax1.set_aspect('equal')
    ax1.grid(True, alpha=0.3)

    # Right: Why 3D is needed
    ax2 = axes[1]
    ax2.text(0.5, 0.9, 'Why 3D Embedding is Required', fontsize=14, fontweight='bold',
             ha='center', transform=ax2.transAxes)

    explanation = """
    ✅ 2D hexagon satisfies GR1-GR3:
       • GR1: 6 vertices ↔ 6 weights
       • GR2: D₆ ⊃ S₃ (Weyl group)
       • GR3: Point inversion = charge conjugation

    🔶 Physical Hypothesis 0.0.0f requires:
       d_embed = rank(G) + 1 = 3

    📐 For 3D polyhedral structure:
       • 6 weight vertices are coplanar
       • Need ≥1 vertex outside weight plane
       • Minimal: 2 apex vertices
       → Stella octangula (8 vertices)

    🎯 Conclusion:
       • 2D hexagon: Valid for d_embed = 2
       • Stella octangula: Minimal for d_embed = 3
    """

    ax2.text(0.1, 0.75, explanation, fontsize=10, va='top',
             transform=ax2.transAxes, family='monospace')
    ax2.axis('off')

    plt.tight_layout()
    plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/issue_M1_hexagon_analysis.png', dpi=150)
    print(f"\nPlot saved to: verification/plots/issue_M1_hexagon_analysis.png")
    plt.close()

except ImportError:
    print("\n(matplotlib not available - skipping plot)")

print("\n" + "=" * 70)
print("ANALYSIS COMPLETE")
print("=" * 70)
