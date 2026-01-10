#!/usr/bin/env python3
"""
Issue 2: Derivation of Geometric μ-τ Asymmetry Formula
========================================================

The proposition claims (§4.3):
    δ_μ - δ_τ = λ/√2 = 0.159 rad = 9.1°

where δ_μ and δ_τ are angular positions of the muon and tau generations
in the stella octangula geometry.

This script provides the missing first-principles derivation.

KEY INSIGHT from Lemma 3.1.2a:
- Generations are localized in a HEXAGONAL pattern (projected from stella octangula)
- 3rd gen (τ): at center (r₃ = 0)
- 2nd gen (μ): at radius r₂ = ε (inner hexagon)
- 1st gen (e): at radius r₁ = √3·ε (outer hexagon)

The μ-τ asymmetry arises when the electroweak VEV picks a DIRECTION in this plane.
"""

import numpy as np
import matplotlib.pyplot as plt

# Constants
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
LAMBDA = np.sin(np.radians(72)) / PHI**3  # Wolfenstein parameter = 0.2245

print("=" * 70)
print("ISSUE 2: GEOMETRIC μ-τ ASYMMETRY DERIVATION")
print("=" * 70)

# ============================================================================
# PART 1: THE HEXAGONAL GENERATION STRUCTURE
# ============================================================================

print("\n### PART 1: Hexagonal Generation Structure ###\n")

print("From Lemma 3.1.2a, the stella octangula projects onto a hexagonal lattice")
print("in the plane perpendicular to the [1,1,1] direction (color-neutral axis).")
print()
print("Generation positions (angular):")
print("  θ_e = 0°              (electron - reference direction)")
print("  θ_μ = 2π/3 + δ_μ      (muon - 120° from e, plus perturbation)")
print("  θ_τ = 4π/3 + δ_τ      (tau - 240° from e, plus perturbation)")
print()
print("In the SYMMETRIC limit (A₄ symmetry preserved):")
print("  δ_μ = δ_τ = 0")
print("  This gives exact μ-τ symmetry: |U_μi| = |U_τi| for all i")
print()

# The hexagonal positions
theta_e = 0
theta_mu_sym = 2 * np.pi / 3
theta_tau_sym = 4 * np.pi / 3

# ============================================================================
# PART 2: ELECTROWEAK VEV DIRECTION
# ============================================================================

print("\n### PART 2: Electroweak VEV Direction ###\n")

print("The electroweak VEV ⟨H⟩ = (0, v/√2)ᵀ selects a direction in the generation space.")
print()
print("In the CG framework, this corresponds to selecting a direction φ_EW in")
print("the hexagonal plane. The generations couple asymmetrically to this VEV.")
print()

# The key physics: The Higgs VEV direction φ_EW is determined by electroweak physics
# In the stella octangula, this direction is related to the Wolfenstein angle

print("The VEV direction angle φ_EW is related to the Cabibbo angle θ_C:")
print("  φ_EW ∝ arctan(|V_us|/|V_ud|) ≈ arctan(λ) ≈ λ (for small λ)")
print()

# VEV direction angle (in radians, measured from the e-direction)
phi_EW = LAMBDA  # The VEV direction is at angle λ from the electron direction

print(f"  φ_EW ≈ λ = {LAMBDA:.4f} rad = {np.degrees(LAMBDA):.2f}°")

# ============================================================================
# PART 3: ASYMMETRIC PERTURBATION FROM VEV
# ============================================================================

print("\n### PART 3: Asymmetric Perturbation from VEV ###\n")

print("The VEV induces perturbations to the generation positions:")
print()
print("  δ_α = ε_α × cos(θ_α - φ_EW) × coupling_strength")
print()
print("where:")
print("  - ε_α is the perturbation strength (related to Yukawa coupling)")
print("  - θ_α is the symmetric position angle")
print("  - φ_EW is the VEV direction")
print()

# The perturbation to each generation position
# The key insight: The perturbation is proportional to the projection of the
# VEV direction onto the generation's angular position

def perturbation(theta_gen, phi_vev, coupling):
    """Calculate angular perturbation to generation position from VEV"""
    return coupling * np.cos(theta_gen - phi_vev)

# The coupling strength is set by the Wolfenstein parameter
# From dimensional analysis: coupling ~ λ (the natural small parameter)
coupling = LAMBDA

# Calculate perturbations (note: electron is at reference direction, no perturbation by definition)
delta_e = 0  # Reference
delta_mu = perturbation(theta_mu_sym, phi_EW, coupling)
delta_tau = perturbation(theta_tau_sym, phi_EW, coupling)

print(f"Perturbations (with coupling λ = {LAMBDA:.4f}):")
print(f"  δ_e = 0 (reference)")
print(f"  δ_μ = λ × cos(2π/3 - λ)")
print(f"      = {LAMBDA:.4f} × cos({np.degrees(theta_mu_sym):.1f}° - {np.degrees(phi_EW):.2f}°)")
print(f"      = {LAMBDA:.4f} × {np.cos(theta_mu_sym - phi_EW):.4f}")
print(f"      = {delta_mu:.5f} rad = {np.degrees(delta_mu):.2f}°")
print()
print(f"  δ_τ = λ × cos(4π/3 - λ)")
print(f"      = {LAMBDA:.4f} × cos({np.degrees(theta_tau_sym):.1f}° - {np.degrees(phi_EW):.2f}°)")
print(f"      = {LAMBDA:.4f} × {np.cos(theta_tau_sym - phi_EW):.4f}")
print(f"      = {delta_tau:.5f} rad = {np.degrees(delta_tau):.2f}°")

# ============================================================================
# PART 4: THE μ-τ ASYMMETRY
# ============================================================================

print("\n### PART 4: The μ-τ Asymmetry ###\n")

delta_mu_tau = delta_mu - delta_tau

print(f"μ-τ asymmetry:")
print(f"  δ_μ - δ_τ = {delta_mu:.5f} - ({delta_tau:.5f})")
print(f"            = {delta_mu_tau:.5f} rad")
print(f"            = {np.degrees(delta_mu_tau):.2f}°")
print()

# Now let's derive the analytical formula
# cos(2π/3 - λ) - cos(4π/3 - λ) = 2 sin(π) sin(π/3 - λ/2)
#                                = 0 (exact, but this is wrong approach)
# Actually: cos(A) - cos(B) = -2 sin((A+B)/2) sin((A-B)/2)

A = theta_mu_sym - phi_EW
B = theta_tau_sym - phi_EW

print("Analytical derivation:")
print(f"  cos(θ_μ - φ) - cos(θ_τ - φ)")
print(f"  = cos({np.degrees(A):.2f}°) - cos({np.degrees(B):.2f}°)")
print()
print("Using cos(A) - cos(B) = -2 sin((A+B)/2) sin((A-B)/2):")
print(f"  A + B = 2π/3 + 4π/3 - 2λ = 2π - 2λ")
print(f"  (A + B)/2 = π - λ")
print(f"  sin(π - λ) = sin(λ) ≈ λ")
print()
print(f"  A - B = 2π/3 - 4π/3 = -2π/3")
print(f"  (A - B)/2 = -π/3")
print(f"  sin(-π/3) = -√3/2")
print()
print(f"  cos(A) - cos(B) = -2 × sin(λ) × (-√3/2)")
print(f"                  = √3 × sin(λ)")
print(f"                  ≈ √3 × λ  (for small λ)")
print()

# So δ_μ - δ_τ = λ × √3 × λ = √3 λ²
analytical_formula = np.sqrt(3) * LAMBDA**2
print(f"Therefore:")
print(f"  δ_μ - δ_τ = λ × (√3 λ) = √3 λ²")
print(f"            = √3 × ({LAMBDA:.4f})²")
print(f"            = {analytical_formula:.5f} rad")
print(f"            = {np.degrees(analytical_formula):.2f}°")

# ============================================================================
# PART 5: RECONCILIATION WITH DOCUMENT CLAIM
# ============================================================================

print("\n### PART 5: Reconciliation with Document Claim ###\n")

doc_claim = LAMBDA / np.sqrt(2)
print(f"Document claims: δ_μ - δ_τ = λ/√2 = {doc_claim:.5f} rad = {np.degrees(doc_claim):.2f}°")
print()
print(f"Our derivation: δ_μ - δ_τ = √3 λ² = {analytical_formula:.5f} rad = {np.degrees(analytical_formula):.2f}°")
print()
print("DISCREPANCY: The document's formula λ/√2 does not match our first-principles derivation √3λ²!")
print()

# Let's check what the document's formula would give vs our derivation
print("Comparison:")
print(f"  Document formula (λ/√2):     {np.degrees(doc_claim):.2f}°")
print(f"  Our derivation (√3λ²):        {np.degrees(analytical_formula):.2f}°")
print(f"  Numerical calculation:        {np.degrees(delta_mu_tau):.2f}°")
print()

# ============================================================================
# PART 6: ALTERNATIVE DERIVATION - DIRECT COUPLING
# ============================================================================

print("\n### PART 6: Alternative Derivation (Direct Coupling Model) ###\n")

print("Perhaps the document uses a different physical model.")
print()
print("Alternative: The asymmetry arises from DIRECT off-diagonal couplings")
print("in the charged lepton mass matrix, proportional to λ.")
print()
print("In this case, the μ-τ splitting might be:")
print("  δ_μ - δ_τ = λ × projection_factor")
print()
print("For the projection factor to give 1/√2:")
print("  This would arise if the VEV projects onto a 45° direction in")
print("  the μ-τ subspace of the mass matrix.")
print()

# Let's try a different approach: the asymmetry comes from the
# misalignment between neutrino and charged lepton bases

print("Physical interpretation:")
print("  The angle 1/√2 factor could arise from the 45° mixing in the 2-3 sector")
print("  of tribimaximal mixing.")
print()
print("  In TBM: θ₂₃ = 45°, so sin(45°) = cos(45°) = 1/√2")
print()
print("  If the VEV direction projects onto the μ-τ plane at angle λ,")
print("  and the projection involves the TBM rotation,")
print("  then: δ_μ - δ_τ ∝ λ × sin(45°) × factor")
print()

# Alternative formula assuming 45° projection
alt_formula = LAMBDA * np.sin(np.radians(45))  # λ × sin(45°)
print(f"  λ × sin(45°) = {alt_formula:.5f} rad = {np.degrees(alt_formula):.2f}°")
print()

# But the document says λ/√2, not λ×sin(45°)×something
# Actually λ/√2 = λ × 1/√2 = λ × sin(45°) = 0.159 rad

print(f"Note: λ/√2 = λ × sin(45°) = {LAMBDA/np.sqrt(2):.5f} rad")
print()

# ============================================================================
# PART 7: PROPOSED CORRECT FORMULA
# ============================================================================

print("\n### PART 7: PROPOSED CORRECT FORMULA ###\n")

print("Based on our analysis, there are TWO possible correct formulas:")
print()
print("FORMULA A (First-principles from hexagonal geometry):")
print("  δ_μ - δ_τ = √3 × λ²")
print(f"            = {np.degrees(analytical_formula):.2f}°")
print()
print("FORMULA B (Phenomenological from TBM structure):")
print("  δ_μ - δ_τ = λ/√2")
print(f"            = {np.degrees(doc_claim):.2f}°")
print()
print("The document uses FORMULA B but doesn't derive it rigorously.")
print()
print("FORMULA B can be justified if:")
print("  - The VEV direction couples to the 2-3 generation sector")
print("  - The coupling strength is λ (Wolfenstein parameter)")
print("  - The projection factor is 1/√2 from TBM's maximal 2-3 mixing")
print()

# ============================================================================
# PART 8: IMPACT ON θ₂₃ PREDICTION
# ============================================================================

print("\n### PART 8: Impact on θ₂₃ Prediction ###\n")

# Using the document's formula for δθ₂₃^(geo)
delta_geo_doc = 0.5 * doc_claim * np.cos(np.radians(33.4))  # From document: (1/2)(δ_μ - δ_τ)cos(θ₁₂)

# Using our derived formula
delta_geo_derived = 0.5 * analytical_formula * np.cos(np.radians(33.4))

print("Translation to θ₂₃ correction:")
print("  δθ₂₃^(geo) = (1/2) × (δ_μ - δ_τ) × cos(θ₁₂)")
print()
print(f"Document formula:")
print(f"  δθ₂₃^(geo) = (1/2) × {np.degrees(doc_claim):.2f}° × cos(33.4°)")
print(f"            = {np.degrees(delta_geo_doc):.2f}°")
print()
print(f"Our derived formula:")
print(f"  δθ₂₃^(geo) = (1/2) × {np.degrees(analytical_formula):.2f}° × cos(33.4°)")
print(f"            = {np.degrees(delta_geo_derived):.2f}°")
print()

# ============================================================================
# PART 9: VISUALIZATION
# ============================================================================

print("\n### Creating visualization... ###\n")

fig, axes = plt.subplots(1, 2, figsize=(14, 6))

# Plot 1: Hexagonal generation structure
ax1 = axes[0]

# Draw hexagonal grid
theta_hex = np.linspace(0, 2*np.pi, 7)
r_hex = 1.0

# Inner hexagon (2nd generation)
hex_x_inner = r_hex * np.cos(theta_hex)
hex_y_inner = r_hex * np.sin(theta_hex)
ax1.plot(hex_x_inner, hex_y_inner, 'b-', alpha=0.3)

# Outer hexagon (1st generation)
hex_x_outer = np.sqrt(3) * r_hex * np.cos(theta_hex + np.pi/6)
hex_y_outer = np.sqrt(3) * r_hex * np.sin(theta_hex + np.pi/6)
ax1.plot(hex_x_outer, hex_y_outer, 'g-', alpha=0.3)

# Generation positions (symmetric)
gen_angles_sym = [0, 2*np.pi/3, 4*np.pi/3]
gen_radii = [np.sqrt(3), 1, 0]  # e, μ, τ
gen_labels = ['e', 'μ', 'τ']
gen_colors = ['green', 'blue', 'red']

for i, (angle, r, label, color) in enumerate(zip(gen_angles_sym, gen_radii, gen_labels, gen_colors)):
    x = r * np.cos(angle)
    y = r * np.sin(angle)
    ax1.plot(x, y, 'o', markersize=15, color=color, label=f'{label} (symmetric)')
    ax1.annotate(label, (x, y), fontsize=14, ha='center', va='center', color='white', fontweight='bold')

# VEV direction
vev_len = 2.0
ax1.arrow(0, 0, vev_len * np.cos(phi_EW), vev_len * np.sin(phi_EW),
          head_width=0.1, head_length=0.1, fc='orange', ec='orange', linewidth=2)
ax1.annotate(f'VEV (φ ≈ λ = {np.degrees(phi_EW):.1f}°)',
             (vev_len * np.cos(phi_EW) * 0.7, vev_len * np.sin(phi_EW) * 0.7 + 0.2),
             fontsize=10, color='orange')

# Perturbed positions (exaggerated for visibility)
scale = 10  # Exaggeration factor for visualization
for i, (angle_sym, r, delta, label) in enumerate(zip(gen_angles_sym, gen_radii, [0, delta_mu, delta_tau], gen_labels)):
    if r > 0:
        angle_pert = angle_sym + scale * delta
        x = r * np.cos(angle_pert)
        y = r * np.sin(angle_pert)
        ax1.plot(x, y, 's', markersize=10, color=gen_colors[i], alpha=0.5)
        # Draw perturbation arc
        arc_angles = np.linspace(angle_sym, angle_pert, 20)
        arc_x = r * np.cos(arc_angles)
        arc_y = r * np.sin(arc_angles)
        ax1.plot(arc_x, arc_y, '--', color=gen_colors[i], alpha=0.7)

ax1.set_xlim(-2.5, 2.5)
ax1.set_ylim(-2.5, 2.5)
ax1.set_aspect('equal')
ax1.axhline(0, color='gray', linestyle='-', alpha=0.2)
ax1.axvline(0, color='gray', linestyle='-', alpha=0.2)
ax1.set_xlabel('x (color space)', fontsize=12)
ax1.set_ylabel('y (color space)', fontsize=12)
ax1.set_title('Hexagonal Generation Structure\n(perturbations exaggerated 10×)', fontsize=14)
ax1.grid(True, alpha=0.2)

# Plot 2: Formula comparison
ax2 = axes[1]

formulas = ['Document\n(λ/√2)', 'First-principles\n(√3λ²)', 'Numerical\ncalculation']
asymmetries = [np.degrees(doc_claim), np.degrees(analytical_formula), np.degrees(delta_mu_tau)]
colors = ['orange', 'green', 'blue']

bars = ax2.bar(range(len(formulas)), asymmetries, color=colors, alpha=0.7, edgecolor='black')

for i, (bar, val) in enumerate(zip(bars, asymmetries)):
    ax2.text(i, val + 0.2, f'{val:.2f}°', ha='center', va='bottom', fontsize=12, fontweight='bold')

ax2.set_xticks(range(len(formulas)))
ax2.set_xticklabels(formulas, fontsize=11)
ax2.set_ylabel('δ_μ - δ_τ (degrees)', fontsize=12)
ax2.set_title('μ-τ Asymmetry: Formula Comparison', fontsize=14)
ax2.grid(True, alpha=0.3, axis='y')

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_8_4_4_issue2_geometric_asymmetry.png', dpi=150)
print("Plot saved to: verification/plots/prop_8_4_4_issue2_geometric_asymmetry.png")

# ============================================================================
# CONCLUSION
# ============================================================================

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)

print("""
The document's geometric asymmetry formula δ_μ - δ_τ = λ/√2 requires justification.

FINDING: First-principles derivation from hexagonal geometry gives √3λ² ≈ 5°,
not λ/√2 ≈ 9.1°.

POSSIBLE RESOLUTIONS:

1. ACCEPT λ/√2 as phenomenological:
   - The formula can be justified if the VEV direction couples to the
     2-3 sector with strength λ and the projection factor 1/√2 comes
     from maximal atmospheric mixing in TBM.
   - This is plausible but requires explicit derivation.

2. USE √3λ² from first principles:
   - This is derived directly from hexagonal geometry + VEV direction.
   - But it gives a much smaller asymmetry (~5° vs ~9°).

3. REFINE the model:
   - The actual asymmetry may involve additional factors not captured
     in either simple formula.
   - A full calculation using the PMNS matrix structure is needed.

RECOMMENDATION:
The document should either:
(a) Provide a rigorous derivation of δ_μ - δ_τ = λ/√2, or
(b) Use the first-principles formula √3λ² and adjust the total prediction.

Impact on θ₂₃:
- With λ/√2: δθ₂₃^(geo) = 3.7° (document value)
- With √3λ²: δθ₂₃^(geo) = 2.2° (first-principles)

This affects the total prediction by about 1.5°.
""")

plt.show()
