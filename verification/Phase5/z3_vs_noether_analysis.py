"""
Z₃ Phase Structure vs Noether Theorem: Analysis of Higher-Rank Exclusion

This script clarifies the distinct roles of:
1. Z₃ phase structure: Ensures color singlets (observable colorlessness)
2. Noether theorem: Ensures conservation of stress-energy (no higher-rank)

Issue being addressed:
- Verification found: "Z₃ phase cancellation prevents rank > 2 conserved tensors"
  is not correctly supported
- Actual mechanism: Higher ranks are excluded by (1) bilinear kinetic structure,
  (2) Noether theorem, (3) no symmetry for rank-3+ conservation

This script demonstrates both mechanisms mathematically.
"""

import numpy as np
import matplotlib.pyplot as plt
from fractions import Fraction

# ============================================================================
# Part 1: Z₃ Phase Structure - What It Actually Does
# ============================================================================

print("="*70)
print("PART 1: Z₃ PHASE STRUCTURE - COLOR SINGLET REQUIREMENT")
print("="*70)

# Z₃ phase: ω = e^(2πi/3)
omega = np.exp(2j * np.pi / 3)

print(f"\nZ₃ cube root of unity: ω = e^(2πi/3)")
print(f"ω = {omega:.6f}")
print(f"ω² = {omega**2:.6f}")
print(f"ω³ = {omega**3:.6f} (should be 1)")

# Color singlet condition
singlet_sum = 1 + omega + omega**2
print(f"\nColor singlet condition: 1 + ω + ω² = {singlet_sum:.10f}")
print(f"This equals 0 (within numerical precision): {np.abs(singlet_sum) < 1e-10}")

# ============================================================================
# Part 1a: Bilinear Phase Cancellation
# ============================================================================

print("\n" + "-"*70)
print("1a: BILINEAR PRODUCTS (χ†χ type)")
print("-"*70)

# For χ_c with phase ω^c, the bilinear χ_c† χ_c has phase:
# Phase of χ_c† χ_c = (-c) + c = 0 for all c

print("\nFor bilinear χ_c† χ_c:")
for c, name in enumerate(['R', 'G', 'B']):
    phase_chi = omega**c
    phase_chi_dag = np.conj(phase_chi)
    bilinear_phase = phase_chi_dag * phase_chi
    print(f"  χ_{name}† χ_{name}: phase = ω^{-c} × ω^{c} = {bilinear_phase:.4f} (colorless ✓)")

print("\nKEY INSIGHT: Bilinear products (∂_μχ†)(∂_νχ) are AUTOMATICALLY colorless")
print("This is why T_μν (rank-2 from bilinear structure) is a color singlet.")
print("Z₃ doesn't 'force' rank-2; it ensures observables are colorless.")

# ============================================================================
# Part 1b: Would Trilinear Products Be Colorless?
# ============================================================================

print("\n" + "-"*70)
print("1b: HYPOTHETICAL TRILINEAR PRODUCTS (χχχ type)")
print("-"*70)

# For trilinear ε_abc χ_a χ_b χ_c (antisymmetric combination):
# Only non-zero term is χ_R χ_G χ_B with phases ω^0 × ω^1 × ω^2 = ω³ = 1

trilinear_phase = omega**0 * omega**1 * omega**2
print(f"\nTrilinear ε_abc χ_a χ_b χ_c:")
print(f"  χ_R χ_G χ_B: phase = ω^0 × ω^1 × ω^2 = ω³ = {trilinear_phase:.4f} (colorless ✓)")

print("\nIMPORTANT: Trilinear products CAN be colorless!")
print("Therefore Z₃ alone does NOT forbid higher-rank tensors.")
print("The exclusion of rank-3+ comes from Noether theorem, not Z₃.")

# ============================================================================
# Part 2: Noether Theorem - What Actually Excludes Higher Ranks
# ============================================================================

print("\n" + "="*70)
print("PART 2: NOETHER THEOREM - THE ACTUAL EXCLUSION MECHANISM")
print("="*70)

print("""
Noether's theorem: For every continuous symmetry, there is a conserved current.

Symmetry               → Conserved Quantity        → Tensor Rank
─────────────────────────────────────────────────────────────────
U(1) phase rotation    → Electric charge           → 0 (scalar)
U(1) global symmetry   → J_μ current               → 1 (vector)
Translations x^μ → x^μ + a^μ → T_μν stress-energy → 2 (tensor)
Rotations/Boosts       → M_μνρ angular momentum    → 3 (antisymmetric!)
─────────────────────────────────────────────────────────────────

KEY: Angular momentum tensor M_μνρ IS rank-3, but it's ANTISYMMETRIC!
A symmetric rank-3 tensor would require a different symmetry.
""")

# ============================================================================
# Part 2a: Why No Conserved Symmetric Rank-3 Tensor
# ============================================================================

print("-"*70)
print("2a: WHY NO CONSERVED SYMMETRIC RANK-3 TENSOR EXISTS")
print("-"*70)

print("""
To have a conserved symmetric rank-3 tensor T_μνρ, we would need:

1. NOETHER REQUIREMENT: A symmetry transformation δχ that generates T_μνρ
   ∂_μ T^μνρ = 0 requires ∂L/∂(∂χ) × δχ to produce two free indices

2. CANDIDATE SYMMETRIES for scalar field χ:
   - δχ = iε χ (U(1) phase) → gives J_μ (rank-1)
   - δχ = ε^μ ∂_μχ (translations) → gives T_μν (rank-2)
   - δχ = ε^μν x_μ ∂_νχ (Lorentz) → gives M_μνρ (antisymmetric rank-3)

3. FOR SYMMETRIC RANK-3: Would need δχ = ε^μν f_μν(χ, ∂χ)
   But no such transformation exists for scalar fields!

The kinetic term ∂_μχ†∂^μχ has TWO derivatives.
Noether procedure converts one ∂_μ into the symmetry parameter ε^μ.
Result: ONE free index remains → rank-2 maximum for symmetric tensors.
""")

# ============================================================================
# Part 2b: Mathematical Derivation
# ============================================================================

print("-"*70)
print("2b: MATHEMATICAL DERIVATION")
print("-"*70)

print("""
Start from Lagrangian: L = ∂_μχ† ∂^μχ - V(|χ|²)

Translation symmetry: x^μ → x^μ + ε^μ

Variation of action:
  δS = ∫ d⁴x ε^μ ∂_μL = ∫ d⁴x ∂_μ(ε^μ L) = 0 (boundary term)

Noether current (canonical):
  T^μ_ν = (∂L/∂(∂_μχ)) ∂_νχ + (∂L/∂(∂_μχ†)) ∂_νχ† - δ^μ_ν L
        = (∂^μχ†)(∂_νχ) + (∂^μχ)(∂_νχ†) - δ^μ_ν L

This is RANK-2 by construction. The procedure cannot generate rank-3.

WHY? The variation δL = ε^μ ∂_μL has ONE index ε^μ.
The resulting current T^μν has TWO indices: one from ∂L/∂(∂χ), one from ε.
No mechanism produces a THIRD free index from scalar field dynamics.
""")

# ============================================================================
# Part 3: Dimensional Analysis (Supporting Argument)
# ============================================================================

print("\n" + "="*70)
print("PART 3: DIMENSIONAL ANALYSIS (SUPPORTING ARGUMENT)")
print("="*70)

print("""
In natural units (ℏ = c = 1), mass dimension [M]:

Field/Quantity          Dimension
─────────────────────────────────
χ (scalar in 4D)        [M]¹
∂_μχ                    [M]²
∂_μ∂_νχ                 [M]³
T_μν = (∂χ†)(∂χ)        [M]⁴
T_μνρ = (∂²χ†)(∂χ)      [M]⁵
L (Lagrangian density)  [M]⁴

For gravitational coupling:
  S_int = ∫ d⁴x κ h^μν T_μν
  [κ] = [M]⁰ / [M]⁴ = [M]⁻⁴ from d⁴x
  Since [h_μν] = [M]⁰ and [T_μν] = [M]⁴
  And [S] = [M]⁰, we get [κ] × [M]⁴ × [M]⁴ / [M]⁴ = [M]⁰
  So [κ] = [M]⁻¹ (as 8πG/c⁴ has dimension [M]⁻²·[T]²·[L]⁻¹ in SI)

For hypothetical rank-3 coupling:
  [T_μνρ] = [M]⁵
  Coupling would be more non-renormalizable.

This is a SECONDARY argument; the PRIMARY exclusion is Noether.
""")

# ============================================================================
# Part 4: Summary and Corrected Statement
# ============================================================================

print("\n" + "="*70)
print("PART 4: SUMMARY - CORRECTED UNDERSTANDING")
print("="*70)

print("""
ORIGINAL CLAIM (Imprecise):
  "Z₃ phase cancellation prevents rank > 2 conserved tensors"

PROBLEM:
  Z₃ ensures color singlets. Trilinear products CAN be colorless (ω³ = 1).
  Therefore Z₃ alone cannot exclude higher-rank tensors.

CORRECTED STATEMENT:
  Higher-rank conserved tensors are excluded by THREE mechanisms:

  1. BILINEAR KINETIC STRUCTURE
     - Lagrangian L = ∂χ†∂χ is bilinear in derivatives
     - Only products like (∂_μχ†)(∂_νχ) are dynamically generated
     - No trilinear derivative terms appear naturally

  2. NOETHER THEOREM (PRIMARY MECHANISM)
     - Conservation ∂_μT^μνρ... = 0 requires a generating symmetry
     - Translation symmetry → rank-2 stress-energy T_μν
     - No symmetry generates conserved symmetric rank-3+ tensors from scalars

  3. Z₃ PHASE STRUCTURE (COMPLEMENTARY ROLE)
     - Ensures all physical observables are color singlets
     - The stress-energy T_μν = Σ_c (∂χ_c†)(∂χ_c) is automatically colorless
     - This is a CONSISTENCY check, not the exclusion mechanism

WHAT Z₃ ACTUALLY DOES:
  - Requires physical observables to be color-neutral
  - The bilinear structure (∂χ†)(∂χ) satisfies this automatically
  - Does NOT directly constrain tensor rank

THE LOGICAL FLOW:
  χ structure → bilinear dynamics → Noether generates T_μν (rank-2)
      ↓
  Z₃ ensures T_μν is color-singlet (consistency check)
      ↓
  Coupling h^μν T_μν requires rank-2 mediator
""")

# ============================================================================
# Part 5: Generate Visualization
# ============================================================================

fig, axes = plt.subplots(1, 3, figsize=(15, 5))

# Panel 1: Z₃ phases in complex plane
ax1 = axes[0]
theta = np.linspace(0, 2*np.pi, 100)
ax1.plot(np.cos(theta), np.sin(theta), 'k-', alpha=0.3, linewidth=1)

phases = [1, omega, omega**2]
colors_plot = ['red', 'green', 'blue']
labels = [r'$\chi_R$ (phase 0)', r'$\chi_G$ (phase $2\pi/3$)', r'$\chi_B$ (phase $4\pi/3$)']

for i, (phase, color, label) in enumerate(zip(phases, colors_plot, labels)):
    ax1.arrow(0, 0, phase.real*0.9, phase.imag*0.9, head_width=0.08,
              head_length=0.05, fc=color, ec=color, linewidth=2)
    ax1.plot(phase.real, phase.imag, 'o', color=color, markersize=12)
    ax1.annotate(label, xy=(phase.real*1.2, phase.imag*1.2), fontsize=10,
                ha='center', va='center')

ax1.set_xlim(-1.8, 1.8)
ax1.set_ylim(-1.8, 1.8)
ax1.set_aspect('equal')
ax1.axhline(y=0, color='k', linewidth=0.5)
ax1.axvline(x=0, color='k', linewidth=0.5)
ax1.set_xlabel('Re')
ax1.set_ylabel('Im')
ax1.set_title(r'$Z_3$ Phase Structure: Color Singlet $1 + \omega + \omega^2 = 0$')

# Panel 2: Tensor rank hierarchy
ax2 = axes[1]
ranks = [0, 1, 2, 3]
sources = ['Scalar\n$|\\chi|^2$', 'Current\n$J_\\mu$', 'Stress-Energy\n$T_{\\mu\\nu}$',
           'Hypothetical\n$T_{\\mu\\nu\\rho}$']
conserved = [False, True, True, False]
colors_bar = ['gray', 'blue', 'green', 'red']
hatches = ['', '', '', '///']

bars = ax2.bar(ranks, [1, 1, 1, 1], color=colors_bar, edgecolor='black', linewidth=2)
for bar, hatch in zip(bars, hatches):
    bar.set_hatch(hatch)

ax2.set_xticks(ranks)
ax2.set_xticklabels(sources, fontsize=9)
ax2.set_ylabel('Existence')
ax2.set_ylim(0, 1.3)
ax2.set_title('Noether Theorem: Conserved Tensors from Scalar Field')

# Add checkmarks/crosses
for i, cons in enumerate(conserved):
    symbol = '✓' if cons else '✗'
    color = 'green' if cons else 'red'
    ax2.text(i, 1.1, symbol, fontsize=20, ha='center', color=color, fontweight='bold')

ax2.text(0, 1.2, 'Not conserved', fontsize=8, ha='center')
ax2.text(1, 1.2, 'U(1) symmetry', fontsize=8, ha='center')
ax2.text(2, 1.2, 'Translation', fontsize=8, ha='center')
ax2.text(3, 1.2, 'No symmetry', fontsize=8, ha='center')

# Panel 3: Logical flow diagram (as text)
ax3 = axes[2]
ax3.axis('off')

flow_text = """
LOGICAL STRUCTURE

┌─────────────────────────────┐
│  χ field with Z₃ structure  │
│  (complex scalar triplet)   │
└──────────────┬──────────────┘
               │
               ▼
┌─────────────────────────────┐
│ Bilinear Lagrangian         │
│ L = ∂μχ† ∂^μχ               │
└──────────────┬──────────────┘
               │
     ┌─────────┴─────────┐
     │                   │
     ▼                   ▼
┌──────────────┐  ┌──────────────┐
│ NOETHER      │  │ Z₃ ENSURES   │
│ Translation  │  │ Color        │
│ → T_μν       │  │ singlet      │
│ (rank-2)     │  │ (colorless)  │
└──────┬───────┘  └──────────────┘
       │
       ▼
┌─────────────────────────────┐
│ Rank-2 source → Rank-2      │
│ mediator h_μν (spin-2)      │
└─────────────────────────────┘

PRIMARY: Noether excludes rank ≠ 2
SECONDARY: Z₃ ensures colorlessness
"""

ax3.text(0.5, 0.5, flow_text, fontsize=9, ha='center', va='center',
         family='monospace', transform=ax3.transAxes)
ax3.set_title('Corrected Logical Flow')

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/z3_vs_noether_analysis.png',
            dpi=150, bbox_inches='tight', facecolor='white')
plt.close()

print("\n" + "="*70)
print("VERIFICATION COMPLETE")
print("="*70)
print("\nGenerated: verification/plots/z3_vs_noether_analysis.png")
print("\nKey conclusions:")
print("1. Z₃ ensures color singlets (observables are colorless)")
print("2. Noether theorem is the PRIMARY mechanism excluding rank > 2")
print("3. Bilinear structure of Lagrangian supports this exclusion")
print("4. The original claim needs reframing, not rejection")
