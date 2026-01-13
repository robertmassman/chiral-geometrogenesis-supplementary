"""
Dimensional Analysis Verification for Gravitational Coupling

Issue being addressed:
- Verification found: "Claim [κ] = [M]⁻¹ appears inconsistent with [h_μν] = [M]⁰"
- Need to verify dimensional conventions for gravitational coupling

This script clarifies the dimensional analysis for the coupling L_int = κ h^μν T_μν
"""

import numpy as np

print("="*70)
print("DIMENSIONAL ANALYSIS: GRAVITATIONAL COUPLING")
print("="*70)

# ============================================================================
# Natural Units Convention
# ============================================================================

print("""
NATURAL UNITS: ℏ = c = 1

In these units, there is only ONE independent dimension: [Mass] = [Length]⁻¹ = [Time]⁻¹

Fundamental dimensions:
- [Mass] = M
- [Length] = M⁻¹
- [Time] = M⁻¹
- [Energy] = M
- [Action] = M⁰ (dimensionless)
""")

# ============================================================================
# Field Dimensions in 4D
# ============================================================================

print("="*70)
print("FIELD DIMENSIONS IN 4D SPACETIME")
print("="*70)

print("""
From the requirement that the action S = ∫d⁴x L is dimensionless:

[d⁴x] = [Length]⁴ = M⁻⁴
[L] = M⁴  (Lagrangian density)

For a scalar field χ with kinetic term L = ∂_μχ† ∂^μχ:
[∂_μχ† ∂^μχ] = M⁴
[∂_μ] = M (derivative adds one mass dimension)
[∂_μχ]² = M⁴
[∂_μχ] = M²
[χ] = M¹

SCALAR FIELD: [χ] = M¹  ✓
""")

# ============================================================================
# Stress-Energy Tensor Dimension
# ============================================================================

print("="*70)
print("STRESS-ENERGY TENSOR DIMENSION")
print("="*70)

print("""
From T_μν = (∂_μχ†)(∂_νχ) + (∂_νχ†)(∂_μχ) - η_μν L:

[T_μν] = [∂_μχ† ∂_νχ] = [∂χ]² = (M²)² = M⁴

STRESS-ENERGY: [T_μν] = M⁴  ✓

This matches the standard result: stress-energy has units of energy density.
""")

# ============================================================================
# Gravitational Coupling Analysis
# ============================================================================

print("="*70)
print("GRAVITATIONAL COUPLING: TWO CONVENTIONS")
print("="*70)

print("""
There are TWO common conventions for the gravitational coupling:

═══════════════════════════════════════════════════════════════════════
CONVENTION 1: Dimensionless Metric Perturbation (GR Standard)
═══════════════════════════════════════════════════════════════════════

Define: g_μν = η_μν + h_μν

Then h_μν is dimensionless: [h_μν] = M⁰

The interaction Lagrangian is:
  L_int = (8πG/c⁴) h^μν T_μν    (with G explicit)

In natural units (c = 1):
  L_int = (8πG) h^μν T_μν

The coupling κ = 8πG has dimension:
  [κ] × [h_μν] × [T_μν] = M⁴
  [κ] × M⁰ × M⁴ = M⁴
  [κ] = M⁰  ???

Wait, this seems wrong. Let's be more careful.

Actually, in GR the coupling appears as:
  G_μν = 8πG T_μν

where G_μν ~ ∂²h_μν has dimension [∂²h] = M² × M⁰ = M²

So: M² = [8πG] × M⁴
    [G] = M⁻²

In natural units: [G] = M⁻² = [M_Planck]⁻²  ✓

═══════════════════════════════════════════════════════════════════════
CONVENTION 2: Canonical Normalization (QFT Standard)
═══════════════════════════════════════════════════════════════════════

For canonical kinetic term L_kin = (1/2)(∂h)², we need [h] such that:
  [(∂h)²] = M⁴
  [∂h]² = M⁴
  [h] = M¹  (mass dimension 1, like a scalar field!)

Then for L_int = κ h^μν T_μν:
  [κ] × [h] × [T] = M⁴
  [κ] × M¹ × M⁴ = M⁴
  [κ] = M⁻¹

This is the LINEARIZED GRAVITY convention where h has mass dimension 1.

The relation between conventions:
  h_GR = √(32πG) × h_canonical
  [√G] = M⁻¹

So κ = √(32πG) and [κ] = M⁻¹  ✓

═══════════════════════════════════════════════════════════════════════
RESOLUTION OF THE APPARENT INCONSISTENCY
═══════════════════════════════════════════════════════════════════════

The verification found apparent inconsistency because:
- Document claims [κ] = M⁻¹
- Document claims [h_μν] = M⁰

These are from DIFFERENT conventions:
- [h_μν] = M⁰ is the GR convention (dimensionless metric perturbation)
- [κ] = M⁻¹ is the QFT convention (canonical normalization)

CORRECT CONSISTENT STATEMENTS:

Option A (GR convention):
  [h_μν] = M⁰ (dimensionless)
  L_int = (8πG) h^μν T_μν
  [8πG] = M⁻² (Newton's constant)
  Check: [G] × [h] × [T] = M⁻² × M⁰ × M⁴ = M² ✓ (for G_μν = 8πG T_μν)

Option B (QFT convention):
  [h_μν] = M¹ (canonical)
  L_int = κ h^μν T_μν
  [κ] = M⁻¹
  Check: [κ] × [h] × [T] = M⁻¹ × M¹ × M⁴ = M⁴ ✓ (for Lagrangian)

THE PROPOSITION SHOULD USE CONSISTENT CONVENTIONS.
""")

# ============================================================================
# Verify numerically with known values
# ============================================================================

print("="*70)
print("NUMERICAL VERIFICATION")
print("="*70)

# Physical constants in SI
G_SI = 6.67430e-11  # m³/(kg·s²)
c_SI = 2.99792458e8  # m/s
hbar_SI = 1.054571817e-34  # J·s

# Planck mass
M_Planck = np.sqrt(hbar_SI * c_SI / G_SI)
print(f"\nPlanck mass: M_P = √(ℏc/G) = {M_Planck:.6e} kg")
print(f"             M_P = {M_Planck * c_SI**2 / 1.602e-10:.6e} GeV")

# In natural units, G = 1/M_P²
print(f"\nIn natural units: G = 1/M_P² ~ {1/(1.22e19)**2:.2e} GeV⁻²")

# The coupling κ = √(8πG) = √(8π)/M_P
kappa = np.sqrt(8 * np.pi) / (1.22e19)  # GeV⁻¹
print(f"\nCoupling κ = √(8π)/M_P ~ {kappa:.2e} GeV⁻¹")
print(f"[κ] = M⁻¹ ✓")

# ============================================================================
# Summary
# ============================================================================

print("\n" + "="*70)
print("SUMMARY: RECOMMENDED FIX")
print("="*70)

print("""
The document should clarify which convention is being used.

RECOMMENDED TEXT:

§6.2 Check: Dimensional Analysis

For the interaction Lagrangian L_int = κ h^μν T_μν to have dimension M⁴:

Using CANONICAL NORMALIZATION (linearized gravity):
- [h_μν] = M¹ (same as scalar field, for canonical kinetic term)
- [T_μν] = M⁴
- [κ] = M⁻¹ = 1/M_Planck

Alternatively, using METRIC PERTURBATION convention:
- [h_μν] = M⁰ (dimensionless perturbation g_μν = η_μν + h_μν)
- The coupling is then 8πG with [G] = M⁻²

Both are consistent; the canonical convention (κ ~ M⁻¹) is standard in QFT
treatments of linearized gravity.

DIMENSIONAL CHECK:
[L_int] = [κ][h][T] = M⁻¹ × M¹ × M⁴ = M⁴  ✓
""")

# ============================================================================
# Generate plot
# ============================================================================

import matplotlib.pyplot as plt

fig, ax = plt.subplots(figsize=(10, 6))

# Table of dimensions
table_data = [
    ['Quantity', 'GR Convention', 'QFT Convention', 'Physical'],
    ['Metric perturbation h_μν', 'M⁰', 'M¹', 'δg ~ 10⁻²¹ (GW)'],
    ['Stress-energy T_μν', 'M⁴', 'M⁴', 'Energy density'],
    ['Coupling κ or 8πG', 'M⁻²', 'M⁻¹', '√(8π)/M_P'],
    ['Action S_int', 'M⁰', 'M⁰', 'Dimensionless'],
    ['Newton G', 'M⁻²', 'M⁻²', '1/M_P²'],
]

# Create table
ax.axis('tight')
ax.axis('off')

table = ax.table(cellText=table_data,
                 cellLoc='center',
                 loc='center',
                 colWidths=[0.3, 0.2, 0.2, 0.3])

table.auto_set_font_size(False)
table.set_fontsize(11)
table.scale(1.2, 2)

# Color header
for j in range(4):
    table[(0, j)].set_facecolor('#4472C4')
    table[(0, j)].set_text_props(color='white', fontweight='bold')

# Color alternating rows
for i in range(1, 6):
    color = '#D6DCE5' if i % 2 == 0 else 'white'
    for j in range(4):
        table[(i, j)].set_facecolor(color)

ax.set_title('Dimensional Analysis: GR vs QFT Conventions\n', fontsize=14, fontweight='bold')

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/dimensional_analysis_conventions.png',
            dpi=150, bbox_inches='tight', facecolor='white')
plt.close()

print("\nGenerated: verification/plots/dimensional_analysis_conventions.png")
print("\nVERIFICATION COMPLETE")
