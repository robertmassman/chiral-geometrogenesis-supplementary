"""
Proposition 0.0.26: Coefficient Gap Analysis — Path Forward Investigation
==========================================================================

Investigating whether other framework propositions provide insight into the
13% gap between unitarity-derived (3.54) and framework ansatz (4) coefficients.

Key patterns from other propositions:
- Prop 0.0.21: exp(1/4) = exp(1/dim(adj_EW)) = "survival fraction" of Higgs d.o.f.
- Prop 0.0.27: λ = 1/8 = (1/dim(adj_EW)) × (1/2) = (1/4) × (1/2)
- Prop 0.0.17d: Λ_QCD = 4πf_π (strong coupling NDA)

Question: Is there a "survival fraction" or geometric factor that bridges the gap?
"""

import numpy as np
import matplotlib.pyplot as plt

# Physical constants
v_H = 246.22  # GeV
f_pi = 0.0921  # GeV
dim_adj_EW = 4
dim_adj_QCD = 8

print("="*70)
print("Proposition 0.0.26: Coefficient Gap Analysis")
print("="*70)

# ============================================================================
# SECTION 1: The Gap
# ============================================================================
print("\n" + "="*70)
print("SECTION 1: The Coefficient Gap")
print("="*70)

coef_unitarity = 2 * np.sqrt(np.pi)  # ≈ 3.545
coef_ansatz = 4.0  # dim(adj_EW)

gap_ratio = coef_ansatz / coef_unitarity
gap_percent = (coef_ansatz - coef_unitarity) / coef_unitarity * 100

print(f"\nUnitarity-derived coefficient: 2√π = {coef_unitarity:.4f}")
print(f"Framework ansatz coefficient:  {coef_ansatz:.1f}")
print(f"Ratio (ansatz/unitarity):      {gap_ratio:.4f}")
print(f"Gap:                           {gap_percent:.1f}%")

# ============================================================================
# SECTION 2: Pattern from Prop 0.0.21 (exp(1/4) factor)
# ============================================================================
print("\n" + "="*70)
print("SECTION 2: Pattern from Proposition 0.0.21")
print("="*70)

# In Prop 0.0.21, v_H = √σ × exp(1/4 + 120/(2π²))
# The factor exp(1/4) is RIGOROUSLY DERIVED as the "survival fraction":
# - Total Higgs d.o.f. = 4 (complex doublet)
# - Physical Higgs d.o.f. = 1 (after Goldstones eaten)
# - Survival fraction = 1/4
# - Factor = exp(1/4) = 1.284

survival_fraction = 1 / dim_adj_EW  # = 1/4
exp_survival = np.exp(survival_fraction)

print(f"\nFrom Prop 0.0.21:")
print(f"  Survival fraction: n_physical/n_total = 1/{dim_adj_EW} = {survival_fraction:.4f}")
print(f"  exp(1/{dim_adj_EW}) = {exp_survival:.4f}")

# ============================================================================
# SECTION 3: Pattern from Prop 0.0.27 (λ = 1/8)
# ============================================================================
print("\n" + "="*70)
print("SECTION 3: Pattern from Proposition 0.0.27")
print("="*70)

# In Prop 0.0.27, λ = 1/8 (Higgs quartic) is derived from:
# Method 1: n_vertices of stella octangula = 8
# Method 2: λ = (1/dim(adj_EW)) × (1/2) = (1/4) × (1/2) = 1/8
#           where 1/2 is the "survival" factor (1 physical Higgs out of 2 doublet components)

lambda_higgs = 1 / 8
lambda_decomposed = (1 / dim_adj_EW) * (1 / 2)  # (1/4) × (1/2)

print(f"\nFrom Prop 0.0.27:")
print(f"  λ = 1/{8} = {lambda_higgs:.4f}")
print(f"  λ = (1/{dim_adj_EW}) × (1/2) = {lambda_decomposed:.4f}")
print(f"  Key factor: 1/2 = n_physical_components / n_doublet_components")

# ============================================================================
# SECTION 4: Mathematical Relationships
# ============================================================================
print("\n" + "="*70)
print("SECTION 4: Mathematical Relationships")
print("="*70)

# Strong coupling (QCD): 4π
# Unitarity (any coupling): 2√π
# Framework ansatz (weak coupling): 4

factor_strong = 4 * np.pi  # ≈ 12.57
factor_unitarity = 2 * np.sqrt(np.pi)  # ≈ 3.54
factor_weak = 4.0

print(f"\nCutoff enhancement factors (Λ = factor × f or v):")
print(f"  Strong coupling (QCD NDA):   4π = {factor_strong:.4f}")
print(f"  Unitarity (any coupling):    2√π = {factor_unitarity:.4f}")
print(f"  Framework ansatz (weak):     dim(adj) = {factor_weak:.1f}")

# Ratios
ratio_strong_unitarity = factor_strong / factor_unitarity
ratio_ansatz_unitarity = factor_weak / factor_unitarity

print(f"\nRatios:")
print(f"  Strong / Unitarity:  4π / 2√π = 2√π = {ratio_strong_unitarity:.4f}")
print(f"  Ansatz / Unitarity:  4 / 2√π = 2/√π = {ratio_ansatz_unitarity:.4f}")

# Key mathematical identity
print(f"\nKey identities:")
print(f"  4π / 4 = π = {np.pi:.4f}")
print(f"  2√π / 2 = √π = {np.sqrt(np.pi):.4f}")
print(f"  4 / 2√π = 2/√π = √(4/π) = {np.sqrt(4/np.pi):.4f}")

# ============================================================================
# SECTION 5: Candidate Bridging Factors
# ============================================================================
print("\n" + "="*70)
print("SECTION 5: Candidate Bridging Factors")
print("="*70)

# We need a factor F such that: 2√π × F = 4
# F = 4 / (2√π) = 2/√π ≈ 1.128

F_needed = factor_weak / factor_unitarity

print(f"\nFactor F needed to bridge gap: F = 4/(2√π) = 2/√π = {F_needed:.4f}")

# Check against various geometric/physics factors
candidates = {
    "exp(1/dim(adj))": np.exp(1/dim_adj_EW),  # From Prop 0.0.21
    "√(dim(adj)/π)": np.sqrt(dim_adj_EW/np.pi),  # Geometric candidate
    "2/√π": 2/np.sqrt(np.pi),  # Exact
    "exp(1/8)": np.exp(1/8),  # From Prop 0.0.27 (λ = 1/8)
    "√(4/π)": np.sqrt(4/np.pi),  # Same as 2/√π
    "4/(2+π)": 4/(2+np.pi),  # Random test
    "ln(2)": np.log(2),  # Simple factor
    "1 + 1/8": 1 + 1/8,  # Small correction from λ
}

print(f"\nCandidate factors vs required F = {F_needed:.4f}:")
print("-" * 50)
for name, value in candidates.items():
    match = abs(value - F_needed) / F_needed * 100
    status = "✅" if match < 1 else ("⚠️" if match < 10 else "❌")
    print(f"  {name:25s}: {value:.4f} ({match:.1f}% off) {status}")

# ============================================================================
# SECTION 6: Potential Derivation Path
# ============================================================================
print("\n" + "="*70)
print("SECTION 6: Potential Derivation Paths")
print("="*70)

print("""
Path A: "Survival Fraction" Correction (from Prop 0.0.21)
---------------------------------------------------------
In Prop 0.0.21, exp(1/4) corrects the bare formula for v_H.

Could a similar factor correct the unitarity result?
  Λ_corrected = Λ_unitarity × correction
  4 v_H = 2√π v_H × (2/√π)

The correction factor 2/√π = √(4/π) would need physical justification.

Path B: Weak-Coupling Limit of NDA
----------------------------------
Strong coupling: Λ = 4π f (NDA)
Weak coupling:   Λ = ? f

If there's a smooth interpolation:
  Λ(α) = 4π f × g(α)

where g(1) = 1 (strong) and g(0) = 1/π (weak → Λ = 4f)

The function g(α) = 1/(1 + (π-1)×(1-α)) would interpolate smoothly.

Path C: Higgs Doublet Structure
-------------------------------
The Higgs doublet has 4 components, but only 1 survives as physical Higgs.
In unitarity analysis, we use N = 4 gauge bosons.

What if the "effective N" includes a Higgs correction?
  N_eff = 4 × (survival factor)

With survival factor = 1, we get Λ = 2√π v_H.
Need survival factor to give Λ = 4 v_H.

Path D: Accept as Framework Ansatz
----------------------------------
Most honest approach:
1. Unitarity rigorously gives: Λ ≈ 2√π v_H ≈ 872 GeV
2. Framework chooses: Λ = dim(adj_EW) × v_H = 985 GeV
3. The 13% gap is within EFT uncertainty
4. The choice provides clean gauge-algebraic formula
""")

# ============================================================================
# SECTION 7: Connection to Prop 0.0.27 (Higgs Mass)
# ============================================================================
print("\n" + "="*70)
print("SECTION 7: Cross-Check with Prop 0.0.27")
print("="*70)

# From Prop 0.0.27: m_H = v_H/2 × (1 + radiative)
# This uses λ = 1/8 = (1/dim(adj)) × (1/2)

# If we apply similar logic to the cutoff:
# Λ = dim(adj) × v_H × (some factor)

# Check: What factor would give the unitarity result?
factor_to_unitarity = coef_unitarity / coef_ansatz  # ≈ 0.886

print(f"\nIf Λ = dim(adj) × v_H × F_correction:")
print(f"  To match unitarity: F = 2√π/4 = √π/2 = {factor_to_unitarity:.4f}")

# This is the RECIPROCAL of what we need if we start from unitarity
# Starting from unitarity: 2√π × (2/√π) = 4
# Starting from ansatz:    4 × (√π/2) = 2√π

# The relationship to λ = 1/8:
print(f"\nRelationship to Higgs quartic λ = 1/8:")
print(f"  λ = 1/8 = 0.125")
print(f"  1 - λ = 7/8 = 0.875")
print(f"  √(1 - λ) = √(7/8) = {np.sqrt(7/8):.4f}")
print(f"  √π/2 = {np.sqrt(np.pi)/2:.4f}")
print(f"  Match: {abs(np.sqrt(7/8) - np.sqrt(np.pi)/2)/np.sqrt(np.pi)*2*100:.1f}% difference")

# Hmm, √(7/8) ≈ 0.935, not √π/2 ≈ 0.886

# ============================================================================
# SECTION 8: Summary
# ============================================================================
print("\n" + "="*70)
print("SECTION 8: Summary and Recommendation")
print("="*70)

print("""
FINDINGS:
=========

1. The 13% gap between unitarity (2√π ≈ 3.54) and ansatz (4) is REAL.

2. The factor needed to bridge the gap is 2/√π ≈ 1.128.

3. This factor does NOT match:
   - exp(1/4) = 1.284 (from Prop 0.0.21) — 14% off
   - Any simple geometric factor I tested

4. Patterns from other propositions:
   - Prop 0.0.21 uses exp(1/dim) as "survival fraction" — rigorously derived
   - Prop 0.0.27 uses (1/dim) × (1/2) for λ — geometric interpretation
   - Neither directly gives the needed 2/√π factor

RECOMMENDATION:
===============

Option A (Preferred): Accept the gap as theoretical uncertainty
   - State clearly: Unitarity gives 2√π v_H ≈ 872 GeV (rigorous)
   - Framework adopts 4 v_H = 985 GeV as ansatz
   - Central value: 930 ± 55 GeV (spans the range)
   - This is HONEST about the derivation status

Option B: Future work to derive 2/√π factor
   - The factor 2/√π = √(4/π) might have a physical origin
   - Possibly related to massive vs massless gauge boson counting
   - Or to the weak-coupling limit of NDA

Option C: Reframe the coefficient as "~4" rather than "exactly 4"
   - The coefficient is 4 ± 0.5 (covering 3.5-4.5)
   - This spans the unitarity result and preserves the dim(adj) interpretation
""")

# ============================================================================
# SECTION 9: Visualization
# ============================================================================
print("\n" + "="*70)
print("SECTION 9: Generating Comparison Plot")
print("="*70)

fig, axes = plt.subplots(2, 2, figsize=(14, 10))

# Plot 1: Scale comparison
ax1 = axes[0, 0]
scales = {
    'QCD: 4πf_π': 4 * np.pi * 0.0921 * 1000,  # in GeV
    'EW: 2√π v_H\n(unitarity)': 2 * np.sqrt(np.pi) * v_H,
    'EW: 4 v_H\n(ansatz)': 4 * v_H,
    'LQT bound': 1502,
}

bars = ax1.barh(list(scales.keys()), list(scales.values()),
                color=['green', 'blue', 'red', 'purple'])
ax1.set_xlabel('Cutoff [GeV]', fontsize=12)
ax1.set_title('EFT Cutoff Comparison Across Regimes', fontsize=12)
for i, (name, val) in enumerate(scales.items()):
    ax1.text(val + 20, i, f'{val:.0f} GeV', va='center', fontsize=10)
ax1.set_xlim(0, 2000)
ax1.grid(True, alpha=0.3, axis='x')

# Plot 2: Coefficient as function of coupling
ax2 = axes[0, 1]
alpha_values = np.linspace(0.01, 1, 100)

# Hypothetical interpolation formulas
coef_NDA = 4 * np.pi * np.ones_like(alpha_values)  # Strong coupling (constant)
coef_unitarity_line = 2 * np.sqrt(np.pi) * np.ones_like(alpha_values)  # Unitarity
coef_ansatz_line = 4 * np.ones_like(alpha_values)  # Ansatz

# An interpolation that goes 4π → 4 as α → 0
coef_interp = 4 * np.pi * (1 / (1 + (np.pi - 1) * (1 - alpha_values)))

ax2.plot(alpha_values, coef_NDA, 'g--', label='Strong (4π)', linewidth=2)
ax2.plot(alpha_values, coef_unitarity_line, 'b-', label='Unitarity (2√π)', linewidth=2)
ax2.plot(alpha_values, coef_ansatz_line, 'r-', label='Ansatz (dim(adj)=4)', linewidth=2)
ax2.plot(alpha_values, coef_interp, 'k:', label='Interpolation (4π→4)', linewidth=2)
ax2.axvline(x=0.034, color='orange', linestyle='--', label='EW: α₂ ≈ 0.034')
ax2.axvline(x=1.0, color='green', linestyle='--', alpha=0.5, label='QCD: α_s ~ 1')
ax2.set_xlabel('Coupling strength α', fontsize=12)
ax2.set_ylabel('Cutoff coefficient', fontsize=12)
ax2.set_title('Coefficient vs Coupling Strength', fontsize=12)
ax2.legend(loc='upper left', fontsize=9)
ax2.set_xlim(0, 1.1)
ax2.set_ylim(0, 15)
ax2.grid(True, alpha=0.3)

# Plot 3: Factor comparison
ax3 = axes[1, 0]
factor_names = ['Strong\n4π/4', 'Unitarity\n2√π/4', 'Ansatz\n4/4', 'Gap\n2/√π']
factor_values = [np.pi, np.sqrt(np.pi)/2, 1.0, 2/np.sqrt(np.pi)]
colors = ['green', 'blue', 'red', 'orange']

ax3.bar(factor_names, factor_values, color=colors)
ax3.axhline(y=1.0, color='black', linestyle='--', linewidth=1)
ax3.set_ylabel('Factor relative to dim(adj)=4', fontsize=12)
ax3.set_title('Relative Factors: Why 4 vs 2√π vs 4π?', fontsize=12)
for i, v in enumerate(factor_values):
    ax3.text(i, v + 0.05, f'{v:.3f}', ha='center', fontsize=10)
ax3.grid(True, alpha=0.3, axis='y')

# Plot 4: Prop patterns
ax4 = axes[1, 1]
prop_factors = {
    'Prop 0.0.17d\nΛ_QCD = 4πf_π': 4 * np.pi,
    'Prop 0.0.21\nexp(1/4)': np.exp(0.25),
    'Prop 0.0.26\nunitarity': 2 * np.sqrt(np.pi),
    'Prop 0.0.26\nansatz': 4.0,
    'Prop 0.0.27\nλ⁻¹ = 8': 8.0,
}

bars = ax4.barh(list(prop_factors.keys()), list(prop_factors.values()),
                color=['green', 'purple', 'blue', 'red', 'cyan'])
ax4.set_xlabel('Characteristic Number', fontsize=12)
ax4.set_title('Key Numbers Across Propositions', fontsize=12)
for i, v in enumerate(prop_factors.values()):
    ax4.text(v + 0.2, i, f'{v:.3f}', va='center', fontsize=10)
ax4.grid(True, alpha=0.3, axis='x')

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_0_0_26_coefficient_analysis.png',
            dpi=150, bbox_inches='tight')
print("Saved: verification/plots/prop_0_0_26_coefficient_analysis.png")
plt.close()

print("\n" + "="*70)
print("ANALYSIS COMPLETE")
print("="*70)
