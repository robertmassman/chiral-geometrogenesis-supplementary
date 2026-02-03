"""
Proposition 0.0.26: Rigorous Unitarity Bound Derivation for Electroweak Cutoff
================================================================================

This script provides a comprehensive analysis of the unitarity constraints on the
electroweak EFT cutoff, addressing the verification report's concern about the
gap between the elastic bound (~3.54 v_H) and the claimed EFT cutoff (4 v_H).

Key Questions Addressed:
1. What does elastic unitarity give? → 2√π v_H ≈ 3.54 v_H
2. What does inelastic unitarity give? → Derived here
3. Is the coefficient exactly 4 or ~3.5-4 with uncertainty?
4. How does the multi-channel analysis work?

References:
- Lee, Quigg, Thacker (1977): PRD 16, 1519
- Chanowitz, Gaillard (1985): NPB 261, 379
- Grzadkowski et al. (2010): JHEP 1010, 085 (Warsaw basis)

Author: Verification script for Proposition 0.0.26
Date: 2026-02-02
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy import optimize

# Physical constants
v_H = 246.22  # GeV, Higgs VEV
G_F = 1.1663788e-5  # GeV^-2, Fermi constant
m_W = 80.377  # GeV
m_Z = 91.188  # GeV
g2 = 0.6527  # SU(2) coupling
alpha_2 = g2**2 / (4 * np.pi)

print("="*70)
print("Proposition 0.0.26: Rigorous Unitarity Bound Analysis")
print("="*70)

# ============================================================================
# PART 1: Standard Lee-Quigg-Thacker Analysis
# ============================================================================
print("\n" + "="*70)
print("PART 1: Lee-Quigg-Thacker Unitarity Bound")
print("="*70)

# The J=0 partial wave amplitude for W_L W_L → W_L W_L at high energy
# Using Goldstone equivalence theorem: W_L ≈ π (Goldstone boson)
#
# The tree-level amplitude for π⁺π⁻ → π⁺π⁻ at high energy is:
# M = s/v_H² + t/v_H² (ignoring Higgs exchange)
#
# The J=0 partial wave is:
# a_0 = 1/(32π) ∫_{-1}^{1} d(cosθ) M(s, cosθ)
#
# For M = s/v_H² (s-channel dominant):
# a_0 = s/(16π v_H²)

def partial_wave_amplitude(s, v_H):
    """J=0 partial wave amplitude for Goldstone scattering"""
    return s / (16 * np.pi * v_H**2)

# Elastic unitarity bound: |a_0| ≤ 1/2
# s/(16π v_H²) ≤ 1/2
# s ≤ 8π v_H²
# √s ≤ √(8π) v_H ≈ 5.01 v_H

Lambda_LQT_standard = np.sqrt(8 * np.pi) * v_H
print(f"\nStandard LQT bound (|a_0| ≤ 1/2):")
print(f"  Λ_LQT = √(8π) × v_H = {np.sqrt(8*np.pi):.4f} × {v_H:.2f} GeV")
print(f"  Λ_LQT = {Lambda_LQT_standard:.2f} GeV")

# However, this gives ~5 v_H, not the 1.5 TeV often quoted.
# The 1.5 TeV comes from a more careful treatment.

# ============================================================================
# PART 2: Full LQT Derivation with Proper Formula
# ============================================================================
print("\n" + "="*70)
print("PART 2: Full LQT Derivation")
print("="*70)

# The original Lee-Quigg-Thacker result uses:
# Λ_LQT = √(8π√2 / 3G_F) ≈ 1.2 TeV (their Eq. 3.14)
# Or with improved treatment:
# Λ_LQT = √(8π² / 3G_F) ≈ 1.5 TeV

Lambda_LQT_paper = np.sqrt(8 * np.pi**2 / (3 * G_F))
print(f"\nLQT paper formula: Λ_LQT = √(8π²/3G_F)")
print(f"  Λ_LQT = {Lambda_LQT_paper:.2f} GeV")
print(f"  Λ_LQT / v_H = {Lambda_LQT_paper/v_H:.2f}")

# Let's verify this using v_H = (√2 G_F)^{-1/2}
v_H_from_GF = 1 / np.sqrt(np.sqrt(2) * G_F)
print(f"\nConsistency check: v_H from G_F:")
print(f"  v_H = 1/√(√2 G_F) = {v_H_from_GF:.2f} GeV (vs PDG: {v_H:.2f} GeV)")

# ============================================================================
# PART 3: Multi-Channel Unitarity Analysis
# ============================================================================
print("\n" + "="*70)
print("PART 3: Multi-Channel Unitarity Analysis")
print("="*70)

# In the SM, we have multiple 2→2 scattering channels:
# 1. W⁺W⁻ → W⁺W⁻
# 2. W⁺W⁻ → ZZ
# 3. W⁺W⁻ → HH
# 4. ZZ → ZZ
# 5. ZZ → HH
# 6. HH → HH
# Plus charged channels W⁺Z, W⁺H, etc.

# The coupled-channel analysis gives a matrix of partial waves:
# The unitarity constraint is that the largest eigenvalue satisfies |a_max| ≤ 1/2

# Chanowitz & Gaillard (1985) showed the full coupled-channel matrix.
# The largest eigenvalue comes from the symmetric combination:
# |W⁺W⁻⟩_s = (|W⁺W⁻⟩ + |ZZ⟩/√2 + |HH⟩/√2) / √2

# For the isoscalar I=0 channel at high energy (s >> m_H², m_W², m_Z²):
# a_0^{I=0} = s/(16π v_H²) × (factor from channel counting)

print("\n--- Scattering Channels in the EW sector ---")
print("The Goldstone/Higgs sector has the following 2→2 channels:")
channels = [
    ("W⁺W⁻ → W⁺W⁻", "I=0, 2"),
    ("W⁺W⁻ → ZZ", "I=0"),
    ("W⁺W⁻ → HH", "I=0"),
    ("ZZ → ZZ", "I=0"),
    ("ZZ → HH", "I=0"),
    ("HH → HH", "I=0"),
    ("W⁺Z → W⁺Z", "I=1"),
    ("W⁺H → W⁺H", "I=1/2"),
]
for ch, iso in channels:
    print(f"  {ch:20s}  {iso}")

# ============================================================================
# PART 4: The Elastic vs Inelastic Distinction
# ============================================================================
print("\n" + "="*70)
print("PART 4: Elastic vs Inelastic Unitarity")
print("="*70)

# ELASTIC unitarity: |a_0^{el}| ≤ 1/2
# This applies to a single channel like W⁺W⁻ → W⁺W⁻

# INELASTIC unitarity (optical theorem):
# Im(a_0) = |a_0|² + Σ_{n≠el} |a_0^n|²
# This requires: Σ_n |a_0^n|² ≤ 1/4

# With N comparable channels: N × |a_0|² ≤ 1/4
# |a_0| ≤ 1/(2√N)

print("\n--- Elastic bound (single channel): ---")
print("  |a_0| ≤ 1/2")
print("  s/(16π v_H²) ≤ 1/2")
print("  √s ≤ √(8π) v_H = {:.3f} v_H = {:.1f} GeV".format(
    np.sqrt(8*np.pi), np.sqrt(8*np.pi) * v_H))

print("\n--- Inelastic bound (N channels): ---")
print("  Σ_n |a_0^n|² ≤ 1/4")
print("  For N comparable channels: |a_0| ≤ 1/(2√N)")

# What is N?
# The proposition claims N = dim(adj_EW) = 4
# But let's check what the actual scattering channels give

# For the EW sector Goldstone bosons:
# π⁺, π⁻, π⁰ (eaten by W⁺, W⁻, Z)
# Plus H (physical Higgs)
#
# The scattering matrix is actually over states like:
# |W⁺W⁻⟩, |ZZ⟩, |HH⟩, |W⁺Z⟩, |ZH⟩, |W⁺H⟩ (and charge conjugates)

# For the I=0 sector specifically:
# 3 states: W⁺W⁻, ZZ/√2, HH/√2
N_I0_sector = 3

print("\n--- Counting channels for I=0 sector: ---")
print("  States: |W⁺W⁻⟩, |ZZ⟩/√2, |HH⟩/√2")
print(f"  N = {N_I0_sector}")

# If we use N = 3 (I=0 sector):
Lambda_N3 = np.sqrt(8 * np.pi / np.sqrt(3)) * v_H
Lambda_N3_alt = 2 * np.sqrt(np.pi / np.sqrt(3)) * v_H
print(f"\n  With N=3: Λ = 2√(π/√3) v_H = {2*np.sqrt(np.pi/np.sqrt(3)):.3f} v_H = {Lambda_N3_alt:.1f} GeV")

# If we use N = 4 (as claimed in proposition):
Lambda_N4 = np.sqrt(8 * np.pi / 2) * v_H  # |a_0| ≤ 1/(2×2) = 1/4
Lambda_N4_alt = 2 * np.sqrt(np.pi) * v_H
print(f"\n  With N=4: Λ = 2√π v_H = {2*np.sqrt(np.pi):.3f} v_H = {Lambda_N4_alt:.1f} GeV")

# ============================================================================
# PART 5: The Proposition's Claim Analysis
# ============================================================================
print("\n" + "="*70)
print("PART 5: Analysis of Proposition's Claim Λ = 4 v_H")
print("="*70)

Lambda_prop = 4 * v_H
print(f"\nProposition claims: Λ_EW = 4 × v_H = {Lambda_prop:.2f} GeV")

# Let's see what unitarity bound would give N = 4:
# From inelastic: |a_0| ≤ 1/(2√N) → √N = 1/(2|a_0|)
# a_0 = s/(16π v_H²), at s = Λ²:
# a_0_at_Lambda = Λ²/(16π v_H²) = (4v_H)²/(16π v_H²) = 1/π

a_0_at_Lambda_prop = Lambda_prop**2 / (16 * np.pi * v_H**2)
print(f"\nPartial wave at Λ = 4v_H:")
print(f"  a_0 = Λ²/(16π v_H²) = {a_0_at_Lambda_prop:.4f}")

# What N would this correspond to for inelastic saturation?
# 1/(2√N) = a_0 → N = 1/(4 a_0²)
N_implied = 1 / (4 * a_0_at_Lambda_prop**2)
print(f"  Implied N for saturation: N = 1/(4 a_0²) = {N_implied:.2f}")

# This gives N ≈ π² ≈ 9.87, not 4!

print("\n*** KEY FINDING ***")
print(f"  If Λ = 4v_H, the implied channel count for saturation is N ≈ {N_implied:.1f}")
print(f"  This is NOT N = 4 = dim(adj_EW)!")

# ============================================================================
# PART 6: What Gives Λ = 4 v_H?
# ============================================================================
print("\n" + "="*70)
print("PART 6: Alternative Derivation for Λ = N × v_H")
print("="*70)

# The proposition's formula Λ = N × v_H does NOT come from unitarity saturation.
# Let's examine what physical principle could give this.

# Possibility 1: Tree-level amplitude matching
# The tree-level amplitude scales as A ~ s/v_H²
# Requiring A ~ 1 at the cutoff: Λ²/v_H² ~ 1 → Λ ~ v_H
# This gives Λ ~ v_H, not 4v_H

# Possibility 2: SMEFT operator counting
# With N operators contributing, each with coefficient c/Λ²,
# the total correction is ~ N × v_H²/Λ²
# Requiring this < 1: Λ > √N × v_H
# This gives Λ > 2v_H for N=4, not Λ = 4v_H

# Possibility 3: Linear counting (proposition's claim)
# The proposition claims Λ = N × v_H, asserting that operators contribute
# linearly (additively to amplitude) rather than quadratically (to cross section)

print("The proposition claims operators contribute ADDITIVELY to amplitude:")
print("  δA/A ~ N × (v_H²/Λ²)")
print("  Setting δA/A ~ 1: Λ ~ √N × v_H = 2v_H (for N=4)")
print("  This still gives ~2v_H, not 4v_H!")

print("\nLet's test the proposition's stated formula...")
print("Proposition §4.4.1 claims: 'Λ_EW = N_ops × v_H = 4v_H'")
print("But the derivation actually shows: 'Λ ~ √N × v_H' (Eq. in Step 3)")
print("The jump from √N to N is NOT mathematically justified.")

# ============================================================================
# PART 7: Honest Assessment
# ============================================================================
print("\n" + "="*70)
print("PART 7: Honest Assessment of the Coefficient")
print("="*70)

# Let's compute what various arguments actually give:
results = {
    "Elastic (|a_0|=1/2)": np.sqrt(8*np.pi),
    "Inelastic N=3 (|a_0|=1/2√3)": 2*np.sqrt(np.pi/np.sqrt(3)),
    "Inelastic N=4 (|a_0|=1/4)": 2*np.sqrt(np.pi),
    "Inelastic N=5 (|a_0|=1/2√5)": 2*np.sqrt(np.pi/np.sqrt(5)),
    "SMEFT √N (N=4)": 2.0,
    "Proposition (N=4)": 4.0,
    "LQT paper result": Lambda_LQT_paper / v_H,
}

print("\nSummary of cutoff coefficients (Λ = coefficient × v_H):")
print("-" * 60)
for name, coef in results.items():
    lambda_val = coef * v_H
    print(f"  {name:35s}: {coef:.3f} ({lambda_val:.0f} GeV)")
print("-" * 60)

# ============================================================================
# PART 8: The Physical Interpretation
# ============================================================================
print("\n" + "="*70)
print("PART 8: Physical Interpretation")
print("="*70)

print("""
The multi-channel unitarity analysis shows:

1. ELASTIC saturation: √(8π) v_H ≈ 5.0 v_H ≈ 1233 GeV
   - Where a single channel (W_L W_L → W_L W_L) saturates |a_0| = 1/2

2. INELASTIC saturation (N=4): 2√π v_H ≈ 3.54 v_H ≈ 872 GeV
   - Where the SUM over N=4 channels saturates: Σ|a_n|² = 1/4
   - This is the verification report's "elastic bound" (mislabeled)

3. LQT bound: √(8π²/3G_F) ≈ 6.1 v_H ≈ 1502 GeV
   - Full W_L W_L scattering including all effects

4. PROPOSITION claim: 4 v_H ≈ 985 GeV
   - This lies BETWEEN the inelastic saturation and LQT bound
   - It is NOT derivable from standard unitarity arguments

The factor 4 = dim(adj_EW) is a FRAMEWORK CHOICE, not a derived result.
""")

# ============================================================================
# PART 9: Corrected Uncertainty Analysis
# ============================================================================
print("\n" + "="*70)
print("PART 9: Corrected Uncertainty Analysis")
print("="*70)

# Given the derivation gap, we should honestly state the coefficient range:
coef_min = 2 * np.sqrt(np.pi)  # Inelastic N=4 saturation: 3.54
coef_max = 4.0  # Proposition's claim
coef_central = (coef_min + coef_max) / 2  # 3.77

Lambda_min = coef_min * v_H
Lambda_max = coef_max * v_H
Lambda_central = coef_central * v_H

print(f"\nHonest coefficient range:")
print(f"  Inelastic bound (N=4): {coef_min:.3f}")
print(f"  Proposition claim:     {coef_max:.3f}")
print(f"  Central value:         {coef_central:.3f}")

print(f"\nCorresponding Λ_EW range:")
print(f"  Minimum: {Lambda_min:.0f} GeV")
print(f"  Maximum: {Lambda_max:.0f} GeV")
print(f"  Central: {Lambda_central:.0f} GeV")
print(f"  Uncertainty: ±{(Lambda_max - Lambda_central):.0f} GeV ({100*(Lambda_max-Lambda_central)/Lambda_central:.0f}%)")

# ============================================================================
# PART 10: Visualizations
# ============================================================================
print("\n" + "="*70)
print("PART 10: Generating Plots")
print("="*70)

fig, axes = plt.subplots(2, 2, figsize=(14, 12))

# Plot 1: Partial wave amplitude vs energy
ax1 = axes[0, 0]
s_values = np.linspace(100, 3000, 500)**2  # s in GeV²
sqrt_s = np.sqrt(s_values)
a0_values = s_values / (16 * np.pi * v_H**2)

ax1.plot(sqrt_s, a0_values, 'b-', linewidth=2, label=r'$a_0 = s/(16\pi v_H^2)$')
ax1.axhline(y=0.5, color='r', linestyle='--', linewidth=1.5, label=r'Elastic: $|a_0| = 1/2$')
ax1.axhline(y=0.25, color='orange', linestyle='--', linewidth=1.5, label=r'Inelastic (N=4): $|a_0| = 1/4$')
ax1.axhline(y=1/(2*np.sqrt(np.pi)), color='green', linestyle=':', linewidth=1.5, label=r'$1/(2\sqrt{\pi})$')

# Mark key scales
scales = {
    r'$\Lambda_{inel}$ (N=4)': Lambda_N4_alt,
    r'$\Lambda_{prop}$ (4$v_H$)': Lambda_prop,
    r'$\Lambda_{LQT}$': Lambda_LQT_paper,
}
colors = ['orange', 'purple', 'red']
for i, (name, val) in enumerate(scales.items()):
    a0_at_scale = val**2 / (16 * np.pi * v_H**2)
    ax1.scatter([val], [a0_at_scale], s=80, c=colors[i], zorder=5)
    ax1.annotate(name, (val, a0_at_scale), textcoords="offset points",
                xytext=(10, 10), fontsize=10)

ax1.set_xlabel(r'$\sqrt{s}$ [GeV]', fontsize=12)
ax1.set_ylabel(r'$|a_0|$', fontsize=12)
ax1.set_xlim(200, 2000)
ax1.set_ylim(0, 0.8)
ax1.legend(loc='lower right', fontsize=10)
ax1.set_title('Partial Wave Amplitude vs Energy', fontsize=12)
ax1.grid(True, alpha=0.3)

# Plot 2: Cutoff coefficient comparison
ax2 = axes[0, 1]
labels = list(results.keys())
values = [results[k] for k in labels]
colors_bar = ['blue', 'cyan', 'green', 'teal', 'orange', 'red', 'purple']

bars = ax2.barh(labels, values, color=colors_bar)
ax2.axvline(x=4.0, color='red', linestyle='--', linewidth=2, label='Proposition claim (4)')
ax2.axvline(x=2*np.sqrt(np.pi), color='green', linestyle='--', linewidth=2, label=f'Inelastic N=4 ({2*np.sqrt(np.pi):.2f})')

ax2.set_xlabel(r'Coefficient in $\Lambda = c \times v_H$', fontsize=12)
ax2.set_title('Comparison of Cutoff Coefficients', fontsize=12)
ax2.legend(loc='lower right')
ax2.grid(True, alpha=0.3, axis='x')

# Plot 3: Scale hierarchy
ax3 = axes[1, 0]
scales_ordered = [
    ('v_H', v_H, 'black'),
    (r'$\sqrt{N} v_H$ (N=4)', 2*v_H, 'blue'),
    (r'Inelastic (N=4)', Lambda_N4_alt, 'green'),
    (r'Proposition: 4$v_H$', Lambda_prop, 'red'),
    (r'Elastic', np.sqrt(8*np.pi)*v_H, 'orange'),
    (r'LQT bound', Lambda_LQT_paper, 'purple'),
]

y_positions = range(len(scales_ordered))
for i, (name, val, col) in enumerate(scales_ordered):
    ax3.barh(i, val, color=col, alpha=0.7)
    ax3.text(val + 20, i, f'{val:.0f} GeV', va='center', fontsize=10)

ax3.set_yticks(y_positions)
ax3.set_yticklabels([s[0] for s in scales_ordered])
ax3.set_xlabel('Energy Scale [GeV]', fontsize=12)
ax3.set_title('Hierarchy of EW Scales', fontsize=12)
ax3.set_xlim(0, 2000)
ax3.grid(True, alpha=0.3, axis='x')

# Plot 4: Uncertainty bands
ax4 = axes[1, 1]
x_range = np.linspace(0, 1, 100)  # Just for band visualization

# The uncertainty range
ax4.fill_between([0, 1], [Lambda_min]*2, [Lambda_max]*2, alpha=0.3, color='blue',
                  label=f'Coefficient range: {coef_min:.2f}-{coef_max:.2f}')
ax4.axhline(y=Lambda_central, color='blue', linestyle='-', linewidth=2,
             label=f'Central: {Lambda_central:.0f} GeV')
ax4.axhline(y=Lambda_prop, color='red', linestyle='--', linewidth=2,
             label=f'Proposition: {Lambda_prop:.0f} GeV')
ax4.axhline(y=Lambda_N4_alt, color='green', linestyle='--', linewidth=2,
             label=f'Inelastic (N=4): {Lambda_N4_alt:.0f} GeV')

ax4.axhline(y=Lambda_LQT_paper, color='purple', linestyle=':', linewidth=2,
             label=f'LQT: {Lambda_LQT_paper:.0f} GeV')

ax4.set_ylabel(r'$\Lambda_{EW}$ [GeV]', fontsize=12)
ax4.set_title('EW Cutoff Uncertainty Analysis', fontsize=12)
ax4.set_xlim(0, 1)
ax4.set_ylim(700, 1700)
ax4.set_xticks([])
ax4.legend(loc='upper right', fontsize=9)
ax4.grid(True, alpha=0.3, axis='y')

# Add text box with summary
textstr = f"""Summary:
• Elastic bound: {np.sqrt(8*np.pi):.2f} v_H = {np.sqrt(8*np.pi)*v_H:.0f} GeV
• Inelastic N=4: {coef_min:.2f} v_H = {Lambda_min:.0f} GeV
• Proposition:   {coef_max:.2f} v_H = {Lambda_max:.0f} GeV
• Gap: {(coef_max - coef_min)/coef_min*100:.0f}%

The coefficient 4 is NOT derived from
unitarity—it is a framework choice."""
ax4.text(0.05, 0.35, textstr, transform=ax4.transAxes, fontsize=9,
         verticalalignment='top', fontfamily='monospace',
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_0_0_26_unitarity_analysis_rigorous.png', dpi=150, bbox_inches='tight')
print(f"Saved plot to: verification/plots/prop_0_0_26_unitarity_analysis_rigorous.png")
plt.close()

# ============================================================================
# PART 11: Summary and Recommendations
# ============================================================================
print("\n" + "="*70)
print("PART 11: SUMMARY AND RECOMMENDATIONS")
print("="*70)

print("""
┌────────────────────────────────────────────────────────────────────┐
│                    VERIFICATION FINDINGS                           │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  1. The claim Λ_EW = 4v_H is NOT derivable from unitarity bounds   │
│                                                                    │
│  2. Inelastic unitarity with N=4 channels gives:                   │
│     Λ ≈ 2√π v_H ≈ 3.54 v_H ≈ 872 GeV                               │
│                                                                    │
│  3. The jump from 3.54 to 4.0 (13% increase) is ASSERTED,          │
│     not derived in the proposition                                 │
│                                                                    │
│  4. The coefficient 4 = dim(adj_EW) appears to be a                │
│     FRAMEWORK CHOICE that "matches" the gauge algebra dimension    │
│                                                                    │
│  5. RECOMMENDATIONS:                                               │
│     a. Acknowledge the coefficient is ~3.5-4, not exactly 4        │
│     b. State that 4 is a framework-specific ansatz                 │
│     c. Update uncertainty to ±115 GeV (to span the range)          │
│     d. Keep NOVEL status - this is an interesting conjecture       │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
""")

print("\n" + "="*70)
print("VERIFICATION COMPLETE")
print("="*70)
