#!/usr/bin/env python3
"""
Issue 1 Resolution: Charged Lepton Correction - Final Analysis
================================================================

Based on Steve King's 2014 INSS lecture notes and the literature research,
we now understand the correct formulas for charged lepton corrections.

KEY INSIGHT from King lecture:
- The atmospheric sum rule for TM1 mixing is: θ₂₃ - 45° ≈ √2 θ₁₃ cos(δ)
- The atmospheric sum rule for TM2 mixing is: θ₂₃ - 45° ≈ -(θ₁₃/√2) cos(δ)

The proposition uses a different formula involving mass ratios.
Let's understand which is appropriate and how to reconcile them.
"""

import numpy as np
import matplotlib.pyplot as plt

# Constants from NuFIT 6.0 (Normal Ordering)
THETA_12_DEG = 33.41
THETA_13_DEG = 8.54
THETA_23_EXP = 49.1  # Experimental value
DELTA_CP_DEG = 197   # Best fit

# Convert to radians
THETA_12 = np.radians(THETA_12_DEG)
THETA_13 = np.radians(THETA_13_DEG)
DELTA_CP = np.radians(DELTA_CP_DEG)

# Lepton masses (PDG 2024)
M_TAU = 1776.86  # MeV
M_MU = 105.6584  # MeV

print("=" * 70)
print("ISSUE 1 RESOLUTION: CHARGED LEPTON CORRECTION ANALYSIS")
print("=" * 70)

# ============================================================================
# PART 1: ATMOSPHERIC SUM RULES (FROM KING LECTURE)
# ============================================================================

print("\n### PART 1: Atmospheric Sum Rules (King 2014) ###\n")

print("From discrete flavor symmetry models:")
print()
print("TM1 Sum Rule (first column preserved):")
print("  θ₂₃ - 45° ≈ √2 × θ₁₃ × cos(δ)")
print()
print("TM2 Sum Rule (second column preserved):")
print("  θ₂₃ - 45° ≈ -(θ₁₃/√2) × cos(δ)")
print()

# Calculate predictions from atmospheric sum rules
delta_TM1 = np.sqrt(2) * THETA_13 * np.cos(DELTA_CP)
delta_TM2 = -(THETA_13 / np.sqrt(2)) * np.cos(DELTA_CP)

theta_23_TM1 = 45 + np.degrees(delta_TM1)
theta_23_TM2 = 45 + np.degrees(delta_TM2)

print(f"Using θ₁₃ = {THETA_13_DEG}° and δ_CP = {DELTA_CP_DEG}°:")
print()
print(f"TM1: δθ₂₃ = √2 × {THETA_13_DEG}° × cos({DELTA_CP_DEG}°)")
print(f"         = √2 × {THETA_13_DEG}° × ({np.cos(DELTA_CP):.4f})")
print(f"         = {np.degrees(delta_TM1):.2f}°")
print(f"     θ₂₃ = 45° + ({np.degrees(delta_TM1):.2f}°) = {theta_23_TM1:.1f}°")
print()
print(f"TM2: δθ₂₃ = -(θ₁₃/√2) × cos({DELTA_CP_DEG}°)")
print(f"         = -({THETA_13_DEG}°/√2) × ({np.cos(DELTA_CP):.4f})")
print(f"         = {np.degrees(delta_TM2):.2f}°")
print(f"     θ₂₃ = 45° + ({np.degrees(delta_TM2):.2f}°) = {theta_23_TM2:.1f}°")

print()
print(f"Experimental: θ₂₃ = {THETA_23_EXP}° ± 1.0°")

# ============================================================================
# PART 2: UNDERSTANDING THE PROPOSITION'S FORMULA
# ============================================================================

print("\n### PART 2: The Proposition's Formula Structure ###\n")

print("The proposition decomposes θ₂₃ correction into:")
print("  δθ₂₃ = δθ₂₃^(A₄) + δθ₂₃^(geo) + δθ₂₃^(RG) + δθ₂₃^(μτ)")
print()
print("This is MORE GENERAL than the atmospheric sum rules.")
print("The atmospheric sum rules are SPECIAL CASES assuming specific symmetries.")
print()

# The proposition's individual contributions
delta_A4 = 2.89  # degrees (from λ²)
delta_geo = 3.80  # degrees (geometric asymmetry)
delta_RG = 0.50   # degrees (RG running)

print("From the proposition:")
print(f"  δθ₂₃^(A₄)  = +{delta_A4}°  (A₄ → Z₃ breaking, from λ²)")
print(f"  δθ₂₃^(geo) = +{delta_geo}°  (geometric μ-τ asymmetry)")
print(f"  δθ₂₃^(RG)  = +{delta_RG}°  (RG running)")
print(f"  δθ₂₃^(μτ)  = ???         (charged lepton correction)")
print()

# ============================================================================
# PART 3: RECONCILING THE FORMULAS
# ============================================================================

print("\n### PART 3: Formula Reconciliation ###\n")

print("The proposition's charged lepton formula:")
print("  δθ₂₃^(μτ) = (1/2) sin(2θ₁₂) sin(θ₁₃) cos(δ_CP) f(m_μ/m_τ)")
print()
print("This formula has the SAME cos(δ) dependence as the atmospheric sum rules!")
print("The key observation is:")
print("  - Document formula: ~ sin(θ₁₃) cos(δ)")
print("  - TM1/TM2 rules:    ~ θ₁₃ cos(δ)")
print()
print("These are structurally similar (for small θ₁₃, sin(θ₁₃) ≈ θ₁₃)")

# Calculate with both formulas
def f_mass_ratio(m_light, m_heavy):
    x = m_light / m_heavy
    return (1 - x) / (1 + x)

f_val = f_mass_ratio(M_MU, M_TAU)

# Document formula (with corrected cos(δ_CP))
delta_charged_doc = 0.5 * np.sin(2*THETA_12) * np.sin(THETA_13) * np.cos(DELTA_CP) * f_val

print(f"\nNumerical comparison (δ_CP = {DELTA_CP_DEG}°):")
print()
print(f"Document formula: {np.degrees(delta_charged_doc):.2f}°")
print(f"TM1 correction:   {np.degrees(delta_TM1):.2f}°")
print(f"TM2 correction:   {np.degrees(delta_TM2):.2f}°")

# ============================================================================
# PART 4: THE RESOLUTION
# ============================================================================

print("\n### PART 4: RESOLUTION ###\n")

print("The proposition has TWO ISSUES with the charged lepton term:")
print()
print("ISSUE 1a: cos(δ_CP) VALUE")
print("  - States δ_CP ≈ 200° but uses cos(δ_CP) = -0.4")
print("  - cos(200°) = -0.94, NOT -0.4")
print("  - The -1.4° value is ARITHMETICALLY CORRECT for cos = -0.4")
print("  - But -0.4 implies δ_CP ≈ 114° or 246°, not 200°")
print()
print("ISSUE 1b: FORMULA APPROPRIATENESS")
print("  - The formula used is from general charged lepton corrections")
print("  - It's different from the atmospheric sum rules (TM1/TM2)")
print("  - Both are valid; they apply to different theoretical frameworks")
print()

# ============================================================================
# PART 5: PROPOSED CORRECTION
# ============================================================================

print("\n### PART 5: PROPOSED CORRECTION ###\n")

print("OPTION A: Correct the cos(δ_CP) value (minimal change)")
print("-" * 50)
print(f"  Keep the formula: δθ₂₃^(μτ) = (1/2)sin(2θ₁₂)sin(θ₁₃)cos(δ)f")
print(f"  Use δ_CP = 197° (NuFIT 6.0 best fit)")
print(f"  Result: δθ₂₃^(μτ) = {np.degrees(delta_charged_doc):.1f}°")
print()

total_A = delta_A4 + delta_geo + delta_RG + np.degrees(delta_charged_doc)
theta_23_A = 45 + total_A

print(f"  Total correction: {delta_A4}° + {delta_geo}° + {delta_RG}° + ({np.degrees(delta_charged_doc):.1f}°)")
print(f"                  = {total_A:.1f}°")
print(f"  θ₂₃ = 45° + {total_A:.1f}° = {theta_23_A:.1f}°")
print(f"  Tension with experiment: ({theta_23_A:.1f} - {THETA_23_EXP})/1.0 = {(theta_23_A - THETA_23_EXP):.1f}σ")
print()

print("OPTION B: Use atmospheric sum rule approach (TM1)")
print("-" * 50)
print(f"  Use TM1: θ₂₃ - 45° ≈ √2 × θ₁₃ × cos(δ)")
print(f"  This gives: δθ₂₃ = {np.degrees(delta_TM1):.1f}° (includes charged lepton effects)")
print()

# For TM1, the atmospheric deviation IS the charged lepton + A4 effect combined
# We need to separate or combine appropriately
print("  Note: In TM1 framework, the sum rule gives the TOTAL deviation from 45°")
print(f"  θ₂₃ = 45° + ({np.degrees(delta_TM1):.1f}°) = {theta_23_TM1:.1f}°")
print(f"  Tension: ({theta_23_TM1:.1f} - {THETA_23_EXP})/1.0 = {(theta_23_TM1 - THETA_23_EXP):.1f}σ")
print()

print("OPTION C: Keep cos(δ_CP) = -0.4 but clarify δ_CP value")
print("-" * 50)
print(f"  If we want to preserve the -1.4° result:")
print(f"  Need cos(δ_CP) = -0.4, which means δ_CP ≈ 114° or 246°")
print(f"  246° is within NuFIT 3σ range (128° to 359°)")
print()

delta_charged_C = -1.4  # degrees (keep original)
total_C = delta_A4 + delta_geo + delta_RG + delta_charged_C
theta_23_C = 45 + total_C

print(f"  Total correction: {delta_A4}° + {delta_geo}° + {delta_RG}° + ({delta_charged_C})°")
print(f"                  = {total_C:.1f}°")
print(f"  θ₂₃ = 45° + {total_C:.1f}° = {theta_23_C:.1f}°")
print(f"  Tension: ({theta_23_C:.1f} - {THETA_23_EXP})/1.0 = {(theta_23_C - THETA_23_EXP):.1f}σ")

# ============================================================================
# PART 6: FINAL RECOMMENDATION
# ============================================================================

print("\n" + "=" * 70)
print("FINAL RECOMMENDATION")
print("=" * 70)

print("""
The proposition should choose ONE of these approaches:

RECOMMENDED: OPTION A (Correct cos(δ_CP))
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Fix the inconsistency: State δ_CP = 197° AND cos(δ_CP) = -0.96
2. Update δθ₂₃^(μτ) = -3.3° (instead of -1.4°)
3. This gives θ₂₃ = 48.9°, which is CLOSER to experiment!
4. Tension improves from 1.6σ to 0.2σ

ALTERNATIVE: OPTION C (Clarify δ_CP)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Keep δθ₂₃^(μτ) = -1.4°
2. Change "δ_CP ≈ 200°" to "δ_CP ≈ 246°" (still within NuFIT 3σ)
3. This gives θ₂₃ = 50.7° (current document value)
4. Tension remains at 1.6σ

The key insight is that BOTH options are mathematically valid.
Option A gives better agreement with experiment.
Option C preserves the document's structure but requires δ_CP correction.
""")

# ============================================================================
# Create comparison plot
# ============================================================================

fig, ax = plt.subplots(figsize=(10, 6))

options = ['Document\n(inconsistent)', 'Option A\n(δ_CP=197°)', 'Option C\n(δ_CP=246°)',
           'TM1 Sum Rule', 'TM2 Sum Rule']
predictions = [50.7, theta_23_A, theta_23_C, theta_23_TM1, theta_23_TM2]
colors = ['red', 'green', 'blue', 'purple', 'orange']

bars = ax.bar(range(len(options)), predictions, color=colors, alpha=0.7, edgecolor='black')

# Add experimental band
ax.axhspan(48.1, 50.1, alpha=0.2, color='gray', label='Exp. ±1σ')
ax.axhline(49.1, color='black', linestyle='--', linewidth=2, label='Experiment (49.1°)')
ax.axhline(45, color='gray', linestyle=':', linewidth=1, label='TBM (45°)')

# Add value labels
for i, (bar, pred) in enumerate(zip(bars, predictions)):
    ax.text(i, pred + 0.3, f'{pred:.1f}°', ha='center', va='bottom', fontsize=10, fontweight='bold')
    tension = (pred - 49.1) / 1.0
    ax.text(i, 44.5, f'{tension:+.1f}σ', ha='center', fontsize=9)

ax.set_xticks(range(len(options)))
ax.set_xticklabels(options, fontsize=10)
ax.set_ylabel('θ₂₃ (degrees)', fontsize=12)
ax.set_title('θ₂₃ Prediction Comparison: Issue 1 Resolution Options', fontsize=14)
ax.set_ylim(43, 55)
ax.legend(loc='upper right')
ax.grid(True, alpha=0.3, axis='y')

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_8_4_4_issue1_resolution.png', dpi=150)
print("\nPlot saved to: verification/plots/prop_8_4_4_issue1_resolution.png")

plt.show()
