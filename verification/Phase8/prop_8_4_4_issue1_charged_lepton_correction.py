#!/usr/bin/env python3
"""
Issue 1: Charged Lepton Correction Analysis
============================================

The proposition uses the formula:
    δθ₂₃^(μτ) = (1/2) sin(2θ₁₂) sin(θ₁₃) cos(δ_CP) f(m_μ/m_τ)

There's an inconsistency:
- Document claims δ_CP ≈ 200°
- But uses cos(δ_CP) = -0.4
- cos(200°) = -0.94, not -0.4

This script investigates:
1. What cos(δ_CP) value is consistent with current data
2. The correct calculation of the charged lepton correction
3. Alternative formulas from the literature
"""

import numpy as np
import matplotlib.pyplot as plt

# ============================================================================
# CONSTANTS FROM PDG/NuFIT 2024
# ============================================================================

# Mixing angles (NuFIT 6.0, normal ordering, with SK atmospheric data)
THETA_12_DEG = 33.41  # +0.75 -0.72 degrees
THETA_13_DEG = 8.54   # ±0.11 degrees
THETA_23_DEG = 49.1   # ±1.0 degrees (higher octant)

# CP phase (NuFIT 6.0, normal ordering)
DELTA_CP_DEG = 197    # Best fit for NO (range ~128° to ~359° at 3σ)

# Alternative: Some fits give δ_CP closer to 230°-270°
DELTA_CP_ALT_DEG = 230  # Alternative fit value

# Lepton masses (PDG 2024)
M_TAU = 1776.86  # MeV
M_MU = 105.6584  # MeV
M_E = 0.511      # MeV

# Convert to radians
THETA_12 = np.radians(THETA_12_DEG)
THETA_13 = np.radians(THETA_13_DEG)
THETA_23 = np.radians(THETA_23_DEG)
DELTA_CP = np.radians(DELTA_CP_DEG)

print("=" * 70)
print("ISSUE 1: CHARGED LEPTON CORRECTION ANALYSIS")
print("=" * 70)

# ============================================================================
# PART 1: THE cos(δ_CP) INCONSISTENCY
# ============================================================================

print("\n### PART 1: cos(δ_CP) Inconsistency ###\n")

print("Document states:")
print(f"  δ_CP ≈ 200°")
print(f"  cos(δ_CP) = -0.4  (used in calculation)")
print(f"  sin(δ_CP) ≈ 0.9   (used in Step 2)")

print("\nActual values:")
print(f"  cos(200°) = {np.cos(np.radians(200)):.4f}")
print(f"  sin(200°) = {np.sin(np.radians(200)):.4f}")

print("\nIf cos(δ_CP) = -0.4, then δ_CP = ?")
# cos⁻¹(-0.4) = 113.6° or 246.4°
delta_from_cos = np.degrees(np.arccos(-0.4))
print(f"  δ_CP = {delta_from_cos:.1f}° or {360 - delta_from_cos:.1f}°")

print("\nNuFIT 6.0 (NO) best fit: δ_CP = 197° ± ~40°")
print(f"  → cos(197°) = {np.cos(np.radians(197)):.4f}")
print(f"  → sin(197°) = {np.sin(np.radians(197)):.4f}")

# ============================================================================
# PART 2: FORMULA ANALYSIS
# ============================================================================

print("\n### PART 2: Charged Lepton Correction Formulas ###\n")

def f_mass_ratio(m_light, m_heavy):
    """Kinematic function f(x) = (1-x)/(1+x) where x = m_light/m_heavy"""
    x = m_light / m_heavy
    return (1 - x) / (1 + x)

# Document's formula (Eq. in §4.2 Step 3)
def charged_lepton_correction_v1(theta_12, theta_13, delta_cp, m_mu, m_tau):
    """
    Document formula:
    δθ₂₃^(μτ) = (1/2) sin(2θ₁₂) sin(θ₁₃) cos(δ_CP) f(m_μ/m_τ)
    """
    f = f_mass_ratio(m_mu, m_tau)
    return 0.5 * np.sin(2 * theta_12) * np.sin(theta_13) * np.cos(delta_cp) * f

# Literature formula from arXiv:0905.3534 (A4 models)
def charged_lepton_correction_A4(theta_13, delta_cp):
    """
    From A4 model literature:
    sin²θ₂₃ = 1/2 + (√2/2) sin(δ) cos(θ₁₃) sin(θ₁₃)

    This implies:
    δθ₂₃ ≈ (1/√2) sin(δ_CP) sin(θ₁₃) cos(θ₁₃)  for small corrections
    """
    return (1/np.sqrt(2)) * np.sin(delta_cp) * np.sin(theta_13) * np.cos(theta_13)

# Simplified formula (small angle approximation)
def charged_lepton_correction_simple(theta_13, delta_cp):
    """
    Simple formula: δθ₂₃ ~ θ₁₃ sin(δ_CP) / √2
    """
    return theta_13 * np.sin(delta_cp) / np.sqrt(2)

print("Formula 1 (Document §4.2):")
print("  δθ₂₃^(μτ) = (1/2) sin(2θ₁₂) sin(θ₁₃) cos(δ_CP) f(m_μ/m_τ)")

print("\nFormula 2 (A4 literature, arXiv:0905.3534):")
print("  δθ₂₃ ≈ (1/√2) sin(δ_CP) sin(θ₁₃) cos(θ₁₃)")

print("\nFormula 3 (Simple approximation):")
print("  δθ₂₃ ~ θ₁₃ sin(δ_CP) / √2")

# ============================================================================
# PART 3: NUMERICAL CALCULATIONS
# ============================================================================

print("\n### PART 3: Numerical Calculations ###\n")

# Calculate f(m_μ/m_τ)
f_val = f_mass_ratio(M_MU, M_TAU)
print(f"f(m_μ/m_τ) = f({M_MU/M_TAU:.4f}) = {f_val:.4f}")

print("\n--- Using Document's Formula ---")

# Case A: Using cos(δ_CP) = -0.4 as document does
cos_delta_doc = -0.4
correction_doc_value = 0.5 * np.sin(2*THETA_12) * np.sin(THETA_13) * cos_delta_doc * f_val
print(f"\nCase A: cos(δ_CP) = -0.4 (as used in document)")
print(f"  sin(2θ₁₂) = sin({2*THETA_12_DEG:.1f}°) = {np.sin(2*THETA_12):.4f}")
print(f"  sin(θ₁₃) = sin({THETA_13_DEG}°) = {np.sin(THETA_13):.4f}")
print(f"  δθ₂₃ = 0.5 × {np.sin(2*THETA_12):.3f} × {np.sin(THETA_13):.3f} × ({cos_delta_doc}) × {f_val:.3f}")
print(f"  δθ₂₃ = {correction_doc_value:.5f} rad = {np.degrees(correction_doc_value):.2f}°")

# Case B: Using cos(197°) - actual value for δ_CP = 197°
cos_delta_197 = np.cos(np.radians(197))
correction_197 = 0.5 * np.sin(2*THETA_12) * np.sin(THETA_13) * cos_delta_197 * f_val
print(f"\nCase B: cos(197°) = {cos_delta_197:.4f} (for δ_CP = 197°)")
print(f"  δθ₂₃ = 0.5 × {np.sin(2*THETA_12):.3f} × {np.sin(THETA_13):.3f} × ({cos_delta_197:.3f}) × {f_val:.3f}")
print(f"  δθ₂₃ = {correction_197:.5f} rad = {np.degrees(correction_197):.2f}°")

# Case C: Using cos(230°) - alternative δ_CP value
cos_delta_230 = np.cos(np.radians(230))
correction_230 = 0.5 * np.sin(2*THETA_12) * np.sin(THETA_13) * cos_delta_230 * f_val
print(f"\nCase C: cos(230°) = {cos_delta_230:.4f} (for δ_CP = 230°)")
print(f"  δθ₂₃ = 0.5 × {np.sin(2*THETA_12):.3f} × {np.sin(THETA_13):.3f} × ({cos_delta_230:.3f}) × {f_val:.3f}")
print(f"  δθ₂₃ = {correction_230:.5f} rad = {np.degrees(correction_230):.2f}°")

print("\n--- Using Alternative Formulas ---")

# A4 formula
correction_A4 = charged_lepton_correction_A4(THETA_13, DELTA_CP)
print(f"\nA4 Formula (sin-dependent):")
print(f"  δθ₂₃ = (1/√2) × sin({DELTA_CP_DEG}°) × sin({THETA_13_DEG}°) × cos({THETA_13_DEG}°)")
print(f"  δθ₂₃ = {correction_A4:.5f} rad = {np.degrees(correction_A4):.2f}°")

# Simple formula
correction_simple = charged_lepton_correction_simple(THETA_13, DELTA_CP)
print(f"\nSimple Formula:")
print(f"  δθ₂₃ = {THETA_13:.4f} × sin({DELTA_CP_DEG}°) / √2")
print(f"  δθ₂₃ = {correction_simple:.5f} rad = {np.degrees(correction_simple):.2f}°")

# ============================================================================
# PART 4: RESOLUTION OF THE DISCREPANCY
# ============================================================================

print("\n### PART 4: Resolution of the Discrepancy ###\n")

print("The document's calculation appears to use:")
print("  δ_CP such that cos(δ_CP) = -0.4")
print(f"  This corresponds to δ_CP ≈ 114° or 246°")
print()
print("However, NuFIT 6.0 (NO) gives δ_CP ≈ 197° where cos(197°) = -0.956")
print()
print("RESOLUTION OPTIONS:")
print()
print("Option 1: Keep δ_CP = 197° (NuFIT best fit)")
print(f"  → cos(δ_CP) = -0.956")
print(f"  → δθ₂₃^(μτ) = {np.degrees(correction_197):.2f}°")
print()
print("Option 2: Use δ_CP = 246° (to get cos = -0.4)")
print(f"  → cos(δ_CP) = -0.4")
print(f"  → δθ₂₃^(μτ) = {np.degrees(correction_doc_value):.2f}°")
print(f"  → But 246° is outside NuFIT 3σ range for NO")
print()

# What δ_CP gives the -1.4° claimed in the document?
# -1.4° = -0.0244 rad
# 0.5 × 0.919 × 0.149 × cos(δ) × 0.888 = -0.0244
# cos(δ) = -0.0244 / (0.5 × 0.919 × 0.149 × 0.888) = -0.401
target_delta = 0.5 * np.sin(2*THETA_12) * np.sin(THETA_13) * f_val
required_cos = -0.0244 / target_delta
print("Option 3: Find δ_CP that gives exactly -1.4°")
print(f"  Required cos(δ_CP) = {required_cos:.3f}")
print(f"  Implied δ_CP = {np.degrees(np.arccos(required_cos)):.1f}° or {360-np.degrees(np.arccos(required_cos)):.1f}°")

# ============================================================================
# PART 5: RECOMMENDED CORRECTION
# ============================================================================

print("\n### PART 5: RECOMMENDED CORRECTION ###\n")

print("RECOMMENDATION: Use NuFIT 6.0 best-fit value with proper error propagation")
print()
print("Updated calculation:")
print(f"  θ₁₂ = {THETA_12_DEG}° ± 0.75°")
print(f"  θ₁₃ = {THETA_13_DEG}° ± 0.11°")
print(f"  δ_CP = {DELTA_CP_DEG}° (+40°/-50°, NuFIT 6.0 NO)")
print(f"  m_μ/m_τ = {M_MU/M_TAU:.5f}")
print()

# Calculate with central values
delta_theta_central = charged_lepton_correction_v1(THETA_12, THETA_13, DELTA_CP, M_MU, M_TAU)
print(f"Central value: δθ₂₃^(μτ) = {np.degrees(delta_theta_central):.2f}°")

# Error propagation
# Main uncertainty comes from δ_CP
delta_cp_up = np.radians(DELTA_CP_DEG + 40)
delta_cp_down = np.radians(DELTA_CP_DEG - 50)
correction_up = charged_lepton_correction_v1(THETA_12, THETA_13, delta_cp_up, M_MU, M_TAU)
correction_down = charged_lepton_correction_v1(THETA_12, THETA_13, delta_cp_down, M_MU, M_TAU)

print(f"With δ_CP = {DELTA_CP_DEG+40}°: δθ₂₃^(μτ) = {np.degrees(correction_up):.2f}°")
print(f"With δ_CP = {DELTA_CP_DEG-50}°: δθ₂₃^(μτ) = {np.degrees(correction_down):.2f}°")

# Range
print(f"\nRange: {np.degrees(correction_up):.2f}° to {np.degrees(correction_down):.2f}°")

# Symmetric error estimate
sigma_delta_cp = 45  # degrees (approximate)
# Derivative: d(correction)/d(δ_CP) = -0.5 × sin(2θ₁₂) × sin(θ₁₃) × sin(δ_CP) × f
deriv = -0.5 * np.sin(2*THETA_12) * np.sin(THETA_13) * np.sin(DELTA_CP) * f_val
sigma_correction = abs(deriv) * np.radians(sigma_delta_cp)
print(f"\nError estimate: σ ≈ {np.degrees(sigma_correction):.2f}°")

print(f"\n*** FINAL CORRECTED VALUE: δθ₂₃^(μτ) = {np.degrees(delta_theta_central):.1f}° ± {np.degrees(sigma_correction):.1f}° ***")

# ============================================================================
# PART 6: COMPARISON TABLE
# ============================================================================

print("\n### PART 6: Summary Comparison ###\n")

print("| Source | cos(δ_CP) used | δθ₂₃^(μτ) |")
print("|--------|----------------|-----------|")
print(f"| Document (claimed) | -0.4 | -1.4° |")
print(f"| Using cos(δ_CP)=-0.4 | -0.400 | {np.degrees(correction_doc_value):.2f}° |")
print(f"| Using δ_CP=197° | {cos_delta_197:.3f} | {np.degrees(correction_197):.2f}° |")
print(f"| Using δ_CP=230° | {cos_delta_230:.3f} | {np.degrees(correction_230):.2f}° |")
print(f"| A4 formula (sin-based) | N/A | {np.degrees(correction_A4):.2f}° |")

# ============================================================================
# PART 7: CREATE VISUALIZATION
# ============================================================================

print("\n### Creating visualization... ###\n")

fig, axes = plt.subplots(1, 2, figsize=(14, 5))

# Plot 1: δθ₂₃ vs δ_CP
delta_cp_range = np.linspace(0, 360, 361)
corrections_cos = [np.degrees(charged_lepton_correction_v1(
    THETA_12, THETA_13, np.radians(d), M_MU, M_TAU)) for d in delta_cp_range]
corrections_sin = [np.degrees(charged_lepton_correction_A4(
    THETA_13, np.radians(d))) for d in delta_cp_range]

ax1 = axes[0]
ax1.plot(delta_cp_range, corrections_cos, 'b-', linewidth=2, label='Document formula (cos-based)')
ax1.plot(delta_cp_range, corrections_sin, 'r--', linewidth=2, label='A4 formula (sin-based)')
ax1.axvline(197, color='green', linestyle=':', linewidth=1.5, label=f'NuFIT 6.0 best fit (197°)')
ax1.axhline(-1.4, color='orange', linestyle=':', linewidth=1.5, label='Document claims (-1.4°)')
ax1.axhline(np.degrees(correction_197), color='purple', linestyle='-.', linewidth=1.5,
            label=f'Corrected ({np.degrees(correction_197):.1f}°)')

# Mark specific points
ax1.plot(197, np.degrees(correction_197), 'go', markersize=10)
ax1.plot(246, np.degrees(correction_doc_value), 'mo', markersize=10)

ax1.set_xlabel('δ_CP (degrees)', fontsize=12)
ax1.set_ylabel('δθ₂₃^(μτ) (degrees)', fontsize=12)
ax1.set_title('Charged Lepton Correction vs CP Phase', fontsize=14)
ax1.legend(loc='upper right', fontsize=9)
ax1.grid(True, alpha=0.3)
ax1.set_xlim(0, 360)

# Add NuFIT 3σ range shading
ax1.axvspan(128, 359, alpha=0.1, color='green', label='NuFIT 3σ range')

# Plot 2: Impact on total prediction
ax2 = axes[1]

# Components
A4_breaking = 2.89  # degrees
geometric_asymmetry = 3.80
RG_running = 0.50

# Scenarios
scenarios = [
    ('Document\n(cos=-0.4)', -1.4, 'orange'),
    ('δ_CP=197°\n(NuFIT)', np.degrees(correction_197), 'green'),
    ('δ_CP=230°', np.degrees(correction_230), 'blue'),
    ('A4 formula', np.degrees(correction_A4), 'red'),
]

x_pos = np.arange(len(scenarios))
for i, (label, charged, color) in enumerate(scenarios):
    total = A4_breaking + geometric_asymmetry + RG_running + charged
    theta_23 = 45 + total
    ax2.bar(i, theta_23 - 45, bottom=45, color=color, alpha=0.7, width=0.6)
    ax2.text(i, theta_23 + 0.3, f'{theta_23:.1f}°', ha='center', fontsize=10)

ax2.axhline(49.1, color='black', linestyle='--', linewidth=2, label='Experiment (49.1°)')
ax2.axhspan(48.1, 50.1, alpha=0.2, color='gray', label='Exp. ±1σ')
ax2.axhline(45, color='gray', linestyle=':', linewidth=1, label='TBM (45°)')

ax2.set_xticks(x_pos)
ax2.set_xticklabels([s[0] for s in scenarios], fontsize=9)
ax2.set_ylabel('θ₂₃ (degrees)', fontsize=12)
ax2.set_title('Total θ₂₃ Prediction by Scenario', fontsize=14)
ax2.legend(loc='upper right', fontsize=9)
ax2.set_ylim(44, 53)
ax2.grid(True, alpha=0.3, axis='y')

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_8_4_4_issue1_charged_lepton.png', dpi=150)
print("Plot saved to: verification/plots/prop_8_4_4_issue1_charged_lepton.png")

# ============================================================================
# FINAL CONCLUSION
# ============================================================================

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)

print("""
The document's charged lepton correction has an inconsistency:

1. STATED: δ_CP ≈ 200° and cos(δ_CP) = -0.4
   - These are INCONSISTENT: cos(200°) = -0.94, not -0.4

2. The -1.4° result matches cos(δ_CP) = -0.4, which requires δ_CP ≈ 114° or 246°
   - 246° is marginally within NuFIT 3σ range
   - 114° is outside the range

3. RECOMMENDED CORRECTION:
   - Use δ_CP = 197° (NuFIT 6.0 best fit)
   - This gives δθ₂₃^(μτ) = -3.3° (not -1.4°)

   OR

   - Acknowledge using δ_CP = 246° (within 3σ uncertainty)
   - Keep the -1.4° result but correct the stated δ_CP value

4. IMPACT ON TOTAL PREDICTION:
   - With δ_CP = 197°: θ₂₃ = 45° + 3.9° = 48.9° (0.2σ from experiment)
   - With δ_CP = 246°: θ₂₃ = 45° + 5.8° = 50.8° (1.7σ from experiment)

   The NuFIT best-fit value actually gives BETTER agreement!
""")

plt.show()
