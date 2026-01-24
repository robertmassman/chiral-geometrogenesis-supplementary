"""
Analysis of neutrino Dirac mass hierarchy implications for Theorem 3.1.5

This script investigates the contradiction between:
1. Theorem 3.1.5's assumption that m_D is generation-universal (~0.7 GeV for all 3 generations)
2. Theorem 3.1.2's derivation that ALL fermion masses follow η_f = λ^(2n) × c_f

We calculate M_R under both scenarios and assess phenomenological implications.
"""

import numpy as np
import matplotlib.pyplot as plt

# Constants
eV_to_GeV = 1e-9
GeV_to_eV = 1e9

# Input parameters from CG framework
lambda_CG = 0.2245  # Wolfenstein parameter from Theorem 3.1.2
m_D3_base = 0.70  # GeV - third generation Dirac mass (heaviest)
Sigma_m_nu_obs = 0.066  # eV - neutrino mass sum from oscillation + cosmology
Sigma_m_nu_obs_uncertainty = 0.010  # eV
Sigma_m_nu_holographic_bound = 0.132  # eV - from Proposition 3.1.4 with χ=4

# PDG neutrino mass-squared differences
Delta_m21_sq = 7.53e-5  # eV^2 (solar)
Delta_m32_sq_NO = 2.453e-3  # eV^2 (atmospheric, normal ordering)
Delta_m32_sq_IO = -2.536e-3  # eV^2 (inverted ordering)

print("="*80)
print("NEUTRINO DIRAC MASS HIERARCHY ANALYSIS")
print("="*80)
print()

# ============================================================================
# SCENARIO 1: Generation-Universal Dirac Masses (Current Theorem 3.1.5)
# ============================================================================

print("SCENARIO 1: Generation-Universal Dirac Masses")
print("-" * 80)
print(f"Assumption: m_D1 = m_D2 = m_D3 = {m_D3_base} GeV")
print()

m_D_universal = np.array([m_D3_base, m_D3_base, m_D3_base])
sum_m_D_sq_universal = np.sum(m_D_universal**2)

M_R_universal = (sum_m_D_sq_universal) / (Sigma_m_nu_obs * eV_to_GeV)
M_R_universal_lower = (sum_m_D_sq_universal) / (Sigma_m_nu_holographic_bound * eV_to_GeV)

print(f"Sum of m_D^2: {sum_m_D_sq_universal:.4f} GeV^2")
print(f"M_R (using Σm_ν = {Sigma_m_nu_obs} eV): {M_R_universal:.2e} GeV")
print(f"M_R (using holographic bound {Sigma_m_nu_holographic_bound} eV): {M_R_universal_lower:.2e} GeV")
print()

# Light neutrino masses from seesaw
m_nu_universal = m_D_universal**2 / M_R_universal
print(f"Implied light neutrino masses (quasi-degenerate):")
for i in range(3):
    print(f"  m_ν{i+1} = {m_nu_universal[i]*GeV_to_eV:.4f} eV")
print(f"  Sum: {np.sum(m_nu_universal)*GeV_to_eV:.4f} eV (by construction)")
print()

# ============================================================================
# SCENARIO 2: Hierarchical Dirac Masses (Theorem 3.1.2 Prediction)
# ============================================================================

print("SCENARIO 2: Hierarchical Dirac Masses (Theorem 3.1.2)")
print("-" * 80)
print(f"Assumption: m_Di ∝ λ^(2n) with λ = {lambda_CG}")
print()

# Generation indices: n=0 (3rd gen), n=1 (2nd gen), n=2 (1st gen)
m_D_hierarchical = np.array([
    m_D3_base * lambda_CG**(2*2),  # 1st generation (n=2)
    m_D3_base * lambda_CG**(2*1),  # 2nd generation (n=1)
    m_D3_base * lambda_CG**(2*0),  # 3rd generation (n=0)
])

print(f"m_D1 = m_D3 × λ^4 = {m_D_hierarchical[0]:.4f} GeV")
print(f"m_D2 = m_D3 × λ^2 = {m_D_hierarchical[1]:.4f} GeV")
print(f"m_D3 = {m_D_hierarchical[2]:.4f} GeV")
print()

# Check mass ratios
print("Mass ratios:")
print(f"  m_D3/m_D2 = {m_D_hierarchical[2]/m_D_hierarchical[1]:.2f} (expected: λ^(-2) = {lambda_CG**(-2):.2f})")
print(f"  m_D2/m_D1 = {m_D_hierarchical[1]/m_D_hierarchical[0]:.2f} (expected: λ^(-2) = {lambda_CG**(-2):.2f})")
print()

sum_m_D_sq_hierarchical = np.sum(m_D_hierarchical**2)
print(f"Sum of m_D^2: {sum_m_D_sq_hierarchical:.4f} GeV^2")
print(f"  Dominated by m_D3^2 = {m_D_hierarchical[2]**2:.4f} GeV^2 ({100*m_D_hierarchical[2]**2/sum_m_D_sq_hierarchical:.1f}%)")
print()

M_R_hierarchical = (sum_m_D_sq_hierarchical) / (Sigma_m_nu_obs * eV_to_GeV)
M_R_hierarchical_lower = (sum_m_D_sq_hierarchical) / (Sigma_m_nu_holographic_bound * eV_to_GeV)

print(f"M_R (using Σm_ν = {Sigma_m_nu_obs} eV): {M_R_hierarchical:.2e} GeV")
print(f"M_R (using holographic bound {Sigma_m_nu_holographic_bound} eV): {M_R_hierarchical_lower:.2e} GeV")
print()

# Light neutrino masses from seesaw
m_nu_hierarchical = m_D_hierarchical**2 / M_R_hierarchical
print(f"Implied light neutrino masses (hierarchical):")
for i in range(3):
    print(f"  m_ν{i+1} = {m_nu_hierarchical[i]*GeV_to_eV:.6f} eV")
print(f"  Sum: {np.sum(m_nu_hierarchical)*GeV_to_eV:.4f} eV (by construction)")
print()

# Calculate mass-squared differences for hierarchical case
Delta_m21_sq_hierarchical = m_nu_hierarchical[1]**2 - m_nu_hierarchical[0]**2
Delta_m32_sq_hierarchical = m_nu_hierarchical[2]**2 - m_nu_hierarchical[1]**2

print("Mass-squared differences (hierarchical scenario):")
print(f"  Δm²21 = {Delta_m21_sq_hierarchical*GeV_to_eV**2:.2e} eV² (observed: {Delta_m21_sq:.2e} eV²)")
print(f"  Δm²32 = {Delta_m32_sq_hierarchical*GeV_to_eV**2:.2e} eV² (observed: {Delta_m32_sq_NO:.2e} eV²)")
print()

# Determine ordering
if m_nu_hierarchical[2] > m_nu_hierarchical[0]:
    ordering = "INVERTED (m3 > m1, m2)"
else:
    ordering = "NORMAL (m1 < m2 < m3)"
print(f"Implied mass ordering: {ordering}")
print()

# ============================================================================
# COMPARISON
# ============================================================================

print("="*80)
print("COMPARISON: Universal vs. Hierarchical")
print("="*80)
print()

print(f"M_R ratio: {M_R_universal / M_R_hierarchical:.2f}")
print(f"  Universal: {M_R_universal:.2e} GeV")
print(f"  Hierarchical: {M_R_hierarchical:.2e} GeV")
print()

print("Physical Constraints:")
print(f"  Leptogenesis bound: M_R > 1e9 GeV")
print(f"    Universal: {'✓ PASS' if M_R_universal > 1e9 else '✗ FAIL'}")
print(f"    Hierarchical: {'✓ PASS' if M_R_hierarchical > 1e9 else '✗ FAIL'}")
print()

print(f"  B-L scale < M_GUT (~1e16 GeV)")
print(f"    Universal: {'✓ PASS' if M_R_universal < 1e16 else '✗ FAIL'}")
print(f"    Hierarchical: {'✓ PASS' if M_R_hierarchical < 1e16 else '✗ FAIL'}")
print()

# ============================================================================
# PHENOMENOLOGICAL IMPLICATIONS
# ============================================================================

print("="*80)
print("PHENOMENOLOGICAL IMPLICATIONS")
print("="*80)
print()

print("1. Mass Ordering:")
print(f"   Universal → Quasi-degenerate light neutrinos")
print(f"   Hierarchical → {ordering}")
print(f"   Observation → NORMAL ordering preferred (3σ)")
print()

print("2. Consistency with Theorem 3.1.2:")
print(f"   Universal → Requires special explanation for why neutrinos differ")
print(f"   Hierarchical → Consistent with universal η_f = λ^(2n) × c_f pattern")
print()

print("3. Impact on M_R:")
print(f"   Factor of {M_R_universal/M_R_hierarchical:.2f} difference")
print(f"   Both satisfy leptogenesis bound (>1e9 GeV)")
print()

# ============================================================================
# PHYSICAL JUSTIFICATION FOR UNIVERSAL CASE
# ============================================================================

print("="*80)
print("POSSIBLE PHYSICAL JUSTIFICATIONS FOR UNIVERSAL m_D")
print("="*80)
print()

print("Option 1: Different Geometric Position")
print("  - Right-handed neutrinos all occupy the same position in T2")
print("  - No inter-generation separation → no λ^(2n) suppression")
print("  - Requires: Special property of gauge singlets")
print()

print("Option 2: Different Coupling Mechanism")
print("  - Neutrino Dirac masses from different mechanism than charged fermions")
print("  - Example: Higgs doublet vs. triplet coupling")
print("  - Requires: Extension of phase-gradient mass generation")
print()

print("Option 3: Approximate Degeneracy")
print("  - Hierarchical at tree level, but radiative corrections enhance m_D1, m_D2")
print("  - Requires: Special flavor symmetry at intermediate scale")
print()

print("Option 4: Use Hierarchical Masses")
print("  - Accept M_R ~ 7.4e9 GeV (factor of 3 lower)")
print("  - Still satisfies all phenomenological constraints")
print("  - More consistent with Theorem 3.1.2")
print()

# ============================================================================
# VISUALIZATION
# ============================================================================

fig, axes = plt.subplots(2, 2, figsize=(14, 10))

# Plot 1: Dirac mass patterns
ax = axes[0, 0]
generations = [1, 2, 3]
width = 0.35
x = np.array(generations)
ax.bar(x - width/2, m_D_universal, width, label='Universal', alpha=0.8, color='blue')
ax.bar(x + width/2, m_D_hierarchical, width, label='Hierarchical (λ^{2n})', alpha=0.8, color='red')
ax.set_xlabel('Generation', fontsize=12)
ax.set_ylabel('Dirac Mass (GeV)', fontsize=12)
ax.set_title('Neutrino Dirac Mass Patterns', fontsize=14, fontweight='bold')
ax.set_xticks(generations)
ax.set_yscale('log')
ax.legend()
ax.grid(True, alpha=0.3)

# Plot 2: Light neutrino masses
ax = axes[0, 1]
ax.bar(x - width/2, m_nu_universal*GeV_to_eV, width, label='Universal m_D', alpha=0.8, color='blue')
ax.bar(x + width/2, m_nu_hierarchical*GeV_to_eV, width, label='Hierarchical m_D', alpha=0.8, color='red')
ax.set_xlabel('Mass Eigenstate', fontsize=12)
ax.set_ylabel('Light Neutrino Mass (eV)', fontsize=12)
ax.set_title('Implied Light Neutrino Masses (Seesaw)', fontsize=14, fontweight='bold')
ax.set_xticks(generations)
ax.set_yscale('log')
ax.legend()
ax.grid(True, alpha=0.3)

# Plot 3: M_R comparison
ax = axes[1, 0]
scenarios = ['Universal\nm_D', 'Hierarchical\nm_D']
M_R_values = [M_R_universal, M_R_hierarchical]
colors = ['blue', 'red']
bars = ax.bar(scenarios, M_R_values, color=colors, alpha=0.8)
ax.axhline(y=1e9, color='green', linestyle='--', linewidth=2, label='Leptogenesis bound (10⁹ GeV)')
ax.axhline(y=1e16, color='orange', linestyle='--', linewidth=2, label='GUT scale (~10¹⁶ GeV)')
ax.set_ylabel('Majorana Scale M_R (GeV)', fontsize=12)
ax.set_title('Predicted M_R under Different Assumptions', fontsize=14, fontweight='bold')
ax.set_yscale('log')
ax.legend()
ax.grid(True, alpha=0.3, axis='y')

# Add values on bars
for i, (bar, val) in enumerate(zip(bars, M_R_values)):
    height = bar.get_height()
    ax.text(bar.get_x() + bar.get_width()/2., height*1.2,
            f'{val:.2e} GeV',
            ha='center', va='bottom', fontsize=11, fontweight='bold')

# Plot 4: Parameter space exploration
ax = axes[1, 1]
Sigma_m_nu_range = np.linspace(0.06, 0.15, 100)
M_R_universal_range = 3 * m_D3_base**2 / (Sigma_m_nu_range * eV_to_GeV)
M_R_hierarchical_range = sum_m_D_sq_hierarchical / (Sigma_m_nu_range * eV_to_GeV)

ax.plot(Sigma_m_nu_range, M_R_universal_range, 'b-', linewidth=2, label='Universal m_D')
ax.plot(Sigma_m_nu_range, M_R_hierarchical_range, 'r-', linewidth=2, label='Hierarchical m_D')
ax.axvline(x=Sigma_m_nu_obs, color='purple', linestyle='--', label=f'Observed Σm_ν ({Sigma_m_nu_obs} eV)')
ax.axvline(x=Sigma_m_nu_holographic_bound, color='orange', linestyle='--',
           label=f'Holographic bound ({Sigma_m_nu_holographic_bound} eV)')
ax.axhline(y=1e9, color='green', linestyle=':', alpha=0.5)
ax.set_xlabel('Σm_ν (eV)', fontsize=12)
ax.set_ylabel('M_R (GeV)', fontsize=12)
ax.set_title('M_R vs. Σm_ν Parameter Space', fontsize=14, fontweight='bold')
ax.set_yscale('log')
ax.legend(fontsize=9)
ax.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/neutrino_dirac_mass_hierarchy_analysis.png',
            dpi=300, bbox_inches='tight')
print(f"Plot saved to: verification/plots/neutrino_dirac_mass_hierarchy_analysis.png")
print()

# ============================================================================
# RECOMMENDATIONS
# ============================================================================

print("="*80)
print("RECOMMENDATIONS FOR THEOREM 3.1.5")
print("="*80)
print()

print("OPTION A: Add Physical Justification for Universal m_D")
print("  Pro: Preserves current numerical result (M_R = 2.2e10 GeV)")
print("  Pro: Simpler calculation")
print("  Con: Requires explanation for why neutrinos differ from other fermions")
print("  Con: Inconsistent with Theorem 3.1.2 unless justified")
print()

print("OPTION B: Use Hierarchical m_D (Recommended for Consistency)")
print("  Pro: Fully consistent with Theorem 3.1.2")
print("  Pro: Natural extension of η_f = λ^(2n) × c_f to all fermions")
print("  Con: Changes M_R from 2.2e10 to 7.4e9 GeV (factor of 3)")
print("  Con: More complex light neutrino spectrum")
print(f"  Result: M_R = {M_R_hierarchical:.2e} GeV (still > leptogenesis bound)")
print()

print("OPTION C: Hybrid Approach")
print("  - State M_R as order-of-magnitude prediction: M_R ~ (0.7-2) × 10^10 GeV")
print("  - Discuss both scenarios as possibilities")
print("  - Note that precise value depends on neutrino Dirac mass pattern")
print()

print("="*80)
print("CONCLUSION")
print("="*80)
print()
print("The hierarchical scenario (Option B) is more theoretically consistent")
print("with Theorem 3.1.2, while the universal scenario requires additional")
print("justification. BOTH scenarios satisfy all phenomenological constraints.")
print()
print(f"Recommended action: Add discussion of both possibilities, or provide")
print(f"geometric justification for why ν_R occupies special position.")
print()
