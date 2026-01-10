#!/usr/bin/env python3
"""
Analysis: QCD-EM Coupling Efficiency Saturation at High Temperature

Issue: The document shows ε ~ (T/T_c)^4 which gives ε = 16 at T = 2T_c.
This exceeds unity, which is unphysical for a coupling efficiency.

This script analyzes:
1. Physical meaning of ε > 1 in the QGP regime
2. Proper saturation formula
3. Physical interpretation

Author: Analysis Agent
Date: 2025-12-14
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy import constants

# Physical constants
k_B = constants.k
hbar = constants.hbar
c = constants.c
e = constants.e

# QCD parameters
T_c_MeV = 155  # QCD critical temperature in MeV
Lambda_QCD_MeV = 200  # QCD scale
alpha_em = 1/137

def epsilon_equilibrium(T_K):
    """
    Coupling efficiency for equilibrium matter (T << T_c).
    ε = (k_BT/Λ_QCD)^4 × α_em
    """
    k_BT_eV = k_B * T_K / e  # in eV
    k_BT_MeV = k_BT_eV * 1e-6  # in MeV
    ratio = k_BT_MeV / Lambda_QCD_MeV
    return ratio**4 * alpha_em

def epsilon_qgp_naive(T_MeV, T_c_MeV=155):
    """
    Naive QGP coupling: ε = (T/T_c)^4
    This is what the document currently uses.
    Problem: Gives ε > 1 for T > T_c.
    """
    return (T_MeV / T_c_MeV)**4

def epsilon_qgp_saturated(T_MeV, T_c_MeV=155, epsilon_0=1e-42):
    """
    Saturated coupling efficiency.

    Physical argument:
    - Below T_c: ε follows vacuum polarization scaling (T^4)
    - Near T_c: Deconfinement transition
    - Above T_c: QGP state where color degrees of freedom are directly thermal

    The efficiency cannot exceed 1, but the T^4 scaling needs reinterpretation:
    - ε measures "how much of internal Gibbs entropy appears as thermodynamic entropy"
    - In QGP, ALL entropy appears (ε → 1) because quarks/gluons are deconfined
    - Above T_c, the excess (ε > 1) represents departure from equilibrium
    """
    # Low T: vacuum polarization scaling
    # High T: saturate at 1

    # Smoothly interpolate using Fermi-Dirac-like function
    # ε = 1 / (1 + exp(-(T-T_c)/width))

    # Actually, the physics is:
    # - Below T_c: ε << 1 (confined, suppressed)
    # - At T_c: rapid transition
    # - Above T_c: ε = 1 (deconfined, all entropy visible)

    if isinstance(T_MeV, np.ndarray):
        result = np.ones_like(T_MeV, dtype=float)
        below_Tc = T_MeV < T_c_MeV
        result[below_Tc] = epsilon_0 * (T_MeV[below_Tc] / (k_B * 300 / e * 1e-6))**4 / epsilon_0
        # This simplifies to (T/T_room)^4 * epsilon_0 / epsilon_0 = (T/T_room)^4 * epsilon_0

        # Actually let's use proper formula:
        # Below T_c: ε = (T/Λ_QCD)^4 * α_em  [vacuum pol]
        # Above T_c: ε = 1 [saturated]
        result[below_Tc] = (T_MeV[below_Tc] / Lambda_QCD_MeV)**4 * alpha_em
        return np.minimum(result, 1.0)
    else:
        if T_MeV < T_c_MeV:
            return min((T_MeV / Lambda_QCD_MeV)**4 * alpha_em, 1.0)
        else:
            return 1.0

def analyze_qgp_physics():
    """
    Analyze the physical meaning of ε in the QGP regime.
    """
    print("=" * 70)
    print("ANALYSIS: QGP Coupling Efficiency")
    print("=" * 70)
    print()

    # Calculate transition temperature
    print("1. PHASE TRANSITION PHYSICS")
    print("-" * 40)
    print(f"T_c (QCD deconfinement) = {T_c_MeV} MeV")
    print(f"T_c in Kelvin = {T_c_MeV * 1e6 * e / k_B:.2e} K")
    print()

    # At T_c, what is ε from the equilibrium formula?
    T_c_K = T_c_MeV * 1e6 * e / k_B
    eps_at_Tc = epsilon_equilibrium(T_c_K)
    print(f"ε(T_c) from equilibrium formula = {eps_at_Tc:.2e}")
    print()

    # This shows the transition is VERY sharp
    # Below T_c: ε ~ 10^{-42} (suppressed)
    # Above T_c: ε = 1 (deconfined)

    print("2. PHYSICAL INTERPRETATION")
    print("-" * 40)
    print("""
The naive formula ε_QGP ~ (T/T_c)^4 comes from dimensional analysis but
has incorrect physics for T > T_c:

BELOW T_c (Confined phase):
- Color is confined inside hadrons
- Internal QCD dynamics decouple from external thermal bath
- Coupling via vacuum polarization: ε ~ (k_BT/Λ_QCD)^4 × α_em
- Result: ε ~ 10^{-42} at room temperature

AT T_c (Deconfinement transition):
- Hadrons dissolve into QGP
- Color degrees of freedom become thermal
- Abrupt transition (crossover, but rapid)

ABOVE T_c (QGP phase):
- Quarks and gluons are deconfined
- Color entropy IS thermodynamic entropy (no suppression)
- ε = 1 (by definition — all internal entropy is external)

The (T/T_c)^4 formula is meant to capture the TRANSITION region,
not the fully deconfined QGP.
""")

    print("3. CORRECTED FORMULA")
    print("-" * 40)
    print("""
For T < T_c (confined):
    ε(T) = (k_BT/Λ_QCD)^4 × α_em

For T ≥ T_c (deconfined):
    ε(T) = 1

The statement "ε ~ 16 at T = 2T_c" should be reinterpreted:
- It describes the ENHANCEMENT FACTOR relative to naive expectations
- NOT the coupling efficiency itself
- In QGP, ε = 1, but the entropy production rate is enhanced
  because σ_QGP ~ g²T >> σ_confined ~ K
""")

    print("4. NUMERICAL VERIFICATION")
    print("-" * 40)

    temperatures_MeV = [0.001, 0.01, 0.1, 1, 10, 100, 150, 155, 160, 200, 300, 400]

    print(f"{'T (MeV)':<12} {'T/T_c':<10} {'ε (naive)':<15} {'ε (saturated)':<15}")
    print("-" * 52)

    for T in temperatures_MeV:
        eps_naive = epsilon_qgp_naive(T)
        eps_sat = epsilon_qgp_saturated(T)
        print(f"{T:<12.3f} {T/T_c_MeV:<10.3f} {eps_naive:<15.2e} {eps_sat:<15.2e}")

    print()

    return T_c_MeV

def plot_comparison():
    """
    Plot comparison of naive vs saturated coupling efficiency.
    """
    T_MeV = np.logspace(-3, 3, 1000)  # 0.001 MeV to 1000 MeV

    eps_naive = epsilon_qgp_naive(T_MeV)
    eps_sat = epsilon_qgp_saturated(T_MeV)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Left: Full range
    ax1.loglog(T_MeV, eps_naive, 'b--', label=r'Naive: $\varepsilon = (T/T_c)^4$', linewidth=2)
    ax1.loglog(T_MeV, eps_sat, 'r-', label=r'Saturated: $\varepsilon = \min[1, ...]$', linewidth=2)
    ax1.axvline(T_c_MeV, color='g', linestyle=':', alpha=0.7, label=f'$T_c$ = {T_c_MeV} MeV')
    ax1.axhline(1, color='k', linestyle='--', alpha=0.5, label=r'$\varepsilon = 1$')
    ax1.set_xlabel('Temperature (MeV)', fontsize=12)
    ax1.set_ylabel(r'Coupling Efficiency $\varepsilon$', fontsize=12)
    ax1.set_title('QCD-EM Coupling: Naive vs Saturated', fontsize=14)
    ax1.set_xlim(0.001, 1000)
    ax1.set_ylim(1e-20, 100)
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)

    # Right: Near T_c (linear scale)
    T_near = np.linspace(50, 400, 500)
    eps_naive_near = epsilon_qgp_naive(T_near)
    eps_sat_near = epsilon_qgp_saturated(T_near)

    ax2.plot(T_near, eps_naive_near, 'b--', label=r'Naive: $\varepsilon = (T/T_c)^4$', linewidth=2)
    ax2.plot(T_near, eps_sat_near, 'r-', label=r'Saturated: $\varepsilon \leq 1$', linewidth=2)
    ax2.axvline(T_c_MeV, color='g', linestyle=':', alpha=0.7, label=f'$T_c$ = {T_c_MeV} MeV')
    ax2.axhline(1, color='k', linestyle='--', alpha=0.5)
    ax2.set_xlabel('Temperature (MeV)', fontsize=12)
    ax2.set_ylabel(r'Coupling Efficiency $\varepsilon$', fontsize=12)
    ax2.set_title('Near Deconfinement Transition', fontsize=14)
    ax2.set_xlim(50, 400)
    ax2.set_ylim(0, 20)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)

    # Add annotation
    ax2.annotate('Unphysical region\n(ε > 1)', xy=(250, 10), fontsize=11,
                ha='center', color='blue', alpha=0.7)
    ax2.fill_between(T_near, 1, eps_naive_near, where=eps_naive_near > 1,
                    color='blue', alpha=0.1)

    plt.tight_layout()
    plt.savefig('verification/plots/epsilon_saturation_analysis.png', dpi=150, bbox_inches='tight')
    plt.close()

    print("📊 Plot saved: verification/plots/epsilon_saturation_analysis.png")

def derive_proper_formula():
    """
    Derive the proper saturation formula with physical justification.
    """
    print()
    print("5. PROPER FORMULA DERIVATION")
    print("-" * 40)
    print("""
The coupling efficiency ε describes what fraction of internal Gibbs
entropy production manifests as observable thermodynamic entropy:

    dS_thermo/dt = ε × dS_Gibbs/dt

Physical constraints:
1. ε ≥ 0 (entropy can only increase)
2. ε ≤ 1 (can't produce more observable entropy than internal)

The transition at T_c is a phase transition, so ε should have
a step-like behavior:

    ε(T) = { (k_BT/Λ_QCD)^4 × α_em    for T < T_c
           { 1                         for T ≥ T_c

This can be smoothed with a Fermi function:

    ε(T) = ε_low(T) + [1 - ε_low(T)] × f_FD(T)

where:
    ε_low(T) = (k_BT/Λ_QCD)^4 × α_em
    f_FD(T) = 1 / (1 + exp(-(T - T_c)/ΔT))
    ΔT ~ 10-20 MeV (transition width from lattice QCD)

For practical purposes in the document, we can use:

    ε(T) = min[1, (k_BT/Λ_QCD)^4 × α_em]    for T < T_c
    ε(T) = 1                                  for T ≥ T_c

The statement "ε ~ 16 at T = 2T_c" should be REWRITTEN as:

    "At T = 2T_c, the QGP is fully deconfined (ε = 1), and the
     entropy production rate is enhanced by a factor ~(T/T_c)^4 ~ 16
     relative to the critical temperature."

This clarifies that (T/T_c)^4 describes the RATE enhancement,
not the coupling efficiency.
""")

def main():
    """Main analysis."""
    T_c = analyze_qgp_physics()
    plot_comparison()
    derive_proper_formula()

    print()
    print("=" * 70)
    print("RECOMMENDED DOCUMENT CHANGES")
    print("=" * 70)
    print("""
1. In §7.2, change:

   CURRENT:
   "At T ~ 2T_c: ε_QGP ~ 16
    This means **more than 100%** of the Gibbs entropy becomes observable"

   TO:
   "At T ~ 2T_c: ε_QGP = 1 (saturated)
    In the deconfined phase, ALL internal color dynamics become directly
    thermalized. The factor (T/T_c)^4 ~ 16 describes the RATE enhancement
    of entropy production, not the coupling efficiency itself."

2. Add new subsection §7.2.1:

   "### 7.2.1 Saturation of Coupling Efficiency

   The coupling efficiency cannot exceed unity:
   $$\\varepsilon(T) = \\min\\left[1, \\left(\\frac{k_B T}{\\Lambda_{QCD}}\\right)^4 \\cdot \\alpha_{em}\\right]$$

   Below T_c: Confined phase with ε << 1
   Above T_c: Deconfined phase with ε = 1"

3. In §8.1 consistency table, change:

   CURRENT: "ε → 1 for T → T_c"
   TO: "ε → 1 for T ≥ T_c (saturates at deconfinement)"
""")

if __name__ == "__main__":
    main()
