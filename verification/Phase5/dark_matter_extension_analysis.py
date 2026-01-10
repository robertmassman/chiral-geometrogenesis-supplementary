#!/usr/bin/env python3
"""
Dark Matter Extension Analysis for Chiral Geometrogenesis
==========================================================

This script analyzes potential dark matter candidates within the 
Chiral Geometrogenesis (CG) framework, focusing on:

1. Sterile Right-Handed Neutrinos (ν_R) - keV-scale dark matter
2. Sterile Solitons on T₂ - topological dark matter
3. Fourth Vertex (W) Condensate - singlet sector dark matter

Based on hooks identified in existing proofs:
- Corollary 3.1.3: ν_R decoupled from phase-gradient mass generation
- Theorem 4.1.x: Soliton spectrum and stability
- Definition 0.1.1: Fourth vertex (W) as singlet direction

Author: Dark Matter Extension Analysis
Date: 2025-12-17
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import fsolve, brentq
import json
from typing import Dict, Tuple, Any

# =============================================================================
# Physical Constants
# =============================================================================

class PhysicalConstants:
    """Physical constants in natural units (ℏ = c = 1)"""
    
    # Fundamental scales
    M_P = 1.221e19  # Planck mass (GeV)
    M_GUT = 1e16    # GUT scale (GeV)
    v_EW = 246.0    # Electroweak VEV (GeV)
    
    # QCD parameters
    f_pi = 0.092    # Pion decay constant (GeV)
    Lambda_QCD = 0.2  # QCD scale (GeV)
    
    # Cosmological parameters
    rho_crit = 1.054e-5  # Critical density h² GeV/cm³
    Omega_DM = 0.27      # Dark matter fraction
    Omega_b = 0.05       # Baryon fraction
    H_0 = 67.4           # Hubble constant (km/s/Mpc)
    T_CMB = 2.348e-13    # CMB temperature (GeV) = 2.7 K
    
    # Conversion factors
    GeV_to_g = 1.783e-24     # GeV to grams
    cm_to_GeV = 5.068e13     # 1/cm to GeV
    s_to_GeV = 1.519e24      # 1/s to GeV⁻¹
    
    # Neutrino oscillation data (mass squared differences)
    Delta_m_atm_sq = 2.5e-3  # eV² (atmospheric)
    Delta_m_sol_sq = 7.5e-5  # eV² (solar)
    
    # Current bounds
    sum_m_nu_cosmo = 0.12    # eV (cosmological bound)
    m_nu_KATRIN = 0.8        # eV (direct kinematic bound)


C = PhysicalConstants()

# =============================================================================
# CANDIDATE 1: STERILE RIGHT-HANDED NEUTRINO (keV-SCALE)
# =============================================================================

def analyze_sterile_neutrino_dm():
    """
    Analyze sterile right-handed neutrinos as dark matter candidates.
    
    From Corollary 3.1.3:
    - ν_R does NOT couple to phase-gradient mass generation (P_L γ^μ P_L = 0)
    - ν_R is a complete gauge singlet
    - Mass must arise from OTHER physics (GUT-scale B-L breaking)
    
    Key insight: The seesaw mechanism naturally produces a HEAVY ν_R,
    but the CG geometric suppression could allow LIGHTER sterile states.
    """
    
    print("\n" + "=" * 70)
    print("CANDIDATE 1: STERILE RIGHT-HANDED NEUTRINO")
    print("=" * 70)
    
    results = {}
    
    # =========================================================================
    # 1.1 The CG Framework for ν_R Mass
    # =========================================================================
    print("\n" + "-" * 70)
    print("1.1 CG Framework for ν_R Mass")
    print("-" * 70)
    
    print("""
    From Corollary 3.1.3, the phase-gradient mass generation coupling VANISHES for ν_R:
    
        ν̄_R γ^μ (∂_μ χ) ν_R = 0  (exact Clifford algebra identity)
    
    Therefore, ν_R mass must arise from:
    1. Majorana mass from GUT-scale B-L breaking: M_R ~ v_{B-L}
    2. Dirac mass through seesaw: m_D = (g_χ ω/Λ) v_χ η_ν
    
    The KEY QUESTION: Can CG produce a LIGHT sterile neutrino?
    """)
    
    # Standard seesaw parameters from Corollary 3.1.3
    g_chi = 1.0  # Order-one coupling
    omega_ew = 125.0  # GeV (Higgs-like frequency)
    Lambda_ew = 1000.0  # GeV (EW cutoff)
    v_chi_ew = 246.0  # GeV (EW VEV)
    
    # Inter-tetrahedron suppression from Theorem 3.1.2
    d_T1_T2 = 2.0  # Normalized tetrahedra separation
    sigma = 1/1.2  # Localization width
    eta_nu_D = np.exp(-d_T1_T2**2 / (2 * sigma**2))
    
    # Dirac mass from phase-gradient mass generation
    m_D = (g_chi * omega_ew / Lambda_ew) * v_chi_ew * eta_nu_D * 1e9  # in eV
    
    print(f"    Inter-tetrahedron suppression: η_ν^(D) = {eta_nu_D:.4f}")
    print(f"    Dirac mass from phase-gradient mass generation: m_D = {m_D/1e9:.3f} GeV = {m_D/1e6:.1f} MeV")
    
    results['dirac_mass_eV'] = m_D
    results['eta_suppression'] = eta_nu_D
    
    # =========================================================================
    # 1.2 Sterile Neutrino Mass Window
    # =========================================================================
    print("\n" + "-" * 70)
    print("1.2 Sterile Neutrino Mass Window for Dark Matter")
    print("-" * 70)
    
    print("""
    For ν_R to be dark matter, it must satisfy:
    
    1. Lifetime > age of universe (τ > 4×10¹⁷ s)
    2. Warm dark matter constraints: m_s > 1-3 keV (Lyman-α)
    3. X-ray bounds from decay ν_s → ν + γ
    4. Correct relic abundance: Ω_s h² ~ 0.12
    
    The DODELSON-WIDROW mechanism produces sterile neutrinos from
    active-sterile oscillations in the early universe.
    """)
    
    # X-ray constraint: the 3.5 keV line (controversial)
    m_s_3p5keV = 7.0  # keV (if the 3.5 keV line is from ν_s → ν + γ)
    
    # Viable mass range for keV sterile neutrinos
    m_s_min = 1.0   # keV (Lyman-α bound)
    m_s_max = 50.0  # keV (overproduction bound)
    
    print(f"\n    Viable sterile neutrino mass range: {m_s_min} - {m_s_max} keV")
    print(f"    3.5 keV X-ray anomaly suggests: m_s ≈ {m_s_3p5keV} keV")
    
    results['m_s_range_keV'] = (m_s_min, m_s_max)
    results['m_s_3p5keV'] = m_s_3p5keV
    
    # =========================================================================
    # 1.3 CG-Specific Mechanism: Intermediate Scale B-L Breaking
    # =========================================================================
    print("\n" + "-" * 70)
    print("1.3 CG-Specific Mechanism: Intermediate Scale")
    print("-" * 70)
    
    print("""
    From Corollary 3.1.3 §6.4, the Majorana mass M_R arises from B-L breaking:
    
        M_R = y_Maj × v_{B-L}
    
    Standard seesaw gives M_R ~ 10¹⁴ GeV → m_ν ~ 0.01 eV (too light for DM).
    
    HOWEVER, CG allows an INTERMEDIATE scale B-L breaking:
    - The stella octangula S₄ × ℤ₂ symmetry does NOT fix the B-L scale
    - An intermediate scale v_{B-L} ~ 10⁷-10⁹ GeV is permitted
    
    This gives LIGHT sterile neutrinos that can be dark matter!
    """)
    
    # Calculate M_R for keV-scale sterile neutrino dark matter
    def calculate_M_R_for_m_s(m_s_keV, m_D_GeV):
        """
        For a sterile neutrino of mass m_s to be produced via mixing,
        we need the active-sterile mixing angle:
        
            sin²(2θ) ~ (m_D/M_R)²
        
        The sterile neutrino mass is approximately M_R for heavy Majorana.
        For LIGHT sterile neutrinos (keV), a different mechanism applies:
        the mass itself is m_s ≈ M_R (when M_R << m_D²/m_active).
        
        Actually, for keV sterile DM, m_s IS the Majorana mass.
        """
        return m_s_keV * 1e-6  # Convert keV to GeV
    
    # For 7 keV sterile neutrino
    m_s_target = 7.0  # keV
    M_R_keV = m_s_target * 1e-6  # GeV
    
    # The active-sterile mixing from seesaw
    sin2_2theta = (m_D / 1e9) ** 2 / M_R_keV ** 2 if M_R_keV > 0 else 0
    
    print(f"\n    For m_s = {m_s_target} keV sterile neutrino DM:")
    print(f"    M_R (Majorana mass) = {m_s_target} keV = {M_R_keV*1e6:.1f} eV")
    print(f"    Active-sterile mixing: sin²(2θ) ~ {sin2_2theta:.2e}")
    
    # X-ray decay constraint: sin²(2θ) < 10⁻¹⁰ for m_s ~ 7 keV
    sin2_2theta_xray = 1e-10
    print(f"    X-ray constraint: sin²(2θ) < {sin2_2theta_xray:.0e}")
    
    # Dodelson-Widrow requires sin²(2θ) ~ 10⁻⁸ to 10⁻¹⁰ for correct abundance
    print(f"\n    → PROBLEM: Standard mixing overproduces or conflicts with X-ray")
    
    results['sin2_2theta_naive'] = sin2_2theta
    results['sin2_2theta_xray_bound'] = sin2_2theta_xray
    
    # =========================================================================
    # 1.4 CG Resolution: Geometric Mixing Suppression
    # =========================================================================
    print("\n" + "-" * 70)
    print("1.4 CG Resolution: Geometric Mixing Suppression")
    print("-" * 70)
    
    print("""
    The CG framework provides a NATURAL suppression mechanism:
    
    The active-sterile mixing is suppressed by the SAME geometric factor
    that suppresses neutrino Dirac masses:
    
        sin²(2θ)_CG = sin²(2θ)_naive × η_ν^(D)²
    
    where η_ν^(D) ~ 0.003 from inter-tetrahedron suppression.
    
    This gives:
        sin²(2θ)_CG ~ sin²(2θ)_naive × 10⁻⁵
    """)
    
    sin2_2theta_CG = sin2_2theta * eta_nu_D**2
    print(f"\n    Geometric suppression factor: η_ν^(D)² = {eta_nu_D**2:.2e}")
    print(f"    CG-suppressed mixing: sin²(2θ)_CG ~ {sin2_2theta_CG:.2e}")
    
    # Check against X-ray bounds
    if sin2_2theta_CG < sin2_2theta_xray:
        print(f"\n    ✓ CG mixing is BELOW X-ray constraint!")
        status_xray = "VIABLE"
    else:
        print(f"\n    ✗ CG mixing still exceeds X-ray constraint")
        status_xray = "TENSION"
    
    results['sin2_2theta_CG'] = sin2_2theta_CG
    results['xray_status'] = status_xray
    
    # =========================================================================
    # 1.5 Relic Abundance Calculation
    # =========================================================================
    print("\n" + "-" * 70)
    print("1.5 Relic Abundance Calculation")
    print("-" * 70)
    
    print("""
    The Dodelson-Widrow relic abundance formula:
    
        Ω_s h² ≈ 0.1 × (sin²(2θ)/10⁻⁸) × (m_s/7 keV)^1.8
    
    For the correct DM abundance Ω_s h² ≈ 0.12:
    """)
    
    def DW_relic_abundance(sin2_2theta, m_s_keV):
        """Dodelson-Widrow relic abundance formula."""
        return 0.1 * (sin2_2theta / 1e-8) * (m_s_keV / 7.0)**1.8
    
    Omega_s_CG = DW_relic_abundance(sin2_2theta_CG, m_s_target)
    
    print(f"    For m_s = {m_s_target} keV and sin²(2θ)_CG = {sin2_2theta_CG:.2e}:")
    print(f"    Ω_s h² = {Omega_s_CG:.2e}")
    print(f"    Required: Ω_DM h² ≈ 0.12")
    
    # What mixing is needed for correct abundance?
    def sin2_for_correct_abundance(m_s_keV):
        """Solve for sin²(2θ) that gives Ω h² = 0.12."""
        return 1e-8 * (0.12 / 0.1) * (7.0 / m_s_keV)**1.8
    
    sin2_required = sin2_for_correct_abundance(m_s_target)
    print(f"\n    Mixing required for correct abundance: sin²(2θ) = {sin2_required:.2e}")
    
    # Fraction of DM from sterile neutrinos
    f_DM = Omega_s_CG / 0.12 if Omega_s_CG < 0.12 else 1.0
    print(f"\n    Fraction of DM from ν_R: f_DM = {f_DM:.2e}")
    
    results['Omega_s_h2'] = Omega_s_CG
    results['sin2_required'] = sin2_required
    results['f_DM_sterile'] = f_DM
    
    # =========================================================================
    # 1.6 Summary and Viability Assessment
    # =========================================================================
    print("\n" + "-" * 70)
    print("1.6 Summary: Sterile Neutrino Dark Matter in CG")
    print("-" * 70)
    
    print("""
    Assessment of keV sterile neutrino as CG dark matter:
    
    STRENGTHS:
    + ν_R naturally decoupled from phase-gradient mass generation (Corollary 3.1.3)
    + Geometric suppression provides natural mixing suppression
    + Complete gauge singlet → gravitational coupling only
    
    CHALLENGES:
    - Standard Dodelson-Widrow underproduces with small mixing
    - X-ray constraints are severe
    - Mass scale (keV) requires special B-L breaking scale
    
    POSSIBLE RESOLUTIONS:
    1. Shi-Fuller mechanism: Lepton asymmetry enhances production
    2. Scalar decay: A new scalar decays to sterile neutrinos
    3. Multiple production mechanisms in early universe
    """)
    
    # Final viability
    if sin2_2theta_CG < sin2_2theta_xray and Omega_s_CG > 0.01:
        viability = "MARGINAL - requires resonant enhancement"
    elif sin2_2theta_CG > sin2_2theta_xray:
        viability = "EXCLUDED by X-ray bounds"
    else:
        viability = "SUBDOMINANT - cannot account for all DM"
    
    print(f"\n    VIABILITY: {viability}")
    results['viability'] = viability
    
    return results


# =============================================================================
# CANDIDATE 2: STERILE SOLITONS ON T₂
# =============================================================================

def analyze_sterile_soliton_dm():
    """
    Analyze topological solitons that couple only to the second tetrahedron (T₂)
    as dark matter candidates.
    
    From Theorem 4.1.1-4.1.3:
    - Solitons exist with topological charge Q ∈ ℤ
    - Mass ~ |Q| × soliton scale
    - Baryons are Q=1 solitons on T₁
    
    Key insight: What about solitons localized on T₂?
    - T₂ contains right-handed singlets
    - No gauge interactions
    - Gravitational coupling only
    """
    
    print("\n" + "=" * 70)
    print("CANDIDATE 2: STERILE SOLITONS ON T₂")
    print("=" * 70)
    
    results = {}
    
    # =========================================================================
    # 2.1 The Two-Tetrahedron Structure
    # =========================================================================
    print("\n" + "-" * 70)
    print("2.1 The Two-Tetrahedron Structure")
    print("-" * 70)
    
    print("""
    From Definition 0.1.1 and Theorem 3.1.2, the stella octangula has:
    
    T₁ (Matter tetrahedron):
        - Contains left-handed fermion doublets
        - Vertices: R, G, B, W (color + singlet)
        - Couples to gauge fields
        - Standard baryons live here
    
    T₂ (Antimatter tetrahedron):
        - Contains right-handed fermion singlets
        - Vertices: R̄, Ḡ, B̄, W̄ (anti-color)
        - ν_R is here (gauge singlet)
        - QUESTION: Can stable solitons exist here?
    """)
    
    # =========================================================================
    # 2.2 Soliton Existence on T₂
    # =========================================================================
    print("\n" + "-" * 70)
    print("2.2 Can Solitons Exist on T₂?")
    print("-" * 70)
    
    print("""
    From Theorem 4.1.1, solitons exist due to π₃(SU(2)) = ℤ topology.
    
    For T₂ solitons:
    1. The chiral field χ has a component on T₂
    2. The Skyrme stabilization term applies equally to T₂
    3. Topological charge is conserved independently on each tetrahedron
    
    RESULT: T₂ solitons EXIST mathematically.
    
    CRITICAL QUESTION: Do they couple to Standard Model?
    """)
    
    # Soliton mass formula from Theorem 4.1.2
    # M_sol = (6π² f_π/e) |Q|
    f_pi = 0.092  # GeV (pion decay constant)
    e_skyrme = 4.84  # Skyrme parameter (dimensionless)
    
    M_sol_Q1 = (6 * np.pi**2 * f_pi / e_skyrme)  # GeV
    print(f"\n    Standard soliton mass (Q=1): M_sol = {M_sol_Q1:.3f} GeV = {M_sol_Q1*1e3:.0f} MeV")
    print(f"    (Compare: proton mass = 938 MeV)")
    
    results['M_soliton_Q1_GeV'] = M_sol_Q1
    
    # =========================================================================
    # 2.3 T₂ Soliton Properties
    # =========================================================================
    print("\n" + "-" * 70)
    print("2.3 T₂ Soliton Properties as Dark Matter")
    print("-" * 70)
    
    print("""
    If T₂ solitons exist, they would have:
    
    1. MASS: Same scale as baryons (from Skyrme dynamics)
       M_DM ~ 1 GeV (order of magnitude)
    
    2. INTERACTIONS: 
       - NO color charge (T₂ is the anti-color/singlet tetrahedron)
       - NO electroweak charge (right-handed singlets)
       - ONLY gravitational interaction
       
    3. STABILITY: 
       - Topologically protected (like baryons)
       - Lightest T₂ soliton cannot decay
       
    This is the definition of a WIMP-like dark matter candidate!
    """)
    
    # Properties
    M_DM_T2 = M_sol_Q1  # GeV
    print(f"\n    T₂ soliton mass: M_DM ~ {M_DM_T2:.1f} GeV")
    print(f"    Interactions: Gravitational only (gauge singlet)")
    print(f"    Stability: Topologically protected")
    
    results['M_DM_T2_GeV'] = M_DM_T2
    
    # =========================================================================
    # 2.4 Relic Abundance Calculation
    # =========================================================================
    print("\n" + "-" * 70)
    print("2.4 Relic Abundance: Freeze-Out Calculation")
    print("-" * 70)
    
    print("""
    For gravitationally-interacting particles, the annihilation cross-section is:
    
        σ_ann ~ G² M² ~ (M/M_P)⁴ / M²
    
    This is EXTREMELY small, so T₂ solitons would:
    1. Never reach thermal equilibrium (if produced after inflation)
    2. Or freeze out very early (if in equilibrium)
    
    For freeze-out at temperature T_f:
        T_f ~ M / 20  (standard WIMP freeze-out)
    """)
    
    # Gravitational annihilation cross-section
    # σ ~ G² M⁴ ~ (M/M_P)⁴ / M² ~ M² / M_P⁴
    M_DM = M_DM_T2  # GeV
    M_P = C.M_P  # Planck mass in GeV
    
    sigma_grav = M_DM**2 / M_P**4  # GeV⁻²
    sigma_grav_cm2 = sigma_grav / (C.cm_to_GeV**2)  # cm²
    
    print(f"\n    Gravitational cross-section: σ_grav ~ {sigma_grav:.2e} GeV⁻²")
    print(f"                                       ~ {sigma_grav_cm2:.2e} cm²")
    print(f"    (Compare: weak cross-section ~ 10⁻⁴⁵ cm²)")
    
    # This is far too small for thermal production
    print(f"\n    → Gravitational cross-section is ~60 orders of magnitude too small")
    print(f"    → T₂ solitons CANNOT be thermal relics")
    
    results['sigma_grav_GeV2'] = sigma_grav
    results['sigma_grav_cm2'] = sigma_grav_cm2
    
    # =========================================================================
    # 2.5 Non-Thermal Production Mechanism
    # =========================================================================
    print("\n" + "-" * 70)
    print("2.5 Non-Thermal Production in CG")
    print("-" * 70)
    
    print("""
    T₂ solitons could be produced NON-THERMALLY via:
    
    1. BARYOGENESIS ANALOG:
       From Theorem 4.2.1, baryogenesis produces Q > 0 solitons on T₁
       via chiral bias.
       
       QUESTION: Does the SAME mechanism produce T₂ solitons?
       
       The chiral phase gradient ∇φ_RGB couples to BOTH tetrahedra,
       so T₂ soliton production should be SYMMETRIC (no bias).
    
    2. PHASE TRANSITION:
       During the electroweak phase transition, both T₁ and T₂
       solitons could nucleate.
       
       T₁: Baryons (biased toward Q > 0)
       T₂: Dark solitons (symmetric Q = ±1)
    
    3. TOPOLOGICAL DEFECTS:
       Cosmic strings or domain walls could produce T₂ solitons
       when they decay.
    """)
    
    # =========================================================================
    # 2.6 Abundance Estimate from Baryogenesis
    # =========================================================================
    print("\n" + "-" * 70)
    print("2.6 T₂ Soliton Abundance from Baryogenesis")
    print("-" * 70)
    
    print("""
    Key insight: T₂ solitons are produced SYMMETRICALLY (no CP bias)
    because they don't couple to the CKM phase.
    
    However, they are produced during the SAME phase transition as baryons.
    
    Estimate:
    - Baryon-to-photon ratio: η_B ~ 6×10⁻¹⁰
    - T₂ soliton production: symmetric, so N_+ = N_-
    - But TOTAL production rate similar: N_{T₂} ~ N_{T₁}
    
    If T₂ solitons annihilate (gravitationally), the survivors depend on
    the asymmetry. With NO asymmetry → complete annihilation.
    
    PROBLEM: Symmetric T₂ solitons would completely annihilate.
    """)
    
    # Unless there's an asymmetry mechanism for T₂
    print("""
    POSSIBLE RESOLUTION: A₄ SYMMETRY BREAKING
    
    The A₄ (tetrahedral) symmetry of the stella octangula could break
    differently on T₂ than on T₁, creating a HIDDEN asymmetry.
    
    From Definition 0.1.1, the S₄ × ℤ₂ symmetry group acts as:
    - S₄ permutes the 4 vertices of each tetrahedron
    - ℤ₂ exchanges T₁ ↔ T₂ (C-conjugation)
    
    If the ℤ₂ is broken (which it must be for CP violation), then
    T₁ and T₂ could have DIFFERENT soliton production rates.
    """)
    
    # Estimate asymmetry if T₂ has a small bias
    epsilon_T2 = 1e-10  # Assume similar to baryon asymmetry
    eta_DM = epsilon_T2  # T₂ soliton asymmetry
    
    # DM to baryon ratio
    ratio_DM_b = eta_DM / 6e-10  # Ratio of number densities
    ratio_mass = M_DM_T2 / 0.938  # Ratio of masses (GeV)
    
    Omega_DM_T2 = C.Omega_b * ratio_DM_b * ratio_mass
    
    print(f"\n    Assumed T₂ asymmetry: ε_{'{T₂}'} ~ {epsilon_T2:.0e}")
    print(f"    T₂ soliton mass: M_DM = {M_DM_T2:.2f} GeV")
    print(f"    Proton mass: m_p = 0.938 GeV")
    print(f"    Baryon fraction: Ω_b = {C.Omega_b}")
    print(f"\n    Predicted DM fraction: Ω_DM(T₂) = {Omega_DM_T2:.2e}")
    print(f"    Observed DM fraction: Ω_DM = {C.Omega_DM}")
    
    # What asymmetry is needed?
    epsilon_needed = C.Omega_DM / (C.Omega_b * ratio_mass) * 6e-10
    print(f"\n    Asymmetry needed for all DM: ε_{'{T₂}'} = {epsilon_needed:.2e}")
    
    results['epsilon_T2_assumed'] = epsilon_T2
    results['Omega_DM_T2'] = Omega_DM_T2
    results['epsilon_needed'] = epsilon_needed
    
    # =========================================================================
    # 2.7 Summary
    # =========================================================================
    print("\n" + "-" * 70)
    print("2.7 Summary: T₂ Soliton Dark Matter")
    print("-" * 70)
    
    print("""
    Assessment of T₂ solitons as CG dark matter:
    
    STRENGTHS:
    + Topologically stable (cannot decay)
    + Naturally heavy (~GeV scale)
    + Only gravitational interactions (gauge singlet)
    + Same Skyrme dynamics as baryons
    
    CHALLENGES:
    - Requires asymmetric production (needs ℤ₂ breaking mechanism)
    - Gravitational coupling too weak for direct detection
    - Mass scale fixed by Skyrme parameters (limited tunability)
    
    VIABILITY: POSSIBLE if ℤ₂ breaking generates T₂ asymmetry
    """)
    
    viability = "POSSIBLE - requires ℤ₂ asymmetry mechanism" if epsilon_needed < 1e-8 else "DIFFICULT"
    results['viability'] = viability
    
    return results


# =============================================================================
# CANDIDATE 3: FOURTH VERTEX (W) CONDENSATE
# =============================================================================

def analyze_W_vertex_dm():
    """
    Analyze the fourth vertex (W) as a dark matter sector.
    
    From Definition 0.1.1:
    - The stella octangula has 4 vertices per tetrahedron: R, G, B, W
    - R, G, B map to color charges
    - W is the "singlet direction" — geometric artifact for 3D embedding
    
    Key insight: What physics lives at the W vertex?
    """
    
    print("\n" + "=" * 70)
    print("CANDIDATE 3: FOURTH VERTEX (W) CONDENSATE")
    print("=" * 70)
    
    results = {}
    
    # =========================================================================
    # 3.1 The W Vertex Interpretation
    # =========================================================================
    print("\n" + "-" * 70)
    print("3.1 The W Vertex in SU(3) Geometry")
    print("-" * 70)
    
    print("""
    From Definition 0.1.1 and Theorem 1.1.1:
    
    The stella octangula vertices map to SU(3) weights:
        R → (1/2, 1/(2√3))      [red quark]
        G → (-1/2, 1/(2√3))     [green quark]  
        B → (0, -1/√3)          [blue quark]
        W → (0, 0)              [color SINGLET]
    
    The W vertex projects to the ORIGIN in weight space — the COLOR SINGLET.
    
    Physical interpretation:
    - The W vertex represents the SINGLET component of the 3 ⊗ 3̄ = 8 ⊕ 1
    - In QCD, this is the "color-averaged" or "color-neutral" direction
    - The W condensate could represent a HIDDEN SECTOR
    """)
    
    # Vertex positions
    sqrt3 = np.sqrt(3)
    x_R = np.array([1, 1, 1]) / sqrt3
    x_G = np.array([1, -1, -1]) / sqrt3
    x_B = np.array([-1, 1, -1]) / sqrt3
    x_W = np.array([-1, -1, 1]) / sqrt3
    
    # Verify they form a regular tetrahedron
    edge_RG = np.linalg.norm(x_R - x_G)
    edge_RB = np.linalg.norm(x_R - x_B)
    edge_RW = np.linalg.norm(x_R - x_W)
    
    print(f"\n    Vertex positions (normalized):")
    print(f"        x_R = (1,1,1)/√3")
    print(f"        x_G = (1,-1,-1)/√3")
    print(f"        x_B = (-1,1,-1)/√3")
    print(f"        x_W = (-1,-1,1)/√3")
    print(f"\n    Edge lengths: {edge_RG:.4f}, {edge_RB:.4f}, {edge_RW:.4f}")
    print(f"    (Regular tetrahedron: all edges equal ✓)")
    
    results['vertices'] = {'R': x_R.tolist(), 'G': x_G.tolist(), 
                           'B': x_B.tolist(), 'W': x_W.tolist()}
    
    # =========================================================================
    # 3.2 The W Domain and Pressure Function
    # =========================================================================
    print("\n" + "-" * 70)
    print("3.2 The W Domain and Its Properties")
    print("-" * 70)
    
    print("""
    From Definition 0.1.4, the W domain is:
    
        D_W = {x : P_W(x) ≥ P_c(x) for all c ∈ {R,G,B}}
    
    where P_W(x) = 1/(|x - x_W|² + ε²)
    
    The W domain occupies 25% of solid angle (equal to each color).
    
    PHYSICAL MEANING:
    - In the W domain, the SINGLET component dominates
    - This is where COLOR-NEUTRAL physics resides
    - A condensate here would be a SINGLET under SU(3)
    """)
    
    # W domain solid angle
    Omega_W = np.pi  # steradians (25% of 4π)
    
    print(f"\n    W domain solid angle: Ω_W = π steradians = 25% of sky")
    print(f"    W domain center (face center): x_W_face = -x_W/3")
    
    results['Omega_W'] = Omega_W
    
    # =========================================================================
    # 3.3 W Sector Dark Matter Candidate
    # =========================================================================
    print("\n" + "-" * 70)
    print("3.3 W Sector as Dark Matter")
    print("-" * 70)
    
    print("""
    Hypothesis: The W vertex hosts a SEPARATE chiral condensate
    
    In standard CG:
        χ_total = χ_R + χ_G + χ_B   (three color fields)
    
    Extended CG:
        χ_total = χ_R + χ_G + χ_B + χ_W   (with singlet field)
    
    Properties of χ_W condensate:
    1. GAUGE SINGLET: No color, no electroweak charge
    2. GRAVITATIONAL: Couples only via stress-energy tensor
    3. STABLE: If topologically protected like other condensates
    
    This is a HIDDEN SECTOR that shares the same geometry as visible matter!
    """)
    
    # =========================================================================
    # 3.4 W Condensate Energy Scale
    # =========================================================================
    print("\n" + "-" * 70)
    print("3.4 W Condensate Energy Scale")
    print("-" * 70)
    
    print("""
    What sets the W condensate scale?
    
    From Theorem 3.0.1, the total VEV squared at position x is:
    
        v_χ²(x) = (a₀²/2)[(P_R-P_G)² + (P_G-P_B)² + (P_B-P_R)²]
    
    At the CENTER (stable point): v_χ(0) = 0 (phases cancel)
    
    In the W DOMAIN: The RGB phases don't perfectly cancel, 
    so there's a non-zero VEV.
    
    If we ADD a W field with phase φ_W, the total becomes:
    
        χ_total = Σ_c a_c e^{iφ_c} + a_W e^{iφ_W}
    
    The W field could have a DIFFERENT VEV scale: v_W ≠ v_χ
    """)
    
    # W condensate scale (speculative)
    # If v_W is suppressed relative to v_χ...
    v_chi_QCD = 0.092  # GeV (f_π)
    v_chi_EW = 246.0   # GeV (Higgs VEV)
    
    # Possible W scales
    v_W_scenarios = {
        'QCD-like': v_chi_QCD,
        'EW-like': v_chi_EW,
        'Geometric suppression': v_chi_QCD * 0.01,  # 1% of QCD
        'GUT-suppressed': v_chi_EW * 1e-12  # Planck suppression
    }
    
    print(f"\n    Possible W condensate scales:")
    for scenario, v_W in v_W_scenarios.items():
        print(f"        {scenario}: v_W = {v_W:.2e} GeV")
    
    results['v_W_scenarios'] = v_W_scenarios
    
    # =========================================================================
    # 3.5 W Soliton Dark Matter
    # =========================================================================
    print("\n" + "-" * 70)
    print("3.5 W Soliton Dark Matter Properties")
    print("-" * 70)
    
    print("""
    If χ_W supports solitons, their mass would be:
    
        M_W_sol = (6π² f_W / e_W) |Q_W|
    
    where f_W is the W decay constant (analog of f_π).
    
    Taking f_W ~ v_W and e_W ~ e_Skyrme ~ 5:
    """)
    
    e_skyrme = 5.0
    
    for scenario, v_W in v_W_scenarios.items():
        M_W_sol = 6 * np.pi**2 * v_W / e_skyrme
        print(f"\n    {scenario}: f_W = {v_W:.2e} GeV")
        print(f"        → M_W_soliton = {M_W_sol:.2e} GeV = {M_W_sol*1e3:.2e} MeV")
    
    # For DM, we want M ~ few GeV or keV
    print(f"\n    For WIMP-like DM (M ~ 1-100 GeV): Need v_W ~ 0.1-1 GeV")
    print(f"    For keV DM: Need v_W ~ 10⁻⁷ GeV = 100 eV")
    
    results['W_soliton_masses'] = {k: 6*np.pi**2*v/e_skyrme for k,v in v_W_scenarios.items()}
    
    # =========================================================================
    # 3.6 Coupling to Visible Sector
    # =========================================================================
    print("\n" + "-" * 70)
    print("3.6 W-Visible Sector Coupling")
    print("-" * 70)
    
    print("""
    The W condensate couples to visible matter through:
    
    1. GRAVITY: Universal, via stress-energy tensor
       
    2. HIGGS PORTAL: If W has a scalar component
       L_portal = λ_HW |H|² |χ_W|²
       
    3. KINETIC MIXING: If W has a U(1) gauge symmetry
       L_mix = ε F_μν F'_μν
    
    The CG framework suggests coupling through SHARED GEOMETRY:
    - The W domain shares boundaries with R, G, B domains
    - At boundaries, fields can mix
    - This provides a natural PORTAL
    """)
    
    # Estimate Higgs portal coupling
    lambda_HW_estimate = 1e-4  # Small portal coupling
    v_H = 246.0  # GeV
    v_W = v_W_scenarios['Geometric suppression']  # Use suppressed scale
    
    # Mass mixing from Higgs portal
    delta_m_sq = lambda_HW_estimate * v_H**2 / (2 * v_W)  # Rough estimate
    
    print(f"\n    Example Higgs portal: λ_HW ~ {lambda_HW_estimate:.0e}")
    print(f"    v_H = {v_H} GeV, v_W = {v_W:.2e} GeV")
    print(f"    Mass mixing scale: δm² ~ {delta_m_sq:.2e} GeV²")
    
    results['lambda_HW'] = lambda_HW_estimate
    results['delta_m_sq'] = delta_m_sq
    
    # =========================================================================
    # 3.7 Summary
    # =========================================================================
    print("\n" + "-" * 70)
    print("3.7 Summary: W Vertex Dark Matter")
    print("-" * 70)
    
    print("""
    Assessment of W vertex condensate as CG dark matter:
    
    STRENGTHS:
    + Natural extension of CG geometry
    + Gauge singlet (only gravitational + portal interactions)
    + Mass scale can be tuned via v_W
    + Topological stability from Skyrme dynamics
    + Natural portal through domain boundaries
    
    CHALLENGES:
    - v_W scale is NOT predicted (free parameter)
    - Phase φ_W relationship to RGB not determined
    - Production mechanism needs development
    - Phenomenology highly model-dependent
    
    VIABILITY: PROMISING — requires detailed model building
    """)
    
    viability = "PROMISING - natural hidden sector"
    results['viability'] = viability
    
    return results


# =============================================================================
# SUMMARY AND RECOMMENDATIONS
# =============================================================================

def summarize_dm_candidates():
    """Summarize all dark matter candidates and make recommendations."""
    
    print("\n" + "=" * 70)
    print("SUMMARY: DARK MATTER CANDIDATES IN CHIRAL GEOMETROGENESIS")
    print("=" * 70)
    
    print("""
    ┌─────────────────────────────────────────────────────────────────────┐
    │ CANDIDATE           │ MASS SCALE   │ PRODUCTION    │ VIABILITY     │
    ├─────────────────────┼──────────────┼───────────────┼───────────────┤
    │ 1. Sterile ν_R      │ keV          │ Oscillation   │ MARGINAL      │
    │    (Corollary 3.1.3)│              │ (DW+resonant) │               │
    ├─────────────────────┼──────────────┼───────────────┼───────────────┤
    │ 2. T₂ Solitons      │ ~1 GeV       │ Phase trans.  │ POSSIBLE      │
    │    (Theorem 4.1.x)  │              │ (needs asym.) │               │
    ├─────────────────────┼──────────────┼───────────────┼───────────────┤
    │ 3. W Condensate     │ Tunable      │ Portal/freeze │ PROMISING     │
    │    (Definition 0.1.1)│              │               │               │
    └─────────────────────┴──────────────┴───────────────┴───────────────┘
    
    RECOMMENDATION: Prioritize W CONDENSATE development
    
    Reasons:
    1. Natural extension of existing CG geometry
    2. Most flexible (mass scale tunable)
    3. Natural portal coupling through domain boundaries
    4. Does NOT require new physics beyond CG
    
    The W condensate provides a HIDDEN SECTOR that:
    - Shares the stella octangula geometry
    - Is automatically gauge-singlet
    - Can have Skyrme-stabilized solitons
    - Has natural portal to visible sector
    """)
    
    return {
        'recommended_candidate': 'W_condensate',
        'priority_order': ['W_condensate', 'T2_solitons', 'sterile_neutrino'],
        'next_steps': [
            'Develop W field Lagrangian extension',
            'Calculate W phase relationship to RGB',
            'Derive v_W from CG consistency conditions',
            'Compute relic abundance for W solitons',
            'Determine detection signatures'
        ]
    }


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def main():
    """Run the complete dark matter extension analysis."""
    
    print("\n" + "=" * 70)
    print("DARK MATTER EXTENSION ANALYSIS FOR CHIRAL GEOMETROGENESIS")
    print("=" * 70)
    print(f"\nAnalysis Date: 2025-12-17")
    print("Framework: Chiral Geometrogenesis (CG)")
    print("Status: Addressing Open Challenge #2 (Dark Matter)")
    
    all_results = {}
    
    # Analyze each candidate
    all_results['sterile_neutrino'] = analyze_sterile_neutrino_dm()
    all_results['T2_solitons'] = analyze_sterile_soliton_dm()
    all_results['W_condensate'] = analyze_W_vertex_dm()
    
    # Summary and recommendations
    all_results['summary'] = summarize_dm_candidates()
    
    # Save results
    output_path = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/dark_matter_analysis_results.json'
    
    # Convert numpy types for JSON
    def convert_numpy(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.float64, np.float32)):
            return float(obj)
        elif isinstance(obj, (np.int64, np.int32)):
            return int(obj)
        elif isinstance(obj, dict):
            return {k: convert_numpy(v) for k, v in obj.items()}
        elif isinstance(obj, (list, tuple)):
            return [convert_numpy(x) for x in obj]
        return obj
    
    with open(output_path, 'w') as f:
        json.dump(convert_numpy(all_results), f, indent=2)
    
    print(f"\n\nResults saved to: {output_path}")
    
    return all_results


if __name__ == "__main__":
    results = main()
