#!/usr/bin/env python3
"""
Proposition 4.3.3: Symmetric W-Soliton Depletion in ADM
=========================================================

Quantitative Boltzmann analysis of whether the symmetric W-soliton
component is efficiently depleted via annihilation.

RESULT: With the Higgs-portal cross section <sigma v> ~ 6e-29 cm^3/s
(properly computed including all channels), the symmetric depletion
factor is delta_sym ~ 100-200. The ADM mechanism requires delta_sym << 1.
This constitutes a quantitative gap in Proposition 4.3.3 Section 4.2.

Related Documents:
- Proof: docs/proofs/Phase4/Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md
- Definition: docs/proofs/Phase4/Definition-4.3.1-W-Sector-Field-Theory.md
- Lean: lean/ChiralGeometrogenesis/Phase4/Theorem_4_3_2.lean

Verification Date: 2026-02-25
"""

import numpy as np
from scipy.integrate import solve_ivp
import json
from datetime import datetime

print("=" * 76)
print("PROPOSITION 4.3.3: SYMMETRIC DEPLETION QUANTITATIVE ANALYSIS")
print("Date: 2026-02-25")
print("=" * 76)

# =====================================================================
# PHYSICAL CONSTANTS
# =====================================================================
M_Pl       = 1.22e19       # Planck mass [GeV]
g_star      = 106.75        # relativistic d.o.f. at EW scale
g_star_S    = 106.75        # entropic d.o.f.
g_W         = 1             # W-soliton internal d.o.f.

# Standard Model
m_h         = 125.11        # Higgs mass [GeV]
m_t         = 173.0         # top quark mass [GeV]
m_W_ew      = 80.377        # W boson mass [GeV]
m_Z_ew      = 91.1876       # Z boson mass [GeV]
v_ew        = 246.22        # Higgs VEV [GeV]
Gamma_h     = 4.07e-3       # SM Higgs width [GeV]

# CG W-soliton parameters
M_W         = 1620.0        # W-soliton mass [GeV]
lambda_HPhi = 0.036         # Portal coupling
epsilon_W   = 3.1e-13       # W-sector asymmetry

# Unit conversion
hbar_c_cm   = 1.9733e-14    # GeV*cm
hbar_s      = 6.5822e-25    # GeV*s
cm3_s_to_GeV2 = (1.0 / hbar_c_cm)**3 / (1.0 / hbar_s)  # 1 cm^3/s in GeV^{-2}

# =====================================================================
# 1. CROSS SECTION CALCULATION
# =====================================================================
print("\n" + "=" * 76)
print("1. HIGGS-PORTAL ANNIHILATION CROSS SECTION")
print("=" * 76)

s = 4 * M_W**2
sqrt_s = 2 * M_W
prop_denom = (s - m_h**2)**2 + m_h**2 * Gamma_h**2

# Using Burgess-Pospelov-ter Veldhuis (NPB 619, 2001) formulas:

# --- WW channel ---
# sigma v = lambda^2 * 2 / (8 pi s) * (s^2/4 - s*mW^2 + 3*mW^4) * sqrt(1-4mW^2/s) / prop_denom
x_W = 4 * m_W_ew**2 / s
sv_WW = (lambda_HPhi**2 * 2 / (8*np.pi*s) * 
         (s**2/4 - s*m_W_ew**2 + 3*m_W_ew**4) * np.sqrt(1-x_W) / prop_denom)

# --- ZZ channel ---
x_Z = 4 * m_Z_ew**2 / s
sv_ZZ = (lambda_HPhi**2 * 1 / (8*np.pi*s) * 
         (s**2/4 - s*m_Z_ew**2 + 3*m_Z_ew**4) * np.sqrt(1-x_Z) / prop_denom)

# --- tt channel ---
x_t = 4 * m_t**2 / s
sv_tt = 3 * lambda_HPhi**2 * m_t**2 * (1-x_t)**1.5 / (16*np.pi*prop_denom)

# --- hh contact channel ---
x_h = 4 * m_h**2 / s
sv_hh = lambda_HPhi**2 / (32*np.pi*s) * np.sqrt(1-x_h)

# Total
sv_total = sv_WW + sv_ZZ + sv_tt + sv_hh
sv_total_cgs = sv_total / cm3_s_to_GeV2

print(f"\n  Parameters: M_W = {M_W} GeV, lambda_HPhi = {lambda_HPhi}")
print(f"  sqrt(s) = {sqrt_s} GeV, s = {s:.0f} GeV^2")
print(f"  (s - m_h^2)^2 = {(s-m_h**2)**2:.4e} GeV^4")

print(f"\n  Channel breakdown [GeV^{{-2}}] and [cm^3/s]:")
for name, sv in [("WW", sv_WW), ("ZZ", sv_ZZ), ("tt", sv_tt), ("hh(contact)", sv_hh)]:
    pct = sv/sv_total*100
    print(f"    {name:>12}: {sv:.4e} GeV^{{-2}} = {sv/cm3_s_to_GeV2:.4e} cm^3/s  ({pct:.1f}%)")
print(f"    {'TOTAL':>12}: {sv_total:.4e} GeV^{{-2}} = {sv_total_cgs:.4e} cm^3/s")
print(f"\n  Quoted in §3.1: ~1.3e-28 cm^3/s")
print(f"  Our calculation: {sv_total_cgs:.2e} cm^3/s (factor {sv_total_cgs/1.3e-28:.2f})")
print(f"  Note: The quoted value is ~2x larger, suggesting §3.1 used a slightly")
print(f"  different 'sum_f' factor. Both are O(10^{{-28}}) cm^3/s.")

# For the Boltzmann analysis, use the quoted value as the proposition states it
sv_for_boltzmann = 1.3e-28 * cm3_s_to_GeV2  # use quoted value
sv_for_boltzmann_full = sv_total  # use our calculation

# =====================================================================
# 2. BOLTZMANN EQUATION (NUMERICAL)
# =====================================================================
print("\n" + "=" * 76)
print("2. NUMERICAL BOLTZMANN INTEGRATION (ADM)")
print("=" * 76)

print("""
  The ADM Boltzmann equation for the anti-particle yield Y_bar = n_bar/s:
  
    dY_bar/dx = -(Lambda/x^2) [Y_bar(Y_bar + Delta) - Y_eq^2]
  
  where:
    x = M_W/T
    Delta = epsilon_W (conserved asymmetry)
    Lambda = sqrt(pi/45) sqrt(g_*) M_Pl M_W <sigma v>
    Y_eq(x) = (45 g_W)/(4 pi^4 g_*S) x^{3/2} exp(-x)
""")

def solve_adm_boltzmann(sv_nat, label="", verbose=True):
    """Solve ADM Boltzmann equation numerically."""
    Lambda = np.sqrt(np.pi / 45.0) * np.sqrt(g_star) * M_Pl * M_W * sv_nat
    Delta = epsilon_W
    
    def Y_eq(x):
        if x > 500: return 0.0
        return g_W * 45.0 / (4.0 * np.pi**4 * g_star_S) * x**1.5 * np.exp(-x)
    
    def rhs(x, y):
        Yb = max(y[0], 0.0)
        Yeq = Y_eq(x)
        return [-(Lambda / x**2) * (Yb * (Yb + Delta) - Yeq**2)]
    
    sol = solve_ivp(rhs, (1.0, 1000.0), [Y_eq(1.0)],
                    method='Radau', rtol=1e-12, atol=1e-40,
                    t_eval=np.linspace(1.0, 1000.0, 10000))
    
    Y_bar_f = max(sol.y[0][-1], 0.0)
    delta_sym = Y_bar_f / Delta
    
    sv_cgs = sv_nat / cm3_s_to_GeV2
    if verbose:
        print(f"\n  {label}:")
        print(f"    <sigma v> = {sv_cgs:.2e} cm^3/s ({sv_nat:.4e} GeV^{{-2}})")
        print(f"    Lambda = {Lambda:.4e}")
        print(f"    Y_bar_final = {Y_bar_f:.4e}")
        print(f"    epsilon_W   = {Delta:.4e}")
        print(f"    delta_sym = Y_bar/epsilon_W = {delta_sym:.2e}")
        if delta_sym < 0.01:
            print(f"    STATUS: PASS -- delta_sym << 1, ADM works")
        elif delta_sym < 1:
            print(f"    STATUS: MARGINAL -- delta_sym < 1")
        else:
            print(f"    STATUS: FAIL -- delta_sym = {delta_sym:.0f} >> 1, symmetric NOT depleted")
    
    return Y_bar_f, delta_sym

# Run with quoted cross section
Y1, d1 = solve_adm_boltzmann(sv_for_boltzmann, "Quoted <sigma v> = 1.3e-28 cm^3/s")

# Run with our calculated cross section
Y2, d2 = solve_adm_boltzmann(sv_for_boltzmann_full, f"Calculated <sigma v> = {sv_total_cgs:.1e} cm^3/s")

# =====================================================================
# 3. FREEZE-OUT TEMPERATURE
# =====================================================================
print("\n" + "=" * 76)
print("3. FREEZE-OUT TEMPERATURE")
print("=" * 76)

def find_xf(sv_nat):
    """Standard condition: n_eq <sigma v> = H(T)."""
    def ratio(x):
        T = M_W / x
        n_eq = g_W * (M_W * T / (2*np.pi))**1.5 * np.exp(-x)
        H = np.sqrt(np.pi**2 * g_star / 30.0) * T**2 / M_Pl
        return n_eq * sv_nat / H
    
    xl, xh = 5.0, 200.0
    for _ in range(200):
        xm = (xl + xh) / 2.0
        if ratio(xm) > 1:
            xl = xm
        else:
            xh = xm
    return (xl + xh) / 2.0

xf_quoted = find_xf(sv_for_boltzmann)
xf_calc = find_xf(sv_for_boltzmann_full)

print(f"\n  Freeze-out (standard Gamma=H condition):")
print(f"    Quoted <sigma v>:     x_f = {xf_quoted:.1f}, T_f = {M_W/xf_quoted:.1f} GeV")
print(f"    Calculated <sigma v>: x_f = {xf_calc:.1f}, T_f = {M_W/xf_calc:.1f} GeV")
print(f"\n  (Typical WIMP: x_f ~ 20-25; higher x_f = later freeze-out = LESS depletion)")

# =====================================================================
# 4. ANALYTIC CROSS-CHECK
# =====================================================================
print("\n" + "=" * 76)
print("4. ANALYTIC CROSS-CHECK (Lee-Weinberg / Kolb-Turner)")
print("=" * 76)

def analytic_Y_infty(sv_nat):
    """Standard analytic approximation for freeze-out yield."""
    Lambda = np.sqrt(np.pi / 45.0) * np.sqrt(g_star) * M_Pl * M_W * sv_nat
    # Iterative x_f: x_f = ln(c) - 0.5*ln(ln(c))
    c = 0.038 * g_W * M_Pl * M_W * sv_nat / np.sqrt(g_star)
    if c <= 1:
        return float('inf'), 0
    xf = np.log(c) - 0.5 * np.log(np.log(c))
    Y = (xf + 1) / Lambda
    return Y, xf

Y_an_q, xf_an_q = analytic_Y_infty(sv_for_boltzmann)
Y_an_c, xf_an_c = analytic_Y_infty(sv_for_boltzmann_full)

print(f"\n  Analytic (Kolb-Turner) Y_infty:")
print(f"    Quoted: Y = {Y_an_q:.4e} (x_f = {xf_an_q:.1f})")
print(f"    Calc'd: Y = {Y_an_c:.4e} (x_f = {xf_an_c:.1f})")
print(f"\n  Numerical Boltzmann Y_bar_final:")
print(f"    Quoted: Y = {Y1:.4e}")
print(f"    Calc'd: Y = {Y2:.4e}")
print(f"\n  Ratio (numerical/analytic): {Y1/Y_an_q:.2f} and {Y2/Y_an_c:.2f}")
print(f"  (O(1) agreement expected; analytic is approximate)")

# =====================================================================
# 5. GAMMA/H AT VARIOUS TEMPERATURES
# =====================================================================
print("\n" + "=" * 76)
print("5. ANNIHILATION RATE vs HUBBLE EXPANSION RATE")
print("=" * 76)

print(f"\n  Using calculated <sigma v> = {sv_total_cgs:.2e} cm^3/s:")
print(f"\n  {'x=M/T':>8} {'T [GeV]':>10} {'n_eq [GeV^3]':>14} {'Gamma [GeV]':>14} {'H [GeV]':>14} {'Gamma/H':>12} {'Status':>10}")
print("  " + "-" * 86)

for x in [5, 10, 15, 20, 25, 30, 35, 40, 50, 60]:
    T = M_W / x
    n_eq = g_W * (M_W * T / (2*np.pi))**1.5 * np.exp(-x) if x < 500 else 0
    Gamma = n_eq * sv_total
    H = np.sqrt(np.pi**2 * g_star / 30.0) * T**2 / M_Pl
    ratio = Gamma / H if H > 0 else 0
    status = "coupled" if ratio > 1 else "decoupled"
    print(f"  {x:8d} {T:10.1f} {n_eq:14.4e} {Gamma:14.4e} {H:14.4e} {ratio:12.4e} {status:>10}")

# =====================================================================
# 6. RESIDUAL SYMMETRIC ABUNDANCE
# =====================================================================
print("\n" + "=" * 76)
print("6. RESIDUAL SYMMETRIC ABUNDANCE")
print("=" * 76)

s_0 = 2891.2          # today's entropy density [cm^{-3}]
rho_c_h2 = 1.054e-5   # rho_crit/h^2 [GeV/cm^3]
conv = s_0 / rho_c_h2 # ~ 2.742e8

Omega_sym = M_W * Y1 * conv
Omega_asym = M_W * epsilon_W * conv

print(f"\n  With quoted <sigma v> = 1.3e-28 cm^3/s:")
print(f"    Y_bar (residual anti-W):  {Y1:.4e}")
print(f"    Y_W (asymmetric excess):  {epsilon_W:.4e}")
print(f"    delta_sym = Y_bar/Y_W:    {d1:.1f}")
print(f"\n    Omega_symmetric h^2  = {Omega_sym:.4f}")
print(f"    Omega_asymmetric h^2 = {Omega_asym:.4f}")
print(f"    Omega_total h^2      = {Omega_sym + Omega_asym:.4f}")
print(f"    Omega_DM h^2 (Planck) = 0.1200 +/- 0.0012")

print(f"\n  The symmetric component dominates by {d1:.0f}x.")
print(f"  The dark matter is only {Omega_asym/(Omega_sym+Omega_asym)*100:.1f}% asymmetric.")

# =====================================================================
# 7. WHAT CROSS SECTION IS NEEDED?
# =====================================================================
print("\n" + "=" * 76)
print("7. REQUIRED CROSS SECTION FOR EFFICIENT SYMMETRIC DEPLETION")
print("=" * 76)

print("\n  Scanning <sigma v> to find thresholds...")

targets = {10: None, 1: None, 0.1: None, 0.01: None}
sv_scan = np.logspace(-30, -24, 80)

for sv_cgs_i in sv_scan:
    sv_nat_i = sv_cgs_i * cm3_s_to_GeV2
    _, ds_i = solve_adm_boltzmann(sv_nat_i, verbose=False)
    for t in sorted(targets.keys(), reverse=True):
        if targets[t] is None and ds_i < t:
            targets[t] = sv_cgs_i

print(f"\n  {'Criterion':>20} {'<sigma v> needed':>18} {'Ratio to ours':>16} {'lambda needed':>16}")
print("  " + "-" * 74)
for t in sorted(targets.keys(), reverse=True):
    if targets[t]:
        ratio = targets[t] / sv_total_cgs
        # sigma v scales as lambda^2, so lambda scales as sqrt
        lam_needed = lambda_HPhi * np.sqrt(ratio)
        print(f"  delta_sym < {t:<9g} {targets[t]:18.2e} {ratio:16.0f}x {lam_needed:16.4f}")

# =====================================================================
# 8. DIRECT DETECTION CONSTRAINT ON lambda
# =====================================================================
print("\n" + "=" * 76)
print("8. DIRECT DETECTION CONSTRAINT")
print("=" * 76)

m_N = 0.938
f_N = 0.3
mu_N = m_N * M_W / (m_N + M_W)
sigma_SI = lambda_HPhi**2 * f_N**2 * m_N**2 * mu_N**2 / (np.pi * m_h**4 * M_W**2)
sigma_SI_cm2 = sigma_SI * hbar_c_cm**2

LZ_bound = 4.7e-47  # cm^2 at 1620 GeV

# Maximum lambda allowed by LZ
lambda_max_LZ = lambda_HPhi * np.sqrt(LZ_bound / sigma_SI_cm2)

print(f"\n  sigma_SI(lambda={lambda_HPhi}) = {sigma_SI_cm2:.2e} cm^2")
print(f"  LZ 90% CL bound at {M_W} GeV: {LZ_bound:.1e} cm^2")
print(f"  Ratio (prediction/bound): {sigma_SI_cm2/LZ_bound:.2f}")
print(f"  Status: {'ALLOWED' if sigma_SI_cm2 < LZ_bound else 'EXCLUDED'}")
print(f"\n  Maximum lambda_HPhi from LZ: {lambda_max_LZ:.4f}")

# What delta_sym would we get at lambda_max_LZ?
sv_at_max_lambda = sv_total * (lambda_max_LZ / lambda_HPhi)**2
sv_at_max_cgs = sv_at_max_lambda / cm3_s_to_GeV2
_, d_at_max = solve_adm_boltzmann(sv_at_max_lambda, verbose=False)
print(f"  <sigma v> at lambda_max: {sv_at_max_cgs:.2e} cm^3/s")
print(f"  delta_sym at lambda_max: {d_at_max:.1f}")

# =====================================================================
# 9. POSSIBLE RESOLUTIONS
# =====================================================================
print("\n" + "=" * 76)
print("9. POSSIBLE RESOLUTIONS")
print("=" * 76)

needed_01 = targets.get(0.1, targets.get(0.01))
if needed_01:
    enhancement = needed_01 / sv_total_cgs
else:
    enhancement = 500  # approximate

print(f"""
  PROBLEM: delta_sym ~ {d1:.0f} >> 1. The symmetric W-soliton component
  is NOT efficiently depleted. The ADM mechanism requires delta_sym << 1.

  Required enhancement: <sigma v> must increase by ~{enhancement:.0f}x to get
  delta_sym < 0.1, which means lambda_HPhi ~ {lambda_HPhi * np.sqrt(enhancement):.2f}.
  But LZ constrains lambda_HPhi < {lambda_max_LZ:.3f}, allowing at most
  {(lambda_max_LZ/lambda_HPhi)**2:.1f}x enhancement in <sigma v>.

  POSSIBLE RESOLUTIONS (in order of plausibility):

  (a) W-SECTOR SELF-ANNIHILATION
      W-solitons may annihilate via W-sector gauge interactions,
      not just the Higgs portal. The W-sector has its own SU(2)_W
      gauge coupling (Theorem 4.3.2) which could give additional
      annihilation channels W + W-bar -> W-sector gauge bosons.
      This is the most natural resolution since M_W ~ 1.6 TeV is
      the W-sector confinement scale.

  (b) SOMMERFELD ENHANCEMENT
      The Higgs-portal coupling creates an attractive Yukawa potential
      between W and anti-W at low velocities. At freeze-out (v ~ 0.2),
      the Sommerfeld factor S = pi*alpha_eff/v with alpha_eff = lambda^2*v_ew^2/(4pi*m_h^2)
      gives S ~ {np.pi * lambda_HPhi**2 * v_ew**2 / (4*np.pi * m_h**2) / 0.2:.2f}.
      This is insufficient (need S ~ {enhancement:.0f}).

  (c) BOUND STATE FORMATION
      W and anti-W could form bound states that enhance annihilation.
      For a Yukawa potential with range ~1/m_h and strength ~lambda^2/(4pi),
      bound states exist when lambda^2*v_ew*M_W/(4pi*m_h) > ~1.
      Value: {lambda_HPhi**2*v_ew*M_W/(4*np.pi*m_h):.3f}. {'Possible' if lambda_HPhi**2*v_ew*M_W/(4*np.pi*m_h) > 0.5 else 'Unlikely'}.

  (d) CANNIBALIZATION (3->2 PROCESSES)
      Number-changing processes within the W-sector (W+W+W -> W+W)
      could reduce the symmetric component. This requires strong
      self-interactions within the W-sector.

  (e) LATE ANNIHILATION DURING PHASE TRANSITION
      If annihilation is enhanced during the first-order EWPT
      (Theorem 4.2.3), the symmetric component could be depleted
      in bubble walls where the Higgs field is large.

  MOST PROMISING: Resolution (a) -- W-sector self-annihilation.
  The W-sector has its own gauge interactions at the TeV scale.
  Including these channels naturally enhances <sigma v> without
  affecting direct detection (which depends only on the Higgs portal).
""")

# =====================================================================
# SUMMARY
# =====================================================================
print("=" * 76)
print("FINAL SUMMARY")
print("=" * 76)

print(f"""
  ================================================================
  QUANTITATIVE SYMMETRIC DEPLETION ANALYSIS
  ================================================================
  
  INPUT PARAMETERS:
    M_W = {M_W} GeV, lambda_HPhi = {lambda_HPhi}
    epsilon_W = {epsilon_W:.1e}, eta_B = 6.1e-10
  
  CROSS SECTION (all Higgs-portal channels):
    <sigma v> = {sv_total_cgs:.2e} cm^3/s
    Channels: WW ({sv_WW/sv_total*100:.0f}%), ZZ ({sv_ZZ/sv_total*100:.0f}%), hh ({sv_hh/sv_total*100:.0f}%), tt ({sv_tt/sv_total*100:.0f}%)
    Consistent with quoted ~1.3e-28 cm^3/s to factor ~2
  
  FREEZE-OUT:
    x_f = {xf_calc:.1f} (T_f = {M_W/xf_calc:.1f} GeV)
  
  DEPLETION:
    Y_bar (residual symmetric) = {Y1:.2e}
    epsilon_W (asymmetric)      = {epsilon_W:.2e}
    delta_sym = Y_bar/epsilon_W = {d1:.0f}
  
  VERDICT: FAIL -- delta_sym >> 1
    The Higgs-portal cross section alone is INSUFFICIENT to deplete
    the symmetric W-soliton component. The residual anti-W density
    exceeds the asymmetric W density by ~{d1:.0f}x.
  
  IMPACT ON PROPOSITION 4.3.3:
    - The claim in §4.2 that <sigma v> ~ 10^{{-28}} is "sufficient to
      annihilate the symmetric component" is NOT supported
      quantitatively.
    - The five-factor geometric derivation (§5) and ADM abundance
      formula (§6) remain valid and valuable.
    - Resolution requires identifying additional annihilation channels
      (most naturally from W-sector self-interactions).
  
  REQUIRED FIX:
    Need <sigma v>_total > ~{targets.get(0.01, 1e-25):.0e} cm^3/s for delta_sym < 0.01.
    Enhancement factor: ~{targets.get(0.01, 1e-25)/sv_total_cgs:.0f}x beyond Higgs portal alone.
    Most promising: W-sector gauge self-annihilation channels.
  ================================================================
""")

# =====================================================================
# SAVE RESULTS
# =====================================================================
results = {
    "theorem": "4.3.3",
    "title": "W-Soliton Symmetric Depletion Analysis",
    "timestamp": datetime.now().isoformat(),
    "parameters": {
        "M_W_GeV": M_W,
        "lambda_HPhi": lambda_HPhi,
        "epsilon_W": epsilon_W,
    },
    "cross_section": {
        "total_GeV2": float(sv_total),
        "total_cm3_s": float(sv_total_cgs),
        "WW_fraction": float(sv_WW/sv_total),
        "ZZ_fraction": float(sv_ZZ/sv_total),
        "tt_fraction": float(sv_tt/sv_total),
        "hh_fraction": float(sv_hh/sv_total),
        "quoted_cm3_s": 1.3e-28,
    },
    "freeze_out": {
        "x_f": float(xf_calc),
        "T_f_GeV": float(M_W/xf_calc),
    },
    "boltzmann_result": {
        "Y_bar_residual": float(Y1),
        "epsilon_W": epsilon_W,
        "delta_sym": float(d1),
        "adm_works": d1 < 0.1,
    },
    "thresholds": {
        "delta_sym_0.01": targets.get(0.01),
        "delta_sym_0.1": targets.get(0.1),
        "delta_sym_1": targets.get(1),
    },
    "direct_detection": {
        "sigma_SI_cm2": float(sigma_SI_cm2),
        "LZ_bound_cm2": LZ_bound,
        "lambda_max_LZ": float(lambda_max_LZ),
    },
    "issues": [{
        "severity": "MAJOR",
        "location": "§4.2",
        "description": f"Symmetric depletion fails: delta_sym = {d1:.0f} >> 1. "
                      f"The Higgs portal cross section ({sv_total_cgs:.1e} cm^3/s) is "
                      f"~{targets.get(0.01, 1e-25)/sv_total_cgs:.0f}x too small for ADM.",
        "recommended_fix": "Include W-sector self-annihilation channels or other "
                          "non-portal annihilation mechanisms.",
    }],
    "overall_status": "ISSUE_FOUND",
}

output_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/Phase4/prop_4_3_3_symmetric_depletion_results.json"
with open(output_path, "w") as f:
    json.dump(results, f, indent=2, default=str)
print(f"Results saved to: {output_path}")

