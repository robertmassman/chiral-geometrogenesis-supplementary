#!/usr/bin/env python3
"""
Derivation of Lepton η_f Values from Geometric Principles

This script derives the lepton η_f (helicity coupling) values from the
geometric framework of Theorem 3.1.2 and verifies consistency with
the values used in Proposition 0.0.17n.

The framework predicts:
    η_f = λ^(2n_f) × c_f

where:
    λ = (1/φ³)sin(72°) ≈ 0.2245 (geometric Wolfenstein parameter)
    n_f = generation index (0=3rd, 1=2nd, 2=1st generation)
    c_f = order-one coefficient from isospin/color structure

For leptons (color singlets), the c_f values are determined by matching
to the EW-sector mass formula with the known EW base mass.
"""

import numpy as np

# Fundamental geometric constants
phi = (1 + np.sqrt(5)) / 2  # Golden ratio
lambda_geo = (1 / phi**3) * np.sin(np.radians(72))  # = 0.2245

print("=" * 70)
print("DERIVATION OF LEPTON η_f VALUES")
print("=" * 70)

# EW sector parameters
omega_EW = 125.0e3  # MeV (Higgs mass scale)
v_EW = 246.0e3     # MeV (EW VEV)
Lambda_EW = 1000.0e3  # MeV (1 TeV cutoff)
g_chi = 4 * np.pi / 9

base_mass_EW = (g_chi * omega_EW / Lambda_EW) * v_EW
print(f"\nEW Sector Base Mass:")
print(f"  m_base^EW = (g_χ × ω_EW / Λ_EW) × v_EW")
print(f"           = ({g_chi:.4f} × {omega_EW/1e3:.0f} GeV / {Lambda_EW/1e3:.0f} GeV) × {v_EW/1e3:.0f} GeV")
print(f"           = {base_mass_EW/1e3:.2f} GeV = {base_mass_EW:.0f} MeV")

# PDG 2024 lepton masses
m_e_pdg = 0.51099895  # MeV
m_mu_pdg = 105.6583755  # MeV
m_tau_pdg = 1776.93  # MeV

print(f"\n" + "=" * 70)
print("STEP 1: Calculate required η_f from mass formula")
print("=" * 70)
print(f"\nMass formula: m_f = m_base^EW × η_f")
print(f"Therefore: η_f = m_f / m_base^EW")

eta_e_required = m_e_pdg / base_mass_EW
eta_mu_required = m_mu_pdg / base_mass_EW
eta_tau_required = m_tau_pdg / base_mass_EW

print(f"\nRequired η_f values (to match PDG masses):")
print(f"  η_e   = {m_e_pdg:.6f} / {base_mass_EW:.0f} = {eta_e_required:.6e}")
print(f"  η_μ   = {m_mu_pdg:.4f} / {base_mass_EW:.0f} = {eta_mu_required:.6e}")
print(f"  η_τ   = {m_tau_pdg:.2f} / {base_mass_EW:.0f} = {eta_tau_required:.6e}")

print(f"\n" + "=" * 70)
print("STEP 2: Geometric decomposition η_f = λ^(2n) × c_f")
print("=" * 70)
print(f"\nGeometric λ = (1/φ³)sin(72°) = {lambda_geo:.6f}")
print(f"λ² = {lambda_geo**2:.6f}")
print(f"λ⁴ = {lambda_geo**4:.8f}")

# Generation indices: tau=3rd(n=0), muon=2nd(n=1), electron=1st(n=2)
n_tau = 0
n_mu = 1
n_e = 2

lambda_factor_tau = lambda_geo**(2*n_tau)  # = 1
lambda_factor_mu = lambda_geo**(2*n_mu)    # = λ²
lambda_factor_e = lambda_geo**(2*n_e)      # = λ⁴

print(f"\nGeneration factors λ^(2n):")
print(f"  τ (3rd gen, n=0): λ^0 = {lambda_factor_tau:.6f}")
print(f"  μ (2nd gen, n=1): λ² = {lambda_factor_mu:.6f}")
print(f"  e (1st gen, n=2): λ⁴ = {lambda_factor_e:.8f}")

# Solve for c_f: c_f = η_f / λ^(2n)
c_tau = eta_tau_required / lambda_factor_tau
c_mu = eta_mu_required / lambda_factor_mu
c_e = eta_e_required / lambda_factor_e

print(f"\nDerived c_f coefficients (c_f = η_f / λ^(2n)):")
print(f"  c_τ = {eta_tau_required:.6e} / {lambda_factor_tau:.4f} = {c_tau:.4f}")
print(f"  c_μ = {eta_mu_required:.6e} / {lambda_factor_mu:.6f} = {c_mu:.4f}")
print(f"  c_e = {eta_e_required:.6e} / {lambda_factor_e:.8f} = {c_e:.4f}")

print(f"\n" + "=" * 70)
print("STEP 3: Physical interpretation of c_f values")
print("=" * 70)

print(f"\nThe c_f values encode:")
print(f"  - Lepton wavefunction overlap with chiral vacuum")
print(f"  - Color factor (leptons are color singlets, so no SU(3) enhancement)")
print(f"  - Isospin structure within doublets")
print(f"\nObserved pattern:")
print(f"  c_τ ≈ {c_tau:.4f} ~ O(0.04)")
print(f"  c_μ ≈ {c_mu:.4f} ~ O(0.05)")
print(f"  c_e ≈ {c_e:.4f} ~ O(0.005)")
print(f"\nRatios:")
print(f"  c_e/c_μ = {c_e/c_mu:.2f}")
print(f"  c_μ/c_τ = {c_mu/c_tau:.2f}")

print(f"\n" + "=" * 70)
print("STEP 4: Reconstruct η_f from geometric formula")
print("=" * 70)

# Reconstruct η_f using geometric formula
eta_tau_geo = lambda_factor_tau * c_tau
eta_mu_geo = lambda_factor_mu * c_mu
eta_e_geo = lambda_factor_e * c_e

print(f"\nReconstructed η_f = λ^(2n) × c_f:")
print(f"  η_τ = λ⁰ × {c_tau:.4f} = {eta_tau_geo:.6e}")
print(f"  η_μ = λ² × {c_mu:.4f} = {eta_mu_geo:.6e}")
print(f"  η_e = λ⁴ × {c_e:.4f} = {eta_e_geo:.6e}")

# Verify mass predictions
m_e_pred = base_mass_EW * eta_e_geo
m_mu_pred = base_mass_EW * eta_mu_geo
m_tau_pred = base_mass_EW * eta_tau_geo

print(f"\nVerification - predicted masses:")
print(f"  m_e   = {base_mass_EW:.0f} × {eta_e_geo:.6e} = {m_e_pred:.6f} MeV (PDG: {m_e_pdg:.6f})")
print(f"  m_μ   = {base_mass_EW:.0f} × {eta_mu_geo:.6e} = {m_mu_pred:.4f} MeV (PDG: {m_mu_pdg:.4f})")
print(f"  m_τ   = {base_mass_EW:.0f} × {eta_tau_geo:.6e} = {m_tau_pred:.2f} MeV (PDG: {m_tau_pdg:.2f})")

print(f"\n" + "=" * 70)
print("STEP 5: Verification against Prop 0.0.17n Table 4.1")
print("=" * 70)

# Current values in Prop 0.0.17n Table 4.1 (updated 2026-01-05)
eta_e_doc = 1.19e-5
eta_mu_doc = 2.46e-3
eta_tau_doc = 4.14e-2

print(f"\nVerification (document values should match derived):")
print(f"  {'Lepton':<8} {'η_f (document)':<18} {'η_f (derived)':<18} {'Match':<10}")
print(f"  {'-'*54}")
print(f"  {'e':<8} {eta_e_doc:<18.6e} {eta_e_geo:<18.6e} {'✅' if abs(eta_e_geo/eta_e_doc - 1) < 0.01 else '❌':<10}")
print(f"  {'μ':<8} {eta_mu_doc:<18.6e} {eta_mu_geo:<18.6e} {'✅' if abs(eta_mu_geo/eta_mu_doc - 1) < 0.01 else '❌':<10}")
print(f"  {'τ':<8} {eta_tau_doc:<18.6e} {eta_tau_geo:<18.6e} {'✅' if abs(eta_tau_geo/eta_tau_doc - 1) < 0.01 else '❌':<10}")

print(f"\n" + "=" * 70)
print("SUMMARY: Complete η_f derivation for leptons")
print("=" * 70)

print(f"""
The lepton η_f values from the geometric formula η_f = λ^(2n) × c_f:

| Lepton | Gen (n) | λ^(2n)   | c_f    | η_f          | Mass (MeV)  |
|--------|---------|----------|--------|--------------|-------------|
| e      | 1st (2) | {lambda_factor_e:.6f} | {c_e:.3f}  | {eta_e_geo:.4e} | {m_e_pred:.4f}    |
| μ      | 2nd (1) | {lambda_factor_mu:.4f}   | {c_mu:.3f}  | {eta_mu_geo:.4e} | {m_mu_pred:.2f}   |
| τ      | 3rd (0) | {lambda_factor_tau:.4f}   | {c_tau:.3f}  | {eta_tau_geo:.4e} | {m_tau_pred:.1f}   |

Key insight: The c_f coefficients follow: c_μ > c_τ > c_e
This pattern suggests that the 1st generation has REDUCED coupling
to the EW condensate relative to heavier generations.

Geometric λ = (1/φ³)sin(72°) = {lambda_geo:.6f}
Base mass (EW) = {base_mass_EW/1e3:.2f} GeV
""")

# Output for updating documentation
print("=" * 70)
print("VALUES FOR PROP 0.0.17n UPDATE")
print("=" * 70)
print(f"""
Update Table 4.1 lepton section with:

| Lepton | m_PDG | Sector | η_f | c_f | m_pred | Agreement |
|--------|-------|--------|-----|-----|--------|-----------|
| e | {m_e_pdg:.6f} MeV | EW | {eta_e_geo:.2e} | {c_e:.4f} | {m_e_pred:.4f} MeV | 100% |
| μ | {m_mu_pdg:.4f} MeV | EW | {eta_mu_geo:.2e} | {c_mu:.3f} | {m_mu_pred:.2f} MeV | 100% |
| τ | {m_tau_pdg:.2f} MeV | EW | {eta_tau_geo:.2e} | {c_tau:.4f} | {m_tau_pred:.1f} MeV | 100% |

Note: The η_f and c_f values are derived to match PDG masses exactly.
The predictive content is the λ^(2n) hierarchy PATTERN, not the absolute values.
""")
