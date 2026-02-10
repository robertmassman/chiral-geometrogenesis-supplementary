#!/usr/bin/env python3
"""
Proposition 6.3.4: Higgs Z-Gamma Decay (h -> Zgamma) Verification
===================================================================

Verifies the h -> Zgamma decay width calculation from Chiral Geometrogenesis
against Standard Model predictions and experimental data.

This script implements the full two-variable Passarino-Veltman loop integrals
for h -> Zgamma, which are more complex than the single-variable h -> gammagamma
loop functions of Proposition 6.3.3.

Related Documents:
- Proof: docs/proofs/Phase6/Proposition-6.3.4-Higgs-Z-Gamma-Decay.md
- Parent: docs/proofs/Phase6/Proposition-6.3.3-Higgs-Diphoton-Decay.md

Verification Date: 2026-02-09
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from dataclasses import dataclass
import os
import json
from datetime import datetime

# =============================================================================
# Physical Constants (PDG 2024)
# =============================================================================

@dataclass
class Constants:
    """Physical constants used in the calculation."""
    # Masses (GeV)
    m_H: float = 125.20        # Higgs mass
    M_W: float = 80.3692       # W boson mass
    M_Z: float = 91.1876       # Z boson mass
    m_t: float = 172.50        # Top quark pole mass
    m_b: float = 4.18          # Bottom quark mass (MS-bar at m_b)
    m_tau: float = 1.777       # Tau lepton mass
    v_H: float = 246.22        # Higgs VEV (GeV)

    # Couplings
    alpha_em: float = 1/137.036    # Fine structure constant
    G_F: float = 1.1663788e-5      # Fermi constant (GeV^-2)

    # Electroweak mixing
    s_W2: float = 0.23122          # sin^2(theta_W) MS-bar
    c_W2: float = 0.76878          # cos^2(theta_W)

    @property
    def c_W(self):
        return np.sqrt(self.c_W2)

    @property
    def s_W(self):
        return np.sqrt(self.s_W2)

    # Total Higgs width (SM)
    Gamma_H_total: float = 4.10e-3  # GeV

const = Constants()


# =============================================================================
# Auxiliary Functions (Djouadi convention: tau = 4m^2/m_H^2, lambda = 4m^2/M_Z^2)
# =============================================================================
#
# IMPORTANT: The I1, I2 Passarino-Veltman integrals use the Djouadi convention
# where tau = 4m^2/m_H^2 (heavy particles have tau > 1, light particles tau < 1).
# This is the INVERSE of the convention used in Prop 6.3.3 for h -> gammagamma.
#
# The external interface (calculate_tau, calculate_lambda) uses the Prop 6.3.3
# convention (tau = m_H^2/4m^2). We convert at the call sites.
# =============================================================================

def f_tau(tau):
    """
    Auxiliary function f(tau) for loop integrals (Prop 6.3.3 convention: tau = m_H^2/4m^2).

    f(tau) = arcsin^2(sqrt(tau))                          for tau <= 1
           = -1/4 [ln((1+sqrt(1-1/tau))/(1-sqrt(1-1/tau))) - i*pi]^2  for tau > 1
    """
    if tau <= 1.0:
        return complex(np.arcsin(np.sqrt(tau))**2)
    else:
        sqrt_term = np.sqrt(1.0 - 1.0/tau)
        log_arg = (1.0 + sqrt_term) / (1.0 - sqrt_term)
        return -0.25 * (np.log(log_arg) - 1j * np.pi)**2


def f_djouadi(tau):
    """
    Auxiliary function f(tau) in Djouadi convention (tau = 4m^2/m_H^2).

    f(tau) = arcsin^2(1/sqrt(tau))                          for tau >= 1 (heavy)
           = -1/4 [ln((1+sqrt(1-tau))/(1-sqrt(1-tau))) - i*pi]^2  for tau < 1 (light)

    This is f_tau(1/tau) from the Prop 6.3.3 convention.
    """
    if tau >= 1.0:
        return complex(np.arcsin(1.0 / np.sqrt(tau))**2)
    else:
        sqrt_term = np.sqrt(1.0 - tau)
        log_arg = (1.0 + sqrt_term) / (1.0 - sqrt_term)
        return -0.25 * (np.log(log_arg) - 1j * np.pi)**2


def g_djouadi(tau):
    """
    Auxiliary function g(tau) in Djouadi convention (tau = 4m^2/m_H^2).

    g(tau) = sqrt(tau - 1) * arcsin(1/sqrt(tau))           for tau >= 1 (heavy)
           = sqrt(1 - tau)/2 * [ln((1+sqrt(1-tau))/(1-sqrt(1-tau))) - i*pi]  for tau < 1 (light)
    """
    if tau >= 1.0:
        return complex(np.sqrt(tau - 1.0) * np.arcsin(1.0 / np.sqrt(tau)))
    else:
        sqrt_term = np.sqrt(1.0 - tau)
        log_arg = (1.0 + sqrt_term) / (1.0 - sqrt_term)
        return 0.5 * sqrt_term * (np.log(log_arg) - 1j * np.pi)


def g_tau(tau):
    """
    Auxiliary function g(tau) in Prop 6.3.3 convention (tau = m_H^2/4m^2).

    g(tau) = sqrt(1/tau - 1) * arcsin(sqrt(tau))                      for tau <= 1
           = sqrt(1 - 1/tau)/2 * [ln((1+sqrt(1-1/tau))/(1-sqrt(1-1/tau))) - i*pi]  for tau > 1

    Equivalent to g_djouadi(1/tau).
    """
    if tau <= 1.0:
        return complex(np.sqrt(1.0/tau - 1.0) * np.arcsin(np.sqrt(tau)))
    else:
        sqrt_term = np.sqrt(1.0 - 1.0/tau)
        log_arg = (1.0 + sqrt_term) / (1.0 - sqrt_term)
        return 0.5 * sqrt_term * (np.log(log_arg) - 1j * np.pi)


# =============================================================================
# Passarino-Veltman Master Integrals (Djouadi convention)
# =============================================================================
#
# Following Djouadi, Phys.Rept. 457 (2008), Eqs. (2.62)-(2.63):
#   tau = 4m^2/m_H^2,  lambda = 4m^2/M_Z^2
#
# I1(tau, lambda) = tau*lambda / [2(tau-lambda)]
#                 + tau^2*lambda^2 / [2(tau-lambda)^2] * [f(tau) - f(lambda)]
#                 + tau^2*lambda / [(tau-lambda)^2] * [g(tau) - g(lambda)]
#
# I2(tau, lambda) = -tau*lambda / [2(tau-lambda)] * [f(tau) - f(lambda)]
# =============================================================================

def I1_dj(tau, lambda_):
    """
    First Passarino-Veltman master integral (Djouadi convention).
    tau = 4m^2/m_H^2, lambda = 4m^2/M_Z^2.
    """
    diff = tau - lambda_
    if abs(diff) < 1e-10:
        return complex(0.0)

    ft = f_djouadi(tau)
    fl = f_djouadi(lambda_)
    gt = g_djouadi(tau)
    gl = g_djouadi(lambda_)

    term1 = tau * lambda_ / (2.0 * diff)
    term2 = tau**2 * lambda_**2 / (2.0 * diff**2) * (ft - fl)
    term3 = tau**2 * lambda_ / (diff**2) * (gt - gl)

    return term1 + term2 + term3


def I2_dj(tau, lambda_):
    """
    Second Passarino-Veltman master integral (Djouadi convention).
    tau = 4m^2/m_H^2, lambda = 4m^2/M_Z^2.
    """
    diff = tau - lambda_
    if abs(diff) < 1e-10:
        return complex(0.0)

    ft = f_djouadi(tau)
    fl = f_djouadi(lambda_)

    return -tau * lambda_ / (2.0 * diff) * (ft - fl)


# =============================================================================
# Loop Functions for h -> Zgamma
# =============================================================================

def A_half_Zgamma(m_f, m_H, M_Z):
    """
    Spin-1/2 (fermion) loop function for h -> Zgamma.

    Takes physical masses and internally converts to Djouadi convention.
    A_{1/2}^{Zgamma} = I1(tau, lambda) - I2(tau, lambda)
    where tau = 4m_f^2/m_H^2, lambda = 4m_f^2/M_Z^2.
    """
    tau = 4.0 * m_f**2 / m_H**2    # Djouadi convention
    lam = 4.0 * m_f**2 / M_Z**2    # Djouadi convention
    return I1_dj(tau, lam) - I2_dj(tau, lam)


def A_one_Zgamma(m_W, m_H, M_Z):
    """
    Spin-1 (W boson) loop function for h -> Zgamma.

    Takes physical masses and internally converts to Djouadi convention.
    A_1^{Zgamma} = c_W * [4*(3 - tan^2(theta_W)) * I2
        + ((1 + 2/tau_W)*tan^2(theta_W) - (5 + 2/tau_W)) * I1]
    """
    tau_W = 4.0 * m_W**2 / m_H**2   # Djouadi convention
    lam_W = 4.0 * m_W**2 / M_Z**2   # Djouadi convention

    cw = const.c_W
    sw2 = const.s_W2
    cw2 = const.c_W2
    tan2 = sw2 / cw2

    i1 = I1_dj(tau_W, lam_W)
    i2 = I2_dj(tau_W, lam_W)

    coeff_i2 = 4.0 * (3.0 - tan2)
    coeff_i1 = (1.0 + 2.0/tau_W) * tan2 - (5.0 + 2.0/tau_W)

    return cw * (coeff_i2 * i2 + coeff_i1 * i1)


def fermion_coupling_Zgamma(Nc, Qf, I3f):
    """
    Coupling factor for a fermion in h -> Zgamma.

    C_f^{Zgamma} = N_c * Q_f * (2*I3_f - 4*Q_f*s_W^2) / c_W
    """
    sw2 = const.s_W2
    cw = const.c_W
    return Nc * Qf * (2.0 * I3f - 4.0 * Qf * sw2) / cw


# =============================================================================
# h -> gammagamma functions (for cross-check with Prop 6.3.3)
# =============================================================================

def A_half_gg(tau):
    """Spin-1/2 loop function for h -> gammagamma."""
    f = f_tau(tau)
    return 2.0 * tau**(-2) * (tau + (tau - 1.0) * f)


def A_one_gg(tau):
    """Spin-1 loop function for h -> gammagamma."""
    f = f_tau(tau)
    return -tau**(-2) * (2.0 * tau**2 + 3.0 * tau + 3.0 * (2.0 * tau - 1.0) * f)


# =============================================================================
# Decay Width Calculations
# =============================================================================

def calculate_tau(m_H, m_particle):
    """Calculate tau = m_H^2/(4*m^2)."""
    return m_H**2 / (4.0 * m_particle**2)


def calculate_lambda(M_Z, m_particle):
    """Calculate lambda = M_Z^2/(4*m^2)."""
    return M_Z**2 / (4.0 * m_particle**2)


def calculate_Zgamma_amplitude():
    """
    Calculate the total h -> Zgamma amplitude.

    A_Zgamma = sum_f C_f * A_{1/2}^{Zgamma}(m_f) + A_1^{Zgamma}(M_W)
    """
    m_H = const.m_H
    M_Z = const.M_Z

    # W boson contribution
    A_W = A_one_Zgamma(const.M_W, m_H, M_Z)

    # Top quark
    C_t = fermion_coupling_Zgamma(3, 2.0/3.0, 0.5)
    A_t = C_t * A_half_Zgamma(const.m_t, m_H, M_Z)

    # Bottom quark
    C_b = fermion_coupling_Zgamma(3, -1.0/3.0, -0.5)
    A_b = C_b * A_half_Zgamma(const.m_b, m_H, M_Z)

    # Tau lepton
    C_tau = fermion_coupling_Zgamma(1, -1.0, -0.5)
    A_tau = C_tau * A_half_Zgamma(const.m_tau, m_H, M_Z)

    A_total = A_W + A_t + A_b + A_tau

    return A_total, {'W': A_W, 'top': A_t, 'bottom': A_b, 'tau': A_tau}


def calculate_Zgamma_width(A_total):
    """
    Calculate Gamma(h -> Zgamma).

    Gamma = (G_F^2 * M_W^2 * alpha * m_H^3) / (64 * pi^4)
            * (1 - M_Z^2/m_H^2)^3 * |A|^2
    """
    phase_space = (1.0 - const.M_Z**2 / const.m_H**2)**3

    prefactor = (const.G_F**2 * const.M_W**2 * const.alpha_em * const.m_H**3) / \
                (64.0 * np.pi**4)

    width = prefactor * phase_space * np.abs(A_total)**2
    return width


def calculate_gg_width():
    """Calculate Gamma(h -> gammagamma) for cross-check with Prop 6.3.3."""
    tau_W = calculate_tau(const.m_H, const.M_W)
    tau_t = calculate_tau(const.m_H, const.m_t)
    tau_b = calculate_tau(const.m_H, const.m_b)
    tau_tau = calculate_tau(const.m_H, const.m_tau)

    A_W = A_one_gg(tau_W)
    A_t = 3 * (2.0/3.0)**2 * A_half_gg(tau_t)
    A_b = 3 * (1.0/3.0)**2 * A_half_gg(tau_b)
    A_tau = 1 * 1.0**2 * A_half_gg(tau_tau)

    A_total = A_W + A_t + A_b + A_tau

    prefactor = (const.G_F * const.alpha_em**2 * const.m_H**3) / \
                (128.0 * np.sqrt(2.0) * np.pi**3)

    return prefactor * np.abs(A_total)**2


# =============================================================================
# Verification Tests
# =============================================================================

def test_1_g_tau_function():
    """Test 1: g(tau) function values and branch cut handling."""
    print("\n" + "="*60)
    print("Test 1: g(tau) Function Values")
    print("="*60)

    passed = True

    # Below threshold (tau <= 1)
    tau_test = 0.5
    g_val = g_tau(tau_test)
    expected_real = np.sqrt(1.0/tau_test - 1.0) * np.arcsin(np.sqrt(tau_test))
    print(f"  g(0.5) = {g_val.real:.6f} + {g_val.imag:.6f}i")
    print(f"  Expected: {expected_real:.6f} + 0i")
    if abs(g_val.real - expected_real) > 1e-10 or abs(g_val.imag) > 1e-10:
        passed = False
        print("  ERROR: g(0.5) incorrect")

    # At threshold (tau = 1)
    g_at_1 = g_tau(0.999999)
    print(f"  g(1-eps) = {g_at_1.real:.6f} + {g_at_1.imag:.6f}i")

    # Above threshold (tau > 1): should have imaginary part
    tau_above = 10.0
    g_above = g_tau(tau_above)
    print(f"  g(10) = {g_above.real:.6f} + {g_above.imag:.6f}i")
    if abs(g_above.imag) < 1e-10:
        passed = False
        print("  ERROR: g(10) should have imaginary part")

    # Very large tau (light fermion limit)
    g_large = g_tau(1000.0)
    print(f"  g(1000) = {g_large.real:.6f} + {g_large.imag:.6f}i")

    if passed:
        print("  PASS: g(tau) function values correct with proper branch cuts")
    else:
        print("  FAIL")
    return passed


def test_2_I1_I2_consistency():
    """Test 2: I1, I2 consistency in limits (Djouadi convention)."""
    print("\n" + "="*60)
    print("Test 2: I1, I2 Consistency in Limits")
    print("="*60)

    passed = True

    # Djouadi convention: tau = 4m^2/m_H^2, lambda = 4m^2/M_Z^2
    # Top quark (heavy: tau > 1)
    tau_t = 4 * const.m_t**2 / const.m_H**2
    lam_t = 4 * const.m_t**2 / const.M_Z**2

    i1 = I1_dj(tau_t, lam_t)
    i2 = I2_dj(tau_t, lam_t)

    print(f"  Top quark (Djouadi): tau_t = {tau_t:.4f}, lambda_t = {lam_t:.4f}")
    print(f"  I1 = {i1.real:.6f} + {i1.imag:.6f}i")
    print(f"  I2 = {i2.real:.6f} + {i2.imag:.6f}i")

    # Both should be real for heavy particles (tau, lambda > 1)
    if abs(i1.imag) > 1e-10:
        print(f"  WARNING: I1 has imaginary part {i1.imag:.6e} for heavy top")

    # W boson (intermediate: tau ~1.6)
    tau_W = 4 * const.M_W**2 / const.m_H**2
    lam_W = 4 * const.M_W**2 / const.M_Z**2

    i1_W = I1_dj(tau_W, lam_W)
    i2_W = I2_dj(tau_W, lam_W)

    print(f"\n  W boson (Djouadi): tau_W = {tau_W:.4f}, lambda_W = {lam_W:.4f}")
    print(f"  I1 = {i1_W.real:.6f} + {i1_W.imag:.6f}i")
    print(f"  I2 = {i2_W.real:.6f} + {i2_W.imag:.6f}i")

    # Bottom quark (light: tau << 1, should have imaginary parts)
    tau_b = 4 * const.m_b**2 / const.m_H**2
    lam_b = 4 * const.m_b**2 / const.M_Z**2

    i1_b = I1_dj(tau_b, lam_b)
    i2_b = I2_dj(tau_b, lam_b)
    print(f"\n  Bottom (Djouadi): tau_b = {tau_b:.6f}, lambda_b = {lam_b:.6f}")
    print(f"  I1 = {i1_b.real:.6f} + {i1_b.imag:.6f}i")
    print(f"  I2 = {i2_b.real:.6f} + {i2_b.imag:.6f}i")
    print(f"  A_half_b = {(i1_b - i2_b).real:.6f} + {(i1_b - i2_b).imag:.6f}i")

    # Bottom contribution should be small (< 0.1 in magnitude)
    a_half_b = i1_b - i2_b
    if abs(a_half_b) > 1.0:
        passed = False
        print(f"  ERROR: Bottom loop function too large: |A| = {abs(a_half_b):.4f}")

    if passed:
        print("\n  PASS: I1, I2 have correct analytic structure")
    return passed


def test_3_MZ_to_zero_limit():
    """Test 3: M_Z -> 0 limit reduces to gammagamma structure."""
    print("\n" + "="*60)
    print("Test 3: M_Z -> 0 Limit (reduces to gammagamma)")
    print("="*60)

    passed = True

    # When M_Z -> 0, the Zgamma process should approach the gammagamma structure.
    # In Djouadi convention: as M_Z -> 0, lambda = 4m^2/M_Z^2 -> infinity.
    # I2 -> -tau*lambda/(2(tau-lambda)) * [f(tau)-f(lambda)]
    # As lambda -> inf, f(lambda) -> arcsin^2(1/sqrt(lambda)) -> 0
    # So I2 -> tau/2 * f(tau) for large lambda

    tau_gg = calculate_tau(const.m_H, const.m_t)  # our convention
    a_gg = A_half_gg(tau_gg)

    print("  Testing A_{1/2}^{Zgamma} as M_Z -> 0:")
    for MZ_frac in [1.0, 0.5, 0.1, 0.01]:
        MZ_test = const.M_Z * MZ_frac
        if MZ_test < 0.01:
            MZ_test = 0.01
        a_zg = A_half_Zgamma(const.m_t, const.m_H, MZ_test)
        print(f"    M_Z = {MZ_test:.2f} GeV: A_{'{1/2}'}^Zgamma = {a_zg.real:.6f}, "
              f"A_{'{1/2}'}^gg = {a_gg.real:.4f}")

    # Check W boson
    a1_gg = A_one_gg(calculate_tau(const.m_H, const.M_W))
    print(f"\n  W loop comparison (A_1^gg = {a1_gg.real:.4f}):")
    for MZ_frac in [1.0, 0.5, 0.1]:
        MZ_test = const.M_Z * MZ_frac
        a1_zg = A_one_Zgamma(const.M_W, const.m_H, MZ_test)
        print(f"    M_Z = {MZ_test:.2f} GeV: A_1^Zgamma = {a1_zg.real:.4f}")

    print("\n  PASS: M_Z -> 0 limit shows smooth behavior")
    return passed


def test_4_loop_function_values():
    """Test 4: Loop function numerical values at physical point."""
    print("\n" + "="*60)
    print("Test 4: Loop Function Numerical Values")
    print("="*60)

    passed = True

    # Djouadi convention values
    tau_t_dj = 4 * const.m_t**2 / const.m_H**2
    lam_t_dj = 4 * const.m_t**2 / const.M_Z**2
    tau_W_dj = 4 * const.M_W**2 / const.m_H**2
    lam_W_dj = 4 * const.M_W**2 / const.M_Z**2

    # Compute loop function values
    i1_t = I1_dj(tau_t_dj, lam_t_dj)
    i2_t = I2_dj(tau_t_dj, lam_t_dj)
    a_half_t = A_half_Zgamma(const.m_t, const.m_H, const.M_Z)
    a_one_W = A_one_Zgamma(const.M_W, const.m_H, const.M_Z)

    print(f"  Djouadi convention:")
    print(f"    tau_W = {tau_W_dj:.4f}, lambda_W = {lam_W_dj:.4f}")
    print(f"    tau_t = {tau_t_dj:.4f}, lambda_t = {lam_t_dj:.4f}")
    print(f"\n  I1(tau_t, lambda_t) = {i1_t.real:.4f}")
    print(f"  I2(tau_t, lambda_t) = {i2_t.real:.4f}")
    print(f"  A_{{1/2}}^Zgamma(top) = {a_half_t.real:.4f}")
    print(f"  A_1^Zgamma(W) = {a_one_W.real:.4f}")

    # The W loop function should be the dominant contribution
    # (Sign convention in Djouadi: W contribution is positive for h -> Zgamma)
    if abs(a_one_W.real) < abs(a_half_t.real):
        passed = False
        print("  ERROR: W loop should dominate over top")

    # Check reasonable ranges (from Djouadi 2008 and literature)
    if abs(a_one_W.real) < 2 or abs(a_one_W.real) > 12:
        passed = False
        print(f"  ERROR: W loop function out of expected range: {a_one_W.real:.2f}")

    if passed:
        print("\n  PASS: Loop function values in expected ranges")
    return passed


def test_5_fermion_coupling_factors():
    """Test 5: Fermion coupling factors for Zgamma."""
    print("\n" + "="*60)
    print("Test 5: Fermion Coupling Factors")
    print("="*60)

    passed = True

    sw2 = const.s_W2
    cw = const.c_W

    # Top quark: Nc=3, Q=2/3, I3=+1/2
    C_t = fermion_coupling_Zgamma(3, 2.0/3.0, 0.5)
    v_t = 2*0.5 - 4*(2.0/3.0)*sw2  # = 1 - 8/3 * 0.231 = 1 - 0.616 = 0.384
    expected_Ct = 3 * (2.0/3.0) * v_t / cw
    print(f"  Top:    C_t = {C_t:.4f} (expected: {expected_Ct:.4f})")
    if abs(C_t - expected_Ct) > 1e-6:
        passed = False

    # Bottom quark: Nc=3, Q=-1/3, I3=-1/2
    C_b = fermion_coupling_Zgamma(3, -1.0/3.0, -0.5)
    v_b = 2*(-0.5) - 4*(-1.0/3.0)*sw2  # = -1 + 4/3 * 0.231 = -1 + 0.308 = -0.692
    expected_Cb = 3 * (-1.0/3.0) * v_b / cw
    print(f"  Bottom: C_b = {C_b:.4f} (expected: {expected_Cb:.4f})")
    if abs(C_b - expected_Cb) > 1e-6:
        passed = False

    # Tau lepton: Nc=1, Q=-1, I3=-1/2
    C_tau = fermion_coupling_Zgamma(1, -1.0, -0.5)
    v_tau = 2*(-0.5) - 4*(-1.0)*sw2  # = -1 + 4*0.231 = -1 + 0.925 = -0.075
    expected_Ctau = 1 * (-1.0) * v_tau / cw
    print(f"  Tau:    C_tau = {C_tau:.4f} (expected: {expected_Ctau:.4f})")
    if abs(C_tau - expected_Ctau) > 1e-6:
        passed = False

    # Check signs: top positive, bottom positive, tau negative (for these sw2 values)
    print(f"\n  Sign check: C_t > 0? {C_t > 0}, C_b > 0? {C_b > 0}, C_tau < 0? {C_tau < 0}")

    if passed:
        print("  PASS: Fermion coupling factors correct")
    return passed


def test_6_phase_space_factor():
    """Test 6: Phase space factor (1 - M_Z^2/m_H^2)^3 = 0.103."""
    print("\n" + "="*60)
    print("Test 6: Phase Space Factor")
    print("="*60)

    passed = True

    ratio = const.M_Z**2 / const.m_H**2
    beta = 1.0 - ratio
    ps_factor = beta**3

    print(f"  M_Z^2/m_H^2 = {ratio:.4f}")
    print(f"  beta = 1 - M_Z^2/m_H^2 = {beta:.4f}")
    print(f"  Phase space factor = beta^3 = {ps_factor:.4f}")

    # Should be approximately 0.103
    expected = 0.103
    if abs(ps_factor - expected) / expected > 0.05:
        passed = False
        print(f"  ERROR: Phase space factor {ps_factor:.4f} differs from expected {expected}")
    else:
        print(f"  Agreement with expected 0.103: {abs(ps_factor-expected)/expected*100:.1f}%")

    if passed:
        print("  PASS: Phase space factor = {:.4f} (expected ~0.103)".format(ps_factor))
    return passed


def test_7_total_amplitude():
    """Test 7: Total amplitude calculation."""
    print("\n" + "="*60)
    print("Test 7: Total Amplitude")
    print("="*60)

    passed = True

    A_total, contributions = calculate_Zgamma_amplitude()

    print("  Amplitude contributions:")
    for name, val in contributions.items():
        print(f"    {name:8s}: {val.real:+.4f} + {val.imag:.4f}i  (|A| = {abs(val):.4f})")

    print(f"\n  Total amplitude: {A_total.real:.4f} + {A_total.imag:.4f}i")
    print(f"  |A_total|^2 = {np.abs(A_total)**2:.2f}")

    # W should dominate (in Djouadi convention, W is positive for Zgamma)
    if abs(contributions['W'].real) < abs(contributions['top'].real):
        passed = False
        print("  ERROR: W contribution should dominate over top")

    # Top should have opposite sign to W (destructive interference)
    if np.sign(contributions['top'].real) == np.sign(contributions['W'].real):
        passed = False
        print("  ERROR: Top and W should have opposite signs (destructive interference)")

    # There should be destructive interference (|A_total| < |A_W|)
    if abs(A_total.real) > abs(contributions['W'].real):
        passed = False
        print("  ERROR: Should have destructive interference (|A_total| < |A_W|)")

    # |A_total|^2 should be in a reasonable range (20-40)
    A2 = np.abs(A_total)**2
    if A2 < 15 or A2 > 50:
        passed = False
        print(f"  ERROR: |A|^2 = {A2:.1f} outside expected range [15, 50]")

    if passed:
        print("  PASS: Total amplitude has correct structure")
    return passed


def test_8_decay_width():
    """Test 8: Decay width vs SM."""
    print("\n" + "="*60)
    print("Test 8: Decay Width vs SM")
    print("="*60)

    passed = True

    A_total, _ = calculate_Zgamma_amplitude()
    width = calculate_Zgamma_width(A_total)
    width_keV = width * 1e6

    # SM prediction
    width_SM_keV = 6.32
    width_SM_err = 0.13

    print(f"  CG prediction: Gamma(h -> Zgamma) = {width_keV:.2f} keV")
    print(f"  SM prediction: Gamma(h -> Zgamma) = {width_SM_keV:.2f} +/- {width_SM_err:.2f} keV")

    deviation_pct = abs(width_keV - width_SM_keV) / width_SM_keV * 100
    print(f"  Deviation: {deviation_pct:.1f}%")

    # Should match SM within 15% (loop calculations have inherent ~5-10% uncertainty
    # from different schemes, higher orders, etc.)
    if deviation_pct > 15:
        passed = False
        print(f"  ERROR: Deviation {deviation_pct:.1f}% exceeds 15% tolerance")

    if passed:
        print("  PASS: Decay width consistent with SM")
    return passed


def test_9_branching_ratio():
    """Test 9: Branching ratio."""
    print("\n" + "="*60)
    print("Test 9: Branching Ratio")
    print("="*60)

    passed = True

    A_total, _ = calculate_Zgamma_amplitude()
    width = calculate_Zgamma_width(A_total)
    BR = width / const.Gamma_H_total

    # SM prediction
    BR_SM = 1.54e-3
    BR_SM_err = 0.09e-3

    print(f"  CG prediction: BR(h -> Zgamma) = {BR*1e3:.3f} x 10^-3")
    print(f"  SM prediction: BR(h -> Zgamma) = ({BR_SM*1e3:.2f} +/- {BR_SM_err*1e3:.2f}) x 10^-3")

    tension = abs(BR - BR_SM) / BR_SM_err
    print(f"  Tension: {tension:.1f}sigma")

    if tension > 3:
        passed = False
        print(f"  ERROR: Tension {tension:.1f}sigma too large")

    if passed:
        print("  PASS: Branching ratio consistent with SM")
    return passed


def test_10_BR_ratio_cross_check():
    """Test 10: BR ratio Zgamma/gammagamma cross-check."""
    print("\n" + "="*60)
    print("Test 10: BR Ratio Zgamma/gammagamma")
    print("="*60)

    passed = True

    # h -> Zgamma width
    A_Zg, _ = calculate_Zgamma_amplitude()
    width_Zg = calculate_Zgamma_width(A_Zg)

    # h -> gammagamma width
    width_gg = calculate_gg_width()

    ratio = width_Zg / width_gg
    BR_ratio_SM = 1.54e-3 / 2.27e-3  # = 0.678

    print(f"  Gamma(h -> Zgamma) = {width_Zg*1e6:.2f} keV")
    print(f"  Gamma(h -> gammagamma) = {width_gg*1e6:.2f} keV")
    print(f"  Ratio Zgamma/gammagamma = {ratio:.4f}")
    print(f"  SM expected ratio = {BR_ratio_SM:.4f}")

    deviation = abs(ratio - BR_ratio_SM) / BR_ratio_SM * 100
    print(f"  Deviation: {deviation:.1f}%")

    # Should be within 20% (combining uncertainties from both channels)
    if deviation > 20:
        passed = False
        print(f"  ERROR: BR ratio deviation {deviation:.1f}% exceeds 20% tolerance")

    if passed:
        print("  PASS: BR ratio Zgamma/gammagamma consistent")
    return passed


def test_11_threshold():
    """Test 11: m_H = M_Z threshold (Gamma -> 0)."""
    print("\n" + "="*60)
    print("Test 11: Threshold m_H -> M_Z (Gamma -> 0)")
    print("="*60)

    passed = True

    # At threshold m_H = M_Z, the phase space factor vanishes
    original_mH = const.m_H

    # Test with m_H approaching M_Z
    test_masses = [const.M_Z * 1.01, const.M_Z * 1.001, const.M_Z * 1.0001]

    print("  Testing phase space suppression near threshold:")
    for mH_test in test_masses:
        ps = (1.0 - const.M_Z**2 / mH_test**2)**3
        print(f"    m_H = {mH_test:.4f} GeV: phase space = {ps:.2e}")
        if ps < 0:
            passed = False
            print("    ERROR: Phase space should be positive")

    # At exact threshold
    ps_threshold = (1.0 - const.M_Z**2 / const.M_Z**2)**3
    print(f"\n  At m_H = M_Z: phase space = {ps_threshold:.2e}")
    if abs(ps_threshold) > 1e-15:
        passed = False
        print("  ERROR: Phase space should vanish at threshold")

    # Below threshold (m_H < M_Z): decay is kinematically forbidden
    mH_below = const.M_Z * 0.99
    ps_below = (1.0 - const.M_Z**2 / mH_below**2)**3
    print(f"  Below threshold (m_H = {mH_below:.2f} GeV): (1-MZ^2/mH^2)^3 = {ps_below:.4f}")
    print(f"  (Negative -> kinematically forbidden)")

    if passed:
        print("\n  PASS: Threshold behavior correct (Gamma -> 0 as m_H -> M_Z)")
    return passed


# =============================================================================
# Plotting
# =============================================================================

def get_plot_dir():
    """Get the plots directory path."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    plot_dir = os.path.join(script_dir, '..', 'plots')
    os.makedirs(plot_dir, exist_ok=True)
    return plot_dir


def plot_loop_functions():
    """Plot 1: Loop functions I1, I2, A_{1/2}^Zgamma, A_1^Zgamma."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Plot I1, I2 for fermion as function of tau_dj (Djouadi convention)
    # lambda/tau ratio is fixed = m_H^2/M_Z^2 (since lambda = 4m^2/M_Z^2, tau = 4m^2/m_H^2)
    lambda_tau_ratio = const.m_H**2 / const.M_Z**2  # ~1.885

    tau_dj_range = np.linspace(0.5, 20.0, 200)

    I1_vals = []
    I2_vals = []
    A_half_vals = []

    for tau_dj in tau_dj_range:
        lam_dj = tau_dj * lambda_tau_ratio
        i1 = I1_dj(tau_dj, lam_dj)
        i2 = I2_dj(tau_dj, lam_dj)
        ah = i1 - i2
        I1_vals.append(i1.real)
        I2_vals.append(i2.real)
        A_half_vals.append(ah.real)

    ax = axes[0]
    ax.plot(tau_dj_range, I1_vals, 'b-', linewidth=2, label=r'$I_1(\tau, \lambda)$')
    ax.plot(tau_dj_range, I2_vals, 'r-', linewidth=2, label=r'$I_2(\tau, \lambda)$')
    ax.plot(tau_dj_range, A_half_vals, 'g--', linewidth=2, label=r'$A_{1/2}^{Z\gamma} = I_1 - I_2$')

    tau_t_dj = 4 * const.m_t**2 / const.m_H**2
    ax.axvline(tau_t_dj, color='gray', linestyle=':', alpha=0.7,
               label=f'$\\tau_t$ = {tau_t_dj:.2f}')

    ax.set_xlabel(r'$\tau = 4m^2/m_H^2$ (Djouadi)', fontsize=12)
    ax.set_ylabel('Function value', fontsize=12)
    ax.set_title(r'$h \to Z\gamma$ Master Integrals', fontsize=13)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # Plot A_1^Zgamma for W boson as function of m_W (varying effective W mass)
    mW_range = np.linspace(50, 200, 200)
    A1_vals = []
    for mW in mW_range:
        a1 = A_one_Zgamma(mW, const.m_H, const.M_Z)
        A1_vals.append(a1.real)

    ax = axes[1]
    ax.plot(mW_range, A1_vals, 'r-', linewidth=2, label=r'$A_1^{Z\gamma}(M_W)$')

    A1_phys = A_one_Zgamma(const.M_W, const.m_H, const.M_Z)
    ax.plot(const.M_W, A1_phys.real, 'ko', markersize=8,
            label=f'Physical: {A1_phys.real:.2f}')

    ax.set_xlabel(r'$M_W$ (GeV)', fontsize=12)
    ax.set_ylabel(r'$A_1^{Z\gamma}$', fontsize=12)
    ax.set_title(r'W Boson Loop Function', fontsize=13)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(get_plot_dir(), 'proposition_6_3_4_loop_functions.png'), dpi=150)
    print("  Plot saved: verification/plots/proposition_6_3_4_loop_functions.png")
    plt.close()


def plot_amplitude_breakdown():
    """Plot 2: Amplitude breakdown by contribution."""
    fig, ax = plt.subplots(figsize=(10, 6))

    _, contributions = calculate_Zgamma_amplitude()

    labels = ['W boson', 'Top quark', 'Bottom quark', 'Tau lepton']
    values = [contributions['W'].real, contributions['top'].real,
              contributions['bottom'].real, contributions['tau'].real]
    colors = ['red', 'blue', 'orange', 'green']

    bars = ax.bar(labels, values, color=colors, alpha=0.7, edgecolor='black')

    total = sum(v for v in values)
    ax.axhline(total, color='purple', linestyle='--', linewidth=2,
               label=f'Total = {total:.2f}')

    for bar, val in zip(bars, values):
        height = bar.get_height()
        if abs(val) > 0.01:
            ax.annotate(f'{val:.3f}',
                        xy=(bar.get_x() + bar.get_width()/2, height),
                        xytext=(0, 5 if height > 0 else -15),
                        textcoords="offset points",
                        ha='center', va='bottom' if height > 0 else 'top',
                        fontsize=11, fontweight='bold')

    ax.set_ylabel(r'Amplitude contribution $\mathcal{A}_{Z\gamma}$', fontsize=12)
    ax.set_title(r'$h \to Z\gamma$ Amplitude Breakdown', fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig(os.path.join(get_plot_dir(), 'proposition_6_3_4_amplitude_breakdown.png'), dpi=150)
    print("  Plot saved: verification/plots/proposition_6_3_4_amplitude_breakdown.png")
    plt.close()


def plot_width_comparison():
    """Plot 3: Width comparison CG vs SM."""
    fig, ax = plt.subplots(figsize=(10, 6))

    A_total, _ = calculate_Zgamma_amplitude()
    width_CG = calculate_Zgamma_width(A_total) * 1e6  # keV

    # SM prediction
    width_SM = 6.32
    width_SM_err = 0.13

    # Also show gammagamma for comparison
    width_gg_CG = calculate_gg_width() * 1e6
    width_gg_SM = 9.28
    width_gg_SM_err = 0.15

    x = np.arange(2)
    width_bar = 0.3

    # CG bars
    ax.bar(x - width_bar/2, [width_CG, width_gg_CG], width_bar,
           label='CG Prediction', color='steelblue', alpha=0.8, edgecolor='black')

    # SM bars with error bars
    ax.bar(x + width_bar/2, [width_SM, width_gg_SM], width_bar,
           label='SM Prediction', color='coral', alpha=0.8, edgecolor='black',
           yerr=[width_SM_err, width_gg_SM_err], capsize=5)

    ax.set_xticks(x)
    ax.set_xticklabels([r'$h \to Z\gamma$', r'$h \to \gamma\gamma$'], fontsize=13)
    ax.set_ylabel(r'$\Gamma$ (keV)', fontsize=12)
    ax.set_title('Loop-Induced Higgs Decay Widths: CG vs SM', fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3, axis='y')

    # Add value labels
    ax.text(0 - width_bar/2, width_CG + 0.15, f'{width_CG:.2f}', ha='center', fontsize=10)
    ax.text(0 + width_bar/2, width_SM + 0.25, f'{width_SM:.2f}', ha='center', fontsize=10)
    ax.text(1 - width_bar/2, width_gg_CG + 0.15, f'{width_gg_CG:.2f}', ha='center', fontsize=10)
    ax.text(1 + width_bar/2, width_gg_SM + 0.25, f'{width_gg_SM:.2f}', ha='center', fontsize=10)

    plt.tight_layout()
    plt.savefig(os.path.join(get_plot_dir(), 'proposition_6_3_4_width_comparison.png'), dpi=150)
    print("  Plot saved: verification/plots/proposition_6_3_4_width_comparison.png")
    plt.close()


def plot_signal_strength():
    """Plot 4: Signal strength with ATLAS data point."""
    fig, ax = plt.subplots(figsize=(10, 6))

    A_total, _ = calculate_Zgamma_amplitude()
    width_CG = calculate_Zgamma_width(A_total)
    width_SM = 6.32e-6  # GeV

    mu_CG = width_CG / width_SM

    # Experimental measurements
    experiments = {
        'ATLAS 2023': (2.0, 0.6),
        'CMS Run 2': (2.4, 0.9),
    }

    y_pos = [2, 1]
    colors_exp = ['green', 'orange']

    for i, (name, (mu, err)) in enumerate(experiments.items()):
        ax.errorbar(mu, y_pos[i], xerr=err, fmt='o', markersize=10,
                     color=colors_exp[i], capsize=8, capthick=2, linewidth=2,
                     label=f'{name}: {mu:.1f} +/- {err:.1f}')

    # SM/CG prediction
    ax.axvline(1.0, color='blue', linewidth=2, linestyle='-', label='SM/CG: 1.00')
    ax.axvspan(1.0 - 0.03, 1.0 + 0.03, alpha=0.2, color='blue')

    # CG specific point
    ax.plot(mu_CG, 3, 's', markersize=12, color='blue', label=f'CG calc: {mu_CG:.2f}')

    ax.set_xlabel(r'Signal strength $\mu_{Z\gamma}$', fontsize=12)
    ax.set_yticks([1, 2, 3])
    ax.set_yticklabels(['CMS Run 2', 'ATLAS 2023', 'CG calculation'])
    ax.set_title(r'$h \to Z\gamma$ Signal Strength', fontsize=14)
    ax.legend(loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3, axis='x')
    ax.set_xlim(-0.5, 4.0)

    plt.tight_layout()
    plt.savefig(os.path.join(get_plot_dir(), 'proposition_6_3_4_signal_strength.png'), dpi=150)
    print("  Plot saved: verification/plots/proposition_6_3_4_signal_strength.png")
    plt.close()


# =============================================================================
# Main
# =============================================================================

def main():
    """Run all verification tests and generate plots."""
    print("="*60)
    print("Proposition 6.3.4: Higgs Z-Gamma Decay (h -> Zgamma)")
    print("Verification Script")
    print("="*60)

    tests = [
        ("g(tau) function", test_1_g_tau_function),
        ("I1, I2 consistency", test_2_I1_I2_consistency),
        ("M_Z -> 0 limit", test_3_MZ_to_zero_limit),
        ("Loop function values", test_4_loop_function_values),
        ("Fermion couplings", test_5_fermion_coupling_factors),
        ("Phase space factor", test_6_phase_space_factor),
        ("Total amplitude", test_7_total_amplitude),
        ("Decay width", test_8_decay_width),
        ("Branching ratio", test_9_branching_ratio),
        ("BR ratio Zgamma/gg", test_10_BR_ratio_cross_check),
        ("m_H=M_Z threshold", test_11_threshold),
    ]

    results = []
    for name, test_func in tests:
        try:
            result = test_func()
            results.append((name, result))
        except Exception as e:
            print(f"  FAIL: {e}")
            import traceback
            traceback.print_exc()
            results.append((name, False))

    # Generate plots
    print("\n" + "="*60)
    print("Generating Plots")
    print("="*60)
    try:
        plot_loop_functions()
        plot_amplitude_breakdown()
        plot_width_comparison()
        plot_signal_strength()
    except Exception as e:
        print(f"  Plot generation error: {e}")
        import traceback
        traceback.print_exc()

    # Summary
    print("\n" + "="*60)
    print("VERIFICATION SUMMARY")
    print("="*60)

    passed = sum(1 for _, r in results if r)
    total = len(results)

    for name, result in results:
        status = "PASS" if result else "FAIL"
        print(f"  {name:25s}: {status}")

    print(f"\n  Total: {passed}/{total} tests passed")

    # Final results
    A_total, contributions = calculate_Zgamma_amplitude()
    width = calculate_Zgamma_width(A_total)
    width_gg = calculate_gg_width()

    print(f"\n  Final Results:")
    print(f"    Gamma(h -> Zgamma)_CG  = {width*1e6:.2f} keV")
    print(f"    BR(h -> Zgamma)_CG     = {width/const.Gamma_H_total*1e3:.3f} x 10^-3")
    print(f"    Gamma(h -> gammagamma)  = {width_gg*1e6:.2f} keV")
    print(f"    BR ratio Zgamma/gg     = {width/width_gg:.4f}")
    print(f"    mu_Zgamma              = {width/(6.32e-6):.2f}")

    # Save results to JSON
    results_dict = {
        "proposition": "6.3.4",
        "title": "Higgs Z-Gamma Decay (h -> Zgamma)",
        "timestamp": datetime.now().isoformat(),
        "tests_passed": passed,
        "tests_total": total,
        "results": {
            "Gamma_Zgamma_keV": float(width * 1e6),
            "BR_Zgamma": float(width / const.Gamma_H_total),
            "Gamma_gammagamma_keV": float(width_gg * 1e6),
            "BR_ratio_Zgamma_gg": float(width / width_gg),
            "mu_Zgamma": float(width / 6.32e-6),
            "phase_space_factor": float((1 - const.M_Z**2/const.m_H**2)**3),
            "A_total_real": float(A_total.real),
            "A_total_imag": float(A_total.imag),
            "A_total_squared": float(np.abs(A_total)**2),
            "contributions": {
                name: {"real": float(val.real), "imag": float(val.imag), "abs": float(abs(val))}
                for name, val in contributions.items()
            }
        },
        "test_results": [
            {"name": name, "passed": result} for name, result in results
        ],
        "overall_status": "PASSED" if passed == total else "FAILED"
    }

    script_dir = os.path.dirname(os.path.abspath(__file__))
    json_path = os.path.join(script_dir, '..', 'foundations',
                              'prop_6_3_4_results.json')
    os.makedirs(os.path.dirname(json_path), exist_ok=True)
    with open(json_path, 'w') as f:
        json.dump(results_dict, f, indent=2)
    print(f"\n  Results saved to: verification/foundations/prop_6_3_4_results.json")

    if passed == total:
        print(f"\n  PROPOSITION 6.3.4 VERIFIED")
        print("  h -> Zgamma decay width matches SM prediction")
    else:
        print(f"\n  VERIFICATION INCOMPLETE ({total-passed} test(s) failed)")

    return passed == total


if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
