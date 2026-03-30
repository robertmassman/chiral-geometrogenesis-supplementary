#!/usr/bin/env python3
"""
Proposition 0.0.38 — Verification of Four Mathematical Corrections
===================================================================

This script verifies the four corrections needed for the exact stella gauge
partition function using numerical integration with the SU(3) Weyl integration
formula:

    int_{SU(3)} f(U) dU = (1/(24pi^2)) int_0^{2pi} int_0^{2pi} dthet1 dtheta2 |Delta(theta)|^2 f(theta1,theta2)

where z1=e^{itheta1}, z2=e^{itheta2}, z3=e^{-i(theta1+theta2)} and
    |Delta(theta)|^2 = prod_{i<j} |z_i - z_j|^2

Corrections verified:
  1. Vandermonde coefficient: |Delta(theta)|^2 = 64 prod sin^2(...) (not 8)
  2. a1(beta) coefficient: Z = 1 + beta^2/36 + ... (not beta^2/54)
  3. a8(beta) coefficient: a8 = beta^2/288 (not beta^2/324)
  4. Plaquette formula: <P> = beta/18 at leading order (no "+1")
"""

import numpy as np
from scipy import integrate
import json
import sys

# ============================================================================
# Core Weyl Integration Machinery
# ============================================================================

def vandermonde_sq(theta1, theta2):
    """
    Compute |Delta(theta)|^2 = prod_{i<j} |z_i - z_j|^2 for SU(3).
    
    Eigenvalues: z1=e^{itheta1}, z2=e^{itheta2}, z3=e^{-i(theta1+theta2)}.
    |e^{ia} - e^{ib}|^2 = 2 - 2cos(a-b)
    """
    d12 = 2.0 - 2.0 * np.cos(theta1 - theta2)
    d13 = 2.0 - 2.0 * np.cos(2*theta1 + theta2)
    d23 = 2.0 - 2.0 * np.cos(theta1 + 2*theta2)
    return d12 * d13 * d23


def weyl_integrate(f, n_points=500):
    """
    Numerically integrate f over SU(3) using the Weyl integration formula.
    
    int_{SU(3)} f(U) dU = (1/(24pi^2)) int_0^{2pi} int_0^{2pi} |Delta|^2 f dtheta1 dtheta2
    
    Normalization 1/(24pi^2) = 1/(3! * (2pi)^2).
    """
    theta = np.linspace(0, 2*np.pi, n_points, endpoint=False)
    dtheta = 2*np.pi / n_points
    t1, t2 = np.meshgrid(theta, theta, indexing='ij')
    vdm = vandermonde_sq(t1, t2)
    fvals = f(t1, t2)
    integral = np.sum(vdm * fvals) * dtheta * dtheta
    norm = 1.0 / (24.0 * np.pi**2)
    return norm * integral


def weyl_integrate_scipy(f):
    """Higher-accuracy integration using scipy dblquad."""
    def integrand(theta2, theta1):
        return vandermonde_sq(theta1, theta2) * f(theta1, theta2)
    
    norm = 1.0 / (24.0 * np.pi**2)
    result, error = integrate.dblquad(
        integrand,
        0, 2*np.pi,
        0, 2*np.pi,
        epsabs=1e-10,
        epsrel=1e-10
    )
    return norm * result, norm * error


def trace_fundamental(theta1, theta2):
    """Tr(U) = z1 + z2 + z3 = e^{itheta1} + e^{itheta2} + e^{-i(theta1+theta2)}"""
    return np.exp(1j * theta1) + np.exp(1j * theta2) + np.exp(-1j * (theta1 + theta2))


def re_trace_fundamental(theta1, theta2):
    """Re Tr(U) in the fundamental representation."""
    return np.cos(theta1) + np.cos(theta2) + np.cos(theta1 + theta2)


def trace_adjoint(theta1, theta2):
    """chi_8(U) = |Tr_fund(U)|^2 - 1 for SU(3)."""
    tr = trace_fundamental(theta1, theta2)
    return np.abs(tr)**2 - 1.0


# ============================================================================
# CORRECTION 1: Vandermonde Coefficient (64, not 8)
# ============================================================================

def verify_vandermonde_coefficient():
    print("=" * 72)
    print("CORRECTION 1: Vandermonde Coefficient |Delta(theta)|^2")
    print("=" * 72)
    
    # Scan for maximum
    n = 1000
    theta = np.linspace(0, 2*np.pi, n, endpoint=False)
    t1, t2 = np.meshgrid(theta, theta, indexing='ij')
    vdm = vandermonde_sq(t1, t2)
    
    max_val = np.max(vdm)
    max_idx = np.unravel_index(np.argmax(vdm), vdm.shape)
    max_t1 = theta[max_idx[0]]
    max_t2 = theta[max_idx[1]]
    
    print(f"\nNumerical scan (n={n}):")
    print(f"  max |Delta|^2 = {max_val:.6f}")
    print(f"  at theta1 = {max_t1:.6f} ({max_t1/np.pi:.4f}pi)")
    print(f"  at theta2 = {max_t2:.6f} ({max_t2/np.pi:.4f}pi)")
    
    # At Z3-symmetric point: theta1=2pi/3, theta2=4pi/3
    t1_sym = 2*np.pi/3
    t2_sym = 4*np.pi/3
    vdm_sym = vandermonde_sq(t1_sym, t2_sym)
    print(f"\nAt Z3-symmetric point (theta1=2pi/3, theta2=4pi/3):")
    print(f"  |Delta|^2 = {vdm_sym:.6f}")
    
    # Analytical: |e^{ia}-e^{ib}|^2 = 4 sin^2((a-b)/2)
    # So |Delta|^2 = 4^3 prod_{i<j} sin^2((theta_i-theta_j)/2)
    #             = 64 prod sin^2(...)
    # At Z3 point, all phase differences = 2pi/3, half-differences = pi/3
    # sin^2(pi/3) = 3/4
    # Product = (3/4)^3 = 27/64
    # |Delta|^2 = 64 * 27/64 = 27
    
    sin_product = np.sin(np.pi/3)**2
    analytical_max = 64 * sin_product**3
    
    print(f"\nAnalytical derivation:")
    print(f"  |e^{{ia}} - e^{{ib}}|^2 = 4 sin^2((a-b)/2)")
    print(f"  Therefore |Delta|^2 = 4^3 * prod sin^2((theta_i-theta_j)/2)")
    print(f"                      = 64 * prod sin^2((theta_i-theta_j)/2)")
    print(f"  At Z3 point: sin^2(pi/3) = {sin_product:.6f} = 3/4")
    print(f"  Product of three factors = (3/4)^3 = {sin_product**3:.6f}")
    print(f"  |Delta|^2 = 64 * {sin_product**3:.6f} = {analytical_max:.6f}")
    print(f"  Numerical max = {max_val:.6f}")
    
    # Verify normalization: int dU = 1
    def one(t1, t2):
        return np.ones_like(t1)
    norm_check = weyl_integrate(one, n_points=500)
    norm_scipy, norm_err = weyl_integrate_scipy(lambda t1, t2: 1.0)
    print(f"\nNormalization check: int_{{SU(3)}} dU = {norm_check:.8f} (grid)")
    print(f"                                      = {norm_scipy:.8f} +/- {norm_err:.2e} (scipy)")
    
    # Integral of Vandermonde
    vdm_integral = np.sum(vdm) * (2*np.pi/n)**2
    print(f"\nint |Delta|^2 dtheta1 dtheta2 = {vdm_integral:.4f}")
    print(f"  24 pi^2 = {24 * np.pi**2:.4f}")
    print(f"  Ratio = {vdm_integral / (24 * np.pi**2):.8f} (should be 1.0)")
    
    print(f"\n--- KEY RESULT ---")
    print(f"|Delta|^2 = 64 * prod sin^2((theta_i-theta_j)/2), coefficient = 64")
    print(f"If one incorrectly uses coefficient 8:")
    print(f"  8 * (3/4)^3 = {8 * sin_product**3:.6f} != 27")
    print(f"Correct coefficient 64: 64 * (3/4)^3 = {64 * sin_product**3:.6f} = 27  [VERIFIED]")
    
    return {
        "max_vandermonde_sq": float(max_val),
        "max_at_theta1": float(max_t1),
        "max_at_theta2": float(max_t2),
        "z3_symmetric_value": float(vdm_sym),
        "normalization_integral": float(vdm_integral),
        "expected_normalization": float(24 * np.pi**2),
        "coefficient_correct": 64,
        "coefficient_incorrect": 8,
        "pass": abs(max_val - 27.0) < 0.1 and abs(norm_scipy - 1.0) < 0.01
    }


# ============================================================================
# CORRECTION 2: a1(beta) coefficient (1 + beta^2/36, not beta^2/54)
# ============================================================================

def verify_a1_coefficient():
    print("\n" + "=" * 72)
    print("CORRECTION 2: a1(beta) Coefficient — Z(beta) Expansion")
    print("=" * 72)
    
    # Compute Haar measure moments
    print("\nComputing Haar measure moments of Re Tr(U)...")
    
    val_1, err_1 = weyl_integrate_scipy(lambda t1, t2: 1.0)
    print(f"  <1> = {val_1:.10f} (should be 1.0)")
    
    val_ReTr, err_ReTr = weyl_integrate_scipy(
        lambda t1, t2: re_trace_fundamental(t1, t2))
    print(f"  <Re Tr U> = {val_ReTr:.10f} (should be 0)")
    
    val_ReTr2, err_ReTr2 = weyl_integrate_scipy(
        lambda t1, t2: re_trace_fundamental(t1, t2)**2)
    print(f"  <(Re Tr U)^2> = {val_ReTr2:.10f} +/- {err_ReTr2:.2e}")
    
    val_absTr2, err_absTr2 = weyl_integrate_scipy(
        lambda t1, t2: np.abs(trace_fundamental(t1, t2))**2)
    print(f"  <|Tr U|^2> = {val_absTr2:.10f} +/- {err_absTr2:.2e}")
    
    val_ReTr4, err_ReTr4 = weyl_integrate_scipy(
        lambda t1, t2: re_trace_fundamental(t1, t2)**4)
    print(f"  <(Re Tr U)^4> = {val_ReTr4:.10f} +/- {err_ReTr4:.2e}")
    
    # Theoretical values by Schur orthogonality:
    # <|Tr|^2> = 1 (fundamental is irreducible)
    # Tr(U)^2 decomposes as Sym^2(3) + Anti^2(3) = 6 + 3bar, no singlet => <Tr^2>=0
    # (Re Tr)^2 = (1/2)(|Tr|^2 + Re(Tr^2))
    # <(Re Tr)^2> = (1/2)(1 + 0) = 1/2
    print(f"\n  Theoretical predictions:")
    print(f"    <|Tr|^2> = 1 (Schur)        -> got {val_absTr2:.8f}")
    print(f"    <(Re Tr)^2> = 1/2 = 0.5     -> got {val_ReTr2:.8f}")
    
    # Z(beta) expansion with Wilson action convention:
    # Z(beta) = int dU exp((beta/3) Re Tr U)
    # = sum_n (beta/3)^n / n! * <(Re Tr)^n>
    # = 1 + 0 + (beta/3)^2/2 * (1/2) + ...
    # = 1 + beta^2/(9*4) + ... = 1 + beta^2/36 + ...
    
    Z_coeff_numerical = val_ReTr2 / (2.0 * 9.0)
    print(f"\n  Z(beta) = 1 + (beta/3)^2/2! * <(ReTr)^2> + ...")
    print(f"         = 1 + beta^2 * <(ReTr)^2> / 18 + ...")
    print(f"         = 1 + beta^2 * {Z_coeff_numerical:.10f} + ...")
    print(f"  Correct claim: 1 + beta^2/36 = 1 + {1/36:.10f} beta^2")
    print(f"  Wrong claim:   1 + beta^2/54 = 1 + {1/54:.10f} beta^2")
    
    # Direct numerical verification
    print(f"\n  Direct numerical check of Z(beta) at several beta values:")
    print(f"  {'beta':>6s}  {'Z_numerical':>14s}  {'1+b^2/36':>12s}  {'1+b^2/54':>12s}  {'err(1/36)':>10s}  {'err(1/54)':>10s}")
    print(f"  " + "-" * 72)
    
    all_closer_36 = True
    for beta in [0.1, 0.3, 0.5, 0.8, 1.0]:
        x = beta / 3.0
        Z_num = weyl_integrate(
            lambda t1, t2: np.exp(x * re_trace_fundamental(t1, t2)),
            n_points=600)
        Z_36 = 1.0 + beta**2 / 36.0
        Z_54 = 1.0 + beta**2 / 54.0
        e36 = abs(Z_num - Z_36)
        e54 = abs(Z_num - Z_54)
        if beta <= 0.5:
            all_closer_36 = all_closer_36 and (e36 < e54)
        print(f"  {beta:6.2f}  {Z_num:14.8f}  {Z_36:12.8f}  {Z_54:12.8f}  {e36:10.2e}  {e54:10.2e}")
    
    print(f"\n  At small beta, Z is closer to 1+beta^2/36: {all_closer_36}")
    
    return {
        "ReTr_moment1": float(val_ReTr),
        "ReTr_moment2": float(val_ReTr2),
        "absTr_moment2": float(val_absTr2),
        "ReTr_moment4": float(val_ReTr4),
        "Z_coeff_numerical": float(Z_coeff_numerical),
        "expected_1_over_36": 1.0/36.0,
        "wrong_1_over_54": 1.0/54.0,
        "correct_coefficient": "1/36",
        "wrong_coefficient": "1/54",
        "pass": abs(val_ReTr2 - 0.5) < 0.01 and all_closer_36
    }


# ============================================================================
# CORRECTION 3: a8(beta) coefficient (beta^2/288, not beta^2/324)
# ============================================================================

def verify_a8_coefficient():
    print("\n" + "=" * 72)
    print("CORRECTION 3: a8(beta) Coefficient")
    print("=" * 72)
    
    # Moments involving adjoint character
    val_chi8, err_chi8 = weyl_integrate_scipy(
        lambda t1, t2: trace_adjoint(t1, t2))
    print(f"\n  <chi_8> = {val_chi8:.10f} (should be 0)")
    
    val_chi8_ReTr, err = weyl_integrate_scipy(
        lambda t1, t2: trace_adjoint(t1, t2) * re_trace_fundamental(t1, t2))
    print(f"  <chi_8 * ReTr> = {val_chi8_ReTr:.10f} (should be 0)")
    
    val_chi8_ReTr2, err = weyl_integrate_scipy(
        lambda t1, t2: trace_adjoint(t1, t2) * re_trace_fundamental(t1, t2)**2)
    print(f"  <chi_8 * (ReTr)^2> = {val_chi8_ReTr2:.10f}")
    
    # a8(x) = (1/d_8) int dU chi_8(U) exp(x ReTr U)
    # = (1/8) [0 + 0 + (x^2/2) <chi_8 (ReTr)^2> + ...]
    # With x = beta/3:
    # a8(beta) = (1/8) * (beta/3)^2/2 * <chi_8*(ReTr)^2>
    #          = beta^2/(8*18) * <chi_8*(ReTr)^2>
    #          = beta^2/144 * <chi_8*(ReTr)^2>
    
    a8_coeff = val_chi8_ReTr2 / 144.0
    print(f"\n  a8(beta) = beta^2 * <chi_8*(ReTr)^2> / 144")
    print(f"           = beta^2 * {val_chi8_ReTr2:.10f} / 144")
    print(f"           = beta^2 * {a8_coeff:.10f}")
    
    # Analytical value of <chi_8 * (ReTr)^2>:
    # chi_8 = |Tr|^2 - 1
    # (ReTr)^2 = (1/2)(|Tr|^2 + Re(Tr^2))
    # <chi_8 * (ReTr)^2> = <(|Tr|^2-1)(1/2)(|Tr|^2+Re(Tr^2))>
    #   = (1/2)[<|Tr|^4> + <|Tr|^2 Re(Tr^2)> - <|Tr|^2> - <Re(Tr^2)>]
    
    val_absTr4, err = weyl_integrate_scipy(
        lambda t1, t2: np.abs(trace_fundamental(t1, t2))**4)
    print(f"\n  <|Tr|^4> = {val_absTr4:.10f} (should be 2)")
    
    val_absTr2_ReTr2, err = weyl_integrate_scipy(
        lambda t1, t2: np.abs(trace_fundamental(t1, t2))**2 * np.real(trace_fundamental(t1, t2)**2))
    print(f"  <|Tr|^2 Re(Tr^2)> = {val_absTr2_ReTr2:.10f}")
    
    val_ReTr2_char, err = weyl_integrate_scipy(
        lambda t1, t2: np.real(trace_fundamental(t1, t2)**2))
    print(f"  <Re(Tr^2)> = {val_ReTr2_char:.10f} (should be 0)")
    
    val_absTr2, _ = weyl_integrate_scipy(
        lambda t1, t2: np.abs(trace_fundamental(t1, t2))**2)
    
    analytical_chi8_ReTr2 = 0.5 * (val_absTr4 + val_absTr2_ReTr2 - val_absTr2 - val_ReTr2_char)
    print(f"\n  Cross-check: <chi_8*(ReTr)^2> via decomposition = {analytical_chi8_ReTr2:.10f}")
    print(f"  Direct computation: {val_chi8_ReTr2:.10f}")
    
    # Theoretical: <|Tr|^4> = 2 by character decomposition
    # |chi_3|^2 = 1 + chi_8, so |chi_3|^4 = 1 + 2chi_8 + chi_8^2
    # <|chi_3|^4> = 1 + 0 + <chi_8^2> = 1 + 1 = 2
    print(f"\n  <|Tr|^4> = 2 (from 3 x 3bar = 1 + 8): got {val_absTr4:.8f}")
    
    # Numerical computation at small beta
    print(f"\n--- Computing a8(beta) numerically at small beta ---")
    print(f"  {'beta':>6s}  {'a8_numerical':>14s}  {'b^2/288':>12s}  {'b^2/324':>12s}")
    print(f"  " + "-" * 50)
    
    for beta in [0.1, 0.3, 0.5, 0.8, 1.0]:
        x = beta / 3.0
        a8_num = weyl_integrate(
            lambda t1, t2: trace_adjoint(t1, t2) * np.exp(x * re_trace_fundamental(t1, t2)),
            n_points=500) / 8.0
        print(f"  {beta:6.2f}  {a8_num:14.10f}  {beta**2/288:12.10f}  {beta**2/324:12.10f}")
    
    # Comparison
    err_288 = abs(a8_coeff - 1.0/288.0)
    err_324 = abs(a8_coeff - 1.0/324.0)
    closer_to_288 = err_288 < err_324
    
    print(f"\n  Comparison:")
    print(f"    1/288 = {1/288:.10f} (correct)")
    print(f"    1/324 = {1/324:.10f} (wrong)")
    print(f"    Numerical = {a8_coeff:.10f}")
    print(f"    |num - 1/288| = {err_288:.2e}")
    print(f"    |num - 1/324| = {err_324:.2e}")
    print(f"    Closer to 1/288: {closer_to_288}")
    
    print(f"\n  d8 * a8(beta):")
    print(f"    Using 1/288: 8 * beta^2/288 = beta^2/36 = {8/288:.10f}")
    print(f"    Using 1/324: 8 * beta^2/324 = {8/324:.10f}")
    print(f"    Numerical: 8 * {a8_coeff:.8f} = {8*a8_coeff:.10f}")
    
    return {
        "chi8_moment0": float(val_chi8),
        "chi8_ReTr_moment": float(val_chi8_ReTr),
        "chi8_ReTr2_moment": float(val_chi8_ReTr2),
        "absTr4": float(val_absTr4),
        "a8_beta_coefficient": float(a8_coeff),
        "expected_correct": 1.0/288.0,
        "expected_wrong": 1.0/324.0,
        "closer_to_correct": bool(closer_to_288),
        "pass": closer_to_288
    }


# ============================================================================
# CORRECTION 4: Plaquette Formula (beta/18, not beta/18 + 1)
# ============================================================================

def verify_plaquette_formula():
    print("\n" + "=" * 72)
    print("CORRECTION 4: Plaquette Formula <P> = beta/18 (no +1)")
    print("=" * 72)
    
    N = 3
    
    # Compute <P>(beta) = (1/N) <Re Tr U>_beta for several beta
    print(f"\n{'beta':>6s}  {'<P> numerical':>15s}  {'beta/18':>12s}  {'beta/18+1':>12s}")
    print("-" * 55)
    
    plaq_data = []
    for beta in [0.01, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 3.0, 5.0, 6.0]:
        x = beta / N
        Z = weyl_integrate(
            lambda t1, t2: np.exp(x * re_trace_fundamental(t1, t2)),
            n_points=500)
        ReTr_avg = weyl_integrate(
            lambda t1, t2: re_trace_fundamental(t1, t2) * np.exp(x * re_trace_fundamental(t1, t2)),
            n_points=500) / Z
        plaq = ReTr_avg / N
        plaq_data.append((beta, plaq))
        print(f"{beta:6.2f}  {plaq:15.8f}  {beta/18:12.8f}  {beta/18+1:12.8f}")
    
    # Verify via d(ln Z)/d(beta) using central differences
    print(f"\n--- Verification via d(ln Z)/dbeta (central differences) ---")
    db = 0.0001
    print(f"\n{'beta':>6s}  {'d(lnZ)/dbeta':>14s}  {'(1/N)<ReTr>':>14s}  {'beta/18':>10s}")
    print("-" * 52)
    
    for beta in [0.1, 0.5, 1.0, 2.0]:
        xp = (beta + db) / N
        xm = (beta - db) / N
        x0 = beta / N
        
        Zp = weyl_integrate(
            lambda t1, t2: np.exp(xp * re_trace_fundamental(t1, t2)), n_points=500)
        Zm = weyl_integrate(
            lambda t1, t2: np.exp(xm * re_trace_fundamental(t1, t2)), n_points=500)
        Z0 = weyl_integrate(
            lambda t1, t2: np.exp(x0 * re_trace_fundamental(t1, t2)), n_points=500)
        
        dlnZ = (np.log(Zp) - np.log(Zm)) / (2 * db)
        plaq_direct = weyl_integrate(
            lambda t1, t2: re_trace_fundamental(t1, t2) * np.exp(x0 * re_trace_fundamental(t1, t2)),
            n_points=500) / (N * Z0)
        
        print(f"{beta:6.2f}  {dlnZ:14.8f}  {plaq_direct:14.8f}  {beta/18:10.8f}")
    
    # Key physical argument
    print(f"\n--- KEY PHYSICAL ARGUMENT ---")
    print(f"At beta=0 (infinite temperature / strong coupling):")
    print(f"  All gauge configs equally weighted (Haar measure)")
    print(f"  <Re Tr U>_Haar = 0 (by character orthogonality)")
    print(f"  Therefore <P> = 0 at beta=0")
    print(f"")
    print(f"  Formula 'beta/18':      at beta=0 gives 0    [CORRECT]")
    print(f"  Formula 'beta/18 + 1':  at beta=0 gives 1    [WRONG]")
    
    # Confirm <P> -> 0 as beta -> 0
    x_tiny = 0.001 / N
    Z_tiny = weyl_integrate(
        lambda t1, t2: np.exp(x_tiny * re_trace_fundamental(t1, t2)), n_points=500)
    plaq_tiny = weyl_integrate(
        lambda t1, t2: re_trace_fundamental(t1, t2) * np.exp(x_tiny * re_trace_fundamental(t1, t2)),
        n_points=500) / (N * Z_tiny)
    
    print(f"\n  At beta=0.001:")
    print(f"    <P> = {plaq_tiny:.12f}")
    print(f"    beta/18 = {0.001/18:.12f}")
    print(f"    beta/18+1 = {0.001/18+1:.12f}")
    print(f"    <P> matches beta/18: {abs(plaq_tiny - 0.001/18) < 1e-6}")
    
    # Expansion proof:
    # Z(beta) = 1 + beta^2/36 + ...
    # ln Z(beta) = beta^2/36 + ...
    # d(ln Z)/dbeta = 2*beta/36 + ... = beta/18 + ...
    # <P> = d(ln Z)/dbeta = beta/18 + O(beta^3)
    print(f"\n  Expansion proof:")
    print(f"    Z(beta) = 1 + beta^2/36 + O(beta^4)")
    print(f"    ln Z = beta^2/36 + O(beta^4)")
    print(f"    d(ln Z)/dbeta = beta/18 + O(beta^3)")
    print(f"    <P> = beta/18 at leading order [VERIFIED]")
    
    return {
        "plaq_at_tiny_beta": float(plaq_tiny),
        "correct_at_tiny": 0.001/18,
        "wrong_at_tiny": 0.001/18 + 1,
        "plaq_vanishes_at_beta0": bool(abs(plaq_tiny) < 1e-4),
        "leading_order": "beta/18",
        "pass": abs(plaq_tiny - 0.001/18) < abs(plaq_tiny - (0.001/18 + 1))
    }


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("Proposition 0.0.38 -- Verification of Four Mathematical Corrections")
    print("=" * 72)
    print("Using SU(3) Weyl integration formula with numerical quadrature")
    print()
    
    all_results = {}
    all_pass = True
    
    results1 = verify_vandermonde_coefficient()
    all_results["correction_1_vandermonde"] = results1
    all_pass = all_pass and results1["pass"]
    
    results2 = verify_a1_coefficient()
    all_results["correction_2_a1"] = results2
    all_pass = all_pass and results2["pass"]
    
    results3 = verify_a8_coefficient()
    all_results["correction_3_a8"] = results3
    all_pass = all_pass and results3["pass"]
    
    results4 = verify_plaquette_formula()
    all_results["correction_4_plaquette"] = results4
    all_pass = all_pass and results4["pass"]
    
    # Summary
    print("\n" + "=" * 72)
    print("SUMMARY OF CORRECTIONS")
    print("=" * 72)
    
    corrections = [
        ("1. Vandermonde coefficient",
         "|Delta|^2 = 64 prod sin^2(...)",
         "coefficient 8",
         results1["pass"]),
        ("2. a1(beta) in Z(beta)",
         "1 + beta^2/36",
         "beta^2/54",
         results2["pass"]),
        ("3. a8(beta) coefficient",
         "beta^2/288",
         "beta^2/324",
         results3["pass"]),
        ("4. Plaquette formula",
         "<P> = beta/18",
         "beta/18 + 1",
         results4["pass"]),
    ]
    
    for name, correct, wrong, passed in corrections:
        status = "VERIFIED" if passed else "FAILED"
        print(f"\n  {name}:")
        print(f"    Correct: {correct}")
        print(f"    Wrong:   {wrong}")
        print(f"    Status:  [{status}]")
    
    all_results["all_pass"] = all_pass
    print(f"\n  Overall: {'ALL CORRECTIONS VERIFIED' if all_pass else 'SOME CORRECTIONS FAILED'}")
    
    # Save results
    output_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/foundations/prop_0_0_38_corrections_results.json"
    
    def convert(obj):
        if isinstance(obj, (np.floating, np.float64)):
            return float(obj)
        if isinstance(obj, (np.integer, np.int64)):
            return int(obj)
        if isinstance(obj, np.bool_):
            return bool(obj)
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        return obj
    
    serializable = json.loads(json.dumps(all_results, default=convert))
    with open(output_path, 'w') as f:
        json.dump(serializable, f, indent=2)
    print(f"\n  Results saved to: {output_path}")
    
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
