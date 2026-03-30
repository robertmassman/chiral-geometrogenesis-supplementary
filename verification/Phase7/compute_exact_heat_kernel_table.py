"""
Compute exact SU(3) heat kernel eigenvalues for Prop 7.8.2 numerical table.

Uses Weyl integration formula for SU(3):
  u_R(β) = (1/d_R) * ∫ dg χ_R(g)* exp((β/3) Re χ_3(g)) / ∫ dg exp((β/3) Re χ_3(g))

The eigenvalues of g ∈ SU(3) are e^{iα₁}, e^{iα₂}, e^{-i(α₁+α₂)}.
The Haar measure in terms of eigenvalue angles is:
  dg = (1/3!) (1/(2π)²) |Δ(α)|² dα₁ dα₂

where Δ is the Vandermonde determinant.
"""

import numpy as np
from scipy import integrate

def vandermonde_sq(a1, a2):
    """Squared Vandermonde determinant for SU(3) eigenvalues e^{iα₁}, e^{iα₂}, e^{-i(α₁+α₂)}."""
    a3 = -a1 - a2
    # |e^{ia_i} - e^{ia_j}|^2 = 2 - 2cos(a_i - a_j)
    v12 = 2.0 - 2.0 * np.cos(a1 - a2)
    v13 = 2.0 - 2.0 * np.cos(a1 - a3)
    v23 = 2.0 - 2.0 * np.cos(a2 - a3)
    return v12 * v13 * v23

def chi_fund(a1, a2):
    """Fundamental character χ_3(g) = e^{iα₁} + e^{iα₂} + e^{-i(α₁+α₂)}."""
    return np.exp(1j * a1) + np.exp(1j * a2) + np.exp(-1j * (a1 + a2))

def chi_adj(a1, a2):
    """Adjoint character χ_8(g) = |χ_3(g)|² - 1."""
    c3 = chi_fund(a1, a2)
    return np.abs(c3)**2 - 1.0

def boltzmann(a1, a2, beta):
    """Boltzmann weight exp((β/3) Re χ_3(g))."""
    c3 = chi_fund(a1, a2)
    return np.exp((beta / 3.0) * np.real(c3))

def compute_u_R(beta, chi_R_func, d_R):
    """
    Compute normalized heat kernel eigenvalue u_R(β).

    u_R = (1/d_R) * ∫ dμ χ_R*(g) exp((β/3) Re χ_3(g)) / ∫ dμ exp((β/3) Re χ_3(g))

    where dμ includes the Vandermonde factor.
    """
    def integrand_num(a1, a2):
        """Numerator: χ_R(g) * Boltzmann * Vandermonde²."""
        return np.real(chi_R_func(a1, a2)) * boltzmann(a1, a2, beta) * vandermonde_sq(a1, a2)

    def integrand_den(a1, a2):
        """Denominator: Boltzmann * Vandermonde²."""
        return boltzmann(a1, a2, beta) * vandermonde_sq(a1, a2)

    # Integrate over [0, 2π] × [0, 2π]
    num, num_err = integrate.dblquad(
        integrand_num, 0, 2*np.pi, 0, 2*np.pi,
        epsabs=1e-12, epsrel=1e-12
    )
    den, den_err = integrate.dblquad(
        integrand_den, 0, 2*np.pi, 0, 2*np.pi,
        epsabs=1e-12, epsrel=1e-12
    )

    # Note: χ_R for the adjoint is real. For fundamental, χ_3* = χ_{3̄}.
    # We use Re(χ_R) in the integrand since we need the coefficient in the
    # character expansion. For self-conjugate reps (adjoint), this is exact.
    # For fundamental, u_3 uses χ_{3̄} · exp(S) / Z, which equals the
    # coefficient in the character expansion.

    u_R = num / (d_R * den)
    rel_err = np.sqrt((num_err/num)**2 + (den_err/den)**2) if num != 0 else 0

    return u_R, rel_err

def compute_u3_fund(beta):
    """
    Compute u_3(β) for fundamental representation.

    For fundamental rep, the character expansion coefficient is:
    u_3 = (1/d_3) * ∫ dg |χ_3(g)|² exp(S) / ∫ dg exp(S)

    because χ_3* = χ_{3̄} and the character expansion involves χ_R* in the projection.
    Actually: u_R = (1/d_R) ∫ dg χ_R(g)* exp(S) / ∫ dg exp(S)

    For fundamental: u_3 = (1/3) ∫ dg χ_{3̄}(g) exp(S) / Z

    But the Boltzmann factor exp((β/3) Re Tr_3) is invariant under g → g†,
    and ∫ dg χ_{3̄}(g) exp(S) = ∫ dg χ_3(g†) exp(S(g†)) = ∫ dg χ_3(g) exp(S(g))
    by the invariance of Haar measure under g → g†.

    So u_3 = (1/3) ∫ dg Re(χ_3(g)) exp(S) / Z = (1/3) ∫ dg χ_3(g) exp(S) / Z
    where the last equality uses that the imaginary part integrates to zero by symmetry.
    """
    def integrand_num(a1, a2):
        c3 = chi_fund(a1, a2)
        return np.real(c3) * boltzmann(a1, a2, beta) * vandermonde_sq(a1, a2)

    def integrand_den(a1, a2):
        return boltzmann(a1, a2, beta) * vandermonde_sq(a1, a2)

    num, num_err = integrate.dblquad(
        integrand_num, 0, 2*np.pi, 0, 2*np.pi,
        epsabs=1e-14, epsrel=1e-14
    )
    den, den_err = integrate.dblquad(
        integrand_den, 0, 2*np.pi, 0, 2*np.pi,
        epsabs=1e-14, epsrel=1e-14
    )

    u3 = num / (3.0 * den)
    return u3

def compute_u8_adj(beta):
    """Compute u_8(β) for adjoint representation."""
    return compute_u_R(beta, chi_adj, 8)[0]

# ============================================================
# Main computation
# ============================================================

print("=" * 90)
print("Exact SU(3) Heat Kernel Eigenvalues for Prop 7.8.2")
print("=" * 90)

# Check strong-coupling formulas
print("\n--- Strong-coupling checks ---")
for beta in [0.01, 0.05, 0.1]:
    u3 = compute_u3_fund(beta)
    u8 = compute_u8_adj(beta)
    u3_sc = beta / 18.0
    u8_sc = beta**2 / 288.0
    print(f"β={beta:6.3f}: u3={u3:.6e} (SC: {u3_sc:.6e}, ratio={u3/u3_sc:.4f}), "
          f"u8={u8:.6e} (SC: {u8_sc:.6e}, ratio={u8/u8_sc:.4f})")

# Check weak-coupling formulas
print("\n--- Weak-coupling checks ---")
for beta in [50, 100, 200, 500]:
    u3 = compute_u3_fund(beta)
    u8 = compute_u8_adj(beta)
    u3_wc = 1.0 - (4.0/3.0) / (2.0 * beta)
    u8_wc = 1.0 - 3.0 / (2.0 * beta)
    print(f"β={beta:5d}: u3={u3:.8f} (WC: {u3_wc:.8f}), "
          f"u8={u8:.8f} (WC: {u8_wc:.8f})")

# Full table
print("\n" + "=" * 90)
print("Complete numerical table")
print("=" * 90)
print(f"{'β':>8s} | {'u3':>14s} | {'u8':>14s} | {'σ3':>10s} | {'σ8':>10s} | {'σ8/σ3':>10s}")
print("-" * 75)

beta_values = [0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0, 200.0, 500.0]

results = []
for beta in beta_values:
    u3 = compute_u3_fund(beta)
    u8 = compute_u8_adj(beta)
    sigma3 = -np.log(u3) if u3 > 0 else float('inf')
    sigma8 = -np.log(u8) if u8 > 0 else float('inf')
    ratio = sigma8 / sigma3 if sigma3 != 0 else float('inf')
    results.append((beta, u3, u8, sigma3, sigma8, ratio))
    print(f"{beta:8.1f} | {u3:14.6e} | {u8:14.6e} | {sigma3:10.4f} | {sigma8:10.4f} | {ratio:10.4f}")

print("\n" + "=" * 90)
print("Verification of asymptotic ratios")
print("=" * 90)
print(f"Strong coupling limit (β→0): σ8/σ3 → 2.000")
print(f"Weak coupling limit (β→∞):   σ8/σ3 → 9/4 = 2.250")
print(f"\nActual values from table:")
print(f"  β=0.1:   σ8/σ3 = {results[0][5]:.4f} (expected ~2.00)")
print(f"  β=500.0: σ8/σ3 = {results[-1][5]:.4f} (expected ~2.25)")

# ============================================================
# Delta estimates and R_cont computation
# ============================================================
print("\n" + "=" * 90)
print("Delta estimates and R_cont^FI computation")
print("=" * 90)

# Framework-internal estimates
Lambda_over_sigma = 1.0 / 1.994
Delta_1 = 0.5 * Lambda_over_sigma**2
print(f"\nΔ₁ (Λ/√σ scaling) = (1/2)(1/1.994)² = {Delta_1:.4f}")

b0 = 11.0 / (16.0 * np.pi**2)
I_FCC = 0.276
Delta_2 = (3.0 / (2.0 * np.pi)) * np.sqrt(b0 * I_FCC)
print(f"Δ₂ (FCC tadpole)  = (3/2π)√(b₀·I_FCC) = {Delta_2:.4f}")

# Lattice-calibrated (for comparison only)
R_lat = 3.405
eta_SU3 = 1.5
M0_lat = R_lat / eta_SU3
Delta_3 = (M0_lat - 2.0) / 2.0
print(f"Δ₃ (lattice-calibrated) = (M₀ˡᵃᵗ - 2)/2 = ({M0_lat:.4f} - 2)/2 = {Delta_3:.4f}")
print(f"  ⚠ This uses R_cont^lat = {R_lat} — NOT framework-internal!")

# Adopted value: centered on Δ₁ (better-motivated full one-loop estimate)
Delta_adopted = Delta_1  # 0.1258
Delta_err = 0.07  # spans from below Δ₂ to ~0.20

print(f"\nAdopted (framework-internal): Δ = {Delta_adopted:.3f} ± {Delta_err:.2f}")
print(f"  (centered on Δ₁; ±0.07 spans [{Delta_adopted-Delta_err:.3f}, {Delta_adopted+Delta_err:.3f}])")
print(f"  Contains Δ₂ = {Delta_2:.3f}? {'Yes' if Delta_adopted - Delta_err <= Delta_2 <= Delta_adopted + Delta_err else 'No'}")
print(f"  Contains Δ₃ = {Delta_3:.3f}? {'Yes' if Delta_adopted - Delta_err <= Delta_3 <= Delta_adopted + Delta_err else 'No'}")

# M₀ computation
M0_SC = 2.0
M0_SC_err = 0.10  # 5% systematic from constituent gluon model
M0 = M0_SC * (1 + Delta_adopted)
print(f"\nM₀^SC = {M0_SC:.2f} ± {M0_SC_err:.2f} (5% systematic)")
print(f"M₀ = M₀^SC × (1 + Δ) = {M0_SC} × {1 + Delta_adopted:.4f} = {M0:.3f}")

# R_cont^FI
R_FI = M0_SC * (1 + Delta_adopted) * eta_SU3
print(f"\nR_cont^FI = M₀^SC × (1+Δ) × η = {M0_SC} × {1+Delta_adopted:.4f} × {eta_SU3} = {R_FI:.3f}")

# Error propagation with M₀^SC systematic
# R = M₀^SC × (1+Δ) × η
# δR/R = √[(δM₀^SC/M₀^SC)² + (δΔ/(1+Δ))²]
rel_err_M0 = M0_SC_err / M0_SC
rel_err_Delta = Delta_err / (1 + Delta_adopted)
rel_err_R = np.sqrt(rel_err_M0**2 + rel_err_Delta**2)
delta_R = R_FI * rel_err_R

print(f"\nError propagation:")
print(f"  δM₀^SC/M₀^SC = {rel_err_M0:.4f}")
print(f"  δΔ/(1+Δ) = {rel_err_Delta:.4f}")
print(f"  δR/R = √({rel_err_M0:.4f}² + {rel_err_Delta:.4f}²) = {rel_err_R:.4f}")
print(f"  δR = {R_FI:.3f} × {rel_err_R:.4f} = {delta_R:.3f}")

# Compare: error without M₀^SC systematic
delta_R_no_sys = M0_SC * Delta_err * eta_SU3
print(f"\n  (Without M₀^SC systematic: δR = {delta_R_no_sys:.3f})")

# Round
R_FI_rounded = round(R_FI, 2)
delta_R_rounded = round(delta_R + 0.005, 2)  # round up
print(f"\n  → R_cont^FI = {R_FI_rounded} ± {delta_R_rounded}")

# Tension with lattice
R_lat_val = 3.405
R_lat_err = 0.021
tension = abs(R_FI_rounded - R_lat_val) / delta_R_rounded
print(f"\n  Tension with lattice: |{R_FI_rounded} - {R_lat_val}|/{delta_R_rounded} = {tension:.2f}σ")

# c_FI computation
sigma_Lambda = 1.994
sigma_Lambda_err = 0.021

c_FI = R_FI_rounded * sigma_Lambda
print(f"\nc_FI = R × (√σ/Λ) = {R_FI_rounded} × {sigma_Lambda} = {c_FI:.4f}")

# Error propagation for c_FI
rel_err_c = np.sqrt((delta_R_rounded/R_FI_rounded)**2 + (sigma_Lambda_err/sigma_Lambda)**2)
delta_c = c_FI * rel_err_c
print(f"  δc/c = √[({delta_R_rounded}/{R_FI_rounded})² + ({sigma_Lambda_err}/{sigma_Lambda})²] = {rel_err_c:.4f}")
print(f"  δc = {c_FI:.4f} × {rel_err_c:.4f} = {delta_c:.3f}")

c_FI_rounded = round(c_FI, 2)
delta_c_rounded = round(delta_c + 0.005, 2)
print(f"\n  → c_FI = {c_FI_rounded} ± {delta_c_rounded}")

# c_lat for comparison
c_lat = R_lat_val * sigma_Lambda
c_lat_err = c_lat * np.sqrt((R_lat_err/R_lat_val)**2 + (sigma_Lambda_err/sigma_Lambda)**2)
print(f"  c_lat = {R_lat_val} × {sigma_Lambda} = {c_lat:.4f} ± {c_lat_err:.2f}")

tension_c = abs(c_FI_rounded - round(c_lat, 2)) / np.sqrt(delta_c_rounded**2 + c_lat_err**2)
print(f"  Tension: {tension_c:.2f}σ")

# Conservative lower bound at 3σ
R_low_3sigma = R_FI_rounded - 3 * delta_R_rounded
sigma_Lambda_low = sigma_Lambda - 3 * sigma_Lambda_err
c_low = R_low_3sigma * sigma_Lambda_low
print(f"\nConservative 3σ lower bound:")
print(f"  R_low = {R_FI_rounded} - 3×{delta_R_rounded} = {R_low_3sigma:.2f}")
print(f"  (√σ/Λ)_low = {sigma_Lambda} - 3×{sigma_Lambda_err} = {sigma_Lambda_low:.3f}")
print(f"  c_low = {R_low_3sigma:.2f} × {sigma_Lambda_low:.3f} = {c_low:.2f}")

# ============================================================
# What if we use purely framework-internal Δ (midpoint of Δ₁ and Δ₂)?
# ============================================================
print("\n" + "=" * 90)
print("Sensitivity analysis: purely framework-internal Δ (midpoint)")
print("=" * 90)

Delta_mid = (Delta_1 + Delta_2) / 2
R_mid = M0_SC * (1 + Delta_mid) * eta_SU3
print(f"Δ_mid = ({Delta_1:.4f} + {Delta_2:.4f})/2 = {Delta_mid:.4f}")
print(f"R_cont^FI(Δ_mid) = 2 × {1+Delta_mid:.4f} × 1.5 = {R_mid:.3f}")
tension_mid = abs(R_mid - R_lat_val) / delta_R_rounded
print(f"Tension: |{R_mid:.3f} - {R_lat_val}|/{delta_R_rounded} = {tension_mid:.2f}σ")

print("\n" + "=" * 90)
print("ALL DONE")
print("=" * 90)
