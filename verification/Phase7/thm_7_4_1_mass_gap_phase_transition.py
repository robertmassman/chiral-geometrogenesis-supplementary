#!/usr/bin/env python3
"""
Theorem 7.4.1: Mass Gap Phase Transition for FCC Lattice Gauge Theory
======================================================================

Computes and illustrates the confinement-deconfinement phase transition
encoded in the per-cell mass gap formula:

    mu(beta) = -3 ln(3) - 8 ln(u_3(beta))

where u_3(beta) = a_3(beta) / a_1(beta) is the normalized heat kernel
coefficient for the fundamental representation of SU(3).

Key Results:
    1. Numerical computation of u_3(beta) via Weyl integration over SU(3)
    2. Determination of critical coupling beta_c where mu(beta_c) = 0
    3. Demonstration of confinement (mu > 0) for beta < beta_c
    4. Demonstration of deconfinement (mu < 0) for beta > beta_c
    5. Physical interpretation of the ground state switching

Related Documents:
    - Statement: docs/proofs/Phase7/Theorem-7.4.1-Reflection-Positivity-FCC.md
    - Derivation: docs/proofs/Phase7/Theorem-7.4.1-Reflection-Positivity-FCC-Derivation.md
    - Applications: docs/proofs/Phase7/Theorem-7.4.1-Reflection-Positivity-FCC-Applications.md
    - Parent: Proposition-2.5.2c (Transfer Matrix for FCC Layers)

Verification Date: 2026-02-13
"""

import numpy as np
import json
import os
from datetime import datetime

try:
    from scipy.optimize import brentq
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyArrowPatch
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False

# =============================================================================
# OUTPUT DIRECTORIES
# =============================================================================

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BASE_DIR = os.path.dirname(SCRIPT_DIR)
PLOT_DIR = os.path.join(BASE_DIR, 'plots')
os.makedirs(PLOT_DIR, exist_ok=True)

# =============================================================================
# SU(3) HEAT KERNEL COMPUTATION VIA WEYL INTEGRATION
# =============================================================================

N_C = 3  # Number of colors


def su3_dim(p, q):
    """Dimension of SU(3) irrep with Dynkin labels (p, q)."""
    return (p + 1) * (q + 1) * (p + q + 2) // 2


def su3_casimir(p, q):
    """Quadratic Casimir C_2 for SU(3) irrep (p, q)."""
    return (p**2 + q**2 + p*q + 3*p + 3*q) / 3.0


def weyl_measure(theta1, theta2):
    """
    Weyl integration measure |Delta(theta)|^2 for SU(3).

    The Vandermonde factor for SU(3) maximal torus parametrized by
    diag(e^{i*theta1}, e^{i*theta2}, e^{-i*(theta1+theta2)}).
    """
    d12 = 2.0 * np.sin((theta1 - theta2) / 2.0)
    d13 = 2.0 * np.sin((2.0 * theta1 + theta2) / 2.0)
    d23 = 2.0 * np.sin((theta1 + 2.0 * theta2) / 2.0)
    return d12**2 * d13**2 * d23**2


def su3_boltzmann(theta1, theta2, beta):
    """
    Boltzmann weight exp(beta/3 * Re Tr U) for SU(3) Wilson action.

    For U = diag(e^{i*theta1}, e^{i*theta2}, e^{-i*(theta1+theta2)}):
        Re Tr U = cos(theta1) + cos(theta2) + cos(theta1 + theta2)
    """
    re_tr = np.cos(theta1) + np.cos(theta2) + np.cos(theta1 + theta2)
    return np.exp(beta / 3.0 * re_tr)


def su3_character(p, q, theta1, theta2):
    """
    Character chi_{(p,q)}(theta1, theta2) of SU(3) irrep via Weyl character formula.

    Uses the alternating sum over S_3 permutations applied to the
    highest weight shifted by the Weyl vector rho = (2,1,0).
    """
    z1 = np.exp(1j * theta1)
    z2 = np.exp(1j * theta2)
    z3 = np.exp(-1j * (theta1 + theta2))
    zs = [z1, z2, z3]

    # Shifted highest weight: lambda + rho
    lam_rho = [p + q + 2, q + 1, 0]
    rho = [2, 1, 0]

    # All permutations of S_3 with signs
    perms = [
        ([0, 1, 2], +1), ([0, 2, 1], -1), ([1, 0, 2], -1),
        ([1, 2, 0], +1), ([2, 0, 1], +1), ([2, 1, 0], -1),
    ]

    num = 0.0 + 0.0j
    den = 0.0 + 0.0j
    for perm, sign in perms:
        num += sign * zs[perm[0]]**lam_rho[0] * zs[perm[1]]**lam_rho[1] * zs[perm[2]]**lam_rho[2]
        den += sign * zs[perm[0]]**rho[0] * zs[perm[1]]**rho[1] * zs[perm[2]]**rho[2]

    if abs(den) < 1e-12:
        return complex(float(su3_dim(p, q)), 0.0)

    return num / den


def compute_a_R(p, q, beta, n_grid=300):
    """
    Compute heat kernel coefficient a_R(beta) via grid-based Weyl integration.

    a_R(beta) = (1/d_R) * int dU exp(beta/3 * Re Tr U) * chi_Rbar(U) / Vol

    where Vol = int dU exp(beta/3 * Re Tr U) is NOT divided out.
    Rather, the normalization is:

        a_R = int dU |Delta|^2 exp(beta/3 * Re Tr U) * chi_Rbar(U) / (24*pi^2 * d_R)

    This gives a_1(beta) = <1>_beta (partition function per unit volume),
    and u_R = a_R / a_1 = <chi_R>_beta / d_R.
    """
    d_R = su3_dim(p, q)
    p_conj, q_conj = q, p  # Conjugate rep for chi_bar

    theta1 = np.linspace(0, 2 * np.pi, n_grid, endpoint=False)
    theta2 = np.linspace(0, 2 * np.pi, n_grid, endpoint=False)
    T1, T2 = np.meshgrid(theta1, theta2)

    wm = weyl_measure(T1, T2)
    bw = su3_boltzmann(T1, T2, beta)

    # Character of conjugate representation
    chi = np.zeros_like(T1, dtype=complex)
    for i in range(n_grid):
        for j in range(n_grid):
            chi[i, j] = su3_character(p_conj, q_conj, T1[i, j], T2[i, j])

    integrand = wm * bw * chi
    dtheta = (2 * np.pi / n_grid)**2
    result = np.sum(integrand) * dtheta

    # Normalization: total volume of SU(3) in Weyl coordinates is 24*pi^2
    normalization = 24.0 * np.pi**2
    return (result / (normalization * d_R)).real


def compute_u3(beta, n_grid=300):
    """Compute normalized coefficient u_3(beta) = a_3(beta) / a_1(beta)."""
    a_1 = compute_a_R(0, 0, beta, n_grid=n_grid)
    a_3 = compute_a_R(1, 0, beta, n_grid=n_grid)
    if a_1 > 0:
        return a_3 / a_1
    return 0.0


def mass_gap_mu(beta, n_grid=300):
    """
    Per-cell intensive mass gap:
        mu(beta) = -3*ln(3) - 8*ln(u_3(beta))

    For N_s spatial cells per (111) layer:
        m_gap = N_s * mu(beta)
    """
    u3 = compute_u3(beta, n_grid=n_grid)
    if u3 > 0:
        return -3.0 * np.log(3) - 8.0 * np.log(u3)
    return np.inf


# =============================================================================
# ANALYTIC APPROXIMATIONS FOR COMPARISON
# =============================================================================

def u3_strong_coupling(beta):
    """
    Strong-coupling expansion of u_3(beta).

    Leading order: u_3 ~ beta/18
    Next-to-leading: u_3 ~ beta/18 * (1 + beta^2/108 + ...)

    This comes from expanding exp(beta/3 * Re Tr U) to first order in beta
    and using the orthogonality of SU(3) characters.
    """
    return (beta / 18.0) * (1.0 + beta**2 / 108.0)


def u3_weak_coupling(beta):
    """
    Weak-coupling expansion of u_3(beta).

    At large beta, all representations become equally weighted:
        u_3 ~ 1 - C_2(3)/(beta * d_adj) + ...
        u_3 ~ 1 - 4/(3*beta)

    where C_2(3) = 4/3 is the fundamental Casimir and d_adj = 8.
    """
    return 1.0 - 4.0 / (3.0 * beta)


def u3_interpolation(beta):
    """
    Pade-like interpolation between strong and weak coupling:
        u_3(beta) ~ (beta/18) / (1 + beta/18)

    This satisfies:
        beta -> 0: u_3 -> beta/18 (correct leading order)
        beta -> inf: u_3 -> 1 (correct limit)
    """
    x = beta / 18.0
    return x / (1.0 + x)


def mu_from_u3(u3):
    """Mass gap from given u_3 value."""
    if u3 > 0:
        return -3.0 * np.log(3) - 8.0 * np.log(u3)
    return np.inf


# =============================================================================
# CRITICAL COUPLING DETERMINATION
# =============================================================================

def find_beta_c_numerical(beta_low=0.5, beta_high=30.0, n_grid=300, tol=1e-6):
    """
    Find critical coupling beta_c where mu(beta_c) = 0.

    At mu = 0:  -3*ln(3) - 8*ln(u_3) = 0
    =>          ln(u_3) = -3*ln(3)/8
    =>          u_3 = 3^{-3/8}
    """
    u3_critical = 3.0**(-3.0/8.0)
    print(f"  Critical u_3 value: u_3(beta_c) = 3^(-3/8) = {u3_critical:.8f}")

    if HAS_SCIPY:
        def objective(beta):
            return compute_u3(beta, n_grid=n_grid) - u3_critical

        # Verify sign change
        f_low = objective(beta_low)
        f_high = objective(beta_high)
        print(f"  Objective at beta={beta_low}: {f_low:.6f} (should be < 0)")
        print(f"  Objective at beta={beta_high}: {f_high:.6f} (should be > 0)")

        if f_low < 0 and f_high > 0:
            beta_c = brentq(objective, beta_low, beta_high, xtol=tol)
            return beta_c
        else:
            print("  WARNING: No sign change detected, using bisection manually")

    # Manual bisection fallback
    for _ in range(60):
        beta_mid = (beta_low + beta_high) / 2
        u3_mid = compute_u3(beta_mid, n_grid=n_grid)
        if u3_mid < u3_critical:
            beta_low = beta_mid
        else:
            beta_high = beta_mid
        if (beta_high - beta_low) < tol:
            break

    return (beta_low + beta_high) / 2


def find_beta_c_from_interpolation():
    """
    Find beta_c from the Pade interpolation u_3 = (beta/18)/(1 + beta/18).

    Solving (beta/18)/(1 + beta/18) = 3^{-3/8}:
        beta/18 = 3^{-3/8} / (1 - 3^{-3/8})
        beta = 18 * 3^{-3/8} / (1 - 3^{-3/8})
    """
    u3c = 3.0**(-3.0/8.0)
    return 18.0 * u3c / (1.0 - u3c)


# =============================================================================
# ENERGY SPECTRUM AND GROUND STATE ANALYSIS
# =============================================================================

def compute_energy_spectrum(beta, N_s=1, n_reps=8, n_grid=300):
    """
    Compute energy spectrum E_R = -3*N_s*ln(d_R) - 8*N_s*ln(a_R).

    Returns dict with representation labels and energies.
    """
    reps = [
        ((0, 0), '1'),    # trivial
        ((1, 0), '3'),    # fundamental
        ((0, 1), '3bar'), # anti-fundamental
        ((1, 1), '8'),    # adjoint
        ((2, 0), '6'),    # symmetric
        ((0, 2), '6bar'), # anti-symmetric
        ((3, 0), '10'),   # decuplet
        ((2, 1), '15'),   # mixed
    ][:n_reps]

    a_1 = compute_a_R(0, 0, beta, n_grid=n_grid)
    energies = {}

    for (p, q), label in reps:
        d_R = su3_dim(p, q)
        a_R = compute_a_R(p, q, beta, n_grid=n_grid)
        if a_R > 0:
            E_R = -3.0 * N_s * np.log(d_R) - 8.0 * N_s * np.log(a_R)
        else:
            E_R = np.inf
        energies[label] = {
            'pq': (p, q), 'd_R': d_R, 'a_R': a_R,
            'E_R': E_R, 'u_R': a_R / a_1 if a_1 > 0 else 0.0
        }

    return energies


# =============================================================================
# PHYSICAL MASS GAP (ALWAYS NON-NEGATIVE)
# =============================================================================

def physical_mass_gap(beta, N_s=1, n_grid=300):
    """
    The PHYSICAL mass gap is always E_first_excited - E_ground >= 0.

    Below beta_c: ground = R=1, first excited = R=3
        => m_gap = E_3 - E_1 = N_s * mu(beta) > 0

    Above beta_c: ground = R=3, first excited = R=1
        => m_gap = E_1 - E_3 = -N_s * mu(beta) > 0

    At beta_c: m_gap = 0 (level crossing)
    """
    spectrum = compute_energy_spectrum(beta, N_s=N_s, n_grid=n_grid)
    E_1 = spectrum['1']['E_R']
    E_3 = spectrum['3']['E_R']

    # Ground state is whichever has lower energy
    if E_1 <= E_3:
        ground = '1'
        excited = '3'
        m_gap = E_3 - E_1
    else:
        ground = '3'
        excited = '1'
        m_gap = E_1 - E_3

    return m_gap, ground, excited


# =============================================================================
# MAIN COMPUTATION
# =============================================================================

def main():
    print("=" * 72)
    print("THEOREM 7.4.1: MASS GAP PHASE TRANSITION FOR FCC LATTICE")
    print("=" * 72)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    # =========================================================================
    # PART 1: Compute u_3(beta) over a range of beta
    # =========================================================================

    print("PART 1: Normalized heat kernel coefficient u_3(beta)")
    print("-" * 55)

    n_grid = 300  # Grid resolution for Weyl integration

    # Fine grid for smooth curves
    betas_fine = np.concatenate([
        np.linspace(0.2, 2.0, 20),
        np.linspace(2.0, 8.0, 30),
        np.linspace(8.0, 15.0, 20),
        np.linspace(15.0, 30.0, 15),
    ])
    betas_fine = np.unique(betas_fine)

    u3_values = []
    mu_values = []
    print(f"\n  Computing u_3(beta) for {len(betas_fine)} beta values "
          f"(n_grid={n_grid})...")
    print(f"  {'beta':>8s}  {'u_3(beta)':>12s}  {'mu(beta)':>12s}  {'Phase':>15s}")
    print(f"  {'----':>8s}  {'----------':>12s}  {'--------':>12s}  {'-----':>15s}")

    for i, beta in enumerate(betas_fine):
        u3 = compute_u3(beta, n_grid=n_grid)
        u3_values.append(u3)
        mu = mu_from_u3(u3)
        mu_values.append(mu)
        if i % 10 == 0 or abs(mu) < 2.0:
            phase = "CONFINED" if mu > 0 else "DECONFINED"
            print(f"  {beta:8.3f}  {u3:12.8f}  {mu:12.6f}  {phase:>15s}")

    u3_values = np.array(u3_values)
    mu_values = np.array(mu_values)

    # =========================================================================
    # PART 2: Critical coupling beta_c
    # =========================================================================

    print(f"\n\nPART 2: Critical Coupling beta_c")
    print("-" * 55)

    u3_critical = 3.0**(-3.0/8.0)
    print(f"\n  Mass gap formula: mu(beta) = -3*ln(3) - 8*ln(u_3(beta))")
    print(f"  Setting mu = 0:  u_3(beta_c) = 3^(-3/8) = {u3_critical:.10f}")
    print(f"  Equivalently:    -3*ln(3) = {-3*np.log(3):.10f}")

    beta_c_numerical = find_beta_c_numerical(
        beta_low=1.0, beta_high=25.0, n_grid=n_grid
    )

    beta_c_interpolation = find_beta_c_from_interpolation()

    # Verify numerically
    u3_at_bc = compute_u3(beta_c_numerical, n_grid=n_grid)
    mu_at_bc = mu_from_u3(u3_at_bc)

    print(f"\n  --- Results ---")
    print(f"  Numerical beta_c         = {beta_c_numerical:.6f}")
    print(f"  u_3(beta_c)              = {u3_at_bc:.10f}")
    print(f"  Target u_3               = {u3_critical:.10f}")
    print(f"  mu(beta_c)               = {mu_at_bc:.2e}  (should be ~0)")
    print(f"  Pade interpolation beta_c = {beta_c_interpolation:.6f}")
    print(f"  Relative discrepancy      = "
          f"{abs(beta_c_numerical - beta_c_interpolation)/beta_c_numerical:.4f}")

    # Physical interpretation of beta_c in terms of coupling g^2
    g2_at_bc = 6.0 / beta_c_numerical
    print(f"\n  Physical coupling at transition:")
    print(f"  beta = 6/g^2  =>  g^2(beta_c) = {g2_at_bc:.6f}")
    print(f"  alpha_s = g^2/(4*pi) = {g2_at_bc/(4*np.pi):.6f}")

    # =========================================================================
    # PART 3: Confinement vs deconfinement demonstration
    # =========================================================================

    print(f"\n\nPART 3: Confinement vs Deconfinement")
    print("-" * 55)

    test_betas = [0.5, 1.0, 2.0, 5.0, beta_c_numerical, 10.0, 15.0, 20.0, 25.0]

    print(f"\n  {'beta':>8s}  {'u_3':>10s}  {'mu':>10s}  {'m_phys':>10s}  "
          f"{'Ground':>8s}  {'Phase':>14s}")
    print(f"  {'----':>8s}  {'---':>10s}  {'--':>10s}  {'------':>10s}  "
          f"{'------':>8s}  {'-----':>14s}")

    for beta in test_betas:
        u3 = compute_u3(beta, n_grid=n_grid)
        mu = mu_from_u3(u3)
        m_phys, ground, excited = physical_mass_gap(beta, N_s=1, n_grid=n_grid)

        if abs(beta - beta_c_numerical) < 0.1:
            phase = "CRITICAL"
        elif mu > 0:
            phase = "CONFINED"
        else:
            phase = "DECONFINED"

        print(f"  {beta:8.3f}  {u3:10.6f}  {mu:10.4f}  {m_phys:10.4f}  "
              f"R={ground:>5s}  {phase:>14s}")

    # =========================================================================
    # PART 4: Energy spectrum at selected beta values
    # =========================================================================

    print(f"\n\nPART 4: Energy Spectrum at Selected beta Values")
    print("-" * 55)

    for beta_show in [1.0, beta_c_numerical, 20.0]:
        phase_label = ("CONFINED" if beta_show < beta_c_numerical
                       else "CRITICAL" if abs(beta_show - beta_c_numerical) < 0.1
                       else "DECONFINED")
        print(f"\n  beta = {beta_show:.3f}  ({phase_label})")
        print(f"  {'Rep':>6s}  {'d_R':>4s}  {'a_R':>12s}  {'u_R':>10s}  {'E_R':>10s}")
        print(f"  {'---':>6s}  {'---':>4s}  {'---':>12s}  {'---':>10s}  {'---':>10s}")

        spectrum = compute_energy_spectrum(beta_show, N_s=1, n_grid=n_grid)
        E_min = min(s['E_R'] for s in spectrum.values() if np.isfinite(s['E_R']))

        for label in ['1', '3', '3bar', '8', '6', '6bar', '10', '15']:
            if label in spectrum:
                s = spectrum[label]
                rel_E = s['E_R'] - E_min
                print(f"  {label:>6s}  {s['d_R']:4d}  {s['a_R']:12.8f}  "
                      f"{s['u_R']:10.6f}  {s['E_R']:10.4f}  (gap: {rel_E:.4f})")

    # =========================================================================
    # PART 5: Comparison with analytic approximations
    # =========================================================================

    print(f"\n\nPART 5: Comparison with Analytic Approximations")
    print("-" * 55)

    print(f"\n  {'beta':>8s}  {'u3_exact':>12s}  {'u3_strong':>12s}  "
          f"{'u3_weak':>12s}  {'u3_pade':>12s}")
    print(f"  {'----':>8s}  {'--------':>12s}  {'---------':>12s}  "
          f"{'-------':>12s}  {'-------':>12s}")

    compare_betas = [0.5, 1.0, 2.0, 3.0, 5.0, 8.0, 10.0, 15.0, 20.0, 25.0]
    for beta in compare_betas:
        u3_exact = compute_u3(beta, n_grid=n_grid)
        u3_sc = u3_strong_coupling(beta)
        u3_wc = u3_weak_coupling(beta)
        u3_pad = u3_interpolation(beta)
        print(f"  {beta:8.2f}  {u3_exact:12.8f}  {u3_sc:12.8f}  "
              f"{u3_wc:12.8f}  {u3_pad:12.8f}")

    # =========================================================================
    # PART 6: Physical interpretation
    # =========================================================================

    print(f"\n\nPART 6: Physical Interpretation")
    print("-" * 55)
    print(f"""
  The mass gap mu(beta) measures the energy difference between the first
  excited state (fundamental representation R=3) and the ground state
  (trivial representation R=1) of the FCC lattice transfer matrix.

  CONFINEMENT PHASE (beta < beta_c = {beta_c_numerical:.3f}):
    - Ground state: R = 1 (color singlet)
    - First excited: R = 3 (color triplet)
    - mu > 0: color-charged states cost energy => CONFINEMENT
    - At beta -> 0 (strong coupling): mu -> +inf (maximum confinement)
    - Physical: only color-neutral (singlet) excitations propagate cheaply

  DECONFINEMENT PHASE (beta > beta_c):
    - Naive formula gives mu < 0, meaning lambda_3 > lambda_1
    - R = 3 eigenvalue exceeds R = 1 eigenvalue
    - The "ground state" switches from R=1 to R=3
    - Physical: color-charged excitations become energetically favorable
    - This signals the DECONFINEMENT transition

  PHYSICAL MASS GAP (always >= 0):
    The physical mass gap is ALWAYS m_phys = |E_excited - E_ground| >= 0.
    Below beta_c: m_phys = E_3 - E_1 = +mu > 0
    Above beta_c: m_phys = E_1 - E_3 = -mu > 0
    At beta_c: m_phys = 0 (level crossing, phase transition)

  WHY THE GROUND STATE SWITCHES:
    The eigenvalue is lambda_R = d_R^(3*N_s) * a_R^(8*N_s).
    - d_1 = 1, d_3 = 3: the fundamental has higher degeneracy
    - a_1 > a_3 always, but d_3 > d_1 compensates at weak coupling
    - At large beta, a_3 -> a_1 so d_3^3 * a_3^8 > d_1^3 * a_1^8
    - The entropy factor d_R^(3*N_s) overwhelms the energy factor a_R^(8*N_s)
    - This is a lattice artifact of the strong-coupling expansion framework

  RELATION TO CONTINUUM QCD:
    In continuum QCD, confinement persists at all couplings.
    The lattice deconfinement transition at beta_c ~ {beta_c_numerical:.1f} is
    understood as the bulk phase transition of the lattice theory, which must
    be carefully handled when taking the continuum limit (beta -> infinity).
    The physically relevant regime for confinement is beta < beta_c.
""")

    # =========================================================================
    # PART 7: N_s scaling
    # =========================================================================

    print(f"\nPART 7: Scaling with Spatial Volume N_s")
    print("-" * 55)

    print(f"\n  For N_s cells per (111) layer:")
    print(f"  m_gap(N_s) = N_s * mu(beta)")
    print(f"  => Mass gap scales LINEARLY with spatial volume")
    print(f"  => Intensive (per-cell) gap mu(beta) is the fundamental quantity")
    print()

    for N_s in [1, 2, 4, 8]:
        for beta in [2.0, 5.0, beta_c_numerical]:
            u3 = compute_u3(beta, n_grid=n_grid)
            mu = mu_from_u3(u3)
            m_total = N_s * mu
            phase = "CRIT" if abs(beta - beta_c_numerical) < 0.1 else (
                "CONF" if mu > 0 else "DECONF")
            print(f"  N_s={N_s:2d}, beta={beta:6.2f}: "
                  f"mu={mu:8.4f}, m_gap(N_s)={m_total:10.4f}  [{phase}]")

    # =========================================================================
    # PLOTTING
    # =========================================================================

    if HAS_MATPLOTLIB:
        create_plots(betas_fine, u3_values, mu_values, beta_c_numerical, n_grid)

    # =========================================================================
    # SAVE RESULTS
    # =========================================================================

    results = {
        "theorem": "7.4.1",
        "title": "Mass Gap Phase Transition for FCC Lattice",
        "date": datetime.now().isoformat(),
        "parameters": {
            "n_grid": n_grid,
            "N_c": N_C,
        },
        "critical_values": {
            "u3_critical": float(u3_critical),
            "beta_c_numerical": float(beta_c_numerical),
            "beta_c_pade": float(beta_c_interpolation),
            "mu_at_beta_c": float(mu_at_bc),
            "g_squared_at_beta_c": float(g2_at_bc),
            "alpha_s_at_beta_c": float(g2_at_bc / (4 * np.pi)),
        },
        "mass_gap_formula": "mu(beta) = -3*ln(3) - 8*ln(u_3(beta))",
        "u3_definition": "u_3 = a_3(beta) / a_1(beta)",
        "beta_values": betas_fine.tolist(),
        "u3_values": u3_values.tolist(),
        "mu_values": mu_values.tolist(),
        "physical_interpretation": {
            "confined": "beta < beta_c: R=1 ground state, mu > 0",
            "deconfined": "beta > beta_c: R=3 ground state, mu < 0",
            "critical": "beta = beta_c: level crossing, mu = 0",
        },
    }

    output_path = os.path.join(SCRIPT_DIR, 'thm_7_4_1_mass_gap_results.json')
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n  Results saved to: {output_path}")

    print(f"\n{'=' * 72}")
    print("SUMMARY")
    print(f"{'=' * 72}")
    print(f"  beta_c (numerical)  = {beta_c_numerical:.6f}")
    print(f"  u_3(beta_c)         = {u3_at_bc:.10f}")
    print(f"  u_3 critical        = {u3_critical:.10f}")
    print(f"  g^2 at transition   = {g2_at_bc:.6f}")
    print(f"  alpha_s at trans.   = {g2_at_bc/(4*np.pi):.6f}")
    print(f"  Confined phase:       beta < {beta_c_numerical:.2f}  (mu > 0)")
    print(f"  Deconfined phase:     beta > {beta_c_numerical:.2f}  (mu < 0)")
    print(f"  Physical mass gap:    ALWAYS >= 0 (|mu| at level crossing)")
    print(f"{'=' * 72}")

    return True


# =============================================================================
# PLOTTING
# =============================================================================

def create_plots(betas, u3_vals, mu_vals, beta_c, n_grid):
    """Create comprehensive visualization of the mass gap phase transition."""

    u3_critical = 3.0**(-3.0/8.0)

    # ---- Figure 1: Three-panel overview ----
    fig, axes = plt.subplots(2, 2, figsize=(14, 11))
    fig.suptitle(
        'Theorem 7.4.1: Mass Gap Phase Transition on FCC Lattice\n'
        r'$\mu(\beta) = -3\ln 3 - 8\ln u_3(\beta)$',
        fontsize=14, fontweight='bold'
    )

    # Panel (a): u_3(beta) vs beta
    ax = axes[0, 0]
    ax.plot(betas, u3_vals, 'b-', linewidth=2, label=r'$u_3(\beta)$ (numerical)')

    # Analytic approximations
    betas_sc = betas[betas < 4]
    betas_wc = betas[betas > 6]
    ax.plot(betas_sc, [u3_strong_coupling(b) for b in betas_sc],
            'r--', linewidth=1.5, alpha=0.7, label=r'Strong coupling: $\beta/18$')
    ax.plot(betas_wc, [u3_weak_coupling(b) for b in betas_wc],
            'g--', linewidth=1.5, alpha=0.7, label=r'Weak coupling: $1 - 4/(3\beta)$')
    ax.plot(betas, [u3_interpolation(b) for b in betas],
            'k:', linewidth=1.5, alpha=0.5, label=r'Pad$\acute{e}$: $(\beta/18)/(1+\beta/18)$')

    # Critical point
    ax.axhline(y=u3_critical, color='gray', linestyle=':', alpha=0.5)
    ax.axvline(x=beta_c, color='gray', linestyle=':', alpha=0.5)
    ax.plot(beta_c, u3_critical, 'ro', markersize=10, zorder=5,
            label=rf'$\beta_c = {beta_c:.2f}$')

    ax.set_xlabel(r'$\beta = 6/g^2$', fontsize=12)
    ax.set_ylabel(r'$u_3(\beta) = a_3/a_1$', fontsize=12)
    ax.set_title(r'(a) Normalized Heat Kernel Coefficient $u_3(\beta)$', fontsize=11)
    ax.legend(fontsize=9, loc='lower right')
    ax.set_xlim([0, 30])
    ax.set_ylim([0, 1.05])
    ax.grid(True, alpha=0.3)

    # Panel (b): mu(beta) - the mass gap
    ax = axes[0, 1]
    ax.plot(betas, mu_vals, 'b-', linewidth=2.5)
    ax.axhline(y=0, color='k', linewidth=0.8)
    ax.axvline(x=beta_c, color='gray', linestyle=':', alpha=0.5)

    # Fill regions
    conf_mask = mu_vals > 0
    deconf_mask = mu_vals < 0
    ax.fill_between(betas, mu_vals, 0, where=conf_mask,
                     alpha=0.15, color='blue', label='Confined (R=1 ground)')
    ax.fill_between(betas, mu_vals, 0, where=deconf_mask,
                     alpha=0.15, color='red', label='Deconfined (R=3 ground)')

    ax.plot(beta_c, 0, 'ro', markersize=10, zorder=5,
            label=rf'$\beta_c = {beta_c:.2f}$')

    # Asymptotic value
    ax.axhline(y=-3*np.log(3), color='red', linestyle='--', alpha=0.4,
               label=rf'$\mu \to -3\ln 3 \approx {-3*np.log(3):.2f}$')

    ax.set_xlabel(r'$\beta = 6/g^2$', fontsize=12)
    ax.set_ylabel(r'$\mu(\beta)$ (lattice units per cell)', fontsize=12)
    ax.set_title(r'(b) Per-Cell Mass Gap $\mu(\beta)$', fontsize=11)
    ax.legend(fontsize=9, loc='upper right')
    ax.set_xlim([0, 30])
    ax.set_ylim([-4, max(mu_vals[np.isfinite(mu_vals)]) * 1.1])
    ax.grid(True, alpha=0.3)

    # Panel (c): Physical mass gap (always non-negative)
    ax = axes[1, 0]
    physical_gap = np.abs(mu_vals)
    ax.plot(betas, physical_gap, 'purple', linewidth=2.5,
            label=r'$m_{\rm phys} = |E_{\rm excited} - E_{\rm ground}|$')
    ax.axvline(x=beta_c, color='gray', linestyle=':', alpha=0.5)
    ax.plot(beta_c, 0, 'ro', markersize=10, zorder=5,
            label=rf'$\beta_c = {beta_c:.2f}$')

    # Annotations
    ax.annotate('Confined\n(R=1 ground)', xy=(beta_c/3, 8),
                fontsize=10, ha='center', color='blue',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='lightskyblue', alpha=0.5))
    ax.annotate('Deconfined\n(R=3 ground)', xy=(beta_c + 7, 2.0),
                fontsize=10, ha='center', color='red',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='lightsalmon', alpha=0.5))

    ax.set_xlabel(r'$\beta = 6/g^2$', fontsize=12)
    ax.set_ylabel(r'$m_{\rm phys}$ (lattice units per cell)', fontsize=12)
    ax.set_title(r'(c) Physical Mass Gap (always $\geq 0$)', fontsize=11)
    ax.legend(fontsize=9, loc='upper right')
    ax.set_xlim([0, 30])
    ax.set_ylim(bottom=-0.5)
    ax.grid(True, alpha=0.3)

    # Panel (d): Energy levels vs beta
    ax = axes[1, 1]

    # Compute E_1 and E_3 vs beta
    betas_spectrum = np.linspace(0.5, 30, 60)
    E1_vals = []
    E3_vals = []
    E8_vals = []

    for beta in betas_spectrum:
        a_1 = compute_a_R(0, 0, beta, n_grid=200)
        a_3 = compute_a_R(1, 0, beta, n_grid=200)
        a_8 = compute_a_R(1, 1, beta, n_grid=200)

        E_1 = -8.0 * np.log(a_1) if a_1 > 0 else np.inf
        E_3 = -3.0 * np.log(3) - 8.0 * np.log(a_3) if a_3 > 0 else np.inf
        E_8 = -3.0 * np.log(8) - 8.0 * np.log(a_8) if a_8 > 0 else np.inf
        E1_vals.append(E_1)
        E3_vals.append(E_3)
        E8_vals.append(E_8)

    E1_vals = np.array(E1_vals)
    E3_vals = np.array(E3_vals)
    E8_vals = np.array(E8_vals)

    ax.plot(betas_spectrum, E1_vals, 'b-', linewidth=2, label=r'$E_1$ (trivial)')
    ax.plot(betas_spectrum, E3_vals, 'r-', linewidth=2, label=r'$E_3$ (fundamental)')
    ax.plot(betas_spectrum, E8_vals, 'g--', linewidth=1.5, alpha=0.7,
            label=r'$E_8$ (adjoint)')
    ax.axvline(x=beta_c, color='gray', linestyle=':', alpha=0.5,
               label=rf'$\beta_c = {beta_c:.2f}$')

    # Mark the crossing
    # Find where E_1 and E_3 cross
    diff = E1_vals - E3_vals
    for i in range(len(diff) - 1):
        if diff[i] * diff[i+1] < 0:
            # Linear interpolation for crossing point
            frac = -diff[i] / (diff[i+1] - diff[i])
            beta_cross = betas_spectrum[i] + frac * (betas_spectrum[i+1] - betas_spectrum[i])
            E_cross = E1_vals[i] + frac * (E1_vals[i+1] - E1_vals[i])
            ax.plot(beta_cross, E_cross, 'ko', markersize=10, zorder=5)
            ax.annotate('Level crossing', xy=(beta_cross, E_cross),
                        xytext=(beta_cross + 3, E_cross + 2),
                        fontsize=9, ha='left',
                        arrowprops=dict(arrowstyle='->', color='black'))
            break

    ax.set_xlabel(r'$\beta = 6/g^2$', fontsize=12)
    ax.set_ylabel(r'$E_R = -3N_s\ln d_R - 8N_s\ln a_R$', fontsize=12)
    ax.set_title(r'(d) Energy Level Crossing ($N_s = 1$)', fontsize=11)
    ax.legend(fontsize=9, loc='upper right')
    ax.set_xlim([0, 30])

    # Set y-limits to avoid extreme values
    finite_mask = np.isfinite(E1_vals) & np.isfinite(E3_vals) & np.isfinite(E8_vals)
    if np.any(finite_mask):
        all_E = np.concatenate([E1_vals[finite_mask], E3_vals[finite_mask],
                                E8_vals[finite_mask]])
        y_margin = 0.1 * (np.max(all_E) - np.min(all_E))
        ax.set_ylim([np.min(all_E) - y_margin, np.max(all_E) + y_margin])

    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    plot_path = os.path.join(PLOT_DIR, 'thm_7_4_1_mass_gap_phase_transition_detailed.png')
    fig.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\n  Plot saved to: {plot_path}")
    plt.close(fig)

    # ---- Figure 2: Strong-coupling expansion accuracy ----
    fig2, ax2 = plt.subplots(1, 1, figsize=(10, 6))
    fig2.suptitle('Heat Kernel Approximation Quality', fontsize=13, fontweight='bold')

    u3_exact = u3_vals
    u3_sc = np.array([u3_strong_coupling(b) for b in betas])
    u3_wc = np.array([u3_weak_coupling(b) for b in betas])
    u3_pad = np.array([u3_interpolation(b) for b in betas])

    # Relative errors
    err_sc = np.abs(u3_sc - u3_exact) / np.maximum(u3_exact, 1e-30)
    err_wc = np.abs(u3_wc - u3_exact) / np.maximum(u3_exact, 1e-30)
    err_pad = np.abs(u3_pad - u3_exact) / np.maximum(u3_exact, 1e-30)

    ax2.semilogy(betas, err_sc, 'r-', linewidth=1.5,
                 label='Strong coupling rel. error')
    ax2.semilogy(betas[betas > 2], err_wc[betas > 2], 'g-', linewidth=1.5,
                 label='Weak coupling rel. error')
    ax2.semilogy(betas, err_pad, 'k--', linewidth=1.5,
                 label=r'Pad$\acute{e}$ rel. error')
    ax2.axvline(x=beta_c, color='gray', linestyle=':', alpha=0.5,
                label=rf'$\beta_c = {beta_c:.2f}$')
    ax2.axhline(y=0.01, color='orange', linestyle=':', alpha=0.5,
                label='1% error')

    ax2.set_xlabel(r'$\beta = 6/g^2$', fontsize=12)
    ax2.set_ylabel('Relative error in $u_3$', fontsize=12)
    ax2.legend(fontsize=10)
    ax2.set_xlim([0.5, 30])
    ax2.set_ylim([1e-4, 10])
    ax2.grid(True, alpha=0.3, which='both')

    plot_path2 = os.path.join(PLOT_DIR, 'thm_7_4_1_u3_approximation_quality.png')
    fig2.savefig(plot_path2, dpi=150, bbox_inches='tight')
    print(f"  Plot saved to: {plot_path2}")
    plt.close(fig2)


if __name__ == '__main__':
    main()
