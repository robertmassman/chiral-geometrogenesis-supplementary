"""
Analytical Formulas for Lattice Gauge Theory
==============================================

Provides character expansion (single-plaquette) predictions for
comparison with Monte Carlo measurements on FCC, D4, and Z^4 lattices.
Ported from prop_7_4_4_scaling_window.py.

The heat kernel ratio u_3(beta) = a_{fund}(beta) / a_{trivial}(beta)
controls the single-plaquette average. The single-plaquette prediction
is exact only at strong coupling (small beta). At larger beta,
inter-plaquette correlations cause the true MC plaquette to exceed
u_3(beta).

Key formulas (single-plaquette / strong-coupling approximation):
    u_3(beta)           - Fundamental/trivial heat kernel ratio
    <Plaquette>(beta)   - Single-plaquette prediction = u_3
    mu(beta)            - Mass gap = -3*ln(3) - 8*ln(u_3) [FCC only]
    sigma(beta)         - String tension = -ln(u_3)
    beta_c              - Critical coupling where u_3 = 3^(-3/8)

Z^4-specific strong/weak coupling expansions:
    z4_strong_coupling_plaquette - beta/18 + O(beta^2)
    z4_weak_coupling_plaquette   - 1 - 8/(3*beta) + O(1/beta^2)
"""

import numpy as np

# =============================================================================
# SU(3) representation data
# =============================================================================

def su3_dim(p, q):
    """Dimension of SU(3) irrep with Dynkin labels (p, q)."""
    return (p + 1) * (q + 1) * (p + q + 2) // 2


def su3_casimir(p, q):
    """Quadratic Casimir for SU(3) irrep (p, q)."""
    return (p**2 + q**2 + p * q + 3 * p + 3 * q) / 3.0


# =============================================================================
# Weyl integration for heat kernel coefficients
# =============================================================================

def weyl_measure(theta1, theta2):
    """Weyl integration measure |Delta(theta)|^2 for SU(3)."""
    d12 = 2.0 * np.sin((theta1 - theta2) / 2.0)
    d13 = 2.0 * np.sin((2.0 * theta1 + theta2) / 2.0)
    d23 = 2.0 * np.sin((theta1 + 2.0 * theta2) / 2.0)
    return d12**2 * d13**2 * d23**2


def su3_boltzmann(theta1, theta2, beta):
    """Boltzmann weight exp(beta/3 * Re Tr U)."""
    re_tr = np.cos(theta1) + np.cos(theta2) + np.cos(theta1 + theta2)
    return np.exp(beta / 3.0 * re_tr)


def su3_character(p, q, theta1, theta2):
    """Character chi_{(p,q)} via Weyl character formula."""
    z1 = np.exp(1j * theta1)
    z2 = np.exp(1j * theta2)
    z3 = np.exp(-1j * (theta1 + theta2))
    zs = [z1, z2, z3]

    lam_rho = [p + q + 2, q + 1, 0]
    perms = [
        ([0, 1, 2], +1), ([0, 2, 1], -1), ([1, 0, 2], -1),
        ([1, 2, 0], +1), ([2, 0, 1], +1), ([2, 1, 0], -1),
    ]

    num = 0.0 + 0.0j
    den = 0.0 + 0.0j
    for perm, sign in perms:
        num += sign * zs[perm[0]]**lam_rho[0] * zs[perm[1]]**lam_rho[1] * zs[perm[2]]**lam_rho[2]
        den += sign * zs[perm[0]]**2 * zs[perm[1]]**1 * zs[perm[2]]**0

    if abs(den) < 1e-12:
        return complex(float(su3_dim(p, q)), 0.0)
    return num / den


def compute_a_R(p, q, beta, n_grid=200):
    """Compute heat kernel coefficient a_R(beta) via grid integration.

    a_R(beta) = (1/d_R) * integral dmu(U) exp(beta/3 Re Tr U) chi_R*(U)
    """
    d_R = su3_dim(p, q)
    p_conj, q_conj = q, p

    theta1 = np.linspace(0, 2 * np.pi, n_grid, endpoint=False)
    theta2 = np.linspace(0, 2 * np.pi, n_grid, endpoint=False)
    T1, T2 = np.meshgrid(theta1, theta2)

    wm = weyl_measure(T1, T2)
    bw = su3_boltzmann(T1, T2, beta)

    chi = np.zeros_like(T1, dtype=complex)
    for i in range(n_grid):
        for j in range(n_grid):
            chi[i, j] = su3_character(p_conj, q_conj, T1[i, j], T2[i, j])

    integrand = wm * bw * chi
    dtheta = (2 * np.pi / n_grid) ** 2
    result = np.sum(integrand) * dtheta

    normalization = 24.0 * np.pi ** 2
    return (result / (normalization * d_R)).real


# =============================================================================
# Core exact quantities
# =============================================================================

def compute_u3(beta, n_grid=200):
    """Compute u_3(beta) = a_fund / a_trivial.

    This is the fundamental ratio controlling all FCC lattice observables.
    """
    a_1 = compute_a_R(0, 0, beta, n_grid=n_grid)
    a_3 = compute_a_R(1, 0, beta, n_grid=n_grid)
    if a_1 > 0:
        return a_3 / a_1
    return 0.0


def exact_plaquette(beta, n_grid=200):
    """Single-plaquette prediction for the average plaquette.

    <P> = u_3(beta). Exact at strong coupling; approximate for the
    full 3D FCC lattice at intermediate/weak coupling.
    """
    return compute_u3(beta, n_grid=n_grid)


def exact_mass_gap(beta, n_grid=200, lattice_type='fcc'):
    """Exact mass gap from strong-coupling expansion.

    For FCC (D3): mu(beta) = -3*ln(3) - 8*ln(u_3).
    For D4: formula TBD (returns None).

    Parameters:
        lattice_type: 'fcc' or 'd4'
    """
    if lattice_type == 'd4':
        return None
    u3 = compute_u3(beta, n_grid=n_grid)
    if u3 > 0:
        return -3.0 * np.log(3) - 8.0 * np.log(u3)
    return np.inf


def exact_string_tension(beta, n_grid=200):
    """Exact lattice string tension sigma = -ln(u_3).

    In lattice units. Vanishes as beta -> infinity.
    """
    u3 = compute_u3(beta, n_grid=n_grid)
    if 0 < u3 < 1:
        return -np.log(u3)
    return np.inf


def exact_critical_coupling(n_grid=200, tol=0.01):
    """Find beta_c where u_3 = 3^(-3/8) (mass gap vanishes).

    Uses binary search.

    Returns: beta_c
    """
    u3_target = 3.0 ** (-3.0 / 8.0)

    beta_low, beta_high = 5.0, 15.0
    for _ in range(60):
        beta_mid = (beta_low + beta_high) / 2
        u3_mid = compute_u3(beta_mid, n_grid=n_grid)
        if u3_mid < u3_target:
            beta_low = beta_mid
        else:
            beta_high = beta_mid

    return (beta_low + beta_high) / 2


def exact_quantities_at_beta(beta, n_grid=200, lattice_type='fcc'):
    """Compute all exact quantities at a given beta.

    Parameters:
        lattice_type: 'fcc' or 'd4'. u3 and plaquette are
            lattice-independent (single-plaquette prediction).
            Mass gap formula is FCC-specific; returns None for D4.

    Returns dict with: u3, plaquette, mass_gap, string_tension.
    """
    u3 = compute_u3(beta, n_grid=n_grid)
    plaq = u3
    if lattice_type == 'd4':
        mu = None
        sigma = -np.log(u3) if 0 < u3 < 1 else np.inf
    elif u3 > 0:
        mu = -3.0 * np.log(3) - 8.0 * np.log(u3)
        sigma = -np.log(u3) if u3 < 1 else 0.0
    else:
        mu = np.inf
        sigma = np.inf

    return {
        'beta': beta,
        'u3': u3,
        'plaquette': plaq,
        'mass_gap': mu,
        'string_tension': sigma,
    }


# =============================================================================
# Scan helper
# =============================================================================

def scan_beta_range(beta_min=1.0, beta_max=10.0, n_beta=15, n_grid=150):
    """Compute exact quantities across a range of beta values.

    Returns list of dicts, one per beta value.
    """
    betas = np.linspace(beta_min, beta_max, n_beta)
    results = []
    for beta in betas:
        r = exact_quantities_at_beta(beta, n_grid=n_grid)
        results.append(r)
    return results


# =============================================================================
# Z^4 (standard hypercubic) lattice formulas
# =============================================================================

def z4_strong_coupling_plaquette(beta):
    """Strong-coupling expansion for Z^4 SU(3) average plaquette.

    At leading order: <P> = beta / (2 * N_c^2) = beta / 18.
    This is exact in the beta -> 0 limit (single-plaquette integral
    for square plaquettes).
    """
    return beta / 18.0


def z4_weak_coupling_plaquette(beta):
    """Weak-coupling expansion for Z^4 SU(3) average plaquette.

    At leading order: <P> = 1 - (N_c^2 - 1) / (N_c * beta) * d
    where d = dimension = 4, giving coefficient 8/(3*beta) for SU(3) in 4D.

    More precisely: <P> = 1 - 8/(3*beta) + O(1/beta^2).
    """
    if beta <= 0:
        return 0.0
    return 1.0 - 8.0 / (3.0 * beta)


def z4_single_plaquette(beta, n_grid=200):
    """Single-plaquette prediction for Z^4 lattice.

    Same as u_3(beta) — the single-plaquette character expansion is
    lattice-geometry-independent (depends only on the gauge group).
    """
    return compute_u3(beta, n_grid=n_grid)


def exact_quantities_at_beta_z4(beta, n_grid=200):
    """Compute all exact/reference quantities for Z^4 at a given beta.

    Returns dict with: u3, plaquette (single-plaq), strong_coupling,
    weak_coupling, string_tension.
    """
    u3 = compute_u3(beta, n_grid=n_grid)
    sigma = -np.log(u3) if 0 < u3 < 1 else np.inf

    return {
        'beta': beta,
        'u3': u3,
        'plaquette': u3,  # single-plaquette prediction
        'strong_coupling': z4_strong_coupling_plaquette(beta),
        'weak_coupling': z4_weak_coupling_plaquette(beta),
        'string_tension': sigma,
    }
