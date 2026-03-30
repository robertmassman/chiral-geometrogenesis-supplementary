#!/usr/bin/env python3
"""
Definitive Resolution: Information Amplification on ∂S
======================================================

Resolves the conflicting results between phase_h_3d_fisher.c (Model B: primes > integers
on stella surface) and verify_prop_XXg_corrections.py (integers > primes everywhere).

ROOT CAUSES OF DISAGREEMENT (found by investigation):
  1. Fisher formula: C code 1D uses ∂P/∂ω (with 2*x factor), 3D uses ∂P/∂θ
  2. Frequency mapping: C code uses log(prime), Python uses raw prime
  3. Amplitude decay: C code uses 1/√p, Python uses exp(-0.01·f)
  4. Z₃ offsets: C code includes 2π/3 offset for T₋ vertices, Python does not
  5. Phase offsets: Python adds 2πk/K equilibrium phases, C code does not

THIS TEST:
  - Uses IDENTICAL ∂P/∂θ_k formula for ALL geometries (no 2*x)
  - Tests BOTH frequency conventions (log vs raw) to see which drives the result
  - Tests WITH and WITHOUT Z₃ offsets
  - Uses Dunavant quadrature (matching C code) AND random barycentric (matching Python)
  - Includes control geometries with identical sampling
  - Sweeps quadrature density for convergence

Related: Proposition 0.0.XXg claim (b), §4.2
Date: 2026-03-27
"""

import numpy as np
from itertools import combinations

# =============================================================================
# GEOMETRY DEFINITIONS
# =============================================================================

def stella_vertices():
    """Stella octangula vertices (unit circumradius)."""
    s = 1.0 / np.sqrt(3.0)
    T_plus = np.array([[ s, s, s], [ s,-s,-s], [-s, s,-s], [-s,-s, s]])
    T_minus = np.array([[-s,-s,-s], [-s, s, s], [ s,-s, s], [ s, s,-s]])
    return T_plus, T_minus

# Stella faces: 4 per tetrahedron
FACES_PLUS = [(0,1,2), (0,1,3), (0,2,3), (1,2,3)]
FACES_MINUS = [(0,1,2), (0,1,3), (0,2,3), (1,2,3)]

# Dunavant quadrature (order 3, 10 points) — matches C code exactly
BARY_PTS = np.array([
    [1/3, 1/3, 1/3],
    [0.059716, 0.470142, 0.470142],
    [0.470142, 0.059716, 0.470142],
    [0.470142, 0.470142, 0.059716],
    [0.797427, 0.101287, 0.101287],
    [0.101287, 0.797427, 0.101287],
    [0.101287, 0.101287, 0.797427],
    [0.0, 0.5, 0.5],
    [0.5, 0.0, 0.5],
    [0.5, 0.5, 0.0]
])
BARY_WTS = np.array([
    0.1125,
    0.0662, 0.0662, 0.0662,
    0.0630, 0.0630, 0.0630,
    0.0278, 0.0278, 0.0278
])

def dunavant_quadrature(vertices, faces, order_multiplier=1):
    """
    Generate quadrature points on triangulated surface using Dunavant scheme.
    order_multiplier > 1 subdivides each face for higher density.
    """
    points = []
    weights = []
    areas = []

    for face in faces:
        v0, v1, v2 = vertices[face[0]], vertices[face[1]], vertices[face[2]]
        # Face area
        area = 0.5 * np.linalg.norm(np.cross(v1 - v0, v2 - v0))
        areas.append(area)

        if order_multiplier == 1:
            # Standard Dunavant points
            for pt_idx in range(len(BARY_PTS)):
                b = BARY_PTS[pt_idx]
                cart = b[0]*v0 + b[1]*v1 + b[2]*v2
                points.append(cart)
                weights.append(BARY_WTS[pt_idx] * area)
        else:
            # Subdivide: split each face into order_multiplier² sub-triangles
            n = order_multiplier
            for i in range(n):
                for j in range(n - i):
                    # Sub-triangle vertices in barycentric coords
                    b00 = np.array([(n-i-j)/n, i/n, j/n])
                    b10 = np.array([(n-i-j-1)/n, (i+1)/n, j/n])
                    b01 = np.array([(n-i-j-1)/n, i/n, (j+1)/n])
                    sv0 = b00[0]*v0 + b00[1]*v1 + b00[2]*v2
                    sv1 = b10[0]*v0 + b10[1]*v1 + b10[2]*v2
                    sv2 = b01[0]*v0 + b01[1]*v1 + b01[2]*v2
                    sub_area = 0.5 * np.linalg.norm(np.cross(sv1-sv0, sv2-sv0))

                    for pt_idx in range(len(BARY_PTS)):
                        b = BARY_PTS[pt_idx]
                        cart = b[0]*sv0 + b[1]*sv1 + b[2]*sv2
                        points.append(cart)
                        weights.append(BARY_WTS[pt_idx] * sub_area)

                    # Second sub-triangle (if exists)
                    if i + j < n - 1:
                        b11 = np.array([(n-i-j-2)/n, (i+1)/n, (j+1)/n])
                        sv3 = b11[0]*v0 + b11[1]*v1 + b11[2]*v2
                        sub_area2 = 0.5 * np.linalg.norm(np.cross(sv3-sv1, sv2-sv1))
                        for pt_idx in range(len(BARY_PTS)):
                            b = BARY_PTS[pt_idx]
                            cart = b[0]*sv1 + b[1]*sv3 + b[2]*sv2
                            points.append(cart)
                            weights.append(BARY_WTS[pt_idx] * sub_area2)

    total_area = sum(areas)
    weights = np.array(weights) / total_area  # Normalize to sum ≈ sum(bary_wts)*n_faces
    return np.array(points), weights


def random_barycentric(vertices, faces, n_per_face=10, seed=42):
    """Random barycentric sampling (matching Python retest approach)."""
    rng = np.random.RandomState(seed)
    points = []
    for face in faces:
        v0, v1, v2 = vertices[face[0]], vertices[face[1]], vertices[face[2]]
        for _ in range(n_per_face):
            r1, r2 = rng.random(), rng.random()
            if r1 + r2 > 1:
                r1, r2 = 1 - r1, 1 - r2
            r3 = 1 - r1 - r2
            points.append(r1*v0 + r2*v1 + r3*v2)
    return np.array(points), np.ones(len(points)) / len(points)


def two_spheres_surface(n_per_face=10, seed=42):
    """Control: two disjoint spheres, triangulated."""
    rng = np.random.RandomState(seed)
    radius = 1.0 / np.sqrt(3.0)  # Match stella circumradius
    points = []
    for center in [np.array([0.5, 0, 0]), np.array([-0.5, 0, 0])]:
        for _ in range(n_per_face * 4):  # 4 faces per tet, match count
            v = rng.randn(3)
            v = v / np.linalg.norm(v) * radius + center
            points.append(v)
    pts = np.array(points)
    return pts, np.ones(len(pts)) / len(pts)


def random_8vertex_surface(n_per_face=10, seed=123):
    """Control: 8 random vertices on unit sphere, random triangulated."""
    rng = np.random.RandomState(seed)
    verts = rng.randn(8, 3)
    verts = verts / np.linalg.norm(verts, axis=1, keepdims=True) / np.sqrt(3.0)
    points = list(verts)
    for _ in range(n_per_face * 8):
        i, j, k = rng.choice(8, 3, replace=False)
        r1, r2 = rng.random(), rng.random()
        if r1 + r2 > 1:
            r1, r2 = 1 - r1, 1 - r2
        r3 = 1 - r1 - r2
        points.append(r1*verts[i] + r2*verts[j] + r3*verts[k])
    pts = np.array(points)
    return pts, np.ones(len(pts)) / len(pts)


# =============================================================================
# FREQUENCY SETS
# =============================================================================

def sieve_primes(n):
    """Return first n primes."""
    primes = []
    candidate = 2
    while len(primes) < n:
        if all(candidate % p != 0 for p in primes if p*p <= candidate):
            primes.append(candidate)
        candidate += 1
    return primes

PRIMES = sieve_primes(110)


def freq_sets_c_convention(K):
    """C code convention: log frequencies, 1/√p amplitudes."""
    prime_freq = np.array([np.log(PRIMES[k]) for k in range(K)])
    prime_amp = np.array([1.0 / np.sqrt(PRIMES[k]) for k in range(K)])

    int_freq = np.array([np.log(k + 2) for k in range(K)])
    int_amp = np.array([1.0 / np.sqrt(k + 2) for k in range(K)])

    return {
        'prime': (prime_freq, prime_amp),
        'integer': (int_freq, int_amp),
    }


def freq_sets_python_convention(K):
    """Python retest convention: raw frequencies, exponential decay."""
    prime_freq = np.array(PRIMES[:K], dtype=float)
    prime_amp = np.exp(-0.01 * prime_freq)

    int_freq = np.arange(1, K + 1, dtype=float)
    int_amp = np.exp(-0.01 * int_freq)

    return {
        'prime': (prime_freq, prime_amp),
        'integer': (int_freq, int_amp),
    }


# =============================================================================
# FISHER MATRIX COMPUTATION
# =============================================================================

def fibonacci_directions(K):
    """Mode directions on S² using Fibonacci lattice (matches C code)."""
    golden = (1 + np.sqrt(5)) / 2
    dirs = np.zeros((K, 3))
    for k in range(K):
        theta = np.arccos(1 - 2*(k + 0.5)/K)
        phi = 2 * np.pi * (k + 0.5) / golden
        dirs[k] = [np.sin(theta)*np.cos(phi), np.sin(theta)*np.sin(phi), np.cos(theta)]
    return dirs


def fisher_erank_3d(points, weights, K, freqs, amps, dirs,
                    z3_charges=None, phase_offsets=None):
    """
    Compute Fisher effective rank on 3D sample points.

    Uses ∂P/∂θ_k formula (phase sensitivity) for all geometries.

    Parameters:
        points: (N, 3) sample points
        weights: (N,) quadrature weights
        K: number of frequency components
        freqs: (K,) frequencies
        amps: (K,) amplitudes
        dirs: (K, 3) mode directions
        z3_charges: (N,) optional Z₃ charge per point (1 or 2)
        phase_offsets: (K,) optional equilibrium phase offsets
    """
    F = np.zeros((K, K))

    for idx in range(len(points)):
        pt = points[idx]
        w = weights[idx]

        re_z = np.zeros(K)
        im_z = np.zeros(K)

        for k in range(K):
            rdot = np.dot(pt, dirs[k])
            phase = freqs[k] * rdot

            # Z₃ offset
            if z3_charges is not None and z3_charges[idx] == 2:
                phase += 2.0 * np.pi / 3.0

            # Equilibrium phase offset
            if phase_offsets is not None:
                phase += phase_offsets[k]

            re_z[k] = amps[k] * np.cos(phase)
            im_z[k] = amps[k] * np.sin(phase)

        Re_Z = re_z.sum()
        Im_Z = im_z.sum()
        P = Re_Z**2 + Im_Z**2
        if P < 1e-30:
            continue

        # ∂P/∂θ_k = 2(re_z[k]*Im_Z - im_z[k]*Re_Z)
        # Factor of 2 cancels in ratio, so use: dp[k] = re_z[k]*Im_Z - im_z[k]*Re_Z
        dp = re_z * Im_Z - im_z * Re_Z

        F += w * np.outer(dp, dp) / P

    eigs = np.linalg.eigvalsh(F)
    return effective_rank(eigs)


def fisher_erank_1d(K, freqs, amps, x_max=200.0, n_grid=8000,
                    phase_offsets=None):
    """
    Compute Fisher effective rank on 1D line.
    Uses ∂P/∂θ_k formula (NO 2*x factor).
    """
    dx = x_max / n_grid
    F = np.zeros((K, K))

    for g in range(n_grid):
        x = (g + 0.5) * dx

        re_z = np.zeros(K)
        im_z = np.zeros(K)

        for k in range(K):
            phase = freqs[k] * x
            if phase_offsets is not None:
                phase += phase_offsets[k]
            re_z[k] = amps[k] * np.cos(phase)
            im_z[k] = amps[k] * np.sin(phase)

        Re_Z = re_z.sum()
        Im_Z = im_z.sum()
        P = Re_Z**2 + Im_Z**2
        if P < 1e-30:
            continue

        dp = re_z * Im_Z - im_z * Re_Z
        F += dx * np.outer(dp, dp) / (P * x_max)

    eigs = np.linalg.eigvalsh(F)
    return effective_rank(eigs)


def effective_rank(eigenvalues):
    """Roy-Vetterli entropy-based effective rank."""
    pos = eigenvalues[eigenvalues > 1e-15]
    if len(pos) == 0:
        return 0.0
    p = pos / pos.sum()
    entropy = -np.sum(p * np.log(p))
    return np.exp(entropy)


# =============================================================================
# LOG-LINEAR FIT
# =============================================================================

def log_fit(K_vals, eranks):
    """Fit erank = a·ln(K) + b, return (slope, intercept, R²)."""
    lnK = np.log(np.array(K_vals, dtype=float))
    y = np.array(eranks, dtype=float)
    if len(lnK) < 2:
        return 0, 0, 0
    A = np.vstack([lnK, np.ones_like(lnK)]).T
    result = np.linalg.lstsq(A, y, rcond=None)
    slope, intercept = result[0]
    ss_res = np.sum((y - slope*lnK - intercept)**2)
    ss_tot = np.sum((y - y.mean())**2)
    r2 = 1 - ss_res/ss_tot if ss_tot > 0 else 0
    return slope, intercept, r2


# =============================================================================
# MAIN TEST BATTERY
# =============================================================================

def run_test(label, geometry_fn, freq_convention, K_values,
             use_z3=False, use_phase_offsets=False):
    """
    Run a single test configuration.
    Returns dict with prime/integer slopes.
    """
    freq_fn = freq_sets_c_convention if freq_convention == 'c' else freq_sets_python_convention

    results = {'prime': [], 'integer': []}

    for K in K_values:
        dirs = fibonacci_directions(K)
        fsets = freq_fn(K)
        phase_offsets = np.array([2*np.pi*k/K for k in range(K)]) if use_phase_offsets else None

        for ftype in ['prime', 'integer']:
            freqs, amps = fsets[ftype]

            if geometry_fn == '1d':
                er = fisher_erank_1d(K, freqs, amps, phase_offsets=phase_offsets)
            else:
                points, weights, z3_charges = geometry_fn(K, use_z3)
                er = fisher_erank_3d(points, weights, K, freqs, amps, dirs,
                                     z3_charges=z3_charges if use_z3 else None,
                                     phase_offsets=phase_offsets)
            results[ftype].append(er)

    p_slope, p_int, p_r2 = log_fit(K_values, results['prime'])
    i_slope, i_int, i_r2 = log_fit(K_values, results['integer'])

    return {
        'label': label,
        'prime_slope': p_slope, 'prime_r2': p_r2,
        'int_slope': i_slope, 'int_r2': i_r2,
        'prime_eranks': results['prime'],
        'int_eranks': results['integer'],
        'p_gt_i': p_slope > i_slope,
    }


def make_stella_dunavant(order_mult=1):
    """Factory for stella surface with Dunavant quadrature."""
    def fn(K, use_z3):
        T_plus, T_minus = stella_vertices()
        all_verts = np.vstack([T_plus, T_minus])
        faces_p = [(i, j, k) for i, j, k in FACES_PLUS]
        faces_m = [(i+4, j+4, k+4) for i, j, k in FACES_MINUS]
        all_faces = faces_p + faces_m

        pts, wts = dunavant_quadrature(all_verts, all_faces, order_mult)

        z3_charges = None
        if use_z3:
            # Assign charges based on which tetrahedron face the point belongs to
            n_plus = len(faces_p) * (len(BARY_PTS) * (order_mult**2 if order_mult > 1 else 1))
            # Actually count properly
            pts_p, _ = dunavant_quadrature(T_plus, FACES_PLUS, order_mult)
            pts_m, _ = dunavant_quadrature(T_minus, FACES_MINUS, order_mult)
            z3_charges = np.concatenate([np.ones(len(pts_p)), 2*np.ones(len(pts_m))])

        return pts, wts, z3_charges
    return fn


def make_stella_random(n_per_face=10, seed=42):
    """Factory for stella surface with random barycentric sampling."""
    def fn(K, use_z3):
        T_plus, T_minus = stella_vertices()
        all_verts = np.vstack([T_plus, T_minus])
        faces_p = [(i, j, k) for i, j, k in FACES_PLUS]
        faces_m = [(i+4, j+4, k+4) for i, j, k in FACES_MINUS]
        all_faces = faces_p + faces_m

        pts, wts = random_barycentric(all_verts, all_faces, n_per_face, seed)

        z3_charges = None
        if use_z3:
            n_plus = len(faces_p) * n_per_face
            z3_charges = np.concatenate([
                np.ones(n_plus),
                2 * np.ones(len(pts) - n_plus)
            ])

        return pts, wts, z3_charges
    return fn


def make_two_spheres(n_per_face=10, seed=42):
    """Factory for two-spheres control."""
    def fn(K, use_z3):
        pts, wts = two_spheres_surface(n_per_face, seed)
        z3_charges = np.concatenate([
            np.ones(len(pts)//2), 2*np.ones(len(pts) - len(pts)//2)
        ]) if use_z3 else None
        return pts, wts, z3_charges
    return fn


def make_random_8v(n_per_face=10, seed=123):
    """Factory for random 8-vertex control."""
    def fn(K, use_z3):
        pts, wts = random_8vertex_surface(n_per_face, seed)
        z3_charges = np.concatenate([
            np.ones(len(pts)//2), 2*np.ones(len(pts) - len(pts)//2)
        ]) if use_z3 else None
        return pts, wts, z3_charges
    return fn


def main():
    print("=" * 78)
    print("DEFINITIVE RESOLUTION: Information Amplification on ∂S")
    print("=" * 78)
    print()
    print("All tests use identical ∂P/∂θ_k formula (no 2*x factor).")
    print("Each test varies ONE parameter at a time to isolate the cause.")
    print()

    K_VALUES = [3, 5, 7, 10, 15, 20, 30, 40, 50]

    # =========================================================================
    # BATTERY 1: Reproduce C code result (log freqs, Z₃, Dunavant quadrature)
    # =========================================================================
    print("=" * 78)
    print("BATTERY 1: C-CODE FAITHFUL REPRODUCTION")
    print("  (log frequencies, 1/√p amps, Z₃ offsets, Dunavant quadrature)")
    print("=" * 78)
    print()

    tests_b1 = [
        run_test("1D reference", '1d', 'c', K_VALUES),
        run_test("Stella (Dunavant)", make_stella_dunavant(1), 'c', K_VALUES, use_z3=True),
        run_test("Two-spheres ctrl", make_two_spheres(10), 'c', K_VALUES, use_z3=True),
        run_test("Random-8v ctrl", make_random_8v(10), 'c', K_VALUES, use_z3=True),
    ]

    print_results(tests_b1)

    # =========================================================================
    # BATTERY 2: Same as B1 but WITHOUT Z₃ offsets
    # =========================================================================
    print("=" * 78)
    print("BATTERY 2: LOG FREQUENCIES, NO Z₃ OFFSETS")
    print("  (isolates Z₃ contribution)")
    print("=" * 78)
    print()

    tests_b2 = [
        run_test("1D reference", '1d', 'c', K_VALUES),
        run_test("Stella (Dunavant)", make_stella_dunavant(1), 'c', K_VALUES, use_z3=False),
        run_test("Two-spheres ctrl", make_two_spheres(10), 'c', K_VALUES, use_z3=False),
        run_test("Random-8v ctrl", make_random_8v(10), 'c', K_VALUES, use_z3=False),
    ]

    print_results(tests_b2)

    # =========================================================================
    # BATTERY 3: Python convention (raw freqs, no Z₃, phase offsets)
    # =========================================================================
    print("=" * 78)
    print("BATTERY 3: PYTHON RETEST REPRODUCTION")
    print("  (raw frequencies, exp decay, phase offsets 2πk/K, no Z₃)")
    print("=" * 78)
    print()

    tests_b3 = [
        run_test("1D reference", '1d', 'python', K_VALUES, use_phase_offsets=True),
        run_test("Stella (Dunavant)", make_stella_dunavant(1), 'python', K_VALUES,
                 use_phase_offsets=True),
        run_test("Stella (random bary)", make_stella_random(12), 'python', K_VALUES,
                 use_phase_offsets=True),
        run_test("Two-spheres ctrl", make_two_spheres(12), 'python', K_VALUES,
                 use_phase_offsets=True),
        run_test("Random-8v ctrl", make_random_8v(12), 'python', K_VALUES,
                 use_phase_offsets=True),
    ]

    print_results(tests_b3)

    # =========================================================================
    # BATTERY 4: Quadrature convergence (does result change with density?)
    # =========================================================================
    print("=" * 78)
    print("BATTERY 4: QUADRATURE CONVERGENCE (C convention, with Z₃)")
    print("  Testing Dunavant order_mult = 1, 2, 3")
    print("=" * 78)
    print()

    for om in [1, 2, 3]:
        geo = make_stella_dunavant(om)
        # Count points
        pts_test, _, _ = geo(5, True)
        n_pts = len(pts_test)
        result = run_test(f"Stella Dunavant ×{om} ({n_pts} pts)", geo, 'c',
                          K_VALUES, use_z3=True)
        print(f"  {result['label']:<40s}  P_slope={result['prime_slope']:7.3f} (R²={result['prime_r2']:.3f})"
              f"  I_slope={result['int_slope']:7.3f} (R²={result['int_r2']:.3f})"
              f"  {'P > I' if result['p_gt_i'] else 'I > P'}")

    for npf in [10, 20, 40, 80]:
        geo = make_stella_random(npf, seed=42)
        pts_test, _, _ = geo(5, True)
        n_pts = len(pts_test)
        result = run_test(f"Stella random bary ×{npf} ({n_pts} pts)", geo, 'c',
                          K_VALUES, use_z3=True)
        print(f"  {result['label']:<40s}  P_slope={result['prime_slope']:7.3f} (R²={result['prime_r2']:.3f})"
              f"  I_slope={result['int_slope']:7.3f} (R²={result['int_r2']:.3f})"
              f"  {'P > I' if result['p_gt_i'] else 'I > P'}")

    print()

    # =========================================================================
    # BATTERY 5: Isolate each variable
    # =========================================================================
    print("=" * 78)
    print("BATTERY 5: VARIABLE ISOLATION (stella Dunavant, Z₃)")
    print("  Change one variable at a time from the C-code baseline")
    print("=" * 78)
    print()

    geo = make_stella_dunavant(1)

    baseline = run_test("Baseline (C convention)", geo, 'c', K_VALUES, use_z3=True)
    no_z3 = run_test("No Z₃ offsets", geo, 'c', K_VALUES, use_z3=False)
    with_po = run_test("+ phase offsets 2πk/K", geo, 'c', K_VALUES,
                       use_z3=True, use_phase_offsets=True)
    raw_freq = run_test("Raw frequencies (python)", geo, 'python', K_VALUES, use_z3=True)
    raw_no_z3 = run_test("Raw freq + no Z₃", geo, 'python', K_VALUES, use_z3=False)

    for r in [baseline, no_z3, with_po, raw_freq, raw_no_z3]:
        print(f"  {r['label']:<30s}  P_slope={r['prime_slope']:7.3f} (R²={r['prime_r2']:.3f})"
              f"  I_slope={r['int_slope']:7.3f} (R²={r['int_r2']:.3f})"
              f"  {'P > I ✓' if r['p_gt_i'] else 'I > P ✗'}")

    print()

    # =========================================================================
    # VERDICT
    # =========================================================================
    print("=" * 78)
    print("VERDICT")
    print("=" * 78)
    print()

    # Count how many tests show P > I on stella
    stella_tests = []
    for battery_name, tests in [("B1", tests_b1), ("B2", tests_b2), ("B3", tests_b3)]:
        for t in tests:
            if 'Stella' in t['label']:
                stella_tests.append((battery_name, t))

    n_pgi = sum(1 for _, t in stella_tests if t['p_gt_i'])
    n_total = len(stella_tests)
    print(f"  Stella tests showing Primes > Integers: {n_pgi}/{n_total}")
    print()

    # Check if any stella test shows P > I when control does NOT
    for battery_name, tests in [("B1", tests_b1), ("B2", tests_b2), ("B3", tests_b3)]:
        stella_pgi = [t for t in tests if 'Stella' in t['label'] and t['p_gt_i']]
        ctrl_pgi = [t for t in tests if 'ctrl' in t['label'] and t['p_gt_i']]
        if stella_pgi and not ctrl_pgi:
            print(f"  *** {battery_name}: STELLA-SPECIFIC AMPLIFICATION DETECTED ***")
            print(f"      Stella shows P > I, but controls show I > P")
        elif stella_pgi and ctrl_pgi:
            print(f"  {battery_name}: Both stella and controls show P > I (not stella-specific)")
        else:
            stella_results = [t for t in tests if 'Stella' in t['label']]
            if stella_results and not stella_results[0]['p_gt_i']:
                print(f"  {battery_name}: Integers > Primes on stella (no amplification)")

    print()
    print("If NO battery shows stella-specific amplification, claim (b) is FALSIFIED.")
    print("If amplification appears only with specific parameter choices, it is a TUNING ARTIFACT.")
    print()

    # Detail table
    print("=" * 78)
    print("DETAILED ERANK VALUES (Battery 1 — C-code faithful)")
    print("=" * 78)
    print()
    print(f"  {'K':>4s}", end="")
    for t in tests_b1:
        short = t['label'][:15]
        print(f"  | {short:>15s} P    {short:>15s} I", end="")
    print()
    print("  " + "-" * (4 + len(tests_b1) * 38))
    for ki, K in enumerate(K_VALUES):
        print(f"  {K:4d}", end="")
        for t in tests_b1:
            print(f"  | {t['prime_eranks'][ki]:15.3f}    {t['int_eranks'][ki]:15.3f}", end="")
        print()


def print_results(tests):
    """Print summary table for a battery of tests."""
    print(f"  {'Geometry':<25s} {'P slope':>8s} {'P R²':>6s}  {'I slope':>8s} {'I R²':>6s}  {'Winner':>8s}")
    print(f"  {'-'*25} {'-'*8} {'-'*6}  {'-'*8} {'-'*6}  {'-'*8}")
    for t in tests:
        winner = "P > I" if t['p_gt_i'] else "I > P"
        print(f"  {t['label']:<25s} {t['prime_slope']:8.3f} {t['prime_r2']:6.3f}"
              f"  {t['int_slope']:8.3f} {t['int_r2']:6.3f}  {winner:>8s}")
    print()


if __name__ == '__main__':
    main()
