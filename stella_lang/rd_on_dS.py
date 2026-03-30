#!/usr/bin/env python3
"""
Reaction-Diffusion Simulation on ∂S (Stella Octangula boundary)

Solves the Fisher-KPP equation derived in Phase 3 (Prop 0.0.XXe):

    ∂ρ/∂t = D ∇²ρ + k_eff ρ(1 - ρ) - μ_eff ρ - γ ρ²

on triangulated ∂S = ∂T₊ ⊔ ∂T₋ (two tetrahedra).

Parameters extracted from Phase 1/2 data:
    k_eff   = 0.22   (effective replication rate, from μ_c = 0.011)
    γ       = 0.027  (intra-specific competition)
    μ_eff   = 20μ    (effective mutation rate, L_core = 20 trits)
    D       = 0.01   (diffusion, from local pairing geometry)

References:
    - Phase 3 document: Proposition-0.0.XXe-Phase3-Reaction-Diffusion-Formulation.md
    - Phase 1 results:  Proposition-0.0.XXe-Phase1-2D-Soup-Results.md
    - Phase 2 analysis: Proposition-0.0.XXe-Phase2-Z3-Potts-Model-Connection.md
"""

import numpy as np
import json
import sys
from collections import defaultdict

# ============================================================
# Mesh construction: triangulated tetrahedron surfaces
# ============================================================

def tetrahedron_vertices(which='plus'):
    """Vertices of T+ or T- inscribed in unit cube.

    T+ vertices: even-parity cube corners (s1*s2*s3 = +1)
    T- vertices: odd-parity cube corners (s1*s2*s3 = -1)
    """
    if which == 'plus':
        return np.array([
            [ 1,  1,  1],
            [ 1, -1, -1],
            [-1,  1, -1],
            [-1, -1,  1]
        ], dtype=float)
    else:
        return np.array([
            [-1, -1, -1],
            [-1,  1,  1],
            [ 1, -1,  1],
            [ 1,  1, -1]
        ], dtype=float)


def triangulate_tetrahedron(n_sub, which='plus'):
    """Triangulate a tetrahedron surface with n_sub subdivisions per edge.

    Returns:
        vertices: (N, 3) array of vertex positions
        triangles: (M, 3) array of triangle vertex indices
        neighbors: dict mapping vertex index -> set of neighbor indices
    """
    verts = tetrahedron_vertices(which)
    # 4 faces of tetrahedron, each defined by 3 vertices
    faces = [(0,1,2), (0,1,3), (0,2,3), (1,2,3)]

    all_points = {}  # (face, i, j) -> global index
    vertices = []

    # Generate vertices on each face via barycentric subdivision
    for fi, (a, b, c) in enumerate(faces):
        va, vb, vc = verts[a], verts[b], verts[c]
        for i in range(n_sub + 1):
            for j in range(n_sub + 1 - i):
                k = n_sub - i - j
                # Barycentric coordinates
                u, v, w = i / n_sub, j / n_sub, k / n_sub
                pt = u * va + v * vb + w * vc
                # Project onto unit sphere (normalize)
                # Actually keep on flat tetrahedron for now

                # Check if this point already exists (shared edges/corners)
                pt_key = tuple(np.round(pt, 10))
                found = False
                for idx, existing in enumerate(vertices):
                    if np.allclose(pt, existing, atol=1e-9):
                        all_points[(fi, i, j)] = idx
                        found = True
                        break
                if not found:
                    all_points[(fi, i, j)] = len(vertices)
                    vertices.append(pt)

    vertices = np.array(vertices)

    # Generate triangles
    triangles = []
    for fi in range(4):
        for i in range(n_sub):
            for j in range(n_sub - i):
                # Upward triangle
                v0 = all_points[(fi, i, j)]
                v1 = all_points[(fi, i+1, j)]
                v2 = all_points[(fi, i, j+1)]
                triangles.append((v0, v1, v2))

                # Downward triangle (if it exists)
                if i + j < n_sub - 1:
                    v3 = all_points[(fi, i+1, j+1)]
                    triangles.append((v1, v3, v2))

    triangles = np.array(triangles)

    # Build neighbor map
    neighbors = defaultdict(set)
    for tri in triangles:
        for ii in range(3):
            for jj in range(ii+1, 3):
                neighbors[tri[ii]].add(tri[jj])
                neighbors[tri[jj]].add(tri[ii])

    return vertices, triangles, dict(neighbors)


def build_mesh(n_sub):
    """Build full ∂S mesh: T+ and T- with cross-links.

    Returns:
        vertices: combined vertex array
        neighbors_same: intra-tetrahedron neighbors
        neighbors_cross: inter-tetrahedron neighbors (for 50% cross-talk)
        n_plus: number of vertices in T+
    """
    v_plus, tri_plus, nbr_plus = triangulate_tetrahedron(n_sub, 'plus')
    v_minus, tri_minus, nbr_minus = triangulate_tetrahedron(n_sub, 'minus')

    n_plus = len(v_plus)
    n_total = n_plus + len(v_minus)

    # Offset T- indices
    nbr_minus_offset = {}
    for k, v in nbr_minus.items():
        nbr_minus_offset[k + n_plus] = {vi + n_plus for vi in v}

    # Combine same-tetrahedron neighbors
    neighbors_same = {}
    for k, v in nbr_plus.items():
        neighbors_same[k] = v
    neighbors_same.update(nbr_minus_offset)

    # Cross-tetrahedron links: connect each T+ vertex to nearest T- vertices
    # In the soup, cross-talk is random (any T- tile); here we use spatial proximity
    neighbors_cross = defaultdict(set)
    for i in range(n_plus):
        # Find nearest T- vertices
        dists = np.linalg.norm(v_minus - v_plus[i], axis=1)
        nearest = np.argsort(dists)[:6]  # ~6 nearest cross-neighbors
        for j in nearest:
            neighbors_cross[i].add(j + n_plus)
            neighbors_cross[j + n_plus].add(i)

    vertices = np.vstack([v_plus, v_minus])

    return vertices, neighbors_same, dict(neighbors_cross), n_plus


# ============================================================
# Discrete Laplacian
# ============================================================

def build_laplacian_weights(n_vertices, neighbors_same, neighbors_cross, cross_weight=0.5):
    """Build the discrete Laplacian as sparse weight arrays.

    For the bilayer model:
        (∇²f)_i = (1-α) Σ_{j∈same} w_ij(f_j - f_i) + α Σ_{j∈cross} w_ij(f_j - f_i)

    where α = cross_weight = 0.5 (50% cross-tetrahedron interaction).
    Uses uniform weights (appropriate for nearly-equilateral triangulation).
    """
    # Store as list of (neighbor_indices, weights) per vertex
    lap_indices = []
    lap_weights = []

    for i in range(n_vertices):
        same = list(neighbors_same.get(i, set()))
        cross = list(neighbors_cross.get(i, set()))

        n_same = len(same)
        n_cross = len(cross)

        indices = same + cross
        weights = []

        if n_same > 0:
            w_s = (1 - cross_weight) / n_same
            weights.extend([w_s] * n_same)
        if n_cross > 0:
            w_c = cross_weight / n_cross
            weights.extend([w_c] * n_cross)

        lap_indices.append(np.array(indices, dtype=int))
        lap_weights.append(np.array(weights, dtype=float))

    return lap_indices, lap_weights


def apply_laplacian(rho, lap_indices, lap_weights):
    """Compute discrete Laplacian ∇²ρ."""
    n = len(rho)
    lap = np.zeros(n)
    for i in range(n):
        if len(lap_indices[i]) > 0:
            lap[i] = np.sum(lap_weights[i] * (rho[lap_indices[i]] - rho[i]))
    return lap


# ============================================================
# Fisher-KPP reaction-diffusion solver
# ============================================================

def reaction_term(rho, k_eff, mu_eff, gamma):
    """Compute R(ρ) = k_eff ρ(1-ρ) - μ_eff ρ - γ ρ².

    Equivalent to: ρ[(k_eff - μ_eff) - (k_eff + γ)ρ]
    """
    return k_eff * rho * (1 - rho) - mu_eff * rho - gamma * rho**2


def steady_state(k_eff, mu_eff, gamma):
    """Compute analytical steady state ρ* = (k_eff - μ_eff)/(k_eff + γ)."""
    if k_eff <= mu_eff:
        return 0.0
    return (k_eff - mu_eff) / (k_eff + gamma)


def run_simulation(n_sub=16, mu=0.001, D=0.01, k_eff=0.22, gamma=0.027,
                   n_epochs=500, dt=0.1, seed_type='localized', seed_size=10,
                   cross_weight=0.5, noise_amplitude=0.0, rng_seed=42,
                   report_interval=50):
    """Run Fisher-KPP simulation on ∂S.

    Args:
        n_sub: mesh subdivision level
        mu: per-trit mutation rate
        D: diffusion coefficient
        k_eff: effective replication rate
        gamma: competition coefficient
        n_epochs: number of time steps
        dt: time step size
        seed_type: 'localized', 'random', 'uniform', 'single'
        seed_size: number of seed vertices (for localized)
        cross_weight: T+/T- coupling strength (0.5 = 50%)
        noise_amplitude: stochastic noise strength (0 = deterministic)
        rng_seed: random seed
        report_interval: epochs between status reports

    Returns:
        dict with simulation results
    """
    np.random.seed(rng_seed)

    L_core = 20  # trits in replicator core
    mu_eff = L_core * mu
    rho_star = steady_state(k_eff, mu_eff, gamma)

    print(f"=== Fisher-KPP on ∂S ===")
    print(f"Parameters: k_eff={k_eff}, γ={gamma}, μ={mu}, μ_eff={mu_eff:.4f}")
    print(f"Predicted steady state: ρ* = {rho_star:.4f}")
    print(f"Growth rate r = k_eff - μ_eff = {k_eff - mu_eff:.4f}")
    print(f"Mesh: n_sub={n_sub}, cross_weight={cross_weight}")
    print()

    # Build mesh
    print("Building mesh...")
    vertices, nbr_same, nbr_cross, n_plus = build_mesh(n_sub)
    n_total = len(vertices)
    print(f"  T+: {n_plus} vertices, T-: {n_total - n_plus} vertices, total: {n_total}")

    # Build Laplacian
    print("Building Laplacian...")
    lap_idx, lap_wt = build_laplacian_weights(n_total, nbr_same, nbr_cross, cross_weight)

    # Initial conditions
    rho = np.zeros(n_total)

    if seed_type == 'localized':
        # Seed a cluster of vertices on T+
        seed_center = 0  # first vertex
        # BFS to find seed_size nearest vertices
        visited = {seed_center}
        frontier = [seed_center]
        while len(visited) < seed_size and frontier:
            next_frontier = []
            for v in frontier:
                for nb in nbr_same.get(v, set()):
                    if nb not in visited and len(visited) < seed_size:
                        visited.add(nb)
                        next_frontier.append(nb)
            frontier = next_frontier
        for v in visited:
            rho[v] = 1.0
        print(f"  Seeded {len(visited)} vertices (localized on T+)")

    elif seed_type == 'single':
        rho[0] = 1.0
        print("  Seeded 1 vertex")

    elif seed_type == 'random':
        rho = np.random.uniform(0, 0.1, n_total)
        print(f"  Random initial: mean={rho.mean():.4f}")

    elif seed_type == 'uniform':
        rho[:] = 0.01
        print(f"  Uniform initial: ρ=0.01")

    # Time evolution
    print(f"\nRunning {n_epochs} epochs (dt={dt})...")
    print(f"{'Epoch':>8} {'ρ_mean':>8} {'ρ_max':>8} {'ρ_T+':>8} {'ρ_T-':>8} {'Δρ/epoch':>10}")
    print("-" * 56)

    history = {
        'rho_mean': [],
        'rho_max': [],
        'rho_tplus': [],
        'rho_tminus': [],
        'rho_snapshots': [],
        'snapshot_epochs': []
    }

    rho_prev_mean = rho.mean()

    for epoch in range(n_epochs):
        # Compute Laplacian
        lap = apply_laplacian(rho, lap_idx, lap_wt)

        # Compute reaction
        R = reaction_term(rho, k_eff, mu_eff, gamma)

        # Forward Euler update
        drho = D * lap + R

        # Add stochastic noise if requested
        if noise_amplitude > 0:
            noise = noise_amplitude * np.sqrt(np.maximum(rho * (1 - rho), 0) / 6.0)
            drho += noise * np.random.randn(n_total)

        rho = rho + dt * drho

        # Clamp to [0, 1]
        rho = np.clip(rho, 0, 1)

        # Record
        rho_mean = rho.mean()
        rho_max = rho.max()
        rho_tplus = rho[:n_plus].mean()
        rho_tminus = rho[n_plus:].mean()

        history['rho_mean'].append(float(rho_mean))
        history['rho_max'].append(float(rho_max))
        history['rho_tplus'].append(float(rho_tplus))
        history['rho_tminus'].append(float(rho_tminus))

        if epoch % report_interval == 0 or epoch == n_epochs - 1:
            delta = rho_mean - rho_prev_mean
            print(f"{epoch:8d} {rho_mean:8.4f} {rho_max:8.4f} {rho_tplus:8.4f} {rho_tminus:8.4f} {delta:10.6f}")
            rho_prev_mean = rho_mean

            # Save snapshot
            history['rho_snapshots'].append(rho.copy().tolist())
            history['snapshot_epochs'].append(epoch)

    # Final analysis
    print(f"\n=== Final State ===")
    print(f"ρ_mean = {rho.mean():.4f} (predicted: {rho_star:.4f})")
    print(f"ρ_max  = {rho.max():.4f}")
    print(f"ρ_min  = {rho.min():.4f}")
    print(f"ρ_T+   = {rho[:n_plus].mean():.4f}")
    print(f"ρ_T-   = {rho[n_plus:].mean():.4f}")
    print(f"Spatial std = {rho.std():.4f}")

    # Check convergence to steady state
    final_mean = np.mean(history['rho_mean'][-20:])
    print(f"\nMean of last 20 epochs: {final_mean:.4f}")
    print(f"Predicted ρ*: {rho_star:.4f}")
    print(f"Relative error: {abs(final_mean - rho_star) / max(rho_star, 1e-10):.2%}")

    results = {
        'parameters': {
            'n_sub': n_sub, 'mu': mu, 'D': D, 'k_eff': k_eff, 'gamma': gamma,
            'mu_eff': mu_eff, 'n_epochs': n_epochs, 'dt': dt,
            'seed_type': seed_type, 'seed_size': seed_size,
            'cross_weight': cross_weight, 'noise_amplitude': noise_amplitude,
            'rng_seed': rng_seed
        },
        'mesh': {
            'n_total': n_total, 'n_plus': n_plus, 'n_minus': n_total - n_plus
        },
        'predicted_steady_state': rho_star,
        'final_rho_mean': float(rho.mean()),
        'final_rho_std': float(rho.std()),
        'history': {
            'rho_mean': history['rho_mean'],
            'rho_max': history['rho_max'],
            'rho_tplus': history['rho_tplus'],
            'rho_tminus': history['rho_tminus'],
        }
    }

    return results


def run_mutation_sweep():
    """Sweep mutation rate to compare PDE steady states with Phase 1/2 data."""
    print("=" * 60)
    print("EXPERIMENT 1: Mutation Rate Sweep")
    print("Compare PDE steady states with Phase 2 data (§2.2.2)")
    print("=" * 60)

    mu_values = [0.000, 0.001, 0.002, 0.003, 0.004, 0.005, 0.006, 0.008, 0.010, 0.012]
    # Phase 2 observed values (from error_threshold_confinement.c)
    observed = {
        0.000: 0.89, 0.002: 0.802, 0.003: 0.728, 0.004: 0.644,
        0.005: 0.567, 0.006: 0.477, 0.008: 0.315, 0.010: 0.189, 0.012: 0.0
    }

    k_eff = 0.22
    gamma = 0.027
    L_core = 20

    print(f"\nParameters: k_eff={k_eff}, γ={gamma}, L_core={L_core}")
    print(f"\n{'μ':>8} {'μ_eff':>8} {'ρ*_pred':>8} {'ρ*_obs':>8} {'error':>8}")
    print("-" * 44)

    for mu in mu_values:
        mu_eff = L_core * mu
        rho_pred = steady_state(k_eff, mu_eff, gamma)
        rho_obs = observed.get(mu, None)
        obs_str = f"{rho_obs:.3f}" if rho_obs is not None else "  —  "
        err_str = f"{abs(rho_pred - rho_obs):.3f}" if rho_obs is not None else "  —  "
        print(f"{mu:8.4f} {mu_eff:8.4f} {rho_pred:8.3f} {obs_str:>8} {err_str:>8}")

    print("\nNote: Systematic overprediction expected — mean-field model")
    print("doesn't capture quasispecies diversity effects (see §3.2.6).")


def run_nucleation_test():
    """Test nucleation dynamics: seed replicators and track growth."""
    print("\n" + "=" * 60)
    print("EXPERIMENT 2: Nucleation and Growth Dynamics")
    print("Compare PDE growth with Phase 1 seeded data (§2.2.4)")
    print("=" * 60)

    seed_sizes = [1, 2, 5, 10, 20]

    for ns in seed_sizes:
        print(f"\n--- Seed size: {ns} ---")
        results = run_simulation(
            n_sub=16, mu=0.001, D=0.01,
            n_epochs=300, dt=0.1,
            seed_type='localized', seed_size=ns,
            noise_amplitude=0.0,
            report_interval=50
        )


def run_front_speed_test():
    """Measure traveling wave front speed and compare with Fisher-KPP prediction."""
    print("\n" + "=" * 60)
    print("EXPERIMENT 3: Traveling Wave Front Speed")
    print("Fisher-KPP prediction: v_min = 2√(Dr)")
    print("=" * 60)

    k_eff = 0.22
    mu = 0.001
    mu_eff = 20 * mu
    gamma = 0.027
    D = 0.01
    r = k_eff - mu_eff
    v_predicted = 2 * np.sqrt(D * r)

    print(f"\nr = k_eff - μ_eff = {r:.4f}")
    print(f"D = {D}")
    print(f"Predicted front speed: v_min = 2√(Dr) = {v_predicted:.4f}")

    results = run_simulation(
        n_sub=32, mu=mu, D=D,
        n_epochs=500, dt=0.05,
        seed_type='localized', seed_size=5,
        report_interval=100
    )

    # Measure front speed from the density profile
    rho_mean = results['history']['rho_mean']
    # Front reaches half-density at some time
    half_idx = None
    for i, r in enumerate(rho_mean):
        if r > 0.5 * results['predicted_steady_state']:
            half_idx = i
            break

    if half_idx:
        # Rough estimate: front traverses ~half the surface in half_idx steps
        # Surface radius ~ 1 (unit cube), so characteristic length ~ π
        char_length = np.pi  # approximate half-circumference of tetrahedron
        t_half = half_idx * 0.05
        v_measured = char_length / t_half if t_half > 0 else float('inf')
        print(f"\nTime to 50% density: {t_half:.1f}")
        print(f"Estimated front speed: {v_measured:.4f}")
        print(f"Fisher-KPP prediction: {v_predicted:.4f}")
    else:
        print("\nDensity did not reach 50% of steady state")


def run_bilayer_test():
    """Test bilayer coupling: compare T+ and T- densities."""
    print("\n" + "=" * 60)
    print("EXPERIMENT 4: Bilayer Coupling (T+ vs T-)")
    print("Seed only T+, observe propagation to T- via cross-talk")
    print("=" * 60)

    # Seed only on T+
    results = run_simulation(
        n_sub=16, mu=0.001, D=0.01,
        n_epochs=500, dt=0.1,
        seed_type='localized', seed_size=10,
        cross_weight=0.5,
        report_interval=50
    )

    rho_tp = results['history']['rho_tplus']
    rho_tm = results['history']['rho_tminus']

    # Find when T- reaches 10% of steady state
    threshold = 0.1 * results['predicted_steady_state']
    t_cross = None
    for i, r in enumerate(rho_tm):
        if r > threshold:
            t_cross = i
            break

    if t_cross:
        print(f"\nT- reaches 10% of ρ* at epoch {t_cross}")
        print(f"T+ at that time: {rho_tp[t_cross]:.4f}")
        print(f"Delay (T- lag): {t_cross} epochs")
    else:
        print("\nT- did not reach threshold")


# ============================================================
# Main
# ============================================================

if __name__ == '__main__':
    if len(sys.argv) > 1:
        experiment = sys.argv[1]
    else:
        experiment = 'all'

    if experiment in ('all', 'sweep'):
        run_mutation_sweep()

    if experiment in ('all', 'nucleation'):
        run_nucleation_test()

    if experiment in ('all', 'front'):
        run_front_speed_test()

    if experiment in ('all', 'bilayer'):
        run_bilayer_test()

    if experiment not in ('all', 'sweep', 'nucleation', 'front', 'bilayer'):
        print(f"Unknown experiment: {experiment}")
        print("Usage: python3 rd_on_dS.py [all|sweep|nucleation|front|bilayer]")
