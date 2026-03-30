"""
Observable Measurements
========================

Measurement functions for SU(3) lattice gauge theory on FCC, D4, and Z^4 lattices.

Triangular-plaquette observables (FCC/D4):
    average_plaquette    - Average (1/3) Re Tr(W_triangle) over all faces

Square-plaquette observables (Z^4):
    average_plaquette_square - Average (1/3) Re Tr(W_square) over all faces

Shared:
    polyakov_loop        - Polyakov loop along a primitive direction
    correlator_polyakov  - Polyakov loop correlator for mass gap extraction
    extract_mass_gap     - Effective mass from correlator log ratio
    jackknife_error      - Statistical error with autocorrelation handling
    wilson_loop          - Rectangular Wilson loops for string tension
"""

import numpy as np
from numba import njit
from . import su3_ops


@njit(cache=True)
def average_plaquette(links, face_edges, face_dirs, n_faces):
    """Compute the average plaquette: <(1/3) Re Tr(W_triangle)>.

    The Wilson loop around each triangular face is:
        W_f = link(e0,d0) @ link(e1,d1) @ link(e2,d2)

    The plaquette value is (1/Nc) Re Tr(W_f), averaged over all faces.
    For identity links this gives 1.0; for random links ~0.

    Returns: float in approximately [-1/3, 1].
    """
    plaq_sum = 0.0

    for f_idx in range(n_faces):
        e0 = face_edges[f_idx, 0]
        e1 = face_edges[f_idx, 1]
        e2 = face_edges[f_idx, 2]
        d0 = face_dirs[f_idx, 0]
        d1 = face_dirs[f_idx, 1]
        d2 = face_dirs[f_idx, 2]

        # Get oriented links
        if d0 == 1:
            L0 = links[e0]
        else:
            L0 = su3_ops.mat3x3_dag(links[e0])
        if d1 == 1:
            L1 = links[e1]
        else:
            L1 = su3_ops.mat3x3_dag(links[e1])
        if d2 == 1:
            L2 = links[e2]
        else:
            L2 = su3_ops.mat3x3_dag(links[e2])

        W = su3_ops.mat3x3_mul(su3_ops.mat3x3_mul(L0, L1), L2)
        plaq_sum += su3_ops.mat3x3_trace(W).real / 3.0

    return plaq_sum / n_faces


@njit(cache=True)
def _polyakov_product_along_dir(links, edge_sites, n_edges, site_coords,
                                L, direction):
    """Compute Polyakov loop product along one primitive direction for each
    spatial position.

    A Polyakov loop wraps around the lattice in one direction (e.g., n1),
    visiting L sites and multiplying the L link matrices connecting them.

    Parameters:
        direction: 0, 1, or 2 for n1, n2, or n3 direction

    Returns: array of (1/3)*Tr(P) for each transverse position, shape (L*L,)
    """
    # Build a lookup: for site with coord[direction]=t, find the edge
    # connecting it to coord[direction]=t+1
    n_perp = L * L
    poly_traces = np.zeros(n_perp, dtype=np.float64)

    # For each transverse position
    for p_idx in range(n_perp):
        # Decode transverse position
        if direction == 0:
            p1 = p_idx // L
            p2 = p_idx % L
        elif direction == 1:
            p1 = p_idx // L
            p2 = p_idx % L
        else:
            p1 = p_idx // L
            p2 = p_idx % L

        P = su3_ops.mat3x3_eye()

        for t in range(L):
            # Source site coordinates
            if direction == 0:
                s = np.array([t, p1, p2], dtype=np.int32)
            elif direction == 1:
                s = np.array([p1, t, p2], dtype=np.int32)
            else:
                s = np.array([p1, p2, t], dtype=np.int32)

            src = (s[0] * L + s[1]) * L + s[2]

            # Target site: s + e_direction (mod L)
            tgt_coords = s.copy()
            tgt_coords[direction] = (tgt_coords[direction] + 1) % L
            tgt = (tgt_coords[0] * L + tgt_coords[1]) * L + tgt_coords[2]

            # Find edge between src and tgt
            i, j = min(src, tgt), max(src, tgt)
            # Linear search (could optimize with hash)
            found = False
            for e_idx in range(n_edges):
                if edge_sites[e_idx, 0] == i and edge_sites[e_idx, 1] == j:
                    if src < tgt:
                        U = links[e_idx]
                    else:
                        U = su3_ops.mat3x3_dag(links[e_idx])
                    P = su3_ops.mat3x3_mul(P, U)
                    found = True
                    break
            if not found:
                # Edge not found; shouldn't happen with correct lattice
                pass

        poly_traces[p_idx] = su3_ops.mat3x3_trace(P).real / 3.0

    return poly_traces


@njit(cache=True)
def _polyakov_product_d4_jit(links, path_edges, path_dirs, n_paths, n_steps):
    """Compute Polyakov loop traces along precomputed zigzag paths on D4.

    Parameters:
        path_edges: int32[n_paths, n_steps] edge indices per path
        path_dirs: int8[n_paths, n_steps] edge orientations per path

    Returns: float64[n_paths] with (1/3)*Re Tr(P) per path
    """
    traces = np.zeros(n_paths, dtype=np.float64)
    for p in range(n_paths):
        P = su3_ops.mat3x3_eye()
        for s in range(n_steps):
            e = path_edges[p, s]
            d = path_dirs[p, s]
            if d == 1:
                U = links[e]
            else:
                U = su3_ops.mat3x3_dag(links[e])
            P = su3_ops.mat3x3_mul(P, U)
        traces[p] = su3_ops.mat3x3_trace(P).real / 3.0
    return traces


def polyakov_loop(links, lattice, direction=0):
    """Compute the spatially-averaged Polyakov loop magnitude.

    Dispatches to FCC (3D), D4 (4D), or Z^4 (4D) based on lattice type.
    Both D4 and Z^4 use precomputed path arrays in the same format.

    Returns: <|P|> averaged over transverse positions.
    """
    if hasattr(lattice, 'dim') and lattice.dim == 4:
        return polyakov_loop_d4(links, lattice, direction)

    traces = _polyakov_product_along_dir(
        links, lattice.edge_sites, lattice.n_edges,
        lattice.site_coords, lattice.L, direction)
    return np.mean(np.abs(traces))


def polyakov_loop_d4(links, lattice, direction=0):
    """Compute spatially-averaged Polyakov loop on D4 lattice.

    Uses precomputed zigzag paths stored in lattice.polyakov_paths.
    """
    path_edges, path_dirs = lattice.polyakov_paths[direction]
    n_paths, n_steps = path_edges.shape
    traces = _polyakov_product_d4_jit(
        links, path_edges, path_dirs, n_paths, n_steps)
    return np.mean(np.abs(traces))


def correlator_polyakov(links, lattice, direction=0, max_sep=None):
    """Compute Polyakov loop correlator C(r) = <P(0) P(r)*> - <P>^2.

    Dispatches to FCC (3D), D4 (4D), or Z^4 (4D) based on lattice type.

    Parameters:
        direction: direction of the Polyakov loop
        max_sep: maximum separation to compute (default L//2)

    Returns: array of C(r) for r = 0, 1, ..., max_sep
    """
    if hasattr(lattice, 'dim') and lattice.dim == 4:
        return correlator_polyakov_d4(links, lattice, direction, max_sep)

    L = lattice.L
    if max_sep is None:
        max_sep = L // 2

    # Compute Polyakov loop traces at each site
    # Group by one of the perpendicular directions for correlation
    traces = _polyakov_product_along_dir(
        links, lattice.edge_sites, lattice.n_edges,
        lattice.site_coords, lattice.L, direction)

    # Reshape into (L, L) grid of perpendicular positions
    poly_grid = traces.reshape(L, L)

    # Correlator along the first perpendicular direction
    C = np.zeros(max_sep + 1)
    for r in range(max_sep + 1):
        corr = 0.0
        count = 0
        for x in range(L):
            for y in range(L):
                xr = (x + r) % L
                corr += poly_grid[x, y] * poly_grid[xr, y]
                count += 1
        C[r] = corr / count

    # Subtract disconnected part
    mean_p = np.mean(traces)
    C -= mean_p ** 2

    return C


def correlator_polyakov_d4(links, lattice, direction=0, max_sep=None):
    """Compute Polyakov loop correlator on D4 lattice.

    Groups Polyakov traces by position along a perpendicular direction
    and computes C(r) = <P(0)P(r)*> - <P>^2.
    """
    L = lattice.L
    if max_sep is None:
        max_sep = L // 2

    path_edges, path_dirs = lattice.polyakov_paths[direction]
    n_paths, n_steps = path_edges.shape
    traces = _polyakov_product_d4_jit(
        links, path_edges, path_dirs, n_paths, n_steps)

    # Pick a perpendicular direction for correlation
    perp = 0 if direction != 0 else 1

    # Group traces by perpendicular coordinate
    # Starting sites are those with coord[direction] == 0
    starts = sorted([i for i in range(lattice.N)
                     if lattice.site_coords[i, direction] == 0])

    # Build mapping: perp coord -> list of traces
    perp_bins = {}
    for p_idx, site_idx in enumerate(starts):
        cp = lattice.site_coords[site_idx, perp]
        if cp not in perp_bins:
            perp_bins[cp] = []
        perp_bins[cp].append(traces[p_idx])

    # Average within each perpendicular slice
    perp_vals = sorted(perp_bins.keys())
    n_perp = len(perp_vals)
    avg_by_perp = np.zeros(n_perp)
    for i, cp in enumerate(perp_vals):
        avg_by_perp[i] = np.mean(perp_bins[cp])

    # Correlator
    C = np.zeros(max_sep + 1)
    for r in range(max_sep + 1):
        corr = 0.0
        for i in range(n_perp):
            ir = (i + r) % n_perp
            corr += avg_by_perp[i] * avg_by_perp[ir]
        C[r] = corr / n_perp

    mean_p = np.mean(traces)
    C -= mean_p ** 2

    return C


def extract_mass_gap(correlator):
    """Extract effective mass from correlator via log ratio.

    m_eff(r) = -ln(C(r+1) / C(r))

    Only computes where both C(r) and C(r+1) are positive.

    Returns: array of m_eff values (may contain nan).
    """
    n = len(correlator) - 1
    m_eff = np.full(n, np.nan)
    for r in range(n):
        if correlator[r] > 0 and correlator[r + 1] > 0:
            m_eff[r] = -np.log(correlator[r + 1] / correlator[r])
    return m_eff


def jackknife_error(time_series, n_bins=20):
    """Compute jackknife error estimate for the mean of a time series.

    Bins the data to reduce autocorrelation effects.

    Parameters:
        time_series: 1D array of measurements
        n_bins: number of jackknife bins

    Returns: (mean, error)
    """
    data = np.asarray(time_series)
    n = len(data)
    if n < n_bins:
        n_bins = max(2, n // 2)

    bin_size = n // n_bins
    if bin_size < 1:
        return np.mean(data), np.std(data) / np.sqrt(max(n, 1))

    # Bin averages
    binned = np.zeros(n_bins)
    for b in range(n_bins):
        start = b * bin_size
        end = start + bin_size
        binned[b] = np.mean(data[start:end])

    full_mean = np.mean(binned)

    # Jackknife resampling
    jack_means = np.zeros(n_bins)
    for b in range(n_bins):
        mask = np.ones(n_bins, dtype=np.bool_)
        mask[b] = False
        jack_means[b] = np.mean(binned[mask])

    # Jackknife variance
    var = (n_bins - 1) / n_bins * np.sum((jack_means - full_mean) ** 2)
    return full_mean, np.sqrt(var)


# =============================================================================
# Square-plaquette observables (Z^4 hypercubic lattice)
# =============================================================================

@njit(cache=True)
def average_plaquette_square(links, face_edges, face_dirs, n_faces):
    """Compute average plaquette for square (4-edge) faces: <(1/3) Re Tr(W)>.

    The Wilson loop around each square face is:
        W_f = link(e0,d0) @ link(e1,d1) @ link(e2,d2) @ link(e3,d3)

    Returns: float in approximately [-1/3, 1].
    """
    plaq_sum = 0.0

    for f_idx in range(n_faces):
        e0 = face_edges[f_idx, 0]
        e1 = face_edges[f_idx, 1]
        e2 = face_edges[f_idx, 2]
        e3 = face_edges[f_idx, 3]
        d0 = face_dirs[f_idx, 0]
        d1 = face_dirs[f_idx, 1]
        d2 = face_dirs[f_idx, 2]
        d3 = face_dirs[f_idx, 3]

        if d0 == 1:
            L0 = links[e0]
        else:
            L0 = su3_ops.mat3x3_dag(links[e0])
        if d1 == 1:
            L1 = links[e1]
        else:
            L1 = su3_ops.mat3x3_dag(links[e1])
        if d2 == 1:
            L2 = links[e2]
        else:
            L2 = su3_ops.mat3x3_dag(links[e2])
        if d3 == 1:
            L3 = links[e3]
        else:
            L3 = su3_ops.mat3x3_dag(links[e3])

        W = su3_ops.mat3x3_mul(
            su3_ops.mat3x3_mul(su3_ops.mat3x3_mul(L0, L1), L2), L3)
        plaq_sum += su3_ops.mat3x3_trace(W).real / 3.0

    return plaq_sum / n_faces
