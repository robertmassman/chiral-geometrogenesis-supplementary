"""
Z^4 Hypercubic Lattice Geometry Builder
========================================

Constructs the standard 4-dimensional hypercubic lattice with periodic
boundary conditions, producing flat Numba-friendly arrays for efficient
Monte Carlo simulation.

The Z^4 lattice is the set of all points (x1,x2,x3,x4) in Z^4 mod L.
It is the standard lattice used in conventional lattice QCD and has:

    N = L^4 sites
    4N edges                 (one per direction per site)
    6N square plaquettes     (one per mu<nu plane per site)

Each site has 8 nearest neighbors at distance 1, given by +/- e_mu
for mu = 0,1,2,3.

The Z^4 lattice uses square plaquettes (4 edges per face), in contrast
to the D4 lattice which uses triangular plaquettes (3 edges per face).
"""

import numpy as np
from numba import njit

# 8 nearest-neighbor offsets: +/- e_mu for mu = 0,1,2,3
_offsets = []
for mu in range(4):
    for sign in (+1, -1):
        v = [0, 0, 0, 0]
        v[mu] = sign
        _offsets.append(v)
NN_OFFSETS_Z4 = np.array(_offsets, dtype=np.int32)
assert NN_OFFSETS_Z4.shape == (8, 4)


class Z4Lattice:
    """Z^4 hypercubic lattice with precomputed geometry arrays.

    Attributes:
        L: linear size (must be >= 4)
        N: total sites = L^4
        dim: spatial dimension = 4
        n_edges: total edges = 4*N
        n_faces: total square faces = 6*N
        site_coords: int32[N, 4] coordinates
        neighbor_table: int32[N, 8] neighbor site indices
        edge_sites: int32[n_edges, 2] (i, j) with i < j
        edge_index: dict (i, j) -> edge index
        face_edges: int32[n_faces, 4] edge indices per square
        face_dirs: int8[n_faces, 4] +1/-1 orientation per edge
        edge_faces: int32[n_edges, max_f] face indices per edge (padded with -1)
        edge_n_faces: int32[n_edges] actual face count per edge
        polyakov_paths: dict direction -> (path_edges, path_dirs) arrays
    """

    def __init__(self, L):
        if L < 4:
            raise ValueError(
                f"L must be >= 4 for correct Z4 topology. Got L={L}.")
        self.L = L
        self.N = L ** 4
        self.dim = 4
        self._build()
        self._verify()

    def _coord_to_index(self, x):
        """Convert 4D coordinates to site index (row-major order)."""
        L = self.L
        x0 = x[0] % L
        x1 = x[1] % L
        x2 = x[2] % L
        x3 = x[3] % L
        return ((x0 * L + x1) * L + x2) * L + x3

    def _index_to_coord(self, idx):
        """Convert site index back to 4D coordinates."""
        L = self.L
        x3 = idx % L
        rem = idx // L
        x2 = rem % L
        rem = rem // L
        x1 = rem % L
        x0 = rem // L
        return np.array([x0, x1, x2, x3], dtype=np.int32)

    def _build(self):
        L = self.L
        N = self.N

        # Site coordinates
        self.site_coords = np.zeros((N, 4), dtype=np.int32)
        idx = 0
        for x0 in range(L):
            for x1 in range(L):
                for x2 in range(L):
                    for x3 in range(L):
                        self.site_coords[idx] = [x0, x1, x2, x3]
                        idx += 1
        assert idx == N

        # Build coord -> index lookup
        coord_to_idx = {}
        for i in range(N):
            c = tuple(self.site_coords[i])
            coord_to_idx[c] = i

        # Neighbor table (8 neighbors per site)
        self.neighbor_table = np.zeros((N, 8), dtype=np.int32)
        for i in range(N):
            c = self.site_coords[i]
            for k in range(8):
                nc = tuple(
                    (c[d] + NN_OFFSETS_Z4[k, d]) % L for d in range(4)
                )
                self.neighbor_table[i, k] = coord_to_idx[nc]

        # Build edges: for each site, one edge per positive direction mu
        # Edge mu at site s connects s to s + e_mu.
        # We store edges as (i, j) with i < j.
        edge_set = set()
        for i in range(N):
            for k in range(8):
                nb = self.neighbor_table[i, k]
                a, b = min(i, nb), max(i, nb)
                edge_set.add((a, b))

        edge_list = sorted(edge_set)
        self.n_edges = len(edge_list)
        self.edge_sites = np.array(edge_list, dtype=np.int32)
        self.edge_index = {(e[0], e[1]): k for k, e in enumerate(edge_list)}

        # Build square faces (plaquettes)
        # For each site s, for each pair mu < nu, the plaquette is:
        #   s -> s+e_mu -> s+e_mu+e_nu -> s+e_nu -> s
        # Traversal: edge(s, s+e_mu) forward, edge(s+e_mu, s+e_mu+e_nu) forward,
        #            edge(s+e_nu, s+e_mu+e_nu) backward, edge(s, s+e_nu) backward
        face_list = []
        for s in range(N):
            c = self.site_coords[s]
            for mu in range(4):
                for nu in range(mu + 1, 4):
                    # Four corners
                    c_mu = tuple((c[d] + (1 if d == mu else 0)) % L
                                 for d in range(4))
                    c_nu = tuple((c[d] + (1 if d == nu else 0)) % L
                                 for d in range(4))
                    c_mu_nu = tuple(
                        (c[d] + (1 if d == mu else 0)
                             + (1 if d == nu else 0)) % L
                        for d in range(4))

                    s0 = coord_to_idx[tuple(c)]
                    s_mu = coord_to_idx[c_mu]
                    s_nu = coord_to_idx[c_nu]
                    s_mu_nu = coord_to_idx[c_mu_nu]

                    face_list.append((s0, s_mu, s_mu_nu, s_nu))

        self.n_faces = len(face_list)

        # Build face_edges[n_faces, 4] and face_dirs[n_faces, 4]
        # Traversal order: s0->s_mu, s_mu->s_mu_nu, s_mu_nu->s_nu, s_nu->s0
        # But we store edges as (min, max), so direction depends on order.
        self.face_edges = np.zeros((self.n_faces, 4), dtype=np.int32)
        self.face_dirs = np.zeros((self.n_faces, 4), dtype=np.int8)

        for f_idx, (s0, s_mu, s_mu_nu, s_nu) in enumerate(face_list):
            # Edge 0: s0 -> s_mu
            i, j = min(s0, s_mu), max(s0, s_mu)
            self.face_edges[f_idx, 0] = self.edge_index[(i, j)]
            self.face_dirs[f_idx, 0] = +1 if s0 < s_mu else -1

            # Edge 1: s_mu -> s_mu_nu
            i, j = min(s_mu, s_mu_nu), max(s_mu, s_mu_nu)
            self.face_edges[f_idx, 1] = self.edge_index[(i, j)]
            self.face_dirs[f_idx, 1] = +1 if s_mu < s_mu_nu else -1

            # Edge 2: s_mu_nu -> s_nu (backward along mu direction)
            i, j = min(s_mu_nu, s_nu), max(s_mu_nu, s_nu)
            self.face_edges[f_idx, 2] = self.edge_index[(i, j)]
            self.face_dirs[f_idx, 2] = +1 if s_mu_nu < s_nu else -1

            # Edge 3: s_nu -> s0 (backward along nu direction)
            i, j = min(s_nu, s0), max(s_nu, s0)
            self.face_edges[f_idx, 3] = self.edge_index[(i, j)]
            self.face_dirs[f_idx, 3] = +1 if s_nu < s0 else -1

        # Build edge_faces
        edge_face_list = [[] for _ in range(self.n_edges)]
        for f_idx in range(self.n_faces):
            for k in range(4):
                e_idx = self.face_edges[f_idx, k]
                edge_face_list[e_idx].append(f_idx)

        max_faces_per_edge = max(
            len(fl) for fl in edge_face_list) if edge_face_list else 0
        self.edge_faces = np.full(
            (self.n_edges, max_faces_per_edge), -1, dtype=np.int32)
        self.edge_n_faces = np.zeros(self.n_edges, dtype=np.int32)
        for e_idx in range(self.n_edges):
            faces = edge_face_list[e_idx]
            self.edge_n_faces[e_idx] = len(faces)
            for k, f in enumerate(faces):
                self.edge_faces[e_idx, k] = f

        # Build Polyakov paths (straight lines — no zigzag needed on Z^4)
        self.polyakov_paths = {}
        for d in range(4):
            self.polyakov_paths[d] = self._build_polyakov_paths(d)

    def _build_polyakov_paths(self, direction):
        """Build straight Polyakov loop paths for a given direction.

        On Z^4, links exist along single axis directions, so Polyakov
        loops are simply L links along the same direction. No zigzag
        needed (unlike D4).

        Returns:
            (path_edges, path_dirs): arrays of shape (n_paths, L)
            where n_paths = N // L = L^3 (one per transverse position).
        """
        L = self.L
        n_paths = self.N // L  # L^3

        # Starting sites: all sites with coord[direction] == 0
        starts = sorted([i for i in range(self.N)
                         if self.site_coords[i, direction] == 0])
        assert len(starts) == n_paths, (
            f"Expected {n_paths} Polyakov starts, got {len(starts)}")

        path_edges = np.zeros((n_paths, L), dtype=np.int32)
        path_dirs = np.zeros((n_paths, L), dtype=np.int8)

        for p, start in enumerate(starts):
            current = start
            for step in range(L):
                # Step along +direction
                offset = np.zeros(4, dtype=np.int32)
                offset[direction] = 1
                next_coord = tuple(
                    (self.site_coords[current, k] + offset[k]) % L
                    for k in range(4)
                )
                next_idx = self._coord_to_index(next_coord)

                # Find edge
                i, j = min(current, next_idx), max(current, next_idx)
                e_idx = self.edge_index[(i, j)]
                path_edges[p, step] = e_idx
                path_dirs[p, step] = +1 if current == i else -1

                current = next_idx

            # Verify closure
            assert current == start, (
                f"Polyakov path {p} dir={direction} did not close: "
                f"ended at site {current}, expected {start}")

        return path_edges, path_dirs

    def _verify(self):
        """Run structural assertions on the lattice."""
        N = self.N

        # Every site has 8 neighbors
        for i in range(N):
            nbs = set(self.neighbor_table[i])
            assert len(nbs) == 8, (
                f"Site {i} has {len(nbs)} neighbors, expected 8")

        # Edge count: 4N
        assert self.n_edges == 4 * N, (
            f"n_edges = {self.n_edges}, expected {4 * N}")

        # Face count: 6N
        assert self.n_faces == 6 * N, (
            f"n_faces = {self.n_faces}, expected {6 * N}")

        # Every edge in exactly 6 faces
        for e_idx in range(self.n_edges):
            nf = self.edge_n_faces[e_idx]
            assert nf == 6, (
                f"Edge {e_idx} in {nf} faces, expected 6")

        # Euler characteristic check for 4-torus:
        # V - E + F = N - 4N + 6N = 3N
        euler = N - self.n_edges + self.n_faces
        assert euler == 3 * N, (
            f"Euler char = {euler}, expected {3 * N}")

    def init_links_cold(self):
        """Initialize all links to identity (cold start)."""
        from . import su3_ops
        links = np.zeros((self.n_edges, 3, 3), dtype=np.complex128)
        I = su3_ops.mat3x3_eye()
        for e in range(self.n_edges):
            links[e] = I
        return links

    def init_links_hot(self):
        """Initialize all links to random SU(3) (hot start)."""
        from . import su3_ops
        links = np.zeros((self.n_edges, 3, 3), dtype=np.complex128)
        for e in range(self.n_edges):
            links[e] = su3_ops.random_su3_haar()
        return links

    def summary(self):
        """Return a summary string."""
        return (f"Z4 Lattice L={self.L}: "
                f"N={self.N} sites, {self.n_edges} edges, "
                f"{self.n_faces} faces")
