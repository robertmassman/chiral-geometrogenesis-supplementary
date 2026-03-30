"""
D4 Root Lattice Geometry Builder
==================================

Constructs the 4-dimensional D4 root lattice with periodic boundary
conditions, producing flat Numba-friendly arrays for efficient
Monte Carlo simulation.

The D4 lattice is the set of points (x1,x2,x3,x4) in Z^4 with
x1+x2+x3+x4 even. It is the natural 4D extension of the FCC (D3)
lattice and has:

    N = L^4 / 2 sites        (half of the hypercubic lattice)
    12N edges                 (24 NN / 2 per site)
    32N triangular faces      (elementary plaquettes)

Each site has 24 nearest neighbors at distance sqrt(2), given by
the vectors +/- e_i +/- e_j for 1 <= i < j <= 4.

The D4 lattice has fourth-moment isotropy, eliminating O(a^2)
rotational artifacts that plague hypercubic lattices.
"""

import numpy as np
from numba import njit

# 24 nearest-neighbor offsets: +/- e_i +/- e_j for i < j
_offsets = []
for i in range(4):
    for j in range(i + 1, 4):
        for si in (+1, -1):
            for sj in (+1, -1):
                v = [0, 0, 0, 0]
                v[i] = si
                v[j] = sj
                _offsets.append(v)
NN_OFFSETS_D4 = np.array(_offsets, dtype=np.int32)
assert NN_OFFSETS_D4.shape == (24, 4)


class D4Lattice:
    """D4 root lattice with precomputed geometry arrays.

    Attributes:
        L: linear size (must be even, >= 4)
        N: total sites = L^4 / 2
        dim: spatial dimension = 4
        n_edges: total edges = 12*N
        n_faces: total triangular faces = 32*N
        site_coords: int32[N, 4] coordinates
        neighbor_table: int32[N, 24] neighbor site indices
        edge_sites: int32[n_edges, 2] (i, j) with i < j
        edge_index: dict (i, j) -> edge index
        face_edges: int32[n_faces, 3] edge indices per triangle
        face_dirs: int8[n_faces, 3] +1/-1 orientation per edge
        edge_faces: int32[n_edges, 8] face indices per edge (padded with -1)
        edge_n_faces: int32[n_edges] actual face count per edge
        polyakov_paths: dict direction -> (path_edges, path_dirs) arrays
    """

    def __init__(self, L):
        if L < 4:
            raise ValueError(
                f"L must be >= 4 for correct D4 topology. Got L={L}.")
        if L % 2 != 0:
            raise ValueError(
                f"L must be even for D4 lattice. Got L={L}.")
        self.L = L
        self.N = L ** 4 // 2
        self.dim = 4
        self._build()
        self._verify()

    def _coord_to_index(self, x):
        """Convert 4D coordinates to site index.

        Sites have x1+x2+x3+x4 even. We enumerate by looping over
        x1, x2, x3 and choosing x4 with the correct parity.
        """
        L = self.L
        x1 = x[0] % L
        x2 = x[1] % L
        x3 = x[2] % L
        x4 = x[3] % L
        # Index: flatten (x1, x2, x3) and then x4 // 2
        # x4 steps by 2 for given parity
        parity_needed = (x1 + x2 + x3) % 2
        # Ensure x4 has correct parity
        assert x4 % 2 == parity_needed, (
            f"coord {(x1,x2,x3,x4)} has wrong parity sum")
        return ((x1 * L + x2) * L + x3) * (L // 2) + x4 // 2

    def _index_to_coord(self, idx):
        """Convert site index back to 4D coordinates."""
        L = self.L
        half_L = L // 2
        x4_half = idx % half_L
        rem = idx // half_L
        x3 = rem % L
        rem = rem // L
        x2 = rem % L
        x1 = rem // L
        parity_needed = (x1 + x2 + x3) % 2
        x4 = x4_half * 2 + parity_needed
        return np.array([x1, x2, x3, x4], dtype=np.int32)

    def _min_image_offset(self, a_idx, b_idx):
        """Compute minimum image displacement from site a to site b."""
        L = self.L
        ca = self.site_coords[a_idx]
        cb = self.site_coords[b_idx]
        delta = np.zeros(4, dtype=np.int32)
        for k in range(4):
            d = int((cb[k] - ca[k]) % L)
            if d > L // 2:
                d -= L
            delta[k] = d
        return delta

    def _build(self):
        L = self.L
        N = self.N

        # Site coordinates
        self.site_coords = np.zeros((N, 4), dtype=np.int32)
        idx = 0
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    parity_needed = (x1 + x2 + x3) % 2
                    for x4 in range(parity_needed, L, 2):
                        self.site_coords[idx] = [x1, x2, x3, x4]
                        idx += 1
        assert idx == N

        # Build coord -> index lookup for fast neighbor finding
        coord_to_idx = {}
        for i in range(N):
            c = tuple(self.site_coords[i])
            coord_to_idx[c] = i

        # Neighbor table
        self.neighbor_table = np.zeros((N, 24), dtype=np.int32)
        for i in range(N):
            c = self.site_coords[i]
            for k in range(24):
                nc = np.array([
                    (c[0] + NN_OFFSETS_D4[k, 0]) % L,
                    (c[1] + NN_OFFSETS_D4[k, 1]) % L,
                    (c[2] + NN_OFFSETS_D4[k, 2]) % L,
                    (c[3] + NN_OFFSETS_D4[k, 3]) % L,
                ], dtype=np.int32)
                self.neighbor_table[i, k] = coord_to_idx[tuple(nc)]

        # Build edges (undirected: i < j)
        edge_set = set()
        for i in range(N):
            for k in range(24):
                nb = self.neighbor_table[i, k]
                a, b = min(i, nb), max(i, nb)
                edge_set.add((a, b))

        edge_list = sorted(edge_set)
        self.n_edges = len(edge_list)
        self.edge_sites = np.array(edge_list, dtype=np.int32)
        self.edge_index = {(e[0], e[1]): k for k, e in enumerate(edge_list)}

        # Build adjacency for triangle finding
        adj = [set() for _ in range(N)]
        for i in range(N):
            for k in range(24):
                adj[i].add(self.neighbor_table[i, k])

        # Find triangular faces
        # Filter collinear triples using Gram determinant in 4D:
        # |d12|^2 * |d13|^2 - (d12 . d13)^2 == 0 means collinear
        face_set = set()
        for v1 in range(N):
            for v2 in adj[v1]:
                if v2 <= v1:
                    continue
                for v3 in adj[v1] & adj[v2]:
                    if v3 <= v2:
                        continue
                    d12 = self._min_image_offset(v1, v2)
                    d13 = self._min_image_offset(v1, v3)
                    # Gram determinant for collinearity in 4D
                    dot_12_12 = int(np.dot(d12, d12))
                    dot_13_13 = int(np.dot(d13, d13))
                    dot_12_13 = int(np.dot(d12, d13))
                    gram_det = dot_12_12 * dot_13_13 - dot_12_13 ** 2
                    if gram_det == 0:
                        continue  # collinear, skip
                    face_set.add((v1, v2, v3))

        face_list = sorted(face_set)
        self.n_faces = len(face_list)

        # Build face_edges and face_dirs
        self.face_edges = np.zeros((self.n_faces, 3), dtype=np.int32)
        self.face_dirs = np.zeros((self.n_faces, 3), dtype=np.int8)

        for f_idx, (a, b, c) in enumerate(face_list):
            e_ab = self.edge_index[(a, b)]
            e_bc = self.edge_index[(b, c)]
            e_ac = self.edge_index[(a, c)]

            self.face_edges[f_idx, 0] = e_ab
            self.face_edges[f_idx, 1] = e_bc
            self.face_edges[f_idx, 2] = e_ac

            self.face_dirs[f_idx, 0] = +1   # a -> b
            self.face_dirs[f_idx, 1] = +1   # b -> c
            self.face_dirs[f_idx, 2] = -1   # c -> a (edge stored as a,c)

        # Build edge_faces
        edge_face_list = [[] for _ in range(self.n_edges)]
        for f_idx in range(self.n_faces):
            for k in range(3):
                e_idx = self.face_edges[f_idx, k]
                edge_face_list[e_idx].append(f_idx)

        max_faces_per_edge = max(len(fl) for fl in edge_face_list) if edge_face_list else 0
        self.edge_faces = np.full(
            (self.n_edges, max_faces_per_edge), -1, dtype=np.int32)
        self.edge_n_faces = np.zeros(self.n_edges, dtype=np.int32)
        for e_idx in range(self.n_edges):
            faces = edge_face_list[e_idx]
            self.edge_n_faces[e_idx] = len(faces)
            for k, f in enumerate(faces):
                self.edge_faces[e_idx, k] = f

        # Build Polyakov zigzag paths
        self.polyakov_paths = {}
        for d in range(4):
            self.polyakov_paths[d] = self._build_polyakov_paths(d)

    def _build_polyakov_paths(self, direction):
        """Build zigzag Polyakov loop paths for a given direction.

        On D4, there are no links along a single axis direction
        (NN vectors are +/- e_i +/- e_j). To wrap around direction d
        by L, we use zigzag paths: alternate steps of (e_d + e_k) and
        (e_d - e_k) for some auxiliary direction k != d.

        Each pair of steps advances by 2 in direction d and 0 in
        direction k. After L/2 pairs (L steps total), we wrap by L
        in direction d and return to the same transverse position.

        Returns:
            (path_edges, path_dirs): arrays of shape (n_paths, L)
            where n_paths = N // L = L^3 / 2 (number of distinct
            transverse positions).
        """
        L = self.L
        # Pick auxiliary direction: first available != direction
        aux = 0 if direction != 0 else 1

        n_paths = self.N // L  # L^3 / 2 distinct transverse positions

        # Starting sites: all D4 sites with coord[direction] == 0.
        # For any d, sites at coord[d]=0 need (sum of other coords) even,
        # giving exactly L^3/2 = N/L sites.
        starts = sorted([i for i in range(self.N)
                         if self.site_coords[i, direction] == 0])
        assert len(starts) == n_paths, (
            f"Expected {n_paths} Polyakov starts, got {len(starts)}")

        path_edges = np.zeros((n_paths, L), dtype=np.int32)
        path_dirs = np.zeros((n_paths, L), dtype=np.int8)

        for p, start in enumerate(starts):
            current = start
            for step in range(L):
                # Alternate between (e_d + e_aux) and (e_d - e_aux)
                offset = np.zeros(4, dtype=np.int32)
                offset[direction] = 1
                if step % 2 == 0:
                    offset[aux] = 1
                else:
                    offset[aux] = -1

                next_coord = np.array([
                    (self.site_coords[current, k] + offset[k]) % L
                    for k in range(4)
                ], dtype=np.int32)

                # Find next site index
                next_idx = self._coord_to_index(next_coord)

                # Find edge
                i, j = min(current, next_idx), max(current, next_idx)
                e_idx = self.edge_index[(i, j)]
                path_edges[p, step] = e_idx
                path_dirs[p, step] = +1 if current == i else -1

                current = next_idx

            # Verify path closure: current should equal start
            assert current == start, (
                f"Polyakov path {p} dir={direction} did not close: "
                f"ended at site {current}, expected {start}")

        return path_edges, path_dirs

    def _verify(self):
        """Run structural assertions on the lattice."""
        N = self.N

        # Every site has 24 neighbors
        for i in range(N):
            nbs = set(self.neighbor_table[i])
            assert len(nbs) == 24, (
                f"Site {i} has {len(nbs)} neighbors, expected 24")

        # Edge count
        assert self.n_edges == 12 * N, (
            f"n_edges = {self.n_edges}, expected {12 * N}")

        # Face count
        assert self.n_faces == 32 * N, (
            f"n_faces = {self.n_faces}, expected {32 * N}")

        # Every edge in exactly 8 triangles
        for e_idx in range(self.n_edges):
            nf = self.edge_n_faces[e_idx]
            assert nf == 8, (
                f"Edge {e_idx} in {nf} faces, expected 8")

        # Euler characteristic: V - E + F = N - 12N + 32N = 21N
        euler = N - self.n_edges + self.n_faces
        assert euler == 21 * N, (
            f"Euler char = {euler}, expected {21 * N}")

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
        return (f"D4 Lattice L={self.L}: "
                f"N={self.N} sites, {self.n_edges} edges, "
                f"{self.n_faces} faces")
