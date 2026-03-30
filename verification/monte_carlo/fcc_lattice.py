"""
FCC Lattice Geometry Builder
==============================

Constructs the face-centered cubic lattice with periodic boundary
conditions, producing flat Numba-friendly arrays for efficient
Monte Carlo simulation.

An FCC lattice with L^3 primitive cells has:
    N = L^3 sites       (1 per cell)
    6N edges             (6 per cell, 12 NN / 2)
    8N triangular faces  (8 per cell)

Each site has 12 nearest neighbors. The elementary plaquettes are
triangles (faces of tetrahedra and octahedra in the FCC Voronoi
decomposition).

The 12 NN offsets in primitive-cell fractional coordinates:
    +/- e1, +/- e2, +/- e3,
    +/- (e1-e2), +/- (e1-e3), +/- (e2-e3)
"""

import numpy as np
from numba import njit

# 12 nearest-neighbor offsets in fractional coordinates of primitive cell
NN_OFFSETS = np.array([
    [1, 0, 0], [-1, 0, 0],
    [0, 1, 0], [0, -1, 0],
    [0, 0, 1], [0, 0, -1],
    [1, -1, 0], [-1, 1, 0],
    [1, 0, -1], [-1, 0, 1],
    [0, 1, -1], [0, -1, 1],
], dtype=np.int32)


class FCCLattice:
    """FCC lattice with precomputed geometry arrays.

    Attributes:
        L: linear size
        N: total sites = L^3
        n_edges: total edges = 6*N
        n_faces: total triangular faces = 8*N
        site_coords: int32[N, 3] coordinates
        neighbor_table: int32[N, 12] neighbor site indices
        edge_sites: int32[n_edges, 2] (i, j) with i < j
        edge_index: dict (i, j) -> edge index
        face_edges: int32[n_faces, 3] edge indices per triangle
        face_dirs: int8[n_faces, 3] +1/-1 orientation per edge
        edge_faces: list of lists, face indices per edge
    """

    def __init__(self, L):
        if L < 3:
            raise ValueError(
                f"L must be >= 3 for correct FCC topology "
                f"(L=2 has degenerate NN structure). Got L={L}.")
        self.L = L
        self.N = L ** 3
        self.dim = 3
        self._build()
        self._verify()

    def _coord_to_index(self, n1, n2, n3):
        L = self.L
        return ((n1 % L) * L + (n2 % L)) * L + (n3 % L)

    def _min_image_offset(self, a_idx, b_idx):
        """Compute minimum image displacement from site a to site b."""
        L = self.L
        ca = self.site_coords[a_idx]
        cb = self.site_coords[b_idx]
        delta = np.zeros(3, dtype=np.int32)
        for k in range(3):
            d = int((cb[k] - ca[k]) % L)
            if d > L // 2:
                d -= L
            delta[k] = d
        return delta

    def _build(self):
        L = self.L
        N = self.N

        # Site coordinates
        self.site_coords = np.zeros((N, 3), dtype=np.int32)
        for n1 in range(L):
            for n2 in range(L):
                for n3 in range(L):
                    idx = self._coord_to_index(n1, n2, n3)
                    self.site_coords[idx] = [n1, n2, n3]

        # Neighbor table
        self.neighbor_table = np.zeros((N, 12), dtype=np.int32)
        for idx in range(N):
            n1, n2, n3 = self.site_coords[idx]
            for k, (d1, d2, d3) in enumerate(NN_OFFSETS):
                nb = self._coord_to_index(n1 + d1, n2 + d2, n3 + d3)
                self.neighbor_table[idx, k] = nb

        # Build edges (undirected: i < j)
        edge_set = set()
        for idx in range(N):
            for k in range(12):
                nb = self.neighbor_table[idx, k]
                i, j = min(idx, nb), max(idx, nb)
                edge_set.add((i, j))

        edge_list = sorted(edge_set)
        self.n_edges = len(edge_list)
        self.edge_sites = np.array(edge_list, dtype=np.int32)
        self.edge_index = {(e[0], e[1]): k for k, e in enumerate(edge_list)}

        # Build adjacency for triangle finding
        adj = [set() for _ in range(N)]
        for idx in range(N):
            for k in range(12):
                adj[idx].add(self.neighbor_table[idx, k])

        # Find triangular faces
        # A triangle is a set of 3 mutually adjacent vertices.
        # For L=3, we must filter out collinear wrap-around triangles
        # where 3 sites lie along the same NN direction and wrap around
        # the periodic lattice (3d = 0 mod L for NN offset d).
        face_set = set()
        for v1 in range(N):
            for v2 in adj[v1]:
                if v2 <= v1:
                    continue
                for v3 in adj[v1] & adj[v2]:
                    if v3 <= v2:
                        continue
                    # Check for collinearity using minimum image offsets
                    d12 = self._min_image_offset(v1, v2)
                    d13 = self._min_image_offset(v1, v3)
                    cross = np.cross(d12, d13)
                    if cross[0] == 0 and cross[1] == 0 and cross[2] == 0:
                        continue  # collinear wrap-around, skip
                    face_set.add((v1, v2, v3))

        face_list = sorted(face_set)
        self.n_faces = len(face_list)

        # Build face_edges and face_dirs
        # For triangle (a, b, c) with a < b < c,
        # traversal order: a->b->c->a
        # edges are (a,b), (b,c), (a,c)
        # directions: (a,b)=+1, (b,c)=+1, (a,c)=-1 (reversed: c->a)
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

        # Build edge_faces: which faces each edge belongs to
        self._edge_face_list = [[] for _ in range(self.n_edges)]
        for f_idx in range(self.n_faces):
            for k in range(3):
                e_idx = self.face_edges[f_idx, k]
                self._edge_face_list[e_idx].append(f_idx)

        # Convert to flat arrays for Numba: edge_face_idx[e] gives the
        # 4 face indices (padded with -1 if fewer)
        max_faces_per_edge = max(len(fl) for fl in self._edge_face_list)
        self.edge_faces = np.full((self.n_edges, max_faces_per_edge), -1, dtype=np.int32)
        self.edge_n_faces = np.zeros(self.n_edges, dtype=np.int32)
        for e_idx in range(self.n_edges):
            faces = self._edge_face_list[e_idx]
            self.edge_n_faces[e_idx] = len(faces)
            for k, f in enumerate(faces):
                self.edge_faces[e_idx, k] = f

    def _verify(self):
        """Run structural assertions on the lattice."""
        N = self.N
        # Every site has 12 neighbors
        for idx in range(N):
            nbs = set(self.neighbor_table[idx])
            assert len(nbs) == 12, f"Site {idx} has {len(nbs)} neighbors, expected 12"

        # Edge count
        assert self.n_edges == 6 * N, (
            f"n_edges = {self.n_edges}, expected {6 * N}")

        # Face count
        assert self.n_faces == 8 * N, (
            f"n_faces = {self.n_faces}, expected {8 * N}")

        # Every edge in exactly 4 triangles
        for e_idx in range(self.n_edges):
            nf = self.edge_n_faces[e_idx]
            assert nf == 4, (
                f"Edge {e_idx} in {nf} faces, expected 4")

        # Euler characteristic of 2-skeleton: V - E + F = 3N
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
        return (f"FCC Lattice L={self.L}: "
                f"N={self.N} sites, {self.n_edges} edges, "
                f"{self.n_faces} faces")
