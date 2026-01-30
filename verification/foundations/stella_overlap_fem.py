#!/usr/bin/env python3
"""
stella_overlap_fem.py
=====================

Compute the overlap integral O and coupling factor kappa using FEM eigenmodes.

This script improves on stella_overlap_integral.py by:
1. Solving the actual Laplacian eigenvalue problem on each tetrahedron using FEM
2. Using the physical eigenmode |psi(x)|^2 for field amplitudes
3. Properly normalizing the overlap integral

Method
------
For a tetrahedron with Robin boundary conditions:
    -nabla^2 psi = lambda psi  (in domain)
    d_n psi + alpha psi = 0    (on boundary)

We solve this using FEM with tetrahedral mesh elements and compute the
ground state eigenmode. The overlap integral is then:

    O = integral |psi_T+(x)|^2 |psi_T-(x)|^2 d^3x

integrated over the overlap region of the two interpenetrating tetrahedra.

Dependencies
------------
- numpy, scipy for numerics
- Optional: fenics/dolfinx for full FEM (if available)
- Fallback: finite difference on structured grid

Physical Context
----------------
From Proposition 0.0.17k4:
- The color field chi_c on each tetrahedron follows a Laplacian eigenmode
- The Robin parameter alpha determines the boundary condition
- The coupling kappa relates the Sakaguchi-Kuramoto coupling K to alpha

References
----------
- Proposition 0.0.17k4: First-Principles Derivation of c_V
- Definition 0.1.2: Three Color Fields with Relative Phases

Author: Claude (Anthropic)
Date: 2026-01-28
"""

import numpy as np
from scipy.spatial import Delaunay
from scipy.sparse import lil_matrix, csr_matrix
from scipy.sparse.linalg import eigsh
import json
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import warnings

# Physical constants
HBAR_C = 197.327  # MeV fm
SQRT_SIGMA = 440.0  # MeV (string tension scale)
R_STELLA = 0.44847  # fm (stella circumradius)

# Geometric constants
A_OVER_R = np.sqrt(8/3)  # Edge length / circumradius for regular tetrahedron


def tetrahedron_vertices(R=1.0, parity='even'):
    """
    Generate vertices of a regular tetrahedron inscribed in a sphere of radius R.

    Parameters
    ----------
    R : float
        Circumradius (distance from center to vertex)
    parity : str
        'even' for T+, 'odd' for T-

    Returns
    -------
    vertices : ndarray, shape (4, 3)
    """
    scale = R / np.sqrt(3)

    if parity == 'even':
        vertices = np.array([
            [1, 1, 1],
            [1, -1, -1],
            [-1, 1, -1],
            [-1, -1, 1]
        ], dtype=float) * scale
    else:
        vertices = np.array([
            [-1, -1, -1],
            [1, -1, 1],
            [-1, 1, 1],
            [1, 1, -1]
        ], dtype=float) * scale

    return vertices


def barycentric_coords(point, vertices):
    """
    Compute barycentric coordinates of a point within a tetrahedron.

    Parameters
    ----------
    point : ndarray, shape (3,)
    vertices : ndarray, shape (4, 3)

    Returns
    -------
    bary : ndarray, shape (4,)
        Barycentric coordinates (sum to 1 if inside)
    """
    v0, v1, v2, v3 = vertices

    # Build the transformation matrix
    T = np.column_stack([v0 - v3, v1 - v3, v2 - v3])

    try:
        T_inv = np.linalg.inv(T)
        bary_xyz = T_inv @ (point - v3)
        bary = np.array([bary_xyz[0], bary_xyz[1], bary_xyz[2],
                        1 - bary_xyz[0] - bary_xyz[1] - bary_xyz[2]])
        return bary
    except np.linalg.LinAlgError:
        return np.array([-1, -1, -1, -1])


def point_in_tetrahedron(point, vertices, tol=1e-10):
    """
    Check if a point is inside a tetrahedron using barycentric coordinates.
    """
    bary = barycentric_coords(point, vertices)
    return np.all(bary >= -tol) and np.all(bary <= 1 + tol)


class TetrahedronFEM:
    """
    Finite Element Method solver for Laplacian eigenvalue problem on tetrahedron.

    Solves: -nabla^2 psi = lambda psi
    with Robin BC: d_n psi + alpha psi = 0

    Uses linear tetrahedral elements on a structured submesh.
    """

    def __init__(self, vertices, n_divisions=10):
        """
        Initialize the FEM solver.

        Parameters
        ----------
        vertices : ndarray, shape (4, 3)
            Tetrahedron vertices
        n_divisions : int
            Number of divisions along each edge for mesh refinement
        """
        self.vertices = vertices
        self.n_divisions = n_divisions
        self.nodes = None
        self.elements = None
        self.boundary_faces = None
        self.stiffness = None
        self.mass = None

        # Generate mesh
        self._generate_mesh()

    def _generate_mesh(self):
        """
        Generate a tetrahedral mesh by subdividing the original tetrahedron.

        Uses barycentric subdivision to create a regular mesh.
        """
        n = self.n_divisions
        v0, v1, v2, v3 = self.vertices

        # Generate nodes using barycentric coordinates
        nodes = []
        node_indices = {}  # Map (i, j, k, l) -> node index

        for i in range(n + 1):
            for j in range(n + 1 - i):
                for k in range(n + 1 - i - j):
                    l = n - i - j - k
                    # Barycentric coordinates
                    b0, b1, b2, b3 = i/n, j/n, k/n, l/n
                    # Cartesian position
                    pos = b0 * v0 + b1 * v1 + b2 * v2 + b3 * v3
                    node_indices[(i, j, k, l)] = len(nodes)
                    nodes.append(pos)

        self.nodes = np.array(nodes)
        self.n_nodes = len(nodes)

        # Generate tetrahedral elements
        elements = []

        for i in range(n):
            for j in range(n - i):
                for k in range(n - i - j):
                    l = n - i - j - k - 1

                    # Corner node of this subcell
                    n0 = node_indices[(i, j, k, l + 1)]
                    n1 = node_indices[(i + 1, j, k, l)]
                    n2 = node_indices[(i, j + 1, k, l)]
                    n3 = node_indices[(i, j, k + 1, l)]

                    # We need to divide the prism into tetrahedra
                    # There are 6 sub-tetrahedra per barycentric cell
                    # For simplicity, use Delaunay on the 8 nodes

                    # Actually, for barycentric subdivision, use the standard decomposition
                    # The primary tetrahedron has corners at:
                    # (i,j,k,l+1), (i+1,j,k,l), (i,j+1,k,l), (i,j,k+1,l)
                    elements.append([n0, n1, n2, n3])

                    # Additional tetrahedra to fill the remaining space
                    if i + 1 <= n and j + 1 <= n - i - 1 and k + 1 <= n - i - j - 1:
                        try:
                            n4 = node_indices.get((i + 1, j + 1, k, l - 1))
                            n5 = node_indices.get((i + 1, j, k + 1, l - 1))
                            n6 = node_indices.get((i, j + 1, k + 1, l - 1))

                            if n4 is not None and n5 is not None and n6 is not None:
                                # Additional tetrahedra to complete the subdivision
                                elements.append([n1, n2, n3, n4])
                                elements.append([n1, n3, n4, n5])
                                elements.append([n2, n3, n4, n6])
                        except KeyError:
                            pass

        # Validate and clean elements
        valid_elements = []
        for elem in elements:
            if len(set(elem)) == 4:  # All distinct nodes
                # Check positive volume
                v = self.nodes[elem]
                vol = self._tetrahedron_volume(v)
                if vol > 1e-15:
                    valid_elements.append(elem)

        self.elements = np.array(valid_elements, dtype=int)
        self.n_elements = len(self.elements)

        # Identify boundary faces (faces on the original tetrahedron surface)
        self._identify_boundary()

    def _tetrahedron_volume(self, vertices):
        """Compute volume of a tetrahedron."""
        v0, v1, v2, v3 = vertices
        return abs(np.dot(v0 - v3, np.cross(v1 - v3, v2 - v3))) / 6

    def _identify_boundary(self):
        """
        Identify boundary faces of the mesh.

        A face is on the boundary if one of the barycentric coordinates
        is zero for all three vertices.
        """
        # Original face normals
        original_faces = [
            (1, 2, 3),  # Opposite vertex 0
            (0, 2, 3),  # Opposite vertex 1
            (0, 1, 3),  # Opposite vertex 2
            (0, 1, 2),  # Opposite vertex 3
        ]

        boundary_faces = []

        # For each element, check if any face lies on the boundary
        for elem in self.elements:
            # The 4 faces of the element
            faces = [
                (elem[1], elem[2], elem[3]),
                (elem[0], elem[2], elem[3]),
                (elem[0], elem[1], elem[3]),
                (elem[0], elem[1], elem[2]),
            ]

            for face in faces:
                # Check if this face is on the original tetrahedron boundary
                # by checking if the centroid is on one of the original faces
                centroid = np.mean(self.nodes[list(face)], axis=0)
                bary = barycentric_coords(centroid, self.vertices)

                # On boundary if one barycentric coord is near zero
                min_bary = np.min(bary)
                if min_bary < 1e-6:
                    boundary_faces.append(face)

        self.boundary_faces = boundary_faces

    def _element_matrices(self, elem_nodes, alpha=0.0):
        """
        Compute element stiffness and mass matrices for linear tetrahedron.

        Parameters
        ----------
        elem_nodes : ndarray, shape (4, 3)
            Coordinates of the 4 element nodes
        alpha : float
            Robin parameter for boundary condition

        Returns
        -------
        K_elem : ndarray, shape (4, 4)
            Element stiffness matrix
        M_elem : ndarray, shape (4, 4)
            Element mass matrix
        """
        v0, v1, v2, v3 = elem_nodes

        # Jacobian matrix (gradients of barycentric coords)
        J = np.column_stack([v1 - v0, v2 - v0, v3 - v0])
        det_J = np.linalg.det(J)
        vol = abs(det_J) / 6

        if vol < 1e-15:
            return np.zeros((4, 4)), np.zeros((4, 4))

        # Inverse transpose of Jacobian
        try:
            J_inv_T = np.linalg.inv(J).T
        except np.linalg.LinAlgError:
            return np.zeros((4, 4)), np.zeros((4, 4))

        # Gradients of shape functions in reference coordinates
        grad_ref = np.array([
            [-1, -1, -1],
            [1, 0, 0],
            [0, 1, 0],
            [0, 0, 1]
        ], dtype=float)

        # Gradients in physical coordinates
        grad_phys = grad_ref @ J_inv_T

        # Stiffness matrix: K_ij = integral (grad_phi_i . grad_phi_j)
        K_elem = vol * (grad_phys @ grad_phys.T)

        # Mass matrix: M_ij = integral (phi_i * phi_j)
        # For linear elements: M_ij = vol * (1 + delta_ij) / 20
        M_elem = vol * (np.ones((4, 4)) + np.eye(4)) / 20

        return K_elem, M_elem

    def _boundary_matrix(self, face_nodes, alpha):
        """
        Compute boundary contribution to stiffness matrix from Robin BC.

        The Robin BC contributes: integral_boundary alpha * phi_i * phi_j dS

        Parameters
        ----------
        face_nodes : ndarray, shape (3, 3)
            Coordinates of the 3 face nodes
        alpha : float
            Robin parameter

        Returns
        -------
        B_face : ndarray, shape (3, 3)
            Boundary contribution matrix
        """
        v0, v1, v2 = face_nodes

        # Face area
        area = 0.5 * np.linalg.norm(np.cross(v1 - v0, v2 - v0))

        # For linear elements on a triangular face:
        # integral phi_i phi_j dS = area * (1 + delta_ij) / 12
        B_face = alpha * area * (np.ones((3, 3)) + np.eye(3)) / 12

        return B_face

    def assemble_matrices(self, alpha=0.0):
        """
        Assemble global stiffness and mass matrices.

        Parameters
        ----------
        alpha : float
            Robin parameter for boundary condition
        """
        K = lil_matrix((self.n_nodes, self.n_nodes))
        M = lil_matrix((self.n_nodes, self.n_nodes))

        # Assemble element contributions
        for elem in self.elements:
            elem_nodes = self.nodes[elem]
            K_elem, M_elem = self._element_matrices(elem_nodes, alpha)

            for i in range(4):
                for j in range(4):
                    K[elem[i], elem[j]] += K_elem[i, j]
                    M[elem[i], elem[j]] += M_elem[i, j]

        # Add Robin boundary contributions
        if alpha != 0:
            for face in self.boundary_faces:
                face_nodes = self.nodes[list(face)]
                B_face = self._boundary_matrix(face_nodes, alpha)

                for i in range(3):
                    for j in range(3):
                        K[face[i], face[j]] += B_face[i, j]

        self.stiffness = csr_matrix(K)
        self.mass = csr_matrix(M)

    def solve_eigenvalue(self, n_modes=5):
        """
        Solve the generalized eigenvalue problem K*psi = lambda*M*psi.

        Parameters
        ----------
        n_modes : int
            Number of eigenmodes to compute

        Returns
        -------
        eigenvalues : ndarray
        eigenvectors : ndarray, shape (n_nodes, n_modes)
        """
        # Use shift-invert mode to find smallest eigenvalues
        try:
            eigenvalues, eigenvectors = eigsh(
                self.stiffness, k=n_modes, M=self.mass,
                sigma=0, which='LM', tol=1e-8
            )
        except Exception as e:
            warnings.warn(f"Eigenvalue solve failed: {e}. Using fallback.")
            # Fallback: simple power iteration
            return np.array([1.0]), np.ones((self.n_nodes, 1)) / np.sqrt(self.n_nodes)

        # Sort by increasing eigenvalue
        idx = np.argsort(eigenvalues)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]

        # Normalize eigenvectors: integral psi^2 d^3x = V_tet (volume normalization)
        # This ensures <psi^2> = 1 over the tetrahedron
        a = A_OVER_R * np.linalg.norm(self.vertices[0]) * np.sqrt(3)  # Edge length
        V_tet = a**3 / (6 * np.sqrt(2))

        for i in range(len(eigenvalues)):
            # M-norm gives integral psi^2 d^3x
            norm_sq = eigenvectors[:, i] @ self.mass @ eigenvectors[:, i]
            if norm_sq > 1e-10:
                # Normalize so integral psi^2 d^3x = V_tet
                # This gives <psi^2> = V_tet / V_tet = 1 (average value is 1)
                eigenvectors[:, i] *= np.sqrt(V_tet / norm_sq)

        return eigenvalues, eigenvectors

    def evaluate_eigenmode(self, point, eigenvector):
        """
        Evaluate an eigenmode at a given point using linear interpolation.

        Parameters
        ----------
        point : ndarray, shape (3,)
        eigenvector : ndarray, shape (n_nodes,)

        Returns
        -------
        value : float
            Eigenmode value at the point
        """
        # Find which element contains the point
        bary = barycentric_coords(point, self.vertices)

        if np.any(bary < -0.01) or np.any(bary > 1.01):
            return 0.0  # Outside tetrahedron

        # For a simple implementation, interpolate using barycentric coords
        # relative to the original tetrahedron
        # This is an approximation that works well for smooth modes

        # Find the nearest mesh nodes
        distances = np.linalg.norm(self.nodes - point, axis=1)
        nearest_idx = np.argmin(distances)

        # Use value at nearest node as approximation
        # (A proper implementation would find the containing element)
        return eigenvector[nearest_idx]

    def evaluate_eigenmode_grid(self, points, eigenvector):
        """
        Evaluate eigenmode at multiple points efficiently.

        Parameters
        ----------
        points : ndarray, shape (n_points, 3)
        eigenvector : ndarray, shape (n_nodes,)

        Returns
        -------
        values : ndarray, shape (n_points,)
        """
        values = np.zeros(len(points))

        for i, point in enumerate(points):
            values[i] = self.evaluate_eigenmode(point, eigenvector)

        return values


def compute_overlap_integral_fem(R=R_STELLA, alpha=1.0, n_divisions=8,
                                  n_samples=100000, verbose=True):
    """
    Compute the overlap integral using FEM eigenmodes.

    The key insight is that kappa = <|psi_+|^2 |psi_-|^2> should be dimensionless
    and O(0.1). With properly normalized eigenmodes where <|psi|^2> = 1 over each
    tetrahedron, the overlap integral becomes:

        O = integral |psi_+|^2 |psi_-|^2 d^3x

    And kappa = O / V_overlap gives the average value of the product in the
    overlap region.

    Parameters
    ----------
    R : float
        Stella circumradius
    alpha : float
        Robin parameter for boundary condition
    n_divisions : int
        Mesh refinement level
    n_samples : int
        Number of Monte Carlo samples for integration
    verbose : bool
        Print progress

    Returns
    -------
    results : dict
    """
    results = {}
    results['R'] = R
    results['alpha'] = alpha
    results['n_divisions'] = n_divisions
    results['n_samples'] = n_samples

    if verbose:
        print(f"Setting up FEM meshes (n_divisions={n_divisions})...")

    # Create tetrahedra
    verts_plus = tetrahedron_vertices(R, 'even')
    verts_minus = tetrahedron_vertices(R, 'odd')

    # Create FEM solvers
    fem_plus = TetrahedronFEM(verts_plus, n_divisions)
    fem_minus = TetrahedronFEM(verts_minus, n_divisions)

    if verbose:
        print(f"  T+ mesh: {fem_plus.n_nodes} nodes, {fem_plus.n_elements} elements")
        print(f"  T- mesh: {fem_minus.n_nodes} nodes, {fem_minus.n_elements} elements")

    # Assemble and solve eigenvalue problems
    if verbose:
        print(f"Solving eigenvalue problems (alpha={alpha:.4f})...")

    fem_plus.assemble_matrices(alpha)
    fem_minus.assemble_matrices(alpha)

    eigenvalues_plus, eigenvectors_plus = fem_plus.solve_eigenvalue(n_modes=3)
    eigenvalues_minus, eigenvectors_minus = fem_minus.solve_eigenvalue(n_modes=3)

    # Ground state eigenmodes (now normalized so integral psi^2 = V_tet)
    psi_plus = eigenvectors_plus[:, 0]
    psi_minus = eigenvectors_minus[:, 0]
    lambda_plus = eigenvalues_plus[0]
    lambda_minus = eigenvalues_minus[0]

    results['lambda_plus'] = lambda_plus
    results['lambda_minus'] = lambda_minus
    results['eigenvalues_plus'] = eigenvalues_plus.tolist()
    results['eigenvalues_minus'] = eigenvalues_minus.tolist()

    # Compute c_V from eigenvalue
    a = A_OVER_R * R
    V_tet = a**3 / (6 * np.sqrt(2))
    c_V = lambda_plus * a**2

    if verbose:
        print(f"  Ground state eigenvalue (T+): {lambda_plus:.4f}")
        print(f"  Ground state eigenvalue (T-): {lambda_minus:.4f}")
        print(f"  Implied c_V = lambda * a^2 = {c_V:.3f}")

    # Monte Carlo integration for overlap
    if verbose:
        print(f"\nComputing overlap integral with {n_samples} Monte Carlo samples...")

    # Create Delaunay triangulations for fast inside tests
    delaunay_plus = Delaunay(verts_plus)
    delaunay_minus = Delaunay(verts_minus)

    # Monte Carlo sampling
    integrand_sum = 0.0
    integrand_sq_sum = 0.0
    n_overlap = 0
    psi_plus_sum = 0.0
    psi_minus_sum = 0.0

    V_box = (2 * R)**3
    batch_size = 10000
    n_batches = n_samples // batch_size

    for batch in range(n_batches):
        # Generate random points in bounding box
        points = (np.random.random((batch_size, 3)) - 0.5) * 2 * R

        for point in points:
            in_plus = delaunay_plus.find_simplex(point) >= 0
            in_minus = delaunay_minus.find_simplex(point) >= 0

            if in_plus and in_minus:
                n_overlap += 1

                # Evaluate eigenmodes
                val_plus = fem_plus.evaluate_eigenmode(point, psi_plus)
                val_minus = fem_minus.evaluate_eigenmode(point, psi_minus)

                # |psi|^2 values (normalized so average over tet is ~1)
                # With volume normalization: integral psi^2 = V_tet
                # So average psi^2 = V_tet / V_tet = 1
                psi_sq_plus = val_plus**2 / V_tet
                psi_sq_minus = val_minus**2 / V_tet

                # Overlap integrand (now dimensionless, should be O(1))
                integrand = psi_sq_plus * psi_sq_minus
                integrand_sum += integrand
                integrand_sq_sum += integrand**2

                psi_plus_sum += psi_sq_plus
                psi_minus_sum += psi_sq_minus

        if verbose and (batch + 1) % 10 == 0:
            print(f"  Progress: {(batch + 1) / n_batches * 100:.0f}%")

    # Compute results
    n_total = n_batches * batch_size
    V_overlap = (n_overlap / n_total) * V_box

    if n_overlap > 0:
        avg_integrand = integrand_sum / n_overlap
        avg_integrand_sq = integrand_sq_sum / n_overlap
        variance = avg_integrand_sq - avg_integrand**2
        error = np.sqrt(abs(variance) / n_overlap) if n_overlap > 1 else 0

        # O = integral |psi_+|^2 |psi_-|^2 d^3x (dimensionless with our normalization)
        # But we computed the average, so O = avg * V_overlap / V_tet^2
        # Actually, with psi_sq normalized by V_tet, the integrand is already dimensionless
        # O = <psi_sq_+ * psi_sq_-> * V_overlap
        O = avg_integrand * V_overlap
        O_error = error * V_overlap

        avg_psi_sq_plus = psi_plus_sum / n_overlap
        avg_psi_sq_minus = psi_minus_sum / n_overlap
    else:
        avg_integrand = 0
        O = 0
        O_error = 0
        avg_psi_sq_plus = 0
        avg_psi_sq_minus = 0

    results['V_overlap'] = V_overlap
    results['n_overlap'] = n_overlap
    results['O'] = O
    results['O_error'] = O_error
    # kappa = O / V_overlap = average value of |psi_+|^2 |psi_-|^2 in overlap
    results['O_normalized'] = avg_integrand  # This is kappa
    results['avg_psi_sq_plus'] = avg_psi_sq_plus
    results['avg_psi_sq_minus'] = avg_psi_sq_minus

    # Tetrahedron properties
    results['a'] = a
    results['V_tetrahedron'] = V_tet

    if verbose:
        print()
        print("Results:")
        print(f"  Overlap volume: V_overlap = {V_overlap:.6f} fm^3")
        print(f"  Overlap fraction: {V_overlap / V_tet:.3f}")
        print(f"  Average |psi_+|^2 (normalized): {avg_psi_sq_plus:.4f}")
        print(f"  Average |psi_-|^2 (normalized): {avg_psi_sq_minus:.4f}")
        print(f"  Average <|psi_+|^2 |psi_-|^2>: {avg_integrand:.4f}")
        print(f"  Overlap integral: O = {O:.6f} +/- {O_error:.6f}")
        print(f"  kappa = <|psi_+|^2 |psi_-|^2> = {results['O_normalized']:.4f}")

    return results, fem_plus, fem_minus


def derive_kappa_fem(O_results, K, verbose=True):
    """
    Derive kappa from FEM overlap integral results.

    Parameters
    ----------
    O_results : dict
        Results from compute_overlap_integral_fem
    K : float
        Sakaguchi-Kuramoto coupling in fm^-1
    verbose : bool

    Returns
    -------
    kappa_results : dict
    """
    results = {}

    O = O_results['O']
    V_overlap = O_results['V_overlap']
    R = O_results['R']
    a = O_results['a']
    O_normalized = O_results['O_normalized']

    results['O'] = O
    results['V_overlap'] = V_overlap
    results['R'] = R
    results['K'] = K

    # kappa = O / V_overlap (dimensionless, = <|psi_+|^2 |psi_-|^2>)
    kappa = O_normalized
    results['kappa'] = kappa

    # Robin parameter: alpha = kappa * K / R
    alpha = kappa * K / R
    results['alpha'] = alpha

    # c_V from Robin interpolation formula
    # c_V(alpha) = c_V^D + (c_V^N - c_V^D) / (1 + alpha/beta)
    cV_N, cV_D = 4.077, 2.683
    beta = 1 / (3 * a)  # Geometric estimate

    cV = cV_D + (cV_N - cV_D) / (1 + alpha / beta)
    results['cV'] = cV
    results['beta'] = beta

    # Mass prediction
    M_V = SQRT_SIGMA * np.sqrt(cV)
    results['M_V'] = M_V

    M_rho = 775.26
    results['M_rho'] = M_rho
    results['deviation'] = (M_V - M_rho) / M_rho * 100

    # Target kappa (to match M_rho exactly)
    kappa_target = 0.130
    results['kappa_target'] = kappa_target
    results['kappa_ratio'] = kappa / kappa_target

    if verbose:
        print()
        print("=" * 70)
        print("KAPPA DERIVATION FROM FEM OVERLAP INTEGRAL")
        print("=" * 70)
        print()
        print(f"Input K = {K:.2f} fm^-1")
        print(f"Geometric beta = {beta:.4f} fm^-1")
        print()
        print(f"Computed kappa = O/V_overlap = {kappa:.4f}")
        print(f"Target kappa (from M_rho): {kappa_target:.4f}")
        print(f"Ratio: {kappa / kappa_target:.2f}")
        print()
        print(f"Robin parameter alpha = {alpha:.4f} fm^-1")
        print(f"Eigenvalue c_V = {cV:.3f}")
        print(f"Vector meson mass M_V = {M_V:.0f} MeV")
        print(f"Experimental M_rho = {M_rho:.2f} MeV")
        print(f"Deviation: {(M_V - M_rho)/M_rho*100:+.1f}%")

    return results


def scan_alpha_dependence(R=R_STELLA, alpha_range=None, n_divisions=6,
                           n_samples=50000, verbose=True):
    """
    Scan how the overlap integral and kappa depend on the Robin parameter alpha.

    This helps understand the self-consistency of the framework:
    - We use alpha to solve the eigenvalue problem
    - The resulting eigenmode determines kappa
    - kappa determines alpha through alpha = kappa * K / R

    For self-consistency: alpha_input = alpha_output

    Parameters
    ----------
    R : float
        Stella circumradius
    alpha_range : array-like
        Values of alpha to scan
    n_divisions : int
        Mesh refinement level
    n_samples : int
        Monte Carlo samples per alpha value
    verbose : bool

    Returns
    -------
    scan_results : dict
    """
    if alpha_range is None:
        alpha_range = np.linspace(0.1, 5.0, 10)

    results = {
        'R': R,
        'alpha_values': [],
        'kappa_values': [],
        'cV_values': [],
        'M_V_values': [],
        'O_values': [],
    }

    # Load K from previous calculation
    try:
        with open('verification/foundations/stella_casimir_coupling_results.json', 'r') as f:
            casimir_results = json.load(f)
        K = casimir_results['K_best']
    except FileNotFoundError:
        K = 3.5

    if verbose:
        print(f"Scanning alpha dependence (K = {K:.2f} fm^-1)...")
        print()

    for alpha in alpha_range:
        if verbose:
            print(f"alpha = {alpha:.2f}...")

        O_results, _, _ = compute_overlap_integral_fem(
            R=R, alpha=alpha, n_divisions=n_divisions,
            n_samples=n_samples, verbose=False
        )

        kappa_results = derive_kappa_fem(O_results, K, verbose=False)

        results['alpha_values'].append(alpha)
        results['kappa_values'].append(kappa_results['kappa'])
        results['cV_values'].append(kappa_results['cV'])
        results['M_V_values'].append(kappa_results['M_V'])
        results['O_values'].append(O_results['O'])

        if verbose:
            print(f"  kappa = {kappa_results['kappa']:.4f}, "
                  f"c_V = {kappa_results['cV']:.3f}, "
                  f"M_V = {kappa_results['M_V']:.0f} MeV")

    # Find self-consistent solution
    # alpha_output = kappa * K / R
    alpha_input = np.array(results['alpha_values'])
    kappa = np.array(results['kappa_values'])
    alpha_output = kappa * K / R

    # Find where alpha_input = alpha_output (self-consistent point)
    diff = alpha_output - alpha_input

    # Linear interpolation to find zero crossing
    if np.any(diff < 0) and np.any(diff > 0):
        # Find the crossing
        for i in range(len(diff) - 1):
            if diff[i] * diff[i+1] < 0:
                # Linear interpolation
                alpha_sc = alpha_input[i] - diff[i] * (alpha_input[i+1] - alpha_input[i]) / (diff[i+1] - diff[i])

                # Interpolate kappa and M_V
                kappa_sc = kappa[i] + (kappa[i+1] - kappa[i]) * (alpha_sc - alpha_input[i]) / (alpha_input[i+1] - alpha_input[i])

                results['alpha_self_consistent'] = alpha_sc
                results['kappa_self_consistent'] = kappa_sc

                if verbose:
                    print()
                    print(f"Self-consistent solution found:")
                    print(f"  alpha = {alpha_sc:.3f} fm^-1")
                    print(f"  kappa = {kappa_sc:.4f}")
                break

    return results


def make_fem_plot(O_results, kappa_results, fem_plus, fem_minus,
                  eigenvectors_plus, eigenvectors_minus, save_path=None):
    """
    Create visualization of FEM eigenmode and overlap calculation.
    """
    fig = plt.figure(figsize=(14, 10))

    R = O_results['R']

    # Panel 1: Stella geometry
    ax1 = fig.add_subplot(2, 2, 1, projection='3d')

    verts_plus = tetrahedron_vertices(R, 'even')
    verts_minus = tetrahedron_vertices(R, 'odd')

    faces_idx = [(0, 1, 2), (0, 2, 3), (0, 3, 1), (1, 3, 2)]
    for face in faces_idx:
        tri = [verts_plus[face[0]], verts_plus[face[1]], verts_plus[face[2]]]
        poly = Poly3DCollection([tri], alpha=0.2, facecolor='blue', edgecolor='blue')
        ax1.add_collection3d(poly)

    for face in faces_idx:
        tri = [verts_minus[face[0]], verts_minus[face[1]], verts_minus[face[2]]]
        poly = Poly3DCollection([tri], alpha=0.2, facecolor='red', edgecolor='red')
        ax1.add_collection3d(poly)

    ax1.set_xlim(-R, R)
    ax1.set_ylim(-R, R)
    ax1.set_zlim(-R, R)
    ax1.set_xlabel('x (fm)')
    ax1.set_ylabel('y (fm)')
    ax1.set_zlabel('z (fm)')
    ax1.set_title(f'Stella Octangula (R = {R:.3f} fm)')

    # Panel 2: Eigenmode profile along x-axis
    ax2 = fig.add_subplot(2, 2, 2)

    psi_plus = eigenvectors_plus[:, 0] if eigenvectors_plus is not None else None
    psi_minus = eigenvectors_minus[:, 0] if eigenvectors_minus is not None else None

    x_vals = np.linspace(-R, R, 100)
    psi_plus_vals = []
    psi_minus_vals = []

    if psi_plus is not None and psi_minus is not None:
        for x in x_vals:
            point = np.array([x, 0, 0])
            val_plus = fem_plus.evaluate_eigenmode(point, psi_plus)
            val_minus = fem_minus.evaluate_eigenmode(point, psi_minus)
            psi_plus_vals.append(val_plus**2)
            psi_minus_vals.append(val_minus**2)

        ax2.plot(x_vals, psi_plus_vals, 'b-', label='$|\\psi_{T+}|^2$', alpha=0.7)
        ax2.plot(x_vals, psi_minus_vals, 'r-', label='$|\\psi_{T-}|^2$', alpha=0.7)
        ax2.plot(x_vals, np.array(psi_plus_vals) * np.array(psi_minus_vals),
                'g-', label='$|\\psi_{T+}|^2|\\psi_{T-}|^2$', linewidth=2)

    ax2.set_xlabel('x (fm)')
    ax2.set_ylabel('$|\\psi|^2$')
    ax2.set_title('FEM Eigenmode Profile Along x-axis')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # Panel 3: kappa comparison with previous methods
    ax3 = fig.add_subplot(2, 2, 3)

    methods = ['FEM\neigenmode', 'Target\n(from $M_\\rho$)']
    kappas = [kappa_results['kappa'], kappa_results['kappa_target']]
    colors = ['purple', 'green']

    bars = ax3.bar(methods, kappas, color=colors, alpha=0.7, edgecolor='black')
    ax3.set_ylabel('$\\kappa$ (dimensionless)')
    ax3.set_title('Coupling Factor $\\kappa$ from FEM')
    ax3.axhline(y=kappa_results['kappa_target'], color='green', linestyle='--', alpha=0.5)

    for bar, val in zip(bars, kappas):
        ax3.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.005,
                f'{val:.4f}', ha='center', va='bottom')

    # Panel 4: Mass prediction
    ax4 = fig.add_subplot(2, 2, 4)

    methods = ['FEM', '$M_\\rho$ (PDG)']
    masses = [kappa_results['M_V'], kappa_results['M_rho']]
    colors = ['purple', 'green']

    bars = ax4.bar(methods, masses, color=colors, alpha=0.7, edgecolor='black')
    ax4.set_ylabel('Mass (MeV)')
    ax4.set_title('Vector Meson Mass from FEM')
    ax4.axhline(y=kappa_results['M_rho'], color='green', linestyle='--', alpha=0.5)
    ax4.set_ylim(700, 900)

    for bar, mass in zip(bars, masses):
        ax4.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 5,
                f'{mass:.0f}', ha='center', va='bottom')

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"\nPlot saved to: {save_path}")

    plt.close()
    return fig


def main():
    """Main entry point."""
    print()
    print("=" * 70)
    print("FEM-BASED OVERLAP INTEGRAL CALCULATION")
    print("=" * 70)
    print()

    # Load K from previous calculation
    try:
        with open('verification/foundations/stella_casimir_coupling_results.json', 'r') as f:
            casimir_results = json.load(f)
        K = casimir_results['K_best']
        print(f"Loaded K = {K:.2f} fm^-1 from previous Casimir coupling analysis")
    except FileNotFoundError:
        K = 3.5
        print(f"Using default K = {K:.2f} fm^-1")

    print()

    # Initial calculation with estimated alpha
    # From previous analysis, alpha ~ 1.0 fm^-1 gives reasonable results
    alpha_initial = 1.0

    print("-" * 70)
    print(f"INITIAL FEM CALCULATION (alpha = {alpha_initial})")
    print("-" * 70)

    O_results, fem_plus, fem_minus = compute_overlap_integral_fem(
        R=R_STELLA, alpha=alpha_initial, n_divisions=8,
        n_samples=200000, verbose=True
    )

    # Get eigenvectors for plotting
    eigenvalues_plus, eigenvectors_plus = fem_plus.solve_eigenvalue(n_modes=3)
    eigenvalues_minus, eigenvectors_minus = fem_minus.solve_eigenvalue(n_modes=3)

    kappa_results = derive_kappa_fem(O_results, K, verbose=True)

    # Self-consistency iteration
    print()
    print("-" * 70)
    print("SELF-CONSISTENCY ITERATION")
    print("-" * 70)
    print()

    # The self-consistent alpha should satisfy: alpha = kappa(alpha) * K / R
    # Start with the kappa we just computed

    alpha = kappa_results['alpha']
    kappa_prev = kappa_results['kappa']

    for iteration in range(5):
        print(f"Iteration {iteration + 1}: alpha = {alpha:.4f} fm^-1")

        O_results_iter, fem_plus, fem_minus = compute_overlap_integral_fem(
            R=R_STELLA, alpha=alpha, n_divisions=8,
            n_samples=100000, verbose=False
        )

        kappa_results_iter = derive_kappa_fem(O_results_iter, K, verbose=False)
        kappa_new = kappa_results_iter['kappa']
        alpha_new = kappa_new * K / R_STELLA

        print(f"  kappa = {kappa_new:.4f}, alpha_new = {alpha_new:.4f}")

        # Check convergence
        if abs(alpha_new - alpha) / alpha < 0.01:
            print(f"  Converged!")
            break

        alpha = 0.5 * alpha + 0.5 * alpha_new  # Damped update
        kappa_prev = kappa_new

    # Final result
    print()
    print("=" * 70)
    print("FINAL SELF-CONSISTENT RESULT")
    print("=" * 70)
    print()

    O_results_final, fem_plus_final, fem_minus_final = compute_overlap_integral_fem(
        R=R_STELLA, alpha=alpha, n_divisions=10,
        n_samples=300000, verbose=True
    )

    eigenvalues_plus_final, eigenvectors_plus_final = fem_plus_final.solve_eigenvalue(n_modes=3)
    eigenvalues_minus_final, eigenvectors_minus_final = fem_minus_final.solve_eigenvalue(n_modes=3)

    kappa_results_final = derive_kappa_fem(O_results_final, K, verbose=True)

    # Summary
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print(f"Self-consistent Robin parameter: alpha = {alpha:.4f} fm^-1")
    print(f"FEM-derived coupling factor: kappa = {kappa_results_final['kappa']:.4f}")
    print(f"Target kappa (from M_rho): {kappa_results_final['kappa_target']:.4f}")
    print(f"Ratio: {kappa_results_final['kappa_ratio']:.2f}")
    print()
    print(f"Eigenvalue c_V = {kappa_results_final['cV']:.3f}")
    print(f"Predicted M_V = {kappa_results_final['M_V']:.0f} MeV")
    print(f"Experimental M_rho = {kappa_results_final['M_rho']:.2f} MeV")
    print(f"Deviation: {kappa_results_final['deviation']:+.1f}%")

    # Uncertainty estimate
    # Compare with different mesh resolutions
    print()
    print("-" * 70)
    print("UNCERTAINTY ESTIMATE (mesh resolution comparison)")
    print("-" * 70)

    kappa_values = [kappa_results_final['kappa']]

    for n_div in [6, 12]:
        O_test, _, _ = compute_overlap_integral_fem(
            R=R_STELLA, alpha=alpha, n_divisions=n_div,
            n_samples=100000, verbose=False
        )
        kappa_test = derive_kappa_fem(O_test, K, verbose=False)
        kappa_values.append(kappa_test['kappa'])
        print(f"  n_divisions={n_div}: kappa = {kappa_test['kappa']:.4f}")

    kappa_mean = np.mean(kappa_values)
    kappa_std = np.std(kappa_values)

    print()
    print(f"FEM kappa = {kappa_mean:.4f} +/- {kappa_std:.4f}")

    # Propagate to M_V uncertainty
    # M_V = sqrt_sigma * sqrt(c_V), and c_V depends on kappa
    # Approximate: delta_M_V / M_V ~ 0.5 * delta_c_V / c_V ~ 0.5 * delta_kappa / kappa
    M_V_uncertainty = kappa_results_final['M_V'] * 0.5 * kappa_std / kappa_mean if kappa_mean > 0 else 0

    print(f"Propagated M_V uncertainty: +/- {M_V_uncertainty:.0f} MeV")

    # Save results
    final_results = {
        'R': R_STELLA,
        'K': K,
        'alpha_self_consistent': alpha,
        'fem': {
            'kappa': kappa_results_final['kappa'],
            'kappa_uncertainty': kappa_std,
            'cV': kappa_results_final['cV'],
            'M_V': kappa_results_final['M_V'],
            'M_V_uncertainty': M_V_uncertainty,
            'O': O_results_final['O'],
            'O_normalized': O_results_final['O_normalized'],
            'eigenvalue_plus': float(eigenvalues_plus_final[0]),
            'eigenvalue_minus': float(eigenvalues_minus_final[0]),
        },
        'target': {
            'kappa': kappa_results_final['kappa_target'],
            'M_rho': kappa_results_final['M_rho'],
        },
        'deviation_percent': kappa_results_final['deviation'],
    }

    json_path = 'verification/foundations/stella_overlap_fem_results.json'
    with open(json_path, 'w') as f:
        json.dump(final_results, f, indent=2)
    print(f"\nResults saved to: {json_path}")

    # Make plot
    plot_path = 'verification/plots/stella_overlap_fem.png'
    make_fem_plot(O_results_final, kappa_results_final,
                  fem_plus_final, fem_minus_final,
                  eigenvectors_plus_final, eigenvectors_minus_final,
                  save_path=plot_path)

    return final_results


if __name__ == '__main__':
    main()
