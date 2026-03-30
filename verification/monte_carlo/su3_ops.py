"""
SU(3) Matrix Operations for Monte Carlo
=========================================

Provides both Numba-JIT accelerated and pure NumPy implementations
of SU(3) matrix algebra needed for lattice gauge theory simulations.

Numba-accelerated (hot-loop safe):
    mat3x3_mul, mat3x3_dag, mat3x3_trace, mat3x3_det,
    project_su3_gs, random_su3_near_id_cayley,
    kennedy_pendleton_su2, su2_extract, su2_embed

NumPy fallbacks (for initialization, testing):
    random_su3_haar, project_su3_svd
"""

import numpy as np
from numba import njit, types

NC = 3

# =============================================================================
# Numba-accelerated 3x3 complex matrix operations
# =============================================================================

@njit(cache=True)
def mat3x3_mul(A, B):
    """Multiply two 3x3 complex matrices."""
    C = np.zeros((3, 3), dtype=np.complex128)
    for i in range(3):
        for j in range(3):
            s = 0.0 + 0.0j
            for k in range(3):
                s += A[i, k] * B[k, j]
            C[i, j] = s
    return C


@njit(cache=True)
def mat3x3_dag(A):
    """Conjugate transpose of a 3x3 complex matrix."""
    B = np.zeros((3, 3), dtype=np.complex128)
    for i in range(3):
        for j in range(3):
            B[i, j] = np.conj(A[j, i])
    return B


@njit(cache=True)
def mat3x3_trace(A):
    """Trace of a 3x3 complex matrix."""
    return A[0, 0] + A[1, 1] + A[2, 2]


@njit(cache=True)
def mat3x3_det(A):
    """Determinant of a 3x3 complex matrix."""
    return (A[0, 0] * (A[1, 1] * A[2, 2] - A[1, 2] * A[2, 1])
          - A[0, 1] * (A[1, 0] * A[2, 2] - A[1, 2] * A[2, 0])
          + A[0, 2] * (A[1, 0] * A[2, 1] - A[1, 1] * A[2, 0]))


@njit(cache=True)
def mat3x3_eye():
    """3x3 identity matrix."""
    I = np.zeros((3, 3), dtype=np.complex128)
    I[0, 0] = 1.0
    I[1, 1] = 1.0
    I[2, 2] = 1.0
    return I


# =============================================================================
# SU(3) projection via Gram-Schmidt (Numba-safe)
# =============================================================================

@njit(cache=True)
def project_su3_gs(M):
    """Project a 3x3 complex matrix onto SU(3) via modified Gram-Schmidt.

    Takes the first two rows, orthonormalizes, and constructs the third
    row via cross product to ensure det = +1.
    """
    # Extract rows
    v0 = np.zeros(3, dtype=np.complex128)
    v1 = np.zeros(3, dtype=np.complex128)
    for j in range(3):
        v0[j] = M[0, j]
        v1[j] = M[1, j]

    # Normalize v0
    norm0 = 0.0
    for j in range(3):
        norm0 += (np.conj(v0[j]) * v0[j]).real
    norm0 = np.sqrt(norm0)
    if norm0 < 1e-15:
        return mat3x3_eye()
    for j in range(3):
        v0[j] /= norm0

    # Orthogonalize v1 against v0
    dot01 = 0.0 + 0.0j
    for j in range(3):
        dot01 += np.conj(v0[j]) * v1[j]
    for j in range(3):
        v1[j] -= dot01 * v0[j]

    # Normalize v1
    norm1 = 0.0
    for j in range(3):
        norm1 += (np.conj(v1[j]) * v1[j]).real
    norm1 = np.sqrt(norm1)
    if norm1 < 1e-15:
        return mat3x3_eye()
    for j in range(3):
        v1[j] /= norm1

    # Third row = conj(v0 x v1) to get det = +1
    v2 = np.zeros(3, dtype=np.complex128)
    v2[0] = np.conj(v0[1] * v1[2] - v0[2] * v1[1])
    v2[1] = np.conj(v0[2] * v1[0] - v0[0] * v1[2])
    v2[2] = np.conj(v0[0] * v1[1] - v0[1] * v1[0])

    U = np.zeros((3, 3), dtype=np.complex128)
    for j in range(3):
        U[0, j] = v0[j]
        U[1, j] = v1[j]
        U[2, j] = v2[j]
    return U


# =============================================================================
# Random SU(3) near identity via Cayley map (Numba-safe)
# =============================================================================

@njit(cache=True)
def _randn_complex_3x3():
    """Generate random 3x3 complex matrix with standard normal entries."""
    M = np.zeros((3, 3), dtype=np.complex128)
    for i in range(3):
        for j in range(3):
            M[i, j] = np.random.randn() + 1j * np.random.randn()
    return M


@njit(cache=True)
def random_su3_near_id(epsilon):
    """Generate SU(3) matrix near identity via Cayley approximation.

    Uses X = epsilon * (random anti-Hermitian traceless), then
    U = (I + X/2)(I - X/2)^{-1} (Cayley map), projected to SU(3).
    """
    # Random anti-Hermitian traceless 3x3
    H = _randn_complex_3x3()
    # Make anti-Hermitian: A = (H - H†)/2
    A = np.zeros((3, 3), dtype=np.complex128)
    for i in range(3):
        for j in range(3):
            A[i, j] = (H[i, j] - np.conj(H[j, i])) / 2.0
    # Make traceless
    tr = (A[0, 0] + A[1, 1] + A[2, 2]) / 3.0
    A[0, 0] -= tr
    A[1, 1] -= tr
    A[2, 2] -= tr
    # Scale by epsilon
    for i in range(3):
        for j in range(3):
            A[i, j] *= epsilon / np.sqrt(2.0)

    # Cayley map: U = (I + A/2)(I - A/2)^{-1}
    # For small epsilon this is very close to exp(A)
    Ip = mat3x3_eye()
    Ap = np.zeros((3, 3), dtype=np.complex128)
    Am = np.zeros((3, 3), dtype=np.complex128)
    for i in range(3):
        for j in range(3):
            Ap[i, j] = Ip[i, j] + A[i, j] / 2.0
            Am[i, j] = Ip[i, j] - A[i, j] / 2.0

    # Invert Am via Cramer's rule (3x3)
    det_Am = mat3x3_det(Am)
    if abs(det_Am) < 1e-15:
        return mat3x3_eye()

    # Cofactor matrix
    Cof = np.zeros((3, 3), dtype=np.complex128)
    Cof[0, 0] = Am[1, 1] * Am[2, 2] - Am[1, 2] * Am[2, 1]
    Cof[0, 1] = -(Am[1, 0] * Am[2, 2] - Am[1, 2] * Am[2, 0])
    Cof[0, 2] = Am[1, 0] * Am[2, 1] - Am[1, 1] * Am[2, 0]
    Cof[1, 0] = -(Am[0, 1] * Am[2, 2] - Am[0, 2] * Am[2, 1])
    Cof[1, 1] = Am[0, 0] * Am[2, 2] - Am[0, 2] * Am[2, 0]
    Cof[1, 2] = -(Am[0, 0] * Am[2, 1] - Am[0, 1] * Am[2, 0])
    Cof[2, 0] = Am[0, 1] * Am[1, 2] - Am[0, 2] * Am[1, 1]
    Cof[2, 1] = -(Am[0, 0] * Am[1, 2] - Am[0, 2] * Am[1, 0])
    Cof[2, 2] = Am[0, 0] * Am[1, 1] - Am[0, 1] * Am[1, 0]

    # Inverse = Cof^T / det
    Am_inv = np.zeros((3, 3), dtype=np.complex128)
    for i in range(3):
        for j in range(3):
            Am_inv[i, j] = Cof[j, i] / det_Am

    U = mat3x3_mul(Ap, Am_inv)
    return project_su3_gs(U)


# =============================================================================
# Kennedy-Pendleton SU(2) heat bath
# =============================================================================

@njit(cache=True)
def _su2_det(a):
    """Determinant of SU(2) matrix parametrized as (a0, a1, a2, a3)."""
    return a[0]**2 + a[1]**2 + a[2]**2 + a[3]**2


@njit(cache=True)
def kennedy_pendleton_su2(beta_eff):
    """Kennedy-Pendleton heat bath for SU(2).

    Generates a random SU(2) element u = (a0, a1, a2, a3) distributed as:
        P(u) proportional to exp(beta_eff * a0) * sqrt(1 - a0^2)

    This corresponds to the Wilson action exp(beta_eff/2 * Re Tr U)
    where Re Tr U = 2*a0 for U in SU(2).

    Parameters:
        beta_eff: effective coupling for the SU(2) heat bath

    Returns: (a0, a1, a2, a3) with a0^2+a1^2+a2^2+a3^2 = 1
    """
    if beta_eff < 1e-10:
        # Uniform on SU(2) for zero coupling
        x = np.random.randn(4)
        norm = np.sqrt(x[0]**2 + x[1]**2 + x[2]**2 + x[3]**2)
        return x / norm

    for _attempt in range(1000):
        # Kennedy-Pendleton algorithm (Phys. Rev. Lett. 54, 2473)
        r1 = np.random.random()
        r2 = np.random.random()
        r3 = np.random.random()
        r4 = np.random.random()

        # lambda^2 from sum of two modified exponential variates
        lam_sq = -(np.log(r1) + np.log(r3) * np.cos(2.0 * np.pi * r2)**2) / (2.0 * beta_eff)
        if r4 * r4 <= 1.0 - lam_sq:
            a0 = 1.0 - 2.0 * lam_sq
            # Generate (a1, a2, a3) uniformly on sphere of radius sqrt(1-a0^2)
            r = np.sqrt(max(1.0 - a0 * a0, 0.0))
            # Marsaglia method for uniform point on S^2
            while True:
                x1 = 2.0 * np.random.random() - 1.0
                x2 = 2.0 * np.random.random() - 1.0
                s = x1 * x1 + x2 * x2
                if s < 1.0:
                    break
            f = 2.0 * np.sqrt(1.0 - s)
            a1 = r * x1 * f
            a2 = r * x2 * f
            a3 = r * (1.0 - 2.0 * s)
            return np.array([a0, a1, a2, a3])

    # Fallback: return identity
    return np.array([1.0, 0.0, 0.0, 0.0])


@njit(cache=True)
def su2_to_matrix(a):
    """Convert SU(2) quaternion (a0, a1, a2, a3) to 2x2 complex matrix."""
    M = np.zeros((2, 2), dtype=np.complex128)
    M[0, 0] = a[0] + 1j * a[3]
    M[0, 1] = a[2] + 1j * a[1]
    M[1, 0] = -a[2] + 1j * a[1]
    M[1, 1] = a[0] - 1j * a[3]
    return M


# =============================================================================
# SU(2) subgroup extraction/embedding for Cabibbo-Marinari
# =============================================================================

@njit(cache=True)
def su2_extract_subblock(W, sub):
    """Extract 2x2 subblock from 3x3 matrix W for Cabibbo-Marinari.

    sub=0: rows/cols (0,1)  [12-block]
    sub=1: rows/cols (0,2)  [13-block]
    sub=2: rows/cols (1,2)  [23-block]
    """
    if sub == 0:
        i, j = 0, 1
    elif sub == 1:
        i, j = 0, 2
    else:
        i, j = 1, 2

    r = np.zeros((2, 2), dtype=np.complex128)
    r[0, 0] = W[i, i]
    r[0, 1] = W[i, j]
    r[1, 0] = W[j, i]
    r[1, 1] = W[j, j]
    return r


@njit(cache=True)
def su2_embed_subblock(r, sub):
    """Embed 2x2 SU(2) matrix into 3x3, filling rest with identity.

    sub=0: rows/cols (0,1)
    sub=1: rows/cols (0,2)
    sub=2: rows/cols (1,2)
    """
    U = mat3x3_eye()
    if sub == 0:
        i, j = 0, 1
    elif sub == 1:
        i, j = 0, 2
    else:
        i, j = 1, 2

    U[i, i] = r[0, 0]
    U[i, j] = r[0, 1]
    U[j, i] = r[1, 0]
    U[j, j] = r[1, 1]
    return U


@njit(cache=True)
def _su2_project(r):
    """Project 2x2 complex matrix to SU(2) quaternion parameters.

    Extract (a0, a1, a2, a3) from r ~ a0*I + i*a_k*sigma_k,
    normalizing so that a0^2+a1^2+a2^2+a3^2=1.
    """
    a0 = (r[0, 0] + r[1, 1]).real / 2.0
    a3 = (r[0, 0] - r[1, 1]).imag / 2.0
    a1 = (r[0, 1] + r[1, 0]).imag / 2.0
    a2 = (r[0, 1] - r[1, 0]).real / 2.0
    norm = np.sqrt(a0**2 + a1**2 + a2**2 + a3**2)
    if norm < 1e-15:
        return np.array([1.0, 0.0, 0.0, 0.0])
    return np.array([a0, a1, a2, a3]) / norm


@njit(cache=True)
def cabibbo_marinari_su2_update(W, beta_over_nc, sub):
    """Perform one Cabibbo-Marinari SU(2) subgroup update.

    Standard Cabibbo-Marinari algorithm:
        1. Extract 2x2 subblock w of W = U @ V (unscaled)
        2. Decompose w into unnormalized quaternion: w ~ alpha * v_su2
        3. KP heat bath with coupling k = beta_over_nc * alpha
        4. Return R = u_new @ v_old^{-1} embedded in SU(3)

    Parameters:
        W: 3x3 complex matrix = U_current @ staple_sum (NOT scaled by beta)
        beta_over_nc: beta / N_c coupling parameter
        sub: subgroup index (0, 1, or 2)
    """
    r = su2_extract_subblock(W, sub)

    # Extract unnormalized quaternion parameters from 2x2 subblock
    a0 = (r[0, 0] + r[1, 1]).real / 2.0
    a3 = (r[0, 0] - r[1, 1]).imag / 2.0
    a1 = (r[0, 1] + r[1, 0]).imag / 2.0
    a2 = (r[0, 1] - r[1, 0]).real / 2.0

    # alpha = magnitude of the quaternion (effective "determinant")
    alpha = np.sqrt(a0**2 + a1**2 + a2**2 + a3**2)

    if alpha < 1e-15:
        return mat3x3_eye()

    # Normalized old SU(2) element
    a_old = np.array([a0, a1, a2, a3]) / alpha

    # KP coupling: k = 2 * beta_over_nc * alpha
    # Factor of 2 because Re Tr_2(u) = 2*u0 for SU(2) element u,
    # and KP generates from exp(k * a0).
    k = 2.0 * beta_over_nc * alpha
    a_new = kennedy_pendleton_su2(k)

    # Update matrix: R = u_new @ v_old^{-1}
    # v_old^{-1} = (a0, -a1, -a2, -a3) (conjugate quaternion)
    a_old_inv = np.array([a_old[0], -a_old[1], -a_old[2], -a_old[3]])

    # Quaternion multiplication: a_new * a_old_inv
    b0 = a_new[0] * a_old_inv[0] - a_new[1] * a_old_inv[1] - a_new[2] * a_old_inv[2] - a_new[3] * a_old_inv[3]
    b1 = a_new[0] * a_old_inv[1] + a_new[1] * a_old_inv[0] + a_new[2] * a_old_inv[3] - a_new[3] * a_old_inv[2]
    b2 = a_new[0] * a_old_inv[2] - a_new[1] * a_old_inv[3] + a_new[2] * a_old_inv[0] + a_new[3] * a_old_inv[1]
    b3 = a_new[0] * a_old_inv[3] + a_new[1] * a_old_inv[2] - a_new[2] * a_old_inv[1] + a_new[3] * a_old_inv[0]

    update_su2 = su2_to_matrix(np.array([b0, b1, b2, b3]))
    return su2_embed_subblock(update_su2, sub)


# =============================================================================
# Pure NumPy fallbacks (for initialization and testing)
# =============================================================================

def random_su3_haar():
    """Generate a random SU(3) matrix from Haar measure via QR decomposition."""
    z = (np.random.randn(3, 3) + 1j * np.random.randn(3, 3)) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    d = np.diag(r)
    ph = d / np.abs(d)
    q = q @ np.diag(ph)
    det = np.linalg.det(q)
    q = q / det ** (1.0 / 3.0)
    return q


def project_su3_svd(M):
    """Project a 3x3 matrix onto SU(3) via SVD polar decomposition."""
    U, S, Vh = np.linalg.svd(M)
    P = U @ Vh
    det = np.linalg.det(P)
    P = P / det ** (1.0 / 3.0)
    return P


# =============================================================================
# Verification utilities
# =============================================================================

@njit(cache=True)
def check_unitarity(U):
    """Check |U U† - I|_F for a 3x3 matrix. Returns Frobenius norm of deviation."""
    UUd = mat3x3_mul(U, mat3x3_dag(U))
    I = mat3x3_eye()
    err = 0.0
    for i in range(3):
        for j in range(3):
            diff = UUd[i, j] - I[i, j]
            err += (diff.real)**2 + (diff.imag)**2
    return np.sqrt(err)


@njit(cache=True)
def check_det_phase(U):
    """Check |det(U)| - 1 for a 3x3 matrix."""
    d = mat3x3_det(U)
    return abs(abs(d) - 1.0)
