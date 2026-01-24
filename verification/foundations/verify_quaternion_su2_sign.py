"""
Verification: Quaternion-su(2) Isomorphism Sign Convention
===========================================================

This script verifies the correct sign convention for the isomorphism
between imaginary quaternions Im(H) and the su(2) Lie algebra.

The question: Given T_a = c * i_a (where i_a ∈ {i, j, k} are imaginary quaternion units),
what constant c gives the standard su(2) commutation relation [T_a, T_b] = i*ε_abc*T_c?

Quaternion facts:
- [i_a, i_b] = 2*ε_abc*i_c  (commutator of imaginary quaternions)

su(2) convention:
- [T_a, T_b] = i*ε_abc*T_c

Analysis:
=========

Let T_a = c * i_a for some constant c.

[T_a, T_b] = [c*i_a, c*i_b] = c² * [i_a, i_b] = c² * 2*ε_abc*i_c

We want this to equal i*ε_abc*T_c = i*ε_abc*(c*i_c) = i*c*ε_abc*i_c

So we need: c² * 2 * i_c = i * c * i_c

Dividing by i_c (which is nonzero):
c² * 2 = i * c

Solving for c:
c = i/2

Therefore: T_a = (i/2) * i_a  (WITHOUT the minus sign)

Let's verify this computationally.
"""

import numpy as np

# Pauli matrices (standard physics convention)
sigma_1 = np.array([[0, 1], [1, 0]], dtype=complex)
sigma_2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
sigma_3 = np.array([[1, 0], [0, -1]], dtype=complex)

# SU(2) generators (fundamental representation)
T_1 = sigma_1 / 2
T_2 = sigma_2 / 2
T_3 = sigma_3 / 2

def commutator(A, B):
    """Compute [A, B] = AB - BA"""
    return A @ B - B @ A

def verify_su2_commutators():
    """Verify [T_a, T_b] = i*ε_abc*T_c for standard SU(2)"""
    print("=" * 60)
    print("VERIFICATION 1: Standard SU(2) Commutation Relations")
    print("=" * 60)

    # [T_1, T_2] should equal i*T_3
    comm_12 = commutator(T_1, T_2)
    expected_12 = 1j * T_3
    print(f"\n[T_1, T_2] = \n{comm_12}")
    print(f"i*T_3 = \n{expected_12}")
    print(f"Match: {np.allclose(comm_12, expected_12)}")

    # [T_2, T_3] should equal i*T_1
    comm_23 = commutator(T_2, T_3)
    expected_23 = 1j * T_1
    print(f"\n[T_2, T_3] = \n{comm_23}")
    print(f"i*T_1 = \n{expected_23}")
    print(f"Match: {np.allclose(comm_23, expected_23)}")

    # [T_3, T_1] should equal i*T_2
    comm_31 = commutator(T_3, T_1)
    expected_31 = 1j * T_2
    print(f"\n[T_3, T_1] = \n{comm_31}")
    print(f"i*T_2 = \n{expected_31}")
    print(f"Match: {np.allclose(comm_31, expected_31)}")

def verify_quaternion_commutators():
    """Verify [i_a, i_b] = 2*ε_abc*i_c for quaternions"""
    print("\n" + "=" * 60)
    print("VERIFICATION 2: Quaternion Commutation Relations")
    print("=" * 60)

    # Represent quaternion units as 2x2 complex matrices
    # i -> i*σ_1, j -> i*σ_2, k -> i*σ_3 (one standard representation)
    # But let's use: i -> -i*σ_1, j -> -i*σ_2, k -> -i*σ_3
    # This gives the standard quaternion algebra

    # Standard quaternion matrix representation:
    # 1 = [[1,0],[0,1]], i = [[i,0],[0,-i]], j = [[0,1],[-1,0]], k = [[0,i],[i,0]]

    i_quat = np.array([[1j, 0], [0, -1j]], dtype=complex)
    j_quat = np.array([[0, 1], [-1, 0]], dtype=complex)
    k_quat = np.array([[0, 1j], [1j, 0]], dtype=complex)

    # Verify quaternion multiplication: ij = k, ji = -k, so [i,j] = 2k
    ij = i_quat @ j_quat
    ji = j_quat @ i_quat

    print(f"\ni * j = \n{ij}")
    print(f"Expected k = \n{k_quat}")
    print(f"Match: {np.allclose(ij, k_quat)}")

    print(f"\nj * i = \n{ji}")
    print(f"Expected -k = \n{-k_quat}")
    print(f"Match: {np.allclose(ji, -k_quat)}")

    comm_ij = commutator(i_quat, j_quat)
    print(f"\n[i, j] = i*j - j*i = \n{comm_ij}")
    print(f"Expected 2k = \n{2*k_quat}")
    print(f"Match: {np.allclose(comm_ij, 2*k_quat)}")

def verify_isomorphism_sign():
    """Verify which sign convention gives correct isomorphism"""
    print("\n" + "=" * 60)
    print("VERIFICATION 3: Testing Sign Conventions for T_a = c * i_a")
    print("=" * 60)

    # Quaternion units as matrices
    i_quat = np.array([[1j, 0], [0, -1j]], dtype=complex)
    j_quat = np.array([[0, 1], [-1, 0]], dtype=complex)
    k_quat = np.array([[0, 1j], [1j, 0]], dtype=complex)

    print("\n--- Testing c = +i/2 (positive) ---")
    c_pos = 1j / 2
    T1_pos = c_pos * i_quat
    T2_pos = c_pos * j_quat
    T3_pos = c_pos * k_quat

    comm_12_pos = commutator(T1_pos, T2_pos)
    expected_pos = 1j * T3_pos
    print(f"[T_1, T_2] with c = +i/2:")
    print(f"  Result: \n{comm_12_pos}")
    print(f"  Expected (i*T_3): \n{expected_pos}")
    print(f"  Match: {np.allclose(comm_12_pos, expected_pos)}")

    print("\n--- Testing c = -i/2 (negative, as in document) ---")
    c_neg = -1j / 2
    T1_neg = c_neg * i_quat
    T2_neg = c_neg * j_quat
    T3_neg = c_neg * k_quat

    comm_12_neg = commutator(T1_neg, T2_neg)
    expected_neg = 1j * T3_neg
    print(f"[T_1, T_2] with c = -i/2:")
    print(f"  Result: \n{comm_12_neg}")
    print(f"  Expected (i*T_3): \n{expected_neg}")
    print(f"  Match: {np.allclose(comm_12_neg, expected_neg)}")

def detailed_algebraic_analysis():
    """Step-by-step algebraic analysis"""
    print("\n" + "=" * 60)
    print("DETAILED ALGEBRAIC ANALYSIS")
    print("=" * 60)

    print("""
Given:
  [i_a, i_b] = 2*ε_abc*i_c   (quaternion commutator)

Want:
  [T_a, T_b] = i*ε_abc*T_c   (su(2) commutator)

Let T_a = c*i_a for constant c.

Then:
  [T_a, T_b] = [c*i_a, c*i_b] = c² * [i_a, i_b] = c² * 2*ε_abc*i_c

We want this to equal:
  i*ε_abc*T_c = i*ε_abc*(c*i_c) = (i*c)*ε_abc*i_c

Equating coefficients of ε_abc*i_c:
  2*c² = i*c

If c ≠ 0:
  2*c = i
  c = i/2

CONCLUSION: T_a = (i/2)*i_a  (WITHOUT minus sign)

Document states: T_a = -(i/2)*i_a (WITH minus sign)

Let's verify the document's claim is wrong:
""")

    print("\nWith c = -i/2 (document version):")
    print("  c² = (-i/2)² = i²/4 = -1/4")
    print("  2*c² = -1/2")
    print("  i*c = i*(-i/2) = -i²/2 = 1/2")
    print("  Since -1/2 ≠ 1/2, the commutator does NOT match!")

    print("\nWith c = +i/2 (correct version):")
    print("  c² = (i/2)² = i²/4 = -1/4")
    print("  2*c² = -1/2")
    print("  i*c = i*(i/2) = i²/2 = -1/2")
    print("  Since -1/2 = -1/2, the commutator MATCHES!")

    print("\n" + "=" * 60)
    print("WAIT - Let me reconsider this more carefully.")
    print("=" * 60)

def careful_analysis():
    """More careful analysis considering the full structure"""
    print("""
Let me be more careful about the quaternion representation.

The imaginary quaternions i, j, k satisfy:
  i² = j² = k² = -1
  ij = k, jk = i, ki = j
  ji = -k, kj = -i, ik = -j

So: [i, j] = ij - ji = k - (-k) = 2k ✓

Now for the isomorphism. The su(2) algebra has:
  [T_a, T_b] = i*ε_abc*T_c

where i = √(-1) is the imaginary unit (not the quaternion!).

Let T_a = c*i_a where i_a ∈ {i, j, k} are quaternion units.

[T_a, T_b] = c² * [i_a, i_b] = c² * 2*ε_abc*i_c

For this to equal i*ε_abc*T_c = i*c*ε_abc*i_c:
  2*c² = i*c
  c = i/2 (assuming c ≠ 0)

BUT WAIT - we need to be careful about what "equals" means here.

The issue is that T_a should be a matrix (or abstract Lie algebra element),
not a quaternion. The isomorphism maps:

  Im(H) → su(2)
  i_a   → T_a

such that the Lie bracket is preserved:
  [i_a, i_b]_quat = 2*ε_abc*i_c  →  [T_a, T_b]_Lie = i*ε_abc*T_c

But these are different brackets! The left side has coefficient 2,
the right side has coefficient i.

The isomorphism is NOT T_a = c*i_a for some c.
Rather, it's a Lie algebra isomorphism that RESCALES the structure constants.

Let me write this properly.
""")

    print("\n" + "=" * 60)
    print("PROPER ANALYSIS")
    print("=" * 60)

    print("""
The Lie algebra su(2) over R has bracket:
  [T_a, T_b] = ε_abc * T_c

The imaginary quaternions Im(H) over R have bracket (commutator):
  [i_a, i_b] = 2*ε_abc * i_c

These are isomorphic as Lie algebras! The isomorphism is:
  φ: Im(H) → su(2)
  i_a → T_a

This is a LINEAR map (not involving any constants in the map itself).
The structure constants are different (2 vs 1), but both are real,
so these are isomorphic as REAL Lie algebras.

NOW, in physics, we often use the convention:
  [T_a, T_b] = i*ε_abc * T_c  (note the factor of i = √(-1))

This means we're working with the COMPLEXIFIED Lie algebra su(2)_C,
or equivalently, with anti-Hermitian generators multiplied by i.

For this convention, we need:
  T_a^{physics} = (i/2) * t_a^{math}

where t_a^{math} are the standard su(2) generators with [t_a, t_b] = ε_abc * t_c.

But if we want to realize T_a^{physics} directly in terms of quaternions:

The Pauli matrices relate to quaternions via:
  σ_1 = [[0,1],[1,0]]       ↔   (i is mapped differently here)
  σ_2 = [[0,-i],[i,0]]
  σ_3 = [[1,0],[0,-1]]

The SU(2) generators are T_a = σ_a/2.

Actually, let me just verify numerically what works.
""")

def numerical_verification():
    """Numerical verification with explicit matrices"""
    print("\n" + "=" * 60)
    print("NUMERICAL VERIFICATION: What formula gives T_a = σ_a/2?")
    print("=" * 60)

    # Standard Pauli matrices
    sigma_1 = np.array([[0, 1], [1, 0]], dtype=complex)
    sigma_2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
    sigma_3 = np.array([[1, 0], [0, -1]], dtype=complex)

    # SU(2) generators (target)
    T_1 = sigma_1 / 2
    T_2 = sigma_2 / 2
    T_3 = sigma_3 / 2

    # Quaternion units in 2x2 matrix form
    # Standard identification: 1 = I, i = -i*σ_1, j = -i*σ_2, k = -i*σ_3
    # (This comes from the isomorphism H → Mat(2,C))
    i_quat = -1j * sigma_1
    j_quat = -1j * sigma_2
    k_quat = -1j * sigma_3

    print("Using quaternion representation: i_a = -i*σ_a")
    print(f"\ni = -i*σ_1 = \n{i_quat}")
    print(f"\nj = -i*σ_2 = \n{j_quat}")
    print(f"\nk = -i*σ_3 = \n{k_quat}")

    # Verify quaternion relations
    print("\n--- Verifying quaternion multiplication ---")
    ij = i_quat @ j_quat
    print(f"i*j = \n{ij}")
    print(f"k = \n{k_quat}")
    print(f"Match (ij=k): {np.allclose(ij, k_quat)}")

    i_squared = i_quat @ i_quat
    print(f"\ni² = \n{i_squared}")
    print(f"Expected -I: \n{-np.eye(2)}")
    print(f"Match (i²=-1): {np.allclose(i_squared, -np.eye(2))}")

    # Now find the coefficient c such that T_a = c * i_a gives T_a = σ_a/2
    print("\n--- Finding coefficient c such that T_a = c*i_a ---")
    # T_1 = σ_1/2, i_quat = -i*σ_1
    # So σ_1/2 = c*(-i*σ_1) = -i*c*σ_1
    # Therefore: 1/2 = -i*c, so c = -1/(2i) = i/2

    c_test = 1j / 2
    T1_test = c_test * i_quat
    print(f"\nWith c = i/2:")
    print(f"T_1 = (i/2)*(-i*σ_1) = (i/2)*(-i)*σ_1 = (1/2)*σ_1 = σ_1/2")
    print(f"(i/2) * i_quat = \n{T1_test}")
    print(f"T_1 = σ_1/2 = \n{T_1}")
    print(f"Match: {np.allclose(T1_test, T_1)}")

    # Now the document's formula
    print("\n--- Testing document formula: T_a = -(i/2)*i_a ---")
    c_doc = -1j / 2
    T1_doc = c_doc * i_quat
    print(f"\nWith c = -i/2 (document):")
    print(f"T_1 = (-i/2)*(-i*σ_1) = (-i/2)*(-i)*σ_1 = (-1/2)*σ_1 = -σ_1/2")
    print(f"(-i/2) * i_quat = \n{T1_doc}")
    print(f"T_1 = σ_1/2 = \n{T_1}")
    print(f"Match: {np.allclose(T1_doc, T_1)}")
    print(f"(-i/2)*i gives -T_1: {np.allclose(T1_doc, -T_1)}")

def find_correct_formula():
    """Find and verify the correct formula"""
    print("\n" + "=" * 60)
    print("FINDING THE CORRECT FORMULA")
    print("=" * 60)

    # The issue is: what representation of quaternions are we using?

    # Representation 1: i_a maps to -i*σ_a (standard in physics)
    # Then T_a = σ_a/2 = (i/2)*(-i*σ_a) = (i/2)*i_a
    # So with this rep: T_a = (i/2)*i_a (POSITIVE)

    # Representation 2: i_a maps to +i*σ_a
    # Then T_a = σ_a/2 = (-i/2)*(i*σ_a) = (-i/2)*i_a
    # So with this rep: T_a = -(i/2)*i_a (NEGATIVE)

    print("""
The sign depends on which matrix representation of quaternions we use!

If i_a ↔ -i*σ_a (standard physics convention):
  T_a = σ_a/2 = (i/2)*(-i*σ_a) = (i/2)*i_a
  So: T_a = +(i/2)*i_a

If i_a ↔ +i*σ_a (alternative convention):
  T_a = σ_a/2 = (-i/2)*(i*σ_a) = (-i/2)*i_a
  So: T_a = -(i/2)*i_a

The document doesn't specify which quaternion representation is used!
This is the source of the ambiguity.

Let me verify the document's claim is INTERNALLY CONSISTENT:
""")

    print("\n--- Checking document's internal consistency ---")
    print("""
Document claims (§3.2, lines 186-191):
  T_a = -(i/2)*i_a

And claims this gives [T_a, T_b] = i*ε_abc*T_c

Let's verify:
  [T_a, T_b] = [-(i/2)*i_a, -(i/2)*i_b]
             = (i/2)² * [i_a, i_b]
             = (-1/4) * 2*ε_abc*i_c
             = -(1/2)*ε_abc*i_c

  i*ε_abc*T_c = i*ε_abc*(-(i/2)*i_c)
              = -(i²/2)*ε_abc*i_c
              = -(-1/2)*ε_abc*i_c
              = +(1/2)*ε_abc*i_c

These differ by a sign! -(1/2) ≠ +(1/2)

So the document IS INCONSISTENT. The verification report is correct.
""")

    print("=" * 60)
    print("RESOLUTION OPTIONS")
    print("=" * 60)
    print("""
OPTION 1: Change T_a = -(i/2)*i_a to T_a = +(i/2)*i_a
  Then: [T_a, T_b] = (-1/4)*2*ε_abc*i_c = -(1/2)*ε_abc*i_c
        i*ε_abc*T_c = i*(i/2)*ε_abc*i_c = (i²/2)*ε_abc*i_c = -(1/2)*ε_abc*i_c
  Match! ✓

OPTION 2: Keep T_a = -(i/2)*i_a but change the commutator convention
  Document would need [T_a, T_b] = -i*ε_abc*T_c
  But this is non-standard for physics literature.

RECOMMENDATION: Use OPTION 1 (change to positive sign).
""")

def final_verification():
    """Final numerical verification of the correct formula"""
    print("\n" + "=" * 60)
    print("FINAL VERIFICATION: T_a = +(i/2)*i_a with i_a = -i*σ_a")
    print("=" * 60)

    sigma_1 = np.array([[0, 1], [1, 0]], dtype=complex)
    sigma_2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
    sigma_3 = np.array([[1, 0], [0, -1]], dtype=complex)

    # Quaternion units: i_a = -i*σ_a
    i_quat = -1j * sigma_1
    j_quat = -1j * sigma_2
    k_quat = -1j * sigma_3

    # With c = +i/2
    c = 1j / 2
    T_1 = c * i_quat
    T_2 = c * j_quat
    T_3 = c * k_quat

    print(f"T_1 = (i/2)*i = (i/2)*(-i*σ_1) = σ_1/2")
    print(f"Computed: \n{T_1}")
    print(f"Expected (σ_1/2): \n{sigma_1/2}")
    print(f"Match: {np.allclose(T_1, sigma_1/2)}")

    # Verify commutator
    comm_12 = commutator(T_1, T_2)
    expected = 1j * T_3
    print(f"\n[T_1, T_2] = \n{comm_12}")
    print(f"i*T_3 = \n{expected}")
    print(f"Match [T_1,T_2] = i*T_3: {np.allclose(comm_12, expected)}")

    print("\n" + "=" * 60)
    print("CONCLUSION")
    print("=" * 60)
    print("""
The verification report is CORRECT. The document has a sign error.

CURRENT (incorrect): T_a = -(i/2)*i_a
CORRECT: T_a = +(i/2)*i_a

With the quaternion representation i_a ↔ -i*σ_a, the formula
T_a = +(i/2)*i_a gives T_a = σ_a/2 (the standard SU(2) generators),
and satisfies [T_a, T_b] = i*ε_abc*T_c.
""")

if __name__ == "__main__":
    verify_su2_commutators()
    verify_quaternion_commutators()
    verify_isomorphism_sign()
    detailed_algebraic_analysis()
    careful_analysis()
    numerical_verification()
    find_correct_formula()
    final_verification()

    print("\n" + "=" * 60)
    print("SUMMARY FOR DOCUMENT FIX")
    print("=" * 60)
    print("""
The document §3.2 (lines 186-191) should be updated:

CURRENT TEXT:
  "The isomorphism Im(H) ≅ su(2) is realized by the identification:
   T_a = -(i/2)*i_a"

SHOULD BE CHANGED TO:
  "The isomorphism Im(H) ≅ su(2) is realized by the identification:
   T_a = (i/2)*i_a"

(Remove the minus sign)

Additionally, the proof text in lines 188-189 needs updating:

CURRENT: "[T_a, T_b] = [-(i/2)i_a, -(i/2)i_b] = -(1/4)[i_a, i_b]..."

SHOULD BE: "[T_a, T_b] = [(i/2)i_a, (i/2)i_b] = -(1/4)[i_a, i_b]..."

Note: The factor -(1/4) is correct because (i/2)² = i²/4 = -1/4.
""")
