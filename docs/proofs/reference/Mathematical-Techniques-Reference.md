# Mathematical Techniques Reference

This document provides detailed reference material for mathematical techniques commonly used in Chiral Geometrogenesis proofs. These techniques are referenced in the main [CLAUDE.md](../CLAUDE.md) file.

---

## 1. Lie Algebra Representation Theory

**Where Used:** Phase 1 (SU(3) geometry), Theorem 1.1.1, Theorem 2.3.1, Definition 0.1.1

**Key Operations:**
- Computing Cartan subalgebra of 𝔰𝔲(3)
- Deriving weight vectors for fundamental representations
- Working with structure constants f^{abc}
- Casimir operator calculations

**Standard Results to Reference:**
- Weight vectors for quarks: (1,0), (−1/2, √3/2), (−1/2, −√3/2)
- π₃(SU(N)) = ℤ (crucial for topological charges)
- Tr[TᵃTᵇ] = ½δᵃᵇ (normalization convention)

**Common Errors:**
- Incorrect normalization of generators
- Sign errors in structure constants
- Confusing fundamental vs adjoint representations

**Verification:** Cross-check against Georgi's "Lie Algebras in Particle Physics" or Fulton & Harris

---

## 2. Spontaneous Symmetry Breaking (Mexican Hat Potential)

**Where Used:** Theorem 1.2.1, Lemma 2.1.3, Theorem 3.0.1, throughout mass generation

**Standard Form:**
$$V(\chi) = \lambda(|\chi|^2 - v_\chi^2)^2$$

**Key Derivations:**
- Minimum at |χ| = v_χ ≠ 0
- Radial mode mass: m_h² = 2λv_χ²
- Goldstone modes are massless (before explicit breaking)
- Parameterization: χ = (v_χ + h)e^{iπᵃTᵃ/f_π}

**Physical Correspondences:**
- h ↔ Higgs boson (125 GeV)
- πᵃ ↔ Pions (absorbed or physical depending on gauging)

**Pitfall:** Ensure the potential is bounded below; check coefficient signs

---

## 3. Chiral Anomaly (Adler-Bell-Jackiw)

**Where Used:** Theorem 1.2.2, Theorem 2.2.4, Theorem 4.2.1

**Master Equation:**
$$\partial_\mu J_5^\mu = \frac{g^2 N_f}{16\pi^2} G_{\mu\nu}\tilde{G}^{\mu\nu}$$

**Derivation Methods:**
- Triangle diagram calculation (perturbative)
- Fujikawa path integral method (non-perturbative, preferred)
- Index theorem connection

**Key Coefficient:** The factor of 1/(16π²) is exact and protected

**Connection to Instantons:**
$$\int d^4x \, G_{\mu\nu}\tilde{G}^{\mu\nu} = 32\pi^2 Q$$
where Q ∈ ℤ is the instanton number

**Verification:** Coefficient must match Adler-Bell-Jackiw (1969)

---

## 4. Coupled Oscillator Theory (Kuramoto Model)

**Where Used:** Theorem 2.2.1, Theorem 2.2.2, Theorem 2.2.3

**Governing Equations:**
$$\dot{\phi}_i = \omega_i + \sum_{j} K_{ij}\sin(\phi_j - \phi_i - \alpha)$$

**Key Results:**
- Phase-locked solutions exist for sufficient coupling K
- Sakaguchi-Kuramoto (α ≠ 0) breaks time-reversal symmetry
- Limit cycle stability via Lyapunov analysis

**For CG Specifically:**
- Three oscillators (R, G, B) with 120° phase separation
- α = 2π/3 from SU(3) topology
- Dissipative: phase-space contraction rate σ = 3K/4

**Stability Analysis:**
- Linearize around fixed point
- Compute eigenvalues of Jacobian
- Forward cycle: eigenvalues (−K/2, −K) → stable
- Reversed cycle: eigenvalues (+K/2, +K) → unstable

---

## 5. Topological Solitons (Skyrme Model)

**Where Used:** Phase 4, Theorems 4.1.1-4.1.3

**Topological Charge (Winding Number):**
$$Q = \frac{1}{24\pi^2}\int d^3x\, \epsilon^{ijk}\text{Tr}[(U^\dagger\partial_i U)(U^\dagger\partial_j U)(U^\dagger\partial_k U)]$$

**Why Q ∈ ℤ:** From homotopy π₃(SU(2)) = ℤ

**Bogomolny Bound:**
$$E \geq C|Q|$$
This prevents soliton collapse; the Skyrme term is essential.

**Hedgehog Ansatz:**
$$U(\vec{x}) = \exp(i\vec{\tau}\cdot\hat{r}F(r))$$
with boundary conditions F(0) = π, F(∞) = 0

**Fermion Number:** Atiyah-Singer gives N_F = Q (baryon number = winding)

---

## 6. Atiyah-Singer Index Theorem

**Where Used:** Theorem 4.1.3, Theorem 2.2.4

**Statement:**
$$\text{ind}(D) = n_+ - n_- = \frac{1}{32\pi^2}\int d^4x\, G_{\mu\nu}\tilde{G}^{\mu\nu}$$

**Physical Meaning:**
- n₊, n₋ = number of left/right-handed zero modes of Dirac operator
- In instanton background with Q = 1: exactly one zero mode
- This is why instantons create/destroy fermion number

**Application to CG:**
- Connects fermion chirality to gauge field topology
- Explains why chiral anomaly is exact (topological protection)
- Underlies the chirality selection mechanism

---

## 7. Thermodynamic/Entropic Gravity (Jacobson Approach)

**Where Used:** Theorem 5.2.3

**Core Idea:** Einstein equations emerge from δQ = TδS on local Rindler horizons

**Key Steps:**
1. Consider local Rindler horizon with acceleration a
2. Unruh temperature: T = ℏa/(2πck_B)
3. Bekenstein-Hawking entropy: S = A/(4ℓ_P²)
4. Apply Clausius relation: δQ = TδS
5. Require for all null vectors k^μ
6. Einstein equations emerge as integrability condition

**CG Modification:**
- Entropy from phase counting on stella octangula boundary
- Temperature from chiral oscillation frequency
- Logarithmic correction predicted: S = A/(4ℓ_P²) − (3/2)ln(A/ℓ_P²)

---

## 8. Wick Rotation and Euclidean Field Theory

**Where Used:** Theorem 5.2.0

**Standard Procedure:**
- Analytic continuation: t → −iτ
- Minkowski → Euclidean: ds² = −dt² + dx² → ds² = dτ² + dx²
- Path integral becomes well-defined: e^{iS} → e^{−S_E}

**Validity Conditions (Osterwalder-Schrader):**
- Euclidean action bounded below
- Reflection positivity
- Cluster property (mass gap)

**CG Subtlety:**
- Time-dependent VEV χ = v_χe^{iωt} would diverge naively
- Resolution: Internal parameter λ remains real; only emergent time Wick-rotated
- Action in terms of λ is unchanged by Wick rotation of coordinates

---

## 9. Effective Field Theory and Matching

**Where Used:** Theorem 3.2.1, Theorem 3.2.2

**Procedure:**
1. Write most general Lagrangian consistent with symmetries
2. Organize by operator dimension (power counting)
3. Match to UV theory at scale Λ
4. Run down to low energies using RG

**For CG → SM Matching:**
$$\mathcal{L}_{CG}^{eff}(E \ll \Lambda) = \mathcal{L}_{SM} + \sum_i \frac{c_i}{\Lambda^2}\mathcal{O}_i^{(6)} + ...$$

**Key Checks:**
- All dimension-4 operators match SM exactly
- Wilson coefficients c_i calculable from CG Lagrangian
- Current bound: Λ > 3.5 TeV from precision tests

**Cutoff Scale Derived:**
$$\Lambda = 4\pi v \sqrt{v/f_\pi} \approx 4-10 \text{ TeV}$$

---

## 10. Instanton Calculations

**Where Used:** Theorem 2.2.4, Theorem 4.2.1

**Instanton Action:**
$$S_{inst} = \frac{8\pi^2}{g^2}$$

**Instanton Density (Dilute Gas):**
$$n_{inst} \sim \Lambda_{QCD}^4 e^{-8\pi^2/g^2(\Lambda)}$$

**Key CG Result:**
- Instanton density ~1000× LOWER inside hadrons than vacuum
- Inside: α_s(0.3 fm) ≈ 0.3 → exponentially suppressed
- Outside: α_s(1 fm) ≈ 0.5 → vacuum density ~1 fm⁻⁴
- This gradient drives chirality selection at hadron boundary

**'t Hooft Determinant:**
- 2N_f quarks involved in instanton vertex
- Provides cyclic R→G→B coupling in CG

---

## 11. Grand Unified Theory (GUT) Techniques

**Where Used:** Theorem 2.3.1

**SU(5) Embedding:**
- SM gauge groups: SU(3)_c × SU(2)_L × U(1)_Y ⊂ SU(5)
- Coupling unification at M_GUT ~ 10¹⁶ GeV

**Weak Mixing Angle Prediction:**
- At GUT scale: sin²θ_W = 3/8 (group theory)
- CG derivation: sin²θ_W^{GUT} = 2π/(2π + 5α) with α = 2π/3 gives 3/8 ✓

**RG Running:**
$$\frac{d\sin^2\theta_W}{d\ln\mu} = \frac{\sin^2\theta_W \cos^2\theta_W}{2\pi}(b_1 - b_2)$$
- SM coefficients: b₁ = 41/10, b₂ = −19/6
- Result: sin²θ_W(M_Z) ≈ 0.231 matches experiment

**'t Hooft Anomaly Matching:**
- Anomaly coefficients are integers (count zero modes)
- Must match between UV and IR: A_UV = A_IR
- Chirality selected at GUT scale persists to low energy
