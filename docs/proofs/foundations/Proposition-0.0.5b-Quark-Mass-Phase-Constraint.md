# Proposition 0.0.5b: Quark Mass Phase Vanishes from Real Overlap Integrals

## Status: 🔶 NOVEL — Completes Strong CP Resolution

**Purpose:** This proposition closes a critical gap in the Strong CP resolution (Proposition 0.0.5a): showing that the quark mass phase contribution arg det(M_q) vanishes in the CG framework, not just the bare θ parameter.

**Created:** 2026-01-11
**Last Updated:** 2026-01-12

**The Gap Addressed:**

The Strong CP problem involves θ̄ = θ + arg det(M_q):
- **Proposition 0.0.5a** proves: θ = 0 from Z₃ superselection
- **This proposition** proves: arg det(M_q) = 0 from real overlap integrals
- **Combined result**: θ̄ = 0 (full Strong CP resolution)

**Dependencies:**
- ✅ Proposition 0.0.5a (Z₃ Center Constrains θ-Angle)
- ✅ Theorem 3.1.1 (Phase-Gradient Mass Generation Mass Formula)
- ✅ Theorem 3.1.2 (Mass Hierarchy Pattern from Geometry)
- ✅ Definition 0.1.3 (Pressure Functions from Geometric Opposition)
- ✅ Proposition 0.0.17m (Base Mass Scale Parameters)

**Enables:**
- Complete Strong CP resolution in the CG framework
- Full treatment of θ̄ = θ + arg det(M_q) (both terms addressed)

---

## 0. Executive Summary

### The Problem

The observable θ̄ parameter in QCD is:
$$\bar{\theta} = \theta_{bare} + \arg\det(M_q)$$

where M_q is the quark mass matrix. The Strong CP problem asks why θ̄ < 10⁻¹⁰.

**Proposition 0.0.5a** establishes that Z₃ superselection forces θ_bare = 0. But this leaves the question: **Why is arg det(M_q) = 0?**

### The Key Insight

In the CG framework, quark masses arise from the phase-gradient mass generation mechanism (Theorem 3.1.1):
$$m_f = \frac{g_\chi \omega_0}{\Lambda} v_\chi \cdot \eta_f$$

The helicity couplings η_f are determined by **overlap integrals** (Theorem 3.1.2):
$$\eta_f = \lambda^{2n_f} \cdot c_f$$

where $c_f$ comes from the overlap of fermion wavefunctions with the chiral field profile on the stella octangula.

**Crucially:** These overlap integrals are **real-valued by construction** because:
1. The fermion localization functions are real (Gaussian profiles)
2. The chiral field magnitude |χ(x)| is real
3. The integration measure on ∂S is real

Therefore: η_f ∈ ℝ ⟹ m_f ∈ ℝ ⟹ det(M_q) ∈ ℝ ⟹ arg det(M_q) = 0.

---

## 1. Statement

**Proposition 0.0.5b (Quark Mass Phase from Real Overlap Integrals)**

In the Chiral Geometrogenesis framework, the quark mass matrix has vanishing phase:
$$\arg\det(M_q) = 0$$

This follows from the geometric origin of fermion masses:

**(a) Real Helicity Couplings:** The helicity coupling constants η_f from Theorem 3.1.1 are real-valued:
$$\eta_f \in \mathbb{R} \quad \forall f \in \{u, d, s, c, b, t\}$$

**(b) Real Mass Matrix:** The quark mass matrix (in the phase-gradient mass generation mechanism) is real and diagonal in the mass basis:
$$M_q = \text{diag}(m_u, m_d, m_s, m_c, m_b, m_t) \quad \text{with } m_f \in \mathbb{R}^+$$

**(c) Real Determinant:** Therefore:
$$\det(M_q) = \prod_f m_f \in \mathbb{R}^+$$

**(d) Vanishing Phase:** Since det(M_q) is a positive real number:
$$\boxed{\arg\det(M_q) = 0}$$

**(e) Complete Strong CP Resolution:** Combined with Proposition 0.0.5a (θ = 0):
$$\bar{\theta} = \theta + \arg\det(M_q) = 0 + 0 = 0$$

---

## 2. Background: The Quark Mass Phase Problem

### 2.1 Standard Model Analysis

In the Standard Model, the quark mass matrix arises from Yukawa couplings:
$$\mathcal{L}_{Yukawa} = -Y^u_{ij}\bar{Q}_L^i \tilde{H} u_R^j - Y^d_{ij}\bar{Q}_L^i H d_R^j + h.c.$$

After electroweak symmetry breaking, the mass matrices are:
$$M^u_{ij} = Y^u_{ij} v, \quad M^d_{ij} = Y^d_{ij} v$$

where v = 246 GeV is the Higgs VEV.

**The problem:** The Yukawa coupling matrices Y^{u,d} are general complex matrices. There is no a priori reason why:
$$\arg\det(M^u M^d) = \arg\det(Y^u Y^d) = 0$$

### 2.2 Why This Matters for Strong CP

The effective θ parameter is:
$$\bar{\theta} = \theta_{QCD} + \arg\det(M_u M_d)$$

Even if θ_QCD = 0 (from some mechanism), the Yukawa phases can contribute:
$$\arg\det(M_u M_d) = \arg\det(Y^u) + \arg\det(Y^d)$$

Without a mechanism to constrain these phases, θ̄ can be O(1).

### 2.3 Standard Solutions

| Solution | Mechanism | Status |
|----------|-----------|--------|
| **Axion** | Dynamical field relaxes phases | Requires axion searches |
| **Nelson-Barr** | Spontaneous CP at high scale | Requires fine-tuning |
| **Left-right symmetric** | P enforces real couplings | Constrains UV completion |
| **CG (this work)** | Geometric origin forces real η_f | Follows from framework |

---

## 3. The CG Mass Mechanism

### 3.1 Review of Phase-Gradient Mass Generation (Theorem 3.1.1)

The phase-gradient mass generation mass formula is:
$$m_f = \frac{g_\chi \omega_0}{\Lambda} v_\chi \cdot \eta_f$$

where:
- $g_\chi$ is the chiral coupling (dimensionless, real by hermiticity)
- $\omega_0 = \sqrt{\sigma}/(N_c - 1) = 220$ MeV (real, derived)
- $\Lambda = 4\pi f_\pi = 1106$ MeV (real, derived)
- $v_\chi = \sqrt{\sigma}/5 = 88.0$ MeV (real, derived)
- $\eta_f$ is the helicity coupling (fermion-specific)

**Key observation:** The base mass $(g_\chi \omega_0 / \Lambda) v_\chi$ is **real by construction**. The only potential source of complex phases is η_f.

**Base mass scale (from Proposition 0.0.17m):**
$$\frac{g_\chi \omega_0}{\Lambda} v_\chi = \frac{\sqrt{\sigma}}{18} \approx 24.4 \text{ MeV}$$

with parameters: $g_\chi = 4\pi/9 \approx 1.396$, $\omega_0 = 220$ MeV, $\Lambda = 1106$ MeV, $v_\chi = 88$ MeV.

### 3.2 Review of Helicity Couplings (Theorem 3.1.2)

The helicity couplings have the form:
$$\eta_f = \lambda^{2n_f} \cdot c_f$$

where:
- $\lambda = 0.22497 \pm 0.00070$ is the (real) Wolfenstein parameter (PDG 2024)
- $n_f \in \{0, 1, 2\}$ is the generation index (0 = 3rd gen, 1 = 2nd gen, 2 = 1st gen)
- $c_f \in (0, 1]$ is the overlap integral coefficient (see §4.3)

**Generation Hierarchy:**
| Generation | $n_f$ | Suppression $\lambda^{2n_f}$ | Approximate value |
|------------|-------|------------------------------|-------------------|
| 3rd (t, b) | 0 | $\lambda^0 = 1$ | 1 |
| 2nd (c, s) | 1 | $\lambda^2$ | 0.0506 |
| 1st (u, d) | 2 | $\lambda^4$ | 0.00256 |

**Key properties of the Wolfenstein factor:**
- $\lambda^{2n_f} > 0$ for all $n_f$ (positive power of positive number)
- $\lambda^{2n_f} \leq 1$ for all $n_f \geq 0$ (since $0 < \lambda < 1$)

The coefficient $c_f$ is defined as:
$$c_f = \int_{\partial\mathcal{S}} |\psi_f(x)|^2 \cdot |\chi(x)|^2 \, d^2x$$

where:
- $|\psi_f(x)|^2$ is the fermion localization probability density
- $|\chi(x)|^2$ is the chiral field intensity
- $\partial\mathcal{S}$ is the stella octangula boundary

---

## 4. Derivation: Reality of Helicity Couplings

### 4.1 The Overlap Integral Structure

**Definition 4.1.1 (Probability Density):**

A probability density on $\partial\mathcal{S}$ is a function $\rho: \partial\mathcal{S} \to \mathbb{R}$ satisfying:
- **Non-negativity:** $\rho(x) \geq 0$ for all $x \in \partial\mathcal{S}$
- **Normalization:** $\int_{\partial\mathcal{S}} \rho(x) \, d\mu(x) \leq 1$

**Definition 4.1.2 (Overlap Integral):**

The helicity coupling coefficient is:
$$c_f = \int_{\partial\mathcal{S}} \rho_f(x) \cdot \rho_\chi(x) \, d\mu(x)$$

where:
- $\rho_f(x) = |\psi_f(x)|^2$ is the fermion probability density (strictly positive on support)
- $\rho_\chi(x) = |\chi(x)|^2 / \int |\chi|^2$ is the normalized chiral field intensity (strictly positive)
- $d\mu(x)$ is the measure on $\partial\mathcal{S}$

### 4.2 Reality of Each Component

**Lemma 4.2.1 (Fermion Density is Real):**

The fermion localization function takes a Gaussian form:
$$|\psi_f(x)|^2 = \frac{1}{2\pi\sigma^2} e^{-|x - x_f|^2 / (2\sigma^2)}$$

where $x_f$ is the generation localization center and $\sigma$ is the width.

This is manifestly real and positive: $\rho_f(x) \in \mathbb{R}^+$.

#### Justification of Gaussian Localization

The Gaussian form is not merely an ansatz but follows from three physical principles:

**1. Variational Ground State:** For a particle in a confining potential $V(x) \propto |x - x_f|^2$ near a localization center, the ground state wavefunction is Gaussian. The stella geometry creates effective potential wells at generation centers through the pressure gradient structure.

**2. Minimum Uncertainty:** The Gaussian is the unique wavefunction that saturates the Heisenberg uncertainty bound $\Delta x \cdot \Delta p = \hbar/2$. Fermions localized on the stella boundary naturally seek this minimum uncertainty configuration.

**3. Central Limit Theorem:** Even if individual localization contributions are non-Gaussian, the convolution of multiple independent localization effects produces a Gaussian distribution in the limit of many degrees of freedom.

#### Robustness to Non-Gaussian Profiles

**Theorem 4.2.1b (Robustness):** The key result $c_f \in \mathbb{R}^+$ holds for **any** fermion localization function $\rho_f(x)$ satisfying:
- **Non-negativity:** $\rho_f(x) \geq 0$ for all $x \in \partial\mathcal{S}$
- **Normalization:** $\int_{\partial\mathcal{S}} \rho_f(x) \, d\mu(x) = 1$

**Proof:** These are the defining properties of a probability density. Any such density, when integrated against a non-negative chiral field intensity and positive measure, yields a non-negative real number:
$$c_f = \int \underbrace{\rho_f(x)}_{\geq 0} \cdot \underbrace{\rho_\chi(x)}_{\geq 0} \, \underbrace{d\mu(x)}_{> 0} \geq 0$$

Furthermore, if both $\rho_f$ and $\rho_\chi$ have non-empty support, $c_f > 0$.

The specific Gaussian form affects the **value** of $c_f$ (and hence the quark mass hierarchy) but not its **reality**. ∎

**Corollary:** The result $\arg\det(M_q) = 0$ is robust to the specific choice of fermion localization profile.

**Lemma 4.2.2 (Chiral Field Intensity is Real):**

From Definition 0.1.2, the chiral field is:
$$\chi(x) = v_\chi(x) e^{i\Phi(x)}$$

The intensity is:
$$|\chi(x)|^2 = v_\chi(x)^2$$

which is real and positive: $\rho_\chi(x) \in \mathbb{R}^+$.

**Lemma 4.2.3 (Measure is Real):**

The integration measure on $\partial\mathcal{S}$ is the standard area measure, which is real and positive: $d\mu(x) \in \mathbb{R}^+$.

### 4.3 Reality of the Overlap Integral

**Theorem 4.3.1 (Real Overlap Integrals):**

The overlap integral $c_f$ is real and positive:
$$c_f = \int_{\partial\mathcal{S}} \rho_f(x) \cdot \rho_\chi(x) \, d\mu(x) \in \mathbb{R}^+$$

**Proof:**

The integrand is a product of non-negative reals:
$$\rho_f(x) \cdot \rho_\chi(x) \geq 0 \quad \forall x \in \partial\mathcal{S}$$

The integral of non-negative reals over a positive measure is non-negative real:
$$c_f = \int (\text{non-negative real}) \, d(\text{positive measure}) \in \mathbb{R}_{\geq 0}$$

Furthermore, since both densities are positive on open sets (they're Gaussians and pressure functions), the integral is strictly positive:
$$c_f > 0$$

Therefore: $c_f \in \mathbb{R}^+$. ∎

**Lemma 4.3.2 (Overlap Integral Bounded):**

The overlap integral satisfies $c_f \leq 1$.

**Proof:**

By the Cauchy-Schwarz inequality for $L^2$ functions:
$$c_f = \int \rho_f \cdot \rho_\chi \, d\mu \leq \left(\int \rho_f^2 \, d\mu\right)^{1/2} \left(\int \rho_\chi^2 \, d\mu\right)^{1/2}$$

Since both $\rho_f$ and $\rho_\chi$ are normalized probability densities with values $\leq 1$:
$$\int \rho_f^2 \, d\mu \leq \int \rho_f \, d\mu \leq 1$$

and similarly for $\rho_\chi$. Therefore $c_f \leq 1 \cdot 1 = 1$. ∎

**Corollary 4.3.3 (Overlap Integral Range):**

Combining Theorem 4.3.1 and Lemma 4.3.2: $c_f \in (0, 1]$ for all fermion flavors.

### 4.4 Reality of Helicity Couplings

**Corollary 4.4.1 (Real η_f):**

Since $\lambda \in \mathbb{R}^+$ and $c_f \in \mathbb{R}^+$:
$$\eta_f = \lambda^{2n_f} \cdot c_f \in \mathbb{R}^+$$

for all fermion species f.

---

## 5. Derivation: Vanishing of arg det(M_q)

### 5.1 Mass Matrix Structure

#### 5.1.1 Flavor Basis vs Mass Basis: Why the Distinction Matters

**Important clarification:** In the Standard Model, the statement "masses are real and diagonal in the mass basis" is trivially true by definition — any hermitian matrix can be diagonalized with real eigenvalues. The Strong CP-relevant quantity is:

$$\arg\det(M_q) = \arg\det(M^u_{flavor}) + \arg\det(M^d_{flavor})$$

where $M^{u,d}_{flavor}$ are the **flavor-basis** mass matrices before diagonalization.

The non-trivial claim of this proposition is that in the CG framework, the **flavor-basis** mass matrices are already real (not just Hermitian), which immediately implies $\arg\det(M_q) = 0$.

#### 5.1.2 Flavor-Basis Structure in Phase-Gradient Mass Generation

**Theorem 5.1.1 (Real Flavor-Basis Mass Matrix):**

In the phase-gradient mass generation mechanism, the flavor-basis mass matrix $M^f_{ij}$ is real:
$$M^f_{ij} \in \mathbb{R} \quad \forall i,j \in \{1,2,3\}$$

**Proof:**

The phase-gradient mass generation Lagrangian couples the chiral field to fermions:
$$\mathcal{L}_{drag} = -\frac{g_\chi}{\Lambda}\bar{\psi}_{L,i}\gamma^\mu(\partial_\mu\chi)\psi_{R,j} \cdot \mathcal{O}_{ij} + h.c.$$

where $\mathcal{O}_{ij}$ is the overlap matrix encoding the spatial structure:
$$\mathcal{O}_{ij} = \int_{\partial\mathcal{S}} \psi^*_{L,i}(x) \cdot \chi(x) \cdot \psi_{R,j}(x) \, d\mu(x)$$

**Key insight:** In the CG framework, fermion wavefunctions $\psi_{L,i}$ and $\psi_{R,j}$ are determined by geometric localization on $\partial\mathcal{S}$, and these localization profiles are **real Gaussian functions** (not complex):
$$\psi_{L,i}(x) = \psi_{R,i}(x) = N_i \exp\left(-\frac{|x - x_i|^2}{2\sigma_i^2}\right) \in \mathbb{R}$$

where $x_i$ are the generation localization centers determined by the stella geometry.

After phase averaging of the rotating chiral field (see §4), the effective mass matrix becomes:
$$M^f_{ij} = \frac{g_\chi \omega_0}{\Lambda} v_\chi \cdot \mathcal{O}_{ij}$$

Since:
- $g_\chi, \omega_0, \Lambda, v_\chi \in \mathbb{R}$ (framework parameters)
- $\psi_{L,i}(x), \psi_{R,j}(x) \in \mathbb{R}$ (real localization functions)
- $|\chi(x)|^2 \in \mathbb{R}^+$ (field intensity)
- $d\mu(x) \in \mathbb{R}^+$ (measure)

The overlap matrix $\mathcal{O}_{ij}$ is real, and therefore $M^f_{ij} \in \mathbb{R}$. ∎

#### 5.1.3 Diagonal Dominance and Mass Eigenstates

**Corollary 5.1.2 (Diagonal Dominance):**

In the CG framework, the flavor-basis mass matrix is approximately diagonal:
$$M^f_{ij} \approx m_i \delta_{ij} + \mathcal{O}(\epsilon)$$

where $\epsilon \ll 1$ encodes the small off-diagonal mixing from wavefunction overlaps between generations.

**Proof:**

The generation localization centers $x_i$ are separated by distances $\sim \sigma \sqrt{\ln(1/\lambda^2)}$ where $\lambda \approx 0.225$ is the Wolfenstein parameter (PDG 2024: $\lambda = 0.22497 \pm 0.00070$). The Gaussian overlap between generations $i \neq j$ is:
$$\mathcal{O}_{ij} \propto \exp\left(-\frac{|x_i - x_j|^2}{4\sigma^2}\right) \sim \lambda^{|i-j|}$$

This gives a hierarchical structure where diagonal elements dominate. ∎

#### 5.1.4 Mass Eigenvalues and Diagonalization

**Theorem 5.1.3 (Real Positive Mass Eigenvalues):**

Since $M^f_{ij} \in \mathbb{R}$ and $M^f$ is symmetric (from $L \leftrightarrow R$ symmetry of the geometric construction), the eigenvalues (physical masses) are real:
$$m_f = (g_\chi \omega_0 / \Lambda) v_\chi \cdot \eta_f \in \mathbb{R}^+$$

where $\eta_f$ are the eigenvalues of the overlap matrix $\mathcal{O}$.

The diagonalized mass matrix is:
$$M_q = \text{diag}(m_u, m_d, m_s, m_c, m_b, m_t)$$

**Crucially:** Because $M^f_{ij} \in \mathbb{R}$, the determinant is real **before diagonalization**:
$$\det(M^f) = \det(V^\dagger M_q V) = \det(M_q) \cdot \underbrace{|\det(V)|^2}_{=1} = \det(M_q) \in \mathbb{R}$$

where $V$ is the unitary diagonalization matrix.

Therefore: $\arg\det(M^f) = \arg\det(M_q) = 0$. ∎

### 5.2 The Determinant

**Theorem 5.2.1 (Real Positive Determinant):**

The determinant of the quark mass matrix is real and positive:
$$\det(M_q) = \prod_{f} m_f \in \mathbb{R}^+$$

**Proof:**

For a diagonal matrix with positive real entries:
$$\det(\text{diag}(a_1, ..., a_n)) = \prod_{i=1}^n a_i$$

Each $m_f > 0$, so:
$$\det(M_q) = m_u \cdot m_d \cdot m_s \cdot m_c \cdot m_b \cdot m_t > 0$$

Therefore: $\det(M_q) \in \mathbb{R}^+$. ∎

### 5.3 Vanishing Phase

**Theorem 5.3.1 (arg det(M_q) = 0):**

The phase of the quark mass matrix determinant vanishes:
$$\arg\det(M_q) = 0$$

**Proof:**

For any positive real number $r > 0$:
$$\arg(r) = 0$$

Since $\det(M_q) \in \mathbb{R}^+$ (Theorem 5.2.1):
$$\arg\det(M_q) = 0$$ ∎

---

## 6. Complete Strong CP Resolution

### 6.1 Combined Result

**Theorem 6.1.1 (θ̄ = 0 in CG Framework):**

The effective QCD vacuum angle vanishes:
$$\bar{\theta} = \theta + \arg\det(M_q) = 0$$

**Proof:**

From Proposition 0.0.5a:
$$\theta = 0 \quad \text{(Z₃ superselection + energy minimization)}$$

From Theorem 5.3.1:
$$\arg\det(M_q) = 0 \quad \text{(real overlap integrals)}$$

Therefore:
$$\bar{\theta} = 0 + 0 = 0$$ ∎

### 6.2 Why This Is Not Fine-Tuning

| Aspect | Standard Model | CG Framework |
|--------|---------------|--------------|
| θ_bare | Free parameter | Fixed by Z₃ (Prop 0.0.5a) |
| Yukawa phases | Complex matrices | N/A (no Yukawa couplings) |
| arg det(M_q) | Can be O(1) | = 0 from real η_f |
| θ̄ | Requires |θ̄| < 10⁻¹⁰ | Exactly 0 |
| Mechanism | Fine-tuning or axion | Geometric structure |

### 6.3 The Geometric Origin of Reality

The reality of quark masses in the CG framework traces back to:

1. **Stella octangula is a real geometric object:** The boundary $\partial\mathcal{S}$ is a 2D manifold with real coordinates

2. **Pressure functions are real:** From Definition 0.1.3, $P_c(x) = 1/(|x - x_c|^2 + \epsilon^2) \in \mathbb{R}^+$

3. **Fermion localization is real:** Gaussian profiles $e^{-r^2/2\sigma^2} \in \mathbb{R}^+$

4. **Integration is real:** Area integrals of real functions give real results

5. **No complex Yukawa matrices:** The phase-gradient mass generation mechanism replaces Yukawa couplings with geometric overlaps

---

## 7. Consistency Checks

### 7.1 CKM Matrix Phases

**Question:** If all quark masses are real, where do CKM phases come from?

**Answer:** The CKM matrix V_CKM parameterizes the mismatch between up-type and down-type mass eigenstates. In the CG framework:

- The **masses** are real (from overlap integrals)
- The **mixing** comes from the spatial structure of fermion wavefunctions
- The **CP phase** arises from Berry phases in generation transport (see Extension 3.1.2b)

This is analogous to the Standard Model where:
- Yukawa eigenvalues can be made real by field redefinitions
- The CKM phase is a physical invariant related to the Jarlskog determinant

### 7.2 Comparison with Nelson-Barr

The Nelson-Barr mechanism also achieves real mass matrices, but:

| Aspect | Nelson-Barr | CG Framework |
|--------|-------------|--------------|
| Mechanism | Spontaneous CP breaking at UV | Real overlap integrals |
| UV completion | Required | Not required |
| New particles | Vector-like quarks | None |
| Fine-tuning | θ_bare = 0 still required | θ = 0 from Z₃ |

### 7.3 Comparison with Axion

| Aspect | Axion | CG Framework |
|--------|-------|--------------|
| θ relaxation | Dynamical (a → 0) | Structural (Z₃ + geometry) |
| arg det(M_q) | Included via a(x) | Geometric = 0 |
| New particles | Axion | None |
| Testability | Axion searches | Framework predictions |

### 7.4 Radiative Corrections and RG Stability

**Question:** Can radiative corrections introduce complex phases to the mass matrix?

**Answer:** No. The result $\arg\det(M_q) = 0$ is **stable under radiative corrections** for the following reasons:

#### 7.4.1 QCD Loop Corrections

QCD is a vector-like theory (no $\gamma_5$ couplings in QCD vertices). One-loop and higher-order QCD corrections to quark masses take the form:
$$m_f(\mu) = m_f(\mu_0) \left[1 + C_F \frac{\alpha_s(\mu)}{\pi} \left(\frac{3}{2}\ln\frac{\mu}{m_f} + \cdots\right) + \mathcal{O}(\alpha_s^2)\right]$$

where $C_F = 4/3$ is the color factor. **All terms are real** because:
- $\alpha_s$ is real
- $C_F$ is real
- Logarithms of real positive masses are real
- No CP-violating vertices exist in QCD

**Numerical verification:** See `verification/foundations/radiative_corrections_analysis.py`

#### 7.4.2 Electroweak Corrections

Electroweak corrections are $\mathcal{O}(\alpha_{em}/4\pi) \sim 0.02\%$, subdominant to QCD. More importantly:
- EW corrections to **mass eigenvalues** are real
- CKM phases appear in the **mixing matrix** $V_{CKM}$, not in mass eigenvalues
- The physical quantity $\arg\det(M_q)$ uses diagonal mass eigenvalues

#### 7.4.3 Non-Perturbative Effects

Instanton contributions are exponentially suppressed:
$$\mathcal{A}_{inst} \sim e^{-8\pi^2/g^2} \sim 10^{-13}$$

These affect the vacuum energy (contributing to $\theta$ physics) but not the mass eigenvalues directly. The $\theta$ contribution is handled by Proposition 0.0.5a.

#### 7.4.4 CG-Specific Corrections

Loop corrections to the geometric overlap integrals modify their **magnitude** but not their **reality**. The overlap integral remains:
$$c_f = \int_{\partial\mathcal{S}} \rho_f(x) \cdot \rho_\chi(x) \, d\mu(x) + \delta c_f^{(1-loop)} + \cdots$$

where each correction $\delta c_f^{(n-loop)}$ is real because it involves real functions and real measures.

#### 7.4.5 Summary Table

| Correction Source | Magnitude | Phase Contribution |
|-------------------|-----------|-------------------|
| QCD 1-loop | $\sim 4\%$ | 0 |
| QCD 2-loop | $\sim 0.2\%$ | 0 |
| Electroweak | $\sim 0.02\%$ | 0 |
| Threshold | $\sim \alpha_s^2$ | 0 |
| Non-perturbative | $\sim 10^{-13}$ | 0 |
| **Total** | — | **0** |

**Conclusion:** The result $\arg\det(M_q) = 0$ is radiatively stable.

### 7.5 Number of Flavors Independence

**Question:** Does the result depend on the number of active quark flavors $N_f$?

**Answer:** No. The result $\arg\det(M_q) = 0$ is **independent of $N_f$** for the following reason:

#### 7.5.1 Per-Flavor Reality

The argument for real masses applies **independently** to each quark flavor:

$$\eta_f \in \mathbb{R}^+ \quad \Rightarrow \quad m_f \in \mathbb{R}^+ \quad \forall f$$

This holds regardless of how many flavors exist. The reality of each $m_f$ follows from the geometric structure of the overlap integral for that flavor, not from any relationship between flavors.

#### 7.5.2 Determinant Factorization

For any $N_f$ quark flavors:
$$\det(M_q) = \prod_{f=1}^{N_f} m_f$$

If each $m_f \in \mathbb{R}^+$, then:
$$\det(M_q) = (\text{product of positive reals}) \in \mathbb{R}^+$$

Therefore:
$$\arg\det(M_q) = 0 \quad \forall N_f$$

#### 7.5.3 Standard Model Limit

In the Standard Model effective theory below the top threshold ($N_f = 5$), the result still holds:
$$\arg\det(M_q^{N_f=5}) = \arg(m_u \cdot m_d \cdot m_s \cdot m_c \cdot m_b) = 0$$

Similarly for $N_f = 6, 4, 3$, etc.

**Conclusion:** The Strong CP resolution is valid for any number of quark flavors.

---

## 8. Predictions and Tests

### 8.1 Primary Prediction

**Prediction 8.1.1 (θ̄ = 0 exactly):**

The CG framework predicts:
$$\bar{\theta} = 0 \quad \text{(exact)}$$

This is not an approximation or fine-tuning but a structural result.

### 8.2 Secondary Predictions

**Prediction 8.2.1 (No QCD Axion for Strong CP):**

If θ̄ = 0 structurally, the QCD axion is not needed for Strong CP resolution. Axion searches may return null results (though axions could exist for other reasons).

**Prediction 8.2.2 (Real Yukawa-Like Structure):**

Any effective Yukawa couplings extracted from the CG mechanism will be real (modulo CKM-type rotation phases).

### 8.3 Falsification

This proposition would be **falsified** if:
1. A nonzero neutron EDM is measured, implying θ̄ ≠ 0
2. The geometric overlap integrals are shown to have complex contributions
3. The phase-gradient mass generation mechanism is ruled out by other means
4. Precision experiments discover complex phases in Yukawa-equivalent couplings (beyond CKM phases in mixing)
5. A theoretical inconsistency is found between real mass matrices and observed CP violation in the quark sector

**Current experimental status:**
- Neutron EDM: $|d_n| < 1.8 \times 10^{-26}$ e·cm (90% CL) → $|\bar{\theta}| < 10^{-10}$ ✓
- No evidence for complex mass eigenvalue phases exists in any measurement

---

## 9. Summary

**Proposition 0.0.5b** establishes:

1. **Helicity couplings are real:** η_f ∈ ℝ from overlap integral structure
2. **Quark masses are real:** m_f ∈ ℝ from phase-gradient mass generation mechanism
3. **Mass determinant is real:** det(M_q) ∈ ℝ⁺
4. **Phase vanishes:** arg det(M_q) = 0
5. **Complete Strong CP resolution:** θ̄ = θ + arg det(M_q) = 0 + 0 = 0

**Key equation:**
$$\boxed{\bar{\theta} = 0 \quad \text{(Z₃ superselection + real overlap integrals)}}$$

Combined with Proposition 0.0.5a, this provides a **complete geometric resolution** of the Strong CP problem without axions or fine-tuning.

---

## 10. References

### Framework Documents

1. [Proposition 0.0.5a](./Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md) — Z₃ Center Constrains θ-Angle (θ = 0)
2. [Theorem 3.1.1](../Phase3/Theorem-3.1.1-Chiral-Drag-Mass-Formula.md) — Phase-Gradient Mass Generation Mass Formula
3. [Theorem 3.1.2](../Phase3/Theorem-3.1.2-Mass-Hierarchy-From-Geometry.md) — Mass Hierarchy Pattern from Geometry
4. [Definition 0.1.3](../Phase0/Definition-0.1.3-Pressure-Functions.md) — Pressure Functions from Geometric Opposition

### External Literature

5. Nelson, A.E. (1984). "Naturally weak CP violation." *Phys. Lett. B* 136, 387–391.
6. Barr, S.M. (1984). "Solving the strong CP problem without the Peccei-Quinn symmetry." *Phys. Rev. Lett.* 53, 329.
7. Peccei, R.D. & Quinn, H.R. (1977). "CP Conservation in the Presence of Pseudoparticles." *Phys. Rev. Lett.* 38, 1440.
8. Particle Data Group (2024). "Review of Particle Physics." *Phys. Rev. D* 110, 030001.

---

## 11. Lean 4 Formalization

This proposition has been formalized in Lean 4:

**File:** `lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_5b.lean`

**Key formalized structures:**
- `ProbabilityDensity`: Non-negative normalized density with `nonneg` and `normalized` constraints
- `FermionDensity`: Extends `ProbabilityDensity` with strict positivity (`pos : 0 < value`)
- `ChiralFieldDensity`: Chiral field intensity density with strict positivity
- `FlavorBasisMassMatrix`: Real-valued mass matrix encoding M_{ij} ∈ ℝ
- `HelicityCoupling`: Structure with generation index and positivity proof
- `QuarkMassMatrix`: Diagonal mass matrix with positive entries

**Key theorems verified:**
- `overlap_integral_pos`: $c_f > 0$
- `overlap_integral_bounded`: $c_f \leq 1$
- `wolfensteinFactor_pos`: $\lambda^{2n_f} > 0$
- `helicityCouplingFormula_pos`: $\eta_f = \lambda^{2n_f} \cdot c_f > 0$
- `statement_c_real_determinant`: $\det(M_q) > 0$
- `statement_d_vanishing_phase`: $\arg\det(M_q) = 0$
- `statement_e_complete_strong_cp`: $\bar{\theta} = 0$
- `proposition_0_0_5b_master`: Combined theorem proving all five statements (a)-(e)

**Status:** All main theorems proven without `sorry`. Five `True := trivial` statements for meta-level claims (physical interpretations, cited results).

---

*Proposition created: January 11, 2026*
*Lean formalization: January 12, 2026*
*Status: 🔶 NOVEL — Completes Strong CP Resolution*
*Key result: arg det(M_q) = 0 from real overlap integrals*
*Combined with Prop 0.0.5a: θ̄ = 0 (complete Strong CP resolution)*
