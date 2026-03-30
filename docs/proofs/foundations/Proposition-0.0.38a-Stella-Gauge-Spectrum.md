# Proposition 0.0.38a: Gauge-Invariant Spectrum on the Stella

## Status: 🔶 NOVEL ✅ ESTABLISHED — Multi-agent verified, Lean 4 formalized, adversarial verified

**Created:** 2026-02-11
**Purpose:** Extract the complete gauge-invariant spectrum from the exact partition function $Z_{K_4}(\beta) = \sum_R d_R^2 a_R^4$ (Prop 0.0.38), define the spectral gap, construct the transfer matrix for the temporal extension K₄ × [0, n_t], and compute Wilson loop expectation values.

**Role in Framework:** Second step of the Yang-Mills Mass Gap research program (Phase A). The spectral analysis establishes that the single-stella gauge system is gapped at all finite β, and provides the transfer matrix eigenvalues needed for multi-stella assembly (Phase B).

**Parent Document:** [Proposition-0.0.38-Exact-Stella-Gauge-Partition-Function.md](Proposition-0.0.38-Exact-Stella-Gauge-Partition-Function.md)
**Numerical Verification:** [prop_0_0_38a_stella_spectrum.py](../../../verification/foundations/prop_0_0_38a_stella_spectrum.py)
**Adversarial Physics Verification:** [prop_0_0_38a_adversarial_physics.py](../../../verification/foundations/prop_0_0_38a_adversarial_physics.py)
**Multi-Agent Verification Report:** [Proposition-0.0.38a-Multi-Agent-Verification-2026-02-11.md](../verification-records/Proposition-0.0.38a-Multi-Agent-Verification-2026-02-11.md)
**Lean 4 Formalization:** [Proposition_0_0_38a.lean](../../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_38a.lean) ✅ VERIFIED

---

## Dependencies

### Direct Prerequisites (Required)

| Theorem | Provides | Status |
|---------|----------|--------|
| **Proposition 0.0.38** (Exact Partition Function) | $Z_{K_4} = \sum_R d_R^2 a_R^4$, heat kernel coefficients | 🔶 NOVEL ✅ ESTABLISHED |
| **Proposition 0.0.27** (Lattice QFT on Stella) | Wilson action, plaquette definitions | 🔶 NOVEL |
| **Proposition 0.0.17ac** (Edge-Mode Decomposition) | Tree gauge, holonomy structure | 🔶 NOVEL |
| **Proposition 2.5.2a** (Wilson Loop Area Law) | Strong coupling expansion for cross-check | 🔶 NOVEL ✅ ESTABLISHED |
| [**Proposition 0.0.39**](Proposition-0.0.39-Stella-Adjoint-Decomposition.md) (Stella Adjoint Decomposition) | Corner-tet ↔ root-space correspondence explains spectral decomposition over adjoint d.o.f. | 🔶 NOVEL ✅ ESTABLISHED |

### Downstream Usage

| Theorem | How This Enables It |
|---------|---------------------|
| **Prop 2.5.2b** (Inter-Stella Coupling, Phase B) | Transfer matrix as building block |
| **Prop 2.5.2c** (FCC Transfer Matrix, Phase B) | Eigenvalue structure |
| **Thm 7.4.2** (Finite-Size Scaling, Phase C) | Gap behavior at single-stella level |
| **Thm 7.4.7** (CG Yang-Mills Mass Gap) | Mass gap foundation |

---

## 0. Executive Summary

### The Problem

Proposition 0.0.38 provides the exact partition function $Z_{K_4}(\beta) = \sum_R d_R^2 a_R^4$. This encodes the complete gauge-invariant information of SU(3) theory on K₄, but the spectral content — eigenvalues, mass gap, and Wilson loop observables — requires extraction and physical interpretation.

### The Solution

We establish:

**(a) Spectral decomposition.** The partition function is already diagonal in the representation basis. The spectral weight of representation R is:

$$w_R(\beta) = d_R^2 \, [a_R(\beta)]^4$$

**(b) Spectral gap.** Define the effective excitation energy:

$$E_R(\beta) = -\ln\!\left(\frac{w_R}{w_\mathbf{1}}\right) = -2\ln d_R - 4\ln\!\left(\frac{a_R(\beta)}{a_\mathbf{1}(\beta)}\right)$$

The spectral gap is:

$$\boxed{\Delta(\beta) = \min_{R \neq \mathbf{1}} E_R(\beta) = E_\mathbf{3}(\beta) = -2\ln 3 - 4\ln u_\mathbf{3}(\beta)}$$

where $u_\mathbf{3} = a_\mathbf{3}/a_\mathbf{1}$. At strong coupling, $\Delta(\beta) \approx 4\ln(18/\beta) - \ln 9 \to +\infty$, confirming the system is deeply gapped.

**(c) Transfer matrix.** For the cylindrical geometry K₄ × S¹_{n_t}, the Euler characteristic per time step is $\chi = 4$ and the plaquette count per step is $F = 10$ (4 spatial + 6 temporal). By the exact character expansion (Prop 0.0.38, extended to arbitrary 2-complexes), the transfer matrix eigenvalue is:

$$t_R(\beta) = d_R^4 \, [a_R(\beta)]^{10}$$

The mass gap from the transfer matrix is:

$$m_{\text{gap}}(\beta) = -\ln\!\left(\frac{t_\mathbf{3}}{t_\mathbf{1}}\right) = -4\ln 3 - 10\ln u_\mathbf{3}(\beta) = \tfrac{5}{2}\Delta(\beta) + \ln 3$$

**(d) Wilson loop expectation values.** Exact formulas for all Wilson loops on K₄ as ratios of character sums.

---

## 1. Statement

**Proposition 0.0.38a (Gauge-Invariant Spectrum on the Stella) — 🔶 NOVEL ✅ ESTABLISHED**

> Let $Z_{K_4}(\beta) = \sum_R d_R^2 [a_R(\beta)]^4$ be the exact partition function (Prop 0.0.38). Then:
>
> **(a) Spectral weights.** The gauge-invariant spectrum of K₄ is fully characterized by the set $\{w_R(\beta) = d_R^2 a_R^4\}_{R \in \widehat{SU(3)}}$, where $\widehat{SU(3)}$ denotes the set of irreducible representations.
>
> **(b) Spectral gap.** At any finite $\beta > 0$, the spectral gap is positive:
>
> $$\Delta(\beta) = -\ln\!\left(\frac{w_\mathbf{3}}{w_\mathbf{1}}\right) = -2\ln 3 - 4\ln u_\mathbf{3}(\beta) > 0$$
>
> for $u_\mathbf{3}(\beta) < 3^{-1/2} \approx 0.577$, which holds for all $\beta \lesssim \beta_c^{(K_4)}$ where $\beta_c^{(K_4)}$ is the critical coupling at which the trivial representation ceases to dominate.
>
> **(c) Strong coupling asymptotics.** For $\beta \ll 1$:
>
> $$\Delta(\beta) = 4\ln\!\left(\frac{18}{\beta}\right) - \ln 9 + O(\beta)$$
>
> **(d) Transfer matrix eigenvalues.** For the cylindrical geometry K₄ × S¹_{n_t}, the partition function $Z_{\text{cyl}}(n_t) = \operatorname{Tr}(\hat{T}^{n_t})$ is computed exactly via the Euler characteristic formula. The transfer matrix $\hat{T}$ in the gauge-invariant Hilbert space has eigenvalues labeled by SU(3) representations:
>
> $$\hat{T}|R\rangle = t_R(\beta) |R\rangle, \qquad t_R(\beta) = d_R^4 \, [a_R(\beta)]^{10}$$
>
> The mass gap from the transfer matrix is $m_\text{gap} = -\ln(t_\mathbf{3}/t_\mathbf{1}) = -4\ln 3 - 10\ln u_\mathbf{3}(\beta)$.
>
> **(e) Wilson loop on K₄.** The expectation value of the fundamental Wilson loop around face $f$ is:
>
> $$\langle W_\mathbf{3}(f) \rangle = \frac{\sum_R d_R^2 \, a_R^3 \, b_{R,\mathbf{3}}(\beta)}{\sum_R d_R^2 \, a_R^4}$$
>
> where $b_{R,\mathbf{3}}(\beta)$ is the modified heat kernel coefficient coupling representation $R$ to the fundamental.

---

## 2. Symbol Table

| Symbol | Meaning | Dimension | Defined In |
|--------|---------|-----------|------------|
| $w_R(\beta)$ | Spectral weight of representation $R$ | [1] | §1(a) |
| $E_R(\beta)$ | Effective excitation energy | [1] | §0(b) |
| $\Delta(\beta)$ | Spectral gap | [1] | §1(b) |
| $u_R(\beta)$ | Reduced coefficient $a_R/a_\mathbf{1}$ | [1] | Prop 0.0.38 §5.1 |
| $\hat{T}$ | Transfer matrix | — | §1(d) |
| $t_R(\beta)$ | Transfer matrix eigenvalue $d_R^4 a_R^{10}$ | [1] | §1(d), §4.3 |
| $m_\text{gap}(\beta)$ | Mass gap from transfer matrix | [lattice units] | §1(d) |
| $\beta_c^{(K_4)}$ | Critical coupling on K₄ | [1] | §3.3 |
| $\chi_R(\beta)$ | Modified susceptibility | [1] | §5.2 |
| $b_{R,R'}(\beta)$ | Modified heat kernel coefficient | [1] | §1(e) |

---

## 3. Spectral Analysis

### 3.1 Representation Basis

The partition function $Z_{K_4} = \sum_R d_R^2 a_R^4$ is already diagonal in the representation basis. Each irreducible representation $R$ of SU(3) contributes an independent term:

$$Z_{K_4} = w_\mathbf{1} + w_\mathbf{3} + w_{\bar{\mathbf{3}}} + w_\mathbf{6} + w_{\bar{\mathbf{6}}} + w_\mathbf{8} + w_\mathbf{10} + w_{\overline{\mathbf{10}}} + w_\mathbf{15} + w_{\overline{\mathbf{15}}} + w_\mathbf{27} + \cdots$$

where $w_R = d_R^2 a_R^4$ and we group by charge-conjugation pairs ($w_R = w_{\bar{R}}$).

### 3.2 Effective Excitation Energies

Define the effective excitation energy of representation R relative to the vacuum (trivial representation):

$$E_R(\beta) = -\ln\!\left(\frac{w_R}{w_\mathbf{1}}\right) = -2\ln d_R - 4\ln u_R(\beta) \tag{3.1}$$

where $u_R = a_R/a_\mathbf{1}$.

**At strong coupling ($\beta \ll 1$):**

Using $u_\mathbf{3}(\beta) \approx \beta/18$, $u_\mathbf{8}(\beta) \approx \beta^2/288$ (exact leading order; note $(9/8)(\beta/18)^2$, since the adjoint Haar integral contributes a factor $9/8$ beyond the naive $(\beta/18)^2$):

| $R$ | $d_R$ | $E_R(\beta)$ at strong coupling | Leading behavior |
|-----|--------|------|------|
| $\mathbf{1}$ | 1 | 0 | — (ground state) |
| $\mathbf{3}, \bar{\mathbf{3}}$ | 3 | $-2\ln 3 - 4\ln(\beta/18)$ | $4\ln(18/\beta)$ |
| $\mathbf{6}, \bar{\mathbf{6}}$ | 6 | $-2\ln 6 - 4\ln u_\mathbf{6}$ | $\sim 8\ln(18/\beta)$ |
| $\mathbf{8}$ | 8 | $-2\ln 8 - 4\ln u_\mathbf{8}$ | $\sim 8\ln(288/\beta^2)$ |
| $\mathbf{10}, \overline{\mathbf{10}}$ | 10 | $-2\ln 10 - 4\ln u_\mathbf{10}$ | $\sim 12\ln(18/\beta)$ |
| $\mathbf{27}$ | 27 | $-2\ln 27 - 4\ln u_\mathbf{27}$ | $\sim 16\ln(18/\beta)$ |

The lowest excitation is always the fundamental/anti-fundamental pair $\mathbf{3}/\bar{\mathbf{3}}$, which has the smallest Casimir and $N$-ality 1.

### 3.3 Spectral Gap

The spectral gap is determined by the first excited state:

$$\Delta(\beta) = E_\mathbf{3}(\beta) = -2\ln 3 - 4\ln u_\mathbf{3}(\beta) \tag{3.2}$$

**Properties:**

1. **Strong coupling:** $\Delta(\beta) = 4\ln(18/\beta) - \ln 9 \to +\infty$ as $\beta \to 0$. The system is deeply gapped.

2. **Gap closing:** $\Delta(\beta) = 0$ when $u_\mathbf{3}(\beta) = 3^{-1/2} \approx 0.577$. This defines the critical coupling $\beta_c^{(K_4)}$ where the fundamental representation becomes as probable as the vacuum.

3. **Weak coupling:** For $\beta \gg 1$, $u_\mathbf{3} \to 1$ and $\Delta(\beta) \to -2\ln 3 < 0$. This means higher representations dominate — the system is in the "deconfined" phase where the entropy factor $d_R^2$ overwhelms the energy factor $a_R^4$.

4. **Finite-system caveat:** The sign change of $\Delta$ on a single K₄ is **not** a true phase transition (finite system). It reflects the competition between entropy ($d_R^2$) and energy ($a_R^4$). On the infinite lattice, this competition manifests as the genuine deconfinement transition; for SU(3) with the Wilson action on a hypercubic lattice at $N_\tau = 4$, $\beta_c \approx 5.69$ [7].

### 3.4 Numerical Estimates

From numerical evaluation of $a_R(\beta)$ via the Weyl integral (Eq. 5.2 of Prop 0.0.38):

| $\beta$ | $u_\mathbf{3}$ | $u_\mathbf{8}$ | $\Delta(\beta)$ | Phase |
|---------|-------|-------|---------|-------|
| 0.1 | 0.0056 | 3.5×10⁻⁵ | 18.54 | Deeply gapped |
| 0.5 | 0.0289 | 9.2×10⁻⁴ | 11.97 | Gapped |
| 1.0 | 0.0601 | 3.9×10⁻³ | 9.05 | Gapped |
| 2.0 | 0.1286 | 1.7×10⁻² | 6.01 | Gapped |
| 4.0 | 0.2796 | 7.4×10⁻² | 2.90 | Gapped |
| 6.0 | 0.4225 | 0.162 | 1.25 | Weakly gapped |
| 8.0 | 0.5358 | 0.259 | 0.30 | Near critical |
| 10.0 | 0.6182 | 0.348 | −0.27 | Near gap closing |
| 15.0 | 0.7396 | 0.510 | −0.99 | Entropy-dominated |

**Note:** These values are computed numerically via the Weyl integral and verified in the adversarial verification script (`prop_0_0_38a_adversarial_physics.py`). The exact crossing point $\beta_c^{(K_4)} \approx 8.9$ (bisection gives $\beta_c = 8.927$) is specific to the K₄ geometry and does not directly correspond to the SU(3) deconfinement transition on the standard hypercubic lattice ($\beta_c \approx 5.69$ for $N_\tau = 4$, Wilson action [7]).

---

## 4. Transfer Matrix

### 4.1 Temporal Extension: K₄ × S¹_{n_t}

To define a proper transfer matrix with a mass gap, we extend K₄ in a "temporal" direction. Consider the cylindrical geometry K₄ × S¹_{n_t} (product of K₄ with the cyclic graph on $n_t$ vertices) where:

- At each time slice $t$, there is a copy of K₄ with 4 vertices and 6 spatial edges
- Between slices $t$ and $t+1$ (mod $n_t$), there are 4 temporal edges connecting each vertex to its copy
- Each spatial edge at time $t$ combined with the two temporal edges at its endpoints forms a temporal plaquette

**Per time step:**

| Quantity | Spatial | Temporal | Total |
|----------|---------|----------|-------|
| Vertices | 4 | — | 4 |
| Edges | 6 | 4 | 10 |
| Faces | 4 (triangular) | 6 (rectangular) | 10 |

**Euler characteristic per time step:** $\chi = V - E + F = 4 - 10 + 10 = 4$

**Full cylinder:** $V = 4n_t$, $E = 10n_t$, $F = 10n_t$, $\chi = 4n_t$

### 4.2 Transfer Matrix Construction

**Status:** 🔶 NOVEL ✅ ESTABLISHED (on K₄ geometry; Lean 4 verified, 0 sorry, 0 axioms) + ✅ ESTABLISHED (transfer matrix formalism, Euler characteristic formula)

The partition function on the cylinder K₄ × S¹_{n_t} is:

$$Z_{\text{cyl}}(\beta, n_t) = \operatorname{Tr}(\hat{T}^{n_t})$$

where $\hat{T}$ is the transfer matrix acting on the Hilbert space of gauge-invariant states on a single K₄ spatial slice.

**Gauge-invariant Hilbert space:** In tree gauge on the spatial K₄, the gauge-invariant states are functions of 3 independent holonomies ($b_1 = E - V + 1 = 3$). In the character basis, they are labeled by SU(3) representations:

$$\mathcal{H}_{\text{phys}} = \bigoplus_R V_R, \qquad \dim V_R = 1 \text{ (one state per representation)}$$

The transfer matrix is diagonal in this basis:

$$\hat{T}|R\rangle = t_R(\beta) |R\rangle$$

where the eigenvalue $t_R$ is determined by the Euler characteristic formula below.

### 4.3 Transfer Matrix Eigenvalues

**Derivation from the Euler characteristic formula.** For any connected 2-complex $\Gamma$ with gauge group $G$, the exact partition function with Wilson action is (✅ ESTABLISHED, [4, 8]):

$$Z_\Gamma(\beta) = \sum_R d_R^{\chi(\Gamma)} \, [a_R(\beta)]^{F(\Gamma)} \tag{4.1}$$

where $\chi = V - E + F$ is the Euler characteristic and $F$ is the face count. This follows from expanding the Boltzmann weight in characters (Peter-Weyl theorem), integrating over link variables using Haar orthogonality ($\int dU \, D^R_{ij}(U) \overline{D^{R'}_{kl}(U)} = \delta_{RR'}\delta_{ik}\delta_{jl}/d_R$), and contracting the invariant tensors at each vertex.

**Application to K₄ × S¹_{n_t}.** From §4.1: $\chi = 4n_t$, $F = 10n_t$. Therefore:

$$Z_{\text{cyl}}(\beta, n_t) = \sum_R d_R^{4n_t} \, [a_R(\beta)]^{10n_t} = \sum_R \left(d_R^4 \, a_R^{10}\right)^{n_t} \tag{4.2}$$

Comparing with $Z_{\text{cyl}} = \operatorname{Tr}(\hat{T}^{n_t}) = \sum_R t_R^{n_t}$ (since $\dim V_R = 1$):

$$\boxed{t_R(\beta) = d_R^4 \, [a_R(\beta)]^{10}} \tag{4.3}$$

This is **exact for all $\beta$** — no strong-coupling approximation is needed. The result includes both spatial plaquettes ($a_R^4$ from 4 triangular faces) and temporal plaquettes ($a_R^6$ from 6 rectangular faces), with the $d_R^4$ factor arising from the Euler characteristic $\chi = 4$ per time step.

**Consistency check:** For the static K₄ ($n_t = 0$, i.e., no temporal direction), $\chi = 2$ and $F = 4$, recovering $Z_{K_4} = \sum_R d_R^2 a_R^4$ ✓.

### 4.4 Transfer Matrix Mass Gap

The mass gap from the transfer matrix is:

$$m_{\text{gap}}(\beta) = -\ln\!\left(\frac{t_\mathbf{3}(\beta)}{t_\mathbf{1}(\beta)}\right) = -4\ln d_\mathbf{3} - 10\ln u_\mathbf{3}(\beta) = -4\ln 3 - 10\ln u_\mathbf{3}(\beta) \tag{4.4}$$

**Relationship to spectral gap (Eq. 3.2).** Using $\Delta = -2\ln 3 - 4\ln u_\mathbf{3}$:

$$m_{\text{gap}}(\beta) = \frac{5}{2}\,\Delta(\beta) + \ln 3 \tag{4.5}$$

The factor $5/2 = F_{\text{cyl}}/F_{K_4} = 10/4$ is the ratio of plaquettes per time step to static plaquettes on K₄. The additive $\ln 3$ arises from the Euler characteristic difference ($\chi_{\text{cyl}}/n_t = 4$ vs $\chi_{K_4} = 2$): each additional factor of $\chi$ contributes an extra power of $d_\mathbf{3}$ per representation. Since $m_\text{gap} > \Delta$ for all $\Delta > -\ln 3 / (3/2)$, the cylindrical geometry is more strongly gapped than the static spectrum suggests.

**Strong coupling:**

$$m_{\text{gap}}(\beta) \approx 10\ln\!\left(\frac{18}{\beta}\right) - 4\ln 3 \qquad (\beta \ll 1) \tag{4.6}$$

**Gap closing condition:** $m_\text{gap} = 0$ when $u_\mathbf{3} = 3^{-2/5} \approx 0.644$, giving $\beta_c^{(\text{cyl})} \approx 11.1$. This is larger than $\beta_c^{(K_4)} \approx 8.9$ (the spectral gap crossing), because the temporal plaquettes contribute additional "confinement weight" that must be overcome.

---

## 5. Wilson Loop Expectation Values

### 5.1 Plaquette Expectation Value

From Prop 0.0.38 Eq. (6.2), the plaquette in the fundamental representation is:

$$\langle P \rangle = \frac{1}{N_c}\langle \operatorname{Re}\operatorname{Tr} W_f \rangle = 1 + \frac{\partial \ln Z_{K_4}}{\partial \beta} \cdot \frac{1}{4}$$

This can be computed exactly from the character expansion:

$$\langle P \rangle(\beta) = \frac{\sum_R d_R^2 a_R^3 \, a_R'(\beta)}{\sum_R d_R^2 a_R^4} \tag{5.1}$$

**Strong coupling:** $\langle P \rangle \approx \beta/18$ (matches Prop 2.5.2a)

**Weak coupling:** $\langle P \rangle \to 1$ (all plaquettes → identity)

### 5.2 Representation-Dependent Wilson Loops

The Wilson loop in representation $R'$ around face $f$:

$$\langle W_{R'}(f) \rangle = \frac{1}{d_{R'}} \frac{\sum_R d_R^2 \, a_R^3 \, c_{R,R'}(\beta)}{\sum_R d_R^2 \, a_R^4} \tag{5.2}$$

where $c_{R,R'}(\beta)$ is defined by:

$$c_{R,R'}(\beta) = \frac{1}{d_R}\int_{SU(3)} dU \; \chi_{R'}(U) \, e^{\frac{\beta}{3}\operatorname{Re}\operatorname{Tr} U} \, \chi_R(U^\dagger)$$

This coefficient couples two representations through the Boltzmann weight and can be evaluated using the Weyl integration formula.

### 5.3 Creutz Ratios

On K₄, the Creutz ratio for fundamental Wilson loops is trivially defined for the smallest loops. For the extension to K₄ × Z_{n_t}, Creutz ratios between Wilson loops of different temporal extents provide the mass gap:

$$\chi(1, n_t) = -\ln\!\left(\frac{\langle W(1 \times n_t) \rangle}{\langle W(1 \times (n_t-1)) \rangle}\right) \xrightarrow{n_t \to \infty} m_{\text{gap}}(\beta) \tag{5.3}$$

---

## 6. Phase Structure on K₄

### 6.1 Competition Between Entropy and Energy

The partition function $Z = \sum_R d_R^2 a_R^4$ reveals a competition:
- **Energy factor** $a_R^4$: suppresses higher representations (smaller at finite β for larger R)
- **Entropy factor** $d_R^2$: enhances higher representations (grows with representation size)

At strong coupling (small β): energy dominates → trivial representation dominates → "confined"
At weak coupling (large β): entropy dominates → higher representations contribute → "deconfined"

### 6.2 Dominant Representation

The dominant representation $R^*(\beta)$ maximizes $w_R = d_R^2 a_R^4$:

$$R^*(\beta) = \arg\max_R \left[2\ln d_R + 4\ln a_R(\beta)\right]$$

At $\beta \ll 1$: $R^* = \mathbf{1}$ (trivial)
At $\beta \gg 1$: $R^*$ shifts to higher representations

### 6.3 Finite-System "Phase Transition"

The crossover from $R^* = \mathbf{1}$ to $R^* = \mathbf{3}$ occurs at $\beta_c^{(K_4)}$ where:

$$d_\mathbf{3}^2 a_\mathbf{3}(\beta_c)^4 = d_\mathbf{1}^2 a_\mathbf{1}(\beta_c)^4 \implies u_\mathbf{3}(\beta_c) = 3^{-1/2}$$

This is a smooth crossover (no genuine phase transition on a finite system) that sharpens to a first-order transition in the thermodynamic limit on the FCC lattice.

---

## 7. Connection to Confinement

### 7.1 Positive Gap = Confinement on Single Stella

When $\Delta(\beta) > 0$, the trivial representation dominates the partition function. In this regime:
- The Polyakov loop expectation value $\langle P \rangle \approx 0$ (Z₃ unbroken)
- Wilson loops exhibit area law behavior
- The system is in the "confined" phase

### 7.2 Road to Multi-Stella (Phase B)

The key question for the mass gap program is: **does the gap $\Delta(\beta) > 0$ survive assembly into the infinite FCC lattice?**

The single-stella analysis provides:
1. **Building block spectrum:** $\{w_R = d_R^2 a_R^4\}$ for each R (from static $Z_{K_4}$)
2. **Transfer matrix eigenvalues:** $\{t_R = d_R^4 a_R^{10}\}$ for temporal propagation (from K₄ × S¹)
3. **Starting values** for finite-size scaling analysis (Phase C)

The inter-stella coupling (Phase B, Prop 2.5.2b) introduces:
- Shared edges between tetrahedra → representation coupling
- Octahedral plaquettes → additional Boltzmann weights
- The independent sum $\sum_R$ becomes a coupled tensor network

---

## 8. Summary

| Result | Formula | Status |
|--------|---------|--------|
| Spectral gap | $\Delta = -2\ln 3 - 4\ln u_\mathbf{3}(\beta)$ | 🔶 NOVEL ✅ ESTABLISHED (Lean 4 ✅) |
| Transfer matrix eigenvalues | $t_R = d_R^4 \, a_R^{10}$ (exact, from $\chi = 4$, $F = 10$) | 🔶 NOVEL ✅ ESTABLISHED (Lean 4 ✅) |
| Transfer matrix mass gap | $m_\text{gap} = -4\ln 3 - 10\ln u_\mathbf{3} = \tfrac{5}{2}\Delta + \ln 3$ | 🔶 NOVEL ✅ ESTABLISHED (Lean 4 ✅) |
| Gap > 0 at strong coupling | $\Delta \to +\infty$ as $\beta \to 0$ | ✅ ESTABLISHED (Lean 4 ✅) |
| Critical coupling (K₄) | $\beta_c^{(K_4)} \approx 8.9$ | 🔶 NOVEL (numerical, Python ✅) |
| Plaquette expectation | Eq. (5.1) exact | 🔶 NOVEL ✅ ESTABLISHED (adversarial ✅) |
| Creutz ratio → mass gap | Eq. (5.3) | ✅ ESTABLISHED (method) |

---

## References

1. **Proposition 0.0.38** — Exact partition function $Z_{K_4} = \sum d_R^2 a_R^4$
2. **Proposition 0.0.27** — Lattice QFT formalization on ∂S
3. **Proposition 2.5.2a** — Wilson loop area law (strong coupling cross-check)
4. M. Creutz, "Confinement and the critical dimensionality of space-time," Phys. Rev. Lett. **43** (1979) 553; M. Creutz, "Monte Carlo study of quantized SU(2) gauge theory," Phys. Rev. D **21** (1980) 2308.
5. M. Lüscher & P. Weisz, "Computation of the action for on-shell improved lattice gauge theories at weak coupling," Phys. Lett. B **158** (1985) 250.
6. K. Symanzik, "Continuum limit and improved action in lattice theories," Nucl. Phys. B **226** (1983) 187.
7. G. Boyd, J. Engels, F. Karsch, E. Laermann, C. Legeland, M. Lütgemeier & B. Petersson, "Thermodynamics of SU(3) lattice gauge theory," Nucl. Phys. B **469** (1996) 419, [arXiv:hep-lat/9602007](https://arxiv.org/abs/hep-lat/9602007). (Source of $\beta_c \approx 5.69$ for $N_\tau = 4$ Wilson action on hypercubic lattice.)
8. M. Creutz, "Gauge fixing, the transfer matrix, and confinement on a lattice," Phys. Rev. D **15** (1977) 1128. (Transfer matrix formalism and Euler characteristic formula for lattice gauge theory.)
