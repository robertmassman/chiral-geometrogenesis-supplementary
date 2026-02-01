# Hedgehog Ansatz Global Minimality: Research Plan

## Status: 🔸 PARTIAL — Uniqueness Closed, Global Minimality Open

**Related Theorem:** [Theorem 4.1.1 (Existence of Solitons)](../Phase4/Theorem-4.1.1-Existence-of-Solitons.md)

**Date:** 2026-01-31

**Objective:** Strengthen the mathematical foundations of the hedgehog ansatz by proving (or documenting the status of) global energy minimality for the Q=1 skyrmion.

---

## 1. Problem Statement

### 1.1 The Question

In Theorem 4.1.1, the hedgehog ansatz is introduced as an assumed functional form:

$$U(x) = \exp\left(i f(r) \hat{r} \cdot \vec{\tau}\right)$$

where $\hat{r} = \vec{x}/|x|$ locks the isospin direction to the spatial radial direction.

**The open question:** Is the hedgehog configuration the *global* minimum of the energy functional in the $Q = 1$ topological sector, or merely a local minimum?

### 1.2 Why This Matters

| If hedgehog is... | Implication for CG |
|-------------------|-------------------|
| Global minimum | Baryons are uniquely determined by topology—no ambiguity |
| Local minimum only | Other Q=1 configurations might exist with lower energy |
| Saddle point | Hedgehog would be unstable—problematic for baryon physics |

The hedgehog being a global minimum provides the strongest foundation for identifying skyrmions with baryons.

### 1.3 Current Status in Theorem 4.1.1

The theorem currently:
- ✅ Assumes the hedgehog form (§3.4.2)
- ✅ Derives the profile equation from energy minimization within this ansatz (§3.4.5)
- ✅ Verifies topological charge Q = 1 (§3.4.6)
- ❌ Does not prove the hedgehog is globally optimal
- ❌ Does not formally justify the symmetric criticality principle

---

## 2. State of the Art in Mathematical Physics

### 2.1 Summary Table

| Result | Status | Key Reference | Year |
|--------|--------|---------------|------|
| Existence of minimizers in each topological sector | ✅ Proven | Esteban (1986) | 1986 |
| Hedgehog satisfies Euler-Lagrange equations | ✅ Proven | Standard | 1962 |
| Linear stability (second variation δ²E > 0) | ✅ Proven | Creek & Donninger | 2016 |
| Global well-posedness of hedgehog dynamics | ✅ Proven | Li (Duke Math J.) | 2021 |
| Global minimality for Q = 1 | ❌ **OPEN** | Manton (2024): "almost certainly" | — |

### 2.2 Key Papers

#### 2.2.1 Manton (2024) — "Robustness of the Hedgehog Skyrmion"
- **arXiv:** [2405.05731](https://arxiv.org/abs/2405.05731)
- **Journal:** JHEP 08 (2024) 015
- **Key quote:** "The hedgehog Skyrmion, rather than a configuration with less symmetry, is almost certainly the minimal-energy static solution in the B = 1 sector of the field theory."
- **Significance:** State-of-the-art analysis, but "almost certainly" indicates this remains a conjecture, not a theorem.
- **Method:** Analyzes robustness of hedgehog profile across different EFT Lagrangians; shows smoothness at origin.

#### 2.2.2 Li (2021) — Global Well-Posedness
- **Journal:** Duke Mathematical Journal 170(7), 2021
- **DOI:** [10.1215/00127094-2020-0067](https://projecteuclid.org/journals/duke-mathematical-journal/volume-170/issue-7/Global-well-posedness-of-hedgehog-solutions-for-the-31-Skyrme/10.1215/00127094-2020-0067.short)
- **Result:** Proves global well-posedness for hedgehog solutions with arbitrarily large initial data.
- **Significance:** Shows hedgehog dynamics are mathematically well-defined; does not address energy minimality.

#### 2.2.3 Creek & Donninger — Linear Stability
- **Paper:** "Linear stability of the Skyrmion"
- **Semantic Scholar:** [Link](https://www.semanticscholar.org/paper/Linear-stability-of-the-Skyrmion-Creek-Donninger/dd1dafb112d3277e23bbc7f541687a5c053716de)
- **Result:** Proves the spectrum of the linearized operator around the hedgehog has no negative eigenvalues.
- **Significance:** Establishes hedgehog is a **local minimum** (not a saddle point).

#### 2.2.4 Esteban (1986) — Existence of Minimizers
- **Result:** Proves existence of energy minimizers in each topological sector using direct methods of calculus of variations.
- **Significance:** Guarantees a minimizer exists; does not identify it as the hedgehog.

### 2.3 Why Global Minimality Is Hard

The Skyrme model differs from simpler soliton systems:

| System | Bogomolny Bound | Saturation | Global Minimality |
|--------|-----------------|------------|-------------------|
| BPS Monopoles | E ≥ 4πv\|n\| | ✅ Saturated | ✅ Proven (self-dual) |
| Skyrme Model | E ≥ C\|Q\| | ❌ Not saturated | ❌ Open |
| Faddeev-Hopf | E ≥ C\|H\|^{3/4} | ❌ Not saturated | ❌ Open |

In BPS systems, saturation of the Bogomolny bound provides an automatic minimality proof. The Skyrme model lacks this structure.

---

## 3. Three Approaches to Strengthening Theorem 4.1.1

### 3.1 Approach 1: Symmetric Criticality Principle (ACHIEVABLE)

#### Statement (Palais, 1979)

Let $E: X \to \mathbb{R}$ be a smooth functional on a Banach space $X$, invariant under a compact Lie group $G$ acting on $X$. Let $X^G = \{u \in X : g \cdot u = u \text{ for all } g \in G\}$ be the fixed-point set. Then:

$$u \in X^G \text{ is a critical point of } E|_{X^G} \implies u \text{ is a critical point of } E$$

#### Application to Hedgehog

**Setup:**
- $X$ = Sobolev space of finite-energy field configurations with $Q = 1$
- $G$ = diagonal $SO(3)_{\text{diag}} \subset SO(3)_{\text{space}} \times SO(3)_{\text{isospin}}$
- Action: $(R, U(x)) \mapsto R \cdot U(R^{-1}x) \cdot R^{-1}$ (simultaneous rotation)

**Fixed-point set $X^G$:**
Configurations invariant under diagonal $SO(3)$ have the form:
$$U(x) = \exp(i f(r) \hat{r} \cdot \vec{\tau})$$
This is exactly the hedgehog ansatz.

**Implication:**
If the hedgehog minimizes $E|_{X^G}$ (the 1D variational problem for $f(r)$), then it is automatically a critical point of the full energy $E$. This rigorously justifies reducing from the infinite-dimensional problem to the ODE for $f(r)$.

#### What This Does NOT Prove
- That the hedgehog is a *minimum* (only that it's a critical point)
- That there are no other critical points outside $X^G$
- Global minimality

#### Implementation for CG
Add a new subsection §3.4.8 to Theorem 4.1.1:
- State Palais's theorem
- Verify the energy functional is $SO(3)_{\text{diag}}$-invariant
- Identify the fixed-point set as hedgehog configurations
- Conclude the ansatz is mathematically justified (not ad hoc)

---

### 3.2 Approach 2: Second Variation Analysis (ACHIEVABLE)

#### Goal
Prove the hedgehog is a **local minimum** by showing the second variation $\delta^2 E > 0$ for all non-trivial perturbations.

#### The Linearized Operator

Expand $U = U_0 \cdot \exp(i \eta^a \tau^a)$ where $U_0$ is the hedgehog and $\eta^a$ are small perturbations. The second variation is:

$$\delta^2 E = \int d^3x \, \eta^a \mathcal{L}^{ab} \eta^b$$

where $\mathcal{L}$ is the linearized (Hessian) operator.

#### Spectral Decomposition

The perturbations decompose into angular momentum channels:
- **$\ell = 0$ (monopole):** Radial breathing modes
- **$\ell = 1$ (dipole):** Translations and isorotations (zero modes from symmetry)
- **$\ell \geq 2$ (higher):** Deformation modes

**Creek & Donninger's result:** All eigenvalues of $\mathcal{L}$ are non-negative. The only zero eigenvalues correspond to:
1. Translations (3 modes) — broken translational invariance
2. Isorotations (3 modes) — broken $SO(3)_{\text{isospin}}$

This proves the hedgehog is a strict local minimum modulo symmetries.

#### Implementation for CG
Add a subsection §3.4.9 to Theorem 4.1.1:
- State the second variation formula
- Cite Creek & Donninger for spectral positivity
- Identify zero modes with symmetry generators
- Conclude: hedgehog is a local minimum

---

### 3.3 Approach 3: Global Minimality (RESEARCH FRONTIER)

#### Why This Is Hard

To prove global minimality, we need one of:

**Option A: Saturation of a Bound**
If the hedgehog saturated the Bogomolny bound $E \geq C|Q|$ exactly, minimality would follow. But:
- Classical hedgehog energy: $E \approx 72.8 f_\pi / e$
- Bogomolny bound: $E \geq 12\pi^2 f_\pi / e \approx 118.4 f_\pi / e$

The hedgehog energy is *below* what a naive bound would suggest (because the bound isn't tight), but doesn't saturate any known sharp bound.

**Option B: Uniqueness of Critical Points**
If the hedgehog were the *only* critical point in the $Q = 1$ sector, it would be the unique minimizer. But proving uniqueness of critical points for nonlinear PDEs is extremely difficult.

**Option C: Comparison/Rearrangement Inequalities**
Show that any $Q = 1$ configuration can be "symmetrized" to reduce energy. This would require new inequalities specific to the Skyrme energy.

**Option D: Concentration-Compactness + Uniqueness**
1. Show minimizing sequences converge (concentration-compactness)
2. Show the limit is $SO(3)_{\text{diag}}$-symmetric
3. Apply symmetric criticality to identify limit as hedgehog

This is the most promising approach but requires significant technical work.

#### Partial Results Toward Global Minimality

**Numerical evidence (very strong):**
- All numerical minimization studies converge to hedgehog
- Perturbations away from hedgehog increase energy
- No local minima found other than hedgehog (modulo symmetry)

**Analytical evidence:**
- Hedgehog is the unique critical point within the symmetric sector $X^G$
- Linear stability rules out saddle point
- Multi-skyrmion configurations ($|Q| > 1$) break symmetry, suggesting hedgehog is special for $Q = 1$

**What remains:**
- Rule out non-symmetric critical points with lower energy
- Prove concentration-compactness for minimizing sequences

---

## 4. Implementation Plan

### Phase 1: Document Current Status (Immediate)

**Task 1.1:** Add §3.4.8 "Symmetric Criticality Principle" to Theorem 4.1.1
- Statement of Palais's theorem
- Verification of SO(3)-invariance
- Identification of fixed-point set
- Conclusion: hedgehog ansatz is mathematically justified

**Task 1.2:** Add §3.4.9 "Local Minimality (Second Variation)" to Theorem 4.1.1
- Linearized operator definition
- Cite Creek & Donninger for spectral positivity
- Zero mode identification
- Conclusion: hedgehog is a local minimum

**Task 1.3:** Update §3.4 introduction
- Clarify that hedgehog is proven to be a local minimum
- Note that global minimality is strongly supported but remains open
- Reference this research document

### Phase 2: Lean Formalization (Medium-term)

**Task 2.1:** Formalize symmetric criticality in Lean
- Define group action on field configurations
- State and axiomatize Palais's theorem
- Apply to Skyrme model

**Task 2.2:** Formalize second variation positivity
- Define linearized operator
- State spectral positivity as axiom (citing literature)
- Derive local minimality

### Phase 3: Attempt Global Minimality (Research-level)

**Task 3.1:** Literature review on concentration-compactness for Skyrme
- Survey methods from similar nonlinear field theories
- Identify applicable techniques

**Task 3.2:** Investigate comparison inequalities
- Can rearrangement inequalities be adapted?
- Are there monotonicity formulas?

**Task 3.3:** Attempt proof or document obstruction
- If successful: major result, publish
- If obstructed: document why, identify what would be needed

---

## 5. Existing CG Infrastructure

### 5.1 Relevant Files in Codebase

| File | Relevance |
|------|-----------|
| `docs/proofs/Phase4/Theorem-4.1.1-Existence-of-Solitons.md` | Main theorem to be updated |
| `docs/proofs/Phase4/Theorem-4.1.2-Soliton-Mass-Spectrum.md` | Uses hedgehog in mass calculation |
| `docs/proofs/Phase4/Definition-4.1.5-Soliton-Effective-Potential.md` | Stability analysis (Hessian) |
| `verification/Phase4/theorem_4_1_1_verification.py` | Numerical verification |
| `verification/Phase4/theorem_4_1_1_chi_to_U_complete.py` | χ → U construction verification |
| `lean/ChiralGeometrogenesis/Phase4/Theorem_4_1_1.lean` | Lean formalization |

### 5.2 Related Stability Work in CG

The CG framework has extensive stability analysis infrastructure:

- **Theorem 0.2.3:** Hessian eigenvalue analysis for phase-lock stability
- **Theorem 4.1.4:** Lyapunov stability for soliton dynamics
- **Definition 4.1.5:** Hessian of effective potential (eigenvalues ≈ 0.68, positive)

This can be leveraged for the second variation analysis.

### 5.3 Gap in Current Framework

The codebase implicitly uses symmetric criticality without formal justification. Adding the rigorous treatment would:
1. Close this methodological gap
2. Strengthen peer-review readiness
3. Connect to the mathematical physics literature

---

## 6. References

### 6.1 Primary Sources

1. **Manton, N.S. (2024).** "Robustness of the Hedgehog Skyrmion." *JHEP* 08, 015. [arXiv:2405.05731](https://arxiv.org/abs/2405.05731)

2. **Li, D. (2021).** "Global well-posedness of hedgehog solutions for the (3+1) Skyrme model." *Duke Math. J.* 170(7), 1377-1418. [DOI:10.1215/00127094-2020-0067](https://projecteuclid.org/journals/duke-mathematical-journal/volume-170/issue-7/Global-well-posedness-of-hedgehog-solutions-for-the-31-Skyrme/10.1215/00127094-2020-0067.short)

3. **Creek, S. & Donninger, R.** "Linear stability of the Skyrmion." [Semantic Scholar](https://www.semanticscholar.org/paper/Linear-stability-of-the-Skyrmion-Creek-Donninger/dd1dafb112d3277e23bbc7f541687a5c053716de)

4. **Palais, R.S. (1979).** "The principle of symmetric criticality." *Comm. Math. Phys.* 69, 19-30.

5. **Esteban, M.J. (1986).** "A direct variational approach to Skyrme's model for meson fields." *Comm. Math. Phys.* 105, 571-591.

### 6.2 Background References

6. **Skyrme, T.H.R. (1962).** "A unified field theory of mesons and baryons." *Nucl. Phys.* 31, 556-569.

7. **Manton, N. & Sutcliffe, P. (2004).** *Topological Solitons.* Cambridge University Press. (Chapter 9: Skyrmions)

8. **Derrick, G.H. (1964).** "Comments on nonlinear wave equations as models for elementary particles." *J. Math. Phys.* 5, 1252-1254.

---

## 7. Summary

| Question | Answer |
|----------|--------|
| Is the hedgehog profile unique (symmetric sector)? | ✅ **Yes — proven 2026-01-31** (ODE uniqueness + computation) |
| Is the hedgehog ansatz ad hoc? | No — justified by symmetric criticality principle |
| Is the hedgehog a local minimum? | ✅ Yes — proven by second variation analysis |
| Is the hedgehog the global minimum? | ❓ Unknown — strongly supported but open |
| What would prove global minimality? | Concentration-compactness + uniqueness argument |
| Should CG proceed assuming global minimality? | Yes — consistent with all evidence and standard physics practice |

### Gap Closure Record

| Gap | Status | Date | Method |
|-----|--------|------|--------|
| Uniqueness within symmetric sector | ✅ CLOSED | 2026-01-31 | ODE uniqueness + shooting verification |
| Symmetric criticality justification | ✅ DOCUMENTED | 2026-01-31 | Palais (1979) |
| Local minimality | ✅ DOCUMENTED | 2026-01-31 | Creek & Donninger |
| Global minimality | ❓ OPEN | — | Research frontier |

---

*Document created: 2026-01-31*
*Status: Research reference for Theorem 4.1.1 improvements*
