# Adversarial Mathematical Verification Report
# Proposition 0.0.XXe: Continuum Limit of Self-Replicating Fields on dS

> **⚠️ CORRECTION NOTE (2026-03-13):** The "47% discrepancy" between PDE prediction (0.810) and discrete soup (~55%) discussed in this report was caused by a BFS Voronoi tiling bug, not a PDE failure. Corrected runs show ~87% equilibrium density, reducing the PDE discrepancy to ~8% (within mean-field accuracy). See WORKPLAN Q13 and `stella_lang/RERUN_PLAN.md`.

**Date:** 2026-03-10
**Reviewer:** Independent adversarial verification agent
**File reviewed:** `docs/proofs/foundations/Proposition-0.0.XXe-Continuum-Self-Replicating-Fields.md`
**Supporting files reviewed:**
- `docs/proofs/supporting/Proposition-0.0.XXe-Phase3-Reaction-Diffusion-Formulation.md`
- `docs/proofs/supporting/Proposition-0.0.XXe-Phase4-Continuum-Fixed-Point-Identification.md`
- `docs/proofs/supporting/Proposition-0.0.XXe-Phase5-Soliton-Classification.md`

---

## VERDICT

- **VERIFIED:** Partial
- **CONFIDENCE:** Medium
- **Justification:** The core algebraic results (steady-state, stability, uniqueness) are correct. The Fisher-KPP framework is appropriately applied. However, there are several errors of varying severity, gaps in rigor, and one internal inconsistency in the Skyrme mass formula between the main proof and supporting files. The Z3 to SU(3) bridge remains the weakest link, acknowledged as such by the authors.

---

## 1. LOGICAL VALIDITY

### 1.1 Dependency chain — No circularity detected

The logical structure is:

```
Prop 0.0.XXd (discrete soup)
  → Claim 1 (2D universality, empirical)
  → Claim 2 (coarse-graining → Fisher-KPP)
  → Claim 3 (fixed point analysis of Fisher-KPP)
  → Claim 4 (structural analogy: error catastrophe ↔ deconfinement)
  → Claim 5 (topological classification from pi_3(SU(3)))
```

No circular dependencies. Claim 3 depends only on Claim 2 and standard PDE theory. Claim 5 uses Thm 0.0.3 (Stella Uniqueness) for SU(3), which is independent of the soup construction.

### 1.2 Hidden assumptions

**H1 (Moderate concern).** The coarse-graining procedure (section 3.1) assumes that the binary replicator/food classification captures the essential dynamics. The 47% discrepancy between PDE prediction (0.810) and discrete soup observation (~55%) demonstrates this assumption is only partially valid. The proof acknowledges this but does not quantify when the two-component model is a reliable approximation.

**H2 (Minor concern).** The claim that "the VM executes on a linearized 1D tape regardless of the underlying geometry" (section 2.4) assumes that BFS ordering does not affect computational outcomes. While plausible for the specific VM, this is not proven.

**H3 (Moderate concern).** The bilayer coupling term assumes a constant 50% cross-tetrahedron interaction probability. If this probability depends on position (e.g., being higher near regions where the two tetrahedra are geometrically closer), the uniform coupling model is an approximation that could affect front dynamics.

### 1.3 Quantifier usage

No issues found. The universality claim (Claim 1) uses appropriate empirical language ("emerge," "requiring only sufficient population"), not universal quantifiers.

---

## 2. ALGEBRAIC CORRECTNESS

### 2.1 Steady-state formula — VERIFIED

Starting from:
$$f(\rho) = k_\text{eff}\rho(1-\rho) - \mu_\text{eff}\rho - \gamma\rho^2 = 0$$

Expanding: $k_\text{eff}\rho - k_\text{eff}\rho^2 - \mu_\text{eff}\rho - \gamma\rho^2 = 0$

Factor out $\rho$ (nontrivial solution): $k_\text{eff} - k_\text{eff}\rho - \mu_\text{eff} - \gamma\rho = 0$

Solve: $\rho^* = \frac{k_\text{eff} - \mu_\text{eff}}{k_\text{eff} + \gamma}$

With $k_\text{eff} = 0.22$, $\mu_\text{eff} = 20 \times 0.001 = 0.02$, $\gamma = 0.027$:
$$\rho^* = \frac{0.22 - 0.02}{0.22 + 0.027} = \frac{0.20}{0.247} = 0.8097...$$

Text claims 0.810. **VERIFIED.**

### 2.2 Critical mutation rate — VERIFIED

$\rho^* = 0$ when $k_\text{eff} = \mu_\text{eff} = 20\mu_c$:
$$\mu_c = k_\text{eff}/20 = 0.22/20 = 0.011$$

**VERIFIED.**

### 2.3 Linearization f'(rho*) — VERIFIED

$f'(\rho) = k_\text{eff} - 2k_\text{eff}\rho - \mu_\text{eff} - 2\gamma\rho = (k_\text{eff} - \mu_\text{eff}) - 2(k_\text{eff} + \gamma)\rho$

At $\rho = \rho^* = (k_\text{eff} - \mu_\text{eff})/(k_\text{eff} + \gamma)$:

$f'(\rho^*) = (k_\text{eff} - \mu_\text{eff}) - 2(k_\text{eff} + \gamma) \cdot \frac{k_\text{eff} - \mu_\text{eff}}{k_\text{eff} + \gamma} = (k_\text{eff} - \mu_\text{eff}) - 2(k_\text{eff} - \mu_\text{eff}) = -(k_\text{eff} - \mu_\text{eff})$

Text claims $f'(\rho^*) = -(k_\text{eff} - \mu_\text{eff})$. **VERIFIED.**

### 2.4 Stability eigenvalues — VERIFIED

$\sigma_n = -D\lambda_n + f'(\rho^*) = -D\lambda_n - (k_\text{eff} - \mu_\text{eff})$

Since $D > 0$, $\lambda_n \geq 0$, and $k_\text{eff} - \mu_\text{eff} > 0$ (for $\mu < \mu_c$), all $\sigma_n < 0$. **VERIFIED.**

### 2.5 Skyrme mass formula — ERROR / INCONSISTENCY

The main proof (section 6.3) states:
$$M_\text{skyrmion} = \frac{73 f_\pi}{e} \approx \frac{73 \times 88}{5.45} \approx 1180 \text{ MeV}$$

Checking: $73 \times 88 / 5.45 = 6424/5.45 = 1178.7$ MeV. Arithmetic is correct.

**However**, the supporting Phase 5 file (section 5.3.2) uses the formula:
$$M_\text{skyrmion} = \frac{6\pi^2 f_\pi}{e}|Q| \cdot F(m_\pi/f_\pi e)$$

and says this gives $\sim$1170 MeV for QCD (CG). Now $6\pi^2 = 59.22$, not 73.

The resolution (found in Thm 4.3.2 and Def 4.3.1) is that:
- $6\pi^2 f_\pi/e \approx 59.22$ is the **Faddeev-Bogomolny topological lower bound**
- $72.92 f_\pi/e \approx 73 f_\pi/e$ is the **Adkins-Nappi-Witten numerical result** for the B=1 hedgehog

**The inconsistency:** The Phase 5 supporting file uses $6\pi^2 f_\pi/e$ while claiming $M \sim 1170$ MeV. Let's check: $6\pi^2 \times 88 / 5.45 = 59.22 \times 88 / 5.45 = 5211/5.45 = 956$ MeV. This is NOT 1170 MeV; it is much closer to the nucleon mass directly (without quantum corrections).

With the ANW coefficient: $72.92 \times 88/5.45 = 1178$ MeV (classical), then $\times 0.8$ quantum correction $\approx 943$ MeV. This is the consistent chain used in the main proof.

With $6\pi^2$: $59.22 \times 88/5.45 = 956$ MeV (already near nucleon mass without quantum correction).

**The Phase 5 supporting file table at line 232 says "QCD (CG), f_pi=88, e=5.45, M_classical ~1170 MeV" which is only consistent with the coefficient 73 (ANW), NOT with $6\pi^2$ (Faddeev bound) that it writes in the formula at line 225.** This is an internal inconsistency within the Phase 5 supporting document.

**Main proof (section 6.3): Correct** — uses 73 consistently with the numerical value.

### 2.6 Bilayer coupling at steady state — VERIFIED

At steady state with $\rho_+ = \rho_-$, the coupling term $\frac{\kappa}{2}(\rho_\mp - \rho_\pm) = 0$. This is trivially correct and does not affect the uniform fixed-point calculation. **VERIFIED.**

### 2.7 Triangulation formula — VERIFIED

For a tetrahedron with $n_\text{sub}$ subdivisions per edge, the total vertex count is:
- 4 corner vertices
- $6(n_\text{sub} - 1)$ edge-interior vertices (6 edges)
- $4 \times \frac{(n_\text{sub}-1)(n_\text{sub}-2)}{2}$ face-interior vertices (4 faces)

Total: $4 + 6(n-1) + 2(n-1)(n-2) = 4 + 6n - 6 + 2n^2 - 6n + 4 = 2n^2 + 2$

For $n_\text{sub} = 16$: $2(256) + 2 = 514$ per tetrahedron, $1028$ total. **VERIFIED.**

### 2.8 Front speed formula — WARNING

The main proof (section 3.4, table) states:
$$v_\text{KPP} = 2\sqrt{Dk_\text{eff}} = 0.089$$

The standard Fisher-KPP front speed is $2\sqrt{D \cdot f'(0)}$ where $f'(0) = k_\text{eff} - \mu_\text{eff}$.

Using $D = 0.01$, $k_\text{eff} = 0.22$:
- $2\sqrt{0.01 \times 0.22} = 2\sqrt{0.0022} = 2 \times 0.0469 = 0.0939$

Using the correct $f'(0) = k_\text{eff} - \mu_\text{eff} = 0.20$:
- $2\sqrt{0.01 \times 0.20} = 2\sqrt{0.002} = 2 \times 0.0447 = 0.0894$

The numerical value 0.089 matches $f'(0) = 0.20$, not $k_\text{eff} = 0.22$. So the formula in the table is **written incorrectly** as $2\sqrt{Dk_\text{eff}}$ but the **numerical value is computed correctly** using $f'(0) = k_\text{eff} - \mu_\text{eff}$.

**ERROR (minor): The formula should read $2\sqrt{D(k_\text{eff} - \mu_\text{eff})}$, not $2\sqrt{Dk_\text{eff}}$.** The numerical value 0.089 is approximately correct (exact: 0.0894).

### 2.9 Parameter extraction consistency — VERIFIED with caveat

From $\mu_c = 0.011$: $k_\text{eff} = 20 \times 0.011 = 0.22$. **Correct.**

From $\rho^*(\mu=0) = 0.89$: $\gamma = k_\text{eff}(1-0.89)/0.89 = 0.22 \times 0.1236 = 0.0272$. Text says 0.027. **Correct** (rounding).

---

## 3. CONVERGENCE AND WELL-DEFINEDNESS

### 3.1 Fisher-KPP on compact manifold — CORRECTLY INVOKED

The Fisher-KPP equation is well-posed on compact Riemannian manifolds by standard semilinear parabolic PDE theory. The Phase 4 supporting file correctly cites Rothe (1984) and Lunardi (1995). The reaction term $f(\rho) = k_\text{eff}\rho(1-\rho) - \mu_\text{eff}\rho - \gamma\rho^2$ is locally Lipschitz and satisfies $f(0) = 0$ and $f(\rho) < 0$ for $\rho$ sufficiently large. Maximum principle guarantees $\rho \in [0,1]$.

**No issues found.**

### 3.2 Coarse-graining procedure — ADEQUATELY DEFINED but not rigorous

The coarse-graining (section 3.1) defines $\rho$ as an average over a mesoscopic patch of ~k tiles. This is standard in the physics literature but lacks mathematical rigor: the choice of k, the shape of the averaging kernel, and the error bounds on the continuum approximation are not specified. The Wardetzky et al. (2007) reference for discrete Laplacian convergence is appropriate.

**This is a gap but not an error.** The coarse-graining is physics-standard, not mathematically rigorous.

### 3.3 Hair trigger theorem on S^2 — WARNING

The Aronson-Weinberger (1978) hair trigger theorem was originally proven for $\mathbb{R}^n$, not compact manifolds. The proof correctly notes the compact manifold extension but attributes it to Aronson & Weinberger themselves, while the Phase 4 supporting file more accurately cites "Berestycki & Rossi 2008" for the compact manifold extension.

**On compact manifolds, the result is actually stronger**: since there is no "escape to infinity," any nonzero initial condition converges to the nontrivial steady state. This is correct, but the main proof should cite the compact manifold extension explicitly (Berestycki & Rossi 2008 or similar) rather than attributing it to the original 1978 paper.

### 3.4 Laplace-Beltrami eigenvalues on tetrahedral surface vs S^2 — ERROR (Moderate)

Section 4.3 states: "Laplace-Beltrami on $S^2$: $\lambda_n = n(n+1)/R^2$."

**This is the eigenvalue spectrum for a smooth round sphere $S^2$.** But $\partial T_\pm$ is a tetrahedron surface — a piecewise flat surface with cone-point singularities at the 4 vertices (deficit angle at each vertex). The Laplace-Beltrami spectrum on a flat tetrahedron is NOT $n(n+1)/R^2$.

However, **the stability conclusion is unaffected**: the key property used is that all eigenvalues $\lambda_n \geq 0$ with $\lambda_0 = 0$ (the zero mode is the spatially uniform mode). This is true for any compact Riemannian manifold (or piecewise flat surface). The specific formula $\lambda_n = n(n+1)/R^2$ is used only to label modes; the proof only needs $\lambda_n \geq 0$, which is guaranteed by the non-negative definiteness of $-\nabla^2$ on any compact manifold.

**Verdict:** The formula for eigenvalues is wrong for the tetrahedral surface, but the conclusion ($\sigma_n < 0$ for all $n$) is correct because it only requires $\lambda_n \geq 0$, which holds on any compact manifold.

---

## 4. DIMENSIONAL ANALYSIS

### 4.1 Fisher-KPP equation — VERIFIED

$$\frac{\partial \rho}{\partial t} = D\nabla^2\rho + k_\text{eff}\rho(1-\rho) - \mu_\text{eff}\rho - \gamma\rho^2$$

- $[\rho] = $ dimensionless (fraction)
- $[\partial\rho/\partial t] = 1/\text{time}$
- $[D\nabla^2\rho] = (\text{length}^2/\text{time})(1/\text{length}^2) = 1/\text{time}$. **Consistent.**
- $[k_\text{eff}\rho(1-\rho)] = (1/\text{time})$. Requires $[k_\text{eff}] = 1/\text{time}$. **Consistent** (rate per epoch).
- $[\mu_\text{eff}\rho] = 1/\text{time}$. **Consistent.**
- $[\gamma\rho^2] = 1/\text{time}$. **Consistent.**

### 4.2 Diffusion coefficient — WARNING

The main proof (section 3.3) states $D = a^2/(6\Delta t)$. The factor 6 corresponds to a **3D** random walk ($D = a^2/(2d\Delta t)$ with $d=3$).

However, diffusion on $\partial\mathcal{S}$ is a **2D** process. For a 2D triangular lattice, $D = a^2/(2 \times 2 \times \Delta t) = a^2/(4\Delta t)$ or, accounting for the coordination number, $D = a^2/(6\Delta t)$ if the effective dimensionality of the random walk is 3 due to the coordination number 6 on a triangular mesh.

The Phase 3 supporting file (section 3.2.4) gives $D = a^2/(2d\Delta t) \times k_\text{rep}$ with $d=2$, yielding $D = a^2 k_\text{rep}/(4\Delta t)$. This is inconsistent with the main proof's $D = a^2/(6\Delta t)$.

**The exact value of $D$ is not critical for the fixed-point analysis** (it affects front speed and spatial pattern formation, not the uniform steady state), but the inconsistency between the main proof and supporting file should be resolved.

### 4.3 Skyrme mass dimensions — VERIFIED

$[73 f_\pi/e] = [f_\pi] = \text{MeV}$ since $e$ is dimensionless (Skyrme parameter). With $f_\pi = 88$ MeV: $73 \times 88/5.45 = 1179$ MeV. **Consistent.**

---

## 5. PROOF COMPLETENESS

### 5.1 Uniqueness argument (section 4.2) — ADEQUATE

The KPP conditions are verified:
1. $f(0) = 0$ and $f(\rho^*) = 0$ — trivially true by construction
2. $f(\rho) > 0$ for $\rho \in (0, \rho^*)$ — requires checking

Let me verify condition 2: $f(\rho) = \rho[(k_\text{eff} - \mu_\text{eff}) - (k_\text{eff} + \gamma)\rho]$. For $0 < \rho < \rho^* = (k_\text{eff} - \mu_\text{eff})/(k_\text{eff} + \gamma)$, the bracket is positive. So $f(\rho) > 0$. **VERIFIED.**

The additional KPP condition $f(\rho)/\rho \leq f'(0) = k_\text{eff} - \mu_\text{eff}$ for all $\rho \in (0, \rho^*)$: $f(\rho)/\rho = (k_\text{eff} - \mu_\text{eff}) - (k_\text{eff} + \gamma)\rho \leq k_\text{eff} - \mu_\text{eff}$. True since $(k_\text{eff} + \gamma)\rho \geq 0$. **VERIFIED.**

### 5.2 Stability analysis (section 4.3) — VERIFIED with caveat

As noted in section 3.4 above, the eigenvalue formula is wrong for the tetrahedral surface, but the conclusion is correct. All eigenvalues $\sigma_n < 0$, confirming asymptotic stability.

**Missing:** The stability analysis considers only the decoupled single-tetrahedron modes. The bilayer coupling introduces cross-terms. For the symmetric mode ($\rho_+ = \rho_-$), the coupling vanishes and the analysis is correct. For the antisymmetric mode ($\delta\rho_+ = -\delta\rho_-$), the coupling adds $-\kappa$ to the growth rate, making it more negative. So stability is preserved. This should be stated explicitly.

### 5.3 Bootstrap identification (section 4.5) — NOT A PROOF

The "structural isomorphism" between:
- $R(S) = S$ (discrete replicator fixed point)
- $\mathcal{F}[\rho^*] = 0$ (PDE steady state)
- $\Phi(T) = T$ (bootstrap self-consistency)

is presented as a table of analogies, not a mathematical proof. The first two are rigorous: the discrete replicator IS a fixed point, and $\rho^*$ IS the PDE steady state, and the coarse-graining connects them. The third ($\Phi(T) = T$) is an assertion that the bootstrap operator in theory space has the same structure, which is not derived here — it appeals to Thm 0.0.31.

**This is acknowledged in section 8.2 as a "structural result" with a specific gap. The proof is honest about the status.**

### 5.4 Section 7 (Z3 to SU(3) bridge) — COLLECTION OF ARGUMENTS, NOT A PROOF

The five justifications (Svetitsky-Yaffe, center-to-group, Doi-Peliti, Parisi-Wu, geometric constraint) are each individually plausible but none constitutes a constructive proof of the Z3 to SU(3) promotion. The Doi-Peliti verification confirms the algebraic isomorphism between the master equation and a quantum Hamiltonian, but the non-Hermiticity of that Hamiltonian (acknowledged at line 358) means it is NOT immediately a physical quantum mechanical system.

**The proof is honest about this being the main gap (section 8.2).** The five arguments provide a strong plausibility case but fall short of a mathematical proof.

---

## 6. SPECIFIC CONCERNS INVESTIGATED

### 6.1 PDE overprediction (0.810 vs ~55%) — PARTIALLY EXPLAINED

The proof attributes the discrepancy to "quasispecies diversity (multiple competing replicator families)." The Phase 3 supporting file provides more detail: the binary replicator/food classification misses the fitness distribution within the quasispecies cloud.

**My assessment:** The explanation is plausible but not quantitative. The factor of ~1.5x overprediction is large. The Phase 3 file notes that a density-dependent $k_\text{eff}(\rho)$ would give a better fit, but this is not pursued. This is a genuine weakness of the two-component model.

**Note:** The parameter extraction uses the SEEDED data ($\rho^* \approx 0.89$ at $\mu=0$) and the error threshold ($\mu_c = 0.011$) to fix $k_\text{eff}$ and $\gamma$. The resulting prediction at $\mu=0.001$ gives 0.810, not 0.55. The 0.55 value comes from the SPONTANEOUS emergence experiments, which have additional effects (diverse food population, quasispecies competition). So the model is consistent with the seeded data but not the spontaneous data. The proof should be clearer about which experimental condition it matches.

### 6.2 Front speed at 51% of flat-space prediction — ADEQUATELY EXPLAINED

Three effects reduce the front speed on the compact bilayer surface:
1. Bilayer coupling diverts density to the unseeded tetrahedron
2. Curvature modifies the Laplacian
3. Compact geometry means the front interacts with itself

On a compact surface, the concept of asymptotic front speed is not well-defined (the front wraps around). The 51% figure is from a transient measurement. **This is not an error.**

### 6.3 Constant mu_c across program lengths — PARTIALLY JUSTIFIED

The proof claims $\mu_c$ is constant across program lengths, contradicting Eigen scaling ($\mu_c \propto 1/L$). The argument is that the VM's "computational fidelity" sets the threshold, not genome length.

**My assessment:** This is an empirical finding from Phase 2, not a theoretical derivation. The Eigen scaling assumes that every position in the genome contributes independently to fitness, while the VM's self-replicating programs may have a fixed-size "functional core" whose length determines the effective $\mu_c$ regardless of total program length. If the core length $L_\text{core} \approx 20$ is constant, then $\mu_c = k_\text{eff}/(20) = 0.011$ is constant, which is consistent. But this means $\mu_\text{eff} = L_\text{core} \cdot \mu$ with constant $L_\text{core}$, which IS a form of Eigen scaling (with effective length = core length). The claim that it "violates Eigen scaling" is misleading — it actually confirms Eigen scaling with $L = L_\text{core}$.

### 6.4 Laplace-Beltrami eigenvalues on tetrahedral surface vs S^2 — ERROR (see 3.4)

As detailed above: the formula $\lambda_n = n(n+1)/R^2$ is for the round $S^2$, not the tetrahedral surface. The stability conclusion is unaffected.

---

## 7. RE-DERIVED EQUATIONS

| Equation | Location | Status |
|----------|----------|--------|
| $\rho^* = (k_\text{eff} - \mu_\text{eff})/(k_\text{eff} + \gamma)$ | §4.1 | **VERIFIED** |
| $\mu_c = k_\text{eff}/20 = 0.011$ | §4.1, §5.1 | **VERIFIED** |
| $f'(\rho^*) = -(k_\text{eff} - \mu_\text{eff})$ | §4.3 | **VERIFIED** |
| $\sigma_n = -D\lambda_n + f'(\rho^*) < 0$ for all $n$ | §4.3 | **VERIFIED** (conclusion correct; eigenvalue formula applies to S^2 not tetrahedron) |
| $M = 73 f_\pi/e \approx 1179$ MeV | §6.3 | **VERIFIED** (arithmetic correct; 73 = ANW coefficient) |
| KPP conditions ($f(0) = 0$, $f > 0$ on $(0,\rho^*)$, $f/\rho \leq f'(0)$) | §4.2 | **VERIFIED** |
| $2n_\text{sub}^2 + 2$ vertices per tetrahedron | §2.1 | **VERIFIED** |
| $v_\text{KPP} = 2\sqrt{D \cdot f'(0)}$ | §3.4 | **VERIFIED** (but formula written incorrectly in text as $2\sqrt{Dk_\text{eff}}$) |

---

## 8. ADDITIONAL DEEP-DIVE FINDINGS

### 8.1 mu_c inconsistency across Phase 2 supporting file — ERROR (Moderate)

The Phase 2 supporting file (`Proposition-0.0.XXe-Phase2-Z3-Potts-Model-Connection.md`) contains an internal inconsistency in the reported value of $\mu_c$:

- **Lines 46, 111, 393:** Report $\mu_c \approx 0.004$
- **Lines 137-145:** The actual Eigen scaling test data shows $\mu_c \approx 0.011$ (using 10% density threshold), constant across program lengths L = 24-48
- **Main proof:** Correctly uses $\mu_c \approx 0.011$

The value 0.004 appears in the early summary dictionary tables and seems to be a different (unstated) threshold definition -- perhaps where density first drops below 50%. But this is never explained; the same symbol $\mu_c$ is used for both values. The Eigen scaling test at lines 137-145 definitively shows $\mu_c \approx 0.011$ for the 10% threshold (complete loss of replicators), which is the value used in the main proof.

Furthermore, the fine sweep data (lines 120-129) shows density = 18.9% at $\mu = 0.010$ and 0% at $\mu = 0.012$, confirming $\mu_c \in (0.010, 0.012)$ for complete extinction, consistent with 0.011.

**Impact:** The main proof uses the correct value. The Phase 2 supporting file needs correction to use $\mu_c \approx 0.011$ consistently, or to explicitly define two different thresholds.

### 8.2 Bilayer coupling form inconsistency — WARNING (Moderate)

Three different bilayer coupling forms appear across documents:

**(a) Main proof (Claim 2, §3.2):**
$$\frac{\partial \rho_+}{\partial t} = D\nabla^2\rho_+ + k_\text{eff}\rho_+(1-\rho_+) - \mu_\text{eff}\rho_+ - \gamma\rho_+^2 + \frac{\kappa}{2}(\rho_- - \rho_+)$$

**(b) Phase 3 supporting file (§3.2.5):**
$$\frac{\partial \rho_+}{\partial t} = D\nabla^2\rho_+ + k_\text{rep}\left[\frac{1}{2}\rho_+(1-\rho_+) + \frac{1}{2}\bar{\rho}_-(1-\rho_+)\right] - \mu_\text{eff}\rho_+$$

**(c) Phase 4 supporting file (§4.2.6):**
$$\frac{\partial \rho_+}{\partial t} = D\nabla^2\rho_+ + \frac{k_\text{eff}}{2}\left[\rho_+(1-\rho_+) + \bar{\rho}_-(1-\rho_+)\right] - \mu_\text{eff}\rho_+ - \gamma\rho_+^2$$

Forms (b) and (c) derive the bilayer coupling from the 50% interaction probability directly within the growth term. Form (a) separates it into an additive linear coupling $\frac{\kappa}{2}(\rho_- - \rho_+)$.

**Are these equivalent?** At the spatially uniform fixed point $\rho_+ = \rho_- = \rho$, all three reduce to the same single-surface equation. However, away from uniformity they differ:

Expanding form (c): $\frac{k_\text{eff}}{2}[\rho_+(1-\rho_+) + \bar{\rho}_-(1-\rho_+)] = \frac{k_\text{eff}}{2}(\rho_+ + \bar{\rho}_-)(1-\rho_+)$

This is NOT equivalent to form (a): $k_\text{eff}\rho_+(1-\rho_+) + \frac{\kappa}{2}(\rho_- - \rho_+) = k_\text{eff}\rho_+(1-\rho_+) + \frac{\kappa}{2}\rho_- - \frac{\kappa}{2}\rho_+$

Form (a) linearizes the coupling, while forms (b)/(c) keep it nonlinear. The discrepancy matters for:
- Front propagation dynamics between $T_+$ and $T_-$ (transient behavior)
- Stability of asymmetric states where $\rho_+ \neq \rho_-$
- The antisymmetric perturbation mode

Form (b)/(c) is the physically correct derivation from the 50% interaction rule. Form (a) is a convenient simplification that happens to give the same fixed point. **The main proof should either use form (c) or note that the additive coupling is a linearized approximation valid near the symmetric fixed point.**

### 8.3 Uniqueness argument — subtle issue with non-uniform steady states

The Phase 4 supporting file (§4.4.1, lines 374-384) reveals a subtlety that the main proof glosses over. The condition for the uniform $\rho^*$ to be the unique positive steady state is $r < \lambda_1 D$ (Cantrell & Cosner 2003). But the Phase 4 file computes $\lambda_1 D \approx 0.08 < r = 0.20$, meaning this condition is NOT satisfied.

This means non-uniform steady states **may exist in principle**. The Phase 4 file resolves this by appealing to the global attractivity theorem (hair trigger effect), arguing that even if non-uniform steady states exist as mathematical solutions, they are unstable and the dynamics converge to the uniform state. The Phase 3 PDE simulation confirms this numerically.

The main proof (§4.2) does not mention this subtlety -- it simply cites Aronson & Weinberger for uniqueness on compact manifolds. This is adequate for the conclusion but slightly misleading about the mathematical structure. The argument requires two steps: (1) existence of $\rho^*$ (algebraic), (2) global attractivity despite possible non-uniform solutions (dynamical, via hair trigger). The main proof conflates these.

### 8.4 Z3 dynamical symmetry breaking — significant finding from Doi-Peliti

The Phase 4 supporting file (§4.2.5e, finding 2) reveals that the Z3 symmetry is **dynamically broken** in the soup: $\|[T, R]\|_F \neq 0$ because the OPEN/CLOSE instructions test `tape[h0] == 0`, treating trit 0 as distinguished. This means:

1. The soup does NOT have exact Z3 symmetry at the microscopic level
2. The Z3 symmetry claimed in the Potts mapping (Phase 2) is approximate
3. The Svetitsky-Yaffe argument requires the center symmetry to be exact

The Phase 4 file interprets this as "spontaneous symmetry breaking" analogous to a vacuum selecting a preferred color direction. However, this is actually **explicit** symmetry breaking (built into the VM instruction set), not spontaneous. Spontaneous breaking would mean the Hamiltonian has Z3 symmetry but the ground state does not; here the Hamiltonian itself lacks Z3 symmetry.

**Impact on the proof:** The Svetitsky-Yaffe mapping (§5.2, §7.1) assumes Z3 center symmetry. If this symmetry is explicitly broken by the VM, the mapping is approximate rather than exact. The proof should acknowledge this and argue that the breaking is "small" (the NESS $L_1$ distance from its Z3-rotated version is ~1.0-2.0, which is significant on the scale of probability distributions). Alternatively, the proof could argue that the explicit breaking becomes negligible in the continuum limit.

### 8.5 Doi-Peliti verification — VERIFIED

The Doi-Peliti numerical verification (Phase 4, §4.2.5e) is clean:
- $\|H_\text{DP} \cdot P^*\|_2 < 10^{-15}$ in all 4 tests (machine precision)
- Monte Carlo validation independently confirms the exact NESS
- Spectral gap scales sensibly with mutation rate
- NESS concentrates on configurations with inter-tetrahedron coupling instructions

The algebraic isomorphism between the master equation and the quantum Hamiltonian is correctly applied. **No issues found with the Doi-Peliti construction itself.**

### 8.6 Phase 3 PDE vs discrete data comparison — clarifying the discrepancy

There are TWO distinct density comparisons in the proof ecosystem:

**(a) PDE prediction vs spontaneous emergence (main proof §3.4 table):**
$\rho^*_\text{PDE} = 0.810$ vs $\rho^*_\text{spontaneous} \approx 0.55$ at $\mu = 0.001$.
Discrepancy: 47%. Attributed to quasispecies diversity.

**(b) PDE prediction vs seeded mutation sweep (Phase 3, §3.4.3):**
At $\mu = 0.002$: PDE predicts 0.729 vs observed 0.802 (underpredicts by 7.3%)
At $\mu = 0.004$: PDE predicts 0.567 vs observed 0.644 (underpredicts by 7.7%)
At $\mu = 0.010$: PDE predicts 0.081 vs observed 0.189 (underpredicts by 10.8%)

The PDE systematically **underpredicts** the seeded data while it **overpredicts** the spontaneous data. The parameter extraction uses the endpoints ($\mu = 0$: 89%, $\mu_c = 0.011$: 0%) so those match exactly.

The main proof presents only comparison (a) and says the PDE "overpredicts." This creates a misleading impression that the PDE is uniformly too high. A more accurate statement: the PDE correctly models the seeded/fully-mixed regime (within ~10%) but overpredicts the spontaneous emergence regime (by ~47%). The difference reflects quasispecies diversity effects that are absent in the two-component model.

### 8.7 Svetitsky-Yaffe: first-order transition consistency check

The Phase 2 analysis (§2.2.4) correctly identifies that the Z3 Potts model in 2D has a **first-order** phase transition (q = 3 > 2 on the triangular lattice). The computational data shows the soup transition is "smooth but steep" — consistent with either a weakly first-order transition or a crossover in a finite system.

The main proof (§5.2) states "The Z3 Potts transition in 2D is first-order (q >= 3), consistent with SU(3) deconfinement being first-order." This is correct: SU(3) deconfinement is indeed first-order, matching the Z3 Potts prediction. This is a nontrivial structural consistency check.

However, the Phase 2 file also notes (§2.3.1) that the Z3 Potts transition is "weakly first-order" and the parafermion CFT sits at the boundary between first-order and continuous behavior. Combined with the non-equilibrium nature of the soup (which may push it into the directed percolation universality class), the order of the transition is not definitively established from the computational data. The proof is appropriately cautious about this in §5.3.

---

## ERRORS FOUND

| # | Severity | Location | Description |
|---|----------|----------|-------------|
| E1 | **Minor** | Main proof §3.4 table | Front speed formula written as $2\sqrt{Dk_\text{eff}}$ but should be $2\sqrt{D(k_\text{eff} - \mu_\text{eff})}$. The numerical value 0.089 is computed correctly using $f'(0)$. |
| E2 | **Minor** | Main proof §4.3 | Eigenvalue formula $\lambda_n = n(n+1)/R^2$ is for the round $S^2$, not the tetrahedral surface $\partial T_\pm$. Conclusion ($\sigma_n < 0$) is correct regardless. |
| E3 | **Minor** | Main proof §3.3 | $D = a^2/(6\Delta t)$ uses the 3D random walk formula. Inconsistent with Phase 3 supporting file which uses $D = a^2 k_\text{rep}/(4\Delta t)$ for 2D. |
| E4 | **Minor** | Supporting Phase 5, §5.3.2 | Formula uses $6\pi^2 f_\pi/e$ (Faddeev bound = 59.22) but the numerical table gives $M \sim 1170$ MeV which requires the ANW coefficient 72.92 (rounded to 73). Internal inconsistency in supporting file. |
| E5 | **Moderate** | Supporting Phase 2, §§2.1.2, 2.2.2, 2.4.5 | $\mu_c \approx 0.004$ in summary tables contradicts $\mu_c \approx 0.011$ from the Eigen scaling test data in the same file. The main proof correctly uses 0.011. Phase 2 needs correction. |
| E6 | **Moderate** | Main proof §3.2 vs supporting Phase 3 §3.2.5 and Phase 4 §4.2.6 | Bilayer coupling form differs: main proof uses additive linear coupling $\frac{\kappa}{2}(\rho_- - \rho_+)$; supporting files derive nonlinear coupling from 50% interaction probability. These are not equivalent away from the symmetric fixed point. |

## WARNINGS

| # | Severity | Location | Description |
|---|----------|----------|-------------|
| W1 | **Moderate** | Main proof §3.4 | PDE overpredicts density by 47% (0.810 vs 0.55) for spontaneous emergence, but underpredicts by ~7-11% for seeded data. The presentation in §3.4 creates a misleading impression. |
| W2 | **Moderate** | Main proof §4.4 | Hair trigger theorem cited as Aronson & Weinberger 1978, but the compact manifold extension requires additional references (e.g., Berestycki & Rossi 2008). |
| W3 | **Moderate** | Main proof §5.1 | Claim that $\mu_c$ is constant across program lengths "violates Eigen scaling" is misleading. It is consistent with Eigen scaling using $L_\text{core}$ as the effective genome length. |
| W4 | **Moderate** | Phase 4 §4.2.5e + Main proof §7 | Z3 symmetry is explicitly broken by the VM instruction set (OPEN/CLOSE test `tape[h0] == 0`). The Svetitsky-Yaffe mapping requires exact Z3 center symmetry. This weakens the mapping from exact to approximate. |
| W5 | **Moderate** | Main proof §4.2 | Uniqueness argument glosses over the fact that $r > \lambda_1 D$ (non-uniform steady states may exist as mathematical solutions). The conclusion is saved by global attractivity, but the argument should be stated more carefully. |
| W6 | **Low** | Main proof §4.3 | Bilayer coupling stability not explicitly analyzed. The antisymmetric mode adds $-\kappa$ to growth rates, strengthening stability, but this should be shown. |
| W7 | **Low** | Main proof §7 | Z3 to SU(3) bridge relies on five independent plausibility arguments, none constituting a constructive proof. Acknowledged by authors. |
| W8 | **Low** | Main proof §7.3 | Doi-Peliti Hamiltonian is non-Hermitian ($|\text{Im}(\lambda)| \sim 0.59$). Physical interpretation and relation to SU(3) Yang-Mills remains open. |

## SUGGESTIONS

| # | Priority | Description |
|---|----------|-------------|
| S1 | **High** | Fix the front speed formula in §3.4 to $2\sqrt{D(k_\text{eff} - \mu_\text{eff})}$. |
| S2 | **High** | Replace $\lambda_n = n(n+1)/R^2$ in §4.3 with a general statement: "the Laplace-Beltrami eigenvalues $\lambda_n \geq 0$ on the compact surface $\partial T_\pm$, with $\lambda_0 = 0$ for the constant mode." |
| S3 | **High** | Fix $\mu_c$ in Phase 2 supporting file: replace all instances of $\mu_c \approx 0.004$ with $\mu_c \approx 0.011$, or explicitly define two thresholds (50% density threshold vs complete extinction threshold). |
| S4 | **High** | Resolve the bilayer coupling form: either use the physically derived nonlinear form from Phase 3/4 in the main proof, or explicitly state that the additive form is a linearized approximation valid near the symmetric fixed point. |
| S5 | **Medium** | Resolve the diffusion coefficient inconsistency between main proof ($a^2/6\Delta t$) and Phase 3 supporting file ($a^2 k_\text{rep}/4\Delta t$). |
| S6 | **Medium** | Fix the Skyrme mass formula in Phase 5 supporting file to use 72.92 (ANW) consistently, or explicitly note the distinction between Faddeev bound ($6\pi^2$) and ANW numerical coefficient (72.92). |
| S7 | **Medium** | Rephrase the $\mu_c$-constancy claim in §5.1. Instead of "violates Eigen scaling," say "is consistent with Eigen scaling applied to the functional core of length $L_\text{core} \approx 20$, independent of total program length." |
| S8 | **Medium** | Acknowledge the explicit Z3 symmetry breaking by the VM instruction set and argue either (a) the breaking is small/irrelevant in the continuum limit, or (b) the Svetitsky-Yaffe mapping is approximate and quantify the error. |
| S9 | **Medium** | Strengthen the uniqueness argument in §4.2: note that $r > \lambda_1 D$ means the Cantrell-Cosner sufficient condition is not met, but the hair trigger effect (Berestycki-Rossi) still guarantees global convergence to the uniform state. |
| S10 | **Medium** | Add explicit bilayer stability analysis: show that the antisymmetric mode ($\delta\rho_+ = -\delta\rho_-$) has growth rate $\sigma_n^\text{anti} = -D\lambda_n - (k_\text{eff} - \mu_\text{eff}) - \kappa < \sigma_n$. |
| S11 | **Low** | Cite Berestycki & Rossi (2008) or equivalent for the hair trigger effect on compact manifolds, alongside Aronson & Weinberger (1978). |
| S12 | **Low** | In §3.4, distinguish the two density comparisons: PDE vs seeded data (good match, ~7-11% error) and PDE vs spontaneous emergence data (poor match, ~47% error). Explain that the parameter extraction is fitted to the seeded regime. |

---

## SUMMARY

The core mathematical content of Proposition 0.0.XXe is sound. The steady-state formula, stability analysis, uniqueness arguments, and KPP conditions are all algebraically correct and logically valid. The Fisher-KPP framework is appropriately applied to the compact surface $\partial\mathcal{S}$. No errors affect the central conclusions (Claims 1-5).

The errors found fall into two categories:

**Presentational errors in the main proof (E1-E3):** Wrong front speed formula label, S^2 eigenvalue formula on tetrahedral surface, inconsistent diffusion coefficient. These do not affect conclusions but should be fixed for rigor.

**Cross-document inconsistencies (E4-E6):** The Skyrme mass formula discrepancy in Phase 5, the $\mu_c$ value discrepancy in Phase 2, and the bilayer coupling form discrepancy between the main proof and supporting files. These represent a fragmentation problem -- exactly the type of error the project's CLAUDE.md warns about. The main proof's conclusions survive because the inconsistencies cancel at the uniform fixed point, but they indicate insufficient cross-referencing between documents.

The most significant conceptual finding is **W4: the explicit Z3 symmetry breaking** by the VM instruction set, which was not flagged in the main proof. This weakens the Svetitsky-Yaffe mapping that forms one of the five justifications for the Z3-to-SU(3) bridge. While not fatal (the other four arguments remain), it should be acknowledged and addressed.

The proof is commendably honest about its limitations (section 8), clearly distinguishing established results from structural arguments and conjectures. The weakest link remains the Z3-to-SU(3) bridge (section 7), which the authors correctly identify as the main open problem.

**Overall assessment:** The mathematical content that IS proven (Claims 1-3: geometric universality, Fisher-KPP dynamics, vacuum fixed point) is correct and well-supported. The structural arguments (Claims 4-5: error catastrophe mapping, catalytic-topological dichotomy) are physically reasonable but not mathematically rigorous. The cross-document inconsistencies need cleanup but do not undermine the core results.
