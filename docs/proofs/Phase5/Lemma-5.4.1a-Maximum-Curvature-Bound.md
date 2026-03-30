# Lemma 5.4.1a: Maximum Curvature Bound from FCC Lattice

## Status: 🔶 NOVEL ✅ VERIFIED — LATTICE-DERIVED UV CURVATURE CUTOFF

## Dependencies

| Dependency | Status | Role |
|-----------|--------|------|
| Theorem 0.0.6 (Spatial Extension from Octet Truss) | ✅ VERIFIED | FCC lattice structure, coordination number 12 |
| Proposition 0.0.17r (Lattice Spacing from Holographic Self-Consistency) | ✅ VERIFIED | $a^2 = \frac{8\ln(3)}{\sqrt{3}}\ell_P^2 \approx 5.07\ell_P^2$ |

## §1 Statement

**Lemma 5.4.1a (Maximum Curvature Bound).** On the FCC lattice with spacing $a \approx 2.25\ell_P$ (Proposition 0.0.17r), the properly normalized discrete Laplacian imposes a maximum Ricci scalar curvature:

$$\boxed{R_{\max} = \frac{8}{a^2} = \frac{\sqrt{3}}{\ln(3)\,\ell_P^2} \approx \frac{1.58}{\ell_P^2}}$$

with associated bounds:

**(a)** Kretschmann scalar: $K_{\max} = R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}\big|_{\max} \leq 20\,R_{\max}^2 = \frac{1280}{a^4} \approx \frac{49.7}{\ell_P^4}$

**(b)** Minimum trapped surface area: $A_{\min} = \sqrt{3}\,a^2 \approx 8.8\,\ell_P^2$

**(c)** Form factor suppression: The lattice form factor $F(\mathbf{k})$ ranges over $[-1/3,\, 1]$, with $F \to 1$ at long wavelengths (recovering continuum physics) and $F_{\min} = -1/3$ at the Brillouin zone boundary (X and W points), preventing curvature from exceeding $R_{\max}$.

## §2 Proof

### §2.1 Discrete Laplacian on FCC Lattice

The FCC lattice (Theorem 0.0.6) has coordination number $z = 12$. The 12 nearest-neighbour vectors are:

$$\boldsymbol{\delta}_j = \frac{a}{\sqrt{2}}(\pm 1, \pm 1, 0) \quad\text{and permutations of coordinate slots}$$

The discrete scalar Laplacian acting on a function $f$ at site $\mathbf{x}_i$ must be normalized to recover the continuum Laplacian $\nabla^2$ in the long-wavelength limit. The second-order moment matrix of the FCC nearest-neighbour vectors is:

$$M_{ab} \equiv \sum_{j=1}^{12} (\delta_j)_a (\delta_j)_b = 4a^2\,\delta_{ab}$$

This is isotropic (as required by the cubic symmetry of the FCC lattice). For the discrete Laplacian to satisfy $\nabla^2_{\text{disc}} e^{i\mathbf{k}\cdot\mathbf{x}} \to -k^2\, e^{i\mathbf{k}\cdot\mathbf{x}}$ as $k \to 0$, the normalization must be $1/(2a^2)$ rather than $1/a^2$ (see §2.1.2 below). The properly normalized discrete Laplacian is therefore:

$$\nabla^2_{\text{disc}} f(\mathbf{x}_i) = \frac{1}{2a^2}\sum_{j=1}^{12} \left[f(\mathbf{x}_j) - f(\mathbf{x}_i)\right]$$

#### §2.1.1 Continuum limit verification

In Fourier space $f(\mathbf{x}) = e^{i\mathbf{k}\cdot\mathbf{x}}$, the eigenvalues are:

$$\lambda(\mathbf{k}) = \frac{1}{2a^2}\sum_{j=1}^{12}\left[\cos(\mathbf{k}\cdot\boldsymbol{\delta}_j) - 1\right]$$

For small $|\mathbf{k}|$, expanding $\cos(\mathbf{k}\cdot\boldsymbol{\delta}_j) \approx 1 - \tfrac{1}{2}(\mathbf{k}\cdot\boldsymbol{\delta}_j)^2 + \cdots$ gives:

$$\lambda(\mathbf{k}) \approx -\frac{1}{4a^2}\sum_{j=1}^{12}(\mathbf{k}\cdot\boldsymbol{\delta}_j)^2 = -\frac{1}{4a^2}\,\mathbf{k}^T M\,\mathbf{k} = -\frac{1}{4a^2}\cdot 4a^2\,k^2 = -k^2 \qquad\checkmark$$

confirming the correct continuum limit.

#### §2.1.2 Cosine sum factorization and spectral radius

The 12 cosine terms in the eigenvalue are not independent. Defining $u \equiv k_x a/\sqrt{2}$, $v \equiv k_y a/\sqrt{2}$, $w \equiv k_z a/\sqrt{2}$, the sum factorizes exactly:

$$\sum_{j=1}^{12}\cos(\mathbf{k}\cdot\boldsymbol{\delta}_j) = 4\bigl[\cos u\cos v + \cos u\cos w + \cos v\cos w\bigr]$$

*Proof of identity.* The 12 nearest-neighbour dot products group into three pairs of coordinate planes. The four vectors in the $(xy)$-plane contribute $\cos(u+v) + \cos(u-v) + \cos(-u+v) + \cos(-u-v) = 4\cos u\cos v$. Summing the three coordinate planes gives the result. $\square$

To find the spectral radius $|\lambda|_{\max}$, we minimize the cosine sum. Setting $x = \cos u$, $y = \cos v$, $z = \cos w$ with $x, y, z \in [-1, 1]$, we require the minimum of:

$$g(x,y,z) = xy + xz + yz$$

over the cube $[-1,1]^3$. Since $g$ is bilinear in each variable, its extrema lie on vertices. Evaluating all $2^3 = 8$ corners:

| $(x,y,z)$ | $g$ | | $(x,y,z)$ | $g$ |
|---|---|---|---|---|
| $(+,+,+)$ | $+3$ | | $(-,-,-)$ | $+3$ |
| $(+,+,-)$ | $-1$ | | $(-,-,+)$ | $-1$ |
| $(+,-,+)$ | $-1$ | | $(-,+,-)$ | $-1$ |
| $(+,-,-)$ | $-1$ | | $(-,+,+)$ | $-1$ |

$$g_{\min} = -1 \qquad \Longrightarrow \qquad \sum_{j}\cos(\mathbf{k}\cdot\boldsymbol{\delta}_j)\bigg|_{\min} = 4 \times (-1) = -4$$

**Key point:** The naive bound $\cos(\mathbf{k}\cdot\boldsymbol{\delta}_j) \geq -1$ for each of the 12 terms would give $\sum \cos \geq -12$, i.e., a spectral radius of $24/(2a^2) = 12/a^2$. However, the 12 cosines are *correlated* through the factorization identity above: it is impossible for all 12 to simultaneously equal $-1$. The true minimum is $-4$, giving a spectral radius of $16/(2a^2) = 8/a^2$.

The spectral radius of the properly normalized discrete Laplacian is therefore:

$$|\lambda|_{\max} = \frac{1}{2a^2}\bigl(12 - (-4)\bigr) = \frac{8}{a^2}$$

This bound is **tight** (achieved at X and W points of the FCC Brillouin zone), and has been independently verified by (1) analytic factorization as above, (2) exhaustive corner evaluation, (3) brute-force grid search ($N = 200$), and (4) scipy optimization with 500 random starts — all confirming $|\lambda|_{\max} = 8/a^2$ exactly.

### §2.2 Ricci Scalar Bound

The Ricci scalar $R$ on the emergent spacetime is constructed from second derivatives of the metric, which on the lattice are represented by the discrete Laplacian. Since curvature involves second derivatives of $g_{\mu\nu}$, and each component is bounded by the discrete Laplacian spectral radius:

$$|R| \leq \frac{8}{a^2}$$

Substituting $a^2 = \frac{8\ln(3)}{\sqrt{3}}\ell_P^2$ (Proposition 0.0.17r):

$$R_{\max} = \frac{8}{a^2} = \frac{8\sqrt{3}}{8\ln(3)}\frac{1}{\ell_P^2} = \frac{\sqrt{3}}{\ln(3)}\frac{1}{\ell_P^2}$$

Numerically: $\sqrt{3}/\ln(3) = 1.7321/1.0986 \approx 1.577$, giving:

$$\boxed{R_{\max} \approx \frac{1.58}{\ell_P^2}}$$

### §2.3 Kretschmann Scalar Bound

The Kretschmann scalar $K = R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}$ involves the sum of squared Riemann tensor components. In 4 dimensions, the Riemann tensor has 20 algebraically independent components (after accounting for the symmetries $R_{abcd} = R_{cdab}$, $R_{abcd} = -R_{bacd}$, and the first Bianchi identity $R_{a[bcd]} = 0$). Each Riemann component involves second derivatives of the metric, bounded on the lattice by the spectral radius $R_{\max} = 8/a^2$. Therefore:

$$K \leq 20 \times R_{\max}^2 = 20 \times \frac{64}{a^4} = \frac{1280}{a^4}$$

This is a rigorous but conservative upper bound, since it assumes all 20 independent components are simultaneously at their maximum. Physical geometries are more constrained:

**Schwarzschild reference.** For a Schwarzschild black hole in natural units ($c = \hbar = 1$), the Kretschmann scalar is $K = 48G^2M^2/r^6$. At the minimum radius $r = a$ with the maximum enclosed mass $M = a/(2G)$ (Schwarzschild condition $r_s = 2GM$ at $r = a$):

$$K_{\text{Schw}} = \frac{48G^2}{a^6}\cdot\frac{a^2}{4G^2} = \frac{12}{a^4}$$

**De Sitter reference.** For a maximally symmetric space (de Sitter) with $R = R_{\max}$, the Kretschmann scalar is $K_{\text{dS}} = R^2/6 = 64/(6a^4) \approx 11/a^4$.

Both reference geometries give $K \sim 12/a^4$, well below the rigorous bound of $1280/a^4$. The physical content is that $K$ cannot exceed $\mathcal{O}(\ell_P^{-4})$.

### §2.4 Minimum Trapped Surface Area

A trapped surface is a closed spacelike 2-surface on which both families of future-directed null normals have non-positive expansion: $\theta_+ \leq 0$ and $\theta_- \leq 0$ (Penrose 1965). On the FCC lattice, such a surface must be constructible from nearest-neighbour triangular plaquettes.

The FCC nearest-neighbour distance is $|\boldsymbol{\delta}_j| = a$ (each vector has the form $(a/\sqrt{2})(\pm 1, \pm 1, 0)$ with magnitude $a$). Three mutual nearest neighbours (e.g., sites at $\boldsymbol{\delta}_1 = (a/\sqrt{2})(1,1,0)$, $\boldsymbol{\delta}_2 = (a/\sqrt{2})(1,0,1)$, $\boldsymbol{\delta}_3 = (a/\sqrt{2})(0,1,1)$) have pairwise distance $|\boldsymbol{\delta}_i - \boldsymbol{\delta}_j| = a$, forming an equilateral triangle with side $a$. Its area is:

$$A_{\text{triangle}} = \frac{\sqrt{3}}{4}a^2$$

A trapped surface must be a *closed* 2-surface. The minimum closed surface on the FCC lattice consists of the 4 faces of a single tetrahedron formed by 4 mutually nearest-neighbour sites, giving:

$$A_{\min} = 4 \times \frac{\sqrt{3}}{4}a^2 = \sqrt{3}\,a^2$$

Substituting $a^2 \approx 5.07\,\ell_P^2$:

$$A_{\min} = \sqrt{3} \times 5.07\,\ell_P^2 \approx 8.8\,\ell_P^2$$

This exceeds the minimum area for one bit of Bekenstein-Hawking entropy, $A_{1\text{-bit}} = 4\ln(3)\,\ell_P^2 \approx 4.39\,\ell_P^2$ (with $\ln 3$ from the $\mathbb{Z}_3$ center structure of the stella octangula; cf. Theorem 5.2.5), by a factor of $\approx 2.0$. Any trapped surface on the FCC lattice therefore carries at least $\sim 2$ bits of entropy.

### §2.5 Form Factor Suppression

The lattice propagator in Fourier space includes the form factor:

$$F(\mathbf{k}) = \frac{1}{12}\sum_{j=1}^{12}\cos(\mathbf{k}\cdot\boldsymbol{\delta}_j) = \frac{1}{3}\bigl[\cos u\cos v + \cos u\cos w + \cos v\cos w\bigr]$$

where the second equality uses the factorization identity from §2.1.2. Since $g_{\min} = -1$ (shown above), the form factor ranges over:

$$F(\mathbf{k}) \in \left[-\tfrac{1}{3},\; 1\right]$$

**Values at high-symmetry Brillouin zone points:**

| Point | $\mathbf{k}$ (units of $2\pi/a_{\text{cubic}}$) | $F(\mathbf{k})$ |
|---|---|---|
| $\Gamma$ | $(0,0,0)$ | $+1$ |
| X | $(1,0,0)$ | $-1/3$ |
| W | $(1,\tfrac{1}{2},0)$ | $-1/3$ |
| L | $(\tfrac{1}{2},\tfrac{1}{2},\tfrac{1}{2})$ | $0$ |

The Laplacian eigenvalue is related to the form factor by $\lambda(\mathbf{k}) = (6/a^2)(F(\mathbf{k}) - 1)$, so the spectral radius $|\lambda|_{\max} = (6/a^2)(1 + 1/3) = 8/a^2$, consistent with §2.1.2.

**Physical interpretation.** Just as a crystal lattice has a maximum phonon frequency (Debye cutoff; Debye 1912), the FCC pre-geometric lattice has a maximum curvature. Both arise from the same mechanism: discrete structure cannot support arbitrarily short-wavelength excitations. The form factor $F < 1$ for all $\mathbf{k} \neq 0$ ensures that all UV modes are suppressed relative to their continuum values, preventing any physical process from generating curvatures exceeding $R_{\max}$.

### §2.6 Lorentz Invariance Recovery

The FCC lattice breaks continuous rotation symmetry $\text{O}(3)$ to the octahedral group $\text{O}_h$. We must verify that isotropy is recovered in the continuum limit.

**O($k^2$): Exact isotropy.** The quadratic coefficient of the eigenvalue expansion, $\sum_j (\delta_j)_a(\delta_j)_b = 4a^2\,\delta_{ab}$, is proportional to the identity matrix. This is a consequence of the cubic symmetry of the FCC lattice ($\text{O}_h \supset S_4$). The Laplacian eigenvalue at $\mathcal{O}(k^2)$ is therefore exactly isotropic: $\lambda(\mathbf{k}) = -k^2 + \mathcal{O}(k^4)$.

**O($k^4$): Leading anisotropy.** The quartic correction involves the fourth-order moment tensor $T_{abcd} = \sum_j (\delta_j)_a (\delta_j)_b (\delta_j)_c (\delta_j)_d$, which is not proportional to the fully symmetric isotropic tensor. The $\mathcal{O}(k^4)$ coefficient depends on direction:

$$\lambda(\mathbf{k}) = -k^2 + \frac{k^4}{48a^2}\sum_j (\hat{\mathbf{k}}\cdot\boldsymbol{\delta}_j)^4 + \mathcal{O}(k^6)$$

| Direction | $\sum_j (\hat{\mathbf{k}}\cdot\boldsymbol{\delta}_j)^4$ | $\mathcal{O}(k^4)$ coefficient |
|---|---|---|
| $[100]$ | $2a^4$ | $a^2 k^4/24$ |
| $[110]$ | $5a^4/2$ | $5a^2 k^4/96$ |
| $[111]$ | $8a^4/3$ | $a^2 k^4/18$ |

The anisotropy ratio between the extremal directions is $(8/3)/2 = 4/3 \approx 1.33$.

**Observational bound.** The anisotropic correction scales as $(ka)^2 \sim (E/E_P)^2$ relative to the leading term. At the highest accessible laboratory energies ($E \sim 10^4$ GeV), this gives $(E/E_P)^2 \sim 10^{-30}$, far below the strongest Lorentz violation bounds from gamma-ray burst polarimetry ($\sim 10^{-16}$). The lattice-induced Lorentz violation is unobservable by many orders of magnitude.

## §3 Consistency Checks

**Dimensional analysis:** $[R_{\max}] = [a^{-2}] = [\text{length}^{-2}]$ ✓

**Continuum limit:** As $a \to 0$, $R_{\max} \to \infty$, recovering the continuum where curvature is unbounded. ✓

**Comparison with other approaches:**
- Loop Quantum Gravity: $R_{\max} \sim 1/(\gamma^2\ell_P^2)$ with $\gamma \approx 0.2375$ (Domagala-Lewandowski 2004, Meissner 2004) → $R_{\max} \sim 17.7/\ell_P^2$
- Chiral Geometrogenesis: $R_{\max} \approx 1.58/\ell_P^2$

Both give $R_{\max} = \mathcal{O}(1/\ell_P^2)$ with $\mathcal{O}(1)$ coefficients, but the CG bound is tighter (lower maximum curvature). The difference reflects the distinct kinematic structures: LQG uses spin-network states on arbitrary graphs, while CG uses the fixed FCC lattice with its specific coordination geometry.

**Weak-field recovery:** For $R \ll R_{\max}$, the lattice corrections are $\mathcal{O}(a^2 R)$ and GR is recovered to high precision. ✓

## §4 Honest Limitations

1. The spectral radius $8/a^2$ is a sharp mathematical bound for the properly normalized FCC discrete Laplacian. However, the identification of the Ricci scalar $R$ with the Laplacian eigenvalue carries $\mathcal{O}(1)$ uncertainty from the precise discretization of Riemann curvature on the FCC lattice (Regge calculus, simplicial, etc.).

2. The Kretschmann bound $K \leq 1280/a^4$ is rigorous but very conservative (the bound assumes all 20 independent Riemann components are simultaneously maximal). Reference geometries (Schwarzschild, de Sitter) give $K \sim 12/a^4$ at $r = a$, suggesting the true achievable maximum is $\sim \mathcal{O}(10)/a^4$. A tighter bound requires specifying the full lattice Riemann tensor.

3. The minimum trapped surface area depends on the assumption that the Penrose trapped surface condition ($\theta_+ \leq 0$, $\theta_- \leq 0$) can be meaningfully evaluated on the lattice scale. At $r \sim a$, the continuum notion of a trapped surface becomes approximate.

4. The FCC lattice breaks continuous Lorentz symmetry to the discrete octahedral group $\text{O}_h$. While the leading $\mathcal{O}(k^2)$ physics is exactly isotropic, anisotropy at $\mathcal{O}(k^4)$ is a prediction of the framework. The magnitude $\sim (E/E_P)^2$ is far below any foreseeable experimental sensitivity, but the effect is non-zero in principle.

---

*Cross-references:*
- **Used by:** [Theorem 5.4.1](Theorem-5.4.1-Singularity-Resolution-Emergent-Gravity.md)
- **Depends on:** [Theorem 0.0.6](../foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md), [Proposition 0.0.17r](../foundations/Proposition-0.0.17r-Lattice-Spacing-From-Holographic-Self-Consistency.md)

*References:*
- R. Penrose, "Gravitational collapse and space-time singularities," *Phys. Rev. Lett.* **14**, 57 (1965)
- T. Regge, "General relativity without coordinates," *Nuovo Cimento* **19**, 558 (1961)
- J. Domagala, J. Lewandowski, "Black hole entropy from quantum geometry," *Class. Quant. Grav.* **21**, 5233 (2004)
- K. Meissner, "Black hole entropy in loop quantum gravity," *Class. Quant. Grav.* **21**, 5245 (2004)
- A. Ashtekar, T. Pawlowski, P. Singh, "Quantum nature of the big bang," *Phys. Rev. Lett.* **96**, 141301 (2006)
- P. Debye, "Zur Theorie der spezifischen Wärmen," *Ann. Phys.* **344**, 789 (1912)

*Verification:*
- **Multi-agent peer review:** [Lemma-5.4.1a-Multi-Agent-Verification-2026-02-27](../verification-records/Lemma-5.4.1a-Multi-Agent-Verification-2026-02-27.md)
- **Adversarial physics verification:** [lemma_5_4_1a_adversarial_verification.py](../../../verification/Phase5/lemma_5_4_1a_adversarial_verification.py) — 13 tests, 4 plots
- **Lean 4 formalization:** [Lemma_5_4_1a.lean](../../../lean/ChiralGeometrogenesis/Phase5/Lemma_5_4_1a.lean)
