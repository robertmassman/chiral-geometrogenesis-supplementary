# Proposition 7.5.1: Symanzik Effective Theory for FCC — Applications

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Proposition-7.5.1-Symanzik-Effective-Theory-FCC.md) | Proposition statement, motivation, symbol table |
| [Derivation](./Proposition-7.5.1-Symanzik-Effective-Theory-FCC-Derivation.md) | Complete derivation of Parts (a)-(d) |
| **Applications (this file)** | Verification, numerical checks, physical interpretation |

---

## §8. Applications and Verification

### §8.1 Physical Interpretation

#### §8.1.1 What the Symanzik Coefficients Mean

The Symanzik effective theory is not merely a formal classification — it has direct physical consequences:

**1. Discretization errors in physical observables.** For any gauge-invariant observable $\mathcal{O}$ (e.g., glueball mass, string tension, topological susceptibility), the lattice expectation value differs from the continuum by:

$$\langle\mathcal{O}\rangle_\text{lat} = \langle\mathcal{O}\rangle_\text{cont} + a^2 \sum_i c_i \langle\mathcal{O}\cdot\mathcal{O}_i\rangle_\text{cont} + O(a^4) \tag{8.1}$$

On the FCC lattice, the **absence** of $\mathcal{O}_4$ at $O(a^2)$ means that the leading rotational artifact is pushed to $O(a^4)$. This implies:

- Glueball masses in different spin channels ($0^{++}$, $2^{++}$, etc.) converge to their continuum values at the **same rate** up to $O(a^4)$
- The static quark potential $V(r)$ has no $O(a^2)$ angular distortion on the FCC lattice
- The plaquette expectation value approaches the continuum value with $O(a^2)$ corrections from $\mathcal{O}_1$ only

**2. Improved scaling.** On the FCC lattice, the $O(a^2)$ corrections involve only $\mathcal{O}_1$ (EOM, removable on shell) and $\mathcal{O}_3$ (rotationally invariant). The rotational-breaking operator $\mathcal{O}_4$ is absent. For on-shell quantities, the FCC lattice is effectively "tree-level improved" in the rotational sector. The FCC theory with the standard Wilson action has the same $O(a^2)$ rotational structure as the Lüscher-Weisz improved action on the hypercubic lattice.

**3. Scaling violations.** The approach to asymptotic scaling is governed by:

$$\frac{\langle\mathcal{O}\rangle_\text{lat}(\beta)}{\langle\mathcal{O}\rangle_\text{cont}} = 1 + c_1(\beta)\left(\frac{a(\beta)}{\lambda_\text{phys}}\right)^2 + c_4(\beta)\left(\frac{a(\beta)}{\lambda_\text{phys}}\right)^2 + O(a^4)$$

On the FCC lattice, the $c_4$ term is absent, so scaling violations are reduced.

#### §8.1.2 Comparison of Lattice Artifacts

| Observable | Cubic artifact | FCC artifact | Improvement factor |
|-----------|---------------|-------------|-------------------|
| Glueball mass ($0^{++}$) | $(c_1 + c_4) a^2$ | $c_1' a^2$ | ~2× at tree level$^\dagger$ |
| Glueball mass ratio | $c_4 a^2$ (rotational) | $O(a^4)$ | ~$(a/a_0)^2$ |
| Static potential $V(r)$ | $(c_1 + c_4 P_4(\hat{r})) a^2$ | $c_1' a^2$ | Angular dependence eliminated |
| String tension $\sigma$ | $c_1 a^2$ | $c_1' a^2$ | ~1× (same order) |
| Plaquette $\langle P \rangle$ | $(c_1 + c_4) a^2$ | $c_1' a^2$ | ~2× at tree level$^\dagger$ |

Here $P_4(\hat{r})$ denotes the angular-dependent rotational artifact, and $a_0$ is a reference lattice spacing.

$^\dagger$**Note on "~2×" estimates:** The ~2× improvement factors are **tree-level estimates**, valid when $c_1^{(0)} = c_4^{(0)} = 1/12$ on the hypercubic lattice so that removing $c_4$ halves the total coefficient. At one loop and beyond, the relative sizes of $c_1$ and $c_4$ change, so the precise improvement factor is $\beta$-dependent. Furthermore, these estimates do not account for the larger FCC tadpole integral ($I_\text{FCC}/I_\text{cubic} \approx 1.78$), which increases the $c_1'$ coefficient on the FCC lattice relative to the hypercubic $c_1$. For a fair comparison at one loop, one should also consider the Lüscher-Weisz improved action on the hypercubic lattice, which achieves $c_4 = 0$ by adding counter-terms and additionally tunes $c_1$ and $c_3$.

### §8.2 Numerical Verification: Fourth-Moment Isotropy

#### §8.2.1 Direct Computation of the Isotropy Tensor

The $D_4$ lattice has 24 nearest-neighbor unit vectors. The fourth-moment tensor components are:

$$T_{\mu\nu\rho\sigma} = \sum_{i=1}^{24} \hat{n}_{i\mu}\hat{n}_{i\nu}\hat{n}_{i\rho}\hat{n}_{i\sigma}$$

**Computed values:**

| Component | $D_4$ value | Isotropic value | Match? |
|-----------|-------------|-----------------|--------|
| $T_{1111}$ | 3 | 3 | ✅ |
| $T_{1122}$ | 1 | 1 | ✅ |
| $T_{1112}$ | 0 | 0 | ✅ |
| $T_{1123}$ | 0 | 0 | ✅ |

The isotropic tensor has $T_{\mu\nu\rho\sigma}^{\text{iso}} = \delta_{\mu\nu}\delta_{\rho\sigma} + \delta_{\mu\rho}\delta_{\nu\sigma} + \delta_{\mu\sigma}\delta_{\nu\rho}$ (when properly normalized with the factor $z/(d(d+2)) = 24/24 = 1$).

**Verification:** All $4^4 = 256$ components of $T_{\mu\nu\rho\sigma}^{D_4}$ match $T_{\mu\nu\rho\sigma}^{\text{iso}}$ exactly.

**Contrast with hypercubic ($\mathbb{Z}^4$):**

| Component | $\mathbb{Z}^4$ value | Isotropic value | Match? |
|-----------|----------------------|-----------------|--------|
| $T_{1111}$ | 2 | $8/24 \cdot 3 = 1$ | ❌ |
| $T_{1122}$ | 0 | $8/24 \cdot 1 = 1/3$ | ❌ |

The hypercubic lattice has significant fourth-moment anisotropy.

#### §8.2.2 Sixth-Moment Tensor (First Anisotropy for $D_4$)

The sixth-moment tensor $T_{\mu\nu\rho\sigma\alpha\beta}^{(6)}$ is the first place where $D_4$ deviates from perfect isotropy. The isotropic sixth-moment tensor has 15 independent components (from 3 distinct contraction patterns of 6 indices).

For $D_4$, the sixth-moment tensor satisfies:

$$T_{111111}^{D_4} = \sum_{i=1}^{24} n_{i1}^6 = 12 \times (1/\sqrt{2})^6 = 12/8 = 3/2 \tag{8.2}$$

$$T_{111111}^{\text{iso}} = \frac{24}{4\cdot 6\cdot 8}\cdot 15 = \frac{24 \cdot 15}{192} = \frac{15}{8} \tag{8.3}$$

Since $3/2 \neq 15/8$, the sixth-moment tensor is anisotropic. This means:
- **$O(a^4)$ rotational artifacts ARE present** on the FCC lattice
- But they are two orders of $a$ suppressed relative to the hypercubic lattice

### §8.3 Numerical Verification: Symanzik Coefficient $c_1$

#### §8.3.1 Tree-Level Verification

At tree level, the Symanzik coefficient $c_1^{(0)} = 1/12$ can be verified by expanding the FCC plaquette action and comparing with the continuum action at $O(a^2)$.

**Method:** Compute the expectation value $\langle\frac{1}{3}\operatorname{Re}\operatorname{Tr} U_\triangle\rangle$ for a smooth gauge field $A_\mu(x) = A_\mu^0 \cos(k\cdot x)$ with small amplitude, at different lattice spacings $a$, and extract the $O(a^2)$ coefficient by fitting.

**Result:** $c_1^{(\text{FCC}),(0)} = 0.0833 \pm 0.0001 = 1/12.000 \pm 0.001$. ✓

See `verification/Phase7/prop_7_5_1_symanzik_fcc.py` for the numerical implementation.

#### §8.3.2 One-Loop Estimate

The one-loop correction to $c_1$ involves the FCC tadpole integral:

$$c_1^{(\text{FCC}),(1)} \approx c_1^{(\text{cubic}),(1)} + \Delta_\text{tad}(I_\text{FCC} - I_\text{cubic}) \tag{8.4}$$

Using $I_\text{FCC} \approx 0.276$ and $I_\text{cubic} = 0.15493$:

$$\Delta I = I_\text{FCC} - I_\text{cubic} \approx 0.121 \tag{8.5}$$

The one-loop coefficient for the cubic lattice is $c_1^{(\text{cubic}),(1)} = -0.012(1)$ (Lüscher-Weisz 1985). The FCC correction shifts this by an amount proportional to $\Delta I$:

$$c_1^{(\text{FCC}),(1)} \approx -0.012 + \alpha \cdot 0.121 \tag{8.6}$$

where $\alpha$ is a group-theory factor of order unity. A precise determination requires the full one-loop matching calculation on the FCC lattice.

### §8.4 Implications for the Continuum Limit

#### §8.4.1 Rate of Approach to the Continuum

The Symanzik analysis predicts that the FCC lattice approaches the continuum as:

$$\langle\mathcal{O}\rangle_\text{FCC}(a) = \langle\mathcal{O}\rangle_\text{cont}\left[1 + c_1^{(\text{FCC})} a^2 \Lambda^2 + O(a^4)\right] \tag{8.7}$$

where $\Lambda$ is a physical scale (e.g., $\sqrt{\sigma}$ or $m_{0^{++}}$). For the hypercubic lattice:

$$\langle\mathcal{O}\rangle_\text{cubic}(a) = \langle\mathcal{O}\rangle_\text{cont}\left[1 + (c_1^{(\text{cubic})} + c_4^{(\text{cubic})}\cdot R_\mathcal{O}) a^2 \Lambda^2 + O(a^4)\right] \tag{8.8}$$

where $R_\mathcal{O}$ depends on the observable (e.g., the angular momentum content). The FCC lattice has **no** $c_4$ contribution at $O(a^2)$, which:

1. **Eliminates observable-dependent rotational artifacts** — all observables approach the continuum at the same rate (up to universal $c_1$ corrections)
2. **Simplifies the continuum extrapolation** — fewer parameters needed in $a^2$ fits
3. **Reduces systematic errors** in glueball mass determinations

#### §8.4.2 Effective $O(a^4)$ Improvement for Rotationally-Sensitive Quantities

For quantities that are sensitive to rotational symmetry (e.g., glueball mass ratios, angular distributions), the FCC lattice is effectively $O(a^4)$-improved:

$$\left.\frac{m_{2^{++}}}{m_{0^{++}}}\right|_\text{FCC} = \left.\frac{m_{2^{++}}}{m_{0^{++}}}\right|_\text{cont} + O(a^4) \tag{8.9}$$

whereas on the hypercubic lattice:

$$\left.\frac{m_{2^{++}}}{m_{0^{++}}}\right|_\text{cubic} = \left.\frac{m_{2^{++}}}{m_{0^{++}}}\right|_\text{cont} + c_4 \cdot a^2\Lambda^2 + O(a^4) \tag{8.10}$$

This two-order improvement in rotational artifacts is a significant advantage of the FCC lattice for precision spectroscopy.

#### §8.4.3 Tadpole Penalty and Perturbative Convergence

While the FCC lattice eliminates the $O(a^2)$ rotational artifact ($c_4 = 0$), it comes with a cost in the perturbative sector. The FCC tadpole integral is significantly larger than the hypercubic one:

$$I_\text{FCC} \approx 0.276 \quad \text{vs} \quad I_\text{cubic} = 0.15493 \qquad (\text{ratio} \approx 1.78)$$

This means perturbative corrections in the tadpole sector are approximately 78% larger on the FCC lattice. The physical consequences include:

1. **Larger one-loop corrections to $c_1$ and $c_3$:** The FCC-specific one-loop coefficients receive contributions proportional to $I_\text{FCC}$, which shifts them relative to the hypercubic values.

2. **Slower perturbative convergence:** Higher-order perturbative corrections, which generically involve powers of $g_0^2 I_\text{lat}$, converge more slowly on the FCC lattice. This makes tadpole improvement (Lepage-Mackenzie 1993) more important for FCC simulations.

3. **Tadpole improvement becomes essential:** The Lepage-Mackenzie tadpole improvement program replaces $g_0^2 \to g_0^2/u_0^4$ where $u_0 = \langle\frac{1}{3}\operatorname{Re}\operatorname{Tr} U_\triangle\rangle^{1/4}$ absorbs the large tadpole contributions. On the FCC lattice, $u_0^4$ deviates more from 1 than on the hypercubic lattice, making this resummation more impactful.

**Net assessment:** The FCC lattice trades a larger tadpole integral (affecting perturbative corrections to all operators) for the elimination of the rotational-breaking operator. For rotationally sensitive quantities (glueball mass ratios, angular distributions), the FCC advantage is clear. For rotationally insensitive quantities (plaquette, string tension), the FCC lattice has comparable or slightly worse $O(a^2)$ corrections before tadpole improvement.

### §8.5 Connection to Prop 7.4.3

This proposition extends the lattice perturbation theory of Prop 7.4.3 in several ways:

1. **Prop 7.4.3 Part (c)** stated that FCC lattice artifacts are $O(a^2)$ with improved isotropy. **This proposition** provides the complete operator classification showing exactly which $O(a^2)$ operators appear and which are absent.

2. **Prop 7.4.3 Lemma 6.3.1** proved the fourth-moment isotropy of $D_4$. **This proposition** shows the full consequences: $c_4 = 0$ at both tree level and one loop.

3. **Prop 7.4.3 Part (d)** computed the Lambda parameter ratio using the tadpole integral. **This proposition** shows how the tadpole integral enters the one-loop Symanzik coefficients.

### §8.6 Connection to Thm 7.5.2

The Symanzik classification is the direct input to the perturbative universality theorem (Thm 7.5.2):

1. **The operator difference** $S_\text{FCC} - S_\text{cubic} = a^2 \Delta c_i \cdot \mathcal{O}_i + O(a^4)$ involves only dimension $\geq 6$ operators (irrelevant in the RG sense)

2. **The irrelevance of the operator difference** implies that the two lattice theories flow to the same continuum fixed point under RG

3. **The vanishing of $c_4$** on FCC means the operator difference is entirely in the "universal" sector ($\mathcal{O}_1$, $\mathcal{O}_2$, $\mathcal{O}_3$), not in the lattice-specific rotational sector — this simplifies the universality argument

### §8.7 Self-Consistency Checks

#### §8.7.1 Dimensional Analysis

| Quantity | Dimension | Check |
|----------|-----------|-------|
| $c_i^{(0)}$ | Dimensionless | ✅ (pure numbers) |
| $a^2 c_i \int d^4x\, \mathcal{O}_i$ | Dimensionless | ✅ ($[a^2][d^4x][\mathcal{O}_i] = L^2 \cdot L^4 \cdot L^{-6} = 1$) |
| $I_\text{FCC}$ | Dimensionless | ✅ (momentum integral with $d^4k/(2\pi)^4 \cdot 1/k^2$ in lattice units) |
| $c_4^{(\text{FCC})} = 0$ | Dimensionless | ✅ |

#### §8.7.2 Limiting Cases

**1. $a \to 0$ (continuum limit):** All $O(a^2)$ and higher corrections vanish → $S_\text{FCC} \to S_\text{cont}$. ✅

**2. Free-field limit ($g_0 \to 0$):** The Symanzik coefficients reduce to their tree-level values: $c_1 = 1/12$, $c_2 = c_3 = c_4 = 0$. ✅

**3. Abelian limit (U(1)):** The operator $\mathcal{O}_2$ (triple-$F$) has **vanishing coefficient** for abelian gauge groups: the operator $\operatorname{Tr}(F_{\mu\nu}F_{\nu\rho}F_{\rho\mu})$ itself is generally nonzero for $U(1)$, but its Symanzik coefficient $c_2$ vanishes because the non-abelian vertex corrections that generate $c_2^{(1)}$ at one loop are absent. At tree level, $c_2^{(0)} = 0$ for any gauge group. On the FCC lattice, with $c_4 = 0$ from isotropy and $c_3 = 0$ at tree level, the Symanzik expansion reduces to $S_\text{cont} + c_1 a^2 \mathcal{O}_1$, matching the known U(1) lattice result. ✅

**4. Hypercubic limit ($D_4 \to \mathbb{Z}^4$):** If we restrict to axis-aligned plaquettes and $z = 8$ coordination, the fourth-moment tensor becomes anisotropic and $c_4^{(0)} = 1/12$, recovering the standard Curci-Menotti-Paffuti result. ✅

#### §8.7.3 Gauge Invariance

All operators $\mathcal{O}_i$ are gauge-invariant by construction:
- $\mathcal{O}_1 = \operatorname{Tr}(D_\mu F_{\mu\nu}\, D_\rho F_{\rho\nu})$: EOM operator, gauge-invariant (removable by field redefinition)
- $\mathcal{O}_2 = \operatorname{Tr}(F_{\mu\nu} F_{\nu\rho} F_{\rho\mu})$: triple field-strength (cubic vertex correction), gauge-invariant
- $\mathcal{O}_3 = \operatorname{Tr}(D_\mu F_{\nu\rho}\, D_\mu F_{\nu\rho})$: rotationally invariant, involves covariant derivative and field strength
- $\mathcal{O}_4 = \operatorname{Tr}(D_\mu F_{\mu\nu}\, D_\mu F_{\mu\nu})$: rotational-breaking operator, gauge-invariant

The Symanzik coefficients are gauge-invariant quantities (they are Wilson coefficients in the effective theory matching).

### §8.8 Computational Verification

The following tests are implemented in `verification/Phase7/prop_7_5_1_symanzik_fcc.py`:

| Test | Description | Status |
|------|-------------|--------|
| Fourth-moment isotropy | Verify $T_{\mu\nu\rho\sigma}^{D_4}$ is exactly isotropic | Implemented |
| Sixth-moment anisotropy | Verify first anisotropy at order 6 | Implemented |
| Tree-level $c_1$ | Verify $c_1^{(0)} = 1/12$ from plaquette expansion | Implemented |
| $c_4 = 0$ | Verify vanishing of rotational-breaking coefficient | Implemented |
| Plaquette sum isotropy | Verify plaquette sum reproduces continuum action | Implemented |
| Hypercubic comparison | Verify $c_4^{(\text{cubic})} \neq 0$ | Implemented |
| Tadpole integral consistency | Cross-check $I_\text{FCC}$ with Prop 7.4.3 | Implemented |
| Operator independence | Verify 4 operators are linearly independent | Implemented |
| Dimensional analysis | All equations dimensionally consistent | Implemented |

---

## §9. Summary

### §9.1 Main Results

1. **Complete Symanzik classification** for the FCC lattice with triangular plaquettes: 4 dimension-6 operators in the CMP83/LW85 basis with FCC-specific coefficients
2. **$c_4^{(\text{FCC})} = 0$** at $O(a^2)$ — the rotational symmetry-breaking operator is absent, both at tree level and one loop
3. **Only $\mathcal{O}_1$ and $\mathcal{O}_3$ appear at $O(a^2)$** — the FCC lattice has no rotational artifacts at leading order; $\mathcal{O}_1$ is removable on shell
4. **Geometric origin** — the improved isotropy is a consequence of the $D_4$ lattice structure, which is derived from the stella octangula

### §9.2 Significance for the Mass Gap Program

This result is Step F.1–F.2 of the Yang-Mills mass gap program. It establishes that the FCC and hypercubic lattice formulations differ only by **irrelevant operators** (dimension $\geq 6$), which is the key input for perturbative universality (Thm 7.5.2, Step F.3).

---

*Document created: 2026-02-13*
*Classification: 🔶 NOVEL (FCC-specific) / ✅ ESTABLISHED (Symanzik framework)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase F (Universality and Transition Analysis)*
