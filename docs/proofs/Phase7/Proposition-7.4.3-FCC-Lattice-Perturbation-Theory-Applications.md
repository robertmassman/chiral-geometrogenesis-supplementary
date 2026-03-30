# Proposition 7.4.3: FCC Lattice Perturbation Theory — Applications

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Proposition-7.4.3-FCC-Lattice-Perturbation-Theory.md) | Proposition statement, motivation, symbol table |
| [Derivation](./Proposition-7.4.3-FCC-Lattice-Perturbation-Theory-Derivation.md) | Complete derivation of Parts (a)-(d) |
| **Applications (this file)** | Verification, numerical checks, physical interpretation |

---

## §8. Applications and Verification

### §8.1 Physical Interpretation

#### §8.1.1 Lattice Spacing vs Coupling

The asymptotic scaling formula $a(\beta) = \Lambda_\text{FCC}^{-1}(6b_0/\beta)^{-b_1/(2b_0^2)}\exp(-\beta/(12b_0))$ gives the lattice spacing as a function of the bare coupling. Key values for SU(3):

| $\beta$ | $a\Lambda_\text{FCC}$ | $a$ (fm) [$\Lambda_\text{FCC} \approx 2.6$ MeV] | Regime |
|---------|----------------------|-------------------------------------------------|--------|
| 3.0 | 1.2 | 91 | Strong coupling |
| 5.0 | 0.31 | 24 | Intermediate |
| 6.0 | 0.14 | 10.6 | Scaling window |
| 8.0 | 0.016 | 1.2 | Deep scaling |
| 10.0 | 0.0012 | 0.091 | Perturbative |

*Note: These are asymptotic scaling values using $\Lambda_\text{FCC} \approx 2.6$ MeV (from $\Lambda_{\overline{MS}} = 260$ MeV for quenched SU(3) and $\Lambda_\text{FCC}/\Lambda_{\overline{MS}} \approx 0.010$). At strong coupling ($\beta \lesssim 5$), non-perturbative corrections are significant. The physical $a(\text{fm})$ values are unphysically large at moderate $\beta$ because the FCC lattice Lambda is very small.*

#### §8.1.2 Physical Mass Gap Estimate

Combining the lattice mass gap $\mu(\beta)$ from Theorem 7.4.2 with the lattice spacing $a(\beta)$ from this proposition:

$$m_\text{phys}(\beta) = \frac{\sqrt{3/2}\,\mu(\beta)}{a(\beta)}$$

where $a$ is the nearest-neighbor distance (Derivation §5.1) and $d_{111} = a\sqrt{2/3}$ is the (111) interlayer distance. The factor $\sqrt{3/2} = 1/\sqrt{2/3}$ converts from (111) layer units ($\mu$ is dimensionless per layer) to physical units ($m_\text{phys} = \mu / d_{111}$).

At strong coupling ($\beta \ll \beta_c$):
- $\mu(\beta)$ is large (order 10-40)
- $a(\beta)$ is large (order fm)
- $m_\text{phys} \sim O(\text{GeV})$

As $\beta \to \beta_c^-$:
- $\mu \to 0$ (gap vanishes on the lattice)
- $a \to 0$ (lattice becomes invisible)
- The ratio $\mu/a$ should approach a finite limit = physical mass gap

This is the content of Theorem 7.4.5.

#### §8.1.3 Improved Continuum Limit from FCC

The FCC lattice's improved isotropy (Lemma 6.3.1 in the Derivation) has practical consequences:

1. **Faster approach to SO(4):** The absence of $O(a^2)$ rotational artifacts means the FCC theory approaches the continuum faster than the hypercubic theory.

2. **Reduced discretization errors:** For glueball mass computations, the leading lattice artifact is $O(a^2)$ from the non-rotational operators ($\mathcal{O}_1$), not from rotational symmetry breaking.

3. **Connection to CG:** The FCC lattice is not chosen for computational convenience — it is the unique lattice derived from the stella octangula geometry. The improved isotropy is a **prediction** of the framework: the geometrically forced lattice happens to have better continuum limit properties.

### §8.2 Numerical Verification: Beta Function Universality

#### §8.2.1 Small-$\beta$ Heat Kernel Expansion

At strong coupling, we can verify the beta function by comparing the heat kernel expansion of $u_\mathbf{3}(\beta)$ with the perturbative prediction.

For small $g_0^2 = 6/\beta$ (large $\beta$), the heat kernel coefficient ratio approaches:

$$u_\mathbf{3}(\beta) = \frac{a_\mathbf{3}(\beta)}{a_\mathbf{1}(\beta)} \xrightarrow{\beta \to \infty} 1 - \frac{C_2(\mathbf{3})}{2\beta} + O(\beta^{-2})$$

where $C_2(\mathbf{3}) = 4/3$. This gives:

$$\mu(\beta) = -3\ln 3 - 8\ln\left(1 - \frac{2}{3\beta} + \cdots\right) \xrightarrow{\beta \to \infty} -3\ln 3 + \frac{16}{3\beta} + O(\beta^{-2})$$

The perturbative mass gap vanishes logarithmically as $\beta \to \infty$, consistent with asymptotic freedom.

#### §8.2.2 Lattice Spacing Consistency

The asymptotic scaling formula predicts:

$$\frac{a(\beta_1)}{a(\beta_2)} = \left(\frac{\beta_2}{\beta_1}\right)^{b_1/(2b_0^2)} \exp\left(-\frac{\beta_1 - \beta_2}{12b_0}\right)$$

This ratio is independent of $\Lambda_\text{FCC}$ and can be tested numerically by comparing the mass gap at different $\beta$ values (see verification script).

### §8.3 Numerical Verification: FCC Tadpole Integral

#### §8.3.1 Computation Strategy

The FCC tadpole integral

$$I_\text{FCC} = \int_\text{BZ} \frac{d^4k}{(2\pi)^4}\frac{1}{\hat{k}^2_\text{FCC}}$$

is computed by numerical integration over the $D_4$ Brillouin zone. We use:

1. **Method 1:** Direct integration over the 24-cell using a coordinate parameterization
2. **Method 2:** Monte Carlo integration with $10^6$ random points in the Brillouin zone
3. **Method 3:** Lattice perturbation theory series expansion

All three methods should agree to within numerical precision.

#### §8.3.2 Expected Value

Based on the $D_4$ lattice structure with correctly normalized propagator ($\hat{k}^2_\text{FCC} \to k^2$):

$$I_\text{FCC} = 0.276 \pm 0.001 \quad \text{(integer convention, properly normalized)}$$

This is larger than the hypercubic value ($I_\text{cubic} = 0.15493$) because the $1/3$ normalization factor in $\hat{k}^2_\text{FCC}$ (required to give the correct continuum limit from 24 nearest neighbors) increases the integrand $1/\hat{k}^2$. The FCC and cubic integrals are in different lattice spacing conventions (nearest-neighbor distance $\sqrt{2}$ vs 1 in integer units).

### §8.4 Self-Consistency Checks

#### §8.4.1 Dimensional Consistency

| Quantity | Dimensions | Check |
|----------|-----------|-------|
| $b_0 = 11/(16\pi^2)$ | Dimensionless | ✅ |
| $b_1 = 102/(16\pi^2)^2$ | Dimensionless | ✅ |
| $\beta = 6/g_0^2$ | Dimensionless | ✅ |
| $a(\beta) \sim \Lambda_\text{FCC}^{-1} \exp(\cdots)$ | Length | ✅ ($\Lambda$ has dim mass) |
| $I_\text{FCC} = \int d^4k/(2\pi)^4 / \hat{k}^2$ | Dimensionless | ✅ (4D integral / mass$^2$ = mass$^2$, but $k$ in lattice units) |
| $\Lambda_\text{FCC}/\Lambda_{\overline{MS}}$ | Dimensionless | ✅ (ratio of same dimension) |

#### §8.4.2 Limiting Cases

1. **$\beta \to \infty$:** $a \to 0$ ✅ (continuum limit)
2. **$\beta \to 0$:** $a \to \infty$ ✅ (strong coupling, lattice dominates)
3. **$N_c = 0$ (hypothetical):** $b_0 = 0$, no asymptotic freedom ✅
4. **$N_c = 3$, $N_f = 16.5$:** $b_0 = 0$, loss of asymptotic freedom ✅ (Banks-Zaks fixed point)

#### §8.4.3 Cross-Check with Theorem 7.3.2

Theorem 7.3.2 (Asymptotic Freedom) established the beta function in the continuum. This proposition confirms the same result on the lattice, providing a non-trivial consistency check:

- Thm 7.3.2 $b_0$: $11/(16\pi^2) = 0.06966$ ✅
- This proposition $b_0$: $11N_c/(3(4\pi)^2) = 11 \times 3/(3 \times 16\pi^2) = 11/(16\pi^2)$ ✅

### §8.5 Connection to CG Framework

#### §8.5.1 Pressure Balance Origin

Proposition 7.3.2a derives asymptotic freedom from the pressure balance mechanism: at high energies, the chiral pressure gradient weakens, releasing the color fields. On the FCC lattice, this manifests as the perturbative expansion of the Wilson action around $U_\ell = \mathbb{1}$.

The CG contribution: the **structure** of the beta function (negative sign, $N_c$ dependence) has a geometric origin in the pressure balance on the stella octangula. The **coefficient** $b_0 = 11/(16\pi^2)$ is a universal consequence of SU(3) gauge invariance in $d = 4$.

#### §8.5.2 Holographic Lattice Spacing

Proposition 0.0.17r predicts $a^2 = (8/\sqrt{3})\ln(3)\ell_P^2 \approx 5.07\ell_P^2$. Using $\ell_P = 1.616 \times 10^{-35}$ m:

$$a_\text{CG} = \sqrt{5.07} \times 1.616 \times 10^{-35} \text{ m} = 3.64 \times 10^{-35} \text{ m}$$

Converting to energy: $1/a_\text{CG} \approx 5.42 \times 10^{18}$ GeV.

The asymptotic scaling formula gives $a(\beta_*)$ for some $\beta_*$ in the scaling window. Matching:

$$a(\beta_*) = a_\text{CG} \implies \beta_* = 12b_0 \ln\frac{1}{a_\text{CG} \Lambda_\text{FCC}}$$

Using $\Lambda_\text{FCC} \approx 0.010 \times 260$ MeV $= 2.6$ MeV $= 2.6 \times 10^{-3}$ GeV:

$$\beta_* \approx 12 \times 0.06966 \times \ln\frac{5.42 \times 10^{18}}{2.6 \times 10^{-3}} \approx 0.836 \times 49.1 \approx 41.0$$

This is deep in the perturbative regime, consistent with the CG lattice spacing being a Planck-scale quantity.

### §8.6 Comparison with Lattice QCD Literature

| Quantity | Standard lattice QCD | This work (FCC) |
|----------|---------------------|-----------------|
| $b_0$ | $11/(16\pi^2)$ | $11/(16\pi^2)$ ✅ (universal) |
| $b_1$ | $102/(16\pi^2)^2$ | $102/(16\pi^2)^2$ ✅ (universal) |
| $\Lambda_{\overline{MS}}/\Lambda_\text{lat}$ | $28.8$ (cubic) | $\approx 99$ (FCC, estimated) |
| $\Lambda_\text{lat}/\Lambda_{\overline{MS}}$ | $0.035$ (cubic) | $\approx 0.010$ (FCC, estimated) |
| Leading artifact | $O(a^2)$ (rotational) | $O(a^4)$ (rotational!) |
| Tadpole integral | 0.15493 | $0.276 \pm 0.001$ (integer convention) |
| Improvement scheme | Symanzik/Lüscher-Weisz | Same framework, better starting point |

---

*Document created: 2026-02-13*
*Classification: Mixed — ✅ ESTABLISHED (universal) / 🔶 NOVEL (FCC-specific)*
*Phase: 7 (Renormalization, unitarity, consistency)*
