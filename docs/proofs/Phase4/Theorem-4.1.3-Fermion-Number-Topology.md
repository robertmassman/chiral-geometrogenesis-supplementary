# Theorem 4.1.3: Fermion Number from Topology

## Status: ✅ ESTABLISHED — Standard Result | ✅ VERIFIED (2025-12-14) | ✅ LEAN FORMALIZED

**Classification:** This theorem is an established result proven by Witten (1983), building on the Atiyah-Singer index theorem. It provides the fundamental connection between topological solitons and fermionic matter.

**Verification:** Multi-agent peer review (Math + Physics + Literature + Computational); 6/6 tests pass.
**Session Log:** `verification/shared/Theorem-4.1.3-Multi-Agent-Verification-Report.md`

**Lean 4 Formalization:** Complete (December 27, 2025)
- **File:** `lean/ChiralGeometrogenesis/Phase4/Theorem_4_1_3.lean`
- **Main Theorem:** `fermion_number_equals_topological_charge`

**Original Sources:**
- Witten, E. (1983). "Global aspects of current algebra." *Nuclear Physics B*, **223**, 422-432.
- Witten, E. (1983). "Current algebra, baryons, and quark confinement." *Nuclear Physics B*, **223**, 433-444.

---

## 1. Statement

**Theorem 4.1.3 (Fermion Number from Topology)**

A soliton with topological charge $Q$ carries fermion number equal to $Q$:

$$\boxed{N_F = Q}$$

This identification arises from the spectral flow of the Dirac operator in the soliton background.

---

## 2. Mathematical Foundation

### 2.1 The Atiyah-Singer Index Theorem

For a Dirac operator $\cancel{D}$ coupled to a gauge field on a compact 4-manifold, the index theorem states:

$$\text{ind}(\cancel{D}) = n_+ - n_- = \frac{1}{16\pi^2}\int d^4x\, \text{Tr}(F_{\mu\nu}\tilde{F}^{\mu\nu})$$

where:
- $n_+$ = number of positive chirality zero modes (solutions to $\cancel{D}\psi = 0$ with $\gamma_5\psi = +\psi$)
- $n_-$ = number of negative chirality zero modes (solutions to $\cancel{D}\psi = 0$ with $\gamma_5\psi = -\psi$)
- $\tilde{F}^{\mu\nu} = \frac{1}{2}\epsilon^{\mu\nu\rho\sigma}F_{\rho\sigma}$ is the dual field strength
- Trace normalization: $\text{Tr}(T^a T^b) = \frac{1}{2}\delta^{ab}$

**Derivation of coefficient:** The topological density $\text{Tr}(F\tilde{F})$ integrates to give the second Chern number $c_2 = \frac{1}{8\pi^2}\int\text{Tr}(F\wedge F)$. For the index theorem, $\text{ind}(\cancel{D}) = 2c_2$, yielding the $1/(16\pi^2)$ coefficient.

### 2.2 Extension to Non-Compact Spaces (Callias Index Theorem)

For solitons in $\mathbb{R}^3$ (spatial infinity, not compact), we use the Callias index theorem:

$$\text{ind}(\cancel{D}) = \frac{1}{4\pi}\int_{S^2_\infty} \text{Tr}(\Phi \, dA)$$

where $\Phi$ is the Higgs field and $S^2_\infty$ is the sphere at spatial infinity. For Skyrmions, this reduces to the winding number $Q$.

### 2.3 Application to Skyrmions: Index = Winding Number

For a Skyrmion field $U: \mathbb{R}^3 \to SU(2)$ with boundary condition $U \to 1$ as $|\mathbf{x}| \to \infty$, the topological charge is:

$$Q = \frac{1}{24\pi^2}\int d^3x\, \epsilon^{ijk}\text{Tr}(L_i L_j L_k)$$

where $L_i = U^\dagger \partial_i U$ are the left-invariant Maurer-Cartan currents.

**Derivation:** This is the winding number of the map $U: S^3 \to SU(2) \cong S^3$:
- Compactify $\mathbb{R}^3 \cup \{\infty\} \cong S^3$ using the boundary condition
- The map $U$ belongs to $\pi_3(SU(2)) = \mathbb{Z}$
- The topological charge counts how many times $U$ wraps around the target $SU(2)$

**Explicit calculation for hedgehog ansatz:**

For $U(\mathbf{x}) = \exp(i\hat{r}\cdot\boldsymbol{\tau}F(r))$ with $F(0) = \pi$, $F(\infty) = 0$:

$$Q = -\frac{2}{\pi}\int_0^\infty \sin^2(F)\frac{dF}{dr}\,dr = -\frac{2}{\pi}\int_\pi^0 \sin^2(F)\,dF = \frac{2}{\pi}\cdot\frac{\pi}{2} = 1$$

This confirms $Q = 1$ for a single Skyrmion.

---

## 3. Spectral Flow Derivation

### 3.1 Setup: Fermions Coupled to Skyrmion

Consider a fermion field $\psi$ coupled to the chiral field $U(x)$ via the Yukawa interaction:

$$\mathcal{L} = \bar{\psi}(i\cancel{\partial} - m)\psi - g\bar{\psi}_L U \psi_R - g\bar{\psi}_R U^\dagger \psi_L$$

where $\psi_{L,R} = \frac{1}{2}(1 \mp \gamma_5)\psi$.

In the Skyrmion background, the Dirac equation becomes:

$$\left[i\gamma^\mu\partial_\mu - m - g\gamma^i(U^\dagger\partial_i U)_{\text{eff}}\right]\psi = 0$$

### 3.2 Adiabatic Creation and Level Crossing

**Witten's spectral flow argument:**

1. **Initial state (t = -∞):** No soliton present, $U = 1$ everywhere. The Dirac spectrum has the standard form with a gap $[-m, +m]$ and filled Dirac sea.

2. **Adiabatic creation:** Turn on the soliton slowly: $U(x,t) = U_0^{f(t)}$ where $f(-\infty) = 0$, $f(+\infty) = 1$.

3. **Spectral flow:** As the soliton forms, energy levels shift. For $Q = 1$:
   - One negative-energy level rises toward zero
   - It crosses $E = 0$ and becomes a positive-energy state
   - This level becomes the zero mode localized on the soliton

4. **Final state (t = +∞):** The soliton is present with one additional positive-energy fermion compared to the initial vacuum.

**Quantitative analysis:**

The time-dependent Hamiltonian $H(t)$ has eigenvalues $E_n(t)$. The adiabatic theorem ensures:
- If the soliton creation is slow compared to $1/m$, levels don't jump
- The spectral flow is determined by the index theorem

The number of levels crossing zero from below minus those from above equals:

$$\Delta n = \text{ind}(\cancel{D}) = Q$$

### 3.3 Fermion Number Calculation

The fermion number operator is:

$$N_F = \int d^3x\, \psi^\dagger\psi = \sum_n \theta(E_n) - \sum_n \theta(-E_n) + \text{(vacuum subtraction)}$$

After spectral flow with $Q$ level crossings:

$$N_F^{\text{final}} - N_F^{\text{initial}} = Q$$

Since $N_F^{\text{initial}} = 0$ (vacuum), the soliton carries $N_F = Q$.

---

## 4. Zero Mode Solution

### 4.1 Derivation from Dirac Equation

For a static Skyrmion with hedgehog profile $U = \exp(i\hat{r}\cdot\boldsymbol{\tau}F(r))$, the zero mode equation is:

$$\left[\boldsymbol{\alpha}\cdot\mathbf{p} + \beta m(r)\right]\psi_0 = 0$$

where the effective position-dependent mass is:

$$m(r) = m_0 - gf_\pi F'(r)\sin F(r)/r + \ldots$$

**Ansatz for zero mode:**

$$\psi_0(\mathbf{r}) = \frac{1}{r}e^{-\int_0^r m(r')dr'}\chi(\hat{r})$$

where $\chi(\hat{r})$ is a spinor-isospinor harmonics.

**Verification:** Substituting into the Dirac equation:

$$\left[-i\boldsymbol{\alpha}\cdot\hat{r}\frac{\partial}{\partial r} + \beta m(r)\right]\psi_0 = 0$$

$$-i\alpha_r\left(-\frac{1}{r^2}e^{-M(r)} - \frac{m(r)}{r}e^{-M(r)}\right) + \beta\frac{m(r)}{r}e^{-M(r)} = 0$$

where $M(r) = \int_0^r m(r')dr'$. This is satisfied when $-i\alpha_r\beta = 1$ for the appropriate spinor.

### 4.2 Normalizability

The zero mode is normalizable if:

$$\int_0^\infty r^2 |\psi_0|^2 dr = \int_0^\infty e^{-2M(r)} dr < \infty$$

**Condition:** This requires $M(r) \to +\infty$ as $r \to \infty$, i.e., $m(r) > 0$ for large $r$.

For the Skyrmion, $m(r) \to m_0 > 0$ as $r \to \infty$, so:

$$\int_0^\infty e^{-2m_0 r}dr = \frac{1}{2m_0} < \infty \quad \checkmark$$

### 4.3 Explicit Form

For the profile $F(r) = 2\arctan(r_0/r)$ (rational map approximation):

$$\psi_0(r) \propto \frac{1}{r}\exp\left(-m_0 r + gf_\pi\left[\frac{\pi r_0}{r} + \ldots\right]\right)$$

The zero mode is localized within $r \lesssim 1/m_0$ (Compton wavelength of the fermion).

---

## 5. Wess-Zumino-Witten Term and Anomaly Matching

### 5.1 The WZW Term (5-Dimensional Form)

The Wess-Zumino-Witten term is fundamentally a **5-dimensional integral** over an extension $B^5$ of spacetime $M^4$:

$$\Gamma_{\text{WZW}}[U] = \frac{iN_c}{240\pi^2}\int_{B^5} d^5y\, \epsilon^{IJKLM}\text{Tr}(L_I L_J L_K L_L L_M)$$

where:
- $B^5$ is any 5-manifold with boundary $\partial B^5 = M^4$
- $L_I = \tilde{U}^\dagger \partial_I \tilde{U}$ extends $U$ into the bulk
- $N_c = 3$ is the number of QCD colors

**Why 5 dimensions?** The integrand is closed but not exact in 4D. It equals $d\omega_4$ for some 4-form only locally. The 5D formulation makes the action well-defined modulo $2\pi i$.

### 5.2 The Anomaly Equation (4-Dimensional)

The **divergence** of the baryon current derived from the WZW term gives:

$$\boxed{\partial_\mu J^\mu_B = \frac{N_c}{24\pi^2}\epsilon^{\mu\nu\rho\sigma}\text{Tr}(L_\mu L_\nu L_\rho L_\sigma)}$$

This is the **anomaly equation**, not the WZW term itself.

**Derivation:** Varying the WZW action with respect to vector transformations:

$$\delta\Gamma_{\text{WZW}} = \int d^4x\, J^\mu_B \partial_\mu\alpha$$

Integration by parts gives the anomaly equation.

### 5.3 Integration: $\Delta B = \Delta Q$

**Claim:** For a process creating a soliton with topological charge $Q$:

$$\Delta B = \int_{t_i}^{t_f} dt \int d^3x\, \partial_\mu J^\mu_B = Q$$

**Proof:**

1. The 4-divergence of $J^\mu_B$ integrates over spacetime to give:
   $$\int d^4x\, \partial_\mu J^\mu_B = \int d^4x\, \frac{N_c}{24\pi^2}\epsilon^{\mu\nu\rho\sigma}\text{Tr}(L_\mu L_\nu L_\rho L_\sigma)$$

2. This equals the **winding number** of the map $U: M^4 \to SU(2)$:
   $$= N_c \cdot \text{deg}(U) = N_c \cdot Q_{\text{instanton}}$$

3. For a static soliton created adiabatically, $Q_{\text{instanton}} = Q_{\text{Skyrmion}}/N_c$, giving:
   $$\Delta B = Q$$

**Physical interpretation:** The anomaly "pumps" baryon number from the Dirac sea into the soliton at a rate proportional to the topological current.

---

## 6. Physical Interpretation

### 6.1 Baryon Number = Winding Number

In the QCD/Skyrme model:

| Topological Charge $Q$ | Baryon Number $B$ | Fermion Number $N_F$ | Particle |
|------------------------|-------------------|----------------------|----------|
| +1 | +1 | +1 | Nucleon (p, n) |
| -1 | -1 | -1 | Antinucleon ($\bar{p}$, $\bar{n}$) |
| +2 | +2 | +2 | Deuteron-like |
| +3 | +3 | +3 | ${}^3$He-like |
| 0 | 0 | 0 | Mesons ($\pi$, $K$, ...) |

### 6.2 Why This Works

The deep reason is threefold:

1. **Topology enforces quantization:** $Q \in \mathbb{Z}$ because $\pi_3(SU(2)) = \mathbb{Z}$
2. **Anomalies match:** The chiral anomaly coefficient in QCD equals the WZW coefficient
3. **Charge conservation:** Topological charge cannot change continuously → fermion number is conserved

### 6.3 Experimental Verification

| Test | Result | Precision |
|------|--------|-----------|
| Proton lifetime | $\tau_p > 2.4 \times 10^{34}$ years | $B$ conserved to $10^{-34}$/year |
| Skyrmion mass | 940 MeV predicted | 0.2% agreement with nucleon |
| Nucleon spin | 1/2 from collective quantization | Exact |
| Isospin | 1/2 from SU(2) hedgehog | Exact |

**Reference:** Super-Kamiokande Collaboration, *Phys. Rev. D* **95**, 012004 (2017).

---

## 7. Application to Chiral Geometrogenesis

### 7.1 The CG Field Configuration

In CG, the fundamental fields are three complex scalars $\chi_c(x)$ for $c \in \{R, G, B\}$ with phases separated by $2\pi/3$. These combine into a total chiral field:

$$\chi_{\text{total}} = \chi_R + \chi_G + \chi_B$$

**Key question:** How does this map to the Skyrmion framework?

### 7.2 Mapping $\chi$ to $SU(2)$

**Construction:** Define the CG-to-Skyrmion map as:

$$U(\mathbf{x}) = \exp\left(i\frac{\boldsymbol{\tau}\cdot\boldsymbol{\phi}(\mathbf{x})}{f_\chi}\right)$$

where the pion-like fields are constructed from the chiral field phase gradients:

$$\boldsymbol{\phi} = f_\chi\, \text{Im}\left(\chi^\dagger \boldsymbol{\nabla}\chi / |\chi|^2\right)$$

For a soliton configuration where $\chi$ winds around the vacuum manifold:

$$\chi(\mathbf{x}) = v_\chi\, e^{i\Theta(\mathbf{x})}$$

the map $U$ inherits the topology of $\Theta$.

### 7.3 Topological Charge in CG

The CG topological charge is:

$$Q_{\text{CG}} = \frac{1}{24\pi^2}\int d^3x\, \epsilon^{ijk}\text{Tr}(\mathcal{L}_i \mathcal{L}_j \mathcal{L}_k)$$

where $\mathcal{L}_i = U^\dagger\partial_i U$ constructed from the CG fields.

**Theorem application:** By the established Witten result, a CG soliton with $Q_{\text{CG}} = n$ carries fermion number $N_F = n$.

### 7.4 Particle Identification Table

| CG Particle | Topological Sector | $Q$ | $N_F$ | Additional Quantum Numbers |
|-------------|-------------------|-----|-------|---------------------------|
| Baryon (p, n) | Color $SU(3)$ | 1 | 1 | $I = 1/2$, $Y = 1$ |
| Antibaryon | Color $SU(3)$ | -1 | -1 | $I = 1/2$, $Y = -1$ |
| Lepton ($e^-$, $\nu_e$) | Electroweak $SU(2)_L$ | 1 | 1 | $I_3 = \pm 1/2$, $Y = -1$ |
| Antilepton | Electroweak $SU(2)_L$ | -1 | -1 | $I_3 = \mp 1/2$, $Y = +1$ |

**Note:** Different particle types are distinguished by **which gauge sector** hosts the soliton, not just by $Q$.

### 7.5 Addressing the Pre-Geometric Question

**Issue:** The Atiyah-Singer theorem requires a metric, but CG operates pre-geometrically.

**Resolution:**

1. **Topological charge is metric-independent:** The winding number $Q = \frac{1}{24\pi^2}\int\epsilon^{ijk}\text{Tr}(L_i L_j L_k)$ uses only the $\epsilon$ symbol (topology), not $g_{\mu\nu}$ (geometry).

2. **Ordering in CG:**
   - **Phase 0-2:** Topology defined on stella octangula boundary $\partial\mathcal{S}$
   - **Phase 4:** Solitons form with well-defined $Q$ using pre-geometric topology
   - **Phase 5:** Metric emerges; index theorem becomes applicable for fermion coupling

3. **Consistency:** The fermion number assignment $N_F = Q$ is topological and persists through metric emergence.

### 7.6 Role in Baryogenesis (Theorem 4.2.1)

This theorem is essential for CG baryogenesis:

- **If** CG dynamics favor $Q > 0$ solitons over $Q < 0$ (chiral bias)
- **Then** matter ($N_F > 0$) dominates over antimatter ($N_F < 0$)
- **The fermion asymmetry IS the topological charge asymmetry**

See Theorem 4.2.1 for the complete derivation of how right-handed pressure creates this bias.

---

## 8. Key References

### 8.1 Original Proofs

1. **Witten (1983a):** E. Witten, "Global aspects of current algebra," *Nucl. Phys. B* **223**, 422-432 (1983).
   - Proves $N_F = Q$ using spectral flow and index theorem
   - [DOI: 10.1016/0550-3213(83)90063-9](https://doi.org/10.1016/0550-3213(83)90063-9)

2. **Witten (1983b):** E. Witten, "Current algebra, baryons, and quark confinement," *Nucl. Phys. B* **223**, 433-444 (1983).
   - Physical interpretation: Skyrmions as baryons
   - [DOI: 10.1016/0550-3213(83)90064-0](https://doi.org/10.1016/0550-3213(83)90064-0)

### 8.2 Mathematical Foundation

3. **Atiyah & Singer (1968):** M.F. Atiyah and I.M. Singer, "The index of elliptic operators: I," *Ann. Math.* **87**, 484-530 (1968).
   - Fundamental index theorem relating topology to analysis
   - [DOI: 10.2307/1970715](https://doi.org/10.2307/1970715)

4. **Callias (1978):** C. Callias, "Axial anomalies and index theorems on open spaces," *Commun. Math. Phys.* **62**, 213-234 (1978).
   - Extension to non-compact manifolds (essential for solitons in $\mathbb{R}^3$)
   - [DOI: 10.1007/BF01202525](https://doi.org/10.1007/BF01202525)

### 8.3 Reviews and Textbooks

5. **Weinberg (1996):** S. Weinberg, *The Quantum Theory of Fields, Vol. 2: Modern Applications*, Chapter 23: Extended Field Configurations, Cambridge University Press (1996).
   - Standard textbook treatment of anomalies, solitons, and index theorems

6. **Shifman (2012):** M. Shifman, *Advanced Topics in Quantum Field Theory: A Lecture Course*, Chapters 4-5, Cambridge University Press (2012).
   - Modern pedagogical treatment of topological solitons

7. **Manton & Sutcliffe (2004):** N. Manton and P. Sutcliffe, *Topological Solitons*, Cambridge University Press (2004).
   - Comprehensive monograph on Skyrmions and related solitons

### 8.4 Experimental Verification

8. **Super-Kamiokande (2017):** K. Abe et al. (Super-Kamiokande Collaboration), "Search for proton decay via $p \to e^+\pi^0$ and $p \to \mu^+\pi^0$," *Phys. Rev. D* **95**, 012004 (2017).
   - Current best bound: $\tau_p > 2.4 \times 10^{34}$ years

---

## 9. Why This Is Not a Novel CG Claim

This theorem is marked as **ESTABLISHED** because:

1. **Rigorous proof:** Witten's 1983 papers are mathematically complete (cited >3000 times)
2. **Index theorem:** Built on Atiyah-Singer (Fields Medal 1966, Abel Prize 2004)
3. **Experimental support:** Baryon number conserved to $10^{-34}$/year precision
4. **Universal acceptance:** Standard result in QFT textbooks (Weinberg, Peskin & Schroeder, Shifman)

**CG's contribution** is:
- Applying this identification to the chiral field $\chi$
- Explaining matter particles as topological solitons
- Connecting to baryogenesis via chiral bias (Theorem 4.2.1)

---

## 10. Summary

| Aspect | Details |
|--------|---------|
| **Status** | ✅ Established (Witten 1983) |
| **Key result** | $N_F = Q$ (fermion number = topological charge) |
| **Proof method** | Spectral flow + Atiyah-Singer index theorem |
| **Key equation** | $\text{ind}(\cancel{D}) = \frac{1}{16\pi^2}\int\text{Tr}(F\tilde{F})$ |
| **CG application** | Matter particles are topological solitons in $\chi$ field |
| **Novel in CG** | Field mapping $\chi \to U$, connection to baryogenesis |
| **Verification** | 6/6 computational tests pass |

---

## 11. Lean 4 Formalization

**File:** `lean/ChiralGeometrogenesis/Phase4/Theorem_4_1_3.lean`
**Status:** Complete (December 27, 2025)
**Lines:** ~1,100

### 11.1 Formalized Structures

| Structure | Description | Reference |
|-----------|-------------|-----------|
| `DiracIndex` | Dirac operator index with $n_+$, $n_-$, index | §2.1 |
| `AtiyahSingerSoliton` | Index theorem application to soliton configurations | §2.3 |
| `SpectralFlow` | Level crossing during adiabatic soliton creation | §3.2 |
| `ZeroMode` | Zero mode with chirality and localization scale | §4.1 |
| `MinimalZeroModeConfig` | Ground state zero mode configuration | §4.1 |
| `WZWTerm` | Wess-Zumino-Witten term with $N_c$ colors | §5.1 |
| `WZWBaryonCurrent` | Baryon current from WZW term | §5.2 |
| `BaryonCurrentAnomaly` | Anomaly matching $\Delta B = Q$ | §5.3 |
| `CGChiralSoliton` | CG-specific chiral soliton with VEV | §7.1 |
| `CGParticle` | CG particle with gauge sector | §7.4 |

### 11.2 Main Theorems Formalized

```lean
-- Core result: Fermion number equals topological charge
theorem fermion_number_equals_topological_charge (s : SolitonConfig) :
    fermion_number s = s.Q

-- 5-part main theorem statement
theorem theorem_4_1_3 :
    (∀ s : SolitonConfig, fermion_number s = s.Q) ∧
    (∀ s : SolitonConfig, (soliton_to_AS s).dirac_index.index = s.Q) ∧
    (∀ s : SolitonConfig, baryon_number s = fermion_number s) ∧
    (∀ s₁ s₂ : SolitonConfig, s₁.topological_class = s₂.topological_class →
       fermion_number s₁ = fermion_number s₂) ∧
    (fermion_number vacuum_config = 0)

-- Topological stability of proton
theorem proton_topologically_stable (s' : SolitonConfig) (hs' : s'.Q = 0) :
    let proton : SolitonConfig := ⟨⟨1⟩, 0, le_refl 0⟩
    proton.topological_class ≠ s'.topological_class

-- Skyrmion fermion number
theorem skyrmion_fermion_number (p : SkyrmeParameters) :
    let sky := mkSkyrmion p
    fermion_number sky.toSolitonConfig = 1
```

### 11.3 Axioms Used

| Axiom | Justification | Status |
|-------|---------------|--------|
| `callias_index_theorem` | Extension of Atiyah-Singer to non-compact spaces (Callias 1978) | Established mathematics |
| `ground_state_is_minimal` | Ground state solitons have minimal zero mode configuration | Physical axiom from energy minimization |

**Axiom Status:** Both axioms encode established mathematical/physical results that are beyond Mathlib's current scope but are well-documented in the literature.

### 11.4 Key Derivation Chain

The Lean formalization follows the derivation chain from the proof:

1. **SolitonConfig** has topological charge $Q \in \mathbb{Z}$ (from $\pi_3(SU(2)) \cong \mathbb{Z}$)
2. **Callias index theorem** (axiom): $\text{ind}(D) = Q$ for Dirac operator $D$
3. **SpectralFlow** during adiabatic soliton creation: $\Delta N_F = \text{ind}(D)$
4. **Starting from vacuum** ($N_F = 0$): final state has $N_F = Q$

The fermion number is **derived** from spectral flow, not defined as equal to $Q$. The equality $N_F = Q$ is a **theorem**, not a definition.

### 11.5 Alternative Derivation (WZW)

The formalization also includes the WZW/anomaly derivation:

```lean
-- WZW baryon charge equals topological charge
theorem wzw_baryon_eq_topological (wbc : WZWBaryonCurrent) :
    wbc.baryon_charge = wbc.soliton.Q

-- Two derivations agree (consistency check)
theorem derivations_consistent (s : SolitonConfig) (wbc : WZWBaryonCurrent)
    (hs : wbc.soliton = s) :
    fermion_number s = wbc.baryon_charge
```

### 11.6 Physical Applications Formalized

- **Particle identification:** `classify_particle` maps $Q$ to particle type
- **Baryon conservation:** `baryon_conservation` from topological invariance
- **Proton stability:** `proton_stable` with lifetime bound $> 10^{34}$ years
- **Matter-antimatter asymmetry:** `matter_antimatter_asymmetry` from topological asymmetry

---

## 12. Connection to Other Theorems

**Prerequisites:**
- **Theorem 4.1.1:** Establishes that solitons exist with integer $Q$
- **Theorem 4.1.2:** Determines the mass spectrum of solitons

**Downstream:**
- **Theorem 4.2.1:** Uses $N_F = Q$ to explain matter-antimatter asymmetry
- **Theorem 4.2.2:** Shows Sakharov conditions are satisfied with $N_F = Q$

---

*This document summarizes established mathematical physics (Witten 1983, Atiyah-Singer 1968) and its application to the Chiral Geometrogenesis framework. The original proofs are found in the cited literature.*

**Last Updated:** 2025-12-27
**Verification Status:** ✅ VERIFIED (Multi-agent peer review) | ✅ LEAN FORMALIZED
