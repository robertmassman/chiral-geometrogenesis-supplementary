# Multi-Agent Verification Report: Lemma 0.0.XXe-NP

## Nucleation Probability → 1 as N → ∞

**Document:** [Lemma-0.0.XXe-Nucleation-Probability-Proof.md](../supporting/Lemma-0.0.XXe-Nucleation-Probability-Proof.md)

**Date:** 2026-03-11

**Verification Method:** Three independent adversarial agents (Mathematical, Physics, Literature) + computational adversarial script

---

## Overall Verdict: 🔶 PARTIAL — CORRECT LOGIC, NUMERICAL ERRORS REQUIRE CORRECTION

The qualitative theorem (nucleation probability → 1) is **rigorously correct**. The quantitative bounds (Part C) have **correct mathematical form** but contain **numerical errors** in the estimates that propagate through §3. None of the errors affect the theorem's validity or its role in the Proposition 0.0.XXe chain.

| Agent | Verdict | Confidence |
|-------|---------|------------|
| Mathematical | Partial | Medium-High |
| Physics | Partial | Medium-High |
| Literature | Partial | High |
| Computational | 9/12 tests pass | — |

---

## 1. Errors Found (Requiring Correction)

### ERROR 1 (SIGNIFICANT): Theorem Statement vs. Proved Bound Mismatch — Part C

**Location:** §1.2 (line 47) vs. §2.3 Corollary (lines 175–179)

**All three agents flagged this.** The theorem statement gives:

$$N_0(\varepsilon, T) = \frac{3^L \ln(1/\varepsilon)}{r \cdot \lfloor T / \tau_{\text{mix}} \rfloor}$$

But the proof derives:

$$N_0(\varepsilon, T) = \frac{\ln(1/\varepsilon)}{r \cdot q_{\min} \cdot \lfloor T/\tau_{\text{mix}} \rfloor}$$

where $q_{\min} = (1/3 - e^{-3})^L$. Since $q_{\min} \neq 1/3^L$, these differ by a factor of $(1/3^L)/q_{\min} \approx 48.5$ for $L=24$. The theorem statement **underestimates** the required $N_0$ and $T_0$.

**Fix:** State the precise bound with $q_{\min}$ in §1.2, then give the simplified $3^L$ approximation as a clearly-labeled corollary with the correction factor.

### ERROR 2 (MODERATE): Numerical Value of $q_{\min}$ is Wrong

**Location:** §2.3 Remark (line 137), §3.1 table (line 198)

**All three agents independently computed and confirmed:** The claimed $q_{\min} \approx 1.07 \times 10^{-13}$ is incorrect. The actual value:

$$q_{\min} = (1/3 - e^{-3})^{24} = (0.28355)^{24} \approx 7.29 \times 10^{-14}$$

This is **47% smaller** than claimed. All downstream estimates inherit this error:

| Quantity | Claimed | Correct | Error |
|----------|---------|---------|-------|
| $q_{\min}$ | $1.07 \times 10^{-13}$ | $7.29 \times 10^{-14}$ | 47% too large |
| $r \cdot q_{\min}$ | $1.28 \times 10^{-11}$ | $8.75 \times 10^{-12}$ | 46% too large |
| $1/(r \cdot q_{\min})$ | $7.8 \times 10^{10}$ | $1.14 \times 10^{11}$ | 46% too small |
| $N_0(\varepsilon{=}0.01, T{=}10^6)$ | $\sim 1.1 \times 10^{9}$ | $\sim 1.58 \times 10^{9}$ | 44% too small |
| $T_0(\varepsilon{=}0.01, N{=}1666)$ | $\sim 6.5 \times 10^{11}$ | $\sim 9.47 \times 10^{11}$ | 46% too small |

**Impact:** Since these are conservative bounds, the corrected values are *more* conservative (larger $N_0$, larger $T_0$), which actually **strengthens** the gap analysis in §3.2. The ~$10^6$ gap between bound and observation remains.

### ERROR 3 (MODERATE): Correction Factor $(1/0.86)^{24} \approx 27.5$ is Wrong

**Location:** §2.3 Simplified form (line 185)

The exact base is $1 - 3e^{-3} = 0.8506$, not $0.86$. The correction factor:

| Base used | $(1/\text{base})^{24}$ | Claimed |
|-----------|------------------------|---------|
| 0.86 (as written) | 37.3 | 27.5 |
| 0.8506 (exact) | 48.5 | 27.5 |

The claimed 27.5 is wrong by 35–76%.

### ERROR 4 (MODERATE): Hitting Time Bound is Incorrect

**Location:** §2.1, line 77

**Literature agent flagged:** The claim $\mathbb{E}[\tau_A] \leq 1/\pi_{\min}$ is **not a standard result**. The standard result is that the expected *return time* $\mathbb{E}_j[T_j] = 1/\pi(j)$ (an equality, for returns to a single state $j$ starting from $j$). The expected *hitting time* from an arbitrary starting state to a set $A$ can be much larger.

**Impact:** This bound is used only as heuristic motivation in §2.1. The quantitative bound in Part C (§2.3) does not rely on it. The qualitative conclusion $\mathbb{P}(\tau_A < \infty) = 1$ follows from ergodicity alone.

**Fix:** Replace with: "By ergodicity, $\mathbb{E}[\tau_A] < \infty$ for any starting state, so by Markov's inequality, $\mathbb{P}(\tau_A > T) \to 0$ as $T \to \infty$."

### ERROR 5 (MINOR): Incorrect Terminology — "Union Bound"

**Location:** Lemma 2.7, line 149

The proof says probability of matching any replicator is $\geq r \cdot q_{\min}$ "by the union bound." But the union bound gives an **upper** bound $P(\bigcup A_i) \leq \sum P(A_i)$. Since the events {tile $= S_k$} are **mutually exclusive** (a tile is exactly one string), the correct justification is **additivity for disjoint events** (exact sum, not an inequality).

### ERROR 6 (MINOR): Aperiodicity Proof Incomplete

**Location:** Lemma 2.2, line 67

The proof states VM interactions "may" return the system to its current state without demonstrating this for any specific state. A rigorous fix: for any state $\omega$, the VM deterministically produces some $\omega'$. Then mutations revert $\omega' \to \omega$ with probability $(\mu/3)^{d(\omega',\omega)} \cdot (1-\mu)^{LN - d(\omega',\omega)} > 0$. So $P^{(2)}(\omega, \omega) > 0$ for all $\omega$, establishing aperiodicity.

---

## 2. Warnings

### WARNING 1: Selectively Favorable $\gamma_{\text{eff}}$ Calibration (§3.3)

**Physics agent flagged:** The effective search rate $\gamma_{\text{eff}} \approx 1.76$ is calibrated from only the n100 local run ($N=1666$, $T_{\text{emerge}} = 8 \times 10^5$), which the Phase 1 results document identifies as "anomalously fast." Other data points give very different values:

| Run | N | $T_{\text{emerge}}$ | $\gamma_{\text{eff}}$ |
|-----|---|---------------------|----------------------|
| n100 local | 1,666 | $8 \times 10^5$ | 1.76 |
| n100 global | 1,666 | $3.9 \times 10^6$ | 0.36 |
| n157 local | 4,108 | $9.65 \times 10^6$ | 0.059 |
| 1D soup | 4,096 | $3.5 \times 10^6$ | 0.16 |

$\gamma_{\text{eff}}$ spans a 30× range. Presenting only the highest value as "approaching the theoretical maximum of 2" is misleading.

**Recommendation:** Present $\gamma_{\text{eff}}$ as a range (0.06–1.8) calibrated against all runs.

### WARNING 2: Product Bound Needs Explicit Conditioning

**Math agent flagged:** The bound $(1 - r \cdot q_{\min})^{KN}$ takes a product over $K$ windows and $N$ tiles. The correct justification is iterated conditional expectations: for each window/tile, condition on all history up to that point. The proof correctly avoids claiming independence but should state the conditioning argument explicitly.

### WARNING 3: Larger-N Slowdown Based on 2 Data Points (§3.4)

**Physics agent flagged:** The claim rests on exactly two data points, one of which is anomalous. The analogy to the Eigen error threshold is qualitative, not formal. Additional runs at intermediate $N$ values are needed to confirm the scaling.

---

## 3. Verified Claims

The following were independently verified by multiple agents:

| Claim | Agents Verifying | Status |
|-------|-----------------|--------|
| Irreducibility (Lemma 2.1) | Math, Physics | ✅ Correct |
| Single-trit mixing formula (Lemma 2.5) | Math, Literature, Computational | ✅ Correct |
| Mixing time bound $(1-\mu)^{3/\mu} \leq e^{-3}$ | Math, Computational | ✅ Correct |
| Static nucleation bound $(1-r/3^L)^N \leq e^{-rN/3^L}$ (Lemma 2.4) | Math, Literature, Computational | ✅ Correct |
| Shadow process stochastic domination | Math, Physics, Literature | ✅ Correct |
| $\gamma_{\text{eff}}$ calculation (arithmetic) | Physics, Computational | ✅ Correct |
| Core-tail decomposition ($r = 4 \times 30 = 120$) | Computational | ✅ Correct |
| Proto-replicator estimates ($p_{\text{proto}}, \mathbb{E}[\text{proto}]$) | Computational | ✅ Correct |
| All 8 limiting cases | Physics, Computational | ✅ Correct |
| Mutation-only bound shows no N-slowdown | Computational | ✅ Correct |
| Monte Carlo shadow process confirms bound is conservative | Computational | ✅ Confirmed |
| Framework consistency with Prop 0.0.XXe chain | Physics | ✅ Consistent |

---

## 4. Limiting Case Checks

| Limit | Expected | Result | Status |
|-------|----------|--------|--------|
| $\mu \to 0$ | $T_0 \to \infty$ | $\tau_{\text{mix}} \to \infty$, bound diverges | ✅ PASS |
| $\mu \to 1$ | Rapid nucleation | $\tau_{\text{mix}} = 3$, minimal bounds | ✅ PASS |
| $N \to \infty$ (fixed $T$) | $P \to 1$ | $(1 - r \cdot q_{\min})^{KN} \to 0$ | ✅ PASS |
| $T \to \infty$ (fixed $N$) | $P \to 1$ | $K \to \infty$, bound → 0 | ✅ PASS |
| $r \to 0$ | $P \to 0$ | $(1-0)^{KN} = 1$, so $P = 0$ | ✅ PASS |
| $L \to \infty$ | Exponentially harder | $q_{\min} \to 0$ exponentially | ✅ PASS |
| $N = 1$ | Slow but certain | Correct bound | ✅ PASS |
| $\mu = 0$ | Ergodicity fails | Proof requires $\mu > 0$ | ✅ PASS |

---

## 5. Missing References

| Reference | Relevance | Priority |
|-----------|-----------|----------|
| Aronson & Weinberger (1978) | Original Fisher-KPP hair trigger result | High |
| Kauffman (1993) *The Origins of Order* | Phase transition for autocatalytic set emergence | High |
| Nowak (2006) *Evolutionary Dynamics* | Standard reference for mutation-selection | Medium |
| Ray (1992) Tierra; Ofria et al. Avida | Closest alife precedents (both seeded, unlike this lemma) | Medium |
| Levin & Peres (2017) 2nd edition | Update from 1st edition citation | Low |
| Aizenman & Lebowitz (1988) | Bootstrap percolation analogy | Low |

---

## 6. Computational Verification

**Script:** [lemma_0_0_XXe_NP_adversarial_verification.py](../../../verification/supporting/lemma_0_0_XXe_NP_adversarial_verification.py)

**Plots:**
- [lemma_0_0_XXe_NP_adversarial_verification.png](../../../verification/plots/lemma_0_0_XXe_NP_adversarial_verification.png) — Single-trit mixing, nucleation vs N, MC histogram, N₀ vs L
- [lemma_0_0_XXe_NP_bounds_comparison.png](../../../verification/plots/lemma_0_0_XXe_NP_bounds_comparison.png) — Bound vs observed, γ_eff comparison

**Results:** 9/12 tests passed. Three failures all trace to numerical errors in the proof:
1. $q_{\min}$ value (claimed $1.07 \times 10^{-13}$, actual $7.29 \times 10^{-14}$)
2. $N_0, T_0$ estimates (propagated from $q_{\min}$ error)
3. $(1/0.86)^{24}$ correction factor (claimed 27.5, actual 48.5)

**Monte Carlo validation:** Shadow process simulation (L=8, r=5, N=100, μ=0.1) showed 98% nucleation rate in 200 trials, confirming the analytical bound (64.8%) is conservative. ✅

---

## 7. Recommendations (Priority Order)

1. **Fix $q_{\min}$ and all derived numerical values** — Root cause of 5 cascading errors
2. **Reconcile theorem statement (§1.2C) with proof (§2.3)** — Use $q_{\min}$ in statement, give simplified form as labeled approximation
3. **Fix hitting time bound** (§2.1 line 77) — Replace $\mathbb{E}[\tau_A] \leq 1/\pi_{\min}$ with correct ergodicity argument
4. **Fix $(1/0.86)^{24}$ correction factor** — Use correct base 0.8506, correct value ~48.5
5. **Fix "union bound" terminology** (Lemma 2.7) → "additivity for disjoint events"
6. **Tighten aperiodicity proof** (Lemma 2.2) — Add two-step return argument
7. **Present $\gamma_{\text{eff}}$ as a range** — Use all available data points, note anomalous n100 run
8. **Add missing references** — Especially Kauffman (1993), Aronson & Weinberger (1978)
9. **Add iterated conditioning sentence** to product bound justification
10. **Add caveat on larger-N slowdown** — Only 2 data points

---

## 8. Conclusion

**The core theorem is mathematically sound.** Nucleation inevitability (both qualitative and quantitative) is correctly established via standard Markov chain ergodicity and a valid mutation-coupling argument. The proof structure — shadow process stochastic domination over VM interactions — is a novel and correct application of standard techniques.

**Six errors require correction**, all in peripheral elements (numerical estimates, terminology, a non-load-bearing hitting time bound, aperiodicity presentation). None affect the theorem's logical validity or its role in the emergence chain:

$$\text{Random Z}_3 \text{ soup} \xrightarrow{\text{nucleation (this lemma)}} \rho_0 > 0 \xrightarrow{\text{hair trigger (Fisher-KPP)}} \rho^*$$

After corrections, this lemma can be marked **🔶 NOVEL ✅ VERIFIED**.
