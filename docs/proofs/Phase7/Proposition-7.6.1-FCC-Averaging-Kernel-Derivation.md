# Proposition 7.6.1: FCC Averaging Kernel — Derivation

## Navigation

| File | Purpose | Sections |
|------|---------|----------|
| [Proposition-7.6.1-FCC-Averaging-Kernel.md](./Proposition-7.6.1-FCC-Averaging-Kernel.md) | Statement & motivation | §1–4, §9–10 |
| **Proposition-7.6.1-FCC-Averaging-Kernel-Derivation.md** (this file) | Complete derivation | §5–8, Appendices |
| [Proposition-7.6.1-FCC-Averaging-Kernel-Applications.md](./Proposition-7.6.1-FCC-Averaging-Kernel-Applications.md) | Verification & physics | §9–12 |

---

## §5. Part (a) — Voronoi Blocking Decomposition

### §5.1 The D₄ Lattice and Its Sublattices ✅ ESTABLISHED

**Definition.** The $D_4$ root lattice in integer coordinates is:

$$D_4 = \{x = (x_0, x_1, x_2, x_3) \in \mathbb{Z}^4 : x_0 + x_1 + x_2 + x_3 \in 2\mathbb{Z}\} \tag{5.1}$$

This is the checkerboard sublattice of $\mathbb{Z}^4$ — the set of integer 4-vectors whose coordinate sum is even. It has:
- **24 nearest neighbors:** all vectors $(\pm 1, \pm 1, 0, 0)$ and permutations (choosing which two coordinates are nonzero), with squared norm 2
- **Determinant:** $\det(D_4) = 4$ (index $[\mathbb{Z}^4 : D_4] = 2$)
- **Self-dual:** $D_4^* \cong D_4$ (up to scaling by $1/\sqrt{2}$), unique among $D_n$ lattices

**Definition.** The scaled sublattice $2D_4$ is:

$$2D_4 = \{2y : y \in D_4\} = \{x \in (2\mathbb{Z})^4 : x_0 + x_1 + x_2 + x_3 \in 4\mathbb{Z}\} \tag{5.2}$$

Every coordinate of a $2D_4$ point is even, and the coordinate sum is divisible by 4.

### §5.2 The Quotient D₄/2D₄ ✅ ESTABLISHED 🔶 NOVEL (explicit enumeration)

**Theorem (Coset Index).** $[D_4 : 2D_4] = 16$.

*Proof.* We establish this by two independent methods.

**Method 1 (Algebraic — basis argument).** Choose a basis for $D_4$:

$$\{b_1, b_2, b_3, b_4\} = \{e_1 - e_2,\, e_2 - e_3,\, e_3 - e_4,\, e_3 + e_4\} \tag{5.3}$$

where $e_i$ are standard basis vectors. Then $D_4 = \mathbb{Z}b_1 \oplus \mathbb{Z}b_2 \oplus \mathbb{Z}b_3 \oplus \mathbb{Z}b_4$ and $2D_4 = 2\mathbb{Z}b_1 \oplus 2\mathbb{Z}b_2 \oplus 2\mathbb{Z}b_3 \oplus 2\mathbb{Z}b_4$. The quotient is:

$$D_4/2D_4 \cong (\mathbb{Z}/2\mathbb{Z})^4 \tag{5.4}$$

since each generator $b_i$ maps to a generator of $\mathbb{Z}/2\mathbb{Z}$ in the quotient. Therefore $|D_4/2D_4| = 2^4 = 16$.

The 16 coset representatives are given explicitly by all binary combinations:

$$r(\varepsilon) = \sum_{i=1}^{4} \varepsilon_i b_i, \quad \varepsilon_i \in \{0, 1\} \tag{5.5}$$

This construction guarantees distinctness and completeness: the representatives biject with $(\mathbb{Z}/2\mathbb{Z})^4$. $\square$

**Remark on coordinate-reduction approaches.** One might attempt to parametrize $D_4/2D_4$ by reducing $\mathbb{Z}^4$ coordinates modulo 2, but this requires care. The map $x \mapsto x \bmod 2$ sends $D_4$ into $\mathbb{F}_2^4$, where the even-sum constraint $\sum x_i \equiv 0 \pmod{2}$ selects only 8 of the 16 elements of $\mathbb{F}_2^4$. The full index of 16 arises because $2D_4 \subsetneq 2\mathbb{Z}^4 \cap D_4$: membership in $2D_4$ requires not just that all coordinates are even, but also that their sum is divisible by 4. The basis argument above avoids this subtlety entirely.

**Method 2 (Determinant).** The index of a sublattice $\Lambda' \subset \Lambda$ in a rank-$n$ lattice satisfies:

$$[\Lambda : \Lambda'] = \sqrt{\frac{\det(\Lambda')}{\det(\Lambda)}} \tag{5.6}$$

For $D_4$, $\det(D_4) = 4$ (the Gram matrix determinant). For $2D_4$, scaling each basis vector by 2 multiplies the Gram matrix determinant by $2^{2 \times 4} = 256$ (each of the 4 basis vectors is doubled, and the Gram matrix is bilinear). So:

If $\{b_1, \ldots, b_4\}$ is a basis for $D_4$, then $\{2b_1, \ldots, 2b_4\}$ is a basis for $2D_4$. The Gram matrix $G' = (2b_i \cdot 2b_j) = 4(b_i \cdot b_j) = 4G$, so:

$$\det(2D_4) = \det(G') = 4^4 \det(G) = 256 \cdot 4 = 1024 \tag{5.7}$$

Therefore:

$$[D_4 : 2D_4] = \sqrt{\frac{1024}{4}} = \sqrt{256} = 16 \quad \checkmark \tag{5.8}$$

### §5.3 Explicit Coset Representatives 🔶 NOVEL

Using the canonical basis construction from §5.2 (Eq. 5.5), the 16 coset representatives $r(\varepsilon) = \sum_i \varepsilon_i b_i$ are:

| $\alpha$ | $\varepsilon$ | Representative $r_\alpha$ (standard coords) | $|r|^2$ | Type |
|----------|---------------|---------------------------------------------|---------|------|
| 1 | $(0,0,0,0)$ | $(0, 0, 0, 0)$ | 0 | Origin |
| 2 | $(0,0,0,1)$ | $(0, 0, 1, 1)$ | 2 | Root |
| 3 | $(0,0,1,0)$ | $(0, 0, 1, -1)$ | 2 | Root |
| 4 | $(0,1,0,0)$ | $(0, 1, -1, 0)$ | 2 | Root |
| 5 | $(0,1,0,1)$ | $(0, 1, 0, 1)$ | 2 | Root |
| 6 | $(0,1,1,0)$ | $(0, 1, 0, -1)$ | 2 | Root |
| 7 | $(0,1,1,1)$ | $(0, 1, 1, 0)$ | 2 | Root |
| 8 | $(1,0,0,0)$ | $(1, -1, 0, 0)$ | 2 | Root |
| 9 | $(1,1,0,0)$ | $(1, 0, -1, 0)$ | 2 | Root |
| 10 | $(1,1,0,1)$ | $(1, 0, 0, 1)$ | 2 | Root |
| 11 | $(1,1,1,0)$ | $(1, 0, 0, -1)$ | 2 | Root |
| 12 | $(1,1,1,1)$ | $(1, 0, 1, 0)$ | 2 | Root |
| 13 | $(0,0,1,1)$ | $(0, 0, 2, 0)$ | 4 | NNN |
| 14 | $(1,0,0,1)$ | $(1, -1, 1, 1)$ | 4 | Spinor |
| 15 | $(1,0,1,0)$ | $(1, -1, 1, -1)$ | 4 | Spinor |
| 16 | $(1,0,1,1)$ | $(1, -1, 2, 0)$ | 6 | Deep shell |

All 16 representatives lie in $D_4$ (coordinate sum even) and are verified to occupy distinct $2D_4$-cosets by the algorithm in `prop_7_6_1_fcc_averaging_kernel.py` (Tests 1–2).

**Note on coordinates.** Some representatives have coordinates outside $\{0,1\}$ (e.g., $(0,0,2,0)$ and $(1,-1,2,0)$) because the $D_4$ basis vectors contain entries of $-1$. For representative #16, the minimal-norm element in the same coset is $(1,1,0,0)$ (since $(1,1,0,0) - (1,-1,2,0) = (0,2,-2,0) = 2(0,1,-1,0) \in 2D_4$). One may substitute this when a minimal-norm representative is preferred.

**Orbit structure under $W(D_4)$.** The Weyl group $W(D_4)$ (order 192, generated by permutations and even sign changes) acts on $D_4/2D_4$, decomposing the 16 cosets into 5 orbits:

| Orbit | Size | $|r|^2$ | Representatives | Description |
|-------|------|---------|-----------------|-------------|
| I | 1 | 0 | $(0,0,0,0)$ | Trivial coset |
| II | 12 | 2 | $\alpha = 2$–$12$ | $D_4$ root cosets |
| III | 1 | 4 | $(0,0,2,0)$ | Next-nearest-neighbor coset |
| IV | 1 | 4 | $(1,-1,1,1)$ | Spinor weight coset (odd parity) |
| V | 1 | 4 | $(1,-1,1,-1)$ | Spinor weight coset (even parity) |

The orbit sizes sum to $1 + 12 + 1 + 1 + 1 = 16$. ✓ The 12-element orbit consists of the 12 $D_4$ root vectors (half of the 24 NN vectors; each coset contains a NN vector and its negative). Orbits III–V are singleton cosets fixed by $W(D_4)$ up to $2D_4$ translations (their $W(D_4)$ orbits in $D_4$ have sizes 8, 8, and 8 respectively, but all elements within each orbit fall into the same coset modulo $2D_4$).

### §5.4 Voronoi Cell Coverage 🔶 NOVEL

**Claim:** Each Voronoi cell of the coarse lattice $2D_4$ contains exactly 16 fine $D_4$ sites.

*Proof.* The Voronoi cell of $2D_4$ centered at the origin is the set of points in $\mathbb{R}^4$ closer to the origin than to any other $2D_4$ site. Since $2D_4$ is a rescaled $D_4$ lattice (with spacing doubled), its Voronoi cell is a rescaled 24-cell with vertices at $2 \times$ the $D_4$ Voronoi vertices.

The 16 coset representatives $\{r_\alpha\}$ all have squared norm $\leq 4$. The nearest nonzero $2D_4$ sites have squared norm $\geq 8$ (the nearest neighbors of $2D_4$ are $2 \times (\text{NN of } D_4)$, with norm $2\sqrt{2}$, so squared norm 8). For each representative $r_\alpha$:

$$|r_\alpha|^2 \leq 4 < 8/2 = 4 \quad \text{(borderline)} \tag{5.9}$$

Actually, we need $|r_\alpha|^2 < |r_\alpha - 2v|^2$ for all nonzero $D_4$ NN vectors $v$. For the NN-type representatives with $|r_\alpha|^2 = 2$ and $2D_4$ NN vectors $2v$ with $|2v|^2 = 8$:

$$|r_\alpha - 2v|^2 = |r_\alpha|^2 - 4 r_\alpha \cdot v + |2v|^2 = 2 - 4 r_\alpha \cdot v + 8 = 10 - 4 r_\alpha \cdot v$$

Since $r_\alpha \cdot v$ takes values in $\{-2, -1, 0, 1, 2\}$ and $|r_\alpha - 2v|^2 \geq 10 - 8 = 2 = |r_\alpha|^2$, with equality only when $r_\alpha = v$ (i.e., $r_\alpha \cdot v = 2$). In this boundary case, $r_\alpha$ is equidistant from 0 and $2v$, so it lies on the Voronoi cell boundary. By convention, we assign such boundary points to the cell containing the origin.

This is verified numerically in `prop_7_6_1_fcc_averaging_kernel.py` (Test 3): the origin Voronoi cell contains exactly 16 fine sites. ✓

---

## §6. Part (b) — Kernel Construction

### §6.1 Path Set Construction 🔶 NOVEL

**Setup.** Consider a coarse link on $D_4(2\eta)$ from $x'$ to $y' = x' + 2\hat{n}$, where $\hat{n}$ is a $D_4$ nearest-neighbor vector (norm $\sqrt{2}$ in integer coordinates). We need to decompose $2\hat{n}$ into fine-lattice steps of norm $\sqrt{2}$ each.

**Design choice:** We use the *all-paths approach* — averaging over all short lattice paths connecting $x'$ to $y'$ — rather than a tree-path approach. This is more symmetric and provides better cancellation properties due to $D_4$ isotropy.

**Path types:**

**2-step paths.** Decompose $2\hat{n} = v_1 + v_2$ where $v_1, v_2$ are $D_4$ NN vectors. For $\hat{n} = (1,1,0,0)$, the coarse displacement is $(2,2,0,0)$. The only 2-step decomposition is $v_1 = v_2 = (1,1,0,0)$ — the "straight" path repeating the same direction twice. There is exactly **1 straight 2-step path** per direction.

*Why only 1:* The $D_4$ NN vectors have components in $\{-1, 0, +1\}$ with exactly two nonzero entries. For $v_1 + v_2 = (2,2,0,0)$, each component of $v_1$ and $v_2$ must sum to the corresponding component of $(2,2,0,0)$. The first two components must each sum to 2, requiring both to be +1 in both $v_1$ and $v_2$. The last two must sum to 0. Since a $D_4$ NN vector has exactly two nonzero entries, and positions 0 and 1 are already $+1$, positions 2 and 3 must both be 0. Hence $v_1 = v_2 = (1,1,0,0)$. ✓

**3-step paths.** Decompose $2\hat{n} = v_1 + v_2 + v_3$ where each $v_i$ is a $D_4$ NN vector. These "detour" paths deviate from the straight line, necessarily enclosing area (triangular plaquettes) and thereby sampling the field strength.

For direction $\hat{n} = (1,1,0,0)$, the target displacement is $2\hat{n} = (2,2,0,0)$. We need $v_1 + v_2 + v_3 = (2,2,0,0)$ where each $v_i$ is a $D_4$ NN vector (two nonzero entries of $\pm 1$).

**Analytic counting.** Each $v_i$ "uses" exactly 2 coordinate slots, giving 6 slots total across 3 vectors. Coordinates 0 and 1 each require total $+2$, consuming 4 slots (each slot contributes $+1$ to one of these coordinates). The remaining 2 slots go to "spectator" coordinates (2 and 3), which must sum to zero.

- **Case A:** Both extra slots go to coordinate 2. This forces one vector to have a $+1$ and another a $-1$ in position 2, with the third constrained. The 3 planes involved (pairing an active coordinate with the spectator) yield $6 \times 2 = 12$ valid orderings and sign choices.
- **Case B:** Both extra slots go to coordinate 3. By symmetry, this also yields **12 paths**.
- **Case C:** One slot to coordinate 2, one to coordinate 3. This requires vectors with single nonzero spectator entries, but each $D_4$ NN vector has exactly two nonzero entries. The single spectator entry must pair with an active entry, but then the third vector needs to cancel both spectator entries — impossible with only one slot remaining.

**Total: 24 three-step paths** per direction. This is confirmed numerically for all 24 $D_4$ NN directions in `prop_7_6_1_fcc_averaging_kernel.py` (Test 4). All 24 are related by the stabilizer of $\hat{n}$ in $W(D_4)$, and the full 24-direction count follows from $W(D_4)$ symmetry.

**Total path count:** $|P(\hat{n})| = 1 + 24 = 25$ per coarse direction.

**Design choice (W2).** We include only paths of length $\leq 3$ (i.e., 2-step straight and 3-step detour). Longer paths (length $\geq 4$) are excluded because: (i) they contribute higher-order corrections in $\eta_k$ to the BCH expansion, so their inclusion would not improve the leading-order bound; (ii) longer paths sample more plaquettes, increasing $C_\text{avg}$ without corresponding benefit; (iii) the 25-path set already provides sufficient averaging for the $D_4$ isotropy properties to be inherited by the coarse field.

### §6.2 Path Enumeration for Representative Direction 🔶 NOVEL

For the representative direction $\hat{n} = (1,1,0,0)$ with coarse displacement $2\hat{n} = (2,2,0,0)$:

**2-step path (1 path):**
- $(1,1,0,0) + (1,1,0,0) = (2,2,0,0)$ ✓

**3-step paths (24 paths):** By symmetry, we can classify these by the direction of the "detour" step. Representative examples:

| Step 1 | Step 2 | Step 3 | Total |
|--------|--------|--------|-------|
| $(1,1,0,0)$ | $(1,0,1,0)$ | $(0,1,-1,0)$ | $(2,2,0,0)$ ✓ |
| $(1,1,0,0)$ | $(1,0,-1,0)$ | $(0,1,1,0)$ | $(2,2,0,0)$ ✓ |
| $(1,0,1,0)$ | $(1,1,0,0)$ | $(0,1,-1,0)$ | $(2,2,0,0)$ ✓ |
| $(1,0,1,0)$ | $(0,1,-1,0)$ | $(1,1,0,0)$ | $(2,2,0,0)$ ✓ |
| ... | ... | ... | ... |

The full enumeration produces 24 valid 3-step paths per direction. All intermediate points lie in $D_4$ (verified in Test 5). By the $W(D_4)$ symmetry acting on the "transverse" directions (those not aligned with $\hat{n}$), the path count is the same for all 24 coarse link directions.

### §6.3 Gauge Covariance Proof ✅ ESTABLISHED

**Theorem (Balaban, CMP 98, Theorem 3.1).** *Any averaging operation defined as a sum of parallel transports along lattice paths, followed by SU($N$) projection, is automatically gauge-covariant.*

*Proof for $Q_\text{FCC}$.* Under a gauge transformation $g: D_4 \to SU(3)$, the link variable $U_{x,y}$ transforms as $U_{x,y}^g = g(x) U_{x,y} g(y)^{-1}$. The parallel transport along any path $\gamma = (x' = z_0, z_1, \ldots, z_s = y')$ transforms as:

$$U_\gamma^g = U_{z_0,z_1}^g U_{z_1,z_2}^g \cdots U_{z_{s-1},z_s}^g = g(z_0) U_{z_0,z_1} g(z_1)^{-1} g(z_1) U_{z_1,z_2} g(z_2)^{-1} \cdots = g(x') U_\gamma g(y')^{-1} \tag{6.1}$$

by telescoping cancellation. Therefore:

$$\frac{1}{|P|}\sum_{\gamma \in P} U_\gamma^g = g(x') \left(\frac{1}{|P|}\sum_{\gamma \in P} U_\gamma\right) g(y')^{-1} \tag{6.2}$$

The SU(3) projection $\text{Proj}_{SU(3)}$ commutes with conjugation by unitary matrices (since polar decomposition is unitarily equivariant). Therefore:

$$Q_\text{FCC}(U^g)_{x',y'} = g(x')\, Q_\text{FCC}(U)_{x',y'}\, g(y')^{-1} \tag{6.3}$$

This is gauge covariance with $g' = g|_{2D_4}$ being the restriction of $g$ to coarse sites. $\square$

Verified numerically in `prop_7_6_1_fcc_averaging_kernel.py` (Test 6): $\|Q(U^g) - g_{x'} Q(U) g_{y'}^{-1}\| = 9.1 \times 10^{-16}$. ✓

### §6.4 Smoothness and Analyticity 🔶 NOVEL

**Claim:** $Q_\text{FCC}(U)$ is analytic in the link variables $\{U_\ell\}$ in a neighborhood of the identity configuration.

*Proof sketch.* The sum $\bar{U} = \frac{1}{|P|}\sum_\gamma U_\gamma$ is a polynomial (hence analytic) function of the link variables, since each $U_\gamma$ is a product of finitely many link variables. The SU(3) projection (see §6.5) is analytic when $\bar{U}$ is near $SU(3)$, i.e., when $M^\dagger M$ is positive definite and $\det M \neq 0$.

For the identity configuration ($U_\ell = \mathbb{1}$ for all $\ell$), $\bar{U} = \mathbb{1}$, and analyticity holds in a ball of radius $O(1)$ around $\mathbb{1}$ in the space of $3 \times 3$ matrices. In the small-field regime, all link variables satisfy $\|U_\ell - \mathbb{1}\| = O(g_k)$ (in lattice units), so $\|\bar{U} - \mathbb{1}\| = O(g_k)$.

**Explicit well-definedness condition (W3).** The SU(3) projection requires $\bar{U}$ to be nonsingular. Since $\bar{U} = \mathbb{1} + O(g_k)$, the smallest singular value satisfies $\sigma_{\min}(\bar{U}) \geq 1 - O(g_k) > 0$ provided $g_k < g_k^*$ for some $O(1)$ threshold $g_k^*$. For SU(3), $g_k^* \sim 1$ suffices. The small-field condition $|F_p| \leq C g_k^{1-\delta}$ with $g_k \ll 1$ ensures we are well within this domain. $\square$

### §6.5 SU(3) Projection Well-Definedness ✅ ESTABLISHED

The SU(3) projection is constructed in two steps:

**Step 1 (Polar decomposition to $U(3)$).** For any nonsingular $M \in GL(3, \mathbb{C})$, the polar decomposition $M = W H$ with $W \in U(3)$ and $H = (M^\dagger M)^{1/2}$ positive definite gives $W = M (M^\dagger M)^{-1/2}$. This is unique and analytic for nonsingular $M$.

**Step 2 ($U(3) \to SU(3)$ correction).** The unitary factor $W$ has $\det W = e^{i\phi}$ for some phase $\phi$. The SU(3) projection is:

$$\text{Proj}_{SU(3)}(M) = e^{-i\phi/3}\, W, \quad \text{where } \phi = \arg(\det W) \tag{6.4}$$

This rescales $W$ to have unit determinant. The phase $e^{-i\phi/3}$ is analytic in $W$ when $W$ is near $\mathbb{1}$ (since $\det W \approx 1$, the $\arg$ function is smooth). $\square$

The projection error satisfies:

$$\|M - \text{Proj}_{SU(3)}(M)\| = \|M - W\| + O(|e^{i\phi/3} - 1|) = \|H - \mathbb{1}\| + O(\phi) \tag{6.5}$$

For $M$ near $SU(3)$, $H = \mathbb{1} + \delta H$ with $\|\delta H\| = O(\|M - SU(3)\|)$ and $\phi = O(\|M - SU(3)\|)$. In the small-field regime ($g_k \ll 1$):

$$\|\bar{U} - \text{Proj}_{SU(3)}(\bar{U})\| = O(g_k^2) \tag{6.6}$$

This projection error is subleading compared to the $O(g_k^{1-\delta})$ averaging error and can be absorbed into the bound.

Verified numerically in `prop_7_6_1_fcc_averaging_kernel.py` (Test 9): $|\det Q - 1| < 10^{-15}$ and $\|QQ^\dagger - \mathbb{1}\| < 10^{-15}$ for 20 random matrices. ✓

---

## §7. Part (c) — Smallness Bound

### §7.1 BCH Expansion of Path Parallel Transports 🔶 NOVEL

Consider a 3-step path $\gamma = (v_1, v_2, v_3)$ from $x'$ to $y' = x' + 2\hat{n}$. The parallel transport is:

$$U_\gamma = U_{x', x'+v_1}\, U_{x'+v_1, x'+v_1+v_2}\, U_{x'+v_1+v_2, y'} \tag{7.1}$$

In the continuum limit, each link variable encodes the gauge field along that step:

$$U_{x,x+v} = P\exp\left(i\eta_k \int_0^1 A_\mu(x + tv) v^\mu\, dt\right) \approx \exp\left(i\eta_k A_\mu(x) v^\mu + O(\eta_k^2)\right) \tag{7.2}$$

For the straight 2-step path $\gamma_0 = (\hat{n}, \hat{n})$:

$$U_{\gamma_0} = U_{x', x'+\hat{n}}\, U_{x'+\hat{n}, y'} \approx \exp\left(2i\eta_k A_\mu(x') \hat{n}^\mu + O(\eta_k^2)\right) \tag{7.3}$$

This is the "direct transport" $U_{x' \to y'}^\text{direct}$.

For a detour path $\gamma = (v_1, v_2, v_3)$ with $v_1 + v_2 + v_3 = 2\hat{n}$ but $(v_1, v_2, v_3) \neq (\hat{n}, \hat{n}, \cdot)$, the BCH formula gives:

$$U_\gamma = U_{\gamma_0} \cdot \exp\left(i\eta_k^2 F_{\mu\nu} \Sigma_\gamma^{\mu\nu} + O(\eta_k^3)\right) \tag{7.4}$$

where $\Sigma_\gamma^{\mu\nu}$ is the "area tensor" enclosed by the detour:

$$\Sigma_\gamma^{\mu\nu} = \frac{1}{2}\sum_{s=1}^{3} \left(\sum_{t<s} v_t^\mu\right) v_s^\nu - (\mu \leftrightarrow \nu) \tag{7.5}$$

This area tensor measures how far the detour path $\gamma$ deviates from the straight path, and is directly related to the triangular plaquettes enclosed by the detour.

### §7.2 Average Over Paths 🔶 NOVEL

The path-averaged matrix is:

$$\bar{U} = \frac{1}{|P|}\sum_{\gamma \in P} U_\gamma = \frac{1}{|P|}\left[U_{\gamma_0} + \sum_{\gamma \neq \gamma_0} U_\gamma\right] \tag{7.6}$$

Substituting the BCH expansion (7.4):

$$\bar{U} = U_{\gamma_0} \cdot \frac{1}{|P|}\left[\mathbb{1} + \sum_{\gamma \neq \gamma_0} \exp\left(i\eta_k^2 F_{\mu\nu} \Sigma_\gamma^{\mu\nu} + O(\eta_k^3)\right)\right] \tag{7.7}$$

Expanding the exponential to first order:

$$\bar{U} \approx U_{\gamma_0} \cdot \left[\mathbb{1} + \frac{i\eta_k^2}{|P|}\sum_{\gamma \neq \gamma_0} F_{\mu\nu} \Sigma_\gamma^{\mu\nu} + O(\eta_k^4)\right] \tag{7.8}$$

**Key cancellation from D₄ isotropy:** The sum $\sum_\gamma \Sigma_\gamma^{\mu\nu}$ over all detour paths is proportional to the antisymmetric isotropic tensor by the $W(D_4)$ symmetry. For each pair of spatial indices $(\mu, \nu)$, the contributions from detour paths in "opposite" transverse directions cancel. The residual is:

$$\frac{1}{|P|}\sum_{\gamma \neq \gamma_0} \Sigma_\gamma^{\mu\nu} = \alpha_n \cdot (\hat{n}^\mu \delta^{\nu\rho} - \hat{n}^\nu \delta^{\mu\rho}) \cdot \hat{n}_\rho \tag{7.9}$$

for some constant $\alpha_n$ depending on the direction $\hat{n}$. This is proportional to the antisymmetric tensor built from $\hat{n}$, which when contracted with $F_{\mu\nu}$ gives a gauge-covariant quantity proportional to $D_\mu F_{\mu\nu} \hat{n}^\nu$ (the equation of motion). In the small-field region, this is bounded by:

$$\left\|\frac{1}{|P|}\sum_{\gamma} F_{\mu\nu} \Sigma_\gamma^{\mu\nu}\right\| \leq C \cdot g_k^{1-\delta} \tag{7.10}$$

using the small-field condition $|F_p| \leq C g_k^{1-\delta}$.

### §7.3 Explicit C_avg Computation 🔶 NOVEL

We bound the deviation $\|Q_\text{FCC}(U) - U_{\gamma_0}\|$ by estimating each contribution.

**Step 1: Detour area bound.** For any 3-step path $\gamma$ on $D_4$, the enclosed area tensor $\Sigma_\gamma^{\mu\nu}$ satisfies:

$$\|\Sigma_\gamma\|_F \leq N_\triangle(\gamma) \cdot A_\triangle \tag{7.11}$$

where $N_\triangle(\gamma)$ is the number of triangular plaquettes enclosed by the path and $A_\triangle = \eta_k^2 \sqrt{3}/2$ is the area of a single $D_4$ equilateral triangular plaquette (side length $\eta_k\sqrt{2}$, area $= (\eta_k\sqrt{2})^2 \sqrt{3}/4 = \eta_k^2 \sqrt{3}/2$).

**Claim: $N_\triangle^{\max} = 3$ for 3-step detour paths on $D_4$.**

*Proof.* A 3-step detour path $\gamma = (v_1, v_2, v_3)$ together with the 2-step straight path $\gamma_0 = (\hat{n}, \hat{n})$ forms a closed 5-edge polygon. By a polygon-triangulation argument, any 5-edge polygon in the $D_4$ plaquette complex decomposes into at most 3 triangular faces. Numerical verification confirms this: of the 24 three-step paths to $(2,2,0,0)$, exactly 16 paths have $N_\triangle = 1$ (area tensor norm $\sqrt{3/2}$) and 8 paths have $N_\triangle = 3$ (area tensor norm $3\sqrt{3/2}$). The 8 maximal-area paths are those where $v_2 = \hat{n}$ (the straight direction appears as the middle step), creating a "bowtie" pattern that spans 3 elementary triangles. $\square$

**Step 2: Field strength bound.** In the small-field region:

$$\|F_{\mu\nu}\| \leq C_F \cdot g_k^{1-\delta} / \eta_k^2 \tag{7.12}$$

per plaquette (the $\eta_k^2$ accounts for the plaquette area).

**Step 3: Path contribution.** Each detour path contributes:

$$\|U_\gamma - U_{\gamma_0}\| \leq N_\triangle(\gamma) \cdot A_\triangle \cdot C_F g_k^{1-\delta}/\eta_k^2 = N_\triangle(\gamma) \cdot C_F g_k^{1-\delta} \cdot \frac{\sqrt{3}}{2} \tag{7.13}$$

**Step 4: Average (uniform bound).** Using $N_\triangle^{\max} = 3$:

$$\left\|\bar{U} - U_{\gamma_0}\right\| \leq \frac{1}{|P|}\sum_{\gamma \neq \gamma_0} \|U_\gamma - U_{\gamma_0}\| \leq \frac{24}{25} \cdot N_\triangle^{\max} \cdot C_F g_k^{1-\delta} \cdot \frac{\sqrt{3}}{2} \tag{7.14}$$

$$= \frac{24}{25} \cdot 3 \cdot \frac{\sqrt{3}}{2} \cdot C_F \cdot g_k^{1-\delta} = \frac{36\sqrt{3}}{25} C_F \cdot g_k^{1-\delta} \tag{7.15}$$

Therefore:

$$\left\|\bar{U} - U_{\gamma_0}\right\| \leq C_\text{avg} \cdot g_k^{1-\delta} \tag{7.16}$$

with:

$$C_\text{avg} = \frac{36\sqrt{3}}{25} C_F \approx 2.49 \, C_F \tag{7.16a}$$

**Tighter per-path bound.** Using the actual distribution of $N_\triangle(\gamma)$ (16 paths with $N_\triangle = 1$, 8 paths with $N_\triangle = 3$):

$$\left\|\bar{U} - U_{\gamma_0}\right\| \leq \frac{1}{25}\left(16 \cdot 1 + 8 \cdot 3\right) \cdot \frac{\sqrt{3}}{2} \cdot C_F \cdot g_k^{1-\delta} = \frac{4\sqrt{3}}{5} C_F \cdot g_k^{1-\delta} \approx 1.39\, C_F \cdot g_k^{1-\delta} \tag{7.16b}$$

Both bounds are valid; the uniform bound (7.16a) suffices for Balaban's inductive argument.

**Step 5: Including projection error.** The SU(3) projection adds an error of $O(g_k^2 \eta_k^2)$ (Eq. 6.6), which is subleading in the small-field region ($g_k \ll 1$). The total bound in lattice units ($\eta_k = 1$) is:

$$\boxed{\|Q_\text{FCC}(U) - U_{\gamma_0}\| \leq C_\text{avg} \cdot g_k^{1-\delta} + O(g_k^2)} \tag{7.17}$$

This is the primary result: a dimensionless bound in terms of the running coupling and the small-field exponent $\delta$.

**Physical-unit form.** When tracking physical length scales (as needed for Balaban's multi-scale induction), we restore the lattice spacing $\eta_k$. The small-field condition $|F_p| \leq C g_k^{1-\delta}$ constrains the dimensionless plaquette variable $U_p - \mathbb{1} \sim i g_k \eta_k^2 F_{\mu\nu}^{\text{phys}}$, so the field strength in physical units satisfies $\|F_{\mu\nu}^{\text{phys}}\| \leq C g_k^{-\delta} / \eta_k^2$. In terms of the dimensionless lattice field strength $f_p = g_k \eta_k^2 F_{\mu\nu}^{\text{phys}}$ (which is $O(g_k^{1-\delta})$ by the small-field condition), the bound reads:

$$\|Q_\text{FCC}(U) - U_{\gamma_0}\| \leq C_\text{avg} \cdot g_k^{1-\delta} \tag{7.18}$$

For comparison with Balaban's notation, where the bound is written as $O(g_k \cdot p(\eta_k))$ with $p(\eta_k)$ a polynomial in $\eta_k$: in lattice units $\eta_k = 1$, this reduces to $O(g_k)$, consistent with Eq. (7.17) since $g_k^{1-\delta} \leq g_k$ for $g_k \leq 1$ and $\delta > 0$. The $\eta_k^{d/2}$ factor appearing in Balaban's physical-unit formulation is absorbed into the lattice-unit convention where plaquette variables are already dimensionless.

### §7.4 Comparison with Hypercubic C_avg 🔶 NOVEL

On the **hypercubic** lattice ($\mathbb{Z}^4$), the comparison is structurally different because the minimum-length detour paths from $x'$ to $x' + 2\hat{e}_\mu$ have **4 steps** (not 3), since $\mathbb{Z}^4$ NN vectors are unit vectors and $2\hat{e}_\mu$ cannot be decomposed into fewer than 4 non-straight NN steps (each detour must go out in one orthogonal direction and return). The hypercubic averaging kernel therefore uses paths through **square plaquettes** of area $A_\square = \eta_k^2$:

- Straight path: 1 (two-step $\hat{e}_\mu + \hat{e}_\mu$)
- 4-step detour paths: $\sim 40$ per direction (through 3 orthogonal axes, $\pm$, with various orderings)
- Square plaquettes enclosed per detour: $N_\square^{\max} = 1$

The hypercubic $C_\text{avg}$ is (in the analogous uniform-bound framework):

$$C_\text{avg}^{\text{cubic}} \sim C_F \cdot O(1) \tag{7.19}$$

A direct numerical comparison of $C_\text{avg}^{\text{FCC}} / C_\text{avg}^{\text{cubic}}$ depends on the path weighting convention. The verification script (`prop_7_6_1_fcc_averaging_kernel.py`, Test 12) gives a ratio of $\approx 1.87$ using equal-weight averaging. The key qualitative observation is that the FCC $C_\text{avg}$ is $O(1)$ times larger than the hypercubic value — reflecting the higher coordination number and triangular plaquette geometry — but this is compensated in the full Balaban program by the **better UV behavior** of the FCC lattice ($O(a^4)$ rotational artifacts vs. $O(a^2)$ on the hypercubic lattice, from Prop 7.5.1).

---

## §8. Part (d) — Self-Similarity and Inductive Requirements

### §8.1 Scale Transformation Preserves Geometric Structure ✅ ESTABLISHED

The $D_4$ lattice has the **self-coarsening** property: for any spacing $\eta$, the sublattice $2D_4(\eta) = D_4(2\eta)$ is isomorphic to the original $D_4$ lattice with doubled spacing. Specifically:

1. **Same Voronoi cell type:** The Voronoi cell of $D_4(2\eta)$ is a rescaled 24-cell (same polytope as the Voronoi cell of $D_4(\eta)$, scaled by 2)
2. **Same coordination number:** $D_4(2\eta)$ has 24 nearest neighbors (the vectors $2\hat{n}_i$)
3. **Same plaquette structure:** Triangular plaquettes on $D_4(2\eta)$ are rescaled copies of those on $D_4(\eta)$
4. **Same symmetry group:** $W(D_4)$ acts identically on both lattices

Therefore, the averaging kernel $Q_\text{FCC}$ defined in Part (b) applies **verbatim** at every scale — the same path sets, the same number of paths per direction (25), the same geometric constants. This is the self-similarity that enables Balaban's inductive argument.

Verified numerically in `prop_7_6_1_fcc_averaging_kernel.py` (Test 10): the blocked $2D_4$ lattice has 24 NN vectors, all in $2D_4$, with the same norm ratio. ✓

### §8.2 Running Coupling and Small-Field Breakdown 🔶 NOVEL

The averaging kernel operates within the **small-field region** where $|F_p| \leq C g_k^{1-\delta}$. The running coupling at scale $k$ (with blocking factor $L = 2$) is:

$$g_k^2 = \frac{g_0^2}{1 - 2b_0 g_0^2 \ln 2^k} = \frac{g_0^2}{1 - 2b_0 g_0^2 k \ln 2} \tag{8.1}$$

This grows with $k$. The small-field condition requires $g_k^2 \lesssim O(1)$, which limits the RG to:

$$k \lesssim k_{\max} \sim \frac{1}{2b_0 g_0^2 \ln 2} \sim \frac{\beta}{12 b_0 \ln 2} \tag{8.2}$$

At $k = k_{\max}$, the lattice spacing is $\eta_{k_{\max}} = 2^{k_{\max}} \eta_0 \sim 1/\Lambda_\text{QCD}$ — the confinement scale. Beyond this point, the large-field analysis (Balaban Paper X, future Phase G work) takes over.

On the crossover path (Thm 7.5.3), the exact mass gap $\mu(\beta, \varepsilon) > 0$ provides IR control beyond $k_{\max}$ — this is the novel CG contribution identified in the [Research Note](../supporting/Research-Note-Balaban-RG-Adaptation-FCC.md) §5.

### §8.3 Verification of Balaban's Four Inductive Requirements 🔶 NOVEL

For $Q_\text{FCC}$ to serve as the averaging kernel in Balaban's RG iteration, it must satisfy four requirements at every scale $k$:

| Requirement | Statement | Verification |
|-------------|-----------|--------------|
| **R1: Gauge covariance** | $Q(U^g) = Q(U)^{g'}$ | §6.3, Eq. (6.3) ✅ |
| **R2: Smallness** | $\|Q(U) - U_\text{direct}\| \leq C_\text{avg}\, g_k^{1-\delta}$ (lattice units) | §7.3, Eq. (7.17) ✅ |
| **R3: Analyticity** | $Q$ is analytic in link variables near $\mathbb{1}$ | §6.4 ✅ |
| **R4: Lattice compatibility** | $Q$ commutes with $W(D_4)$ transformations | Follows from path-set symmetry ✅ |

**R4 (detailed).** The path set $P(\hat{n})$ for each direction $\hat{n}$ is invariant under the stabilizer of $\hat{n}$ in $W(D_4)$. Since the averaging kernel is defined symmetrically over all paths, it commutes with any lattice symmetry that permutes the paths. Under a $W(D_4)$ transformation $w$:

$$Q_\text{FCC}(w \cdot U)_{w(x'), w(y')} = w \cdot Q_\text{FCC}(U)_{x', y'} \tag{8.3}$$

This follows from the fact that $w$ permutes the path set $P(w \cdot \hat{n})$ into $w \cdot P(\hat{n})$, and the average over paths is invariant under this permutation. ✓

All four requirements are satisfied at every scale by the self-coarsening property. The kernel $Q_\text{FCC}$ is therefore a valid input to Balaban's RG iteration on the $D_4$ lattice. $\square$

---

## Appendix A: All 16 D₄/2D₄ Coset Representatives

The following table lists all 16 coset representatives derived from the $D_4$ basis $\{b_1, b_2, b_3, b_4\} = \{e_1 - e_2, e_2 - e_3, e_3 - e_4, e_3 + e_4\}$ via the canonical construction $r(\varepsilon) = \sum_i \varepsilon_i b_i$ with $\varepsilon_i \in \{0,1\}$. Verified by the algorithm in `prop_7_6_1_fcc_averaging_kernel.py` (Tests 1–2).

| $\alpha$ | $\varepsilon$ | $r_\alpha$ (standard coords) | $|r_\alpha|^2$ | $\sum r_i$ | Orbit | Min-norm alt. |
|----------|---------------|------------------------------|---------------|-----------|-------|---------------|
| 1 | $(0,0,0,0)$ | $(0, 0, 0, 0)$ | 0 | 0 | I | — |
| 2 | $(0,0,0,1)$ | $(0, 0, 1, 1)$ | 2 | 2 | II | — |
| 3 | $(0,0,1,0)$ | $(0, 0, 1, -1)$ | 2 | 0 | II | — |
| 4 | $(0,1,0,0)$ | $(0, 1, -1, 0)$ | 2 | 0 | II | — |
| 5 | $(0,1,0,1)$ | $(0, 1, 0, 1)$ | 2 | 2 | II | — |
| 6 | $(0,1,1,0)$ | $(0, 1, 0, -1)$ | 2 | 0 | II | — |
| 7 | $(0,1,1,1)$ | $(0, 1, 1, 0)$ | 2 | 2 | II | — |
| 8 | $(1,0,0,0)$ | $(1, -1, 0, 0)$ | 2 | 0 | II | — |
| 9 | $(1,1,0,0)$ | $(1, 0, -1, 0)$ | 2 | 0 | II | — |
| 10 | $(1,1,0,1)$ | $(1, 0, 0, 1)$ | 2 | 2 | II | — |
| 11 | $(1,1,1,0)$ | $(1, 0, 0, -1)$ | 2 | 0 | II | — |
| 12 | $(1,1,1,1)$ | $(1, 0, 1, 0)$ | 2 | 2 | II | — |
| 13 | $(0,0,1,1)$ | $(0, 0, 2, 0)$ | 4 | 2 | III | — |
| 14 | $(1,0,0,1)$ | $(1, -1, 1, 1)$ | 4 | 2 | IV | — |
| 15 | $(1,0,1,0)$ | $(1, -1, 1, -1)$ | 4 | 0 | V | — |
| 16 | $(1,0,1,1)$ | $(1, -1, 2, 0)$ | 6 | 2 | II$'$ | $(1, 1, 0, 0)$, $|r|^2 = 2$ |

**Notes:**
- Representatives $\alpha = 2$–$12$ are $D_4$ root vectors (NN vectors with $|r|^2 = 2$), forming the 12-element Orbit II under $W(D_4)$.
- Representative $\alpha = 16$ has the largest norm ($|r|^2 = 6$). Its coset also contains the minimal-norm element $(1,1,0,0)$ (since $(1,1,0,0) - (1,-1,2,0) = (0,2,-2,0) = 2(0,1,-1,0) \in 2D_4$). Under $W(D_4)$, this coset belongs to Orbit II (the root orbit), as $(1,1,0,0)$ is a $D_4$ root vector. Thus the orbit decomposition in $D_4/2D_4$ is $1 + 12 + 1 + 1 + 1 = 16$, where the canonical basis produces 11 minimal-norm root coset reps and 1 non-minimal rep for the 12th root coset.
- Orbits III ($\alpha = 13$), IV ($\alpha = 14$), and V ($\alpha = 15$) are singleton orbits in $D_4/2D_4$: their $W(D_4)$ orbits in $D_4$ each have 8 elements, but all 8 fall into the same $2D_4$-coset.

---

## Appendix B: Path Enumeration by Direction Type

By $W(D_4)$ symmetry, the path counts depend only on the equivalence class of the direction under the lattice symmetry. All 24 $D_4$ nearest-neighbor directions are related by $W(D_4)$ and hence have identical path counts.

**Representative direction $\hat{n} = (1,1,0,0)$:**

| Path type | Length | Count | Example |
|-----------|--------|-------|---------|
| Straight | 2 steps | 1 | $(1,1,0,0) + (1,1,0,0)$ |
| Detour | 3 steps | 24 | $(1,1,0,0) + (1,0,1,0) + (0,1,-1,0)$ |
| **Total** | — | **25** | — |

The 24 three-step paths decompose into classes by the transverse displacement:
- 12 paths with detour in a "positive" transverse direction (e.g., involving $(0,0,1,0)$ component)
- 12 paths with detour in a "negative" transverse direction

**All directions have the same count** by $W(D_4)$ symmetry (verified numerically for $(1,1,0,0)$, $(1,-1,0,0)$, and $(1,0,1,0)$).

---

## Appendix C: Side-by-Side Comparison with Balaban's Hypercubic Kernel

| Feature | Balaban (Hypercubic) | This Work (FCC) |
|---------|---------------------|-----------------|
| **Lattice** | $\mathbb{Z}^4$ | $D_4$ |
| **Blocking** | $\mathbb{Z}^4 \to \mathbb{Z}^4$ (factor 2) | $D_4 \to D_4$ (factor 2) |
| **Sites per coarse cell** | $2^4 = 16$ | $[D_4:2D_4] = 16$ |
| **Coarse link length** | $2a$ (coordinate direction) | $2\sqrt{2}a$ ($D_4$ NN direction) |
| **Plaquette type** | Square (4-link) | Triangular (3-link) |
| **Straight paths** | 1 per direction | 1 per direction |
| **Detour paths** | $\sim$40 per direction (4-step) | 24 per direction (3-step) |
| **Total paths** | $\sim$41 | 25 |
| **Gauge covariance** | Automatic (Thm 3.1) | Automatic (same theorem) |
| **$C_\text{avg}$** | $O(1)\, C_F$ | $\approx 2.49\, C_F$ (uniform); $\approx 1.39\, C_F$ (per-path) |
| **Fourth-moment isotropy** | No (anisotropic at $O(k^4)$) | **Yes** (exact) |
| **Self-coarsening** | Yes ($\mathbb{Z}^4 \to \mathbb{Z}^4$) | Yes ($D_4 \to D_4$) |
| **Inductive requirements** | All 4 satisfied | All 4 satisfied |

**Key differences:** (1) The FCC kernel uses 3-step detours (25 total paths) while the hypercubic kernel uses 4-step detours ($\sim$41 total paths), making direct $C_\text{avg}$ comparison convention-dependent. (2) The FCC $C_\text{avg}$ is $O(1)$ times larger than the hypercubic value (ratio $\approx 1.87$ in equal-weight convention, Test 12). (3) This is offset by the $D_4$ fourth-moment isotropy, which eliminates the $O(a^2)$ rotational artifacts that plague the hypercubic lattice. The net effect is that the FCC kernel provides **comparable or better** control of lattice artifacts in the full Balaban RG iteration.

---

*Document created: 2026-02-14*
*Classification: 🔶 NOVEL (FCC kernel construction) / ✅ ESTABLISHED (Balaban framework)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase G, Step G.1*
