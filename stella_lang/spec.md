# StellaLang Specification

## A Ternary Programming Language from Chiral Geometrogenesis

**Version:** 1.1
**Date:** 2026-03-05

StellaLang is a minimal ternary programming language derived from the
Chiral Geometrogenesis framework. Where Brainfuck operates on binary cells
with 8 commands, StellaLang operates on **ternary cells** (trits) derived
from the Z_3 center symmetry of SU(3).

**Grounding convention:** Each primitive is classified as either:
- **Proof-grounded (P):** Directly derived from a CG theorem
- **Proof-motivated (M):** Inspired by the framework's geometry but is a
  computational design choice, not a mathematical consequence of the proofs

---

## 1. Foundational Principle: "It from Trit"

The framework's First Stable Principle (Prop 0.0.XXa) proves that N = 3 is
the minimal stable configuration — the universe's fundamental information
unit is not the bit (Z_2) but the **trit** (Z_3). StellaLang makes this
concrete: every memory cell holds a value in {0, 1, 2}, corresponding to
the three color field phases.

| Trit Value | Z_3 Element | Phase     | Color Field |
|------------|-------------|-----------|-------------|
| 0          | w^0 = 1     | 0         | chi_R       |
| 1          | w^1         | 2*pi/3    | chi_G       |
| 2          | w^2         | 4*pi/3    | chi_B       |

**Proof basis:** Definition 0.1.2 (Three Color Fields), Prop 0.0.XXa (First Stable Principle)

---

## 2. Memory Model

### 2.1 Tape Structure

Memory is a tape of trit cells with cyclic wrapping at its boundary.

- **Initial size:** 8 cells (the 8 vertices of the stella octangula)
- **Growth:** Tape extends dynamically when the pointer advances past the
  current boundary (new configurations become accessible as lambda evolves)
- **Topology:** Cyclic — position wraps modulo tape length
- **Default values:** All cells initialized to 0 (identity phase)

**Proof basis (P):** Definition 0.1.1 (Stella Octangula Boundary Topology)
provides the initial tape size of 8 vertices. Definition 0.1.2 (Three Color
Fields) constrains each cell to Z_3 = {0, 1, 2}.

**Architectural note (M):** The 8 vertices of the stella octangula are
physically organized as two disjoint tetrahedra: T+ (R, G, B, W) and
T- (R_bar, G_bar, B_bar, W_bar), with Euler characteristic chi = 4
(Def 0.1.1 Section 2.3). The base StellaLang interpreter models these
as a single flat tape for simplicity. The Stella Soup VM (soup.c) more
faithfully captures this structure with two heads: h0 for T+ and h1 for
T-. Cyclic wrapping is a computational convention, not derived from the
proofs — the proofs establish T^2 as the Cartan torus of **phase
configurations**, not as a spatial memory topology (see Prop 0.0.17p).

### 2.2 Pointer

A single pointer indexes the current cell. Pointer movement is a
**spatial** operation on the tape, not a temporal one — the arrow of
time constrains lambda (the execution clock), not the spatial index.

**Proof basis (P):** Prop 0.0.17c (Arrow of Time) establishes that
lambda is strictly forward, but places no constraint on spatial position.

**Architectural note (M):** The spec describes pointer movement as
"geodesic motion," borrowing language from Prop 0.0.17p. However,
Prop 0.0.17p's geodesics are trajectories on the Cartan torus T^2
(parameterizing color field phases), not movements along a memory tape.
The pointer increment is a standard computational primitive. The analogy
is suggestive but not a derivation.

---

## 3. Execution Model

### 3.1 Internal Time (lambda)

Every instruction advances the internal time parameter lambda by one tick.
lambda is strictly monotonically increasing — it never decreases.

- **Clock frequency:** w = 220 MeV (from Casimir equipartition)
- **Tick period:** T = 2*pi/w ~ 2.8 * 10^-21 s

**Proof basis:** Theorem 0.2.2 (Internal Time Emergence),
Prop 0.0.17l (Internal Frequency from Casimir Equipartition)

### 3.2 Arrow of Time

The arrow of time (Prop 0.0.17c) constrains:
1. lambda is strictly forward (execution never reverses)
2. Phase rotation follows the R -> G -> B chirality (Theorem 2.2.4)

The arrow does NOT constrain:
3. Spatial pointer position (can address any cell at any lambda-tick)
4. Re-executing earlier program instructions (loops revisit code
   at later lambda values — this is NOT time reversal)

**Proof basis:** Prop 0.0.17c (Arrow of Time from Information Geometry),
Theorem 2.2.4 (Chirality Selection)

---

## 4. Instruction Set

StellaLang has **7 instructions**. All other characters are comments.

### 4.1 Phase Operations

| Instruction | Name            | Operation              | Proof Basis |
|-------------|-----------------|------------------------|-------------|
| `r`         | Rotate          | cell = (cell + 1) % 3 | Def 0.1.2, Thm 2.2.4 |
| `R`         | Double Rotate   | cell = (cell + 2) % 3 | Prop 0.0.5a (Z_3 group closure) |

**`r` (Rotate):** Applies w (forward phase rotation) to the current cell.
This is the fundamental operation: R -> G -> B -> R, following the chirality
selected by QCD topology.

**`R` (Double Rotate):** Applies w^2 (two forward rotations) to the current
cell. This is NOT a backward rotation. In Z_3, the inverse of w is w^2,
and w^2 is reached by rotating forward twice: w * w = w^2. The result
(cell + 2) % 3 is equivalent to (cell - 1) % 3, but the mechanism is
two forward steps, consistent with the arrow of time.

### 4.2 Pointer Movement

| Instruction | Name    | Operation                              | Grounding |
|-------------|---------|----------------------------------------|-----------|
| `>`         | Advance | pointer = (pointer + 1) % tape_length  | (M) computational primitive |
| `<`         | Retreat | pointer = (pointer - 1) % tape_length  | (M) convenience for (N-1) advances |

**`>` (Advance):** Moves the pointer forward by one position. If at the
tape boundary, the tape extends by one cell (dynamic growth). When the
tape is at maximum size, the pointer wraps cyclically.

**`<` (Retreat):** Moves the pointer backward by one position (wrapping
cyclically). On a cyclic tape this is equivalent to (tape_length - 1)
forward advances, so `<` adds no computational power — it is purely a
convenience. Strict mode disables `<` to demonstrate this.

**Critical distinction:** Pointer movement is a **spatial** operation,
not a temporal one. The arrow of time (Prop 0.0.17c) constrains lambda
(which always increases), not the spatial pointer. Moving left at
lambda=100 and right at lambda=101 involves two strictly-forward
lambda-ticks exploring different spatial positions.

**Architectural note (M):** Earlier versions of this spec described `>`
and `<` as "short geodesic" and "long geodesic," invoking Prop 0.0.17p
(geodesic motion on the Cartan torus T^2). That analogy was incorrect:
Prop 0.0.17p's T^2 is the **phase configuration space** of the color
fields, not a spatial memory topology. Pointer movement is a standard
computational primitive. The terminology has been corrected.

### 4.3 Control Flow

| Instruction | Name               | Operation                                | Proof Basis |
|-------------|--------------------|------------------------------------------|-------------|
| `[`         | Superselection Open | If cell == 0, jump past matching `]`     | (P) Prop 0.0.17h |
| `]`         | Superselection Close| If cell != 0, jump back to matching `[`  | (P) Prop 0.0.17h |

**`[` (Superselection Open):** Tests whether the current cell is in the
identity phase (value 0). If so, the Z_3 superselection mechanism
triggers discretization — execution jumps past the matching `]`.

The Z_3 superselection (Prop 0.0.17h) is a hard gate: when the
information rate exceeds the critical threshold and the phase is at
identity, the configuration space discretizes to T^2/Z_3. This is
kinematically irreversible, unlike soft pressure modulation.

**`]` (Superselection Close):** If the current cell is NOT in the identity
phase (value != 0), execution jumps back to the matching `[`. This
re-executes earlier instructions at a later lambda-tick. The program
counter revisits code, but lambda continues forward — this is loop
iteration, not time reversal.

**Why `[`/`]` test for zero (identity phase):**
Pressure functions P_c(x) are smooth and never exactly zero (Def 0.1.3,
Prop 0.1.3a). They cannot serve as hard gates. Instead, the Z_3
superselection from information horizon crossing (Prop 0.0.17h) provides
the discrete, irreversible gate mechanism: when the phase state is at
identity (the Z_3-invariant fixed point), a qualitative transition occurs.

### 4.4 I/O Operations

| Instruction | Name    | Operation                          | Proof Basis |
|-------------|---------|------------------------------------|-------------|
| `.`         | Observe | Output current cell value          | Def 0.0.32 |
| `,`         | Couple  | Read input into current cell       | Def 0.0.32 |

**`.` (Observe):** The internal observer (Def 0.0.32) applies its
observation map M_obs to the current cell, producing an output value.
The observer's measurement is bounded by the Holevo bound (Def 0.0.32
Prop 3.1) and subject to Z_3 superselection — the output is always
a trit in {0, 1, 2}.

**`,` (Couple):** External input couples to the current cell via the
observation map M_obs. Input values are reduced mod 3, enforcing the
Z_3 constraint. If no input is available, the cell is set to 0
(identity phase).

---

## 5. Turing Completeness

StellaLang is Turing-complete. The proof follows from equivalence with
Brainfuck (which is proven Turing-complete):

| Brainfuck | StellaLang | Notes |
|-----------|------------|-------|
| `+`       | `r`        | Increment mod 3 instead of mod 256 |
| `-`       | `R`        | Double rotate (= effective decrement mod 3) |
| `>`       | `>`        | Identical |
| `<`       | `<`        | Long geodesic (equivalent on cyclic tape) |
| `[`       | `[`        | Tests for 0 in both |
| `]`       | `]`        | Tests for non-0 in both |
| `.`       | `.`        | Output |
| `,`       | `,`        | Input |

The key difference is the cell size: trits (mod 3) instead of bytes
(mod 256). Ternary Brainfuck variants with cells mod p for any prime p
are known to be Turing-complete (a cell mod 3 can simulate a cell mod 2
through encoding, and the tape is unbounded).

---

## 6. Strict Mode (Forward-Only)

For maximum fidelity to the proofs, StellaLang supports a **strict mode**
where the `<` instruction is disabled. In strict mode:

- The tape is cyclic (wraps at boundary)
- The pointer can only advance via `>`
- To reach the "previous" cell, advance (tape_length - 1) times
- This is equivalent to the standard mode (since `<` is syntactic sugar
  for (N-1) applications of `>` on a cyclic tape)

Strict mode demonstrates that `<` adds no computational power — it is
purely a convenience. All programs are expressible using only `r R > [ ] . ,`

---

## 7. Proof Dependency Map

StellaLang primitives fall into two categories: those directly derived
from proofs (P) and those that are proof-motivated design choices (M).

### 7.1 Proof-Grounded Primitives (P)

```
Axiom A1 (Proto-temporal ordering)
  |
  v
Theorem 0.2.2 (Internal Time Emergence) -----> lambda clock
  |
  v
Prop 0.0.17l (Internal Frequency) -----------> tick rate (w = 220 MeV)
  |
  v
Prop 0.0.17c (Arrow of Time) ----------------> forward-only execution
  |
  v
Theorem 2.2.4 (Chirality Selection) ---------> R->G->B rotation direction
  |
  v
Definition 0.1.2 (Three Color Fields) -------> trit data type {0, 1, 2}
  |
  v
Prop 0.0.5a (Z_3 Center Constraint) ---------> group closure (w^2 valid)
  |
  v
Definition 0.1.1 (Stella Octangula) ---------> 8-vertex initial tape size
  |
  v
Prop 0.0.17h (Information Horizon) ----------> superselection gate [/]
  |
  v
Definition 0.0.32 (Internal Observer) -------> I/O operations (. ,)
  |
  v
Prop 0.0.XXb (Bootstrap Computability) ------> computational framework
```

### 7.2 Proof-Motivated Design Choices (M)

| Feature | Design choice | Why not derived |
|---------|---------------|-----------------|
| Single flat tape | 8 cells in a linear array | Def 0.1.1 establishes two disjoint tetrahedra (T+, T-), not a single connected tape. The soup VM's two-head model is more faithful. |
| Cyclic wrapping | pointer wraps mod tape_length | The T^2 torus in Prop 0.0.17p is the Cartan torus of phase configurations, not a spatial memory topology. Wrapping is a standard computational convention. |
| Pointer as "advance" | pointer += 1 | Not derived from geodesic motion on T^2. Standard tape-machine primitive. |
| `<` instruction | pointer -= 1 | Pure convenience (= N-1 advances on cyclic tape). Strict mode disables it. |

### 7.3 The T+/T- Gap

The stella octangula has 8 vertices organized as **two disjoint
tetrahedra** (Def 0.1.1 Section 2.3):
- T+ with vertices {R, G, B, W} — matter sector
- T- with vertices {R_bar, G_bar, B_bar, W_bar} — antimatter sector

The base StellaLang interpreter flattens these into a single tape,
losing the disjoint-union topology (chi = 4, not chi = 2). The
**Stella Soup VM** (soup.c) partially recovers this structure by
using two independent heads (h0 for T+, h1 for T-) with explicit
copy operations (CPY01, CPY10) for information transfer between
the two tetrahedra (grounded in Thm 0.2.1: Total Field Superposition).

---

## 8. Example Programs

See `examples.py` for runnable examples with explanations.

### 8.1 Three Phases

```
r.r.r.
```

Output: `1 2 0` — Cycles through all three phases (G, B, R).

### 8.2 Countdown

```
rr[R.]
```

Set cell to 2, then loop: double-rotate (2->1->0) and observe.
Output: `1 0` — Counts down from 2 to 0 (stops when cell hits 0).

Wait: rr sets cell to 2 (0 -> 1 -> 2). Then [R.] loop:
- Cell is 2 (nonzero), enter loop. R: 2->1. Output: 1.
- Cell is 1 (nonzero), loop. R: 1->0. Output: 0.
- Cell is 0, exit loop.

### 8.3 Copy Cell

```
[>r<R]
```

Copies current cell value to the next cell (destructively).
Uses the torus topology: `<` takes the long geodesic back.
