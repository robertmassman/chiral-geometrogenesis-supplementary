# Lean Verification Quick Prompts

Copy-paste prompts for verifying Lean 4 formalizations. Replace `[FileName]` with actual file names (without `.lean` extension) and `[Path]` with the relative path from `ChiralGeometrogenesis/`.

## Quick Reference: Which Prompt to Use

| Situation | Prompt to Use |
|-----------|---------------|
| **Foundational file** (Foundations/, PureMath/, heavily imported) | **Foundational Integrity Audit** — 6-phase deep audit |
| **Any other file** | **Thorough Adversarial Review** — standard verification |
| **Quick triage** | **Quick foundational check** or **Quick adversarial check** |
| **Fix issues immediately** | **...with fixes** variants |

**Rule of thumb:** If 3+ other files import this file, use the Foundational Integrity Audit.

---

## Lean File Generation

### Generate Lean file from markdown proof
```
Generate a Lean 4 formalization from docs/proofs/[Theorem-X.Y.Z-Name].md:

1. ANALYZE MARKDOWN
   - Extract the formal theorem statement
   - Identify all hypotheses and assumptions
   - List required definitions and dependencies
   - Note any physical constants or parameters

2. DETERMINE PLACEMENT
   - Choose appropriate directory (Foundations/, Phase0/, PureMath/, etc.)
   - Follow naming convention: Theorem_X_Y_Z.lean
   - Check for existing related files to import

3. CREATE LEAN STRUCTURE
   - Add module docstring matching markdown title
   - Import required dependencies (Mathlib, project modules)
   - Define any new types or structures needed
   - State the main theorem with proper type signatures

4. ADD PROOF SKELETON
   - Use `sorry` for proofs that need work
   - Add comments referencing markdown section numbers
   - Include `-- TODO:` markers for complex steps

5. VERIFY
   - Run `lake build` to check syntax
   - Ensure imports resolve correctly
   - Confirm theorem statement matches markdown

Output the complete .lean file content.
```

### Generate Lean stub (minimal)
```
Create minimal Lean stub for docs/proofs/[Theorem-X.Y.Z-Name].md:
- Module docstring
- Required imports
- Main theorem statement with `sorry` proof
- No helper lemmas (add later)

Just get it compiling first.
```

### Generate Lean from multiple markdown files
```
Generate Lean formalization for Theorem [X.Y.Z] using all three files:
- docs/proofs/Theorem-[X.Y.Z]-[Name].md (statement)
- docs/proofs/Theorem-[X.Y.Z]-[Name]-Derivation.md (proof steps)
- docs/proofs/Theorem-[X.Y.Z]-[Name]-Applications.md (verification)

Extract:
1. Formal statement from main file
2. Proof structure from Derivation file
3. Numerical checks from Applications file (as #eval or test theorems)
```

### Batch generate Lean stubs
```
Generate Lean stubs for all unformalized theorems in Phase [N]:
1. Check docs/proofs/Phase[N]/ for all theorem markdown files
2. Check which already have corresponding .lean files
3. For each missing formalization, create a stub with:
   - Correct imports
   - Theorem statement
   - `sorry` proof
4. Report: X new stubs created, Y already existed
```

---

## Build & Compilation

### Build entire project
```
Run `lake build` in the ChiralGeometrogenesis directory and report any errors.
```

### Build specific file
```
Build [Path]/[FileName].lean and report any errors or warnings.
```

### Check for sorry statements
```
Find all `sorry` statements in the Lean codebase and list them by file with line numbers.
```

### List all axioms used
```
Run `lake env lean --run Mathlib/Tactic/ReduceAxioms.lean` or equivalent to list all axioms used in [FileName].lean.
```

---

## Sorry Elimination

### Eliminate sorry in specific file
```
Eliminate all sorry statements in [Path]/[FileName].lean:
1. List each sorry with its context
2. Determine what proof term or tactic is needed
3. Implement the proof
4. Verify compilation succeeds
```

### Prioritize sorry elimination
```
Analyze all sorry statements in the codebase and prioritize elimination by:
1. Foundational theorems (Phase 0) - highest priority
2. Theorems with many dependents
3. Simple tactical proofs
4. Complex proofs requiring new lemmas
```

### Check sorry-free status
```
Verify that [Path]/[FileName].lean is completely sorry-free and compiles cleanly.
```

---

## Type Checking & Consistency

### Verify type consistency
```
Check [Path]/[FileName].lean for:
1. All type annotations are consistent
2. No implicit coercions cause issues
3. Universe levels are correct
4. Dependent types are well-formed
```

### Check definition well-formedness
```
Verify that all definitions in [Path]/[FileName].lean are:
1. Terminating (no infinite recursion)
2. Well-founded (for recursive definitions)
3. Computable (if marked as such)
```

### Verify import consistency
```
Check that all imports in [Path]/[FileName].lean are:
1. Actually used
2. Not circular
3. At the correct module path
```

---

## Proof Verification

### Verify theorem proof
```
Verify the proof of `[theoremName]` in [Path]/[FileName].lean:
1. Check each tactic step is valid
2. Verify all hypotheses are used
3. Check the proof is complete (no sorry)
4. Ensure the statement matches the markdown specification
```

### Check proof against specification
```
Compare [Path]/[FileName].lean against docs/proofs/[Theorem-X.Y.Z].md:
1. Statement matches formal claim
2. All hypotheses are captured
3. Conclusion is equivalent
4. Any discrepancies are documented
```

### Verify lemma dependencies
```
For [theoremName] in [Path]/[FileName].lean:
1. List all lemmas it depends on
2. Verify each dependency is proven (not sorry)
3. Check the dependency chain is acyclic
```

---

## Structure & Organization

### Check module structure
```
Verify [Path]/[FileName].lean follows project conventions:
1. Proper namespace hierarchy
2. Consistent naming (snake_case for defs, CamelCase for types)
3. Appropriate use of sections
4. Documentation comments on public definitions
```

### Check for code duplication
```
Find duplicate or near-duplicate definitions across the Lean codebase that could be unified.
```

### Verify export structure
```
Check that [Path]/[FileName].lean properly exports definitions needed by other modules.
```

---

## Mathematical Consistency

### Verify physical units (if applicable)
```
Check dimensional consistency in [Path]/[FileName].lean:
1. All physical quantities have correct units
2. Unit conversions are explicit
3. Dimensionless quantities are marked
```

### Check numerical bounds
```
Verify any numerical bounds or estimates in [Path]/[FileName].lean:
1. Bounds are provably correct
2. Approximations are justified
3. Error terms are tracked
```

### Verify algebraic identities
```
Check that algebraic identities in [Path]/[FileName].lean are:
1. Correctly stated
2. Proven (not assumed)
3. Consistent with Mathlib conventions
```

---

## Integration with Markdown Proofs

### Sync Lean with markdown
```
Compare [Path]/[FileName].lean with corresponding markdown proof:
1. Identify any statements that differ
2. Check which version is authoritative
3. Propose updates to align them
```

### Generate Lean stub from markdown
```
Create a Lean skeleton for docs/proofs/[Theorem-X.Y.Z].md:
1. Define required types and structures
2. State the main theorem
3. Add sorry placeholders for proofs
4. Include proper imports
```

### Document Lean proof in markdown
```
Update docs/proofs/[Theorem-X.Y.Z].md to reflect the Lean formalization:
1. Add "Lean Formalization" section
2. Note any differences from informal proof
3. List Mathlib dependencies used
```

---

## Testing & Validation

### Run Lean tests
```
Execute any test cases in [Path]/[FileName].lean and report results.
```

### Check example computations
```
Verify that `#check` and `#eval` statements in [Path]/[FileName].lean produce expected results.
```

### Validate against known results
```
For theorems with known numerical results, verify the Lean proof is consistent:
1. Evaluate any computable expressions
2. Compare with values in docs/reference-data/
3. Report any discrepancies
```

---

## Refactoring

### Simplify proof
```
Simplify the proof of [theoremName] in [Path]/[FileName].lean:
1. Remove unnecessary steps
2. Use more powerful tactics where applicable
3. Factor out common patterns into lemmas
```

### Extract reusable lemmas
```
Identify reusable lemmas that could be extracted from [Path]/[FileName].lean to a common module.
```

### Align with Mathlib style
```
Refactor [Path]/[FileName].lean to follow Mathlib style guidelines:
1. Naming conventions
2. Proof style (term-mode vs tactic-mode)
3. Documentation format
```

---

## Dependency Analysis

### Show file dependencies
```
List all files that [Path]/[FileName].lean imports (direct and transitive).
```

### Show dependents
```
List all files that import [Path]/[FileName].lean.
```

### Check for circular imports
```
Verify there are no circular import dependencies in the Lean codebase.
```

---

## Foundational File Integrity Audit

**Use this prompt for foundational files that other theorems depend on.** Foundational files (in `Foundations/`, `PureMath/`, or any file imported by many others) require the highest scrutiny because errors propagate to all dependents.

### Quick foundational check
```
Quick foundational check of [Path]/[FileName].lean:
1. Count axioms (declared + imported): Are there more than expected?
2. Count sorries: Any in critical path?
3. Check if ANY sorry could mask a FALSE statement
4. Identify the single most suspicious claim
5. Rate: ✅ SOLID / ⚠️ NEEDS AUDIT / ❌ BLOCKED

Output 3-5 sentences max.
```

---

## Adversarial Review

**Use these prompts for all verification.** The adversarial approach catches real issues that checklist-style verification misses.

| Prompt | When to use |
|--------|-------------|
| Thorough adversarial review | Primary review for any file |
| Quick adversarial check | Fast triage / status check |
| Adversarial review with fixes | Review + fix in one pass |

### Thorough adversarial review (RECOMMENDED)
```
Conduct a thorough adversarial review of [Path]/[FileName].lean for peer review readiness.

Be thorough and complete. We are writing Lean files and need to achieve completeness for peer review. Refer to CLAUDE.md if needed.

1. PROOF INTEGRITY
   - Check every `sorry` - can it actually be proven?
   - Look for shortcuts that hide complexity
   - Verify no circular reasoning
   - Check that hypotheses are actually used, not just assumed away
   - Check dependency path and verify that dependancies and imports are relevant and complete

2. TYPE CORRECTNESS
   - Are type signatures too weak or too strong?
   - Are there implicit coercions that hide errors?
   - Do universe levels make sense?
   - Are dependent types correctly instantiated?

3. MATHEMATICAL RIGOR
   - Do theorem statements actually say what they claim?
   - Are there hidden assumptions not in the hypotheses?
   - Check edge cases (zero, empty, degenerate)
   - Verify quantifier scoping is correct

4. SPECIFICATION FIDELITY
   - Compare against docs/proofs/[Theorem-X.Y.Z].md
   - Are there claims in markdown not captured in Lean?
   - Are there Lean assumptions not justified in markdown?
   - Do numerical values match?

5. GAPS AND SHORTCUTS
   - List every gap found with severity (CRITICAL/MAJOR/MINOR)
   - For each gap, explain what's missing
   - Propose how to fix each gap
   - Flag any "magic" that needs justification

6. DEPENDENCY AUDIT
   - Are imported lemmas actually proven (not sorry)?
   - Are axioms used appropriately?
   - Could weaker assumptions suffice?

Generate a detailed report with:
- Summary of issues found
- Prioritized list of fixes needed
- Assessment: READY / NEEDS WORK / MAJOR ISSUES

Fix implementation 
- Fix all identified items one by one
- Be diligent and conscious that we are strengthening the lean argument by using the lean files that came before
- When we apply fixed the user asks for and you see a discrepancies between the markdown and lean file. Make sure that the lean file is most accurate and then update the markdown file to match
```

### Quick adversarial check
```
Quick adversarial review of [Path]/[FileName].lean:
1. List all sorries with assessment: trivial / moderate / hard / impossible
2. Find any shortcuts or gaps
3. Check theorem statements match markdown spec
4. Rate: READY / NEEDS WORK / BLOCKED
```

### Adversarial review with fixes
```
Conduct adversarial review of [Path]/[FileName].lean AND fix issues found:

1. First, do full adversarial review (proof integrity, types, rigor, gaps)
2. For each issue found:
   - If fixable: implement the fix
   - If blocked: document why and what's needed
3. Re-run `lake build` after fixes
4. Report what was fixed vs what remains

Goal: Get to zero issues or document exactly why not.
```

---

## Peer Review Readiness

### Batch peer review readiness
```
Check peer review readiness for all Lean files in [Path]/:
For each .lean file, report:
- File name
- Compiles: ✅/❌
- Sorries: count (0 = ✅)
- Documented: ✅/❌
- Spec match: ✅/❌/N/A

Summarize: X of Y files are peer-review ready.
```

---

## Multi-Agent Verification

Unlike informal proofs, Lean's type checker handles mathematical correctness automatically. Multi-agent verification is useful for **specification correctness** and **parallel sorry elimination**.

### Parallel Sorry Elimination (N agents)

**When to use:** After running the unified verification prompt, if sorries were found.

```
Eliminate sorries in [Path]/[FileName].lean using parallel agents:

1. First, list all sorry statements in the file
2. For each independent sorry (not depending on other sorries), launch a Task agent:
   - Agent receives: the sorry context, available hypotheses, goal type
   - Agent task: construct the proof term or tactic sequence
3. Collect results and apply fixes sequentially
4. Re-run `lake build` to verify
5. Re-run unified verification prompt to confirm zero sorries
```

**Workflow:**
```
Verify → Sorries found? → Parallel elimination → Re-verify
```

### Cross-Formalization Consistency (3 agents)
```
Verify consistency between Lean formalization and markdown proof for Theorem [X.Y.Z]:

Launch in parallel:
1. LEAN AGENT - Analyze [Path]/[FileName].lean:
   - Extract all definitions, lemmas, theorems
   - Note any simplifying assumptions
   - List what Mathlib provides vs custom proofs

2. MARKDOWN AGENT - Analyze docs/proofs/Theorem-[X.Y.Z]*.md:
   - Extract formal claims and derivation steps
   - Identify physical assumptions
   - Note numerical predictions

3. RECONCILIATION AGENT - Compare outputs:
   - Map Lean statements to markdown claims
   - Identify gaps in either direction
   - Flag any inconsistencies for resolution
```

### Full Formalization Audit
```
Audit the entire Lean codebase for formalization completeness:

Launch in parallel:
1. SORRY CENSUS AGENT - Count and categorize all sorries by difficulty and priority
2. COVERAGE AGENT - Compare against docs/Mathematical-Proof-Plan.md to find unformalized theorems
3. DEPENDENCY AGENT - Build dependency graph and identify critical path blockers

Generate formalization status report with prioritized action items.
```

---

## Quick Checks

### Compile check
```
lake build [ModulePath]
```

### Find all sorries
```
grep -rn "sorry" ChiralGeometrogenesis/ --include="*.lean"
```

### Count theorems vs sorries
```
Count total theorems/lemmas and compare to sorry count to measure formalization progress.
```

### Check for deprecated syntax
```
Find any deprecated Lean 4 syntax in [Path]/[FileName].lean that should be updated.
```

---

## File References

| Resource | Location |
|----------|----------|
| Lean project root | `ChiralGeometrogenesis/` |
| Lake config | `ChiralGeometrogenesis/lakefile.lean` |
| Markdown proofs | `docs/proofs/` |
| Reference data | `docs/reference-data/` |
| Proof plan | `docs/Mathematical-Proof-Plan.md` |

---

## Directory Structure

```
ChiralGeometrogenesis/
├── Basic.lean              # Root imports
├── Foundations/            # Phase -1: Axioms and foundational theorems
├── Phase0/                 # Phase 0: Pre-geometric foundations
├── PureMath/               # Pure mathematics (not physics-specific)
│   ├── LieAlgebra/         # SU(3), weights, etc.
│   ├── Polyhedra/          # Stella octangula geometry
│   ├── Topology/           # Knot theory, etc.
│   └── Analysis/           # Wave equations, etc.
├── ColorFields/            # Color field definitions
├── Dynamics/               # Dynamical evolution
└── PhysLeanIntegration/    # Integration with PhysLean library
```

---

## Tips

- **Build before verifying**: Always run `lake build` first to catch compilation errors
- **Check sorry count**: A file with 0 sorries is "fully formalized"
- **Match markdown**: Lean statements should match the formal claims in `docs/proofs/`
- **Use Mathlib**: Prefer Mathlib lemmas over custom proofs when available
- **Document discrepancies**: If Lean proof differs from markdown, document why

---

**Last Updated:** 2025-12-22
