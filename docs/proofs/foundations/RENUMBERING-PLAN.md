# Theorem Renumbering Plan: 0.0.8-0.0.14 → 0.0.7-0.0.13

**Created:** 2026-01-01
**Completed:** 2026-01-01
**Purpose:** Close the numbering gap at 0.0.7 by renumbering theorems 0.0.8-0.0.14
**Status:** ✅ COMPLETE

---

## Overview

### Renumbering Scheme

| Current | New | Theorem Name |
|---------|-----|--------------|
| 0.0.8 | **0.0.7** | Lorentz Violation Bounds |
| 0.0.9 | **0.0.8** | Emergent Rotational Symmetry |
| 0.0.10 | **0.0.9** | Framework-Internal D4 Derivation |
| 0.0.11 | **0.0.10** | Quantum Mechanics Emergence |
| 0.0.12 | **0.0.11** | Lorentz Boost Emergence |
| 0.0.13 | **0.0.12** | Categorical Equivalence |
| 0.0.14 | **0.0.13** | Tannaka Reconstruction SU3 |

### Execution Order (CRITICAL)

Renumbering **MUST** be done in **reverse order** to avoid file collisions:
1. 0.0.14 → 0.0.13
2. 0.0.13 → 0.0.12
3. 0.0.12 → 0.0.11
4. 0.0.11 → 0.0.10
5. 0.0.10 → 0.0.9
6. 0.0.9 → 0.0.8
7. 0.0.8 → 0.0.7

---

## Stage 1: Rename 0.0.14 → 0.0.13

### 1.1 Files to Rename

#### Proof Documents
- [ ] `docs/proofs/foundations/Theorem-0.0.14-Tannaka-Reconstruction-SU3.md` → `Theorem-0.0.13-Tannaka-Reconstruction-SU3.md`
- [ ] `docs/proofs/foundations/Theorem-0.0.14-Tannaka-Reconstruction-SU3-Derivation.md` → `Theorem-0.0.13-Tannaka-Reconstruction-SU3-Derivation.md`
- [ ] `docs/proofs/foundations/Theorem-0.0.14-Tannaka-Reconstruction-SU3-Applications.md` → `Theorem-0.0.13-Tannaka-Reconstruction-SU3-Applications.md`

#### Verification Records
- [ ] `docs/proofs/verification-records/Theorem-0.0.14-Multi-Agent-Verification-2026-01-01.md` → `Theorem-0.0.13-Multi-Agent-Verification-2026-01-01.md`

#### Lean Files
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_14.lean` → `Theorem_0_0_13.lean`

#### Python Verification Scripts
- [ ] `verification/foundations/theorem_0_0_14_verification.py` → `theorem_0_0_13_verification.py`
- [ ] `verification/foundations/theorem_0_0_14_lemma_proofs.py` → `theorem_0_0_13_lemma_proofs.py`
- [ ] `verification/foundations/theorem_0_0_14_results.json` → `theorem_0_0_13_results.json`
- [ ] `verification/foundations/theorem_0_0_14_lemma_results.json` → `theorem_0_0_13_lemma_results.json`

### 1.2 Content Updates (search & replace `0.0.14` → `0.0.13`, `0_0_14` → `0_0_13`)

#### Files to Update
- [ ] `docs/Mathematical-Proof-Plan.md`
- [ ] `papers/paper-1-foundations/main.tex`
- [ ] `docs/verification-prompts/agent-prompts.md`
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_13.lean` (after rename - update namespace)
- [ ] All 3 renamed proof documents (internal references)
- [ ] All 2 renamed Python scripts (internal references)
- [ ] Both renamed JSON files (internal references)

### 1.3 Verification
```bash
# Should return NO results after completion
grep -r "0\.0\.14" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
grep -r "0_0_14" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
```

- [ ] Stage 1 Complete

---

## Stage 2: Rename 0.0.13 → 0.0.12

### 2.1 Files to Rename

#### Proof Documents
- [ ] `docs/proofs/foundations/Theorem-0.0.13-Categorical-Equivalence.md` → `Theorem-0.0.12-Categorical-Equivalence.md`
- [ ] `docs/proofs/foundations/Theorem-0.0.13-Categorical-Equivalence-Derivation.md` → `Theorem-0.0.12-Categorical-Equivalence-Derivation.md`
- [ ] `docs/proofs/foundations/Theorem-0.0.13-Categorical-Equivalence-Applications.md` → `Theorem-0.0.12-Categorical-Equivalence-Applications.md`

#### Verification Records
- [ ] `docs/proofs/verification-records/Theorem-0.0.13-Multi-Agent-Verification-2025-12-31.md` → `Theorem-0.0.12-Multi-Agent-Verification-2025-12-31.md`

#### Lean Files
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_13.lean` → `Theorem_0_0_12.lean`

#### Python Verification Scripts
- [ ] `verification/foundations/theorem_0_0_13_verification.py` → `theorem_0_0_12_verification.py`
- [ ] `verification/foundations/theorem_0_0_13_action_items.py` → `theorem_0_0_12_action_items.py`
- [ ] `verification/foundations/theorem_0_0_13_remaining_items.py` → `theorem_0_0_12_remaining_items.py`

#### Plot Files
- [ ] `verification/plots/theorem_0_0_13_stella_weights.png` → `theorem_0_0_12_stella_weights.png`
- [ ] `verification/plots/theorem_0_0_13_remaining_items.png` → `theorem_0_0_12_remaining_items.png`

### 2.2 Content Updates (search & replace `0.0.13` → `0.0.12`, `0_0_13` → `0_0_12`)

#### Files to Update
- [ ] `docs/Mathematical-Proof-Plan.md`
- [ ] `papers/paper-1-foundations/main.tex`
- [ ] `docs/verification-prompts/agent-prompts.md`
- [ ] `docs/proofs/foundations/Theorem-0.0.2-Euclidean-From-SU3.md` (references 0.0.13)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_12.lean` (after rename - update namespace)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_13.lean` (references to old 0.0.13)
- [ ] All 3 renamed proof documents (internal references)
- [ ] All 3 renamed Python scripts (internal references)

### 2.3 Verification
```bash
# Should return NO results for OLD 0.0.13 after completion
# (New 0.0.13 = Tannaka is expected)
grep -r "Categorical.*0\.0\.13" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
grep -r "0_0_13.*Categorical" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
```

- [ ] Stage 2 Complete

---

## Stage 3: Rename 0.0.12 → 0.0.11

### 3.1 Files to Rename

#### Proof Documents
- [ ] `docs/proofs/foundations/Theorem-0.0.12-Lorentz-Boost-Emergence.md` → `Theorem-0.0.11-Lorentz-Boost-Emergence.md`

#### Verification Records
- [ ] `docs/proofs/verification-records/Theorem-0.0.12-Multi-Agent-Verification-2025-12-31.md` → `Theorem-0.0.11-Multi-Agent-Verification-2025-12-31.md`

#### Lean Files
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_12.lean` → `Theorem_0_0_11.lean`

#### Python Verification Scripts
- [ ] `verification/foundations/theorem_0_0_12_verification.py` → `theorem_0_0_11_verification.py`

#### Plot Files
- [ ] `verification/plots/theorem_0_0_12_verification.png` → `theorem_0_0_11_verification.png`

### 3.2 Content Updates (search & replace `0.0.12` → `0.0.11`, `0_0_12` → `0_0_11`)

#### Files to Update
- [ ] `docs/Mathematical-Proof-Plan.md`
- [ ] `papers/paper-1-foundations/main.tex`
- [ ] `docs/proofs/foundations/Theorem-0.0.9-Framework-Internal-D4-Derivation.md` (will be renamed, references 0.0.12)
- [ ] `docs/proofs/foundations/Theorem-0.0.10-Framework-Internal-D4-Derivation.md` (references 0.0.12)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_11.lean` (after rename - update namespace)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_10.lean` (references 0.0.12)
- [ ] Renamed proof document (internal references)
- [ ] Renamed Python script (internal references)

### 3.3 Verification
```bash
# Should return NO results for OLD 0.0.12 (Lorentz Boost) after completion
grep -r "Lorentz.*Boost.*0\.0\.12" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
grep -r "0_0_12.*Lorentz" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
```

- [ ] Stage 3 Complete

---

## Stage 4: Rename 0.0.11 → 0.0.10

### 4.1 Files to Rename

#### Proof Documents
- [ ] `docs/proofs/foundations/Theorem-0.0.11-Quantum-Mechanics-Emergence.md` → `Theorem-0.0.10-Quantum-Mechanics-Emergence.md`

#### Verification Records
- [ ] `docs/proofs/verification-records/Theorem-0.0.11-Multi-Agent-Verification-2025-12-31.md` → `Theorem-0.0.10-Multi-Agent-Verification-2025-12-31.md`

#### Lean Files
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_11.lean` → `Theorem_0_0_10.lean`

#### Python Verification Scripts
- [ ] `verification/foundations/theorem_0_0_11_verification.py` → `theorem_0_0_10_verification.py`
- [ ] `verification/foundations/theorem_0_0_11_issue_resolution.py` → `theorem_0_0_10_issue_resolution.py`
- [ ] `verification/foundations/theorem_0_0_11_remaining_issues.py` → `theorem_0_0_10_remaining_issues.py`

#### Plot Files
- [ ] `verification/plots/theorem_0_0_11_norm_conservation.png` → `theorem_0_0_10_norm_conservation.png`
- [ ] `verification/plots/theorem_0_0_11_continuity.png` → `theorem_0_0_10_continuity.png`
- [ ] `verification/plots/theorem_0_0_11_uncertainty.png` → `theorem_0_0_10_uncertainty.png`
- [ ] `verification/plots/theorem_0_0_11_color_phases.png` → `theorem_0_0_10_color_phases.png`
- [ ] `verification/plots/theorem_0_0_11_prior_work_comparison.png` → `theorem_0_0_10_prior_work_comparison.png`
- [ ] `verification/plots/theorem_0_0_11_classical_limit.png` → `theorem_0_0_10_classical_limit.png`
- [ ] `verification/plots/theorem_0_0_11_strong_continuity.png` → `theorem_0_0_10_strong_continuity.png`
- [ ] `verification/plots/theorem_0_0_11_hilbert_emergence.png` → `theorem_0_0_10_hilbert_emergence.png`
- [ ] `verification/plots/theorem_0_0_11_decoherence.png` → `theorem_0_0_10_decoherence.png`

### 4.2 Content Updates (search & replace `0.0.11` → `0.0.10`, `0_0_11` → `0_0_10`)

#### Files to Update
- [ ] `docs/Mathematical-Proof-Plan.md`
- [ ] `papers/paper-1-foundations/main.tex`
- [ ] `docs/proofs/foundations/Theorem-0.0.9-Framework-Internal-D4-Derivation.md` (will be renamed, references 0.0.11)
- [ ] `docs/proofs/foundations/Theorem-0.0.10-Framework-Internal-D4-Derivation.md` (references 0.0.11)
- [ ] `docs/proofs/verification-records/Theorem-0.0.10-Multi-Agent-Verification-2025-12-31.md` (will be renamed)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_10.lean` (after rename - update namespace and imports)
- [ ] All renamed Python scripts (internal references)

### 4.3 Verification
```bash
# Should return NO results for OLD 0.0.11 (QM Emergence) after completion
grep -r "Quantum.*Mechanics.*0\.0\.11" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
grep -r "0_0_11.*Quantum" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
```

- [ ] Stage 4 Complete

---

## Stage 5: Rename 0.0.10 → 0.0.9

### 5.1 Files to Rename

#### Proof Documents
- [ ] `docs/proofs/foundations/Theorem-0.0.10-Framework-Internal-D4-Derivation.md` → `Theorem-0.0.9-Framework-Internal-D4-Derivation.md`

#### Verification Records
- [ ] `docs/proofs/verification-records/Theorem-0.0.10-Multi-Agent-Verification-2025-12-31.md` → `Theorem-0.0.9-Multi-Agent-Verification-2025-12-31.md`

#### Lean Files
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_10.lean` → `Theorem_0_0_9.lean`

### 5.2 Content Updates (search & replace `0.0.10` → `0.0.9`, `0_0_10` → `0_0_9`)

#### Files to Update
- [ ] `docs/Mathematical-Proof-Plan.md`
- [ ] `papers/paper-1-foundations/main.tex`
- [ ] `docs/proofs/foundations/Theorem-0.0.0a-Polyhedral-Necessity.md` (references 0.0.10)
- [ ] `docs/proofs/foundations/Theorem-0.0.0a-Polyhedral-Necessity-Applications.md` (references 0.0.10)
- [ ] `docs/proofs/verification-records/Theorem-0.0.10-Multi-Agent-Verification-2025-12-31.md` (will be renamed)
- [ ] `docs/proofs/verification-records/Theorem-0.0.11-Multi-Agent-Verification-2025-12-31.md` (now 0.0.10, references old 0.0.10)
- [ ] `verification/shared/Theorem-0.0.0a-Verification-Report.md` (references 0.0.10)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_9.lean` (after rename - update namespace and imports)
- [ ] Renamed proof document (internal references)

### 5.3 Verification
```bash
# Should return NO results for OLD 0.0.10 (Framework D4) after completion
grep -r "Framework.*D4.*0\.0\.10" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
grep -r "0_0_10.*Framework" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
```

- [x] Stage 5 Complete

---

## Stage 6: Rename 0.0.9 → 0.0.8

### 6.1 Files to Rename

#### Proof Documents
- [ ] `docs/proofs/foundations/Theorem-0.0.9-Emergent-Rotational-Symmetry.md` → `Theorem-0.0.8-Emergent-Rotational-Symmetry.md`

#### Verification Records
- [ ] `docs/proofs/verification-records/Theorem-0.0.9-Multi-Agent-Verification-2025-12-31.md` → `Theorem-0.0.8-Multi-Agent-Verification-2025-12-31.md`

#### Verification Logs
- [ ] `verification/foundations/Theorem-0.0.9-Verification-Log.md` → `Theorem-0.0.8-Verification-Log.md`

#### Lean Files
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_9.lean` → `Theorem_0_0_8.lean`

#### Python Verification Scripts
- [ ] `verification/foundations/theorem_0_0_9_verification.py` → `theorem_0_0_8_verification.py`

#### Plot Files
- [ ] `verification/plots/theorem_0_0_9_asymptotic_suppression.png` → `theorem_0_0_8_asymptotic_suppression.png`
- [ ] `verification/plots/theorem_0_0_9_uv_regime.png` → `theorem_0_0_8_uv_regime.png`
- [ ] `plots/theorem_0_0_9_asymptotic_suppression.png` → `theorem_0_0_8_asymptotic_suppression.png`

### 6.2 Content Updates (search & replace `0.0.9` → `0.0.8`, `0_0_9` → `0_0_8`)

#### Files to Update
- [ ] `docs/Mathematical-Proof-Plan.md`
- [ ] `papers/paper-1-foundations/main.tex`
- [ ] `docs/proofs/foundations/Theorem-0.0.8-Lorentz-Violation-Bounds.md` (will be renamed to 0.0.7, references 0.0.9)
- [ ] `docs/proofs/foundations/Theorem-0.0.9-Framework-Internal-D4-Derivation.md` (now named, references 0.0.9)
- [ ] `docs/proofs/foundations/Theorem-0.0.11-Lorentz-Boost-Emergence.md` (now named, references 0.0.9)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_8.lean` (after rename - update namespace)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_9.lean` (now named, references 0.0.9)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_11.lean` (now named, references 0.0.9)
- [ ] `verification/foundations/issue_7_uv_regime.py` (references 0.0.9)
- [ ] Renamed Python script (internal references)

### 6.3 Verification
```bash
# Should return NO results for OLD 0.0.9 (Rotational Symmetry) after completion
grep -r "Rotational.*Symmetry.*0\.0\.9" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
grep -r "0_0_9.*Rotational" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
```

- [ ] Stage 6 Complete

---

## Stage 7: Rename 0.0.8 → 0.0.7

### 7.1 Files to Rename

#### Proof Documents
- [ ] `docs/proofs/foundations/Theorem-0.0.8-Lorentz-Violation-Bounds.md` → `Theorem-0.0.7-Lorentz-Violation-Bounds.md`

#### Session Logs
- [ ] `docs/verification-prompts/session-logs/Theorem-0.0.8-Verification-Log-2025-12-30.md` → `Theorem-0.0.7-Verification-Log-2025-12-30.md`

#### Lean Files
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_8.lean` → `Theorem_0_0_7.lean`

#### Python Verification Scripts
- [ ] `verification/foundations/theorem_0_0_8_math_verification.py` → `theorem_0_0_7_math_verification.py`
- [ ] `verification/foundations/theorem_0_0_8_physics_verification.py` → `theorem_0_0_7_physics_verification.py`
- [ ] `verification/foundations/theorem_0_0_8_cpt_derivation.py` → `theorem_0_0_7_cpt_derivation.py`
- [ ] `verification/foundations/theorem_0_0_8_uncertainty_analysis.py` → `theorem_0_0_7_uncertainty_analysis.py`

### 7.2 Content Updates (search & replace `0.0.8` → `0.0.7`, `0_0_8` → `0_0_7`)

#### Files to Update
- [ ] `docs/Mathematical-Proof-Plan.md`
- [ ] `papers/paper-1-foundations/main.tex`
- [ ] `docs/proofs/foundations/Theorem-0.0.8-Emergent-Rotational-Symmetry.md` (now named, references old 0.0.8)
- [ ] `docs/proofs/foundations/Theorem-0.0.11-Lorentz-Boost-Emergence.md` (now named, references old 0.0.8)
- [ ] `docs/proofs/foundations/Theorem-0.0.0a-Polyhedral-Necessity-Applications.md` (references 0.0.8)
- [ ] `verification/CLAUDE.md` (references 0.0.8)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_7.lean` (after rename - update namespace)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_8.lean` (now named, references old 0.0.8)
- [ ] `lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_11.lean` (now named, references old 0.0.8)
- [ ] `verification/foundations/theorem_0_0_11_verification.py` (now named, references 0.0.8)
- [ ] All 4 renamed Python scripts (internal references)

### 7.3 Verification
```bash
# Should return NO results for OLD 0.0.8 (Lorentz Violation) after completion
grep -r "Lorentz.*Violation.*0\.0\.8" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
grep -r "0_0_8.*Lorentz.*Violation" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
```

- [ ] Stage 7 Complete

---

## Stage 8: Final Cleanup and Verification

### 8.1 Clean Lean Build Artifacts
```bash
cd lean
rm -rf .lake/build/lib/lean/ChiralGeometrogenesis/Foundations/Theorem_0_0_{7,8,9,10,11,12,13,14}.*
rm -rf .lake/build/ir/ChiralGeometrogenesis/Foundations/Theorem_0_0_{7,8,9,10,11,12,13,14}.*
```

### 8.2 Rebuild Lean Project
```bash
cd lean
lake build
```
- [ ] Lean builds successfully

### 8.3 Update Documentation Files
- [ ] `docs/proofs/CLAUDE.md` - update directory listing
- [ ] `CLAUDE.md` (root) - if needed

### 8.4 Final Verification
```bash
# Verify NO orphaned old numbers exist
grep -r "Theorem.0\.0\.14" docs/ papers/ lean/ChiralGeometrogenesis/ verification/
# Should return 0 results

# Verify new numbering is consistent
grep -c "0\.0\.7" docs/Mathematical-Proof-Plan.md  # Should show Lorentz Violation
grep -c "0\.0\.13" docs/Mathematical-Proof-Plan.md  # Should show Tannaka
```

### 8.5 Compile Paper
```bash
cd papers/paper-1-foundations
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```
- [ ] Paper compiles without errors

### 8.6 Git Commit
```bash
git add -A
git commit -m "Renumber theorems 0.0.8-0.0.14 → 0.0.7-0.0.13 to close numbering gap

- Renamed all proof documents, Lean files, and verification scripts
- Updated all cross-references in ~30 files
- Rebuilt Lean project successfully
- Paper compiles correctly

🤖 Generated with Claude Code"
```

- [ ] Stage 8 Complete

---

## Summary Checklist

| Stage | Description | Status |
|-------|-------------|--------|
| 1 | Rename 0.0.14 → 0.0.13 (Tannaka) | ✅ |
| 2 | Rename 0.0.13 → 0.0.12 (Categorical) | ✅ |
| 3 | Rename 0.0.12 → 0.0.11 (Lorentz Boost) | ✅ |
| 4 | Rename 0.0.11 → 0.0.10 (QM Emergence) | ✅ |
| 5 | Rename 0.0.10 → 0.0.9 (Framework D4) | ✅ |
| 6 | Rename 0.0.9 → 0.0.8 (Rotational Sym) | ✅ |
| 7 | Rename 0.0.8 → 0.0.7 (Lorentz Violation) | ✅ |
| 8 | Final cleanup and verification | ✅ |

---

## Estimated Time

- **Per stage:** 15-30 minutes (depending on cross-reference count)
- **Total:** 2-4 hours for complete renumbering
- **Recommended:** Complete in one session to avoid inconsistent state

---

## Rollback Plan

If issues are encountered mid-way:
```bash
git checkout -- .
git clean -fd
```

This will restore all files to the last committed state.
