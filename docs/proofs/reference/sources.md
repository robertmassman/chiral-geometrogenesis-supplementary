# Reference Data Sources Index

**Purpose:** Master index of all external data sources used in Chiral Geometrogenesis proofs.
**Last Updated:** 2025-12-13

---

## Quick Reference

| File | Contents | Last Updated |
|------|----------|--------------|
| [pdg-particle-data.md](pdg-particle-data.md) | Particle masses, decay rates, lifetimes | 2025-12-13 |
| [cosmological-constants.md](cosmological-constants.md) | Planck scale, $G$, $H_0$, cosmological params | 2025-12-13 |
| [coupling-constants.md](coupling-constants.md) | $\alpha_{em}$, $\alpha_s$, Yukawas, CKM | 2025-12-13 |

---

## Primary Sources

### 1. Particle Data Group (PDG)

**Authority for:** Particle masses, decay rates, coupling constants, CKM parameters

| Resource | URL | Version | Access Date |
|----------|-----|---------|-------------|
| PDG Review | https://pdg.lbl.gov | 2024 edition | 2025-12-13 |
| PDG Live (quarks) | https://pdglive.lbl.gov/DataBlock.action?node=Q123SM | Live | 2025-12-13 |
| PDG Summary Tables | https://pdg.lbl.gov/2024/tables/contents_tables.html | 2024 | 2025-12-13 |

**Citation:**
```
R.L. Workman et al. (Particle Data Group), Phys. Rev. D 110, 030001 (2024)
```

---

### 2. CODATA / NIST

**Authority for:** Fundamental physical constants ($c$, $\hbar$, $G$, $\alpha$, Planck units)

| Resource | URL | Version | Access Date |
|----------|-----|---------|-------------|
| CODATA Constants | https://physics.nist.gov/cuu/Constants/ | 2018 (current) | 2025-12-13 |

**Citation:**
```
E. Tiesinga et al., CODATA 2018 values, Rev. Mod. Phys. 93, 025010 (2021)
```

---

### 3. Planck Collaboration

**Authority for:** Cosmological parameters ($H_0$, $\Omega$, $\eta_B$, $n_s$, $r$)

| Resource | URL | Version | Access Date |
|----------|-----|---------|-------------|
| Planck 2018 Results | arXiv:1807.06209 | 2018 | 2025-12-13 |
| Planck Legacy Archive | https://pla.esac.esa.int/ | 2018 | 2025-12-13 |

**Citation:**
```
Planck Collaboration, A&A 641, A6 (2020) [arXiv:1807.06209]
```

---

### 4. FLAG (Flavour Lattice Averaging Group)

**Authority for:** Lattice QCD averages (quark masses, $\alpha_s$, decay constants)

| Resource | URL | Version | Access Date |
|----------|-----|---------|-------------|
| FLAG 2024 | arXiv:2411.04268 | 2024 | 2025-12-13 |
| FLAG Website | https://flag.unibe.ch/ | Live | 2025-12-13 |

**Citation:**
```
FLAG Collaboration, arXiv:2411.04268 (2024)
```

---

### 5. Other Key Sources

| Source | Authority For | Citation | Used In |
|--------|---------------|----------|---------|
| Budapest-Wuppertal | QCD phase transition $T_c$ | PLB 730, 99 (2014) | Theorems 2.1.2, 5.2.6 |
| BICEP/Keck | Tensor-to-scalar ratio $r$ | PRL 127, 151301 (2021) | Theorem 5.2.1 |
| Muon g-2 | $(g-2)_\mu$ | PRL 131, 161802 (2023) | Theorem 3.2.2 |
| Super-Kamiokande | Proton lifetime | PRD 95, 012004 (2017) | Theorem 4.1.1 |
| DESI 2024 | Neutrino mass bounds | arXiv:2404.03002 | Corollary 3.1.3 |

---

## Usage Guidelines

### When Adding New Data

1. **Check if data exists** in one of the three main files first
2. **Add to appropriate file** with:
   - Value and uncertainty
   - Source with citation
   - "Used In" column listing theorems
3. **Update this index** if adding a new source

### Citing in Proofs

Reference format for proofs:
```markdown
The pion decay constant $f_\pi = 92.1 \pm 0.6$ MeV [PDG 2024, reference-data/pdg-particle-data.md §3.1].
```

### Version Control

When updating values:
1. Update the value in the appropriate reference file
2. Add entry to "Changelog" section of that file
3. Grep proofs for uses of that value to check consistency

---

## Data Not Yet Indexed

The following data types appear in proofs but may need future expansion:

- [ ] Lattice QCD simulation parameters (lattice spacing, volumes)
- [ ] Historical measurements for comparison
- [ ] Collider-specific results (LHC run specifications, luminosities)
- [ ] Astrophysical data (SNe Ia, BAO, CMB power spectra)

---

## Changelog

| Date | Change | Files Affected |
|------|--------|----------------|
| 2025-12-13 | Initial creation of reference-data system | All 4 files |
