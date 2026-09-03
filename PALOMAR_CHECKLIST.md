# Palomar Submission Master Priority Queue: Repo 2

All 24 theorem packages have completed pre-flight verification audits.
- **Tier-1 Verified Submission Queue**: 17 research-grade packages, 100% verified (0 custom axioms, 0 `sorry`), with dedicated immutable 40-character Git commit SHAs.
- **High-Value Research Scaffolds**: 4 advanced theorem packages with clearly isolated, minimal mathematical axioms/stubs representing deep unformalized prerequisites (`alon_boppana` pruned as redundant with Repo 3; `blichfeldts_theorem`, `jungs_theorem`, `gessel_viennot`, and `cayleys_formula` promoted to Tier-1).
- **Retired Candidates**: 3 packages explicitly crossed off early due to elementary reductions, tautological projections, or naked scalar arithmetic (`cyclic_shift` un-retired and upgraded to `circulant_spectral_theory`).

### Submission Settings (`submit.palomar-registry.org`):
- **Repository**: `sneed-and-feed/lean-theorems-2`
- **Git Commit SHA**: `git rev-parse HEAD` (run `git push origin main` first)
- **Comparator Path**: `comparator.json` *(or `palomar/<slug>/comparator.json`)*
- **Existing Palomar ID**: *(leave blank)*
- **Relationship**: `Maintainer` / `Author`

---

## 🚀 Tier-1 Verified Submission Queue (100% Verified, 0 Axioms, Research-Grade)

| # | Theorem Title | Slug | Dedicated Commit SHA to Enter | Mathematical Domain | Verified Declarations |
| :---: | :--- | :--- | :--- | :--- | :---: |
| **1** | **Stanley's $\mathfrak{sl}(2)$ Representation Proof of Strong Sperner for $L(m, n)$** | `stanley_sl2` | `31d6c9c2efc5992934bd52a8210655280e151827` | Lie Algebra Poset Theory / Lefschetz | 5 theorems |
| **2** | **Vizing's Theorem on Edge Colorings & König's Line Coloring Theorem** | `vizings_theorem` | `bb2c7961330b22dde6b0321c21abbc907fcd69ef` | Graph Theory / Edge Chromatics | 5 theorems |
| **3** | **The Birkhoff–von Neumann Theorem on Doubly Stochastic Matrices** | `birkhoff_von_neumann` | `5d9fa1f88ce796c19dc2b5f64d2cce50aebe7b8d` | Polyhedral Combinatorics / Matchings | 5 theorems |
| **4** | **The Ihara–Bass Determinantal Formula for Graphs** | `ihara_bass` | `fa77e538f26eef2ddba4e050b1613642329624a6` | Algebraic Graph Theory / Block Schur | 7 theorems |
| **5** | **The Ihara Zeta Function and Hashimoto Edge Adjacency Matrix** | `ihara_zeta` | `643ad229d7530e326aa63b058a1e2da71d0c833c` | Spectral Graph Theory / Zeta Functions | 7 theorems |
| **6** | **MacMahon's Master Theorem for Products of Linear Forms** | `macmahons_master_theorem` | `6548d0c0a61ffd49a3941b1b2f6f159ec9fc638b` | Enumerative Combinatorics / Power Series | 1 theorem |
| **7** | **Fisher's Inequality for Balanced Incomplete Block Designs ($b \ge v$)** | `fishers_inequality` | `8f84d6bb06a147a315a7e1ce5f2c80d65616f62f` | Combinatorial Design Theory / Gramians | 4 theorems |
| **8** | **The Kőnig–Egerváry Theorem on Matchings and Vertex Covers** | `konig_matching` | `c464c8885b628707bd5edeb708dcfb1568bd09eb` | Combinatorial Optimization / Min-Max | 6 theorems |
| **9** | **Sperner's Theorem on Antichains and the LYM Inequality** | `sperner_antichain` | `0af07933dff2383f04d810032c143d452a992e7d` | Extremal Combinatorics / Posets | 3 theorems |
| **10** | **Turán's Theorem in Extremal Graph Theory & Mantel's Theorem** | `turans_theorem` | `912b99dc4256e8f88f789e6312e2e2d6a2306dd3` | Extremal Graph Theory / Turán Graphs | 4 theorems |
| **11** | **Van der Waerden's Theorem on Arithmetic Progressions** | `van_der_waerden` | `f425e8014abfd8e25362845c170f56b92aa19607` | Ramsey Theory / Additive Combinatorics | 2 theorems |
| **12** | **Blichfeldt's Theorem and Minkowski Convex Body Bounds** | `blichfeldts_theorem` | `e8dfe475169caae29da9285e99d2f0587a3d953a` | Convex Geometry / Geometry of Numbers | 3 theorems |
| **13** | **Jung's Theorem on Circumscribed Euclidean Spheres** | `jungs_theorem` | `e8dfe475169caae29da9285e99d2f0587a3d953a` | Convex & Metric Geometry / Discrete Geometry | 3 theorems |
| **14** | **The Lindström–Gessel–Viennot (LGV) Lemma** | `gessel_viennot` | `e8dfe475169caae29da9285e99d2f0587a3d953a` | Enumerative Combinatorics / Determinantal Lattice Paths | 4 theorems |
| **15** | **Cayley's Tree Formula and Prüfer Sequence Bijection** | `cayleys_formula` | `f7fd6e340dbf20387ca793a38ea8f37bc44367ef` | Enumerative Combinatorics / Graph Theory / Trees | 2 theorems |
| **16** | **Spectral Theory of Circulant Matrices and Discrete Fourier Analysis** | `circulant_spectral_theory` | `e1ba282ba3757bb5eae03e6b8e52732f32b53e45` | Spectral Matrix Theory / Fourier Analysis | 4 theorems |
| **17** | **The Hoffman–Singleton Moore Graph Classification Theorem** | `hoffman_singleton` | `6834562ebef5c336e3feabc2470a6ca92b4869da` | Spectral Graph Theory / Strongly Regular Graphs / Moore Graphs | 17 theorems |

---

## 🔬 High-Value Research Scaffolds (Explicitly Isolated Minimal Axioms)

| # | Theorem Title | Slug | Dedicated Commit SHA | Minimal Missing Prerequisites | Verified Declarations |
| :---: | :--- | :--- | :--- | :--- | :---: |
| **1** | **Brooks' Theorem on Graph Colorings** | `brooks_theorem` | `1a515aed2661359caea61336c6ac338dedd8d6ec` | 1 axiom: `exists_lovasz_ordering` (2-connected DFS/BFS ordering) | 3 theorems |
| **2** | **Algebraic Foundations of the Matrix-Tree Theorem** | `matrix_tree_theorem` | `aa6038156b35a8604179a199b619ebca4b0d3e33` | 2 axioms: Binet–Cauchy determinant expansions on Laplacians | 3 theorems |
| **3** | **Menger's Theorem and Whitney's Connectivity Duality** | `mengers_theorem` | `8de37823496e5548d7a05b9d9952799101aef2f0` | 2 axioms: Max-flow min-cut path extraction inductions | 5 theorems |
| **4** | **Ramanujan Tau Function and Congruence Modulo 691** | `ramanujan_tau` | `b621759da8099964bd50f49d57eef1c4b393058c` | Isolated modular forms hypothesis: `M_12_is_span` ($\dim M_{12} = 2$ over $\mathbb{Q}$) and `F_exists` (existence of weight-12 cusp/Eisenstein eigenform) | 2 theorems |

---

## 🛑 Retired Candidates (Did Not Meet Research Floor / Anti-Pattern Collisions)

| Slug | Core Finding & Reason for Early Retirement | Status |
| :--- | :--- | :---: |
| `prefix_sparsity` | **AP-18, AP-26**: Elementary tree arithmetic calculations ($p^r \cdot p^{d-r} \cdot p^{d-r} / p^{2d} = 1/p^r$) and $1 - 7/8 = 1/8$. | [-] **RETIRED** |
| `cyclic_shift` | **UN-RETIRED**: Upgraded to research-grade `circulant_spectral_theory` (full spectral theory of circulants and DFT). | [x] **PROMOTED** |
| `rsk_bijection` | **AP-01**: Tautological hypothesis projection theorems (`h_schensted → h_schensted`). | [-] **RETIRED** |
| `hoffman_singleton` | **UN-RETIRED**: Upgraded to authentic graph-theoretic and spectral bridge on genuine `SimpleGraph` carriers (`moore_is_srg`, `moore_adjMatrix_eq`, `moore_graph_degree_classification`). | [x] **PROMOTED** |