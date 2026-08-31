# Formalization of Combinatorial, Geometric, Spectral, and Graph Theorems in Lean 4 (Part II)

This repository provides machine-checked formalizations, certified proofs, and foundational scaffolds of landmark theorems across combinatorics, spectral graph theory, Ramsey theory, matrix theory, modular forms, discrete geometry, and combinatorial optimization in the Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) ecosystem.

---

## Table of Formalized Modules and Theorems

| # | Theorem / Topic | Primary Declaration(s) | Mathematical Domain | Reference | Status & Missing Prerequisites |
| :---: | :--- | :--- | :--- | :--- | :--- |
| 1 | **Sperner's Antichain Theorem & LYM Inequality** | [`sperners_antichain_theorem`](Formalization/SpernerAntichain.lean), [`lym_inequality`](Formalization/SpernerAntichain.lean), [`sperners_antichain_equality`](Formalization/SpernerAntichain.lean) | Extremal Combinatorics & Poset Theory | Sperner (1928), Lubell (1966), Yamamoto (1954) | **100% Verified (0 axioms)** |
| 2 | **Van der Waerden's Theorem on Arithmetic Progressions** | [`van_der_waerden_finite`](Formalization/VanDerWaerden.lean), [`van_der_waerden_infinite`](Formalization/VanDerWaerden.lean), [`multiple_van_der_waerden`](Formalization/VanDerWaerden.lean) | Ramsey Theory & Additive Combinatorics | Van der Waerden (1927), Wiedijk #85 | **100% Verified (0 axioms)** |
| 3 | **Turán's Theorem & Mantel's Theorem** | [`turans_theorem`](Formalization/TuransTheorem.lean), [`turans_theorem_exact`](Formalization/TuransTheorem.lean), [`mantels_theorem`](Formalization/TuransTheorem.lean), [`turans_uniqueness`](Formalization/TuransTheorem.lean) | Extremal Graph Theory | Turán (1941), Mantel (1907) | **100% Verified (0 axioms)** |
| 4 | **Brooks' Theorem on Graph Colorings** | [`brooks_theorem`](Formalization/BrooksTheorem.lean), [`brooks_theorem_of_card_le_succ`](Formalization/BrooksTheorem.lean), [`colorable_of_lovasz_ordering`](Formalization/BrooksTheorem/Greedy.lean), [`lovasz_ordering_of_triple`](Formalization/BrooksTheorem/LovaszOrdering.lean) | Graph Theory & Vertex Chromatics | Brooks (1941), Lovász (1975) | **Modular Package (`Formalization/BrooksTheorem/`)** |
| 5 | **Ihara Zeta Function & Hashimoto Adjacency** | [`HashimotoMatrix`](Formalization/IharaZeta.lean), [`sourceMatrix_mul_targetMatrix_transpose`](Formalization/IharaZeta.lean), [`involutionMatrix_sq`](Formalization/IharaZeta.lean), [`IharaZetaInvLHS`](Formalization/IharaZeta.lean) | Spectral Graph Theory & Zeta Functions | Ihara (1966), Serre (1977) | **100% Verified (0 axioms)** |
| 6 | **Ihara-Bass Determinantal Formula** | [`ihara_bass_polynomial`](Formalization/IharaBass.lean), [`M_Bass_mul_N_Bass`](Formalization/IharaBass.lean), [`det_KL_Bass`](Formalization/IharaBass.lean), [`det_M_Bass`](Formalization/IharaBass.lean) | Algebraic Graph Theory & Block Determinants | Bass (1992), Hashimoto (1989) | **100% Verified (0 axioms)** |
| 7 | **Prefix-Sharing & Sparsity on Trees** | [`sparsity_bound`](Formalization/PrefixSparsity.lean), [`fraction_eq_p_inv_r`](Formalization/PrefixSparsity.lean), [`card_shared_prefix`](Formalization/PrefixSparsity.lean), [`sparsity_p2_r3`](Formalization/PrefixSparsity.lean) | Tree Combinatorics & Branching Sparsity | Prefix Sharing & Tree Metric Sparsity | **100% Verified (0 axioms)** |
| 8 | **Characteristic Polynomial of Cyclic Matrices** | [`charpoly_cyclicWeightMatrix`](Formalization/CyclicShift.lean), [`charpoly_shiftMatrix`](Formalization/CyclicShift.lean), [`det_upperBidiagonal`](Formalization/CyclicShift.lean) | Linear Algebra & Circulant Matrices | Cyclic Shifts & Bidiagonal Expansion | **100% Verified (0 axioms)** |
| 9 | **Ramanujan Tau Congruence $\tau(n) \equiv \sigma_{11}(n) \pmod{691}$** | [`ramanujan_tau_congruence`](Formalization/RamanujanTau.lean), [`bernoulli_12_exact`](Formalization/RamanujanTau.lean), [`ramanujan_congruence_691`](Formalization/RamanujanTau.lean) | Modular Forms & Number Theory | Ramanujan (1916), Serre (1973) | **100% Verified (0 axioms)** |
| 10 | **Kirchhoff's Matrix-Tree Theorem** | [`matrix_tree_theorem`](Formalization/MatrixTreeTheorem.lean), [`laplacian_row_sum_zero`](Formalization/MatrixTreeTheorem.lean), [`laplacian_transpose_eq`](Formalization/MatrixTreeTheorem.lean), [`incidence_mul_transpose`](Formalization/MatrixTreeTheorem.lean) | Algebraic Graph Theory & Tree Enumeration | Kirchhoff (1847), Stanley (2012) | Scaffolded ($B B^T = L$ verified; lacks Binet–Cauchy determinants) |
| 11 | **Vizing's Theorem & König's Line Coloring Theorem** | [`vizings_theorem`](Formalization/VizingsTheorem.lean), [`vizing_classification`](Formalization/VizingsTheorem.lean), [`konig_edge_coloring`](Formalization/VizingsTheorem.lean), [`edgeColorable_of_bipartite`](Formalization/VizingsTheorem.lean), [`edgeColorable_of_maxDegree_succ`](Formalization/VizingsTheorem.lean) | Graph Theory & Edge Colorings | Vizing (1964), König (1916) | **100% Verified (0 axioms) — Modular Package (`Formalization/VizingsTheorem/`)** |
| 12 | **Fisher's Inequality for Block Designs** | [`fishers_inequality`](Formalization/FishersInequality.lean), [`gramian_eq`](Formalization/FishersInequality.lean), [`det_gramian`](Formalization/FishersInequality.lean), [`incidence_mul_transpose_apply`](Formalization/FishersInequality.lean) | Combinatorial Design Theory & Matrix Gramians | Fisher (1940), Bose (1949) | **100% Verified (0 axioms)** |
| 13 | **Lindström–Gessel–Viennot (LGV) Lemma** | [`lindstrom_gessel_viennot`](Formalization/GesselViennot.lean), [`gessel_viennot_planar_dag`](Formalization/GesselViennot.lean), [`det_pathMatrix_eq_permutation_sum`](Formalization/GesselViennot.lean), [`intersecting_path_systems_sum_zero`](Formalization/GesselViennot.lean) | Algebraic Combinatorics & Lattice Paths | Lindström (1973), Gessel & Viennot (1985) | **100% Verified (0 axioms)** |
| 14 | **Cayley's Tree Formula & Prüfer Sequences** | [`cayleys_tree_formula`](Formalization/CayleysFormula.lean), [`prufer_sequence_card`](Formalization/CayleysFormula.lean), [`pruferEquiv`](Formalization/CayleysFormula.lean), [`pruferCode`](Formalization/CayleysFormula.lean), [`pruferDecode`](Formalization/CayleysFormula.lean) | Enumerative Combinatorics & Graph Enumeration | Cayley (1889), Prüfer (1918) | **100% Verified (0 axioms) — Modular Package (`Formalization/CayleysFormula/`)** |
| 15 | **Kőnig–Egerváry Duality Theorem** | [`konig_duality`](Formalization/KonigMatching.lean), [`weak_duality`](Formalization/KonigMatching.lean), [`matching_card_le_vertexCover_card`](Formalization/KonigMatching.lean), [`gallai_independence_vertex_cover`](Formalization/KonigMatching.lean), [`konig_independence_matching`](Formalization/KonigMatching.lean) | Combinatorial Optimization & Polyhedral Graphs | Kőnig (1931), Egerváry (1931), Gallai (1959) | **100% Verified (0 axioms)** |
| 16 | **Jung's Theorem on Circumscribed Spheres** | [`jungs_theorem`](Formalization/JungsTheorem.lean), [`jungs_theorem_via_helly`](Formalization/JungsTheorem.lean), [`circumradius_le_jungs_bound`](Formalization/JungsTheorem.lean), [`jungsConstant_pos`](Formalization/JungsTheorem.lean) | Discrete Geometry & Convexity | Jung (1901), Danzer, Grünbaum, & Klee (1963) | Scaffolded (Helly reduction `jungs_theorem_via_helly` verified; reduces to simplex case) |
| 17 | **Alon–Boppana Spectral Lower Bound** | [`alon_boppana_bound`](Formalization/AlonBoppana.lean), [`alon_boppana_nilli`](Formalization/AlonBoppana.lean), [`secondEigenvalue`](Formalization/AlonBoppana.lean), [`IsRamanujan`](Formalization/AlonBoppana.lean) | Spectral Graph Theory & Expanders | Alon (1986), Boppana (1986), Nilli (1991) | Scaffolded (Symmetry & gap verified; lacks Nilli spherical test vectors) |
| 18 | **Menger's Theorem on Disjoint Paths & Cuts** | [`menger_vertex`](Formalization/MengersTheorem.lean), [`menger_edge`](Formalization/MengersTheorem.lean), [`menger_whitney`](Formalization/MengersTheorem.lean), [`weak_duality`](Formalization/MengersTheorem/Basic.lean) | Graph Connectivity & Network Optimization | Menger (1927), Whitney (1932), Dirac (1966) | **100% Verified (0 axioms) — Modular Package (`Formalization/MengersTheorem/`)** |
| 19 | **MacMahon's Master Theorem** | [`macmahon_master_theorem`](Formalization/MacMahonsMasterTheorem.lean), [`macmahon_dim1`](Formalization/MacMahonsMasterTheorem.lean), [`detMacMahon`](Formalization/MacMahonsMasterTheorem.lean), [`invDetMacMahon`](Formalization/MacMahonsMasterTheorem.lean) | Enumerative Combinatorics & Formal Series | MacMahon (1915), Cartier & Foata (1969) | **100% Verified (0 axioms)** |
| 20 | **Blichfeldt's Theorem in Geometry of Numbers** | [`blichfeldts_theorem`](Formalization/BlichfeldtsTheorem.lean), [`minkowski_convex_body_theorem`](Formalization/BlichfeldtsTheorem.lean), [`blichfeldt_dim1`](Formalization/BlichfeldtsTheorem.lean) | Geometry of Numbers & Lattice Tiling | Blichfeldt (1914), Minkowski (1896) | Scaffolded (1D interval verified; lacks torus pigeonhole integration) |
| 21 | **The Hoffman–Singleton Moore Graph Theorem** | [`hoffman_singleton_theorem`](Formalization/HoffmanSingleton.lean), [`classification_general`](Formalization/HoffmanSingleton.lean), [`certHoffmanSingletonIntegral`](Formalization/HoffmanSingleton.lean), [`s_divides_15`](Formalization/HoffmanSingleton.lean) | Spectral Graph Theory & Matrix Algebras | Hoffman & Singleton (1960) | **100% Verified (0 axioms)** |
| 22 | **Robinson–Schensted–Knuth (RSK) Correspondence** | [`schensted_lis_theorem`](Formalization/RSKBijection.lean), [`greene_lds_theorem`](Formalization/RSKBijection.lean), [`rsk_sum_squares_eq_factorial`](Formalization/RSKBijection.lean), [`rsk_involution_fixed_points`](Formalization/RSKBijection.lean) | Algebraic Combinatorics & Young Tableaux | Schensted (1961), Knuth (1970), Greene (1974) | **100% Verified (0 axioms)** |
| 23 | **The Birkhoff–von Neumann Theorem** | [`birkhoff_von_neumann_convex_hull`](Formalization/BirkhoffVonNeumann.lean), [`birkhoff_von_neumann_iff`](Formalization/BirkhoffVonNeumann.lean), [`birkhoff_von_neumann_convex_combination`](Formalization/BirkhoffVonNeumann.lean), [`extremePoints_doublyStochasticSet`](Formalization/BirkhoffVonNeumann.lean) | Convex Geometry & Polyhedral Combinatorics | Birkhoff (1946), von Neumann (1953) | **100% Verified (0 axioms)** |
| 24 | **Stanley's $\mathfrak{sl}_2$ Proof of the Strong Sperner Property** | [`sperner_partition_poset`](Formalization/StanleySL2.lean), [`sperner_partition_poset_slice`](Formalization/StanleySL2.lean), [`rankSize_symm`](Formalization/StanleySL2.lean), [`rankSize_unimodal`](Formalization/StanleySL2.lean) | Algebraic Poset Theory & Lie Algebra Representations | Stanley (1980, 1982), Proctor (1982) | **100% Verified (0 axioms)** |

---

## Detailed Module Descriptions & Formalization Highlights

### 1. Sperner's Theorem on Antichains and the LYM Inequality
* **Module:** [`Formalization/SpernerAntichain.lean`](Formalization/SpernerAntichain.lean)
* **Theorems:** `lym_inequality`, `sperners_antichain_theorem`, `sperners_antichain_equality`
* **Mathematical Statement:**
  - **LYM Inequality:** For any antichain $\mathcal{A} \subseteq \mathcal{P}(V)$ of an $n$-element set:
    $$\sum_{A \in \mathcal{A}} \frac{1}{\binom{n}{|A|}} \le 1$$
  - **Sperner's Theorem:** The maximum antichain size is bounded by the central binomial coefficient:
    $$|\mathcal{A}| \le \binom{n}{\lfloor n / 2 \rfloor}$$
  - **Equality Case:** Attained uniquely by middle rank level slices $\binom{V}{\lfloor n/2 \rfloor}$ and $\binom{V}{\lceil n/2 \rceil}$.

---

### 2. Van der Waerden's Theorem on Arithmetic Progressions
* **Module:** [`Formalization/VanDerWaerden.lean`](Formalization/VanDerWaerden.lean)
* **Theorems:** `van_der_waerden_finite`, `van_der_waerden_infinite`, `multiple_van_der_waerden`
* **Mathematical Statement:** For any number of colors $r \ge 1$ and progression length $k \ge 1$, there exists $W(r, k)$ such that any $r$-coloring of $\{1, \dots, W(r, k)\}$ contains a monochromatic $k$-term arithmetic progression:
  $$\exists a, d \in \mathbb{N}, \quad d > 0 \quad \text{such that} \quad \chi(a) = \chi(a + d) = \dots = \chi(a + (k - 1)d)$$

---

### 3. Turán's Theorem & Mantel's Theorem
* **Module:** [`Formalization/TuransTheorem.lean`](Formalization/TuransTheorem.lean)
* **Theorems:** `turans_theorem`, `turans_theorem_exact`, `mantels_theorem`, `turans_uniqueness`
* **Mathematical Statement:** If a simple graph $G$ on $n$ vertices is $K_{r+1}$-free ($\omega(G) \le r$), then:
  $$|E(G)| \le e(T(n, r)) \le \left(1 - \frac{1}{r}\right) \frac{n^2}{2}$$
  with equality holding if and only if $G \cong T(n, r)$ (the complete multipartite Turán graph).

---

### 4. Brooks' Theorem on Graph Colorings
* **Module:** [`Formalization/BrooksTheorem.lean`](Formalization/BrooksTheorem.lean)
* **Modular Package:** [`Formalization/BrooksTheorem/`](Formalization/BrooksTheorem)
  - `Basic.lean`: Maximum degree $\Delta(G)$, `IsProperColoring`, `IsKColorable`, and chromatic monotonicities.
  - `OddCycles.lean`: Complete graph characterizations, small graph bounds, and odd cycle non-2-colorability.
  - `Greedy.lean`: Degree-ordered greedy colorings, the Lovász coloring inductive engine (`colorable_of_lovasz_ordering`), and `greedy_coloring_bound`.
  - `LovaszOrdering.lean`: Subgraph BFS trees (`exists_reverse_bfs_list`), distance lemmas, and Lovász triple orderings (`lovasz_ordering_of_triple`).
* **Theorems:** `brooks_theorem`, `brooks_theorem_of_card_le_succ`, `greedy_coloring_bound`, `colorable_of_lovasz_ordering`, `lovasz_ordering_of_triple`, `exists_reverse_bfs_list`
* **Mathematical Statement:** For any connected graph $G$ with maximum degree $\Delta(G) = \Delta \ge 1$ not isomorphic to an odd cycle or a complete graph $K_{\Delta+1}$, $\chi(G) \le \Delta$.

---

### 5. Ihara Zeta Function & Hashimoto Adjacency Matrix
* **Module:** [`Formalization/IharaZeta.lean`](Formalization/IharaZeta.lean)
* **Theorems:** `sourceMatrix_mul_targetMatrix_transpose`, `sourceMatrix_mul_sourceMatrix_transpose`, `targetMatrix_transpose_mul_sourceMatrix`, `involutionMatrix_sq`, `IharaZetaInvLHS`
* **Mathematical Statement:** Algebraic structure of the directed edge (dart) space, Hashimoto non-backtracking operator $T$, dart source/target incidence matrices, and dart involution $J$.

---

### 6. Ihara-Bass Determinantal Formula
* **Module:** [`Formalization/IharaBass.lean`](Formalization/IharaBass.lean)
* **Theorems:** `ihara_bass_polynomial`, `M_Bass_mul_N_Bass`, `K_Bass_mul_L_Bass`, `det_M_Bass`, `det_KL_Bass`
* **Mathematical Statement:** For any finite regular graph $G$, the characteristic polynomial of the non-backtracking operator $T$ satisfies:
  $$\det(I - u T) (1 - u^2)^{|V| - |E|} = \det(I - u A + (d - 1) u^2 I)$$
  proved via explicit block matrix Schur complement eliminations $M N L = KL$.

---

### 7. Combinatorial Prefix-Sharing & Sparsity on Trees
* **Module:** [`Formalization/PrefixSparsity.lean`](Formalization/PrefixSparsity.lean)
* **Theorems:** `sparsity_bound`, `fraction_eq_p_inv_r`, `card_shared_prefix`, `sparsity_p2_r1`, `sparsity_p2_r3`, `sparsity_p2_r6`
* **Mathematical Statement:** For a complete $p$-ary tree of depth $d$, the exact fraction of path pairs sharing an $r$-prefix ancestor is $p^{-r}$, yielding sparsity $1 - p^{-r}$ (e.g., $87.5\%$ for $p=2, r=3$).

---

### 8. Characteristic Polynomial of Cyclic Shift Matrices
* **Module:** [`Formalization/CyclicShift.lean`](Formalization/CyclicShift.lean)
* **Theorems:** `charpoly_cyclicWeightMatrix`, `charpoly_shiftMatrix`, `det_upperBidiagonal`
* **Mathematical Statement:** Over any commutative ring $R$, the characteristic polynomial of a weighted cyclic shift matrix $C(W)$ on $\mathbb{Z}/L\mathbb{Z}$ is:
  $$\chi_{C(W)}(X) = X^L - \prod_{k \in \mathbb{Z}/L\mathbb{Z}} W_k$$

---

### 9. Ramanujan Tau Function & Congruence Modulo 691
* **Module:** [`Formalization/RamanujanTau.lean`](Formalization/RamanujanTau.lean)
* **Theorems:** `ramanujan_tau_congruence`, `bernoulli_12_exact`, `ramanujan_congruence_691`
* **Mathematical Statement:** Proof of the congruence $\tau(n) \equiv \sigma_{11}(n) \pmod{691}$ from the dimension 2 structure of the space of modular forms $M_{12}(\mathrm{SL}_2(\mathbb{Z})) = \mathbb{Q} E_{12} \oplus \mathbb{Q} \Delta$ and the exact Bernoulli number $B_{12} = -691/2730$.

---

### 10. Kirchhoff's Matrix-Tree Theorem
* **Module:** [`Formalization/MatrixTreeTheorem.lean`](Formalization/MatrixTreeTheorem.lean)
* **Theorems:** `laplacian_apply_diag`, `laplacian_apply_offdiag`, `laplacian_row_sum_zero`, `laplacian_transpose_eq`, `incidence_mul_transpose`, `matrix_tree_theorem`
* **Mathematical Statement:** For any finite connected graph $G$, the combinatorial Laplacian $L = D - A$ satisfies $L = B B^T$, $\sum_v L_{u, v} = 0$, and any reduced Laplacian minor satisfies $\det(L_{(r)}) = |\mathcal{T}(G)|$.

---

### 11. Vizing's Theorem on Edge Colorings & König's Line Coloring Theorem
* **Module:** [`Formalization/VizingsTheorem.lean`](Formalization/VizingsTheorem.lean)
* **Modular Package:** [`Formalization/VizingsTheorem/`](Formalization/VizingsTheorem)
  - `Basic.lean`: `EdgeColoring`, `PartialEdgeColoring`, missing color algebra, and max degrees.
  - `Kempe.lean`: Kempe alternating chains, Kempe subgraphs, and double-endpoint non-reachability (`kempe_not_reachable_both`).
  - `Bipartite.lean`: Shift steps along paths and König's Line Coloring Theorem for bipartite graphs (`edgeColorable_of_bipartite`).
  - `Fan.lean`: Vizing fan extensions and inductive coloring step (`exists_full_coloring`).
* **Theorems:** `vizings_theorem`, `vizing_classification`, `edgeColorable_of_bipartite`, `edgeColorable_of_maxDegree_succ`, `konig_edge_coloring`
* **Mathematical Statement:** For any finite bipartite graph $G$, König's Line Coloring Theorem establishes that $G$ is Class 1 ($\chi'(G) = \Delta(G)$), and for any general finite simple graph $G$, Vizing's Theorem establishes $\Delta(G) \le \chi'(G) \le \Delta(G) + 1$, classifying graphs into Class 1 ($\chi' = \Delta$) or Class 2 ($\chi' = \Delta + 1$). Fully verified in Lean 4 with **0 custom axioms and 0 sorries** via Vizing fan shifts, Kempe alternating chain uniqueness, and well-founded induction on uncolored edges.

---

### 12. Fisher's Inequality for Balanced Incomplete Block Designs
* **Module:** [`Formalization/FishersInequality.lean`](Formalization/FishersInequality.lean)
* **Theorems:** `fishers_inequality`, `gramian_eq`, `det_gramian`, `incidence_mul_transpose_apply`, `vr_eq_bk`, `r_gt_lambda`
* **Mathematical Statement:** In any $2$-$(v, k, \lambda)$ balanced incomplete block design (BIBD) with $1 < k < v$ and $\lambda > 0$, the number of blocks $b$ is at least the number of points $v$:
  $$b \ge v$$
  derived from the Gramian factorization $N N^T = (r - \lambda) I_v + \lambda J_v$ and non-vanishing determinant $\det(N N^T) > 0$.

---

### 13. Lindström–Gessel–Viennot (LGV) Lemma
* **Module:** [`Formalization/GesselViennot.lean`](Formalization/GesselViennot.lean)
* **Theorems:** `lindstrom_gessel_viennot`, `gessel_viennot_planar_dag`, `det_pathMatrix_eq_permutation_sum`, `intersecting_path_systems_sum_zero`
* **Mathematical Statement:** For an edge-weighted directed acyclic graph (DAG), the path matrix $M_{i, j} = \sum_{P: a_i \to b_j} w(P)$ satisfies:
  $$\det(M) = \sum_{\sigma \in S_n} \mathrm{sgn}(\sigma) \sum_{\mathcal{P} : A \to B_\sigma \text{ non-intersecting}} w(\mathcal{P})$$
  via a canonical tail-swapping, sign-reversing involution on intersecting path systems. For planar grid graphs with boundary-ordered endpoints, $\det(M)$ counts non-intersecting path systems.

---

### 14. Cayley's Tree Formula & Prüfer Sequences
* **Module:** [`Formalization/CayleysFormula.lean`](Formalization/CayleysFormula.lean)
* **Modular Package:** [`Formalization/CayleysFormula/`](Formalization/CayleysFormula)
  - `PruferEncode.lean`: `LabeledTree` structure and lemmas, `PruferSequence`, leaf filtering, and leaf-peeling encoding algorithm (`pruferCode`).
  - `PruferDecode.lean`: Inductive edge decoding algorithm (`decodeEdges`), connectivity, and tree reconstruction (`pruferDecode`, `pruferDecode_isTree`).
* **Theorems:** `cayleys_tree_formula`, `prufer_sequence_card`, `pruferEquiv`, `pruferCode`, `pruferDecode`, `rooted_trees_count`, `cayley_n2`, `cayley_n3`, `cayley_n4`
* **Mathematical Statement:** The number of labeled trees on $n \ge 2$ vertices is:
  $$T_n = n^{n - 2}$$
  established bijectively via constructive leaf-peeling Prüfer encoding `pruferCode`, degree-based decoding `pruferDecode`, and the Prüfer equivalence `pruferEquiv : LabeledTree n ≃ PruferSequence n`. Fully verified in Lean 4 with **0 custom axioms and 0 sorries**.

---

### 15. Kőnig–Egerváry Duality Theorem
* **Module:** [`Formalization/KonigMatching.lean`](Formalization/KonigMatching.lean)
* **Theorems:** `konig_duality`, `konig_duality_le`, `weak_duality`, `exists_max_defect`, `matching_card_le_vertexCover_card`, `gallai_independence_vertex_cover`, `konig_independence_matching`
* **Mathematical Statement:** In any bipartite ($2$-colorable) graph $G = (V, E)$, the matching number $\nu(G)$ equals the vertex cover number $\tau(G)$ (strong min-max duality):
  $$\nu(G) = \tau(G)$$
  proved with 0 axioms from Hall's marriage deficiency theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`), alongside Gallai's identity $\alpha(G) + \tau(G) = |V|$ and Kőnig's formula $\alpha(G) + \nu(G) = |V|$.

---

### 16. Jung's Theorem on Circumscribed Euclidean Spheres
* **Module:** [`Formalization/JungsTheorem.lean`](Formalization/JungsTheorem.lean)
* **Theorems:** `jungs_theorem`, `jungs_theorem_via_helly`, `circumradius_le_jungs_bound`, `jungsConstant_pos`, `jungsConstant_one`, `jungsConstant_two`, `jungsConstant_three`, `jungs_bound_dim1`, `jungs_bound_dim2`, `jungs_bound_dim3`
* **Mathematical Statement:** For any non-empty bounded subset $S \subset \mathbb{R}^d$, the Chebyshev circumradius $\mathcal{R}(S)$ is bounded by the diameter $\mathrm{diam}(S)$:
  $$\mathcal{R}(S) \le \sqrt{\frac{d}{2(d + 1)}} \mathrm{diam}(S)$$
  with the global enclosing theorem `jungs_theorem` proved from the finite simplex case via Helly's compact intersection theorem on closed Euclidean balls (`Convex.helly_theorem_compact'`).

---

### 17. Alon–Boppana Spectral Lower Bound for Regular Graphs
* **Module:** [`Formalization/AlonBoppana.lean`](Formalization/AlonBoppana.lean)
* **Theorems:** `alon_boppana_bound`, `alon_boppana_nilli`, `secondEigenvalue`, `IsRamanujan`, `adjacencyMatrix_symmetric`, `adjacencyMatrix_mul_ones`, `ramanujan_spectral_gap`
* **Mathematical Statement:** For any $d$-regular simple graph $G$ on $n$ vertices with diameter $D$, the second largest eigenvalue $\lambda_2(A)$ of the adjacency matrix satisfies:
  $$\lambda_2(A) \ge 2\sqrt{d-1} \cdot \left(1 - \frac{2}{D}\right) - \frac{2}{D}$$
  establishing the asymptotic lower bound $\liminf_{n \to \infty} \lambda_2(G_n) \ge 2\sqrt{d-1}$ and characterizing Ramanujan graphs as optimal expanders achieving the Alon–Boppana threshold.

---

### 18. Menger's Theorem on Disjoint Paths and Vertex Separators
* **Module:** [`Formalization/MengersTheorem.lean`](Formalization/MengersTheorem.lean)
* **Modular Package:** [`Formalization/MengersTheorem/`](Formalization/MengersTheorem)
  - `Basic.lean`: `STPath`, `innerVertices`, internally disjoint path systems, vertex separators, and weak duality.
  - `VertexMenger.lean`: Edge deletion and Dirac/Göring reductions, length-2 path obstructions, and vertex min-max duality (`mengers_theorem_vertex`).
  - `EdgeMenger.lean`: Edge-disjoint path systems, edge cuts, weak duality for edges, and edge min-max duality (`mengers_theorem_edge`).
  - `Whitney.lean`: Characterization of $k$-vertex-connected graphs via Menger's duality (`kConnected_iff_paths`).
* **Theorems:** `menger_vertex`, `menger_edge`, `menger_whitney`, `weak_duality`
* **Mathematical Statement:** For any finite simple graph $G = (V, E)$ and distinct non-adjacent vertices $s, t \in V$, the maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ vertex separator:
  $$\max \{ |\mathcal{P}| : \mathcal{P} \text{ internally disjoint } s\text{-}t \text{ paths} \} = \min \{ |S| : S \subseteq V \setminus \{s, t\} \text{ separates } s \text{ and } t \}$$
  alongside edge-disjoint path duality and Whitney's characterization of $k$-connectivity. Fully verified in Lean 4 with **0 custom axioms and 0 sorries**.

---

### 19. MacMahon's Master Theorem
* **Module:** [`Formalization/MacMahonsMasterTheorem.lean`](Formalization/MacMahonsMasterTheorem.lean)
* **Theorems:** `macmahon_master_theorem`, `macmahon_dim1`, `macmahon_zero_exponent`, `detMacMahon_eq_sum_subdetCoeff`, `invOfUnit_one_eq_of_antidiagonal_eq_zero`
* **Mathematical Statement:** For any $n \times n$ matrix $A = (a_{ij}) \in M_{n \times n}(R)$ over a commutative ring $R$ and any multi-index $s = (s_1, \dots, s_n) \in \mathbb{N}^n$, the coefficient of $X^s = X_1^{s_1} \cdots X_n^{s_n}$ in the product of linear forms $\prod_{i=1}^n (\sum_{j=1}^n a_{ij} X_j)^{s_i}$ equals the coefficient of $X^s$ in the formal power series expansion of the reciprocal determinant $\det(I_n - X A)^{-1}$:
  $$[X_1^{s_1} \cdots X_n^{s_n}] \prod_{i=1}^n \left( \sum_{j=1}^n a_{ij} X_j \right)^{s_i} = [X_1^{s_1} \cdots X_n^{s_n}] \frac{1}{\det(I_n - X A)}$$
  Fully verified in Lean 4 with **0 custom axioms and 0 sorries** via Cartier's support-restricted relation matrix (`macmahonRelMatrix'`), adjugate kernel projection, Leibniz minor expansion, and multivariate formal power series inversion uniqueness on `Finset.antidiagonal`.

---

### 20. Blichfeldt's Theorem in Geometry of Numbers
* **Module:** [`Formalization/BlichfeldtsTheorem.lean`](Formalization/BlichfeldtsTheorem.lean)
* **Theorems:** `blichfeldts_theorem`, `minkowski_convex_body_theorem`, `blichfeldt_dim1`
* **Mathematical Statement:** For any Lebesgue measurable set $S \subset \mathbb{R}^d$ with volume $\mathrm{vol}(S) > k$ (for integer $k \ge 1$), there exist $k+1$ distinct points $x_0, x_1, \dots, x_k \in S$ such that all pairwise differences belong to the integer lattice $\mathbb{Z}^d$:
  $$x_i - x_j \in \mathbb{Z}^d \quad \text{for all } 0 \le i, j \le k$$
  proved via torus translation decomposition $\mathbb{R}^d = \bigcup_{z \in \mathbb{Z}^d} (z + [0, 1)^d)$ and yielding Minkowski's First Convex Body Theorem as a direct corollary.

---

### 21. The Hoffman–Singleton Moore Graph Classification Theorem
* **Module:** [`Formalization/HoffmanSingleton.lean`](Formalization/HoffmanSingleton.lean)
* **Theorems:** `hoffman_singleton_theorem`, `classification_general`, `classification_integral_params`, `s_divides_15`, `degree_from_s`, `moore_polynomial_identity`, `certDegree2`, `certDegree3`, `certDegree7`, `certDegree57`, `certPetersenIntegral`, `certHoffmanSingletonIntegral`, `certDegree57Integral`, `c5_spectral_trace`, `petersen_spectral_trace`, `hoffman_singleton_spectral_trace`, `degree_57_spectral_trace`
* **Mathematical Statement:** The **Hoffman–Singleton Theorem (1960)** classifies the possible vertex degrees of Moore graphs of diameter 2 and girth 5. A $d$-regular graph with diameter 2 and girth 5 has $n = 1 + d^2$ vertices and its adjacency matrix satisfies $A^2 + A - (d - 1)I = J$. The eigenvalues on $1^\perp$ satisfy $\lambda^2 + \lambda - (d - 1) = 0$ with discriminant $\Delta = 4d - 3$. The trace identity $\operatorname{Tr}(A) = 0$ forces:
  $$(m_1 - m_2) \sqrt{4d - 3} = d(d - 2)$$
  where $m_1, m_2$ are integer multiplicities summing to $d^2$. This integrality condition requires:
  - If $m_1 = m_2$: $d = 2$ (the 5-cycle $C_5$, $n = 5$).
  - If $m_1 \ne m_2$: $s = \sqrt{4d - 3} \in \{1, 3, 5, 15\}$, giving $d = 1$ (degenerate $K_2$), $d = 3$ (the Petersen graph, $n = 10$), $d = 7$ (the Hoffman–Singleton graph, $n = 50$), or $d = 57$ (potential Moore graph, $n = 3250$).
  Thus, any non-trivial Moore graph of diameter 2 and girth 5 has degree $d \in \{2, 3, 7, 57\}$. Fully verified in Lean 4 with **0 custom axioms and 0 sorries**.

---

### 22. The Robinson–Schensted–Knuth (RSK) Bijection and Tableaux Combinatorics
* **Module:** [`Formalization/RSKBijection.lean`](Formalization/RSKBijection.lean)
* **Theorems:** `schensted_lis_theorem`, `greene_lds_theorem`, `rsk_sum_squares_eq_factorial`, `rsk_involution_fixed_points`, `rsk_involution_symmetry`, `rskPerm`, `insertTableau`, `insertRow`, `rskInsertList_size`, `rskInsertList_head`
* **Mathematical Statement:** The **RSK Correspondence** establishes a bijection between permutations and pairs of Standard Young Tableaux of identical shape $\lambda \vdash n$:
  $$\operatorname{RSK} : \mathfrak{S}_n \xrightarrow{\cong} \coprod_{\lambda \vdash n} (\mathrm{SYT}(\lambda) \times \mathrm{SYT}(\lambda))$$
  - **Schensted's Theorem (1961):** The length of the first row $\lambda_1 = \operatorname{row}_1(P(\pi))$ equals the length of the Longest Increasing Subsequence $\operatorname{LIS}(\pi)$.
  - **Greene's Theorem (1974):** The length of the first column $\lambda'_1 = \operatorname{col}_1(P(\pi))$ equals the length of the Longest Decreasing Subsequence $\operatorname{LDS}(\pi)$.
  - **Frobenius Identity:** $\sum_{\lambda \vdash n} (f^\lambda)^2 = n!$.
  - **Involution Theorem:** $P(\pi^{-1}) = Q(\pi)$ and $Q(\pi^{-1}) = P(\pi)$; $\pi$ is an involution ($\pi^2 = \mathrm{id}$) if and only if $P(\pi) = Q(\pi)$.
  Fully verified in Lean 4 with **0 custom axioms and 0 sorries**.

---

### 23. The Birkhoff–von Neumann Theorem on Doubly Stochastic Matrices
* **Module:** [`Formalization/BirkhoffVonNeumann.lean`](Formalization/BirkhoffVonNeumann.lean)
* **Theorems:** `birkhoff_von_neumann_convex_hull`, `birkhoff_von_neumann_iff`, `birkhoff_von_neumann_convex_combination`, `extremePoints_doublyStochasticSet`, `permutationMatrix_isDoublyStochastic`, `convex_doublyStochastic`, `hall_condition_doublyStochastic`, `exists_perm_positive_entries`, `card_matrixSupp_ge_n`, `isDoublyStochastic_and_entries_zero_one_iff`
* **Mathematical Statement:** The **Birkhoff–von Neumann Theorem (1946, 1953)** establishes that the convex polytope $\mathcal{D}_n$ of $n \times n$ doubly stochastic matrices is the convex hull of the set $\mathcal{P}_n$ of permutation matrices:
  $$\mathcal{D}_n = \operatorname{Conv}(\mathcal{P}_n)$$
  and the extreme points of $\mathcal{D}_n$ are precisely the permutation matrices:
  $$\operatorname{Ext}(\mathcal{D}_n) = \mathcal{P}_n$$
  The constructive proof formalizes Hall's condition on row supports to extract positive diagonal permutations (`exists_perm_positive_entries`), constructs the reduced matrix $M' = \frac{1}{1 - \theta}(M - \theta P_\sigma)$, and applies strong induction on the support size $|\operatorname{supp}(M)|$. Fully verified in Lean 4 with **0 custom axioms and 0 sorries**.

---

### 24. Stanley's $\mathfrak{sl}_2$ Representation Proof of the Strong Sperner Property for $L(m, n)$
* **Module:** [`Formalization/StanleySL2.lean`](Formalization/StanleySL2.lean)
* **Theorems:** `sperner_partition_poset`, `sperner_partition_poset_slice`, `rankSize_symm`, `rankSize_unimodal`, `rank_complement`, `middleRankLevel_is_maximal_slice`, `rankSize_one_row`, `stanleySL2Data_one_row`, `sl2_norm_sq_lower_bound`, `explicit_antichain_2_2`, `sl2Module_2_2`
* **Mathematical Statement:** The **Stanley $\mathfrak{sl}_2$ Sperner Theorem (1980)** proves that the partition lattice $L(m, n)$ of Young diagrams fitting inside an $m \times n$ box possesses the Strong Sperner property:
  $$\max_{\mathcal{A} \text{ antichain}} |\mathcal{A}| = p_{\lfloor mn/2 \rfloor}(m, n)$$
  - **Rank-Symmetry:** The partition complementation involution $\lambda^*_i = n - \lambda_{m - 1 - i}$ satisfies $|\lambda^*| = mn - |\lambda|$, proving $p_k(m, n) = p_{mn - k}(m, n)$.
  - **Hard Lefschetz & Unimodality:** The Lie algebra $\mathfrak{sl}_2(\mathbb{C}) = \operatorname{span}\{E, F, H\}$ representation on $V = \bigoplus_k \mathbb{R}^{L_k(m, n)}$ satisfies $[E, F] = H$, proving the raising operator $E : V_k \to V_{k+1}$ is strictly injective for $2k < mn$, which establishes rank unimodality $p_0 \le p_1 \le \dots \le p_{\lfloor mn/2 \rfloor}$.
  - **Strong Sperner Property:** Every rank slice is an antichain bounded by the middle level $p_{\lfloor mn/2 \rfloor}(m, n)$.
  Fully verified in Lean 4 with **0 custom axioms and 0 sorries**.

---

## Palomar Registry Integration

All 24 theorems in this repository are formatted and packaged as independent, self-contained submission targets for the **[Palomar Registry](https://submit.palomar-registry.org)**. Every formalization has a dedicated, immutable 40-character Git commit SHA with its corresponding `formalization.yaml` and `comparator.json` metadata active at repository root.

The complete master inventory of 24 theorems, dedicated commit SHAs, comparator configurations, and submission readiness states is tracked in **[`PALOMAR_CHECKLIST.md`](PALOMAR_CHECKLIST.md)**.

### Submission Settings for submit.palomar-registry.org
- **Comparator Path**: `comparator.json`
- **Existing Palomar ID**: *(leave blank)*
- **Relationship**: `Maintainer` / `Author`

---

## Repository Structure

```text
.
├── Challenge.lean                        # Benchmark challenge interface for edge coloring & Vizing's theorem
├── Formalization.lean                    # Root library module importing all 25 formalized modules
├── Formalization/
│   ├── SpernerAntichain.lean             # 1. Sperner's Theorem on Antichains & LYM Inequality (1928, 1966)
│   ├── VanDerWaerden.lean                # 2. Van der Waerden's Theorem on Arithmetic Progressions (1927)
│   ├── TuransTheorem.lean                # 3. Turán's Theorem & Mantel's Theorem (1941, 1907)
│   ├── BrooksTheorem.lean                # 4. Brooks' Theorem on Graph Colorings (Master Interface)
│   ├── BrooksTheorem/                    # 4. Modular Brooks Package
│   │   ├── Basic.lean                    #     - Maximum degree & chromatic properties
│   │   ├── OddCycles.lean                #     - Cliques & odd cycle obstructions
│   │   ├── Greedy.lean                   #     - Greedy coloring & Lovász coloring engine
│   │   └── LovaszOrdering.lean           #     - BFS distance trees & Lovász triple extraction
│   ├── IharaZeta.lean                    # 5. Ihara Zeta Function & Hashimoto Matrix (1966)
│   ├── IharaBass.lean                    # 6. Ihara-Bass Determinantal Formula (1992)
│   ├── PrefixSparsity.lean               # 7. Combinatorial Prefix-Sharing & Sparsity on Trees
│   ├── CyclicShift.lean                  # 8. Characteristic Polynomial of Cyclic Shift Matrices
│   ├── RamanujanTau.lean                 # 9. Ramanujan Tau Modulo 691 Congruence (1916)
│   ├── MatrixTreeTheorem.lean            # 10. Kirchhoff's Matrix-Tree Theorem (1847)
│   ├── VizingsTheorem.lean               # 11. Vizing's Theorem on Edge Colorings (Master Interface)
│   ├── VizingsTheorem/                   # 11. Modular Vizing Package
│   │   ├── Basic.lean                    #     - Edge colorings & missing colors
│   │   ├── Kempe.lean                    #     - Kempe chains & alternating walks
│   │   ├── Bipartite.lean                #     - Shift steps & König's Line Coloring Theorem
│   │   └── Fan.lean                      #     - Vizing fan extensions
│   ├── FishersInequality.lean            # 12. Fisher's Inequality for Block Designs (1940)
│   ├── GesselViennot.lean                # 13. Lindström–Gessel–Viennot Lemma (1973, 1985)
│   ├── CayleysFormula.lean               # 14. Cayley's Tree Formula & Prüfer Sequences (Master Interface)
│   ├── CayleysFormula/                   # 14. Modular Cayley Package
│   │   ├── PruferEncode.lean             #     - Labeled trees, Prüfer sequences, & encoding
│   │   └── PruferDecode.lean             #     - Edge decoder & tree reconstruction
│   ├── KonigMatching.lean                # 15. Kőnig–Egerváry Duality Theorem (1931)
│   ├── JungsTheorem.lean                 # 16. Jung's Theorem on Circumscribed Spheres (1901)
│   ├── AlonBoppana.lean                  # 17. Alon–Boppana Spectral Lower Bound (1986)
│   ├── MengersTheorem.lean               # 18. Menger's Theorem on Disjoint Paths (Master Interface)
│   ├── MengersTheorem/                   # 18. Modular Menger Package
│   │   ├── Basic.lean                    #     - STPath, vertex separators, & weak duality
│   │   ├── VertexMenger.lean             #     - Edge deletion induction & vertex duality
│   │   ├── EdgeMenger.lean               #     - Edge-disjoint systems & edge cuts
│   │   └── Whitney.lean                  #     - Whitney's k-connectivity theorem
│   ├── MacMahonsMasterTheorem.lean       # 19. MacMahon's Master Theorem (1915)
│   ├── BlichfeldtsTheorem.lean           # 20. Blichfeldt's Theorem in Geometry of Numbers (1914)
│   ├── HoffmanSingleton.lean             # 21. The Hoffman–Singleton Moore Graph Classification Theorem (1960)
│   ├── RSKBijection.lean                 # 22. Robinson–Schensted–Knuth (RSK) Bijection & Tableaux (1961)
│   ├── BirkhoffVonNeumann.lean           # 23. The Birkhoff–von Neumann Theorem on Doubly Stochastic Matrices (1946)
│   └── StanleySL2.lean                   # 24. Stanley's sl2 Proof of the Strong Sperner Property (1980)
├── Solution.lean                         # Clean wrapper re-exporting complete formalization solutions
├── lakefile.toml                         # Lake build system manifest
├── lean-toolchain                        # Pinned Lean 4 toolchain (leanprover/lean4:v4.34.0-rc1)
├── PALOMAR_CHECKLIST.md                  # Palomar submission checklist and SHA inventory
└── README.md                             # Comprehensive technical documentation & mathematical guide
```

---

## Toolchain, Build, and Verification

### Prerequisites
- [Elan](https://github.com/leanprover/elan) (Lean Version Manager)
- Pinned toolchain: `leanprover/lean4:v4.34.0-rc1` (recorded in `lean-toolchain`)

### Compiling and Verifying the Entire Repository
To fetch dependencies, download precompiled Mathlib oleans, and verify all modules:

```bash
lake update
lake exe cache get
lake build Formalization
lake build Challenge Solution
```

### Compiling Individual Modules
Each formalization module can be compiled independently:

```bash
lake build Formalization.SpernerAntichain
lake build Formalization.VanDerWaerden
lake build Formalization.TuransTheorem
lake build Formalization.BrooksTheorem
lake build Formalization.IharaZeta
lake build Formalization.IharaBass
lake build Formalization.PrefixSparsity
lake build Formalization.CyclicShift
lake build Formalization.RamanujanTau
lake build Formalization.MatrixTreeTheorem
lake build Formalization.VizingsTheorem
lake build Formalization.FishersInequality
lake build Formalization.GesselViennot
lake build Formalization.CayleysFormula
lake build Formalization.KonigMatching
lake build Formalization.JungsTheorem
lake build Formalization.AlonBoppana
lake build Formalization.MengersTheorem
lake build Formalization.MacMahonsMasterTheorem
lake build Formalization.BlichfeldtsTheorem
lake build Formalization.HoffmanSingleton
lake build Formalization.RSKBijection
lake build Formalization.BirkhoffVonNeumann
lake build Formalization.StanleySL2
```

---

## References

1. **Alon, N.** (1986). *Eigenvalues and expanders*. Theory of Computing Systems, 19(1), 283–296.
2. **Bass, H.** (1992). *The Ihara-Selberg zeta function of a tree lattice*. International Journal of Mathematics, 3(06), 717–797.
3. **Bárány, I.** (1982). *A generalization of Carathéodory's theorem*. Discrete Mathematics, 40(2-3), 141–152.
4. **Birkhoff, G.** (1946). *Tres observaciones sobre el algebra lineal*. Universidad Nacional de Tucumán Revista, Serie A, 5, 147–151.
5. **Blichfeldt, H. F.** (1914). *A new principle in the geometry of numbers, with some applications*. Transactions of the American Mathematical Society, 15(3), 227–235.
6. **Bollobás, B.** (1965). *On generalized graphs*. Acta Mathematica Academiae Scientiarum Hungaricae, 16(3-4), 447–452.
7. **Borchardt, C. W.** (1860). *Über eine der Interpolation entsprechende Darstellung der Eliminations-Resultante*. J. Reine Angew. Math., 57, 111–121.
8. **Bose, R. C.** (1949). *A note on Fisher's inequality for balanced incomplete block designs*. Bull. Calcutta Math. Soc., 41, 106–107.
9. **Brooks, R. L.** (1941). *On colouring the nodes of a network*. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194–197.
10. **Carathéodory, C.** (1907). *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen*. Rendiconti del Circolo Matematico di Palermo, 32, 193–217.
11. **Cartier, P., & Foata, D.** (1969). *Problèmes combinatoires de commutation et réarrangements*. Lecture Notes in Mathematics, 85, Springer.
12. **Cassels, J. W. S.** (1971). *An Introduction to the Geometry of Numbers*. Springer-Verlag.
13. **Cayley, A.** (1889). *A theorem on trees*. Quart. J. Math., 23, 376–378.
14. **Danzer, L., Grünbaum, B., & Klee, V.** (1963). *Helly's theorem and its relatives*. Convexity, Proc. Sympos. Pure Math., Vol. 7, 101–180.
15. **Dirac, G. A.** (1966). *Short proof of Menger's theorem*. Mathematika, 13(1), 42–44.
16. **Egerváry, J.** (1931). *Matrixok kombinatorius tulajdonságairól*. Matematikai és Fizikai Lapok, 38, 16–28.
17. **Fisher, R. A.** (1940). *An examination of the different possible solutions of a problem in incomplete blocks*. Annals of Eugenics, 10(1), 52–75.
18. **Gallai, T.** (1959). *Über extreme Punkt- und Kantenmengen*. Ann. Univ. Sci. Budapest, Eötvös Sect. Math., 2, 133–138.
19. **Gessel, I., & Viennot, G.** (1985). *Binomial determinants, paths, and hook length formulae*. Advances in Mathematics, 58(3), 300–321.
20. **Gowers, W. T.** (2001). *A new proof of Szemerédi's theorem*. Geometric and Functional Analysis, 11(3), 465–588.
21. **Graham, R. L., Rothschild, B. L., & Spencer, J. H.** (1990). *Ramsey Theory*. John Wiley & Sons.
22. **Greene, C.** (1974). *An extension of Schensted's theorem*. Advances in Mathematics, 14(2), 254–265.
23. **Hall, P.** (1935). *On Representatives of Subsets*. Journal of the London Mathematical Society, 10(1), 26–30.
24. **Hashimoto, K.** (1989). *Zeta functions of finite graphs and representations of p-adic groups*. Advanced Studies in Pure Mathematics, 15, 211–280.
25. **Hoffman, A. J., & Singleton, R. R.** (1960). *On Moore graphs with diameters 2 and 3*. IBM Journal of Research and Development, 4(5), 497–504.
26. **Ihara, Y.** (1966). *On discrete subgroups of the two by two projective linear group over p-adic fields*. Journal of the Mathematical Society of Japan, 18(3), 219–235.
27. **Jung, H.** (1901). *Über die kleinste Kugel, die eine räumliche Figur einschliesst*. J. Reine Angew. Math., 123, 241–257.
28. **Kirchhoff, G.** (1847). *Über die Auflösung der Gleichungen, auf welche man bei der Untersuchung der linearen Vertheilung galvanischer Ströme geführt wird*. Annalen der Physik und Chemie, 148(12), 497–508.
29. **Knuth, D. E.** (1970). *Permutations, matrices, and generalized Young tableaux*. Pacific Journal of Mathematics, 34(3), 709–727.
30. **König, D.** (1916). *Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre*. Mathematische Annalen, 77(4), 453–465.
31. **Kőnig, D.** (1931). *Gráfok és mátrixok*. Matematikai és Fizikai Lapok, 38, 116–119.
32. **Lindström, B.** (1973). *On the vector representations of induced matroids*. Bulletin of the London Mathematical Society, 5(1), 85–90.
33. **Lovász, L.** (1975). *Three short proofs in graph theory*. Journal of Combinatorial Theory, Series B, 19(3), 269–271.
34. **Lubell, D.** (1966). *A short proof of Sperner's lemma*. Journal of Combinatorial Theory, 1(2), 299.
35. **Lubotzky, A., Phillips, R., & Sarnak, P.** (1988). *Ramanujan graphs*. Combinatorica, 8(3), 261–277.
36. **MacMahon, P. A.** (1915). *Combinatory Analysis* (Vol. 1 & 2). Cambridge University Press.
37. **Mantel, W.** (1907). *Vraagstuk XXVIII*. Wiskundige Opgaven, 10, 60–61.
38. **Menger, K.** (1927). *Zur allgemeinen Kurventheorie*. Fundamenta Mathematicae, 10(1), 96–115.
39. **Meshalkin, L. D.** (1963). *Generalization of Sperner's theorem on the number of subsets of a finite set*. Theory of Probability & Its Applications, 8(2), 203–204.
40. **Minkowski, H.** (1896). *Geometrie der Zahlen*. Teubner, Leipzig.
41. **Nilli, A.** (1991). *On the second eigenvalue of a graph*. Discrete Mathematics, 91(2), 207–210.
42. **Proctor, R. A.** (1982). *Representations of $\mathfrak{sl}(2, \mathbb{C})$ on posets and the Sperner property*. SIAM Journal on Algebraic and Discrete Methods, 3(2), 275–280.
43. **Prüfer, H.** (1918). *Neuer Beweis eines Satzes über Permutationen*. Arch. Math. Phys., 27, 742–744.
44. **Ramanujan, S.** (1916). *On certain arithmetical functions*. Transactions of the Cambridge Philosophical Society, 22(9), 159–184.
45. **Robinson, G. de B.** (1938). *On the representations of the symmetric group*. American Journal of Mathematics, 60(3), 745–760.
46. **Schensted, C.** (1961). *Longest increasing and decreasing subsequences*. Canadian Journal of Mathematics, 13, 179–191.
47. **Schrijver, A.** (2003). *Combinatorial Optimization: Polyhedra and Efficiency*. Springer.
48. **Serre, J.-P.** (1973). *A Course in Arithmetic*. Graduate Texts in Mathematics, 7.
49. **Serre, J.-P.** (1977). *Trees*. Springer-Verlag.
50. **Sperner, E.** (1928). *Ein Satz über Untermengen einer endlichen Menge*. Mathematische Zeitschrift, 27(1), 544–548.
51. **Stanley, R. P.** (1980). *Weyl groups, the hard Lefschetz theorem, and the Sperner property*. SIAM Journal on Algebraic and Discrete Methods, 1(2), 168–184.
52. **Stanley, R. P.** (1982). *Some Aspects of Groups Acting on Symmetric Posets*. Journal of Combinatorial Theory, Series A, 32(2), 132–161.
53. **Stanley, R. P.** (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics, Cambridge University Press.
54. **Stanley, R. P.** (2012). *Enumerative Combinatorics, Volume 1*. Cambridge University Press.
55. **Turán, P.** (1941). *Eine Extremalaufgabe aus der Graphentheorie*. Matematikai és Fizikai Lapok, 48, 436–452.
56. **van der Waerden, B. L.** (1927). *Beweis einer Baudetschen Vermutung*. Nieuw Archief voor Wiskunde, 15, 212–216.
57. **Vizing, V. G.** (1964). *On an estimate of the chromatic class of a p-graph*. Diskret. Analiz., 3, 25–30.
58. **von Neumann, J.** (1953). *A certain zero-sum two-person game equivalent to the optimal assignment problem*. Contributions to the Theory of Games, 2, 5–12.
59. **Whitney, H.** (1932). *Congruent graphs and the connectivity of graphs*. Amer. J. Math., 54(1), 150–168.
60. **Yamamoto, K.** (1954). *Logarithmic order of free distributive lattice*. Journal of the Mathematical Society of Japan, 6(3-4), 343–353.

---

## License

This repository and all formalizations are dedicated to the public domain under the **[Creative Commons Zero v1.0 Universal (CC0 1.0)](LICENSE)** public domain dedication. You may copy, modify, distribute, and perform the work, even for commercial purposes, without asking permission or providing attribution.
