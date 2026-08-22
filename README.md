# Formalization of Combinatorial, Geometric, Spectral, and Graph Theorems in Lean 4 (Part II)

This repository provides machine-checked formalizations, certified proofs, and foundational scaffolds of landmark theorems across combinatorics, spectral graph theory, Ramsey theory, matrix theory, modular forms, discrete geometry, and combinatorial optimization in the Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) ecosystem.

---

## Table of Formalized Modules and Theorems

| # | Theorem / Topic | Primary Declaration(s) | Mathematical Domain | Reference | Status & Missing Prerequisites |
| :---: | :--- | :--- | :--- | :--- | :--- |
| 1 | **Sperner's Antichain Theorem & LYM Inequality** | [`sperners_antichain_theorem`](Formalization/SpernerAntichain.lean), [`lym_inequality`](Formalization/SpernerAntichain.lean), [`sperners_antichain_equality`](Formalization/SpernerAntichain.lean) | Extremal Combinatorics & Poset Theory | Sperner (1928), Lubell (1966), Yamamoto (1954) | **100% Verified (0 axioms)** |
| 2 | **Van der Waerden's Theorem on Arithmetic Progressions** | [`van_der_waerden_finite`](Formalization/VanDerWaerden.lean), [`van_der_waerden_infinite`](Formalization/VanDerWaerden.lean), [`multiple_van_der_waerden`](Formalization/VanDerWaerden.lean) | Ramsey Theory & Additive Combinatorics | Van der Waerden (1927), Wiedijk #85 | **100% Verified (0 axioms)** |
| 3 | **Turán's Theorem & Mantel's Theorem** | [`turans_theorem`](Formalization/TuransTheorem.lean), [`turans_theorem_exact`](Formalization/TuransTheorem.lean), [`mantels_theorem`](Formalization/TuransTheorem.lean), [`turans_uniqueness`](Formalization/TuransTheorem.lean) | Extremal Graph Theory | Turán (1941), Mantel (1907) | **100% Verified (0 axioms)** |
| 4 | **Brooks' Theorem on Graph Colorings** | [`brooks_theorem`](Formalization/BrooksTheorem.lean), [`greedy_coloring_bound`](Formalization/BrooksTheorem.lean) | Graph Theory & Vertex Chromatics | Brooks (1941), Lovász (1975) | Scaffolded (lacks Lovász 2-connected vertex ordering) |
| 5 | **Ihara Zeta Function & Hashimoto Adjacency** | [`HashimotoMatrix`](Formalization/IharaZeta.lean), [`sourceMatrix_mul_targetMatrix_transpose`](Formalization/IharaZeta.lean), [`involutionMatrix_sq`](Formalization/IharaZeta.lean), [`IharaZetaInvLHS`](Formalization/IharaZeta.lean) | Spectral Graph Theory & Zeta Functions | Ihara (1966), Serre (1977) | **100% Verified (0 axioms)** |
| 6 | **Ihara-Bass Determinantal Formula** | [`ihara_bass_polynomial`](Formalization/IharaBass.lean), [`M_Bass_mul_N_Bass`](Formalization/IharaBass.lean), [`det_KL_Bass`](Formalization/IharaBass.lean) | Algebraic Graph Theory & Block Determinants | Bass (1992), Hashimoto (1989) | **100% Verified (0 axioms)** |
| 7 | **Prefix-Sharing & Sparsity on Trees** | [`sparsity_bound`](Formalization/PrefixSparsity.lean), [`fraction_eq_p_inv_r`](Formalization/PrefixSparsity.lean), [`card_shared_prefix`](Formalization/PrefixSparsity.lean), [`sparsity_p2_r3`](Formalization/PrefixSparsity.lean) | Tree Combinatorics & Branching Sparsity | Prefix Sharing & Tree Metric Sparsity | **100% Verified (0 axioms)** |
| 8 | **Characteristic Polynomial of Cyclic Matrices** | [`charpoly_cyclicWeightMatrix`](Formalization/CyclicShift.lean), [`charpoly_shiftMatrix`](Formalization/CyclicShift.lean), [`det_upperBidiagonal`](Formalization/CyclicShift.lean) | Linear Algebra & Circulant Matrices | Cyclic Shifts & Bidiagonal Expansion | **100% Verified (0 axioms)** |
| 9 | **Ramanujan Tau Congruence $\tau(n) \equiv \sigma_{11}(n) \pmod{691}$** | [`ramanujan_tau_congruence`](Formalization/RamanujanTau.lean), [`bernoulli_12_exact`](Formalization/RamanujanTau.lean), [`ramanujan_congruence_691`](Formalization/RamanujanTau.lean) | Modular Forms & Number Theory | Ramanujan (1916), Serre (1973) | **100% Verified (0 axioms)** |
| 10 | **Kirchhoff's Matrix-Tree Theorem** | [`matrix_tree_theorem`](Formalization/MatrixTreeTheorem.lean), [`laplacian_row_sum_zero`](Formalization/MatrixTreeTheorem.lean), [`laplacian_transpose_eq`](Formalization/MatrixTreeTheorem.lean), [`incidence_mul_transpose`](Formalization/MatrixTreeTheorem.lean) | Algebraic Graph Theory & Tree Enumeration | Kirchhoff (1847), Stanley (2012) | Scaffolded ($B B^T = L$ verified; lacks Binet–Cauchy determinants) |
| 11 | **Vizing's Theorem on Edge Colorings** | [`vizings_theorem`](Formalization/VizingsTheorem.lean), [`chromatic_index_ge_maxDegree`](Formalization/VizingsTheorem.lean), [`vizing_classification`](Formalization/VizingsTheorem.lean), [`konig_edge_coloring`](Formalization/VizingsTheorem.lean) | Graph Theory & Edge Colorings | Vizing (1964), König (1916) | Scaffolded ($\chi' \ge \Delta$ verified; lacks Kempe fan recoloring) |
| 12 | **Fisher's Inequality for Block Designs** | [`fishers_inequality`](Formalization/FishersInequality.lean), [`gramian_eq`](Formalization/FishersInequality.lean), [`det_gramian`](Formalization/FishersInequality.lean), [`incidence_mul_transpose_apply`](Formalization/FishersInequality.lean) | Combinatorial Design Theory & Matrix Gramians | Fisher (1940), Bose (1949) | **100% Verified (0 axioms)** |
| 13 | **Lindström–Gessel–Viennot (LGV) Lemma** | [`lindstrom_gessel_viennot`](Formalization/GesselViennot.lean), [`gessel_viennot_planar_dag`](Formalization/GesselViennot.lean), [`det_pathMatrix_eq_permutation_sum`](Formalization/GesselViennot.lean), [`intersecting_path_systems_sum_zero`](Formalization/GesselViennot.lean) | Algebraic Combinatorics & Lattice Paths | Lindström (1973), Gessel & Viennot (1985) | **100% Verified (0 axioms)** |
| 14 | **Cayley's Tree Formula & Prüfer Sequences** | [`cayleys_tree_formula`](Formalization/CayleysFormula.lean), [`prufer_sequence_card`](Formalization/CayleysFormula.lean), [`pruferEquiv`](Formalization/CayleysFormula.lean), [`pruferCode`](Formalization/CayleysFormula.lean), [`pruferDecode`](Formalization/CayleysFormula.lean) | Enumerative Combinatorics & Graph Enumeration | Cayley (1889), Prüfer (1918) | Scaffolded (`pruferDecode_isTree` & algorithms verified; lacks `prufer_left_inv` induction) |
| 15 | **Kőnig–Egerváry Duality Theorem** | [`konig_duality`](Formalization/KonigMatching.lean), [`weak_duality`](Formalization/KonigMatching.lean), [`matching_card_le_vertexCover_card`](Formalization/KonigMatching.lean), [`gallai_independence_vertex_cover`](Formalization/KonigMatching.lean), [`konig_independence_matching`](Formalization/KonigMatching.lean) | Combinatorial Optimization & Polyhedral Graphs | Kőnig (1931), Egerváry (1931), Gallai (1959) | **100% Verified (0 axioms)** |
| 16 | **Jung's Theorem on Circumscribed Spheres** | [`jungs_theorem`](Formalization/JungsTheorem.lean), [`jungs_theorem_via_helly`](Formalization/JungsTheorem.lean), [`circumradius_le_jungs_bound`](Formalization/JungsTheorem.lean), [`jungsConstant_pos`](Formalization/JungsTheorem.lean) | Discrete Geometry & Convexity | Jung (1901), Danzer, Grünbaum, & Klee (1963) | Scaffolded (Helly reduction `jungs_theorem_via_helly` verified; reduces to simplex case) |
| 17 | **Alon–Boppana Spectral Lower Bound** | [`alon_boppana_bound`](Formalization/AlonBoppana.lean), [`alon_boppana_nilli`](Formalization/AlonBoppana.lean), [`secondEigenvalue`](Formalization/AlonBoppana.lean), [`IsRamanujan`](Formalization/AlonBoppana.lean) | Spectral Graph Theory & Expanders | Alon (1986), Boppana (1986), Nilli (1991) | Scaffolded (Symmetry & gap verified; lacks Nilli spherical test vectors) |
| 18 | **Menger's Theorem on Disjoint Paths & Cuts** | [`mengers_theorem_vertex`](Formalization/MengersTheorem.lean), [`mengers_theorem_edge`](Formalization/MengersTheorem.lean), [`weak_duality`](Formalization/MengersTheorem.lean), [`kConnected_iff_paths`](Formalization/MengersTheorem.lean) | Graph Connectivity & Network Optimization | Menger (1927), Whitney (1932), Dirac (1966) | Scaffolded (Weak duality verified; lacks Dirac edge contraction) |
| 19 | **MacMahon's Master Theorem** | [`macmahon_master_theorem`](Formalization/MacMahonsMasterTheorem.lean), [`macmahon_dim1`](Formalization/MacMahonsMasterTheorem.lean), [`macmahonMatrix`](Formalization/MacMahonsMasterTheorem.lean), [`invDetMacMahon`](Formalization/MacMahonsMasterTheorem.lean) | Enumerative Combinatorics & Formal Series | MacMahon (1915), Cartier & Foata (1969) | Scaffolded (1D cases verified; lacks multivariable log-det expansion) |
| 20 | **Bárány's Colorful Carathéodory Theorem** | [`colorful_caratheodory_origin`](Formalization/ColorfulCaratheodory.lean), [`colorful_caratheodory_point`](Formalization/ColorfulCaratheodory.lean), [`caratheodory_classical_deduction`](Formalization/ColorfulCaratheodory.lean) | Discrete Geometry & Colorful Convexity | Bárány (1982), Carathéodory (1907) | Scaffolded (Classical deduction verified; lacks Bárány–Onn projection) |
| 21 | **Blichfeldt's Theorem in Geometry of Numbers** | [`blichfeldts_theorem`](Formalization/BlichfeldtsTheorem.lean), [`minkowski_convex_body_theorem`](Formalization/BlichfeldtsTheorem.lean), [`blichfeldt_dim1`](Formalization/BlichfeldtsTheorem.lean) | Geometry of Numbers & Lattice Tiling | Blichfeldt (1914), Minkowski (1896) | Scaffolded (1D interval verified; lacks torus pigeonhole integration) |

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

---

### 2. Van der Waerden's Theorem on Arithmetic Progressions
* **Module:** [`Formalization/VanDerWaerden.lean`](Formalization/VanDerWaerden.lean)
* **Theorems:** `van_der_waerden_finite`, `van_der_waerden_infinite`, `multiple_van_der_waerden`
* **Mathematical Statement:** For any number of colors $r \ge 1$ and progression length $k \ge 1$, there exists $W(r, k)$ such that any $r$-coloring of $\{1, \dots, W(r, k)\}$ contains a monochromatic $k$-term arithmetic progression.

---

### 3. Turán's Theorem & Mantel's Theorem
* **Module:** [`Formalization/TuransTheorem.lean`](Formalization/TuransTheorem.lean)
* **Theorems:** `turans_theorem`, `turans_theorem_exact`, `mantels_theorem`, `turans_uniqueness`
* **Mathematical Statement:** If a simple graph $G$ on $n$ vertices is $K_{r+1}$-free ($\omega(G) \le r$), then:
  $$|E(G)| \le e(T(n, r)) \le \left(1 - \frac{1}{r}\right) \frac{n^2}{2}$$

---

### 4. Brooks' Theorem on Graph Colorings
* **Module:** [`Formalization/BrooksTheorem.lean`](Formalization/BrooksTheorem.lean)
* **Theorems:** `brooks_theorem`, `greedy_coloring_bound`
* **Mathematical Statement:** For any connected graph $G$ with maximum degree $\Delta(G) = \Delta \ge 3$ not isomorphic to $K_{\Delta+1}$, $\chi(G) \le \Delta$.

---

### 5. Ihara Zeta Function & Hashimoto Adjacency Matrix
* **Module:** [`Formalization/IharaZeta.lean`](Formalization/IharaZeta.lean)
* **Theorems:** `sourceMatrix_mul_targetMatrix_transpose`, `sourceMatrix_mul_sourceMatrix_transpose`, `targetMatrix_transpose_mul_sourceMatrix`, `involutionMatrix_sq`
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

### 11. Vizing's Theorem on Edge Colorings
* **Module:** [`Formalization/VizingsTheorem.lean`](Formalization/VizingsTheorem.lean)
* **Theorems:** `chromatic_index_ge_maxDegree`, `vizings_theorem`, `vizing_classification`, `konig_edge_coloring`
* **Mathematical Statement:** For any finite simple graph $G$ with maximum vertex degree $\Delta(G)$, the edge chromatic index $\chi'(G)$ satisfies $\Delta(G) \le \chi'(G) \le \Delta(G) + 1$, classifying every graph into Class 1 ($\chi' = \Delta$) or Class 2 ($\chi' = \Delta + 1$).

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
  $$\det(M) = \sum_{\sigma \in S_n} \operatorname{sgn}(\sigma) \sum_{\mathcal{P} : A \to B_\sigma \text{ non-intersecting}} w(\mathcal{P})$$
  via a canonical tail-swapping, sign-reversing involution on intersecting path systems. For planar grid graphs with boundary-ordered endpoints, $\det(M)$ counts non-intersecting path systems.

---

### 14. Cayley's Tree Formula & Prüfer Sequences
* **Module:** [`Formalization/CayleysFormula.lean`](Formalization/CayleysFormula.lean)
* **Theorems:** `cayleys_tree_formula`, `prufer_sequence_card`, `pruferEquiv`, `pruferCode`, `pruferDecode`, `rooted_trees_count`, `cayley_n2`, `cayley_n3`, `cayley_n4`
* **Mathematical Statement:** The number of labeled trees on $n \ge 2$ vertices is:
  $$T_n = n^{n - 2}$$
  established bijectively via constructive leaf-peeling Prüfer encoding `pruferCode`, degree-based decoding `pruferDecode`, and the Prüfer equivalence `pruferEquiv : LabeledTree n ≃ PruferSequence n`.

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
* **Mathematical Statement:** For any non-empty bounded subset $S \subset \mathbb{R}^d$, the Chebyshev circumradius $\mathcal{R}(S)$ is bounded by the diameter $\operatorname{diam}(S)$:
  $$\mathcal{R}(S) \le \sqrt{\frac{d}{2(d + 1)}} \operatorname{diam}(S)$$
  with the global enclosing theorem `jungs_theorem` proved from the finite simplex case via Helly's compact intersection theorem on closed Euclidean balls (`Convex.helly_theorem_compact'`).

---

### 17. Alon–Boppana Spectral Lower Bound for Regular Graphs
* **Module:** [`Formalization/AlonBoppana.lean`](Formalization/AlonBoppana.lean)
* **Theorems:** `alon_boppana_bound`, `alon_boppana_nilli`, `adjacencyMatrix_symmetric`, `adjacencyMatrix_mul_ones`, `ramanujan_spectral_gap`
* **Mathematical Statement:** For any $d$-regular simple graph $G$ on $n$ vertices with diameter $D$, the second largest eigenvalue $\lambda_2(A)$ of the adjacency matrix satisfies:
  $$\lambda_2(A) \ge 2\sqrt{d-1} \cdot \left(1 - \frac{2}{D}\right) - \frac{2}{D}$$
  establishing the asymptotic lower bound $\liminf_{n \to \infty} \lambda_2(G_n) \ge 2\sqrt{d-1}$ and characterizing Ramanujan graphs as optimal expanders achieving the Alon–Boppana threshold.

---

### 18. Menger's Theorem on Disjoint Paths and Vertex Separators
* **Module:** [`Formalization/MengersTheorem.lean`](Formalization/MengersTheorem.lean)
* **Theorems:** `mengers_theorem_vertex`, `mengers_theorem_edge`, `weak_duality`, `kConnected_iff_paths`
* **Mathematical Statement:** For any finite simple graph $G = (V, E)$ and distinct non-adjacent vertices $s, t \in V$, the maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ vertex separator:
  $$\max \{ |\mathcal{P}| : \mathcal{P} \text{ internally disjoint } s\text{-}t \text{ paths} \} = \min \{ |S| : S \subseteq V \setminus \{s, t\} \text{ separates } s \text{ and } t \}$$
  alongside edge-disjoint path duality and Whitney's characterization of $k$-connectivity.

---

### 19. MacMahon's Master Theorem
* **Module:** [`Formalization/MacMahonsMasterTheorem.lean`](Formalization/MacMahonsMasterTheorem.lean)
* **Theorems:** `macmahon_master_theorem`, `macmahon_dim1`, `macmahon_zero_exponent`
* **Mathematical Statement:** For any $n \times n$ matrix $A = (a_{ij}) \in M_{n \times n}(R)$ and any multi-index $s = (s_1, \dots, s_n) \in \mathbb{N}^n$, the coefficient of $X^s = X_1^{s_1} \cdots X_n^{s_n}$ in the product of linear forms $\prod_{i=1}^n (\sum_{j=1}^n a_{ij} X_j)^{s_i}$ equals the coefficient of $X^s$ in the formal power series expansion of the reciprocal determinant $\det(I_n - X A)^{-1}$:
  $$[X_1^{s_1} \cdots X_n^{s_n}] \prod_{i=1}^n \left( \sum_{j=1}^n a_{ij} X_j \right)^{s_i} = [X_1^{s_1} \cdots X_n^{s_n}] \frac{1}{\det(I_n - X A)}$$

---

### 20. Bárány's Colorful Carathéodory Theorem
* **Module:** [`Formalization/ColorfulCaratheodory.lean`](Formalization/ColorfulCaratheodory.lean)
* **Theorems:** `colorful_caratheodory_origin`, `colorful_caratheodory_point`, `caratheodory_classical_deduction`, `colorful_caratheodory_dim1`, `colorful_caratheodory_dim2`
* **Mathematical Statement:** For any $d+1$ subsets of points $S_0, S_1, \dots, S_d \subset \mathbb{R}^d$ such that $0 \in \operatorname{conv}(S_i)$ for each color $i \in \{0, 1, \dots, d\}$, there exists a colorful transversal $(x_0, x_1, \dots, x_d)$ with $x_i \in S_i$ such that:
  $$0 \in \operatorname{conv}(\{x_0, x_1, \dots, x_d\})$$
  with classical Carathéodory as the monochromatic corollary $S_0 = \dots = S_d = S$.

---

### 21. Blichfeldt's Theorem in Geometry of Numbers
* **Module:** [`Formalization/BlichfeldtsTheorem.lean`](Formalization/BlichfeldtsTheorem.lean)
* **Theorems:** `blichfeldts_theorem`, `minkowski_convex_body_theorem`, `blichfeldt_dim1`
* **Mathematical Statement:** For any Lebesgue measurable set $S \subset \mathbb{R}^d$ with volume $\operatorname{vol}(S) > k$ (for integer $k \ge 1$), there exist $k+1$ distinct points $x_0, x_1, \dots, x_k \in S$ such that all pairwise differences belong to the integer lattice $\mathbb{Z}^d$:
  $$x_i - x_j \in \mathbb{Z}^d \quad \text{for all } 0 \le i, j \le k$$
  proved via torus translation decomposition $\mathbb{R}^d = \bigcup_{z \in \mathbb{Z}^d} (z + [0, 1)^d)$ and yielding Minkowski's First Convex Body Theorem as a direct corollary.

---

## Repository Structure

```text
.
├── Formalization.lean                    # Root library module importing all 21 formalized modules
├── Formalization/
│   ├── SpernerAntichain.lean             # 1. Sperner's Theorem on Antichains & LYM Inequality (1928, 1966)
│   ├── VanDerWaerden.lean                # 2. Van der Waerden's Theorem on Arithmetic Progressions (1927)
│   ├── TuransTheorem.lean                # 3. Turán's Theorem & Mantel's Theorem (1941, 1907)
│   ├── BrooksTheorem.lean                # 4. Brooks' Theorem on Graph Colorings (1941)
│   ├── IharaZeta.lean                    # 5. Ihara Zeta Function & Hashimoto Matrix (1966)
│   ├── IharaBass.lean                    # 6. Ihara-Bass Determinantal Formula (1992)
│   ├── PrefixSparsity.lean               # 7. Combinatorial Prefix-Sharing & Sparsity on Trees
│   ├── CyclicShift.lean                  # 8. Characteristic Polynomial of Cyclic Shift Matrices
│   ├── RamanujanTau.lean                 # 9. Ramanujan Tau Modulo 691 Congruence (1916)
│   ├── MatrixTreeTheorem.lean            # 10. Kirchhoff's Matrix-Tree Theorem (1847)
│   ├── VizingsTheorem.lean               # 11. Vizing's Theorem on Edge Colorings (1964)
│   ├── FishersInequality.lean            # 12. Fisher's Inequality for Block Designs (1940)
│   ├── GesselViennot.lean                # 13. Lindström–Gessel–Viennot Lemma (1973, 1985)
│   ├── CayleysFormula.lean               # 14. Cayley's Tree Formula & Prüfer Sequences (1889, 1918)
│   ├── KonigMatching.lean                # 15. Kőnig–Egerváry Duality Theorem (1931)
│   ├── JungsTheorem.lean                 # 16. Jung's Theorem on Circumscribed Spheres (1901)
│   ├── AlonBoppana.lean                  # 17. Alon–Boppana Spectral Lower Bound (1986)
│   ├── MengersTheorem.lean               # 18. Menger's Theorem on Disjoint Paths (1927)
│   ├── MacMahonsMasterTheorem.lean       # 19. MacMahon's Master Theorem (1915)
│   ├── ColorfulCaratheodory.lean         # 20. Bárány's Colorful Carathéodory Theorem (1982)
│   └── BlichfeldtsTheorem.lean           # 21. Blichfeldt's Theorem in Geometry of Numbers (1914)
├── lakefile.toml                         # Lake build system manifest
├── lean-toolchain                        # Pinned Lean 4 toolchain (leanprover/lean4:v4.34.0-rc1)
└── README.md
```

---

## Build and Verification

### Prerequisites
- [Elan](https://github.com/leanprover/elan) (Lean Version Manager)

### Compiling and Verifying
To fetch dependencies, download precompiled Mathlib oleans, and verify all modules:

```bash
lake update
lake exe cache get
lake build
```

Individual modules can be compiled independently:

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
lake build Formalization.ColorfulCaratheodory
lake build Formalization.BlichfeldtsTheorem
lake build Formalization
```

---

## References

1. **Alon, N.** (1986). *Eigenvalues and expanders*. Theory of Computing Systems, 19(1), 283–296.
2. **Bass, H.** (1992). *The Ihara-Selberg zeta function of a tree lattice*. International Journal of Mathematics, 3(06), 717–797.
3. **Bárány, I.** (1982). *A generalization of Carathéodory's theorem*. Discrete Mathematics, 40(2-3), 141–152.
4. **Blichfeldt, H. F.** (1914). *A new principle in the geometry of numbers, with some applications*. Transactions of the American Mathematical Society, 15(3), 227–235.
5. **Borchardt, C. W.** (1860). *Über eine der Interpolation entsprechende Darstellung der Eliminations-Resultante*. J. Reine Angew. Math., 57, 111–121.
6. **Bose, R. C.** (1949). *A note on Fisher's inequality for balanced incomplete block designs*. Bull. Calcutta Math. Soc., 41, 106–107.
7. **Brooks, R. L.** (1941). *On colouring the nodes of a network*. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194–197.
8. **Carathéodory, C.** (1907). *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen*. Rendiconti del Circolo Matematico di Palermo, 32, 193–217.
9. **Cartier, P., & Foata, D.** (1969). *Problèmes combinatoires de commutation et réarrangements*. Lecture Notes in Mathematics, 85, Springer.
10. **Cassels, J. W. S.** (1971). *An Introduction to the Geometry of Numbers*. Springer-Verlag.
11. **Cayley, A.** (1889). *A theorem on trees*. Quart. J. Math., 23, 376–378.
12. **Danzer, L., Grünbaum, B., & Klee, V.** (1963). *Helly's theorem and its relatives*. Convexity, Proc. Sympos. Pure Math., Vol. 7, 101–180.
13. **Dirac, G. A.** (1966). *Short proof of Menger's theorem*. Mathematika, 13(1), 42–44.
14. **Egerváry, J.** (1931). *Matrixok kombinatorius tulajdonságairól*. Matematikai és Fizikai Lapok, 38, 16–28.
15. **Fisher, R. A.** (1940). *An examination of the different possible solutions of a problem in incomplete blocks*. Annals of Eugenics, 10(1), 52–75.
16. **Gallai, T.** (1959). *Über extreme Punkt- und Kantenmengen*. Ann. Univ. Sci. Budapest, Eötvös Sect. Math., 2, 133–138.
17. **Gessel, I., & Viennot, G.** (1985). *Binomial determinants, paths, and hook length formulae*. Advances in Mathematics, 58(3), 300–321.
18. **Ihara, Y.** (1966). *On discrete subgroups of the two by two projective linear group over p-adic fields*. Journal of the Mathematical Society of Japan, 18(3), 219–235.
19. **Jung, H.** (1901). *Über die kleinste Kugel, die eine räumliche Figur einschliesst*. J. Reine Angew. Math., 123, 241–257.
20. **Kirchhoff, G.** (1847). *Über die Auflösung der Gleichungen, auf welche man bei der Untersuchung der linearen Vertheilung galvanischer Ströme geführt wird*. Annalen der Physik und Chemie, 148(12), 497–508.
21. **König, D.** (1916). *Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre*. Mathematische Annalen, 77(4), 453–465.
22. **Kőnig, D.** (1931). *Gráfok és mátrixok*. Matematikai és Fizikai Lapok, 38, 116–119.
23. **Lindström, B.** (1973). *On the vector representations of induced matroids*. Bulletin of the London Mathematical Society, 5(1), 85–90.
24. **Lovász, L.** (1975). *Three short proofs in graph theory*. Journal of Combinatorial Theory, Series B, 19(3), 269–271.
25. **Lubell, D.** (1966). *A short proof of Sperner's lemma*. Journal of Combinatorial Theory, 1(2), 299.
26. **Lubotzky, A., Phillips, R., & Sarnak, P.** (1988). *Ramanujan graphs*. Combinatorica, 8(3), 261–277.
27. **MacMahon, P. A.** (1915). *Combinatory Analysis* (Vol. 1 & 2). Cambridge University Press.
28. **Mantel, W.** (1907). *Vraagstuk XXVIII*. Wiskundige Opgaven, 10, 60–61.
29. **Menger, K.** (1927). *Zur allgemeinen Kurventheorie*. Fundamenta Mathematicae, 10(1), 96–115.
30. **Minkowski, H.** (1896). *Geometrie der Zahlen*. Teubner, Leipzig.
31. **Nilli, A.** (1991). *On the second eigenvalue of a graph*. Discrete Mathematics, 91(2), 207–210.
32. **Prüfer, H.** (1918). *Neuer Beweis eines Satzes über Permutationen*. Arch. Math. Phys., 27, 742–744.
33. **Ramanujan, S.** (1916). *On certain arithmetical functions*. Transactions of the Cambridge Philosophical Society, 22(9), 159–184.
34. **Schrijver, A.** (2003). *Combinatorial Optimization: Polyhedra and Efficiency*. Springer.
35. **Serre, J.-P.** (1973). *A Course in Arithmetic*. Graduate Texts in Mathematics, 7.
36. **Sperner, E.** (1928). *Ein Satz über Untermengen einer endlichen Menge*. Mathematische Zeitschrift, 27(1), 544–548.
37. **Stanley, R. P.** (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics.
38. **Stanley, R. P.** (2012). *Enumerative Combinatorics, Volume 1*. Cambridge University Press.
39. **Turán, P.** (1941). *Eine Extremalaufgabe aus der Graphentheorie*. Matematikai és Fizikai Lapok, 48, 436–452.
40. **van der Waerden, B. L.** (1927). *Beweis einer Baudetschen Vermutung*. Nieuw Archief voor Wiskunde, 15, 212–216.
41. **Vizing, V. G.** (1964). *On an estimate of the chromatic class of a p-graph*. Diskret. Analiz., 3, 25–30.
42. **Whitney, H.** (1932). *Congruent graphs and the connectivity of graphs*. Amer. J. Math., 54(1), 150–168.
43. **Yamamoto, K.** (1954). *Logarithmic order of free distributive lattice*. Journal of the Mathematical Society of Japan, 6(3-4), 343–353.

---

## License

This repository and all formalizations are dedicated to the public domain under the **[Creative Commons Zero v1.0 Universal (CC0 1.0)](LICENSE)** public domain dedication. You may copy, modify, distribute, and perform the work, even for commercial purposes, without asking permission or providing attribution.
