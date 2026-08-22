# Formalization of Combinatorial, Geometric, and Graph Theorems in Lean 4 (Part II)

This repository provides machine-checked formalizations and formalization scaffolds of classical theorems in combinatorics, graph theory, Ramsey theory, discrete geometry, projective geometry, and extremal set theory in the Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) ecosystem.

---

## Table of Theorems

| # | Theorem | Primary Declaration | Mathematical Domain | Reference |
| :---: | :--- | :--- | :--- | :--- |
| 1 | **Desargues's Theorem in Projective Planes** | [`desargues_projective_plane`](Formalization/DesarguesProjectivePlane.lean), [`desargues_dual_projective_plane`](Formalization/DesarguesProjectivePlane.lean) | Projective & Incidence Geometry | Desargues (1639), Hilbert (1899), Wiedijk #53 |
| 2 | **Sperner's Antichain Theorem & LYM Inequality** | [`sperners_antichain_theorem`](Formalization/SpernerAntichain.lean), [`lym_inequality`](Formalization/SpernerAntichain.lean), [`sperners_antichain_equality`](Formalization/SpernerAntichain.lean) | Extremal Combinatorics & Order Theory | Sperner (1928), Lubell (1966), Yamamoto (1954) |
| 3 | **Van der Waerden's Theorem on Arithmetic Progressions** | [`van_der_waerden_finite`](Formalization/VanDerWaerden.lean), [`van_der_waerden_infinite`](Formalization/VanDerWaerden.lean), [`multiple_van_der_waerden`](Formalization/VanDerWaerden.lean) | Ramsey Theory & Additive Combinatorics | Van der Waerden (1927), Wiedijk #85 |
| 4 | **Turán's Theorem & Mantel's Theorem** | [`turans_theorem`](Formalization/TuransTheorem.lean), [`turans_theorem_exact`](Formalization/TuransTheorem.lean), [`mantels_theorem`](Formalization/TuransTheorem.lean), [`turans_uniqueness`](Formalization/TuransTheorem.lean) | Extremal Graph Theory | Turán (1941), Mantel (1907) |
| 5 | **Brooks' Theorem on Graph Colorings** | [`brooks_theorem`](Formalization/BrooksTheorem.lean), [`greedy_coloring_bound`](Formalization/BrooksTheorem.lean) | Graph Theory & Chromatic Number | Brooks (1941), Lovász (1975) |
| 6 | **Erdős–Ko–Rado Stability & Hilton–Milner Theorem** | [`erdos_ko_rado_uniqueness`](Formalization/ErdosKoRadoStability.lean), [`hilton_milner_stability`](Formalization/ErdosKoRadoStability.lean) | Extremal Set Theory | Hilton & Milner (1967), Frankl (1978) |

---

## Detailed Theorem Descriptions & Formalization Highlights

### 1. Desargues's Theorem in Axiomatic Projective Planes
* **Module:** [`Formalization/DesarguesProjectivePlane.lean`](Formalization/DesarguesProjectivePlane.lean)
* **Theorems:** `desargues_projective_plane`, `desargues_dual_projective_plane`
* **Mathematical Statement:** In an axiomatic projective plane $\Pi = (\mathcal{P}, \mathcal{L}, \mathcal{I})$ satisfying the incidence axioms, two triangles $T_1 = (A_1, B_1, C_1)$ and $T_2 = (A_2, B_2, C_2)$ are in **central perspective** from a point $O$ if and only if they are in **axial perspective** from a line $L$:
  $$\text{lines } A_1 A_2, B_1 B_2, C_1 C_2 \text{ concur at } O \iff \text{points } A_1 B_1 \cap A_2 B_2, B_1 C_1 \cap B_2 C_2, C_1 A_1 \cap C_2 A_2 \text{ lie on } L$$

---

### 2. Sperner's Theorem on Antichains and the LYM Inequality
* **Module:** [`Formalization/SpernerAntichain.lean`](Formalization/SpernerAntichain.lean)
* **Theorems:** `lym_inequality`, `sperners_antichain_theorem`, `sperners_antichain_equality`
* **Mathematical Statement:**
  - **LYM Inequality:** For any antichain $\mathcal{A}$ of subsets of an $n$-element set:
    $$\sum_{A \in \mathcal{A}} \frac{1}{\binom{n}{|A|}} \le 1$$
  - **Sperner's Theorem:** The maximum size of an antichain is bounded by the middle binomial coefficient:
    $$|\mathcal{A}| \le \binom{n}{\lfloor n / 2 \rfloor}$$
  - **Equality:** Attained uniquely by the middle level slices $\binom{\alpha}{\lfloor n/2 \rfloor}$ and $\binom{\alpha}{\lceil n/2 \rceil}$.

---

### 3. Van der Waerden's Theorem on Arithmetic Progressions
* **Module:** [`Formalization/VanDerWaerden.lean`](Formalization/VanDerWaerden.lean)
* **Theorems:** `van_der_waerden_finite`, `van_der_waerden_infinite`, `multiple_van_der_waerden`
* **Mathematical Statement:** For any integers $r \ge 1$ and $k \ge 1$, there exists a positive integer $W(r, k)$ such that any $r$-coloring of $\{1, 2, \dots, W(r, k)\}$:
  $$\chi : \{1, \dots, W(r, k)\} \to \{1, \dots, r\}$$
  contains a monochromatic arithmetic progression of length $k$:
  $$\exists a, d \in \mathbb{N}, \quad d > 0, \quad \chi(a) = \chi(a + d) = \dots = \chi(a + (k-1)d)$$

---

### 4. Turán's Theorem & Mantel's Theorem in Extremal Graph Theory
* **Module:** [`Formalization/TuransTheorem.lean`](Formalization/TuransTheorem.lean)
* **Theorems:** `turans_theorem`, `turans_theorem_exact`, `mantels_theorem`, `turans_uniqueness`
* **Mathematical Statement:** If a simple graph $G = (V, E)$ on $n$ vertices contains no complete subgraph $K_{r+1}$ ($\omega(G) \le r$), then:
  $$|E(G)| \le e(T(n, r)) \le \left(1 - \frac{1}{r}\right) \frac{n^2}{2}$$
  with equality if and only if $G$ is isomorphic to the complete multipartite Turán graph $T(n, r)$.

---

### 5. Brooks' Theorem on Graph Colorings
* **Module:** [`Formalization/BrooksTheorem.lean`](Formalization/BrooksTheorem.lean)
* **Theorems:** `brooks_theorem`, `greedy_coloring_bound`
* **Mathematical Statement:** Let $G$ be a connected simple graph with maximum degree $\Delta(G) = \Delta \ge 1$. Then:
  $$\chi(G) \le \Delta$$
  unless $G$ is a complete graph $K_{\Delta+1}$ or an odd cycle $C_{2k+1}$ (with $\Delta = 2$).

---

### 6. Erdős–Ko–Rado Stability & Hilton–Milner Theorem
* **Module:** [`Formalization/ErdosKoRadoStability.lean`](Formalization/ErdosKoRadoStability.lean)
* **Theorems:** `erdos_ko_rado_uniqueness`, `hilton_milner_stability`
* **Mathematical Statement:**
  - **EKR Uniqueness:** For $n > 2k$, every intersecting family of $k$-subsets achieving the maximum cardinality $\binom{n-1}{k-1}$ is a star family (canonically centered pencil).
  - **Hilton–Milner Stability:** If an intersecting family $\mathcal{F} \subset \binom{\alpha}{k}$ is not a star, then:
    $$|\mathcal{F}| \le \binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$$

---

## Repository Structure

```text
.
├── Formalization.lean                    # Root library module importing all formalized theorems
├── Formalization/
│   ├── DesarguesProjectivePlane.lean     # 1. Desargues's Theorem in Axiomatic Projective Planes (1639)
│   ├── SpernerAntichain.lean             # 2. Sperner's Theorem on Antichains & LYM Inequality (1928, 1966)
│   ├── VanDerWaerden.lean                # 3. Van der Waerden's Theorem on Arithmetic Progressions (1927)
│   ├── TuransTheorem.lean                # 4. Turán's Theorem & Mantel's Theorem (1941, 1907)
│   ├── BrooksTheorem.lean                # 5. Brooks' Theorem on Graph Colorings (1941)
│   └── ErdosKoRadoStability.lean         # 6. Erdős–Ko–Rado Stability & Hilton–Milner Theorem (1961, 1967)
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
lake build Formalization.DesarguesProjectivePlane
lake build Formalization.SpernerAntichain
lake build Formalization.VanDerWaerden
lake build Formalization.TuransTheorem
lake build Formalization.BrooksTheorem
lake build Formalization.ErdosKoRadoStability
lake build Formalization
```

---

## References

1. **Brooks, R. L.** (1941). *On colouring the nodes of a network*. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194–197.
2. **Desargues, G.** (1639). *Brouillon project d'une atteinte aux événemens des rencontres du Cône avec un Plan*. Paris.
3. **Erdős, P., Ko, C., & Rado, R.** (1961). *Intersection theorems for systems of finite sets*. The Quarterly Journal of Mathematics, 12(1), 313–320.
4. **Hilbert, D.** (1899). *Grundlagen der Geometrie*. B. G. Teubner, Leipzig.
5. **Hilton, A. J. W., & Milner, E. C.** (1967). *Some intersection theorems for systems of finite sets*. Quarterly Journal of Mathematics, 18(1), 369–384.
6. **Lovász, L.** (1975). *Three short proofs in graph theory*. Journal of Combinatorial Theory, Series B, 19(3), 269–271.
7. **Lubell, D.** (1966). *A short proof of Sperner's lemma*. Journal of Combinatorial Theory, 1(2), 299.
8. **Mantel, W.** (1907). *Vraagstuk XXVIII*. Wiskundige Opgaven, 10, 60–61.
9. **Meshalkin, L. D.** (1963). *Generalization of Sperner's theorem on the number of subsets of a finite set*. Theory of Probability & Its Applications, 8(2), 203–204.
10. **Sperner, E.** (1928). *Ein Satz über Untermengen einer endlichen Menge*. Mathematische Zeitschrift, 27(1), 544–548.
11. **Turán, P.** (1941). *Eine Extremalaufgabe aus der Graphentheorie*. Matematikai és Fizikai Lapok, 48, 436–452.
12. **van der Waerden, B. L.** (1927). *Beweis einer Baudetschen Vermutung*. Nieuw Archief voor Wiskunde, 15, 212–216.
13. **Wiedijk, F.** (2008). *Formalizing 100 Theorems*. http://www.cs.ru.nl/~freek/100/
14. **Yamamoto, K.** (1954). *Logarithmic order of free distributive lattice*. Journal of the Mathematical Society of Japan, 6(3-4), 343–353.

---

## License

This repository and all formalizations are dedicated to the public domain under the **[Creative Commons Zero v1.0 Universal (CC0 1.0)](LICENSE)** public domain dedication. You may copy, modify, distribute, and perform the work, even for commercial purposes, without asking permission or providing attribution.
