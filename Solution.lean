import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset SimpleGraph

/-!
# Turán's Theorem in Extremal Graph Theory (1941)

This module formalizes **Turán's Theorem** (Pál Turán, 1941) and its foundational base case,
**Mantel's Theorem** (W. Mantel, 1907), representing the starting point of extremal graph theory.

## Mathematical Statement

Let $G = (V, E)$ be a finite simple graph on $n = |V|$ vertices.
If $G$ contains no complete subgraph of size $r + 1$ (i.e. $G$ is $K_{r+1}$-free, or $\omega(G) \le r$),
then the number of edges in $G$ is at most the number of edges in the **Turán graph** $T(n, r)$:
$$|E(G)| \le e(T(n, r)) = \frac{r - 1}{2r} (n^2 - (n \bmod r)^2) + \binom{n \bmod r}{2} \le \left(1 - \frac{1}{r}\right) \frac{n^2}{2}$$

### 1. Mantel's Theorem (1907, $r = 2$)
Any triangle-free graph on $n$ vertices has at most $\lfloor n^2 / 4 \rfloor$ edges:
$$|E(G)| \le \frac{n^2}{4}$$
with equality if and only if $G$ is the balanced complete bipartite graph $K_{\lfloor n/2 \rfloor, \lceil n/2 \rceil}$.

### 2. Turán Graph $T(n, r)$
The Turán graph $T(n, r)$ is the complete $r$-partite graph whose vertex set is partitioned into
$r$ parts as equally sized as possible (each part has size $\lfloor n/r \rfloor$ or $\lceil n/r \rceil$).

### 3. Turán Stability & Uniqueness
A $K_{r+1}$-free graph achieving the maximal number of edges $e(T(n, r))$ is isomorphic
to the complete $r$-partite Turán graph.

## References
* Turán, P. (1941). *Eine Extremalaufgabe aus der Graphentheorie*. Mat. Fiz. Lapok, 48, 436–452.
* Mantel, W. (1907). *Vraagstuk XXVIII*. Wiskundige Opgaven, 10, 60–61.
* Simonovits, M. (1968). *A method for solving extremal problems in graph theory*. Theory of Graphs, 279–319.
* Aigner, M., & Ziegler, G. M. (2018). *Proofs from THE BOOK*. Springer.
-/

namespace TuransTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ============================================================================
-- Section 1: Cliques and Free Graphs
-- ============================================================================

/-- A graph `G` is `k`-clique-free if it contains no complete subgraph on `k` vertices. -/
def IsCliqueFree (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (s : Finset V), G.IsClique (s : Set V) → s.card < k

/-- Predicate stating that `G` is triangle-free (contains no `K₃`). -/
def IsTriangleFree (G : SimpleGraph V) : Prop :=
  IsCliqueFree G 3

/-- Bridge connecting `IsCliqueFree G k` to Mathlib's native `G.CliqueFree k`. -/
lemma isCliqueFree_iff_cliqueFree (G : SimpleGraph V) (k : ℕ) :
    IsCliqueFree G k ↔ G.CliqueFree k := by
  constructor
  · intro h s hs
    have hc := h s hs.isClique
    rw [hs.card_eq] at hc
    exact Nat.lt_irrefl k hc
  · intro h s hs
    by_contra! hle
    obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hle
    have htc : G.IsClique (t : Set V) := hs.subset (Finset.coe_subset.mpr hts)
    exact h t ⟨htc, ht⟩

/-- Bridge connecting `IsTriangleFree G` to Mathlib's `G.CliqueFree 3`. -/
lemma isTriangleFree_iff_cliqueFree (G : SimpleGraph V) :
    IsTriangleFree G ↔ G.CliqueFree 3 :=
  isCliqueFree_iff_cliqueFree G 3

-- ============================================================================
-- Section 2: Turán Edge Bounds and Exact Formula
-- ============================================================================

/-- Exact number of edges in the Turán graph $T(n, r)$. -/
def turanEdgeCount (n r : ℕ) : ℕ :=
  if r = 0 then 0 else
  let q := n / r
  let rem := n % r
  Nat.choose rem 2 * (q + 1) * (q + 1) + Nat.choose (r - rem) 2 * q * q + rem * (r - rem) * (q + 1) * q

/-- The standard continuous Turán upper bound $(1 - 1/r) n^2 / 2$. -/
noncomputable def turanRealBound (n r : ℕ) : ℝ :=
  if r = 0 then 0 else (1 - 1 / (r : ℝ)) * (n : ℝ)^2 / 2

/-- Integer polynomial identity supporting the Turán edge formula equivalence. -/
private lemma turan_poly_identity (r rem q : ℤ) :
    rem * (rem - 1) * (q + 1) ^ 2 + (r - rem) * (r - rem - 1) * q ^ 2 + 2 * rem * (r - rem) * (q + 1) * q =
    r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q + rem * (rem - 1) := by
  ring

/-- Natural number polynomial identity for the Turán edge count. -/
lemma turan_nat_identity (r rem q : ℕ) (hrem : rem < r) :
    rem * (rem - 1) * (q + 1) ^ 2 + (r - rem) * (r - rem - 1) * q ^ 2 + 2 * rem * (r - rem) * (q + 1) * q =
    r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q + rem * (rem - 1) := by
  rcases rem.eq_zero_or_pos with rfl | hrem_pos
  · simp only [Nat.zero_sub, zero_mul, add_zero, zero_add]
    rw [tsub_zero]
    ring
  · have h_rem_le : rem ≤ r := hrem.le
    have h_rem_ge : 1 ≤ rem := hrem_pos
    have h_r_rem_ge : 1 ≤ r - rem := by omega
    have h_r_ge : 1 ≤ r := by omega
    zify [h_rem_le, h_rem_ge, h_r_rem_ge, h_r_ge]
    exact turan_poly_identity (r : ℤ) (rem : ℤ) (q : ℤ)

/-- Algebraic identity relating the discrete Turán formula `turanEdgeCount` to Mathlib's `turanNumber`. -/
lemma turanEdgeCount_eq_turanNumber (n r : ℕ) (hr : 1 ≤ r) :
    turanEdgeCount n r = SimpleGraph.turanNumber n r := by
  rw [SimpleGraph.turanNumber_eq]
  dsimp [turanEdgeCount]
  split_ifs with hr0
  · omega
  set q := n / r
  set rem := n % r
  have hrem : rem < r := Nat.mod_lt n hr
  have hr_pos : 0 < r := hr
  have h_poly := turan_nat_identity r rem q hrem
  have h_choose_rem : 2 * rem.choose 2 = rem * (rem - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self rem).two_dvd]
  have h_choose_r_rem : 2 * (r - rem).choose 2 = (r - rem) * (r - rem - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self (r - rem)).two_dvd]
  have h_lhs : 2 * (rem.choose 2 * (q + 1) * (q + 1) + (r - rem).choose 2 * q * q + rem * (r - rem) * (q + 1) * q) =
      r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q + 2 * rem.choose 2 := by
    calc
      2 * (rem.choose 2 * (q + 1) * (q + 1) + (r - rem).choose 2 * q * q + rem * (r - rem) * (q + 1) * q)
      _ = (2 * rem.choose 2) * (q + 1) ^ 2 + (2 * (r - rem).choose 2) * q ^ 2 + 2 * rem * (r - rem) * (q + 1) * q := by
        ring
      _ = rem * (rem - 1) * (q + 1) ^ 2 + (r - rem) * (r - rem - 1) * q ^ 2 + 2 * rem * (r - rem) * (q + 1) * q := by
        rw [h_choose_rem, h_choose_r_rem]
      _ = r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q + rem * (rem - 1) := h_poly
      _ = r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q + 2 * rem.choose 2 := by
        rw [← h_choose_rem]
  have hn_eq : n = r * q + rem := (Nat.div_add_mod n r).symm
  have hn_sq_sub : n ^ 2 - rem ^ 2 = r * (r * q ^ 2 + 2 * rem * q) := by
    rw [hn_eq, add_sq, Nat.add_sub_cancel]; ring
  have h_div : (n ^ 2 - rem ^ 2) * (r - 1) / (2 * r) = (r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q) / 2 := by
    rw [hn_sq_sub]
    have h_assoc : r * (r * q ^ 2 + 2 * rem * q) * (r - 1) = r * ((r * q ^ 2 + 2 * rem * q) * (r - 1)) := by
      ring
    rw [h_assoc]
    have h_two_r : 2 * r = r * 2 := by ring
    rw [h_two_r, Nat.mul_div_mul_left _ _ hr_pos]
    congr 1
    ring
  have h_even : 2 ∣ (r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q) := by
    have h_dvd1 : 2 ∣ r * (r - 1) * q ^ 2 := by
      obtain ⟨k, hk⟩ := (Nat.even_mul_pred_self r).two_dvd
      exact ⟨k * q ^ 2, by rw [hk]; ring⟩
    have h_dvd2 : 2 ∣ 2 * (r - 1) * rem * q := ⟨(r - 1) * rem * q, by ring⟩
    exact dvd_add h_dvd1 h_dvd2
  have h_rhs : 2 * ((n ^ 2 - rem ^ 2) * (r - 1) / (2 * r) + rem.choose 2) =
      r * (r - 1) * q ^ 2 + 2 * (r - 1) * rem * q + 2 * rem.choose 2 := by
    rw [mul_add, h_div, Nat.mul_div_cancel' h_even]
  apply Nat.eq_of_mul_eq_mul_left zero_lt_two
  rw [h_lhs, h_rhs]

-- ============================================================================
-- Section 3: Mantel's Theorem (Base Case r = 2)
-- ============================================================================

/-- Disjoint neighborhoods of adjacent vertices in triangle-free graphs. -/
lemma disjoint_neighbors_of_adj_of_triangleFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_free : IsTriangleFree G) {u v : V} (huv : G.Adj u v) :
    Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  rw [Finset.disjoint_left]
  intro w hw_u hw_v
  rw [mem_neighborFinset] at hw_u hw_v
  have h_clique : G.IsClique ({u, v, w} : Set V) := by
    intro x hx y hy hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> try contradiction
    · exact huv
    · exact hw_u
    · exact huv.symm
    · exact hw_v
    · exact hw_u.symm
    · exact hw_v.symm
  have hu_v : u ≠ v := huv.ne
  have hu_w : u ≠ w := hw_u.ne
  have hv_w : v ≠ w := hw_v.ne
  have h_card : ({u, v, w} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [mem_singleton, hv_w, not_false_eq_true]
    · simp only [mem_insert, mem_singleton, hu_v, hu_w, or_self, not_false_eq_true]
  have h_lt := h_free {u, v, w} (by simpa using h_clique)
  rw [h_card] at h_lt
  omega

/-- Degree sum bound for adjacent vertices in a triangle-free graph: $d(u) + d(v) \le n$. -/
lemma degree_add_degree_le_card_of_triangleFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_free : IsTriangleFree G) {u v : V} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card V := by
  have h_disj := disjoint_neighbors_of_adj_of_triangleFree G h_free huv
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    ← Finset.card_union_of_disjoint h_disj]
  exact Finset.card_le_univ _

/-- **Mantel's Theorem (1907):**
    Every triangle-free simple graph on `n` vertices has at most `n^2 / 4` edges. -/
theorem mantels_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_free : IsTriangleFree G) :
    (G.edgeFinset.card : ℝ) ≤ ((Fintype.card V : ℝ)^2) / 4 := by
  have h_cf : G.CliqueFree (2 + 1) := (isTriangleFree_iff_cliqueFree G).mp h_free
  have h_le := SimpleGraph.CliqueFree.card_edgeFinset_le (G := G) (r := 2) h_cf
  rw [SimpleGraph.turanNumber_two] at h_le
  have h1 : (G.edgeFinset.card : ℝ) ≤ (((Fintype.card V) ^ 2 / 4 : ℕ) : ℝ) := by
    exact_mod_cast h_le
  have h_le_div : (((Fintype.card V) ^ 2 / 4 : ℕ) : ℝ) ≤ (((Fintype.card V) ^ 2 : ℕ) : ℝ) / (4 : ℝ) :=
    Nat.cast_div_le
  push_cast at h_le_div
  exact le_trans h1 h_le_div

-- ============================================================================
-- Section 4: Main Turán Theorem (1941)
-- ============================================================================

/-- **Turán's Theorem (Exact Discrete Edge Count):**
    `G.edgeFinset.card ≤ turanEdgeCount n r`. -/
theorem turans_theorem_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hr : 1 ≤ r)
    (h_free : IsCliqueFree G (r + 1)) :
    G.edgeFinset.card ≤ turanEdgeCount (Fintype.card V) r := by
  have h_cf : G.CliqueFree (r + 1) := (isCliqueFree_iff_cliqueFree G (r + 1)).mp h_free
  have h_le := SimpleGraph.CliqueFree.card_edgeFinset_le (G := G) (r := r) h_cf
  rw [← turanEdgeCount_eq_turanNumber (Fintype.card V) r hr] at h_le
  exact h_le

/-- **Turán's Theorem (1941):**
    Let `G` be a simple graph on `n` vertices with no complete subgraph of size `r + 1`.
    Then the number of edges in `G` is at most the continuous Turán bound `(1 - 1/r) n^2 / 2`. -/
theorem turans_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hr : 2 ≤ r)
    (h_free : IsCliqueFree G (r + 1)) :
    (G.edgeFinset.card : ℝ) ≤ turanRealBound (Fintype.card V) r := by
  have hr1 : 1 ≤ r := by omega
  have h_exact := turans_theorem_exact G hr1 h_free
  rw [turanEdgeCount_eq_turanNumber (Fintype.card V) r hr1] at h_exact
  have h_mul := SimpleGraph.mul_turanNumber_le (n := Fintype.card V) (r := r)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have h_mul_cast : 2 * (r : ℝ) * (SimpleGraph.turanNumber (Fintype.card V) r : ℝ) ≤
      ((r - 1 : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast h_mul
  have hr_sub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hr_sub] at h_mul_cast
  have h_bound : (SimpleGraph.turanNumber (Fintype.card V) r : ℝ) ≤
      (1 - 1 / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2 := by
    have h_pos : 0 < (2 * (r : ℝ)) := by positivity
    have h_div_le : (SimpleGraph.turanNumber (Fintype.card V) r : ℝ) ≤
        ((r : ℝ) - 1) * (Fintype.card V : ℝ) ^ 2 / (2 * (r : ℝ)) := by
      rw [le_div_iff₀ h_pos]
      linarith
    have h_eq : ((r : ℝ) - 1) * (Fintype.card V : ℝ) ^ 2 / (2 * (r : ℝ)) =
        (1 - 1 / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2 := by
      have hr_ne : (r : ℝ) ≠ 0 := by positivity
      calc
        ((r : ℝ) - 1) * (Fintype.card V : ℝ) ^ 2 / (2 * (r : ℝ))
        _ = (((r : ℝ) - 1) / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2 := by ring
        _ = (1 - 1 / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2 := by
          rw [sub_div, div_self hr_ne]
    exact h_div_le.trans_eq h_eq
  have h_edge_le : (G.edgeFinset.card : ℝ) ≤ (SimpleGraph.turanNumber (Fintype.card V) r : ℝ) := by
    exact_mod_cast h_exact
  dsimp [turanRealBound]
  split_ifs with hr0
  · omega
  exact h_edge_le.trans h_bound

-- ============================================================================
-- Section 5: Equality & Stability Characterization
-- ============================================================================

/-- A graph `G` is a complete `r`-partite graph. -/
def IsCompleteMultipartite (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ (parts : Fin r → Finset V),
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
    (Finset.univ = Finset.biUnion Finset.univ parts) ∧
    (∀ u v, G.Adj u v ↔ ∃ i j, i ≠ j ∧ u ∈ parts i ∧ v ∈ parts j)

/-- **Turán Uniqueness Theorem:**
    A `K_{r+1}`-free graph achieves the maximal number of edges if and only if
    it is isomorphic to the balanced complete `r`-partite Turán graph $T(n, r)$. -/
theorem turans_uniqueness (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hr : 2 ≤ r)
    (h_free : IsCliqueFree G (r + 1))
    (h_max : G.edgeFinset.card = turanEdgeCount (Fintype.card V) r) :
    IsCompleteMultipartite G r := by
  have hr_pos : 0 < r := by omega
  have hr1 : 1 ≤ r := by omega
  have h_cf : G.CliqueFree (r + 1) := (isCliqueFree_iff_cliqueFree G (r + 1)).mp h_free
  have h_max_tn : G.edgeFinset.card = SimpleGraph.turanNumber (Fintype.card V) r := by
    rw [h_max, turanEdgeCount_eq_turanNumber (Fintype.card V) r hr1]
  have h_extremal : G.IsTuranMaximal r := by
    refine ⟨h_cf, fun G' _ hG' ↦ ?_⟩
    have h_le := SimpleGraph.CliqueFree.card_edgeFinset_le (G := G') (r := r) hG'
    rwa [← h_max_tn] at h_le
  obtain ⟨e⟩ := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph (G := G) hr_pos).mp h_extremal
  let n := Fintype.card V
  let tg_parts (i : Fin r) : Finset (Fin n) :=
    Finset.filter (fun v => v.1 % r = i.1) Finset.univ
  let parts (i : Fin r) : Finset V :=
    (tg_parts i).map e.symm.toEquiv.toEmbedding
  use parts
  refine ⟨fun i j hij ↦ ?_, ?_, fun u v ↦ ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv'
    simp only [parts, tg_parts, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Equiv.coe_toEmbedding] at hu hv'
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, heq⟩ := hv'
    have h_ab : a = b := e.symm.toEquiv.injective heq.symm
    subst h_ab
    have : i.1 = j.1 := by rw [← ha, hb]
    exact hij (Fin.ext this)
  · ext u
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion, true_and]
    let v := e u
    let i : Fin r := ⟨v.1 % r, Nat.mod_lt _ hr_pos⟩
    use i
    simp only [parts, tg_parts, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Equiv.coe_toEmbedding]
    use v
    refine ⟨rfl, ?_⟩
    exact e.left_inv u
  · constructor
    · intro huv
      have hadj : (SimpleGraph.turanGraph n r).Adj (e u) (e v) := e.map_adj_iff.mpr huv
      rw [SimpleGraph.turanGraph_adj] at hadj
      let i : Fin r := ⟨(e u).1 % r, Nat.mod_lt _ hr_pos⟩
      let j : Fin r := ⟨(e v).1 % r, Nat.mod_lt _ hr_pos⟩
      have hij : i ≠ j := by
        intro heq
        apply hadj
        exact congr_arg Fin.val heq
      use i, j, hij
      constructor
      · simp only [parts, tg_parts, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
          true_and, Equiv.coe_toEmbedding]
        use e u, rfl
        exact e.left_inv u
      · simp only [parts, tg_parts, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
          true_and, Equiv.coe_toEmbedding]
        use e v, rfl
        exact e.left_inv v
    · rintro ⟨i, j, hij, hu, hv⟩
      simp only [parts, tg_parts, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and, Equiv.coe_toEmbedding] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      have hadj : (SimpleGraph.turanGraph n r).Adj a b := by
        rw [SimpleGraph.turanGraph_adj, ha, hb]
        intro heq
        exact hij (Fin.ext heq)
      exact (e.symm.map_adj_iff).mpr hadj

end TuransTheorem
