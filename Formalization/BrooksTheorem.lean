import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset SimpleGraph

/-!
# Brooks' Theorem on Graph Colorings (1941)

This module formalizes **Brooks' Theorem** (R. L. Brooks, 1941), a foundational result
in graph theory and vertex coloring.

## Mathematical Statement

Let $G = (V, E)$ be a connected simple graph with maximum degree $\Delta(G) = \Delta \ge 1$.
Then the chromatic number $\chi(G)$ of $G$ satisfies:
$$\chi(G) \le \Delta$$
**unless** $G$ is one of two exceptional families:
1. $G$ is a complete graph $K_{\Delta + 1}$ (where $\chi(K_{\Delta + 1}) = \Delta + 1$).
2. $\Delta = 2$ and $G$ is an odd cycle $C_{2k+1}$ (where $\chi(C_{2k+1}) = 3 = \Delta + 1$).

For all other connected graphs (in particular, any graph with $\Delta \ge 3$ that is not a clique),
$G$ can be properly colored with $\Delta$ colors.

## Proof Techniques
1. **Greedy Coloring ($\chi(G) \le \Delta + 1$):**
   Ordering the vertices $v_1, \dots, v_n$ allows a greedy coloring where each vertex has at most $\Delta$
   previously colored neighbors, never exhausting $\Delta + 1$ available colors.
2. **2-Connected Reduction & Spanning DFS Trees:**
   When $G$ is 2-connected and not regular, one can find a vertex of degree $< \Delta$ and order the vertices
   towards it. When $G$ is $\Delta$-regular and 3-connected, one can find a pair of non-adjacent vertices
   $v_1, v_2$ with a common neighbor $v_n$ such that $G \setminus \{v_1, v_2\}$ is connected,
   giving $v_1$ and $v_2$ the same color and greedily coloring the rest.

## References
* Brooks, R. L. (1941). *On colouring the nodes of a network*. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194–197.
* Lovász, L. (1975). *Three short proofs in graph theory*. Journal of Combinatorial Theory, Series B, 19(3), 269–271.
* Diestel, R. (2017). *Graph Theory*. 5th edition, Springer.
* Freek Wiedijk. *Formalizing 100 Theorems*.
-/

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ============================================================================
-- Section 1: Maximum Degree and Proper Colorings
-- ============================================================================

/-- Maximum degree $\Delta(G)$ of a finite graph $G$. -/
def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun v => G.degree v)

lemma degree_le_maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ≤ maxDegree G :=
  Finset.le_sup (f := fun u => G.degree u) (Finset.mem_univ v)

/-- Predicate asserting that coloring `c` is a proper vertex coloring of `G`. -/
def IsProperColoring (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- Predicate asserting that graph `G` is `k`-colorable ($\chi(G) \le k$). -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring G c

/-- Bridge between `IsKColorable G k` and Mathlib's native `G.Colorable k`. -/
lemma isKColorable_iff_colorable (G : SimpleGraph V) (k : ℕ) :
    IsKColorable G k ↔ G.Colorable k := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c (fun hadj => hc _ _ hadj)⟩
  · rintro ⟨C⟩
    exact ⟨C.toFun, fun u v hadj => C.valid hadj⟩

/-- Monotonicity of colorability: if $G$ is $k$-colorable, it is also $m$-colorable for any $m \ge k$. -/
lemma isKColorable_mono (G : SimpleGraph V) {k m : ℕ} (hkm : k ≤ m) (h : IsKColorable G k) :
    IsKColorable G m := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v => (c v).castLE hkm, ?_⟩
  intro u v hadj heq
  have hc_ne := hc u v hadj
  dsimp at heq
  have h_val : ((c u).castLE hkm : ℕ) = ((c v).castLE hkm : ℕ) := congrArg Fin.val heq
  have : c u = c v := Fin.ext h_val
  exact hc_ne this

-- ============================================================================
-- Section 2: Exceptional Graphs (Cliques and Odd Cycles)
-- ============================================================================

/-- A graph is complete ($K_n$) if every pair of distinct vertices is adjacent. -/
def IsCompleteGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v

lemma exists_not_adj_of_not_complete (G : SimpleGraph V) (h : ¬ IsCompleteGraph G) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v := by
  dsimp [IsCompleteGraph] at h
  push Not at h
  exact h

/-- Any graph on at most `k` vertices is `k`-colorable. -/
lemma isKColorable_of_card_le (G : SimpleGraph V) (k : ℕ) (h : Fintype.card V ≤ k) :
    IsKColorable G k := by
  let f : V → Fin k := fun v => (Fintype.equivFin V v).castLE h
  refine ⟨f, ?_⟩
  intro u v hadj heq
  have hne : u ≠ v := G.ne_of_adj hadj
  dsimp [f] at heq
  have hval : ((Fintype.equivFin V u).castLE h : ℕ) = ((Fintype.equivFin V v).castLE h : ℕ) :=
    congrArg Fin.val heq
  dsimp at hval
  have hequiv : Fintype.equivFin V u = Fintype.equivFin V v := Fin.ext hval
  have : u = v := (Fintype.equivFin V).injective hequiv
  exact hne this

/-- Any graph on `k + 1` vertices that is not complete is `k`-colorable (`k ≥ 1`). -/
lemma isKColorable_of_card_eq_succ_not_complete (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 1 ≤ k) (h_card : Fintype.card V = k + 1) (h_not_comp : ¬ IsCompleteGraph G) :
    IsKColorable G k := by
  obtain ⟨u, v, h_ne, h_not_adj⟩ := exists_not_adj_of_not_complete G h_not_comp
  let S : Finset V := (Finset.univ.erase u).erase v
  have hu_notin_S : u ∉ S := by
    intro h
    rw [Finset.mem_erase, Finset.mem_erase] at h
    exact h.2.1 rfl
  have hv_notin_S : v ∉ S := by
    intro h
    rw [Finset.mem_erase] at h
    exact h.1 rfl
  have h_card_S : S.card = k - 1 := by
    have hu_mem : u ∈ (Finset.univ : Finset V) := Finset.mem_univ u
    have hv_mem : v ∈ (Finset.univ : Finset V).erase u := by
      rw [Finset.mem_erase]
      exact ⟨h_ne.symm, Finset.mem_univ v⟩
    have h1 : ((Finset.univ : Finset V).erase u).card = Fintype.card V - 1 :=
      Finset.card_erase_of_mem hu_mem
    have h2 : S.card = ((Finset.univ : Finset V).erase u).card - 1 :=
      Finset.card_erase_of_mem hv_mem
    omega
  let S_type := { x : V // x ∈ S }
  haveI : Fintype S_type := Subtype.fintype (fun x => x ∈ S)
  have h_card_Stype : Fintype.card S_type = k - 1 := by
    rw [Fintype.card_coe, h_card_S]
  let e : S_type ≃ Fin (k - 1) := Fintype.equivFin S_type |>.trans (Fin.castOrderIso h_card_Stype).toEquiv
  let c : V → Fin k := fun x =>
    if hx : x = u ∨ x = v then
      ⟨0, hk⟩
    else
      have hxS : x ∈ S := by
        push Not at hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨hx.2, ⟨hx.1, Finset.mem_univ x⟩⟩
      let sx : S_type := ⟨x, hxS⟩
      ⟨(e sx : ℕ) + 1, by
        have : (e sx : ℕ) < k - 1 := (e sx).isLt
        omega⟩
  refine ⟨c, ?_⟩
  intro x y hadj
  have hxy_ne : x ≠ y := G.ne_of_adj hadj
  dsimp [c]
  split_ifs with hx hy hy
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (G.irrefl hadj)
    · exact False.elim (h_not_adj hadj)
    · exact False.elim (h_not_adj (G.adj_symm hadj))
    · exact False.elim (G.irrefl hadj)
  · intro heq
    have h_val : 0 = (e ⟨y, _⟩ : ℕ) + 1 := congrArg Fin.val heq
    omega
  · intro heq
    have h_val : (e ⟨x, _⟩ : ℕ) + 1 = 0 := congrArg Fin.val heq
    omega
  · intro heq
    injection heq with h_inj
    have hxS : x ∈ S := by
      push Not at hx
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hx.2, ⟨hx.1, Finset.mem_univ x⟩⟩
    have hyS : y ∈ S := by
      push Not at hy
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hy.2, ⟨hy.1, Finset.mem_univ y⟩⟩
    have hx_eq : (⟨x, _⟩ : S_type) = ⟨x, hxS⟩ := Subtype.ext rfl
    have hy_eq : (⟨y, _⟩ : S_type) = ⟨y, hyS⟩ := Subtype.ext rfl
    rw [hx_eq, hy_eq] at h_inj
    have h_eval : (e ⟨x, hxS⟩ : ℕ) = (e ⟨y, hyS⟩ : ℕ) := by omega
    have he_eq : e ⟨x, hxS⟩ = e ⟨y, hyS⟩ := Fin.ext h_eval
    have h_sub_eq : (⟨x, hxS⟩ : S_type) = ⟨y, hyS⟩ := e.injective he_eq
    have : x = y := Subtype.ext_iff.mp h_sub_eq
    exact hxy_ne this

/-- If two non-adjacent vertices $u, v$ are identified via the quotient map
    $\pi(x) = \text{if } x = v \text{ then } u \text{ else } x$, any proper coloring
    of the merged graph pulls back to a proper coloring of the original graph $G$. -/
lemma properColoring_of_pullback (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (u v : V) (h_ne : u ≠ v) (h_not_adj : ¬ G.Adj u v)
    (c : V → Fin k)
    (hc : ∀ x y : V, x ≠ y →
      (∃ a b, (if a = v then u else a) = x ∧ (if b = v then u else b) = y ∧ G.Adj a b) → c x ≠ c y) :
    IsProperColoring G (fun x => c (if x = v then u else x)) := by
  intro a b hadj
  let pi := fun x : V => if x = v then u else x
  have h_pi_ne : pi a ≠ pi b := by
    intro h_eq
    have h_pia : pi a = if a = v then u else a := rfl
    have h_pib : pi b = if b = v then u else b := rfl
    rw [h_pia, h_pib] at h_eq
    by_cases ha : a = v <;> by_cases hb : b = v
    · subst ha; subst hb; exact False.elim (G.irrefl hadj)
    · simp only [ha, hb, ↓reduceIte] at h_eq
      have h_vb : G.Adj v b := ha ▸ hadj
      have h_vu : G.Adj v u := h_eq ▸ h_vb
      exact False.elim (h_not_adj (G.adj_symm h_vu))
    · simp only [ha, hb, ↓reduceIte] at h_eq
      have h_av : G.Adj a v := hb ▸ hadj
      have h_uv : G.Adj u v := h_eq ▸ h_av
      exact False.elim (h_not_adj h_uv)
    · simp only [ha, hb, ↓reduceIte] at h_eq
      exact False.elim (hadj.ne h_eq)
  exact hc (pi a) (pi b) h_pi_ne ⟨a, b, rfl, rfl, hadj⟩

/-- A proper coloring of a complete graph must assign distinct colors to every vertex. -/
lemma completeGraph_coloring_injective (G : SimpleGraph V) {k : ℕ} (h_comp : IsCompleteGraph G)
    (c : V → Fin k) (hc : IsProperColoring G c) : Function.Injective c := by
  intro u v heq
  by_contra hne
  have hadj := h_comp u v hne
  exact hc u v hadj heq

/-- Complete graph on $n$ vertices requires at least $n$ colors. -/
lemma completeGraph_card_le_of_properColoring (G : SimpleGraph V) {k : ℕ} (h_comp : IsCompleteGraph G)
    (c : V → Fin k) (hc : IsProperColoring G c) : Fintype.card V ≤ k := by
  have hinj := completeGraph_coloring_injective G h_comp c hc
  have hle := Fintype.card_le_of_injective c hinj
  rwa [Fintype.card_fin] at hle

/-- A complete graph cannot be colored with fewer than $|V|$ colors. -/
lemma not_colorable_completeGraph (G : SimpleGraph V) {k : ℕ} (h_comp : IsCompleteGraph G)
    (hk : k < Fintype.card V) : ¬ IsKColorable G k := by
  rintro ⟨c, hc⟩
  have := completeGraph_card_le_of_properColoring G h_comp c hc
  omega

/-- A graph is an odd cycle $C_{2k+1}$. -/
def IsOddCycle (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Odd (Fintype.card V) ∧ (∀ v : V, G.degree v = 2) ∧ G.Preconnected

lemma fin2_cases (y : Fin 2) : y = 0 ∨ y = 1 := by
  revert y
  decide

/-- An odd cycle is not 2-colorable (requires at least 3 colors). -/
lemma odd_cycle_not_two_colorable (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_odd : IsOddCycle G) : ¬ IsKColorable G 2 := by
  rintro ⟨c, hc⟩
  let V0 := Finset.univ.filter (fun v => c v = 0)
  let V1 := Finset.univ.filter (fun v => c v = 1)
  have h_disj : Disjoint V0 V1 := by
    rw [Finset.disjoint_filter]
    intro x _ h0 h1
    have h_ne : (0 : Fin 2) ≠ 1 := by decide
    exact h_ne (h0.symm.trans h1)
  have h_union : V0 ∪ V1 = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, V0, V1]
    exact iff_true_intro (fin2_cases (c x))
  have h_card_sum : V0.card + V1.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ]
  have h_neighbors_0 : ∀ u ∈ V0, ∀ w ∈ G.neighborFinset u, w ∈ V1 := by
    intro u hu w hw
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ w, ?_⟩
    have hadj := (G.mem_neighborFinset u w).mp hw
    have hc_ne := hc u w hadj
    have hc_u : c u = 0 := hu.2
    rcases fin2_cases (c w) with h0 | h1
    · rw [hc_u, h0] at hc_ne
      exact False.elim (hc_ne rfl)
    · exact h1
  have h_neighbors_1 : ∀ w ∈ V1, ∀ u ∈ G.neighborFinset w, u ∈ V0 := by
    intro w hw u hu
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ u, ?_⟩
    have hadj := (G.mem_neighborFinset w u).mp hu
    have hc_ne := hc w u hadj
    have hc_w : c w = 1 := hw.2
    rcases fin2_cases (c u) with h0 | h1
    · exact h0
    · rw [hc_w, h1] at hc_ne
      exact False.elim (hc_ne rfl)
  have h_sum0 : ∑ u ∈ V0, (G.neighborFinset u).card = 2 * V0.card := by
    have : (∑ u ∈ V0, (G.neighborFinset u).card) = ∑ u ∈ V0, 2 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [G.card_neighborFinset_eq_degree]
      exact h_odd.2.1 u
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have h_sum1 : ∑ w ∈ V1, (G.neighborFinset w).card = 2 * V1.card := by
    have : (∑ w ∈ V1, (G.neighborFinset w).card) = ∑ w ∈ V1, 2 := by
      apply Finset.sum_congr rfl
      intro w _
      rw [G.card_neighborFinset_eq_degree]
      exact h_odd.2.1 w
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have h_double_sum : (∑ u ∈ V0, (G.neighborFinset u).card) = (∑ w ∈ V1, (G.neighborFinset w).card) := by
    have h_lhs : (∑ u ∈ V0, (G.neighborFinset u).card) =
        ∑ u ∈ V0, ∑ w ∈ V1, (if G.Adj u w then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have h_sub : G.neighborFinset u ⊆ V1 := h_neighbors_0 u hu
      have h_filter : (G.neighborFinset u) = V1.filter (fun w => G.Adj u w) := by
        ext w
        simp only [Finset.mem_filter, G.mem_neighborFinset]
        constructor
        · intro hw
          exact ⟨h_sub ((G.mem_neighborFinset u w).mpr hw), hw⟩
        · intro ⟨_, hw⟩
          exact hw
      rw [h_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    have h_rhs : (∑ w ∈ V1, (G.neighborFinset w).card) =
        ∑ w ∈ V1, ∑ u ∈ V0, (if G.Adj w u then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      have h_sub : G.neighborFinset w ⊆ V0 := h_neighbors_1 w hw
      have h_filter : (G.neighborFinset w) = V0.filter (fun u => G.Adj w u) := by
        ext u
        simp only [Finset.mem_filter, G.mem_neighborFinset]
        constructor
        · intro hu
          exact ⟨h_sub ((G.mem_neighborFinset w u).mpr hu), hu⟩
        · intro ⟨_, hu⟩
          exact hu
      rw [h_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [h_lhs, h_rhs, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro w _
    by_cases hadj : G.Adj u w
    · have hadj_symm : G.Adj w u := G.adj_symm hadj
      simp [hadj, hadj_symm]
    · have hadj_symm : ¬ G.Adj w u := fun h => hadj (G.adj_symm h)
      simp [hadj, hadj_symm]
  rw [h_sum0, h_sum1] at h_double_sum
  have h_eq_card : V0.card = V1.card := by omega
  have h_even : Even (Fintype.card V) := by
    use V0.card
    omega
  have h_not_even := Nat.not_even_iff_odd.mpr h_odd.1
  exact h_not_even h_even

lemma card_image_erase_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (u v : α) (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (heq : f u = f v) :
    (s.image f).card ≤ s.card - 1 := by
  have h_eq : s.image f = (s.erase v).image f := by
    ext b
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst hxv
        refine ⟨u, ⟨hne, hu⟩, heq⟩
      · refine ⟨x, ⟨hxv, hx⟩, rfl⟩
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [h_eq]
  have h1 : ((s.erase v).image f).card ≤ (s.erase v).card := Finset.card_image_le
  have h2 : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hv
  omega

-- ============================================================================
-- Section 3: Greedy and Ordered Graph Colorings
-- ============================================================================

/-- If vertices can be ordered such that every vertex has fewer than `k` previously
    colored neighbors in the ordering, then the graph is `k`-colorable. -/
lemma colorable_of_ordered_degree_lt (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (ord : Fin (Fintype.card V) ≃ V)
    (h_deg : ∀ i : Fin (Fintype.card V),
      ((Finset.univ.filter (fun j : Fin (Fintype.card V) => (j : ℕ) < (i : ℕ) ∧ G.Adj (ord i) (ord j))).card < k)) :
    IsKColorable G k := by
  have h_ind : ∀ m ≤ Fintype.card V,
      ∃ c : V → Fin k, ∀ (i j : Fin (Fintype.card V)),
        (i : ℕ) < m → (j : ℕ) < m → G.Adj (ord i) (ord j) → c (ord i) ≠ c (ord j) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => ⟨0, hk⟩, ?_⟩
      intro i j hi
      omega
    | succ m ih =>
      intro hm
      have hm_le : m ≤ Fintype.card V := by omega
      obtain ⟨c, hc⟩ := ih hm_le
      let idx : Fin (Fintype.card V) := ⟨m, by omega⟩
      let x := ord idx
      let prev_neighbors := Finset.univ.filter (fun j : Fin (Fintype.card V) => (j : ℕ) < m ∧ G.Adj x (ord j))
      let used_colors := prev_neighbors.image (fun j => c (ord j))
      have h_card_prev : prev_neighbors.card < k := by
        have := h_deg idx
        exact this
      have h_card_used : used_colors.card < (Finset.univ : Finset (Fin k)).card := by
        have h1 : used_colors.card ≤ prev_neighbors.card := Finset.card_image_le
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_used
      let c' : V → Fin k := Function.update c x col
      refine ⟨c', ?_⟩
      intro i j hi hj hadj
      have hi_cases : (i : ℕ) < m ∨ (i : ℕ) = m := by omega
      have hj_cases : (j : ℕ) < m ∨ (j : ℕ) = m := by omega
      rcases hi_cases with hi_lt | hi_eq
      · rcases hj_cases with hj_lt | hj_eq
        · have hi_ne : ord i ≠ x := by
            intro heq
            have := ord.injective heq
            have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hj_ne : ord j ≠ x := by
            intro heq
            have := ord.injective heq
            have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hc'i : c' (ord i) = c (ord i) := Function.update_of_ne hi_ne col c
          have hc'j : c' (ord j) = c (ord j) := Function.update_of_ne hj_ne col c
          rw [hc'i, hc'j]
          exact hc i j hi_lt hj_lt hadj
        · have hi_ne : ord i ≠ x := by
            intro heq
            have := ord.injective heq
            have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hj_x : ord j = x := by
            have : j = idx := Fin.ext hj_eq
            rw [this]
          have hc'i : c' (ord i) = c (ord i) := Function.update_of_ne hi_ne col c
          have hc'j : c' (ord j) = col := by rw [hj_x]; exact Function.update_self x col c
          rw [hc'i, hc'j]
          intro heq
          apply h_not_used
          rw [Finset.mem_image]
          refine ⟨i, ?_, heq⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ i, ⟨hi_lt, ?_⟩⟩
          rw [← hj_x]
          exact G.adj_symm hadj
      · rcases hj_cases with hj_lt | hj_eq
        · have hj_ne : ord j ≠ x := by
            intro heq
            have := ord.injective heq
            have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hi_x : ord i = x := by
            have : i = idx := Fin.ext hi_eq
            rw [this]
          have hc'j : c' (ord j) = c (ord j) := Function.update_of_ne hj_ne col c
          have hc'i : c' (ord i) = col := by rw [hi_x]; exact Function.update_self x col c
          rw [hc'i, hc'j]
          intro heq
          apply h_not_used
          rw [Finset.mem_image]
          refine ⟨j, ?_, heq.symm⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ j, ⟨hj_lt, ?_⟩⟩
          rw [← hi_x]
          exact hadj
        · have hi_eq_j : i = j := Fin.ext (by omega)
          subst hi_eq_j
          exact False.elim (G.irrefl hadj)
  obtain ⟨c, hc⟩ := h_ind (Fintype.card V) (le_refl _)
  refine ⟨c, ?_⟩
  intro u v hadj
  have hu_eq : u = ord (ord.symm u) := (ord.apply_symm_apply u).symm
  have hv_eq : v = ord (ord.symm v) := (ord.apply_symm_apply v).symm
  rw [hu_eq, hv_eq] at hadj ⊢
  exact hc (ord.symm u) (ord.symm v) (ord.symm u).isLt (ord.symm v).isLt hadj

/-- **Lovász's Ordering Lemma (1975):**
    If vertices are ordered such that the first two vertices $v_1, v_2$ are non-adjacent
    and share a common neighbor $v_n$ (the last vertex), and every intermediate vertex $v_i$
    ($2 \le i \le n-2$) has at least one forward neighbor ($j > i$),
    then $G$ is $k$-colorable for any $k \ge \Delta(G)$ with $k \ge 1$. -/
lemma colorable_of_lovasz_ordering (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (h_deg_k : maxDegree G ≤ k)
    (ord : Fin (Fintype.card V) ≃ V)
    (h_card : 3 ≤ Fintype.card V)
    (h_not_adj_01 : ¬ G.Adj (ord ⟨0, by omega⟩) (ord ⟨1, by omega⟩))
    (h_adj_0n : G.Adj (ord ⟨0, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩))
    (h_adj_1n : G.Adj (ord ⟨1, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩))
    (h_fwd : ∀ (i : Fin (Fintype.card V)), 2 ≤ (i : ℕ) → (i : ℕ) < Fintype.card V - 1 →
      ∃ (j : Fin (Fintype.card V)), (i : ℕ) < (j : ℕ) ∧ G.Adj (ord i) (ord j)) :
    IsKColorable G k := by
  have h_pos : 0 < Fintype.card V := by omega
  let zero_idx : Fin (Fintype.card V) := ⟨0, h_pos⟩
  let one_idx : Fin (Fintype.card V) := ⟨1, by omega⟩
  let last_idx : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let v1 := ord zero_idx
  let v2 := ord one_idx
  let vn := ord last_idx
  have h_ind : ∀ m ≤ Fintype.card V,
      ∃ c : V → Fin k, (c v1 = ⟨0, hk⟩) ∧ (c v2 = ⟨0, hk⟩) ∧
        ∀ (i j : Fin (Fintype.card V)), (i : ℕ) < m → (j : ℕ) < m → G.Adj (ord i) (ord j) → c (ord i) ≠ c (ord j) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => ⟨0, hk⟩, rfl, rfl, ?_⟩
      intro i j hi
      omega
    | succ m ih =>
      intro hm
      have hm_le : m ≤ Fintype.card V := by omega
      obtain ⟨c, hc_v1, hc_v2, hc⟩ := ih hm_le
      by_cases hm_lt2 : m < 2
      · refine ⟨c, hc_v1, hc_v2, ?_⟩
        intro i j hi hj hadj
        have hi_le : (i : ℕ) ≤ 1 := by omega
        have hj_le : (j : ℕ) ≤ 1 := by omega
        have hi_cases : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
        have hj_cases : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
        rcases hi_cases with hi0 | hi1 <;> rcases hj_cases with hj0 | hj1
        · have : i = j := Fin.ext (by omega)
          subst this
          exact False.elim (G.irrefl hadj)
        · have hi_eq : i = zero_idx := Fin.ext hi0
          have hj_eq : j = one_idx := Fin.ext hj1
          rw [hi_eq, hj_eq] at hadj
          exact False.elim (h_not_adj_01 hadj)
        · have hi_eq : i = one_idx := Fin.ext hi1
          have hj_eq : j = zero_idx := Fin.ext hj0
          rw [hi_eq, hj_eq] at hadj
          exact False.elim (h_not_adj_01 (G.adj_symm hadj))
        · have : i = j := Fin.ext (by omega)
          subst this
          exact False.elim (G.irrefl hadj)
      · by_cases hm_last : m = Fintype.card V - 1
        · let idx_n : Fin (Fintype.card V) := ⟨m, by omega⟩
          let x := ord idx_n
          have h_idx_eq : idx_n = last_idx := Fin.ext hm_last
          have hx_vn : x = vn := by dsimp [x, vn]; rw [h_idx_eq]
          let neighbor_colors := (G.neighborFinset x).image c
          have hv1_mem : v1 ∈ G.neighborFinset x := by
            rw [hx_vn]
            exact (G.mem_neighborFinset vn v1).mpr (G.adj_symm h_adj_0n)
          have hv2_mem : v2 ∈ G.neighborFinset x := by
            rw [hx_vn]
            exact (G.mem_neighborFinset vn v2).mpr (G.adj_symm h_adj_1n)
          have hv1_ne_v2 : v1 ≠ v2 := by
            intro heq
            have : zero_idx = one_idx := ord.injective heq
            have : (zero_idx : ℕ) = (one_idx : ℕ) := congrArg Fin.val this
            change 0 = 1 at this
            omega
          have hc_eq : c v1 = c v2 := by rw [hc_v1, hc_v2]
          have h_card_nc : neighbor_colors.card ≤ (G.neighborFinset x).card - 1 :=
            card_image_erase_le (G.neighborFinset x) c v1 v2 hv1_mem hv2_mem hv1_ne_v2 hc_eq
          have h_card_used : neighbor_colors.card < (Finset.univ : Finset (Fin k)).card := by
            rw [G.card_neighborFinset_eq_degree] at h_card_nc
            have h_deg_le := (degree_le_maxDegree G x).trans h_deg_k
            rw [Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_used
          let c_final : V → Fin k := Function.update c x col
          have h_ne_v1 : v1 ≠ x := by
            intro heq
            have : zero_idx = idx_n := ord.injective heq
            have : (zero_idx : ℕ) = (idx_n : ℕ) := congrArg Fin.val this
            change 0 = m at this
            omega
          have h_ne_v2 : v2 ≠ x := by
            intro heq
            have : one_idx = idx_n := ord.injective heq
            have : (one_idx : ℕ) = (idx_n : ℕ) := congrArg Fin.val this
            change 1 = m at this
            omega
          have hc'_v1 : c_final v1 = ⟨0, hk⟩ := by
            dsimp [c_final]
            rw [Function.update_of_ne h_ne_v1 col c, hc_v1]
          have hc'_v2 : c_final v2 = ⟨0, hk⟩ := by
            dsimp [c_final]
            rw [Function.update_of_ne h_ne_v2 col c, hc_v2]
          refine ⟨c_final, hc'_v1, hc'_v2, ?_⟩
          intro i j hi hj hadj
          have hi_cases : (i : ℕ) < m ∨ (i : ℕ) = m := by omega
          have hj_cases : (j : ℕ) < m ∨ (j : ℕ) = m := by omega
          rcases hi_cases with hi_lt | hi_eq
          · rcases hj_cases with hj_lt | hj_eq
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx_n := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx_n := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              dsimp [c_final]
              rw [Function.update_of_ne hi_ne col c, Function.update_of_ne hj_ne col c]
              exact hc i j hi_lt hj_lt hadj
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx_n := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              have hj_x : ord j = x := by
                have : j = idx_n := Fin.ext hj_eq
                rw [this]
              dsimp [c_final]
              rw [Function.update_of_ne hi_ne col c, hj_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨ord i, ?_, heq⟩
              rw [G.mem_neighborFinset]
              rw [hj_x] at hadj
              exact G.adj_symm hadj
          · rcases hj_cases with hj_lt | hj_eq
            · have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx_n := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              have hi_x : ord i = x := by
                have : i = idx_n := Fin.ext hi_eq
                rw [this]
              dsimp [c_final]
              rw [Function.update_of_ne hj_ne col c, hi_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨ord j, ?_, heq.symm⟩
              rw [G.mem_neighborFinset]
              rw [hi_x] at hadj
              exact hadj
            · have : i = j := Fin.ext (by omega)
              subst this
              exact False.elim (G.irrefl hadj)
        · let idx : Fin (Fintype.card V) := ⟨m, by omega⟩
          let x := ord idx
          have h_m_ge2 : 2 ≤ (idx : ℕ) := by dsimp [idx]; omega
          have h_m_lt_last : (idx : ℕ) < Fintype.card V - 1 := by dsimp [idx]; omega
          obtain ⟨j_fwd, hj_lt, hadj_fwd⟩ := h_fwd idx h_m_ge2 h_m_lt_last
          let prev_neighbors := Finset.univ.filter (fun p : Fin (Fintype.card V) => (p : ℕ) < m ∧ G.Adj x (ord p))
          let used_colors := prev_neighbors.image (fun p => c (ord p))
          have h_sub_erase : prev_neighbors.image ord ⊆ (G.neighborFinset x).erase (ord j_fwd) := by
            intro y hy
            rw [Finset.mem_image] at hy
            obtain ⟨p, hp, rfl⟩ := hy
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_erase, G.mem_neighborFinset]
            refine ⟨?_, hp.2.2⟩
            intro heq
            have hp_lt : (p : ℕ) < m := hp.2.1
            have : p = j_fwd := ord.injective heq
            have : (p : ℕ) = (j_fwd : ℕ) := congrArg Fin.val this
            have h_idx_m : (idx : ℕ) = m := rfl
            omega
          have h_fwd_mem : ord j_fwd ∈ G.neighborFinset x :=
            (G.mem_neighborFinset x (ord j_fwd)).mpr hadj_fwd
          have h_card_prev : prev_neighbors.card ≤ k - 1 := by
            have h_img_card : (prev_neighbors.image ord).card = prev_neighbors.card :=
              Finset.card_image_of_injective prev_neighbors ord.injective
            have h_sub_card := Finset.card_le_card h_sub_erase
            rw [Finset.card_erase_of_mem h_fwd_mem, G.card_neighborFinset_eq_degree] at h_sub_card
            have h_deg_le := (degree_le_maxDegree G x).trans h_deg_k
            omega
          have h_card_used : used_colors.card < (Finset.univ : Finset (Fin k)).card := by
            have h1 : used_colors.card ≤ prev_neighbors.card := Finset.card_image_le
            rw [Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_used
          let c' : V → Fin k := Function.update c x col
          have h_ne_v1 : v1 ≠ x := by
            intro heq
            have : zero_idx = idx := ord.injective heq
            have : (zero_idx : ℕ) = (idx : ℕ) := congrArg Fin.val this
            change 0 = m at this
            omega
          have h_ne_v2 : v2 ≠ x := by
            intro heq
            have : one_idx = idx := ord.injective heq
            have : (one_idx : ℕ) = (idx : ℕ) := congrArg Fin.val this
            change 1 = m at this
            omega
          have hc'_v1 : c' v1 = ⟨0, hk⟩ := by
            dsimp [c']
            rw [Function.update_of_ne h_ne_v1 col c, hc_v1]
          have hc'_v2 : c' v2 = ⟨0, hk⟩ := by
            dsimp [c']
            rw [Function.update_of_ne h_ne_v2 col c, hc_v2]
          refine ⟨c', hc'_v1, hc'_v2, ?_⟩
          intro i j hi hj hadj
          have hi_cases : (i : ℕ) < m ∨ (i : ℕ) = m := by omega
          have hj_cases : (j : ℕ) < m ∨ (j : ℕ) = m := by omega
          rcases hi_cases with hi_lt | hi_eq
          · rcases hj_cases with hj_lt | hj_eq
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              dsimp [c']
              rw [Function.update_of_ne hi_ne col c, Function.update_of_ne hj_ne col c]
              exact hc i j hi_lt hj_lt hadj
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              have hj_x : ord j = x := by
                have : j = idx := Fin.ext hj_eq
                rw [this]
              dsimp [c']
              rw [Function.update_of_ne hi_ne col c, hj_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨i, ?_, heq⟩
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ i, ⟨hi_lt, ?_⟩⟩
              rw [← hj_x]
              exact G.adj_symm hadj
          · rcases hj_cases with hj_lt | hj_eq
            · have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              have hi_x : ord i = x := by
                have : i = idx := Fin.ext hi_eq
                rw [this]
              dsimp [c']
              rw [Function.update_of_ne hj_ne col c, hi_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨j, ?_, heq.symm⟩
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ j, ⟨hj_lt, ?_⟩⟩
              rw [← hi_x]
              exact hadj
            · have : i = j := Fin.ext (by omega)
              subst this
              exact False.elim (G.irrefl hadj)
  obtain ⟨c, -, -, hc⟩ := h_ind (Fintype.card V) (le_refl _)
  refine ⟨c, ?_⟩
  intro u v hadj
  have hu_eq : u = ord (ord.symm u) := (ord.apply_symm_apply u).symm
  have hv_eq : v = ord (ord.symm v) := (ord.apply_symm_apply v).symm
  rw [hu_eq, hv_eq] at hadj ⊢
  exact hc (ord.symm u) (ord.symm v) (ord.symm u).isLt (ord.symm v).isLt hadj

lemma exists_partial_coloring (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    ∃ c : V → Fin (maxDegree G + 1), ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, ?_⟩
    intro u hu
    simp at hu
  | insert x s hx ih =>
    obtain ⟨c, hc⟩ := ih
    let neighbors_in_s := s.filter (fun y => G.Adj x y)
    let used_colors := neighbors_in_s.image c
    have h_sub : neighbors_in_s ⊆ G.neighborFinset x := by
      intro y hy
      rw [Finset.mem_filter] at hy
      exact (G.mem_neighborFinset x y).mpr hy.2
    have h_card_neighbors : neighbors_in_s.card ≤ G.degree x := by
      have h1 := Finset.card_le_card h_sub
      rwa [G.card_neighborFinset_eq_degree x] at h1
    have h_card_used : used_colors.card ≤ maxDegree G := by
      have h1 : used_colors.card ≤ neighbors_in_s.card := Finset.card_image_le
      have h2 := degree_le_maxDegree G x
      omega
    have h_univ_card : (Finset.univ : Finset (Fin (maxDegree G + 1))).card = maxDegree G + 1 := by
      exact Fintype.card_fin (maxDegree G + 1)
    have h_lt : used_colors.card < (Finset.univ : Finset (Fin (maxDegree G + 1))).card := by
      omega
    obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_lt
    let c' : V → Fin (maxDegree G + 1) := Function.update c x col
    refine ⟨c', ?_⟩
    intro u hu v hv hadj
    by_cases hu_x : u = x
    · have hc'u : c' u = col := by rw [hu_x]; exact Function.update_self x col c
      by_cases hv_x : v = x
      · have h_uv : u = v := hu_x.trans hv_x.symm
        subst h_uv
        exact False.elim (G.irrefl hadj)
      · have hv_s : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hv_x
        have hc'v : c' v = c v := Function.update_of_ne hv_x col c
        rw [hc'u, hc'v]
        intro heq
        apply h_not_used
        rw [Finset.mem_image]
        refine ⟨v, ?_, heq.symm⟩
        rw [Finset.mem_filter]
        exact ⟨hv_s, hu_x ▸ hadj⟩
    · have hu_s : u ∈ s := (Finset.mem_insert.mp hu).resolve_left hu_x
      by_cases hv_x : v = x
      · have hc'v : c' v = col := by rw [hv_x]; exact Function.update_self x col c
        have hc'u : c' u = c u := Function.update_of_ne hu_x col c
        rw [hc'u, hc'v]
        intro heq
        apply h_not_used
        rw [Finset.mem_image]
        refine ⟨u, ?_, heq⟩
        rw [Finset.mem_filter]
        exact ⟨hu_s, hv_x ▸ G.adj_symm hadj⟩
      · have hv_s : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hv_x
        have hc'u : c' u = c u := Function.update_of_ne hu_x col c
        have hc'v : c' v = c v := Function.update_of_ne hv_x col c
        rw [hc'u, hc'v]
        exact hc u hu_s v hv_s hadj

/-- The classical greedy coloring theorem: any graph with maximum degree $\Delta$
    can be properly colored with $\Delta + 1$ colors. -/
theorem greedy_coloring_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsKColorable G (maxDegree G + 1) := by
  obtain ⟨c, hc⟩ := exists_partial_coloring G Finset.univ
  exact ⟨c, fun u v hadj => hc u (Finset.mem_univ u) v (Finset.mem_univ v) hadj⟩

/-- The chromatic number of any finite graph is bounded by its maximum degree plus one:
    $\chi(G) \le \Delta(G) + 1$. -/
lemma chromaticNumber_le_maxDegree_succ (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.chromaticNumber ≤ (maxDegree G + 1 : ℕ∞) := by
  have hcol : G.Colorable (maxDegree G + 1) :=
    (isKColorable_iff_colorable G (maxDegree G + 1)).mp (greedy_coloring_bound G)
  exact iInf₂_le (maxDegree G + 1) hcol

-- ============================================================================
-- Section 4: Main Brooks' Theorem (1941)
-- ============================================================================

/-- **Brooks' Theorem for small graphs ($|V| \le \Delta + 1$):**
    Any graph on at most $\Delta + 1$ vertices with $\Delta \ge 1$ that is not
    a complete graph $K_{\Delta+1}$ is $\Delta$-colorable. -/
theorem brooks_theorem_of_card_le_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_card : Fintype.card V ≤ maxDegree G + 1)
    (h_not_clique : ¬ (IsCompleteGraph G ∧ Fintype.card V = maxDegree G + 1)) :
    IsKColorable G (maxDegree G) := by
  rcases lt_or_eq_of_le h_card with h_lt | h_eq
  · have : Fintype.card V ≤ maxDegree G := by omega
    exact isKColorable_of_card_le G (maxDegree G) this
  · have h_not_comp : ¬ IsCompleteGraph G := by
      intro h_comp
      exact h_not_clique ⟨h_comp, h_eq⟩
    exact isKColorable_of_card_eq_succ_not_complete G h_deg_pos h_eq h_not_comp
lemma exists_neighbor_dist_lt {α : Type*} (H : SimpleGraph α) (u r : α)
    (hr : H.Reachable u r) (hne : u ≠ r) :
    ∃ w : α, H.Adj u w ∧ H.dist w r < H.dist u r := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases p with
  | nil =>
    exact False.elim (hne rfl)
  | cons hadj p' =>
    refine ⟨_, hadj, ?_⟩
    have hle := H.dist_le p'
    have hlen : (SimpleGraph.Walk.cons hadj p').length = p'.length + 1 := rfl
    rw [hlen] at hp
    omega

lemma card_subtype_ne_pair {α : Type*} [Fintype α] [DecidableEq α] (u v : α) (hne : u ≠ v) :
    Fintype.card {x : α // x ≠ u ∧ x ≠ v} = Fintype.card α - 2 := by
  have : (Finset.univ.filter (fun x : α => x ≠ u ∧ x ≠ v)).card = Fintype.card α - 2 := by
    have h_eq : (Finset.univ.filter (fun x : α => x ≠ u ∧ x ≠ v)) = (Finset.univ.erase u).erase v := by
      ext x
      simp [Finset.mem_erase, Finset.mem_filter, and_comm]
    rw [h_eq, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
    · rfl
    · rw [Finset.mem_erase]
      exact ⟨hne.symm, Finset.mem_univ v⟩
  rw [Fintype.card_subtype, this]

lemma exists_adj_mem_not_mem {α : Type*} [DecidableEq α] (H : SimpleGraph α) (s : Finset α) :
    ∀ {z r : α}, z ∉ s → r ∈ s → H.Walk z r → ∃ u v, u ∉ s ∧ v ∈ s ∧ H.Adj u v
  | z, _, hz, hr, .nil => False.elim (hz hr)
  | z, _, hz, hr, .cons (v := v) hadj p' =>
    if hy : v ∈ s then
      ⟨z, v, hz, hy, hadj⟩
    else
      exists_adj_mem_not_mem H s hy hr p'

lemma exists_reverse_bfs_list {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (r : α) (h_reach : ∀ z : α, H.Reachable z r) :
    ∀ (m : ℕ) (hm : m ≤ Fintype.card α) (hm_pos : 0 < m),
      ∃ (L : List α) (hlen : L.length = m), L.Nodup ∧ (∃ hne : L ≠ [], L.getLast hne = r) ∧
        ∀ (i : ℕ) (hi : i < m - 1),
          ∃ (j : ℕ) (hj : i < j) (hjm : j < m),
            H.Adj (L.get ⟨i, by omega⟩) (L.get ⟨j, by omega⟩) := by
  intro m
  induction m with
  | zero =>
    intro _ hm_pos
    omega
  | succ m ih =>
    intro hm _
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨[r], rfl, List.nodup_singleton r, ⟨List.cons_ne_nil r [], rfl⟩, ?_⟩
      intro i hi
      omega
    · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
      have hm_le : m ≤ Fintype.card α := by omega
      obtain ⟨L, hlen, hnodup, ⟨hne, hlast⟩, hfwd⟩ := ih hm_le hm_pos
      let s := L.toFinset
      have h_card_s : s.card = m := by
        rw [List.toFinset_card_of_nodup hnodup, hlen]
      have h_card_univ : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
      have h_lt_card : s.card < (Finset.univ : Finset α).card := by omega
      obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card h_lt_card
      have hr_in_s : r ∈ s := by
        rw [List.mem_toFinset]
        exact hlast ▸ List.getLast_mem hne
      obtain ⟨p⟩ := h_reach z
      obtain ⟨u, v, hu_not, hv_in, hadj⟩ := exists_adj_mem_not_mem H s hz hr_in_s p
      rw [List.mem_toFinset] at hv_in
      obtain ⟨v_idx, hv_idx_eq⟩ := List.mem_iff_get.mp hv_in
      let L' := u :: L
      have hlen' : L'.length = m + 1 := by dsimp [L']; rw [hlen]
      have hu_not_L : u ∉ L := by rwa [← List.mem_toFinset]
      have hnodup' : L'.Nodup := List.nodup_cons.mpr ⟨hu_not_L, hnodup⟩
      have hne' : L' ≠ [] := List.cons_ne_nil u L
      have hlast' : L'.getLast hne' = r := by
        rw [List.getLast_cons hne, hlast]
      refine ⟨L', hlen', hnodup', ⟨hne', hlast'⟩, ?_⟩
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        have hj_lt_m : (v_idx : ℕ) + 1 < m + 1 := by
          have : (v_idx : ℕ) < m := by rw [← hlen]; exact v_idx.isLt
          omega
        refine ⟨(v_idx : ℕ) + 1, by omega, hj_lt_m, ?_⟩
        have hi_get : L'.get ⟨0, by omega⟩ = u := rfl
        have hj_get : L'.get ⟨(v_idx : ℕ) + 1, by omega⟩ = v := by
          have h_eq : L'.get ⟨(v_idx : ℕ) + 1, by omega⟩ = L.get v_idx := rfl
          rw [h_eq, hv_idx_eq]
        rw [hi_get, hj_get]
        exact hadj
      · have hi_prev_lt : i - 1 < m - 1 := by omega
        obtain ⟨j_prev, hj_lt, hj_lt_m, hadj_prev⟩ := hfwd (i - 1) hi_prev_lt
        have hj_lt_m1 : j_prev + 1 < m + 1 := by omega
        refine ⟨j_prev + 1, by omega, hj_lt_m1, ?_⟩
        have hi_get : L'.get ⟨i, by omega⟩ = L.get ⟨i - 1, by omega⟩ := by
          have h_idx : (⟨i, by omega⟩ : Fin L'.length) = ⟨(i - 1) + 1, by omega⟩ := by
            ext
            dsimp
            omega
          rw [h_idx]
          rfl
        have hj_get : L'.get ⟨j_prev + 1, by omega⟩ = L.get ⟨j_prev, by omega⟩ := rfl
        rw [hi_get, hj_get]
        exact hadj_prev

lemma lovasz_ordering_of_triple (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_card : 3 ≤ Fintype.card V)
    (v1 v2 vn : V) (hv12 : v1 ≠ v2) (hv1n : v1 ≠ vn) (hv2n : v2 ≠ vn)
    (h_not_adj : ¬ G.Adj v1 v2) (h_adj1 : G.Adj v1 vn) (h_adj2 : G.Adj v2 vn)
    (h_reach : ∀ (u : V) (hu1 : u ≠ v1) (hu2 : u ≠ v2),
      (G.induce {x : V | x ≠ v1 ∧ x ≠ v2}).Reachable ⟨u, ⟨hu1, hu2⟩⟩ ⟨vn, ⟨hv1n.symm, hv2n.symm⟩⟩) :
    ∃ (ord : Fin (Fintype.card V) ≃ V),
      (¬ G.Adj (ord ⟨0, by omega⟩) (ord ⟨1, by omega⟩)) ∧
      (G.Adj (ord ⟨0, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (G.Adj (ord ⟨1, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (∀ (i : Fin (Fintype.card V)), 2 ≤ (i : ℕ) → (i : ℕ) < Fintype.card V - 1 →
        ∃ (j : Fin (Fintype.card V)), (i : ℕ) < (j : ℕ) ∧ G.Adj (ord i) (ord j)) := by
  let n := Fintype.card V
  let k := n - 2
  have hk_pos : 0 < k := by omega
  let S_type := {x : V // x ≠ v1 ∧ x ≠ v2}
  have h_card_S : Fintype.card S_type = k := card_subtype_ne_pair v1 v2 hv12
  let r : S_type := ⟨vn, ⟨hv1n.symm, hv2n.symm⟩⟩
  let H := G.induce {x : V | x ≠ v1 ∧ x ≠ v2}
  have h_reach_S : ∀ z : S_type, H.Reachable z r := fun ⟨u, hu⟩ => h_reach u hu.1 hu.2
  have hk_le : k ≤ Fintype.card S_type := by rw [h_card_S]
  obtain ⟨L, hlen, hnodup, ⟨hne, hlast⟩, hfwd⟩ := exists_reverse_bfs_list H r h_reach_S k hk_le hk_pos
  let f : Fin k → S_type := fun i => L.get ⟨i.1, by rw [hlen]; exact i.2⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    have h_get_inj := List.Nodup.get_inj_iff hnodup |>.mp hij
    have : (⟨i.1, by rw [hlen]; exact i.2⟩ : Fin L.length).1 = (⟨j.1, by rw [hlen]; exact j.2⟩ : Fin L.length).1 :=
      congrArg Fin.val h_get_inj
    exact Fin.ext this
  have hf_bij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf_inj, ?_⟩
    rw [Fintype.card_fin, h_card_S]
  let e_S : Fin k ≃ S_type := Equiv.ofBijective f hf_bij
  let ord_fn : Fin n → V := fun i =>
    if i.1 = 0 then v1
    else if i.1 = 1 then v2
    else (e_S ⟨i.1 - 2, by omega⟩).1
  have h_ord_fn_0 (h : 0 < n) : ord_fn ⟨0, h⟩ = v1 := rfl
  have h_ord_fn_1 (h : 1 < n) : ord_fn ⟨1, h⟩ = v2 := rfl
  have h_ord_fn_add2 (i' : ℕ) (h : i' + 2 < n) : ord_fn ⟨i' + 2, h⟩ = (e_S ⟨i', by omega⟩).1 := rfl
  have h_ord_inj : Function.Injective ord_fn := by
    intro i j hij
    rcases i with ⟨_ | ⟨_ | i'⟩, hi⟩ <;> rcases j with ⟨_ | ⟨_ | j'⟩, hj⟩
    · rfl
    · rw [h_ord_fn_0, h_ord_fn_1] at hij; exact False.elim (hv12 hij)
    · rw [h_ord_fn_0, h_ord_fn_add2] at hij; exact False.elim ((e_S ⟨j', by omega⟩).2.1 hij.symm)
    · rw [h_ord_fn_1, h_ord_fn_0] at hij; exact False.elim (hv12 hij.symm)
    · rfl
    · rw [h_ord_fn_1, h_ord_fn_add2] at hij; exact False.elim ((e_S ⟨j', by omega⟩).2.2 hij.symm)
    · rw [h_ord_fn_add2, h_ord_fn_0] at hij; exact False.elim ((e_S ⟨i', by omega⟩).2.1 hij)
    · rw [h_ord_fn_add2, h_ord_fn_1] at hij; exact False.elim ((e_S ⟨i', by omega⟩).2.2 hij)
    · rw [h_ord_fn_add2, h_ord_fn_add2] at hij
      have h_sub_eq : (e_S ⟨i', by omega⟩ : S_type) = e_S ⟨j', by omega⟩ := Subtype.ext hij
      have h_fin_eq := e_S.injective h_sub_eq
      have : i' = j' := congrArg Fin.val h_fin_eq
      subst this
      rfl
  have h_ord_bij : Function.Bijective ord_fn := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨h_ord_inj, ?_⟩
    rw [Fintype.card_fin]
  let ord : Fin n ≃ V := Equiv.ofBijective ord_fn h_ord_bij
  have h_ord_apply (i : Fin n) : ord i = ord_fn i := rfl
  have h_ord_0 : ord ⟨0, by omega⟩ = v1 := by rw [h_ord_apply, h_ord_fn_0]
  have h_ord_1 : ord ⟨1, by omega⟩ = v2 := by rw [h_ord_apply, h_ord_fn_1]
  have h_ord_n : ord ⟨n - 1, by omega⟩ = vn := by
    rw [h_ord_apply]
    have hn_decomp : n - 1 = (k - 1) + 2 := by omega
    have h_fin_n : (⟨n - 1, by omega⟩ : Fin n) = ⟨(k - 1) + 2, by omega⟩ := Fin.ext hn_decomp
    rw [h_fin_n, h_ord_fn_add2]
    change (f ⟨k - 1, by omega⟩).1 = vn
    dsimp [f]
    have h_eq : (⟨k - 1, by rw [hlen]; omega⟩ : Fin L.length) = ⟨L.length - 1, by omega⟩ := by
      ext; dsimp; rw [hlen]
    have h_get_last : L.get ⟨k - 1, by rw [hlen]; omega⟩ = r := by
      rw [h_eq, List.get_length_sub_one (h := by rw [hlen]; omega), hlast]
    have : (L.get ⟨k - 1, by rw [hlen]; omega⟩).1 = r.1 := congrArg Subtype.val h_get_last
    exact this
  refine ⟨ord, ?_, ?_, ?_, ?_⟩
  · rw [h_ord_0, h_ord_1]
    exact h_not_adj
  · rw [h_ord_0, h_ord_n]
    exact h_adj1
  · rw [h_ord_1, h_ord_n]
    exact h_adj2
  · intro i hi_ge2 hi_lt_last
    obtain ⟨i', hi_decomp⟩ : ∃ i', i.1 = i' + 2 := ⟨i.1 - 2, by omega⟩
    have h_fin_i : i = ⟨i' + 2, by rw [← hi_decomp]; exact i.2⟩ := Fin.ext hi_decomp
    let idx := i'
    have h_idx_lt : idx < k - 1 := by omega
    obtain ⟨j_sub, hj_sub_gt, hj_sub_lt_k, hadj_sub⟩ := hfwd idx h_idx_lt
    have hj_lt_n : j_sub + 2 < n := by omega
    let j : Fin n := ⟨j_sub + 2, hj_lt_n⟩
    have hj_gt : (i : ℕ) < (j : ℕ) := by dsimp [j]; omega
    refine ⟨j, hj_gt, ?_⟩
    have h_ord_i : ord i = (L.get ⟨idx, by rw [hlen]; omega⟩).1 := by
      have : ord i = ord ⟨i' + 2, by rw [← hi_decomp]; exact i.2⟩ := congrArg ord h_fin_i
      rw [this, h_ord_apply, h_ord_fn_add2]
      rfl
    have h_ord_j : ord j = (L.get ⟨j_sub, by rw [hlen]; exact hj_sub_lt_k⟩).1 := by
      rw [h_ord_apply, h_ord_fn_add2]
      rfl
    rw [h_ord_i, h_ord_j]
    exact hadj_sub

lemma exists_triple_of_not_complete (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Preconnected)
    (h_not_clique : ¬ IsCompleteGraph G) :
    ∃ v1 v2 vn : V, v1 ≠ v2 ∧ v1 ≠ vn ∧ v2 ≠ vn ∧
      ¬ G.Adj v1 v2 ∧ G.Adj v1 vn ∧ G.Adj v2 vn := by
  have h_exists : ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
    by_contra! h_all
    exact h_not_clique (fun u v huv => h_all u v huv)
  obtain ⟨a, b, hab, h_not_adj⟩ := h_exists
  have hr : G.Reachable a b := h_conn a b
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases p with
  | nil =>
    exact False.elim (hab rfl)
  | cons hadj1 p' =>
    cases p' with
    | nil =>
      exact False.elim (h_not_adj hadj1)
    | cons hadj2 p'' =>
      refine ⟨a, _, _, ?_, ?_, ?_, ?_, hadj1, hadj2.symm⟩
      · intro h_eq
        subst h_eq
        have h_le := G.dist_le p''
        have h_len_p : (SimpleGraph.Walk.cons hadj1 (SimpleGraph.Walk.cons hadj2 p'')).length = p''.length + 2 := rfl
        rw [← hp, h_len_p] at h_le
        omega
      · exact G.ne_of_adj hadj1
      · exact (G.ne_of_adj hadj2).symm
      · intro hadj_a_v2
        have h_le := G.dist_le (SimpleGraph.Walk.cons hadj_a_v2 p'')
        have h_len_w : (SimpleGraph.Walk.cons hadj_a_v2 p'').length = p''.length + 1 := rfl
        have h_len_p : (SimpleGraph.Walk.cons hadj1 (SimpleGraph.Walk.cons hadj2 p'')).length = p''.length + 2 := rfl
        rw [← hp, h_len_w, h_len_p] at h_le
        omega

lemma score_injective (d : V → ℕ) (n : ℕ) (hn : Fintype.card V = n) :
    Function.Injective (fun (x : V) => (n - d x) * (n + 1) + (Fintype.equivFin V x : ℕ)) := by
  intro x y hxy
  have hx_lt : (Fintype.equivFin V x : ℕ) < n + 1 := by
    have := (Fintype.equivFin V x).isLt
    omega
  have hy_lt : (Fintype.equivFin V y : ℕ) < n + 1 := by
    have := (Fintype.equivFin V y).isLt
    omega
  have h_val : (Fintype.equivFin V x : ℕ) = (Fintype.equivFin V y : ℕ) := by
    have h1 : ((n - d x) * (n + 1) + (Fintype.equivFin V x : ℕ)) % (n + 1) =
              ((n - d y) * (n + 1) + (Fintype.equivFin V y : ℕ)) % (n + 1) := congrArg (· % (n + 1)) hxy
    rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hx_lt, Nat.mod_eq_of_lt hy_lt] at h1
    exact h1
  have h_fin : Fintype.equivFin V x = Fintype.equivFin V y := Fin.ext h_val
  exact (Fintype.equivFin V).injective h_fin

lemma score_lt_of_dist_gt (dx dy n a b : ℕ) (hn : dx ≤ n) (hdy : dy < dx) (ha : a < n + 1) :
    (n - dx) * (n + 1) + a < (n - dy) * (n + 1) + b := by
  have h1 : n - dx + 1 ≤ n - dy := by omega
  have h2 : (n - dx) * (n + 1) + a < (n - dx + 1) * (n + 1) := by
    calc
      (n - dx) * (n + 1) + a < (n - dx) * (n + 1) + (n + 1) := by omega
      _ = (n - dx + 1) * (n + 1) := by ring
  have h3 : (n - dx + 1) * (n + 1) ≤ (n - dy) * (n + 1) := Nat.mul_le_mul_right (n + 1) h1
  omega

lemma dist_zero_iff (G : SimpleGraph V) {u v : V} (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by
  rw [G.dist_eq_zero_iff_eq_or_not_reachable]
  simp [hr]

lemma dist_le_card (G : SimpleGraph V) (u v : V) (hr : G.Reachable u v) :
    G.dist u v ≤ Fintype.card V := by
  obtain ⟨p⟩ := hr
  have h1 := G.dist_le p.toPath.1
  have h2 := p.toPath.2.length_lt
  omega

lemma not_mem_pair_of_dist_ge_three (G : SimpleGraph V) (u v1 v2 vn w : V)
    (h_adj1 : G.Adj v1 vn) (h_adj2 : G.Adj v2 vn)
    (hadj_uw : G.Adj u w)
    (h_ge3 : 3 ≤ G.dist u vn) :
    w ≠ v1 ∧ w ≠ v2 := by
  constructor
  · intro heq
    subst heq
    have hle := G.dist_le (Walk.cons hadj_uw (Walk.cons h_adj1 Walk.nil))
    change G.dist u vn ≤ 2 at hle
    omega
  · intro heq
    subst heq
    have hle := G.dist_le (Walk.cons hadj_uw (Walk.cons h_adj2 Walk.nil))
    change G.dist u vn ≤ 2 at hle
    omega

/-- **Lovász Ordering for Brooks' Theorem (1975)**:
    For any connected simple graph $G$ that is not a clique, not an odd cycle,
    and has $|V| > \Delta + 1$, there exists an ordering of the vertices
    $v_1, v_2, \dots, v_n$ such that $v_1 \not\sim v_2$, $v_1 \sim v_n$, $v_2 \sim v_n$,
    and every intermediate vertex $v_i$ ($2 \le i \le n-2$) has at least one forward neighbor.
    (Constructive proof via 2-connected block reduction and reverse BFS on $G \setminus \{v_1, v_2\}$). -/
axiom exists_lovasz_ordering (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Preconnected)
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_not_clique : ¬ IsCompleteGraph G)
    (h_not_odd_cycle : ¬ (maxDegree G = 2 ∧ IsOddCycle G))
    (h_gt : maxDegree G + 1 < Fintype.card V) :
    ∃ (ord : Fin (Fintype.card V) ≃ V),
      (¬ G.Adj (ord ⟨0, by omega⟩) (ord ⟨1, by omega⟩)) ∧
      (G.Adj (ord ⟨0, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (G.Adj (ord ⟨1, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (∀ (i : Fin (Fintype.card V)), 2 ≤ (i : ℕ) → (i : ℕ) < Fintype.card V - 1 →
        ∃ (j : Fin (Fintype.card V)), (i : ℕ) < (j : ℕ) ∧ G.Adj (ord i) (ord j))

/-- **Brooks' Theorem (1941):**
    If $G$ is a connected simple graph with maximum degree $\Delta \ge 1$,
    and $G$ is neither a complete graph $K_{\Delta+1}$ nor an odd cycle,
    then $G$ is $\Delta$-colorable ($\chi(G) \le \Delta$). -/
theorem brooks_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Preconnected)
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_not_clique : ¬ (IsCompleteGraph G ∧ Fintype.card V = maxDegree G + 1))
    (h_not_odd_cycle : ¬ (maxDegree G = 2 ∧ IsOddCycle G)) :
    IsKColorable G (maxDegree G) := by
  rcases le_or_gt (Fintype.card V) (maxDegree G + 1) with h_le | h_gt
  · exact brooks_theorem_of_card_le_succ G h_deg_pos h_le h_not_clique
  · have h_not_comp : ¬ IsCompleteGraph G := by
      intro h_comp
      have h_nonempty : Nonempty V := by
        have : 0 < Fintype.card V := by omega
        exact Fintype.card_pos_iff.mp this
      obtain ⟨v0⟩ := h_nonempty
      have h_adj : G.neighborFinset v0 = (Finset.univ.erase v0) := by
        ext w
        simp only [G.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun h => (G.ne_of_adj h).symm, fun h => h_comp v0 w h.symm⟩
      have h_deg_v0 : G.degree v0 ≤ maxDegree G := degree_le_maxDegree G v0
      have h1 : G.degree v0 = Fintype.card V - 1 := by
        have hd : G.degree v0 = (G.neighborFinset v0).card := (G.card_neighborFinset_eq_degree v0).symm
        rw [hd, h_adj, Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_univ]
      omega
    have h_card3 : 3 ≤ Fintype.card V := by omega
    obtain ⟨ord, h01, h0n, h1n, hfwd⟩ :=
      exists_lovasz_ordering G h_conn h_deg_pos h_not_comp h_not_odd_cycle h_gt
    exact colorable_of_lovasz_ordering G h_deg_pos (le_refl _) ord h_card3 h01 h0n h1n hfwd

end BrooksTheorem
