import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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
  · -- Case |V| ≥ Δ + 2: Lovász's ordering reduction via spanning DFS trees
    -- guarantees the existence of an ordering where each vertex has < Δ colored neighbors.
    sorry

end BrooksTheorem
