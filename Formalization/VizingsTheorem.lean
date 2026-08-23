import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Vizing's Theorem on Edge Colorings & König's Line Coloring Theorem

This file formalizes the theory of proper edge colorings, the chromatic index $\chi'(G)$,
König's Line Coloring Theorem for bipartite graphs, and the statement of Vizing's Theorem
for finite simple graphs.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph


lemma mk_edge_symm {u v : V} (h : G.Adj v u) :
    (⟨s(v, u), h⟩ : G.edgeSet) = ⟨s(u, v), h.symm⟩ := Subtype.ext Sym2.eq_swap

lemma edge_eq_of_mem (e : G.edgeSet) (v : V) (hv : v ∈ (e : Sym2 V)) :
    ∃ (w : V) (h : G.Adj v w), e = ⟨s(v, w), h⟩ := by
  rcases e with ⟨e_val, he_prop⟩
  induction e_val using Sym2.inductionOn with
  | hf x y =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨y, he_prop, rfl⟩
    · exact ⟨x, he_prop.symm, mk_edge_symm G he_prop⟩

/-- Two undirected edges in $G$ share a common endpoint vertex. -/
def ShareVertex (e₁ e₂ : G.edgeSet) : Prop :=
  ∃ v : V, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)

/-- A proper edge coloring of $G$ with color set $\alpha$ assigns colors to edges
such that any two distinct incident edges receive different colors. -/
def IsProperEdgeColoring {α : Type*} (c : G.edgeSet → α) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ → c e₁ ≠ c e₂

/-- The type of proper edge colorings of $G$ using $k$ colors. -/
structure EdgeColoring (k : ℕ) where
  color : G.edgeSet → Fin k
  proper : IsProperEdgeColoring G color

/-- A graph is $k$-edge-colorable if it admits a proper $k$-edge-coloring. -/
def IsEdgeColorable (k : ℕ) : Prop := Nonempty (EdgeColoring G k)

/-- The chromatic index (edge chromatic number) $\chi'(G)$ is the minimum number of colors
needed to properly color the edges of $G$. -/
noncomputable def chromaticIndex : ℕ := sInf {k : ℕ | IsEdgeColorable G k}

theorem edgeColorable_card_edgeSet [Fintype G.edgeSet] :
    IsEdgeColorable G (Fintype.card G.edgeSet) :=
  ⟨⟨Fintype.equivFin G.edgeSet, fun _ _ hne _ heq => hne ((Fintype.equivFin G.edgeSet).injective heq)⟩⟩

theorem degree_le_of_edgeColoring {k : ℕ} (c : EdgeColoring G k) (v : V) : G.degree v ≤ k := by
  have h_inj : Function.Injective (fun e : G.incidenceSet v => c.color ⟨e.val, e.prop.1⟩) := by
    intro e₁ e₂ heq
    by_contra hne
    have he_ne : (⟨e₁.val, e₁.prop.1⟩ : G.edgeSet) ≠ ⟨e₂.val, e₂.prop.1⟩ := by
      intro h_eq
      have h_val : e₁.val = e₂.val := by injection h_eq
      exact hne (Subtype.ext h_val)
    exact c.proper he_ne ⟨v, e₁.prop.2, e₂.prop.2⟩ heq
  have h_le := Fintype.card_le_of_injective _ h_inj
  rwa [SimpleGraph.card_incidenceSet_eq_degree, Fintype.card_fin] at h_le

theorem maxDegree_le_of_edgeColorable {k : ℕ} (h : IsEdgeColorable G k) : G.maxDegree ≤ k := by
  obtain ⟨c⟩ := h
  rw [SimpleGraph.maxDegree, WithBot.unbotD_le_iff (fun _ => Nat.zero_le k), Finset.max_le_iff]
  intro a ha; obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ha
  exact WithBot.coe_le_coe.mpr (degree_le_of_edgeColoring G c v)

/-- Every vertex of degree $d$ has $d$ incident edges that pairwise share a vertex,
providing the trivial lower bound $\chi'(G) \ge \Delta(G)$. -/
theorem chromatic_index_ge_maxDegree [Fintype G.edgeSet] : G.maxDegree ≤ chromaticIndex G :=
  le_csInf ⟨_, edgeColorable_card_edgeSet G⟩ fun _ hk => maxDegree_le_of_edgeColorable G hk

/-! ### Partial Edge Colorings and Kempe Chains -/

/-- A partial proper edge coloring of $G$ using $k$ colors. -/
structure PartialEdgeColoring (k : ℕ) where
  color : G.edgeSet → Option (Fin k)
  proper : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ →
    ∀ ⦃col : Fin k⦄, color e₁ = some col → color e₂ = some col → False

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

/-- The set of uncolored edges under partial coloring `c`. -/
def uncoloredEdges : Finset G.edgeSet := Finset.univ.filter (fun e => c.color e = none)

/-- The empty partial edge coloring (no edges colored). -/
def empty : PartialEdgeColoring G k where
  color _ := none
  proper _ _ _ _ _ h := by cases h

/-- The color assigned to adjacent vertices $u$ and $v$ (if colored). -/
def colorOf (u v : V) (h : G.Adj u v) : Option (Fin k) := c.color ⟨s(u, v), h⟩

lemma colorOf_symm (u v : V) (h : G.Adj u v) : c.colorOf v u h.symm = c.colorOf u v h := by
  dsimp [colorOf]; rw [mk_edge_symm G h]

/-- The set of colors present on edges incident to $v$. -/
def usedColors (v : V) : Finset (Fin k) :=
  Finset.univ.filter (fun col => ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col)

/-- The set of colors missing at vertex $v$. -/
def missingColors (v : V) : Finset (Fin k) := Finset.univ \ c.usedColors v

@[simp] theorem mem_usedColors_iff (v : V) (col : Fin k) :
    col ∈ c.usedColors v ↔ ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col := by simp [usedColors]

@[simp] theorem mem_missingColors_iff (v : V) (col : Fin k) :
    col ∈ c.missingColors v ↔ ∀ (w : V) (h : G.Adj v w), c.colorOf v w h ≠ some col := by simp [missingColors]

lemma colorOf_inj_neighbor (u v w : V) (hv : G.Adj u v) (hw : G.Adj u w) (col : Fin k)
    (h1 : c.colorOf u v hv = some col) (h2 : c.colorOf u w hw = some col) : v = w := by
  by_contra hne
  have he_ne : (⟨s(u, v), hv⟩ : G.edgeSet) ≠ ⟨s(u, w), hw⟩ := by
    intro heq
    rcases Sym2.eq_iff.mp (Subtype.ext_iff.mp heq) with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · exact hv.ne rfl
  exact c.proper he_ne ⟨u, Sym2.mem_mk_left u v, Sym2.mem_mk_left u w⟩ h1 h2

noncomputable def neighborOfColor (u : V) (col : Fin k) : V :=
  if h : col ∈ c.usedColors u then Classical.choose (c.mem_usedColors_iff u col |>.mp h) else u

lemma neighborOfColor_spec (u : V) {col : Fin k} (h : col ∈ c.usedColors u) :
    ∃ h' : G.Adj u (c.neighborOfColor u col), c.colorOf u (c.neighborOfColor u col) h' = some col := by
  dsimp [neighborOfColor]; split_ifs; exact Classical.choose_spec (c.mem_usedColors_iff u col |>.mp h)

lemma neighborOfColor_inj (u : V) : Set.InjOn (c.neighborOfColor u) (c.usedColors u : Set (Fin k)) := by
  intro c1 hc1 c2 hc2 heq
  obtain ⟨h1, hc1'⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hc1)
  obtain ⟨h2, hc2'⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hc2)
  dsimp [colorOf] at hc1' hc2'
  have he : (⟨s(u, c.neighborOfColor u c1), h1⟩ : G.edgeSet) = ⟨s(u, c.neighborOfColor u c2), h2⟩ := by ext; simp [heq]
  exact Option.some.inj (hc1'.symm.trans (he ▸ hc2'))

theorem card_usedColors_le_degree (u : V) : (c.usedColors u).card ≤ G.degree u := by
  have h_maps : Set.MapsTo (c.neighborOfColor u) (c.usedColors u : Set (Fin k)) (G.neighborFinset u : Set V) := by
    intro col hcol; obtain ⟨h', -⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hcol)
    exact Finset.mem_coe.mpr ((G.mem_neighborFinset u _).mpr h')
  have h_le := Finset.card_le_card_of_injOn (c.neighborOfColor u) h_maps (c.neighborOfColor_inj u)
  rwa [G.card_neighborFinset_eq_degree u] at h_le

theorem card_usedColors_le_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none) :
    (c.usedColors u).card ≤ G.maxDegree - 1 := by
  have h_maps : Set.MapsTo (c.neighborOfColor u) (c.usedColors u : Set (Fin k)) ((G.neighborFinset u).erase v : Set V) := by
    intro col hcol
    obtain ⟨h', hc'⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hcol)
    have hne : c.neighborOfColor u col ≠ v := by
      intro heq
      have : c.colorOf u v (heq ▸ h') = some col := heq ▸ hc'
      rw [show c.colorOf u v (heq ▸ h') = c.colorOf u v h from rfl, h_none] at this
      cases this
    exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, (G.mem_neighborFinset u _).mpr h'⟩)
  have h_le := Finset.card_le_card_of_injOn (c.neighborOfColor u) h_maps (c.neighborOfColor_inj u)
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u _).mpr h
  rw [Finset.card_erase_of_mem hv_mem, G.card_neighborFinset_eq_degree u] at h_le
  exact h_le.trans (Nat.sub_le_sub_right (G.degree_le_maxDegree u) 1)

theorem card_usedColors_lt_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) : (c.usedColors u).card < k := by
  have h1 := c.card_usedColors_le_of_uncolored h h_none
  have h2 : 1 ≤ G.degree u := Finset.card_pos.mpr ⟨v, (G.mem_neighborFinset u v).mpr h⟩
  have h3 := G.degree_le_maxDegree u
  omega

theorem exists_missingColor_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) : (c.missingColors u).Nonempty := by
  have hlt := c.card_usedColors_lt_of_uncolored h h_none h_max
  rw [missingColors, Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
  intro hsub
  have := Finset.card_le_card hsub
  rw [Finset.card_fin] at this
  omega

theorem exists_missingColor_of_maxDegree_lt {u : V} (h_max : G.maxDegree < k) :
    (c.missingColors u).Nonempty := by
  have hdeg := c.card_usedColors_le_degree u
  have hmax := G.degree_le_maxDegree u
  rw [missingColors, Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
  intro hsub
  have := Finset.card_le_card hsub
  rw [Finset.card_fin] at this
  omega

/-- Swaps colors $\alpha$ and $\beta$ on an optional color value. -/
def swapColor (α β : Fin k) (c_opt : Option (Fin k)) : Option (Fin k) :=
  c_opt.map (Equiv.swap α β)

theorem swapColor_involutive (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β (swapColor α β c_opt) = c_opt := by
  cases c_opt <;> simp [swapColor]

lemma swapColor_some_left (α β : Fin k) : swapColor α β (some α) = some β := by
  simp [swapColor]

lemma swapColor_some_right (α β : Fin k) : swapColor α β (some β) = some α := by
  simp [swapColor]

lemma swapColor_some_other (α β γ : Fin k) (h1 : γ ≠ α) (h2 : γ ≠ β) : swapColor α β (some γ) = some γ := by
  simp [swapColor, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma swapColor_eq_none_iff (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β c_opt = none ↔ c_opt = none := by
  simp [swapColor]

/-- Predicate asserting that an edge belongs to the connected component of $u$ in $H$. -/
def inComponent (H : SimpleGraph V) (u : V) (e : Sym2 V) : Prop :=
  ∀ x ∈ e, H.Reachable u x

/-- The $(\alpha, \beta)$-Kempe subgraph formed by edges colored $\alpha$ or $\beta$. -/
def kempeGraph (α β : Fin k) : SimpleGraph V where
  Adj x y := ∃ h : G.Adj x y, c.colorOf x y h = some α ∨ c.colorOf x y h = some β
  symm := ⟨fun _ _ ⟨h, hc⟩ => ⟨h.symm, by rwa [colorOf_symm]⟩⟩
  loopless := ⟨fun x ⟨h, _⟩ => h.ne rfl⟩

lemma kempeGraph_le (α β : Fin k) : c.kempeGraph α β ≤ G := fun _ _ h => h.1

lemma kempe_color_eq_of_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hreach : (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      swapColor α β (c.color e) := by
  split_ifs with h_in
  · rfl
  · obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e v₀ hv₀
    have h_not_reach : ¬ (c.kempeGraph α β).Reachable u w := by
      intro hw_reach
      apply h_in
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    have h_not_col : c.colorOf v₀ w hw_adj ≠ some α ∧ c.colorOf v₀ w hw_adj ≠ some β := by
      constructor <;> (intro hc; apply h_not_reach; exact hreach.trans (SimpleGraph.Adj.reachable ⟨hw_adj, by simp [hc]⟩))
    cases hc : c.colorOf v₀ w hw_adj with
    | none => dsimp [colorOf] at hc; simp [swapColor, hc]
    | some col =>
      have h1 : col ≠ α := fun h => h_not_col.1 (h ▸ hc)
      have h2 : col ≠ β := fun h => h_not_col.2 (h ▸ hc)
      dsimp [colorOf] at hc
      rw [hc, swapColor_some_other α β col h1 h2]

lemma kempe_color_eq_of_not_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hnreach : ¬ (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      c.color e := by
  split_ifs with h_in
  · exact False.elim (hnreach (h_in v₀ hv₀))
  · rfl

/-- Kempe swap operation: interchange colors $\alpha$ and $\beta$ on the $(\alpha, \beta)$-Kempe
component connected to vertex $u$. -/
noncomputable def kempeSwap (α β : Fin k) (u : V) : PartialEdgeColoring G k where
  color e := if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e
  proper := by
    intro e₁ e₂ hne ⟨v₀, hv1, hv2⟩ col h1 h2
    by_cases hreach : (c.kempeGraph α β).Reachable u v₀
    · rw [kempe_color_eq_of_reachable c α β u e₁ v₀ hv1 hreach] at h1
      rw [kempe_color_eq_of_reachable c α β u e₂ v₀ hv2 hreach] at h2
      have h1' := congr_arg (swapColor α β) h1
      have h2' := congr_arg (swapColor α β) h2
      rw [swapColor_involutive] at h1' h2'
      cases h_sc : swapColor α β (some col) with
      | none => simp [swapColor] at h_sc
      | some col' =>
        rw [h_sc] at h1' h2'
        exact c.proper hne ⟨v₀, hv1, hv2⟩ h1' h2'
    · rw [kempe_color_eq_of_not_reachable c α β u e₁ v₀ hv1 hreach] at h1
      rw [kempe_color_eq_of_not_reachable c α β u e₂ v₀ hv2 hreach] at h2
      exact c.proper hne ⟨v₀, hv1, hv2⟩ h1 h2

lemma uncoloredEdges_kempeSwap (α β : Fin k) (u : V) :
    (c.kempeSwap α β u).uncoloredEdges = c.uncoloredEdges := by
  ext e
  simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [kempeSwap]
  split_ifs <;> simp [swapColor_eq_none_iff]

lemma kempeSwap_missing_u (α β : Fin k) (u : V) (hα : α ∈ c.missingColors u) :
    β ∈ (c.kempeSwap α β u).missingColors u := by
  rw [mem_missingColors_iff] at hα ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_reachable c α β u ⟨s(u, w), hw⟩ u (Sym2.mem_mk_left u w) (SimpleGraph.Reachable.refl u)]
  intro heq
  have h_inv := congr_arg (swapColor α β) heq
  rw [swapColor_involutive, swapColor_some_right] at h_inv
  exact hα w hw h_inv

lemma kempeSwap_missing_v (α β : Fin k) (u v : V) (hnreach : ¬ (c.kempeGraph α β).Reachable u v)
    (hβ : β ∈ c.missingColors v) :
    β ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff] at hβ ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_not_reachable c α β u ⟨s(v, w), hw⟩ v (Sym2.mem_mk_left v w) hnreach]
  exact hβ w hw

lemma kempeSwap_colorOf_none (α β : Fin k) (u v : V) (hadj : G.Adj u v)
    (hnreach : ¬ (c.kempeGraph α β).Reachable u v)
    (h_none : c.colorOf u v hadj = none) :
    (c.kempeSwap α β u).colorOf u v hadj = none := by
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_not_reachable c α β u ⟨s(u, v), hadj⟩ v (Sym2.mem_mk_right u v) hnreach]
  exact h_none

lemma kempeSwap_missing_of_reachable (α β : Fin k) (u v : V) (hreach : (c.kempeGraph α β).Reachable u v)
    (hβ : β ∈ c.missingColors v) :
    α ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff] at hβ ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_reachable c α β u ⟨s(v, w), hw⟩ v (Sym2.mem_mk_left v w) hreach]
  intro heq
  have h_inv := congr_arg (swapColor α β) heq
  rw [swapColor_involutive, swapColor_some_left] at h_inv
  exact hβ w hw h_inv

lemma kempeSwap_missing_of_ne (α β γ : Fin k) (u v : V) (h1 : γ ≠ α) (h2 : γ ≠ β)
    (hγ : γ ∈ c.missingColors v) :
    γ ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff] at hγ ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  split_ifs
  · intro heq
    have h_inv := congr_arg (swapColor α β) heq
    rw [swapColor_involutive, swapColor_some_other α β γ h1 h2] at h_inv
    exact hγ w hw h_inv
  · exact hγ w hw

lemma kempeSwap_colorOf_of_ne (α β γ : Fin k) (u v w : V) (hadj : G.Adj v w)
    (h1 : γ ≠ α) (h2 : γ ≠ β) (hc : c.colorOf v w hadj = some γ) :
    (c.kempeSwap α β u).colorOf v w hadj = some γ := by
  dsimp [colorOf, kempeSwap]
  split_ifs
  · dsimp [colorOf] at hc
    rw [hc, swapColor_some_other α β γ h1 h2]
  · exact hc

lemma kempeSwap_colorOf_alpha (α β : Fin k) (u w : V) (hadj : G.Adj u w)
    (hc : c.colorOf u w hadj = some β) :
    (c.kempeSwap α β u).colorOf u w hadj = some α := by
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_reachable c α β u ⟨s(u, w), hadj⟩ u (Sym2.mem_mk_left u w) (SimpleGraph.Reachable.refl u)]
  dsimp [colorOf] at hc
  rw [hc, swapColor_some_right]

lemma kempeSwap_color_none (α β : Fin k) (u : V) (e : G.edgeSet) (h : c.color e = none) :
    (c.kempeSwap α β u).color e = none := by
  dsimp [kempeSwap]; split_ifs <;> simp [swapColor, h]

/-- Helper returning the complementary color in $\{\alpha, \beta\}$. -/
def otherColor (α β col : Fin k) : Fin k := Equiv.swap α β col

/-- Predicate asserting that a walk in the Kempe graph strictly alternates colors. -/
def IsAlternating (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h p, col => c.colorOf _ _ h.1 = some col ∧ IsAlternating α β p (otherColor α β col)

/-- Predicate asserting that the initial step of a walk has color `col`. -/
def FirstColor (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h _, col => c.colorOf _ _ h.1 = some col

lemma otherColor_involutive (α β col : Fin k) (_ : col = α ∨ col = β) :
    otherColor α β (otherColor α β col) = col := Equiv.swap_apply_self α β col

lemma isAlternating_of_isPath {α β : Fin k} (hne : α ≠ β) :
    ∀ {x y : V} (p : (c.kempeGraph α β).Walk x y) (col : Fin k),
      p.IsPath → (col = α ∨ col = β) →
      c.FirstColor α β p col →
      c.IsAlternating α β p col := by
  intro x y p
  induction p with
  | nil =>
    intro _ _ _ _
    dsimp [IsAlternating]
  | @cons u₀ v₀ w₀ h p ih =>
    intro col hp hcol_mem h_first
    dsimp [IsAlternating]
    have hc1 : c.colorOf _ _ h.1 = some col := h_first
    refine ⟨hc1, ?_⟩
    have hp' : p.IsPath := hp.of_cons
    have h_next_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      rcases hcol_mem with rfl | rfl <;> simp [otherColor]
    apply ih (otherColor α β col) hp' h_next_mem
    cases p with
    | nil => dsimp [FirstColor]
    | @cons _ z _ h2 p' =>
      dsimp [FirstColor]
      rcases h2.2 with hcolα | hcolβ
      · rcases hcol_mem with rfl | rfl
        · exfalso
          have h_u0_ne_z : u₀ ≠ z := by
            intro heq; subst heq
            exact (List.nodup_cons.mp hp.support_nodup).1 (List.mem_cons_of_mem _ p'.start_mem_support)
          have hne_edge : (⟨s(u₀, v₀), h.1⟩ : G.edgeSet) ≠ ⟨s(v₀, z), h2.1⟩ := by
            intro heq
            have heq_val : s(u₀, v₀) = s(v₀, z) := by injection heq
            rcases Sym2.eq_iff.mp heq_val with ⟨h1_eq, _⟩ | ⟨h1_eq, _⟩
            · exact h.1.ne h1_eq
            · exact h_u0_ne_z h1_eq
          have hshare : ShareVertex G ⟨s(u₀, v₀), h.1⟩ ⟨s(v₀, z), h2.1⟩ :=
            ⟨v₀, Sym2.mem_mk_right u₀ v₀, Sym2.mem_mk_left v₀ z⟩
          exact c.proper hne_edge hshare h_first hcolα
        · simpa [otherColor, hne.symm] using hcolα
      · rcases hcol_mem with rfl | rfl
        · simpa [otherColor, hne] using hcolβ
        · exfalso
          have h_u0_ne_z : u₀ ≠ z := by
            intro heq; subst heq
            exact (List.nodup_cons.mp hp.support_nodup).1 (List.mem_cons_of_mem _ p'.start_mem_support)
          have hne_edge : (⟨s(u₀, v₀), h.1⟩ : G.edgeSet) ≠ ⟨s(v₀, z), h2.1⟩ := by
            intro heq
            have heq_val : s(u₀, v₀) = s(v₀, z) := by injection heq
            rcases Sym2.eq_iff.mp heq_val with ⟨h1_eq, _⟩ | ⟨h1_eq, _⟩
            · exact h.1.ne h1_eq
            · exact h_u0_ne_z h1_eq
          have hshare : ShareVertex G ⟨s(u₀, v₀), h.1⟩ ⟨s(v₀, z), h2.1⟩ :=
            ⟨v₀, Sym2.mem_mk_right u₀ v₀, Sym2.mem_mk_left v₀ z⟩
          exact c.proper hne_edge hshare h_first hcolβ

lemma last_edge_alternating {α β : Fin k} :
    ∀ {x y : V} (p : (c.kempeGraph α β).Walk x y) (col : Fin k),
      c.IsAlternating α β p col → (col = α ∨ col = β) → p.length > 0 →
      ∃ (z : V) (h : G.Adj z y),
        c.colorOf z y h = some (if p.length % 2 = 1 then col else otherColor α β col)
  | _, _, .nil, _, _, _, hlen => (Nat.not_lt_zero 0 hlen).elim
  | _, _, .cons h .nil, col, halt, _, _ => ⟨_, h.1, halt.1⟩
  | _, _, .cons h (.cons h2 p'), col, halt, hcol, _ => by
    have h_other_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      rcases hcol with rfl | rfl <;> simp [otherColor]
    obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating (.cons h2 p') (otherColor α β col) halt.2 h_other_mem (by simp)
    refine ⟨z, hz_adj, ?_⟩
    have hcases : p'.length % 2 = 0 ∨ p'.length % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · have hlen1 : (Walk.cons h2 p').length % 2 = 1 := by simp [h0]; omega
      have hlen2 : (Walk.cons h (Walk.cons h2 p')).length % 2 = 0 := by simp [h0]; omega
      rw [hlen1] at hz_col
      rw [hlen2]
      simpa [otherColor_involutive _ _ _ hcol] using hz_col
    · have hlen1 : (Walk.cons h2 p').length % 2 = 0 := by simp [h1]; omega
      have hlen2 : (Walk.cons h (Walk.cons h2 p')).length % 2 = 1 := by simp [h1]; omega
      rw [hlen1] at hz_col
      rw [hlen2]
      simpa [otherColor_involutive _ _ _ hcol] using hz_col

lemma alternating_walk_eq {α β : Fin k} :
    ∀ {x y₁ y₂ : V} (p₁ : (c.kempeGraph α β).Walk x y₁) (p₂ : (c.kempeGraph α β).Walk x y₂) (col : Fin k),
      (col = α ∨ col = β) → c.IsAlternating α β p₁ col → c.IsAlternating α β p₂ col →
      (∀ w (h : G.Adj y₁ w), c.colorOf y₁ w h ≠ some (if p₁.length % 2 = 1 then otherColor α β col else col)) →
      (∀ w (h : G.Adj y₂ w), c.colorOf y₂ w h ≠ some (if p₂.length % 2 = 1 then otherColor α β col else col)) →
      y₁ = y₂
  | _, _, _, .nil, .nil, _, _, _, _, _, _ => rfl
  | _, _, _, .nil, .cons h _, _, _, _, halt2, hend1, _ => (hend1 _ h.1 halt2.1).elim
  | _, _, _, .cons h _, .nil, _, _, halt1, _, _, hend2 => (hend2 _ h.1 halt1.1).elim
  | _, _, _, .cons h₁ p₁', .cons h₂ p₂', col, hcol, halt1, halt2, hend1, hend2 => by
    have hw_eq : _ = _ := colorOf_inj_neighbor c _ _ _ h₁.1 h₂.1 col halt1.1 halt2.1
    subst hw_eq
    have h_other_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      rcases hcol with rfl | rfl <;> simp [otherColor]
    apply alternating_walk_eq p₁' p₂' (otherColor α β col) h_other_mem halt1.2 halt2.2
    · intro w hw
      have : (p₁'.length + 1) % 2 = 1 - p₁'.length % 2 := by omega
      have hcases : p₁'.length % 2 = 0 ∨ p₁'.length % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · simpa [h0, this, otherColor_involutive _ _ _ hcol] using hend1 w hw
      · simpa [h1, this, otherColor_involutive _ _ _ hcol] using hend1 w hw
    · intro w hw
      have : (p₂'.length + 1) % 2 = 1 - p₂'.length % 2 := by omega
      have hcases : p₂'.length % 2 = 0 ∨ p₂'.length % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · simpa [h0, this, otherColor_involutive _ _ _ hcol] using hend2 w hw
      · simpa [h1, this, otherColor_involutive _ _ _ hcol] using hend2 w hw

lemma kempe_walk_parity_end {u v : V} {α β : Fin k} (hne : α ≠ β) (p : (c.kempeGraph α β).Walk u v)
    (hp : p.IsPath) (hfirst : c.FirstColor α β p β) (hv : β ∈ c.missingColors v) : p.length % 2 = 0 := by
  by_contra h_odd
  have h1 : p.length % 2 = 1 := by omega
  have hlen_pos : p.length > 0 := by omega
  have halt := isAlternating_of_isPath c hne p β hp (Or.inr rfl) hfirst
  obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p β halt (Or.inr rfl) hlen_pos
  rw [h1] at hz_col
  rw [mem_missingColors_iff] at hv
  exact hv z hz_adj.symm (by rwa [colorOf_symm])

/--
Two distinct vertices missing the same color $\beta$ cannot both be reachable
from a vertex $u$ missing color $\alpha$ in the $(\alpha, \beta)$ Kempe graph.
-/
theorem kempe_not_reachable_both {u v₁ v₂ : V} {α β : Fin k} (hne : α ≠ β)
    (hα : α ∈ c.missingColors u) (hv1 : β ∈ c.missingColors v₁) (hv2 : β ∈ c.missingColors v₂)
    (hne_v : v₁ ≠ v₂) :
    ¬ ((c.kempeGraph α β).Reachable u v₁ ∧ (c.kempeGraph α β).Reachable u v₂) := by
  rintro ⟨hreach1, hreach2⟩
  obtain ⟨p₁, hp1⟩ := hreach1.exists_isPath
  obtain ⟨p₂, hp2⟩ := hreach2.exists_isPath
  have hfirst (y : V) (p : (c.kempeGraph α β).Walk u y) : c.FirstColor α β p β := by
    cases p with
    | nil => trivial
    | cons h _ =>
      rcases h.2 with hα' | hβ'
      · rw [mem_missingColors_iff] at hα; exact (hα _ h.1 hα').elim
      · exact hβ'
  have halt1 := isAlternating_of_isPath c hne p₁ β hp1 (Or.inr rfl) (hfirst v₁ p₁)
  have halt2 := isAlternating_of_isPath c hne p₂ β hp2 (Or.inr rfl) (hfirst v₂ p₂)
  have hlen1 := kempe_walk_parity_end c hne p₁ hp1 (hfirst v₁ p₁) hv1
  have hlen2 := kempe_walk_parity_end c hne p₂ hp2 (hfirst v₂ p₂) hv2
  have hend1 : ∀ w (h : G.Adj v₁ w), c.colorOf v₁ w h ≠ some (if p₁.length % 2 = 1 then otherColor α β β else β) := by
    intro w hw; rw [hlen1]; simp; rw [mem_missingColors_iff] at hv1; exact hv1 w hw
  have hend2 : ∀ w (h : G.Adj v₂ w), c.colorOf v₂ w h ≠ some (if p₂.length % 2 = 1 then otherColor α β β else β) := by
    intro w hw; rw [hlen2]; simp; rw [mem_missingColors_iff] at hv2; exact hv2 w hw
  exact hne_v (alternating_walk_eq c p₁ p₂ β (Or.inr rfl) halt1 halt2 hend1 hend2)

def shiftStep (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) : PartialEdgeColoring G k where
  color e :=
    if e = ⟨s(u, v), huv⟩ then some col
    else if e = ⟨s(u, w), huw⟩ then none
    else c.color e
  proper := by
    intro e₁ e₂ hne ⟨v₀, hv1, hv2⟩ c' h1 h2
    have he_vw : (⟨s(u, v), huv⟩ : G.edgeSet) ≠ ⟨s(u, w), huw⟩ := by
      intro heq; have : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq]; exact h_col
      rw [mem_missingColors_iff] at h_miss; exact h_miss u huv.symm (by rwa [colorOf_symm])
    by_cases he1_v : e₁ = ⟨s(u, v), huv⟩
    · have hc' : c' = col := (Option.some.inj (by simpa [he1_v] using h1)).symm
      have he2_v : e₂ ≠ ⟨s(u, v), huv⟩ := by rintro rfl; exact hne he1_v
      have he2_w : e₂ ≠ ⟨s(u, w), huw⟩ := by rintro rfl; simp [he_vw.symm] at h2
      have h2_orig : c.color e₂ = some c' := by simpa [he2_v, he2_w] using h2
      rw [hc'] at h2_orig
      obtain ⟨z, hz_adj, rfl⟩ := edge_eq_of_mem G e₂ v₀ hv2
      rcases Sym2.mem_iff.mp (he1_v ▸ hv1) with rfl | rfl
      · exact c.proper he2_w.symm ⟨v₀, Sym2.mem_mk_left v₀ w, Sym2.mem_mk_left v₀ z⟩ h_col h2_orig
      · rw [mem_missingColors_iff] at h_miss; exact h_miss z hz_adj h2_orig
    · by_cases he2_v : e₂ = ⟨s(u, v), huv⟩
      · have hc' : c' = col := (Option.some.inj (by simpa [he2_v] using h2)).symm
        have he1_v' : e₁ ≠ ⟨s(u, v), huv⟩ := he1_v
        have he1_w : e₁ ≠ ⟨s(u, w), huw⟩ := by rintro rfl; simp [he_vw.symm] at h1
        have h1_orig : c.color e₁ = some c' := by simpa [he1_v', he1_w] using h1
        rw [hc'] at h1_orig
        obtain ⟨z, hz_adj, rfl⟩ := edge_eq_of_mem G e₁ v₀ hv1
        rcases Sym2.mem_iff.mp (he2_v ▸ hv2) with rfl | rfl
        · exact c.proper he1_w ⟨v₀, Sym2.mem_mk_left v₀ z, Sym2.mem_mk_left v₀ w⟩ h1_orig h_col
        · rw [mem_missingColors_iff] at h_miss; exact h_miss z hz_adj h1_orig
      · by_cases he1_w : e₁ = ⟨s(u, w), huw⟩
        · subst he1_w; simp [he1_v] at h1
        · by_cases he2_w : e₂ = ⟨s(u, w), huw⟩
          · subst he2_w; simp [he2_v] at h2
          · exact c.proper hne ⟨v₀, hv1, hv2⟩ (by simpa [he1_v, he1_w] using h1) (by simpa [he2_v, he2_w] using h2)

lemma card_uncoloredEdges_shiftStep [Fintype G.edgeSet] (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (h_none : c.colorOf u v huv = none) :
    (c.shiftStep u v w huv huw col h_col h_miss).uncoloredEdges.card = c.uncoloredEdges.card := by
  have he_vw : (⟨s(u, v), huv⟩ : G.edgeSet) ≠ ⟨s(u, w), huw⟩ := by
    intro heq; have hc : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq]; exact h_col
    dsimp [colorOf] at h_none; rw [h_none] at hc; cases hc
  have he_v_mem : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
    simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_none
  have he_w_not_mem : (⟨s(u, w), huw⟩ : G.edgeSet) ∉ c.uncoloredEdges := by
    simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hc
    dsimp [colorOf] at h_col
    rw [hc] at h_col
    cases h_col
  have heq_set : (c.shiftStep u v w huv huw col h_col h_miss).uncoloredEdges =
      insert ⟨s(u, w), huw⟩ (c.uncoloredEdges.erase ⟨s(u, v), huv⟩) := by
    ext e
    simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_erase]
    dsimp [shiftStep]
    split_ifs with he1 he2
    · simp [he1, he_vw]
    · simp [he2]
    · constructor
      · intro h; exact Or.inr ⟨he1, h⟩
      · rintro (rfl | ⟨-, h⟩)
        · exfalso; exact he2 rfl
        · exact h
  rw [heq_set, Finset.card_insert_of_notMem (by simp [he_vw.symm, he_w_not_mem]), Finset.card_erase_of_mem he_v_mem]
  have := Finset.card_pos.mpr ⟨_, he_v_mem⟩; omega

lemma shiftStep_colorOf_none (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) :
    (c.shiftStep u v w huv huw col h_col h_miss).colorOf u w huw = none := by
  dsimp [colorOf, shiftStep]
  have he_vw : (⟨s(u, w), huw⟩ : G.edgeSet) ≠ ⟨s(u, v), huv⟩ := by
    intro heq; have hc : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq.symm]; exact h_col
    rw [mem_missingColors_iff] at h_miss; exact h_miss u huv.symm (by rwa [colorOf_symm])
  simp [he_vw]

lemma shiftStep_missing_u (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (α : Fin k) (hα : α ∈ c.missingColors u) :
    α ∈ (c.shiftStep u v w huv huw col h_col h_miss).missingColors u := by
  rw [mem_missingColors_iff] at hα ⊢
  intro z hz
  dsimp [colorOf, shiftStep]
  split_ifs with he1 he2
  · intro heq; have hc : col = α := Option.some.inj heq; subst hc; exact hα w huw h_col
  · intro heq; cases heq
  · exact hα z hz

lemma shiftStep_missing_of_ne_v (u v w x : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (hxv : x ≠ v) (γ : Fin k) (hγ : γ ∈ c.missingColors x) :
    γ ∈ (c.shiftStep u v w huv huw col h_col h_miss).missingColors x := by
  rcases eq_or_ne x u with rfl | hxu
  · exact c.shiftStep_missing_u x v w huv huw col h_col h_miss γ hγ
  · rw [mem_missingColors_iff] at hγ ⊢
    intro z hz
    dsimp [colorOf, shiftStep]
    have he1 : (⟨s(x, z), hz⟩ : G.edgeSet) ≠ ⟨s(u, v), huv⟩ := by
      intro heq
      have : s(x, z) = s(u, v) := Subtype.ext_iff.mp heq
      rw [Sym2.eq_iff] at this
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxu rfl
      · exact hxv rfl
    split_ifs with he_v he_w
    · exfalso; exact he1 he_v
    · intro heq; cases heq
    · exact hγ z hz

lemma shiftStep_colorOf_of_ne (u v w y z : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (hyz : G.Adj y z)
    (h_ne1 : (⟨s(y, z), hyz⟩ : G.edgeSet) ≠ ⟨s(u, v), huv⟩)
    (h_ne2 : (⟨s(y, z), hyz⟩ : G.edgeSet) ≠ ⟨s(u, w), huw⟩) :
    (c.shiftStep u v w huv huw col h_col h_miss).colorOf y z hyz = c.colorOf y z hyz := by
  dsimp [colorOf, shiftStep]; simp [h_ne1, h_ne2]

lemma bipartite_walk_length (b : V → Bool) (hb : ∀ x y, G.Adj x y → b y = !b x)
    (H : SimpleGraph V) (hH : H ≤ G) :
    ∀ {x y : V} (p : H.Walk x y), b y = if p.length % 2 = 1 then !b x else b x
  | x, _, .nil => by simp
  | x, y, @Walk.cons _ _ _ v _ h p => by
    have ih := bipartite_walk_length b hb H hH p
    have h_adj := hb x v (hH h)
    rw [Walk.length_cons, ih, h_adj]
    have hcases : p.length % 2 = 0 ∨ p.length % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · have : (p.length + 1) % 2 = 1 := by omega
      simp [h0, this]
    · have : (p.length + 1) % 2 = 0 := by omega
      simp [h1, this]

/--
In any bipartite graph ($G.\text{Colorable } 2$), if $u v$ is an uncolored edge, no alternating
$(\alpha, \beta)$ path in the Kempe subgraph can connect $u$ and $v$.
-/
theorem kempe_not_reachable_bipartite (h_bip : G.Colorable 2) {u v : V} (hadj : G.Adj u v)
    {α β : Fin k} (hne : α ≠ β) (hα : α ∈ c.missingColors u) (hβ : β ∈ c.missingColors v) :
    ¬ (c.kempeGraph α β).Reachable u v := by
  intro hreach
  obtain ⟨bicol⟩ := h_bip
  let b : V → Bool := fun x => (bicol x).val == 0
  have hb : ∀ x y, G.Adj x y → b y = !b x := by
    intro x y hxy
    have hne' : (bicol x).val ≠ (bicol y).val := fun h => bicol.valid hxy (Fin.ext h)
    have hx := (bicol x).isLt; have hy := (bicol y).isLt
    dsimp [b]
    have : (bicol x).val = 0 ∨ (bicol x).val = 1 := by omega
    have : (bicol y).val = 0 ∨ (bicol y).val = 1 := by omega
    rcases ‹(bicol x).val = 0 ∨ (bicol x).val = 1› with hx0 | hx1 <;>
    rcases ‹(bicol y).val = 0 ∨ (bicol y).val = 1› with hy0 | hy1 <;> simp [*] <;> omega
  obtain ⟨p, hp_path⟩ := hreach.exists_isPath
  have h_first : c.FirstColor α β p β := by
    cases p with
    | nil => dsimp [FirstColor]
    | cons h p' =>
      dsimp [FirstColor]
      rcases h.2 with hcolα | hcolβ
      · rw [mem_missingColors_iff] at hα; exact (hα _ h.1 hcolα).elim
      · exact hcolβ
  have h_alt := isAlternating_of_isPath c hne p β hp_path (Or.inr rfl) h_first
  have h_len_eq := bipartite_walk_length b hb (c.kempeGraph α β) (c.kempeGraph_le α β) p
  have hbv := hb u v hadj
  rw [hbv] at h_len_eq
  have h_mod : p.length % 2 = 1 := by
    by_contra h0
    have : p.length % 2 = 0 := by omega
    rw [this] at h_len_eq
    revert h_len_eq; cases b u <;> decide
  have h_len_pos : p.length > 0 := by omega
  obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p β h_alt (Or.inr rfl) h_len_pos
  rw [h_mod] at hz_col
  rw [mem_missingColors_iff] at hβ
  exact hβ z hz_adj.symm (by rwa [colorOf_symm])

/-- Extends a partial edge coloring by coloring uncolored edge $u v$ with a common missing color. -/
def extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) : PartialEdgeColoring G k where
  color e := if e = ⟨s(u, v), hadj⟩ then some col else c.color e
  proper := by
    intro e₁ e₂ hne ⟨v₀, hv1, hv2⟩ c' h1 h2
    by_cases he1 : e₁ = ⟨s(u, v), hadj⟩ <;> by_cases he2 : e₂ = ⟨s(u, v), hadj⟩
    · exact hne (he1.trans he2.symm)
    · have hc' : c' = col := (Option.some.inj (by simpa [he1] using h1)).symm
      have h2_orig : c.color e₂ = some c' := by simpa [he2] using h2
      rw [hc'] at h2_orig
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₂ v₀ hv2
      rcases Sym2.mem_iff.mp (he1 ▸ hv1) with rfl | rfl
      · rw [mem_missingColors_iff] at hu; exact hu w hw_adj h2_orig
      · rw [mem_missingColors_iff] at hv; exact hv w hw_adj h2_orig
    · have hc' : c' = col := (Option.some.inj (by simpa [he2] using h2)).symm
      have h1_orig : c.color e₁ = some c' := by simpa [he1] using h1
      rw [hc'] at h1_orig
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₁ v₀ hv1
      rcases Sym2.mem_iff.mp (he2 ▸ hv2) with rfl | rfl
      · rw [mem_missingColors_iff] at hu; exact hu w hw_adj h1_orig
      · rw [mem_missingColors_iff] at hv; exact hv w hw_adj h1_orig
    · exact c.proper hne ⟨v₀, hv1, hv2⟩ (by simpa [he1] using h1) (by simpa [he2] using h2)

lemma uncoloredEdges_extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) :
    (c.extendColor u v hadj col hu hv).uncoloredEdges = c.uncoloredEdges.erase ⟨s(u, v), hadj⟩ := by
  ext e
  simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  dsimp [extendColor]
  split_ifs with heq <;> simp [heq]

/-- Any non-empty partial edge coloring on a bipartite graph can be extended to strictly fewer uncolored edges. -/
theorem exists_extended_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (hne : c.uncoloredEdges.Nonempty) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  obtain ⟨⟨e_val, he_prop⟩, he⟩ := hne
  induction e_val using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := he_prop
    have he_none : c.colorOf u v hadj = none := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he; exact he
    have he_mem : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]; exact he_none
    obtain ⟨α, hα⟩ := exists_missingColor_of_uncolored c hadj he_none h_max
    obtain ⟨β, hβ⟩ := exists_missingColor_of_uncolored c hadj.symm (by rwa [colorOf_symm]) h_max
    by_cases hab : α = β
    · subst hab
      refine ⟨c.extendColor u v hadj α hα hβ, ?_⟩
      rw [uncoloredEdges_extendColor, Finset.card_erase_of_mem he_mem]
      exact Nat.pred_lt (Finset.card_pos.mpr ⟨_, he_mem⟩).ne'
    · have hnreach := kempe_not_reachable_bipartite c h_bip hadj hab hα hβ
      let c_swap := c.kempeSwap α β u
      have hβ_u : β ∈ c_swap.missingColors u := kempeSwap_missing_u c α β u hα
      have hβ_v : β ∈ c_swap.missingColors v := kempeSwap_missing_v c α β u v hnreach hβ
      have h_none_swap : c_swap.color ⟨s(u, v), hadj⟩ = none := kempeSwap_colorOf_none c α β u v hadj hnreach he_none
      refine ⟨c_swap.extendColor u v hadj β hβ_u hβ_v, ?_⟩
      have he_swap_mem : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ c_swap.uncoloredEdges := by
        simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]; exact h_none_swap
      rw [uncoloredEdges_extendColor, Finset.card_erase_of_mem he_swap_mem, uncoloredEdges_kempeSwap]
      exact Nat.pred_lt (Finset.card_pos.mpr ⟨_, he_mem⟩).ne'

/-- By well-founded induction on uncolored edges, a bipartite graph admits a complete proper edge coloring. -/
theorem exists_full_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (c : PartialEdgeColoring G k) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
  by_cases h : c.uncoloredEdges = ∅
  · exact ⟨c, h⟩
  · obtain ⟨c', hlt⟩ := c.exists_extended_coloring h_max h_bip (Finset.nonempty_iff_ne_empty.mpr h)
    obtain ⟨c'', h''⟩ := exists_full_coloring h_max h_bip c'
    exact ⟨c'', h''⟩
termination_by c.uncoloredEdges.card

lemma exists_extended_of_fan (u : V) :
    ∀ (n : ℕ) (vs : List V) (cols : List (Fin k)) (c : PartialEdgeColoring G k)
      (hlen_vs : vs.length = n + 1)
      (hlen : cols.length = vs.length)
      (hnodup : vs.Nodup)
      (hadj : ∀ v ∈ vs, G.Adj u v)
      (hnone : ∀ (hne : vs ≠ []), c.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none)
      (hstep : ∀ (i : ℕ) (hi : i + 1 < vs.length),
        c.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols[i])
      (hmiss : ∀ (i : ℕ) (hi : i < vs.length),
        cols[i] ∈ c.missingColors vs[i])
      (hend : ∀ (hne : cols ≠ []), cols.getLast hne ∈ c.missingColors u),
      ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  intro n
  induction n with
  | zero =>
    intro vs cols c hlen_vs hlen _ hadj hnone _ hmiss hend
    rcases vs with _ | ⟨v₀, _ | ⟨v₁, vs'⟩⟩ <;> try cases hlen_vs
    rcases cols with _ | ⟨β₀, _ | ⟨β₁, cols'⟩⟩ <;> try cases hlen
    have hadj0 : G.Adj u v₀ := hadj v₀ (by simp)
    have hnone0 : c.colorOf u v₀ hadj0 = none := hnone (by simp)
    have hmiss0 : β₀ ∈ c.missingColors v₀ := hmiss 0 (by simp)
    have hend0 : β₀ ∈ c.missingColors u := hend (by simp)
    have he_mem : (⟨s(u, v₀), hadj0⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnone0
    refine ⟨c.extendColor u v₀ hadj0 β₀ hend0 hmiss0, ?_⟩
    rw [uncoloredEdges_extendColor, Finset.card_erase_of_mem he_mem]
    exact Nat.pred_lt (Finset.card_pos.mpr ⟨⟨s(u, v₀), hadj0⟩, he_mem⟩).ne'
  | succ m ih =>
    intro vs cols c hlen_vs hlen hnodup hadj hnone hstep hmiss hend
    rcases vs with _ | ⟨v₀, _ | ⟨v₁, vs'⟩⟩
    · contradiction
    · simp only [List.length_cons, List.length_nil] at hlen_vs; omega
    rcases cols with _ | ⟨β₀, _ | ⟨β₁, cols'⟩⟩
    · simp only [List.length_cons, List.length_nil] at hlen; omega
    · simp only [List.length_cons, List.length_nil] at hlen; omega
    have hlen_tail : (β₁ :: cols').length = (v₁ :: vs').length := by
      simp only [List.length_cons] at hlen ⊢; omega
    have hlen_vs_tail : (v₁ :: vs').length = m + 1 := by
      simp only [List.length_cons] at hlen_vs ⊢; omega
    have hadj0 : G.Adj u v₀ := hadj v₀ (by simp)
    have hadj1 : G.Adj u v₁ := hadj v₁ (by simp)
    have hnone0 : c.colorOf u v₀ hadj0 = none := hnone (by simp)
    have hcol0 : c.colorOf u v₁ hadj1 = some β₀ := hstep 0 (by simp [hlen_vs])
    have hmiss0 : β₀ ∈ c.missingColors v₀ := hmiss 0 (by simp [hlen_vs])
    let c₁ := c.shiftStep u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0
    have hcard_c1 : c₁.uncoloredEdges.card = c.uncoloredEdges.card :=
      card_uncoloredEdges_shiftStep c u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0 hnone0
    have hnodup_cons := (List.nodup_cons.mp hnodup).2
    have h_v0_not_in : v₀ ∉ v₁ :: vs' := (List.nodup_cons.mp hnodup).1
    have hadj_tail : ∀ v ∈ v₁ :: vs', G.Adj u v := fun v hv => hadj v (List.mem_cons_of_mem _ hv)
    have hnone_tail : ∀ (hne : v₁ :: vs' ≠ []), c₁.colorOf u ((v₁ :: vs').head hne) (hadj_tail _ (List.head_mem hne)) = none := by
      intro _
      exact shiftStep_colorOf_none c u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0
    have hstep_tail : ∀ (i : ℕ) (hi : i + 1 < (v₁ :: vs').length),
        c₁.colorOf u (v₁ :: vs')[i + 1] (hadj_tail _ (List.getElem_mem _)) = some (β₁ :: cols')[i] := by
      intro i hi
      have h_ne1 : (⟨s(u, (v₁ :: vs')[i + 1]), hadj_tail _ (List.getElem_mem _)⟩ : G.edgeSet) ≠ ⟨s(u, v₀), hadj0⟩ := by
        intro heq
        have : s(u, (v₁ :: vs')[i + 1]) = s(u, v₀) := Subtype.ext_iff.mp heq
        rw [Sym2.eq_iff] at this
        rcases this with ⟨-, heq_v⟩ | ⟨heq_u, _⟩
        · exact h_v0_not_in (heq_v ▸ List.getElem_mem (by omega))
        · exact hadj0.ne heq_u
      have h_ne2 : (⟨s(u, (v₁ :: vs')[i + 1]), hadj_tail _ (List.getElem_mem _)⟩ : G.edgeSet) ≠ ⟨s(u, v₁), hadj1⟩ := by
        intro heq
        have : s(u, (v₁ :: vs')[i + 1]) = s(u, v₁) := Subtype.ext_iff.mp heq
        rw [Sym2.eq_iff] at this
        rcases this with ⟨-, heq_v⟩ | ⟨heq_u, _⟩
        · have hi_vs' : i < vs'.length := by simp only [List.length_cons] at hi; omega
          have h_eq_elem : (v₁ :: vs')[i + 1] = vs'[i] := rfl
          have hmem : vs'[i] ∈ vs' := List.getElem_mem hi_vs'
          have : v₁ ∈ vs' := heq_v.symm ▸ (h_eq_elem ▸ hmem)
          exact (List.nodup_cons.mp hnodup_cons).1 this
        · exact hadj1.ne heq_u
      rw [shiftStep_colorOf_of_ne c u v₀ v₁ _ _ hadj0 hadj1 β₀ hcol0 hmiss0 _ h_ne1 h_ne2]
      exact hstep (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
    have hmiss_tail : ∀ (i : ℕ) (hi : i < (v₁ :: vs').length),
        (β₁ :: cols')[i] ∈ c₁.missingColors (v₁ :: vs')[i] := by
      intro i hi
      have h_ne_v0 : (v₁ :: vs')[i] ≠ v₀ := fun heq => h_v0_not_in (heq ▸ List.getElem_mem (by omega))
      exact shiftStep_missing_of_ne_v c u v₀ v₁ _ hadj0 hadj1 β₀ hcol0 hmiss0 h_ne_v0 _
        (hmiss (i + 1) (by simp only [List.length_cons] at hi ⊢; omega))
    have hend_tail : ∀ (hne : β₁ :: cols' ≠ []), (β₁ :: cols').getLast hne ∈ c₁.missingColors u := by
      intro hne'
      have h_last_eq : (β₁ :: cols').getLast hne' = (β₀ :: β₁ :: cols').getLast (by simp) := rfl
      rw [h_last_eq]
      exact shiftStep_missing_u c u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0 _ (hend (by simp))
    obtain ⟨c', hlt⟩ := ih (v₁ :: vs') (β₁ :: cols') c₁ hlen_vs_tail hlen_tail hnodup_cons hadj_tail hnone_tail hstep_tail hmiss_tail hend_tail
    refine ⟨c', ?_⟩
    rwa [hcard_c1] at hlt

lemma exists_extended_of_fan_cycle (u : V) (n : ℕ) (vs : List V) (cols : List (Fin k))
    (c : PartialEdgeColoring G k) (α : Fin k) (j : ℕ)
    (hlen_vs : vs.length = n + 1)
    (hlen : cols.length = vs.length)
    (hnodup : vs.Nodup)
    (hadj : ∀ v ∈ vs, G.Adj u v)
    (hnone : ∀ (hne : vs ≠ []), c.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none)
    (hstep : ∀ (i : ℕ) (hi : i + 1 < vs.length),
      c.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols[i])
    (hmiss : ∀ (i : ℕ) (hi : i < vs.length),
      cols[i] ∈ c.missingColors vs[i])
    (hα : α ∈ c.missingColors u)
    (hj : j < n)
    (h_cycle : cols[n]'(by rw [hlen, hlen_vs]; omega) = cols[j]'(by rw [hlen, hlen_vs]; omega))
    (h_diff : ∀ (i : ℕ) (hi : i < n), i ≠ j → cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ cols[j]'(by rw [hlen, hlen_vs]; omega)) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  have hj_lt_cols : j < cols.length := by rw [hlen, hlen_vs]; omega
  have hn_lt_cols : n < cols.length := by rw [hlen, hlen_vs]; omega
  have hj_lt_vs : j < vs.length := by rw [hlen_vs]; omega
  have hn_lt_vs : n < vs.length := by rw [hlen_vs]; omega
  let β : Fin k := cols[j]
  have hβ_eq : cols[n] = β := h_cycle
  have h_col_ne_α : ∀ (i : ℕ) (hi : i < n), cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ α := by
    intro i hi heq
    have h_edge := hstep i (by rw [hlen_vs]; omega)
    rw [mem_missingColors_iff] at hα
    have h_ne := hα vs[i + 1] (hadj _ (List.getElem_mem (by rw [hlen_vs]; omega)))
    rw [heq] at h_edge
    exact h_ne h_edge
  have h_ne_α_β : α ≠ β := by
    have := h_col_ne_α j hj
    intro heq; exact this heq.symm
  have hmiss_j : β ∈ c.missingColors vs[j] := hmiss j hj_lt_vs
  have hmiss_n : β ∈ c.missingColors vs[n] := by
    have := hmiss n hn_lt_vs; rw [hβ_eq] at this; exact this
  have h_vs_ne : vs[j] ≠ vs[n] := by
    intro heq
    have heq_idx : (⟨j, hj_lt_vs⟩ : Fin vs.length) = ⟨n, hn_lt_vs⟩ :=
      (List.nodup_iff_injective_getElem.mp hnodup) heq
    have : j = n := Fin.ext_iff.mp heq_idx
    omega
  have h_not_reach_both := kempe_not_reachable_both c h_ne_α_β hα hmiss_j hmiss_n h_vs_ne
  let c_swap := c.kempeSwap α β u
  have h_card_swap : c_swap.uncoloredEdges.card = c.uncoloredEdges.card := by
    rw [uncoloredEdges_kempeSwap]
  have h_miss_u_swap : β ∈ c_swap.missingColors u := kempeSwap_missing_u c α β u hα
  have hnone_swap : ∀ (hne : vs ≠ []), c_swap.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none := by
    intro hne; exact kempeSwap_color_none c α β u _ (hnone hne)
  by_cases h_reach_j : (c.kempeGraph α β).Reachable u vs[j]
  · have hnreach_n : ¬ (c.kempeGraph α β).Reachable u vs[n] := fun h => h_not_reach_both ⟨h_reach_j, h⟩
    have hmiss_n_swap : β ∈ c_swap.missingColors vs[n] := kempeSwap_missing_v c α β u vs[n] hnreach_n hmiss_n
    have hmiss_j_swap : α ∈ c_swap.missingColors vs[j] := kempeSwap_missing_of_reachable c α β u vs[j] h_reach_j hmiss_j
    let cols' := cols.set j α
    have hlen_cols' : cols'.length = vs.length := by rw [List.length_set, hlen]
    have hj_lt_cols' : j < cols'.length := by rw [hlen_cols', hlen_vs]; omega
    have hn_lt_cols' : n < cols'.length := by rw [hlen_cols', hlen_vs]; omega
    have hnone_swap' : ∀ (hne : vs ≠ []), c_swap.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none := hnone_swap
    have hstep_swap : ∀ (i : ℕ) (hi : i + 1 < vs.length),
        c_swap.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols'[i] := by
      intro i hi
      have hi_lt_n : i < n := by rw [hlen_vs] at hi; omega
      have hi_lt_cols' : i < cols'.length := by rw [hlen_cols', hlen_vs]; omega
      have h_col_orig := hstep i hi
      by_cases heq_ij : i = j
      · subst heq_ij
        have h_get_cols' : cols'[i] = α := by simp [cols', List.getElem_set]
        rw [h_get_cols']
        exact kempeSwap_colorOf_alpha c α β u vs[i + 1] (hadj _ (List.getElem_mem _)) h_col_orig
      · have h_get_cols' : cols'[i] = cols[i] := by
          have : j ≠ i := fun h => heq_ij h.symm
          simp [cols', List.getElem_set, this]
        rw [h_get_cols']
        exact kempeSwap_colorOf_of_ne c α β (cols[i]) u u vs[i + 1] (hadj _ (List.getElem_mem _))
          (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n heq_ij) h_col_orig
    have hmiss_swap : ∀ (i : ℕ) (hi : i < vs.length), cols'[i] ∈ c_swap.missingColors vs[i] := by
      intro i hi
      by_cases heq_ij : i = j
      · subst heq_ij
        have : i < cols'.length := by rw [hlen_cols']; exact hi
        have h_get_cols' : cols'[i] = α := by simp [cols', List.getElem_set]
        rw [h_get_cols']; exact hmiss_j_swap
      · by_cases heq_in : i = n
        · have h_get_cols' : cols'[i] = β := by
            have : i < cols'.length := by rw [hlen_cols']; exact hi
            have h_idx_eq : cols'[i] = cols'[n] := by congr 1
            rw [h_idx_eq, List.getElem_set]
            have : j ≠ n := ne_of_lt hj
            simp [this, hβ_eq]
          rw [h_get_cols']
          have : vs[i] = vs[n] := by congr 1
          rw [this]; exact hmiss_n_swap
        · have hi_lt_n : i < n := by rw [hlen_vs] at hi; omega
          have : i < cols'.length := by rw [hlen_cols']; exact hi
          have h_get_cols' : cols'[i] = cols[i] := by
            have : j ≠ i := fun h => heq_ij h.symm
            simp [cols', List.getElem_set, this]
          rw [h_get_cols']
          exact kempeSwap_missing_of_ne c α β (cols[i]) u vs[i] (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n heq_ij) (hmiss i (by rw [hlen_vs]; omega))
    have hend_swap : ∀ (hne : cols' ≠ []), cols'.getLast hne ∈ c_swap.missingColors u := by
      intro hne
      have h_last : cols'.getLast hne = β := by
        rw [List.getLast_eq_getElem, List.getElem_set]
        have : j ≠ cols'.length - 1 := by rw [hlen_cols', hlen_vs]; omega
        have : cols'.length - 1 = n := by rw [hlen_cols', hlen_vs]; omega
        have : j ≠ n := ne_of_lt hj
        simp [*, hβ_eq]
      rw [h_last]; exact h_miss_u_swap
    obtain ⟨c', hlt⟩ := exists_extended_of_fan u n vs cols' c_swap hlen_vs hlen_cols' hnodup hadj hnone_swap' hstep_swap hmiss_swap hend_swap
    refine ⟨c', ?_⟩
    rwa [h_card_swap] at hlt
  · have hnreach_j : ¬ (c.kempeGraph α β).Reachable u vs[j] := h_reach_j
    have hmiss_j_swap : β ∈ c_swap.missingColors vs[j] := kempeSwap_missing_v c α β u vs[j] hnreach_j hmiss_j
    let vs_sub := vs.take (j + 1)
    let cols_sub := cols.take (j + 1)
    have hlen_vs_sub : vs_sub.length = j + 1 := by dsimp [vs_sub]; rw [List.length_take]; omega
    have hlen_cols_sub : cols_sub.length = vs_sub.length := by dsimp [cols_sub, vs_sub]; rw [List.length_take, List.length_take, hlen]
    have hnodup_sub : vs_sub.Nodup := List.Nodup.sublist (List.take_sublist (j + 1) vs) hnodup
    have hadj_sub : ∀ v ∈ vs_sub, G.Adj u v := fun v hv => hadj v (List.mem_of_mem_take hv)
    have hnone_swap_sub : ∀ (hne : vs_sub ≠ []), c_swap.colorOf u (vs_sub.head hne) (hadj_sub _ (List.head_mem hne)) = none := by
      intro hne
      have hne_vs : vs ≠ [] := List.ne_nil_of_length_pos (by rw [hlen_vs]; omega)
      have hhead : vs_sub.head hne = vs.head hne_vs := by cases vs with | nil => contradiction | cons _ _ => rfl
      have h0 := hnone hne_vs
      dsimp [colorOf] at h0 ⊢
      have heq_edge : (⟨s(u, vs_sub.head hne), hadj_sub _ (List.head_mem hne)⟩ : G.edgeSet) = ⟨s(u, vs.head hne_vs), hadj _ (List.head_mem hne_vs)⟩ := by
        ext; simp [hhead]
      rw [heq_edge]
      exact kempeSwap_color_none c α β u _ h0
    have hstep_swap_sub : ∀ (i : ℕ) (hi : i + 1 < vs_sub.length),
        c_swap.colorOf u vs_sub[i + 1] (hadj_sub _ (List.getElem_mem _)) = some cols_sub[i] := by
      intro i hi
      have hi_lt_j : i < j := by rw [hlen_vs_sub] at hi; omega
      have hi_lt_n : i < n := by omega
      have h_col_orig := hstep i (by rw [hlen_vs]; omega)
      have h_get_vs : vs_sub[i + 1] = vs[i + 1] := List.getElem_take
      have h_get_cols : cols_sub[i] = cols[i] := List.getElem_take
      have heq_edge : (⟨s(u, vs_sub[i + 1]), hadj_sub _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, vs[i + 1]), hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))⟩ := by
        ext; simp [h_get_vs]
      dsimp [colorOf] at h_col_orig ⊢
      rw [heq_edge, h_get_cols]
      exact kempeSwap_colorOf_of_ne c α β (cols[i]) u u vs[i + 1] (hadj _ (List.getElem_mem _))
        (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n (ne_of_lt hi_lt_j)) h_col_orig
    have hmiss_swap_sub : ∀ (i : ℕ) (hi : i < vs_sub.length), cols_sub[i] ∈ c_swap.missingColors vs_sub[i] := by
      intro i hi
      have hi_le_j : i ≤ j := by rw [hlen_vs_sub] at hi; omega
      have h_get_vs : vs_sub[i] = vs[i] := List.getElem_take
      have h_get_cols : cols_sub[i] = cols[i] := List.getElem_take
      rw [h_get_vs, h_get_cols]
      by_cases heq_ij : i = j
      · subst heq_ij; exact hmiss_j_swap
      · have hi_lt_j : i < j := Nat.lt_of_le_of_ne hi_le_j heq_ij
        have hi_lt_n : i < n := by omega
        exact kempeSwap_missing_of_ne c α β (cols[i]) u vs[i] (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n heq_ij) (hmiss i (by rw [hlen_vs]; omega))
    have hend_swap_sub : ∀ (hne : cols_sub ≠ []), cols_sub.getLast hne ∈ c_swap.missingColors u := by
      intro hne
      have h_last : cols_sub.getLast hne = β := by
        have hlen_sub : cols_sub.length = j + 1 := by dsimp [cols_sub]; rw [List.length_take]; omega
        have h_get : cols_sub[j] = cols[j] := List.getElem_take
        rw [List.getLast_eq_getElem, show cols_sub[cols_sub.length - 1] = cols_sub[j] by congr 1; omega, h_get]
      rw [h_last]; exact h_miss_u_swap
    obtain ⟨c', hlt⟩ := exists_extended_of_fan u j vs_sub cols_sub c_swap hlen_vs_sub hlen_cols_sub hnodup_sub hadj_sub hnone_swap_sub hstep_swap_sub hmiss_swap_sub hend_swap_sub
    refine ⟨c', ?_⟩
    rwa [h_card_swap] at hlt

lemma exists_extended_coloring_of_fan (u : V) (α : Fin k) (hα : α ∈ c.missingColors u) (h_max : G.maxDegree < k) :
    ∀ (N : ℕ) (n : ℕ) (vs : List V) (cols : List (Fin k))
      (_hN : Fintype.card V - vs.length = N)
      (hlen_vs : vs.length = n + 1)
      (hlen : cols.length = vs.length)
      (_hnodup : vs.Nodup)
      (hadj : ∀ v ∈ vs, G.Adj u v)
      (_hnone : ∀ (hne : vs ≠ []), c.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none)
      (_hstep : ∀ (i : ℕ) (hi : i + 1 < vs.length),
        c.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols[i])
      (_hmiss : ∀ (i : ℕ) (hi : i < vs.length),
        cols[i] ∈ c.missingColors vs[i])
      (_h_diff : ∀ (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < i),
        cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ cols[j]'(by rw [hlen, hlen_vs]; omega)),
      ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro n vs cols hN hlen_vs hlen hnodup hadj hnone hstep hmiss h_diff
    have hn_lt_cols : n < cols.length := by rw [hlen, hlen_vs]; omega
    have hn_lt_vs : n < vs.length := by rw [hlen_vs]; omega
    by_cases h_miss_u : cols[n] ∈ c.missingColors u
    · have hend : ∀ (hne : cols ≠ []), cols.getLast hne ∈ c.missingColors u := by
        intro hne
        rw [List.getLast_eq_getElem]
        have : cols.length - 1 = n := by rw [hlen, hlen_vs]; omega
        have h_get : cols[cols.length - 1] = cols[n] := by congr 1
        rw [h_get]
        exact h_miss_u
      exact exists_extended_of_fan u n vs cols c hlen_vs hlen hnodup hadj hnone hstep hmiss hend
    · have hw_used : cols[n] ∈ c.usedColors u := by
        have : cols[n] ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
        simpa [missingColors, Finset.mem_sdiff, this] using h_miss_u
      rw [mem_usedColors_iff] at hw_used
      obtain ⟨w, hw_adj, hw_col⟩ := hw_used
      by_cases hw_in : w ∈ vs
      · obtain ⟨m, hm_lt, hm_eq⟩ := List.getElem_of_mem hw_in
        have hm_pos : 0 < m := by
          by_contra hm0; have hm_zero : m = 0 := by omega
          have hne_vs : vs ≠ [] := List.ne_nil_of_length_pos (by rw [hlen_vs]; omega)
          have h0 := hnone hne_vs; dsimp [colorOf] at h0 hw_col
          have heq_edge : (⟨s(u, vs.head hne_vs), hadj _ (List.head_mem hne_vs)⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by
            ext; simp [List.head_eq_getElem hne_vs, ← show vs[m] = vs[0] by congr 1, hm_eq]
          rw [heq_edge] at h0
          rw [h0] at hw_col; cases hw_col
        let j := m - 1
        have hj : j < n := by rw [hlen_vs] at hm_lt; omega
        have h_cycle : cols[n]'(by rw [hlen, hlen_vs]; omega) = cols[j]'(by rw [hlen, hlen_vs]; omega) := by
          have h_step_j := hstep j (by rw [hlen_vs]; omega)
          have h_vs_j1 : vs[j + 1] = w := by rw [show vs[j + 1] = vs[m] by congr 1; omega, hm_eq]
          dsimp [colorOf] at h_step_j hw_col
          have heq_edge : (⟨s(u, vs[j + 1]), hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by
            ext; simp [h_vs_j1]
          rw [heq_edge] at h_step_j
          rw [hw_col] at h_step_j; exact Option.some.inj h_step_j
        have h_diff_cycle : ∀ (i : ℕ) (hi : i < n), i ≠ j → cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ cols[j]'(by rw [hlen, hlen_vs]; omega) := by
          intro i hi hne_ij
          rcases lt_or_gt_of_ne hne_ij with hlt | hgt
          · exact (h_diff j hj i hlt).symm
          · exact h_diff i hi j hgt
        exact exists_extended_of_fan_cycle u n vs cols c α j hlen_vs hlen hnodup hadj hnone hstep hmiss hα hj h_cycle h_diff_cycle
      · obtain ⟨β_next, hβ_next⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := w)
        have hlen_vs' : (vs ++ [w]).length = (n + 1) + 1 := by simp [hlen_vs]
        have hlen_cols' : (cols ++ [β_next]).length = (vs ++ [w]).length := by simp [hlen, hlen_vs]
        have hnodup' : (vs ++ [w]).Nodup := by
          rw [List.nodup_append]; exact ⟨hnodup, by simp, fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hw_in ha⟩
        have hadj' : ∀ v ∈ vs ++ [w], G.Adj u v := by
          intro v hv; rcases List.mem_append.mp hv with hv | hv
          · exact hadj v hv
          · rw [List.mem_singleton.mp hv]; exact hw_adj
        have hnone' : ∀ (hne : vs ++ [w] ≠ []), c.colorOf u ((vs ++ [w]).head hne) (hadj' _ (List.head_mem hne)) = none := by
          intro hne
          rcases vs with _ | ⟨v0, vs_tl⟩
          · contradiction
          · exact hnone (by simp)
        have hstep' : ∀ (i : ℕ) (hi : i + 1 < (vs ++ [w]).length),
            c.colorOf u (vs ++ [w])[i + 1] (hadj' _ (List.getElem_mem _)) = some (cols ++ [β_next])[i] := by
          intro i hi
          by_cases heq_in : i = n
          · have h_get_vs : (vs ++ [w])[i + 1] = w := by simp [heq_in, hlen_vs]
            have h_get_cols : (cols ++ [β_next])[i] = cols[n] := by simp [heq_in, List.getElem_append_left hn_lt_cols]
            dsimp [colorOf] at hw_col ⊢
            have heq_edge : (⟨s(u, (vs ++ [w])[i + 1]), hadj' _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by ext; simp [h_get_vs]
            rw [heq_edge, h_get_cols, hw_col]
          · have hi_lt_n : i < n := by omega
            have h_get_vs : (vs ++ [w])[i + 1] = vs[i + 1] := List.getElem_append_left (by omega)
            have h_get_cols : (cols ++ [β_next])[i] = cols[i] := List.getElem_append_left (by omega)
            have h_step_orig := hstep i (by omega)
            dsimp [colorOf] at h_step_orig ⊢
            have heq_edge : (⟨s(u, (vs ++ [w])[i + 1]), hadj' _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, vs[i + 1]), hadj _ (List.getElem_mem (by omega))⟩ := by
              ext; simp [h_get_vs]
            rw [heq_edge, h_get_cols, h_step_orig]
        have hmiss' : ∀ (i : ℕ) (hi : i < (vs ++ [w]).length), (cols ++ [β_next])[i] ∈ c.missingColors (vs ++ [w])[i] := by
          intro i hi
          by_cases heq_in : i = vs.length
          · have h_get_vs : (vs ++ [w])[i] = w := by simp [heq_in]
            have h_get_cols : (cols ++ [β_next])[i] = β_next := by
              have : i = cols.length := by rw [heq_in, hlen]
              simp [this]
            rw [h_get_vs, h_get_cols]; exact hβ_next
          · have hi_lt : i < vs.length := by omega
            rw [List.getElem_append_left hi_lt, List.getElem_append_left (by rw [hlen]; exact hi_lt)]
            exact hmiss i hi_lt
        have h_diff' : ∀ (i : ℕ) (hi : i < n + 1) (j : ℕ) (hj : j < i),
            (cols ++ [β_next])[i]'(by omega) ≠ (cols ++ [β_next])[j]'(by omega) := by
          intro i hi j hj
          by_cases heq_in : i = n
          · have h_get_i : (cols ++ [β_next])[i] = cols[n] := by
              have : (cols ++ [β_next])[n] = cols[n] := List.getElem_append_left hn_lt_cols
              rw [show (cols ++ [β_next])[i] = (cols ++ [β_next])[n] by congr 1, this]
            have h_get_j : (cols ++ [β_next])[j] = cols[j] := List.getElem_append_left (by omega)
            rw [h_get_i, h_get_j]
            intro heq_cols
            have h_step_j := hstep j (by omega)
            have h_step_j' : c.colorOf u vs[j + 1] (hadj _ (List.getElem_mem (by omega))) = some (cols[n]) := by rw [h_step_j, heq_cols]
            have heq_w := colorOf_inj_neighbor c u vs[j + 1] w (hadj _ (List.getElem_mem (by omega))) hw_adj (cols[n]) h_step_j' hw_col
            exact hw_in (heq_w ▸ List.getElem_mem (by omega))
          · have hi_lt_n : i < n := by omega
            rw [List.getElem_append_left (show i < cols.length by omega),
                List.getElem_append_left (show j < cols.length by omega)]
            exact h_diff i hi_lt_n j hj
        have hN' : Fintype.card V - (vs ++ [w]).length < N := by
          rw [← hN, List.length_append, List.length_singleton]
          have : (vs ++ [w]).length ≤ Fintype.card V := by rw [← List.toFinset_card_of_nodup hnodup']; exact Finset.card_le_univ _
          omega
        exact ih _ hN' (n + 1) (vs ++ [w]) (cols ++ [β_next]) rfl hlen_vs' hlen_cols' hnodup' hadj' hnone' hstep' hmiss' h_diff'

/-- Any non-empty partial edge coloring with $k > \Delta(G)$ can be extended to strictly fewer uncolored edges. -/
theorem exists_extended_coloring_vizing (h_max : G.maxDegree < k)
    (hne : c.uncoloredEdges.Nonempty) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  obtain ⟨⟨e_val, he_prop⟩, he⟩ := hne
  induction e_val using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := he_prop
    have he_none : c.colorOf u v hadj = none := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he; exact he
    obtain ⟨α, hα⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := u)
    obtain ⟨β₀, hβ₀⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := v)
    have hadj_single : ∀ w ∈ [v], G.Adj u w := by
      intro w hw; simp only [List.mem_singleton] at hw; subst hw; exact hadj
    have hnone_single : ∀ (hne' : [v] ≠ []), c.colorOf u ([v].head hne') (hadj_single _ (List.head_mem hne')) = none := fun _ => he_none
    have hstep_single : ∀ (i : ℕ) (hi : i + 1 < [v].length),
        c.colorOf u [v][i + 1] (hadj_single _ (List.getElem_mem _)) = some [β₀][i] := by
      intro i hi; simp only [List.length_singleton] at hi; omega
    have hmiss_single : ∀ (i : ℕ) (hi : i < [v].length),
        [β₀][i] ∈ c.missingColors [v][i] := by
      intro i hi; have : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst this; exact hβ₀
    have h_diff_single : ∀ (i : ℕ) (hi : i < 0) (j : ℕ) (hj : j < i),
        [β₀][i]'(by omega) ≠ [β₀][j]'(by omega) := by intro i hi; omega
    exact c.exists_extended_coloring_of_fan u α hα h_max (Fintype.card V - 1) 0 [v] [β₀] rfl rfl rfl (List.nodup_singleton v) hadj_single hnone_single hstep_single hmiss_single h_diff_single

/-- By well-founded induction on uncolored edges, any graph admits a complete proper edge coloring with $k > \Delta(G)$ colors. -/
theorem exists_full_coloring_vizing (h_max : G.maxDegree < k)
    (c : PartialEdgeColoring G k) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
  by_cases h : c.uncoloredEdges = ∅
  · exact ⟨c, h⟩
  · obtain ⟨c', hlt⟩ := c.exists_extended_coloring_vizing h_max (Finset.nonempty_iff_ne_empty.mpr h)
    obtain ⟨c'', h''⟩ := exists_full_coloring_vizing h_max c'
    exact ⟨c'', h''⟩
termination_by c.uncoloredEdges.card

lemma color_isSome (h : c.uncoloredEdges = ∅) (e : G.edgeSet) : ∃ col, c.color e = some col := by
  cases hc : c.color e with
  | none => exact False.elim (Finset.notMem_empty e (h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ e, hc⟩))
  | some col => exact ⟨col, rfl⟩

/-- Convert a fully defined `PartialEdgeColoring` (no uncolored edges) into a total `EdgeColoring`. -/
noncomputable def toEdgeColoring (h : c.uncoloredEdges = ∅) : EdgeColoring G k where
  color e := (c.color_isSome h e).choose
  proper e₁ e₂ hne hshare heq := by
    have h1 := (c.color_isSome h e₁).choose_spec
    have h2 := (c.color_isSome h e₂).choose_spec
    dsimp at heq
    exact c.proper hne hshare (heq ▸ h1) h2

end PartialEdgeColoring

/-- Every bipartite graph $G$ admits a proper edge coloring with $\Delta(G)$ colors. -/
theorem edgeColorable_of_bipartite (h_bip : G.Colorable 2) :
    IsEdgeColorable G G.maxDegree := by
  obtain ⟨c, hc⟩ := PartialEdgeColoring.exists_full_coloring (le_refl G.maxDegree) h_bip .empty
  exact ⟨c.toEdgeColoring hc⟩

/-- Every graph $G$ admits a proper edge coloring with $\Delta(G) + 1$ colors. -/
theorem edgeColorable_of_maxDegree_succ :
    IsEdgeColorable G (G.maxDegree + 1) := by
  obtain ⟨c, hc⟩ := PartialEdgeColoring.exists_full_coloring_vizing (Nat.lt_succ_self G.maxDegree) .empty
  exact ⟨c.toEdgeColoring hc⟩

/--
Vizing's Theorem (1964):
For any finite simple graph $G$ with maximum degree $\Delta(G)$, the edge chromatic number
(chromatic index) $\chi'(G)$ satisfies:
$$\Delta(G) \le \chi'(G) \le \Delta(G) + 1$$
-/
theorem vizings_theorem [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G ∧ chromaticIndex G ≤ G.maxDegree + 1 :=
  ⟨chromatic_index_ge_maxDegree G, csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ (edgeColorable_of_maxDegree_succ G)⟩

/-- A graph is Class 1 if its edge chromatic number achieves the maximum degree $\Delta(G)$. -/
def IsClassOne [Fintype G.edgeSet] : Prop := chromaticIndex G = G.maxDegree

/-- A graph is Class 2 if its edge chromatic number is $\Delta(G) + 1$. -/
def IsClassTwo [Fintype G.edgeSet] : Prop := chromaticIndex G = G.maxDegree + 1

/-- Vizing's Classification: Every finite simple graph is either Class 1 or Class 2. -/
theorem vizing_classification [Fintype G.edgeSet] : IsClassOne G ∨ IsClassTwo G := by
  have ⟨hle, hub⟩ := vizings_theorem G; dsimp [IsClassOne, IsClassTwo]; omega

/--
König's Line Coloring Theorem (1916):
Every bipartite graph is Class 1, i.e., $\chi'(G) = \Delta(G)$.
-/
theorem konig_edge_coloring [Fintype G.edgeSet] (h_bip : G.Colorable 2) : IsClassOne G := by
  have h_ge := chromatic_index_ge_maxDegree G
  have h_le : chromaticIndex G ≤ G.maxDegree := csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ (edgeColorable_of_bipartite G h_bip)
  dsimp [IsClassOne]; omega

end SimpleGraph
