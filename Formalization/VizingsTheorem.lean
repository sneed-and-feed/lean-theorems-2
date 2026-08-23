import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Vizing's Theorem on Edge Colorings & König's Line Coloring Theorem

This file formalizes the theory of proper edge colorings, the chromatic index $\chi'(G)$,
König's Line Coloring Theorem for bipartite graphs, and the statement of Vizing's Theorem
for finite simple graphs.

## Main Definitions
- `ShareVertex`: The relation that two undirected edges share a common endpoint vertex.
- `IsProperEdgeColoring`: Predicate asserting that adjacent edges receive distinct colors.
- `EdgeColoring`: Structure of a proper $k$-edge-coloring of $G$.
- `IsEdgeColorable`: Predicate asserting that $G$ admits a proper $k$-edge-coloring.
- `chromaticIndex`: The minimum number of colors needed to properly color the edges of $G$.
- `IsClassOne`: Predicate for Class 1 graphs ($\chi'(G) = \Delta(G)$).
- `IsClassTwo`: Predicate for Class 2 graphs ($\chi'(G) = \Delta(G) + 1$).
- `PartialEdgeColoring`: Structure of a proper partial $k$-edge-coloring of $G$.
- `kempeGraph`: The $(\alpha, \beta)$-Kempe subgraph induced by edges colored $\alpha$ or $\beta$.
- `kempeSwap`: Color-swapping operation on the Kempe component of a vertex.

## Main Results
- `chromatic_index_ge_maxDegree`: The trivial lower bound $\chi'(G) \ge \Delta(G)$.
- `kempe_not_reachable_bipartite`: In any bipartite graph, if $uv$ is uncolored, no alternating
  $(\alpha, \beta)$ path connects $u$ and $v$.
- `edgeColorable_of_bipartite`: Every bipartite graph $G$ is $\Delta(G)$-edge-colorable.
- `konig_edge_coloring`: König's line coloring theorem (bipartite graphs are Class 1, $\chi'(G) = \Delta(G)$).
- `vizings_theorem`: Vizing's Theorem $\Delta(G) \le \chi'(G) \le \Delta(G) + 1$.
- `vizing_classification`: Classification into Class 1 or Class 2.

## References
- König, D. (1916). *Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre*.
  Mathematische Annalen, 77(4), 453–465.
- Vizing, V. G. (1964). *On an estimate of the chromatic class of a p-graph*. Diskret. Analiz., 3, 25–30.
- Diestel, R. (2017). *Graph Theory*. Graduate Texts in Mathematics, 173.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

lemma fin2_cases (y : Fin 2) : y = 0 ∨ y = 1 := by
  cases y using Fin.cases with
  | zero => left; rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => right; rfl
    | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim

lemma edge_eq_of_mem (e : G.edgeSet) (v : V) (hv : v ∈ (e : Sym2 V)) :
    ∃ (w : V) (h : G.Adj v w), e = ⟨s(v, w), h⟩ := by
  rcases e with ⟨e_val, he_prop⟩
  induction e_val using Sym2.inductionOn with
  | hf x y =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨y, he_prop, rfl⟩
    · refine ⟨x, he_prop.symm, ?_⟩
      apply Subtype.ext
      exact Sym2.eq_swap

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
def IsEdgeColorable (k : ℕ) : Prop :=
  Nonempty (EdgeColoring G k)

/-- The chromatic index (edge chromatic number) $\chi'(G)$ is the minimum number of colors
needed to properly color the edges of $G$. -/
noncomputable def chromaticIndex : ℕ :=
  sInf {k : ℕ | IsEdgeColorable G k}

theorem edgeColorable_card_edgeSet [Fintype G.edgeSet] :
    IsEdgeColorable G (Fintype.card G.edgeSet) := by
  refine ⟨⟨Fintype.equivFin G.edgeSet, ?_⟩⟩
  intro e1 e2 hne _ heq
  exact hne ((Fintype.equivFin G.edgeSet).injective heq)

theorem degree_le_of_edgeColoring {k : ℕ} (c : EdgeColoring G k) (v : V) :
    G.degree v ≤ k := by
  let f : (G.incidenceSet v) → G.edgeSet := fun e => ⟨e.val, e.property.1⟩
  have hf_inj : Function.Injective f := by
    intro e1 e2 h
    have : (f e1).val = (f e2).val := congr_arg Subtype.val h
    exact Subtype.ext this
  let g : (G.incidenceSet v) → Fin k := c.color ∘ f
  have hg_inj : Function.Injective g := by
    intro e1 e2 hg
    dsimp [g] at hg
    by_contra hne
    have hf_ne : f e1 ≠ f e2 := fun h => hne (hf_inj h)
    have hshare : ShareVertex G (f e1) (f e2) := by
      refine ⟨v, e1.property.2, e2.property.2⟩
    exact c.proper hf_ne hshare hg
  have h_card : Fintype.card (G.incidenceSet v) ≤ Fintype.card (Fin k) :=
    Fintype.card_le_of_injective g hg_inj
  rw [SimpleGraph.card_incidenceSet_eq_degree, Fintype.card_fin] at h_card
  exact h_card

theorem maxDegree_le_of_edgeColorable {k : ℕ} (h : IsEdgeColorable G k) :
    G.maxDegree ≤ k := by
  obtain ⟨c⟩ := h
  dsimp [SimpleGraph.maxDegree]
  rw [WithBot.unbotD_le_iff (fun _ => Nat.zero_le k)]
  rw [Finset.max_le_iff]
  intro a ha
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ha
  exact WithBot.coe_le_coe.mpr (degree_le_of_edgeColoring G c v)

/-- Every vertex of degree $d$ has $d$ incident edges that pairwise share a vertex,
providing the trivial lower bound $\chi'(G) \ge \Delta(G)$. -/
theorem chromatic_index_ge_maxDegree [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G := by
  dsimp [chromaticIndex]
  have h_ne : {k : ℕ | IsEdgeColorable G k}.Nonempty := ⟨Fintype.card G.edgeSet, edgeColorable_card_edgeSet G⟩
  apply le_csInf h_ne
  intro k hk
  exact maxDegree_le_of_edgeColorable G hk

/-! ### Partial Edge Colorings and Kempe Chains -/

/-- A partial proper edge coloring of $G$ using $k$ colors. -/
structure PartialEdgeColoring (k : ℕ) where
  color : G.edgeSet → Option (Fin k)
  proper : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ →
    ∀ ⦃c : Fin k⦄, color e₁ = some c → color e₂ = some c → False

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

/-- The set of uncolored edges under partial coloring `c`. -/
def uncoloredEdges : Finset G.edgeSet :=
  Finset.univ.filter (fun e => c.color e = none)

/-- The empty partial edge coloring (no edges colored). -/
def empty : PartialEdgeColoring G k where
  color _ := none
  proper := by intro _ _ _ _ _ h; cases h

/-- The color assigned to adjacent vertices $u$ and $v$ (if colored). -/
def colorOf (u v : V) (h : G.Adj u v) : Option (Fin k) :=
  c.color ⟨s(u, v), h⟩

/-- The set of colors present on edges incident to $v$. -/
def usedColors (v : V) : Finset (Fin k) :=
  Finset.univ.filter (fun col => ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col)

/-- The set of colors missing at vertex $v$. -/
def missingColors (v : V) : Finset (Fin k) :=
  Finset.univ \ c.usedColors v

@[simp]
theorem mem_usedColors_iff (v : V) (col : Fin k) :
    col ∈ c.usedColors v ↔ ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col := by
  simp [usedColors]

@[simp]
theorem mem_missingColors_iff (v : V) (col : Fin k) :
    col ∈ c.missingColors v ↔ ∀ (w : V) (h : G.Adj v w), c.colorOf v w h ≠ some col := by
  simp [missingColors]

theorem card_usedColors_lt_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) :
    (c.usedColors u).card < k := by
  have h_choice : ∀ col ∈ c.usedColors u, ∃ w ∈ G.neighborFinset u, ∃ h' : G.Adj u w, c.colorOf u w h' = some col := by
    intro col hcol
    rw [mem_usedColors_iff] at hcol
    obtain ⟨w, h', heq⟩ := hcol
    exact ⟨w, (G.mem_neighborFinset u w).mpr h', h', heq⟩
  choose f hf_mem hf_adj hf_col using h_choice
  have h_inj : ∀ col₁ (h₁ : col₁ ∈ c.usedColors u) col₂ (h₂ : col₂ ∈ c.usedColors u),
      f col₁ h₁ = f col₂ h₂ → col₁ = col₂ := by
    intro col₁ h₁ col₂ h₂ heq
    have h1_col := hf_col col₁ h₁
    have h2_col := hf_col col₂ h₂
    dsimp [colorOf] at h1_col h2_col
    have h_adj1 : s(u, f col₁ h₁) ∈ G.edgeSet := hf_adj col₁ h₁
    have h_adj2 : s(u, f col₂ h₂) ∈ G.edgeSet := hf_adj col₂ h₂
    have : col₁ = col₂ := by
      have h_eq_pair : (⟨s(u, f col₁ h₁), h_adj1⟩ : G.edgeSet) = ⟨s(u, f col₂ h₂), h_adj2⟩ := by
        ext
        simp [heq]
      have h_same_col : (some col₁ : Option (Fin k)) = some col₂ := by
        rw [← h1_col, ← h2_col]
        congr 1
      exact Option.some.inj h_same_col
    exact this
  have h_ne_v : ∀ col (hcol : col ∈ c.usedColors u), f col hcol ≠ v := by
    intro col hcol heq
    have h_col := hf_col col hcol
    dsimp [colorOf] at h_col
    have h_adj_f : s(u, f col hcol) ∈ G.edgeSet := hf_adj col hcol
    have h_adj_v : s(u, v) ∈ G.edgeSet := h
    have heq_edge : (⟨s(u, f col hcol), h_adj_f⟩ : G.edgeSet) = ⟨s(u, v), h_adj_v⟩ := by
      ext; simp [heq]
    have : c.color ⟨s(u, v), h_adj_v⟩ = some col := by
      rw [← heq_edge, h_col]
    dsimp [colorOf] at h_none
    rw [h_none] at this
    cases this
  have h_img_sub : (c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol) ⊆ (G.neighborFinset u).erase v := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hw
    obtain ⟨col, hcol, rfl⟩ := hw
    rw [Finset.mem_erase]
    exact ⟨h_ne_v col hcol, hf_mem col hcol⟩
  have h_card_eq : ((c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol)).card = (c.usedColors u).card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ heq
      simp only [Subtype.mk.injEq]
      exact h_inj c₁ h₁ c₂ h₂ heq
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr h
  have h_erase_card : ((G.neighborFinset u).erase v).card = (G.neighborFinset u).card - 1 :=
    Finset.card_erase_of_mem hv_mem
  have h_sub_card := Finset.card_le_card h_img_sub
  rw [h_card_eq, h_erase_card, G.card_neighborFinset_eq_degree u] at h_sub_card
  have h_deg_le_max : G.degree u ≤ G.maxDegree := G.degree_le_maxDegree u
  have h_deg_pos : 0 < G.degree u := by
    rw [← G.card_neighborFinset_eq_degree u]
    exact Finset.card_pos.mpr ⟨v, hv_mem⟩
  omega

/-- An uncolored edge has at least one missing color at each endpoint when $k \ge \Delta(G)$. -/
theorem exists_missingColor_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) :
    (c.missingColors u).Nonempty := by
  have h_lt := card_usedColors_lt_of_uncolored c h h_none h_max
  by_contra h_empty
  rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
  have h_univ_card : (Finset.univ : Finset (Fin k)).card = k := Finset.card_fin k
  have h_sub : c.usedColors u ⊆ Finset.univ := Finset.subset_univ _
  have h_diff_card := Finset.card_sdiff (s := c.usedColors u) (t := Finset.univ)
  rw [Finset.inter_eq_left.mpr h_sub] at h_diff_card
  dsimp [missingColors] at h_empty
  rw [h_empty, Finset.card_empty, h_univ_card] at h_diff_card
  omega

/-- Swaps colors $\alpha$ and $\beta$ on an optional color value. -/
def swapColor (α β : Fin k) (c_opt : Option (Fin k)) : Option (Fin k) :=
  match c_opt with
  | some col =>
    if col = α then some β
    else if col = β then some α
    else some col
  | none => none

theorem swapColor_involutive (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β (swapColor α β c_opt) = c_opt := by
  dsimp [swapColor]
  cases c_opt with
  | none => rfl
  | some col =>
    dsimp
    split_ifs <;> aesop

lemma swapColor_some_left (α β : Fin k) : swapColor α β (some α) = some β := by
  simp [swapColor]

lemma swapColor_some_right (α β : Fin k) (hne : α ≠ β) : swapColor α β (some β) = some α := by
  simp [swapColor, hne.symm]

lemma swapColor_some_other (α β γ : Fin k) (h1 : γ ≠ α) (h2 : γ ≠ β) : swapColor α β (some γ) = some γ := by
  simp [swapColor, h1, h2]

lemma swapColor_eq_none_iff (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β c_opt = none ↔ c_opt = none := by
  cases c_opt with
  | none => rfl
  | some col =>
    dsimp [swapColor]
    split_ifs <;> simp

/-- Predicate asserting that an edge belongs to the connected component of $u$ in $H$. -/
def inComponent (H : SimpleGraph V) (u : V) (e : Sym2 V) : Prop :=
  ∀ x ∈ e, H.Reachable u x

/-- The $(\alpha, \beta)$-Kempe subgraph formed by edges colored $\alpha$ or $\beta$. -/
def kempeGraph (α β : Fin k) : SimpleGraph V where
  Adj x y := ∃ h : G.Adj x y, c.colorOf x y h = some α ∨ c.colorOf x y h = some β
  symm := ⟨by
    rintro x y ⟨h, hcol⟩
    have heq : (⟨s(y, x), h.symm⟩ : G.edgeSet) = ⟨s(x, y), h⟩ := Subtype.ext Sym2.eq_swap
    refine ⟨h.symm, ?_⟩
    dsimp [colorOf] at hcol ⊢
    rwa [heq]⟩
  loopless := ⟨by
    rintro x ⟨h, -⟩
    exact G.loopless.irrefl x h⟩

lemma kempeGraph_le (α β : Fin k) : c.kempeGraph α β ≤ G :=
  fun _ _ h => h.1

lemma kempe_color_eq_of_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hreach : (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      swapColor α β (c.color e) := by
  split_ifs with h_in
  · rfl
  · rcases e with ⟨e_val, he_prop⟩
    induction e_val using Sym2.inductionOn with
    | hf x y =>
      have hxy : v₀ = x ∨ v₀ = y := Sym2.mem_iff.mp hv₀
      have hadj : G.Adj x y := he_prop
      have h_not_reach : ¬ ((c.kempeGraph α β).Reachable u x ∧ (c.kempeGraph α β).Reachable u y) := by
        intro h_both
        apply h_in
        intro z hz
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact h_both.1
        · exact h_both.2
      have h_c_ne : c.color ⟨s(x, y), hadj⟩ ≠ some α ∧ c.color ⟨s(x, y), hadj⟩ ≠ some β := by
        constructor
        · intro hα
          have h_kempe_adj : (c.kempeGraph α β).Adj x y := ⟨hadj, Or.inl hα⟩
          apply h_not_reach
          rcases hxy with rfl | rfl
          · exact ⟨hreach, hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj)⟩
          · exact ⟨hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj.symm), hreach⟩
        · intro hβ
          have h_kempe_adj : (c.kempeGraph α β).Adj x y := ⟨hadj, Or.inr hβ⟩
          apply h_not_reach
          rcases hxy with rfl | rfl
          · exact ⟨hreach, hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj)⟩
          · exact ⟨hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj.symm), hreach⟩
      dsimp [swapColor]
      cases hc : c.color ⟨s(x, y), hadj⟩ with
      | none => rfl
      | some col =>
        dsimp
        split_ifs with h1 h2
        · exfalso; exact h_c_ne.1 (h1 ▸ hc)
        · exfalso; exact h_c_ne.2 (h2 ▸ hc)
        · rfl

lemma kempe_color_eq_of_not_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hnreach : ¬ (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      c.color e := by
  split_ifs with h_in
  · exfalso; exact hnreach (h_in v₀ hv₀)
  · rfl

/-- Kempe swap operation: interchange colors $\alpha$ and $\beta$ on the $(\alpha, \beta)$-Kempe
component connected to vertex $u$. -/
noncomputable def kempeSwap (α β : Fin k) (u : V) : PartialEdgeColoring G k where
  color e :=
    if inComponent (c.kempeGraph α β) u (e : Sym2 V) then
      swapColor α β (c.color e)
    else
      c.color e
  proper := by
    intro e₁ e₂ hne hshare col h1 h2
    obtain ⟨v₀, hv1, hv2⟩ := hshare
    by_cases hreach : (c.kempeGraph α β).Reachable u v₀
    · rw [kempe_color_eq_of_reachable c α β u e₁ v₀ hv1 hreach] at h1
      rw [kempe_color_eq_of_reachable c α β u e₂ v₀ hv2 hreach] at h2
      have h1' : swapColor α β (swapColor α β (c.color e₁)) = swapColor α β (some col) :=
        congr_arg (swapColor α β) h1
      have h2' : swapColor α β (swapColor α β (c.color e₂)) = swapColor α β (some col) :=
        congr_arg (swapColor α β) h2
      rw [swapColor_involutive] at h1' h2'
      cases h_sc : swapColor α β (some col) with
      | none =>
        dsimp [swapColor] at h_sc; split_ifs at h_sc
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
  split_ifs with h_in
  · rw [swapColor_eq_none_iff]
  · rfl

lemma kempeSwap_missing_u (α β : Fin k) (u : V) (hα : α ∈ c.missingColors u) :
    β ∈ (c.kempeSwap α β u).missingColors u := by
  rw [mem_missingColors_iff]
  intro w hw
  dsimp [colorOf, kempeSwap]
  have hreach_u : (c.kempeGraph α β).Reachable u u := SimpleGraph.Reachable.refl u
  rw [kempe_color_eq_of_reachable c α β u ⟨s(u, w), hw⟩ u (Sym2.mem_mk_left u w) hreach_u]
  intro heq
  have h_inv : swapColor α β (swapColor α β (c.color ⟨s(u, w), hw⟩)) = swapColor α β (some β) :=
    congr_arg (swapColor α β) heq
  rw [swapColor_involutive] at h_inv
  dsimp [swapColor] at h_inv
  split_ifs at h_inv with h1 h2
  · subst h1
    rw [mem_missingColors_iff] at hα
    exact hα w hw h_inv
  · rw [mem_missingColors_iff] at hα
    exact hα w hw h_inv
  · exfalso; exact h2 rfl

lemma kempeSwap_missing_v (α β : Fin k) (u v : V) (hnreach : ¬ (c.kempeGraph α β).Reachable u v)
    (hβ : β ∈ c.missingColors v) :
    β ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff]
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_not_reachable c α β u ⟨s(v, w), hw⟩ v (Sym2.mem_mk_left v w) hnreach]
  rw [mem_missingColors_iff] at hβ
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
  rw [mem_missingColors_iff]
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_reachable c α β u ⟨s(v, w), hw⟩ v (Sym2.mem_mk_left v w) hreach]
  intro heq
  have h_inv : swapColor α β (swapColor α β (c.color ⟨s(v, w), hw⟩)) = swapColor α β (some α) :=
    congr_arg (swapColor α β) heq
  rw [swapColor_involutive, swapColor_some_left] at h_inv
  rw [mem_missingColors_iff] at hβ
  exact hβ w hw h_inv

lemma kempeSwap_missing_of_ne (α β γ : Fin k) (u v : V) (h1 : γ ≠ α) (h2 : γ ≠ β)
    (hγ : γ ∈ c.missingColors v) :
    γ ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff] at hγ ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  split_ifs with h_in
  · intro heq
    have h_inv : swapColor α β (swapColor α β (c.color ⟨s(v, w), hw⟩)) = swapColor α β (some γ) :=
      congr_arg (swapColor α β) heq
    rw [swapColor_involutive, swapColor_some_other α β γ h1 h2] at h_inv
    exact hγ w hw h_inv
  · exact hγ w hw

lemma kempeSwap_colorOf_of_ne (α β γ : Fin k) (u v w : V) (hadj : G.Adj v w)
    (h1 : γ ≠ α) (h2 : γ ≠ β) (hc : c.colorOf v w hadj = some γ) :
    (c.kempeSwap α β u).colorOf v w hadj = some γ := by
  dsimp [colorOf, kempeSwap]
  split_ifs with h_in
  · dsimp [colorOf] at hc
    rw [hc, swapColor_some_other α β γ h1 h2]
  · exact hc

lemma kempeSwap_colorOf_alpha (α β : Fin k) (u w : V) (hadj : G.Adj u w) (hne : α ≠ β)
    (hc : c.colorOf u w hadj = some β) :
    (c.kempeSwap α β u).colorOf u w hadj = some α := by
  dsimp [colorOf, kempeSwap]
  have hreach_u : (c.kempeGraph α β).Reachable u u := SimpleGraph.Reachable.refl u
  rw [kempe_color_eq_of_reachable c α β u ⟨s(u, w), hadj⟩ u (Sym2.mem_mk_left u w) hreach_u]
  dsimp [colorOf] at hc
  rw [hc, swapColor_some_right α β hne]


/-- Helper returning the complementary color in $\{\alpha, \beta\}$. -/
def otherColor (α β col : Fin k) : Fin k :=
  if col = α then β else α

/-- Predicate asserting that a walk in the Kempe graph strictly alternates colors. -/
def IsAlternating (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h p, col =>
    c.colorOf _ _ h.1 = some col ∧
    IsAlternating α β p (otherColor α β col)

/-- Predicate asserting that the initial step of a walk has color `col`. -/
def FirstColor (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h _, col => c.colorOf _ _ h.1 = some col

lemma otherColor_involutive (α β col : Fin k) (hcol : col = α ∨ col = β) :
    otherColor α β (otherColor α β col) = col := by
  dsimp [otherColor]
  rcases hcol with rfl | rfl <;> split_ifs <;> aesop

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
      dsimp [otherColor]
      split_ifs with h1 <;> tauto
    apply ih (otherColor α β col) hp' h_next_mem
    cases p with
    | nil => dsimp [FirstColor]
    | @cons v₀' z w₁ h2 p' =>
      dsimp [FirstColor]
      have hadj2 := h2.2
      rcases hadj2 with hcolα | hcolβ
      · rcases hcol_mem with rfl | rfl
        · exfalso
          have h_nodup := hp.support_nodup
          simp only [Walk.support_cons, List.nodup_cons] at h_nodup
          have h_u0_ne_z : u₀ ≠ z := by
            intro heq
            subst heq
            exact h_nodup.1 (List.mem_cons_of_mem _ (p'.start_mem_support))
          have h_edge_ne : (⟨s(u₀, v₀), h.1⟩ : G.edgeSet) ≠ ⟨s(v₀, z), h2.1⟩ := by
            intro heq
            have : s(u₀, v₀) = s(v₀, z) := Subtype.ext_iff.mp heq
            rw [Sym2.eq_swap] at this
            rw [Sym2.eq_iff] at this
            rcases this with ⟨-, h_eq⟩ | ⟨-, h_eq⟩
            · exact h_u0_ne_z h_eq
            · exact h.1.ne h_eq
          have h_share : ShareVertex G ⟨s(u₀, v₀), h.1⟩ ⟨s(v₀, z), h2.1⟩ := by
            refine ⟨v₀, ?_, ?_⟩
            · exact Sym2.mem_mk_right _ _
            · exact Sym2.mem_mk_left _ _
          exact c.proper h_edge_ne h_share hc1 hcolα
        · dsimp [otherColor]
          split_ifs with h1
          · exfalso; exact hne h1.symm
          · exact hcolα
      · rcases hcol_mem with rfl | rfl
        · dsimp [otherColor]
          split_ifs with h1
          · exact hcolβ
          · exfalso; exact h1 rfl
        · exfalso
          have h_nodup := hp.support_nodup
          simp only [Walk.support_cons, List.nodup_cons] at h_nodup
          have h_u0_ne_z : u₀ ≠ z := by
            intro heq
            subst heq
            exact h_nodup.1 (List.mem_cons_of_mem _ (p'.start_mem_support))
          have h_edge_ne : (⟨s(u₀, v₀), h.1⟩ : G.edgeSet) ≠ ⟨s(v₀, z), h2.1⟩ := by
            intro heq
            have : s(u₀, v₀) = s(v₀, z) := Subtype.ext_iff.mp heq
            rw [Sym2.eq_swap] at this
            rw [Sym2.eq_iff] at this
            rcases this with ⟨-, h_eq⟩ | ⟨-, h_eq⟩
            · exact h_u0_ne_z h_eq
            · exact h.1.ne h_eq
          have h_share : ShareVertex G ⟨s(u₀, v₀), h.1⟩ ⟨s(v₀, z), h2.1⟩ := by
            refine ⟨v₀, ?_, ?_⟩
            · exact Sym2.mem_mk_right _ _
            · exact Sym2.mem_mk_left _ _
          exact c.proper h_edge_ne h_share hc1 hcolβ

lemma last_edge_alternating {α β : Fin k} :
    ∀ {x y : V} (p : (c.kempeGraph α β).Walk x y) (col : Fin k),
      c.IsAlternating α β p col → (col = α ∨ col = β) → p.length > 0 →
      ∃ (z : V) (h : G.Adj z y),
        c.colorOf z y h = some (if p.length % 2 = 1 then col else otherColor α β col) := by
  intro x y p
  induction p with
  | nil =>
    intro _ _ _ hlen
    exfalso; exact Nat.lt_irrefl 0 hlen
  | @cons u v w h p ih =>
    intro col halt hcol_mem _
    dsimp [IsAlternating] at halt
    have hc1 : c.colorOf u v h.1 = some col := halt.1
    have hp_alt : c.IsAlternating α β p (otherColor α β col) := halt.2
    have h_next_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      dsimp [otherColor]
      split_ifs <;> tauto
    cases p with
    | nil =>
      dsimp [Walk.length]
      refine ⟨u, h.1, ?_⟩
      dsimp [colorOf] at hc1 ⊢
      exact hc1
    | @cons v' z w' h2 p' =>
      have hlen_pos : (Walk.cons h2 p').length > 0 := by
        simp only [Walk.length_cons, Nat.succ_pos]
      obtain ⟨z_end, hz_adj, hz_col⟩ := ih (otherColor α β col) hp_alt h_next_mem hlen_pos
      refine ⟨z_end, hz_adj, ?_⟩
      have h_len_eq : (Walk.cons h (Walk.cons h2 p')).length = (Walk.cons h2 p').length + 1 := rfl
      rw [h_len_eq]
      have h_mod : ((Walk.cons h2 p').length + 1) % 2 = 1 - (Walk.cons h2 p').length % 2 := by
        omega
      have h_mod2 : (Walk.cons h2 p').length % 2 = 0 ∨ (Walk.cons h2 p').length % 2 = 1 := by
        omega
      rcases h_mod2 with h0 | h1
      · rw [h0] at hz_col
        rw [h0] at h_mod
        have : 1 - 0 = 1 := rfl
        rw [this] at h_mod
        rw [h_mod]
        dsimp at hz_col
        have h_inv := otherColor_involutive α β col hcol_mem
        dsimp
        rwa [h_inv] at hz_col
      · rw [h1] at hz_col
        rw [h1] at h_mod
        have : 1 - 1 = 0 := rfl
        rw [this] at h_mod
        rw [h_mod]
        dsimp at hz_col
        dsimp
        exact hz_col

lemma kempe_adj_unique_left (α β : Fin k) (col : Fin k) (x y z : V)
    (hxy : (c.kempeGraph α β).Adj x y) (hxz : (c.kempeGraph α β).Adj x z)
    (h_col_xy : c.colorOf x y hxy.1 = some col)
    (h_col_xz : c.colorOf x z hxz.1 = some col) :
    y = z := by
  by_contra hne
  have h_edge_ne : (⟨s(x, y), hxy.1⟩ : G.edgeSet) ≠ ⟨s(x, z), hxz.1⟩ := by
    intro heq
    have : s(x, y) = s(x, z) := Subtype.ext_iff.mp heq
    rw [Sym2.eq_iff] at this
    rcases this with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · exact hxy.1.ne rfl
  have h_share : ShareVertex G ⟨s(x, y), hxy.1⟩ ⟨s(x, z), hxz.1⟩ := by
    exact ⟨x, Sym2.mem_mk_left x y, Sym2.mem_mk_left x z⟩
  exact c.proper h_edge_ne h_share h_col_xy h_col_xz

lemma alternating_walk_eq {α β : Fin k} :
    ∀ {x y₁ y₂ : V} (p₁ : (c.kempeGraph α β).Walk x y₁) (p₂ : (c.kempeGraph α β).Walk x y₂) (col : Fin k),
      (col = α ∨ col = β) →
      c.IsAlternating α β p₁ col → c.IsAlternating α β p₂ col →
      (∀ w (h : G.Adj y₁ w), c.colorOf y₁ w h ≠ some (if p₁.length % 2 = 1 then otherColor α β col else col)) →
      (∀ w (h : G.Adj y₂ w), c.colorOf y₂ w h ≠ some (if p₂.length % 2 = 1 then otherColor α β col else col)) →
      y₁ = y₂ := by
  intro x y₁ y₂ p₁
  induction p₁ with
  | nil =>
    intro p₂ col hcol halt1 halt2 hend1 hend2
    cases p₂ with
    | nil => rfl
    | cons h p₂' =>
      dsimp [Walk.length] at hend1
      dsimp [IsAlternating] at halt2
      have hcol_edge : c.colorOf _ _ h.1 = some col := halt2.1
      exfalso
      exact hend1 _ h.1 hcol_edge
  | @cons x₀ w₀ y₁' h₁ p₁' ih =>
    intro p₂ col hcol halt1 halt2 hend1 hend2
    cases p₂ with
    | nil =>
      dsimp [Walk.length] at hend2
      dsimp [IsAlternating] at halt1
      have hcol_edge : c.colorOf _ _ h₁.1 = some col := halt1.1
      exfalso
      exact hend2 _ h₁.1 hcol_edge
    | @cons _ w₁ y₂' h₂ p₂' =>
      dsimp [IsAlternating] at halt1 halt2
      have hc1 : c.colorOf x₀ w₀ h₁.1 = some col := halt1.1
      have hc2 : c.colorOf x₀ w₁ h₂.1 = some col := halt2.1
      have hw_eq : w₀ = w₁ := c.kempe_adj_unique_left α β col x₀ w₀ w₁ h₁ h₂ hc1 hc2
      subst hw_eq
      have halt1' : c.IsAlternating α β p₁' (otherColor α β col) := halt1.2
      have halt2' : c.IsAlternating α β p₂' (otherColor α β col) := halt2.2
      have h_other_mem : otherColor α β col = α ∨ otherColor α β col = β := by
        dsimp [otherColor]; split_ifs <;> tauto
      have h_inv := otherColor_involutive α β col hcol
      apply ih p₂' (otherColor α β col) h_other_mem halt1' halt2'
      · intro w hw
        have h_len1 : (Walk.cons h₁ p₁').length = p₁'.length + 1 := rfl
        rw [h_len1] at hend1
        have hmod_cases : p₁'.length % 2 = 0 ∨ p₁'.length % 2 = 1 := by omega
        rcases hmod_cases with h0 | h1
        · have : (p₁'.length + 1) % 2 = 1 := by omega
          rw [this] at hend1
          rw [h0]
          dsimp at hend1 ⊢
          exact hend1 w hw
        · have : (p₁'.length + 1) % 2 = 0 := by omega
          rw [this] at hend1
          rw [h1]
          dsimp at hend1 ⊢
          rw [h_inv]
          exact hend1 w hw
      · intro w hw
        have h_len2 : (Walk.cons h₂ p₂').length = p₂'.length + 1 := rfl
        rw [h_len2] at hend2
        have hmod_cases : p₂'.length % 2 = 0 ∨ p₂'.length % 2 = 1 := by omega
        rcases hmod_cases with h0 | h1
        · have : (p₂'.length + 1) % 2 = 1 := by omega
          rw [this] at hend2
          rw [h0]
          dsimp at hend2 ⊢
          exact hend2 w hw
        · have : (p₂'.length + 1) % 2 = 0 := by omega
          rw [this] at hend2
          rw [h1]
          dsimp at hend2 ⊢
          rw [h_inv]
          exact hend2 w hw

/--
Two distinct vertices missing the same color $\beta$ cannot both be reachable
from a vertex $u$ missing color $\alpha$ in the $(\alpha, \beta)$ Kempe graph.
-/
theorem kempe_not_reachable_both {u v₁ v₂ : V} {α β : Fin k} (hne : α ≠ β)
    (hα : α ∈ c.missingColors u) (hv1 : β ∈ c.missingColors v₁) (hv2 : β ∈ c.missingColors v₂)
    (hne_v : v₁ ≠ v₂) :
    ¬ ((c.kempeGraph α β).Reachable u v₁ ∧ (c.kempeGraph α β).Reachable u v₂) := by
  rintro ⟨hreach1, hreach2⟩
  obtain ⟨p₁, hp1_path⟩ := hreach1.exists_isPath
  obtain ⟨p₂, hp2_path⟩ := hreach2.exists_isPath
  have h_first1 : c.FirstColor α β p₁ β := by
    cases p₁ with
    | nil => dsimp [FirstColor]
    | cons h p' =>
      dsimp [FirstColor]
      rcases h.2 with hcolα | hcolβ
      · rw [mem_missingColors_iff] at hα
        exact (hα _ h.1 hcolα).elim
      · exact hcolβ
  have h_first2 : c.FirstColor α β p₂ β := by
    cases p₂ with
    | nil => dsimp [FirstColor]
    | cons h p' =>
      dsimp [FirstColor]
      rcases h.2 with hcolα | hcolβ
      · rw [mem_missingColors_iff] at hα
        exact (hα _ h.1 hcolα).elim
      · exact hcolβ
  have h_alt1 : c.IsAlternating α β p₁ β :=
    isAlternating_of_isPath c hne p₁ β hp1_path (Or.inr rfl) h_first1
  have h_alt2 : c.IsAlternating α β p₂ β :=
    isAlternating_of_isPath c hne p₂ β hp2_path (Or.inr rfl) h_first2
  have hp1_len_even : p₁.length % 2 = 0 := by
    by_contra h_odd
    have h1 : p₁.length % 2 = 1 := by omega
    have hlen_pos : p₁.length > 0 := by omega
    obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p₁ β h_alt1 (Or.inr rfl) hlen_pos
    rw [h1] at hz_col
    dsimp at hz_col
    rw [mem_missingColors_iff] at hv1
    have heq : (⟨s(v₁, z), hz_adj.symm⟩ : G.edgeSet) = ⟨s(z, v₁), hz_adj⟩ := Subtype.ext Sym2.eq_swap
    have hc : c.colorOf v₁ z hz_adj.symm = some β := by
      dsimp [colorOf]; rwa [heq]
    exact hv1 z hz_adj.symm hc
  have hp2_len_even : p₂.length % 2 = 0 := by
    by_contra h_odd
    have h1 : p₂.length % 2 = 1 := by omega
    have hlen_pos : p₂.length > 0 := by omega
    obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p₂ β h_alt2 (Or.inr rfl) hlen_pos
    rw [h1] at hz_col
    dsimp at hz_col
    rw [mem_missingColors_iff] at hv2
    have heq : (⟨s(v₂, z), hz_adj.symm⟩ : G.edgeSet) = ⟨s(z, v₂), hz_adj⟩ := Subtype.ext Sym2.eq_swap
    have hc : c.colorOf v₂ z hz_adj.symm = some β := by
      dsimp [colorOf]; rwa [heq]
    exact hv2 z hz_adj.symm hc
  have hend1 : ∀ w (h : G.Adj v₁ w), c.colorOf v₁ w h ≠ some (if p₁.length % 2 = 1 then otherColor α β β else β) := by
    intro w hw
    rw [hp1_len_even]
    dsimp
    rw [mem_missingColors_iff] at hv1
    exact hv1 w hw
  have hend2 : ∀ w (h : G.Adj v₂ w), c.colorOf v₂ w h ≠ some (if p₂.length % 2 = 1 then otherColor α β β else β) := by
    intro w hw
    rw [hp2_len_even]
    dsimp
    rw [mem_missingColors_iff] at hv2
    exact hv2 w hw
  have heq_v1_v2 := alternating_walk_eq c p₁ p₂ β (Or.inr rfl) h_alt1 h_alt2 hend1 hend2
  exact hne_v heq_v1_v2

theorem card_usedColors_le_degree (u : V) : (c.usedColors u).card ≤ G.degree u := by
  have h_choice : ∀ col ∈ c.usedColors u, ∃ w ∈ G.neighborFinset u, ∃ h' : G.Adj u w, c.colorOf u w h' = some col := by
    intro col hcol
    rw [mem_usedColors_iff] at hcol
    obtain ⟨w, h', heq⟩ := hcol
    exact ⟨w, (G.mem_neighborFinset u w).mpr h', h', heq⟩
  choose f hf_mem hf_adj hf_col using h_choice
  have h_inj : ∀ col₁ (h₁ : col₁ ∈ c.usedColors u) col₂ (h₂ : col₂ ∈ c.usedColors u),
      f col₁ h₁ = f col₂ h₂ → col₁ = col₂ := by
    intro col₁ h₁ col₂ h₂ heq
    have h1_col := hf_col col₁ h₁
    have h2_col := hf_col col₂ h₂
    dsimp [colorOf] at h1_col h2_col
    have h_adj1 : s(u, f col₁ h₁) ∈ G.edgeSet := hf_adj col₁ h₁
    have h_adj2 : s(u, f col₂ h₂) ∈ G.edgeSet := hf_adj col₂ h₂
    have : col₁ = col₂ := by
      have h_eq_pair : (⟨s(u, f col₁ h₁), h_adj1⟩ : G.edgeSet) = ⟨s(u, f col₂ h₂), h_adj2⟩ := by
        ext; simp [heq]
      have h_same_col : (some col₁ : Option (Fin k)) = some col₂ := by
        rw [← h1_col, ← h2_col]
        congr 1
      exact Option.some.inj h_same_col
    exact this
  have h_img_sub : (c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol) ⊆ G.neighborFinset u := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hw
    obtain ⟨col, hcol, rfl⟩ := hw
    exact hf_mem col hcol
  have h_card_eq : ((c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol)).card = (c.usedColors u).card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ heq
      simp only [Subtype.mk.injEq]
      exact h_inj c₁ h₁ c₂ h₂ heq
  have h_sub_card := Finset.card_le_card h_img_sub
  rw [h_card_eq, G.card_neighborFinset_eq_degree u] at h_sub_card
  exact h_sub_card

theorem exists_missingColor_of_maxDegree_lt {u : V} (h_max : G.maxDegree < k) :
    (c.missingColors u).Nonempty := by
  have h_deg := c.card_usedColors_le_degree u
  have h_deg_le_max : G.degree u ≤ G.maxDegree := G.degree_le_maxDegree u
  have h_used_lt : (c.usedColors u).card < k := by omega
  by_contra h_empty
  rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
  have h_univ_card : (Finset.univ : Finset (Fin k)).card = k := Finset.card_fin k
  have h_sub : c.usedColors u ⊆ Finset.univ := Finset.subset_univ _
  have h_diff_card := Finset.card_sdiff (s := c.usedColors u) (t := Finset.univ)
  rw [Finset.inter_eq_left.mpr h_sub] at h_diff_card
  dsimp [missingColors] at h_empty
  rw [h_empty, Finset.card_empty, h_univ_card] at h_diff_card
  omega

theorem card_usedColors_le_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none) :
    (c.usedColors u).card ≤ G.maxDegree - 1 := by
  have h_choice : ∀ col ∈ c.usedColors u, ∃ w ∈ G.neighborFinset u, ∃ h' : G.Adj u w, c.colorOf u w h' = some col := by
    intro col hcol
    rw [mem_usedColors_iff] at hcol
    obtain ⟨w, h', heq⟩ := hcol
    exact ⟨w, (G.mem_neighborFinset u w).mpr h', h', heq⟩
  choose f hf_mem hf_adj hf_col using h_choice
  have h_inj : ∀ col₁ (h₁ : col₁ ∈ c.usedColors u) col₂ (h₂ : col₂ ∈ c.usedColors u),
      f col₁ h₁ = f col₂ h₂ → col₁ = col₂ := by
    intro col₁ h₁ col₂ h₂ heq
    have h1_col := hf_col col₁ h₁
    have h2_col := hf_col col₂ h₂
    dsimp [colorOf] at h1_col h2_col
    have h_adj1 : s(u, f col₁ h₁) ∈ G.edgeSet := hf_adj col₁ h₁
    have h_adj2 : s(u, f col₂ h₂) ∈ G.edgeSet := hf_adj col₂ h₂
    have : col₁ = col₂ := by
      have h_eq_pair : (⟨s(u, f col₁ h₁), h_adj1⟩ : G.edgeSet) = ⟨s(u, f col₂ h₂), h_adj2⟩ := by
        ext; simp [heq]
      have h_same_col : (some col₁ : Option (Fin k)) = some col₂ := by
        rw [← h1_col, ← h2_col]
        congr 1
      exact Option.some.inj h_same_col
    exact this
  have h_ne_v : ∀ col (hcol : col ∈ c.usedColors u), f col hcol ≠ v := by
    intro col hcol heq
    have h_col := hf_col col hcol
    dsimp [colorOf] at h_col
    have h_adj_f : s(u, f col hcol) ∈ G.edgeSet := hf_adj col hcol
    have h_adj_v : s(u, v) ∈ G.edgeSet := h
    have heq_edge : (⟨s(u, f col hcol), h_adj_f⟩ : G.edgeSet) = ⟨s(u, v), h_adj_v⟩ := by
      ext; simp [heq]
    have : c.color ⟨s(u, v), h_adj_v⟩ = some col := by
      rw [← heq_edge, h_col]
    dsimp [colorOf] at h_none
    rw [h_none] at this
    cases this
  have h_img_sub : (c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol) ⊆ (G.neighborFinset u).erase v := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hw
    obtain ⟨col, hcol, rfl⟩ := hw
    rw [Finset.mem_erase]
    exact ⟨h_ne_v col hcol, hf_mem col hcol⟩
  have h_card_eq : ((c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol)).card = (c.usedColors u).card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ heq
      simp only [Subtype.mk.injEq]
      exact h_inj c₁ h₁ c₂ h₂ heq
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr h
  have h_erase_card : ((G.neighborFinset u).erase v).card = (G.neighborFinset u).card - 1 :=
    Finset.card_erase_of_mem hv_mem
  have h_sub_card := Finset.card_le_card h_img_sub
  rw [h_card_eq, h_erase_card, G.card_neighborFinset_eq_degree u] at h_sub_card
  have h_deg_le_max : G.degree u ≤ G.maxDegree := G.degree_le_maxDegree u
  omega

theorem card_missingColors_ge_two_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree < k) :
    2 ≤ (c.missingColors u).card := by
  have h_used := card_usedColors_le_of_uncolored c h h_none
  have h_sub : c.usedColors u ⊆ Finset.univ := Finset.subset_univ _
  have h_card_sdiff := Finset.card_sdiff (s := c.usedColors u) (t := Finset.univ)
  rw [Finset.inter_eq_left.mpr h_sub] at h_card_sdiff
  dsimp [missingColors]
  have h_univ : (Finset.univ : Finset (Fin k)).card = k := Finset.card_fin k
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr h
  have h_deg_pos : 0 < G.degree u := Finset.card_pos.mpr ⟨v, hv_mem⟩
  have h_max_pos : 1 ≤ G.maxDegree := by
    have := G.degree_le_maxDegree u
    omega
  omega

lemma exists_ne_of_card_ge_two {α : Type*} [DecidableEq α] {s : Finset α} (h : 2 ≤ s.card) (a : α) :
    ∃ b ∈ s, b ≠ a := by
  have h_erase : 1 ≤ (s.erase a).card := by
    by_cases ha : a ∈ s
    · rw [Finset.card_erase_of_mem ha]
      omega
    · rw [Finset.erase_eq_of_notMem ha]
      omega
  have h_ne : (s.erase a).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb⟩ := h_ne
  rw [Finset.mem_erase] at hb
  exact ⟨b, hb.2, hb.1⟩

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
      intro heq
      have hc : c.color ⟨s(u, v), huv⟩ = some col := by
        rw [heq]
        exact h_col
      rw [mem_missingColors_iff] at h_miss
      exact h_miss u huv.symm (by
        dsimp [colorOf]
        have hswap : (⟨s(v, u), huv.symm⟩ : G.edgeSet) = ⟨s(u, v), huv⟩ := Subtype.ext Sym2.eq_swap
        rwa [hswap])
    by_cases he1_v : e₁ = ⟨s(u, v), huv⟩
    · subst he1_v
      have hc' : some col = some c' := by simpa using h1
      have heq_c' : c' = col := (Option.some.inj hc').symm
      have he2_v : e₂ ≠ ⟨s(u, v), huv⟩ := hne.symm
      have he2_w : e₂ ≠ ⟨s(u, w), huw⟩ := by
        intro heq; subst heq
        simp [he_vw.symm] at h2
      have h2_orig : c.color e₂ = some col := by
        have : c.color e₂ = some c' := by simpa [he2_v, he2_w] using h2
        rwa [heq_c'] at this
      obtain ⟨z, hz_adj, rfl⟩ := edge_eq_of_mem G e₂ v₀ hv2
      have hv1_cases : v₀ = u ∨ v₀ = v := Sym2.mem_iff.mp hv1
      rcases hv1_cases with rfl | rfl
      · apply c.proper (e₁ := ⟨s(v₀, w), huw⟩) (e₂ := ⟨s(v₀, z), hz_adj⟩)
        · exact he2_w.symm
        · exact ⟨v₀, Sym2.mem_mk_left v₀ w, Sym2.mem_mk_left v₀ z⟩
        · exact h_col
        · exact h2_orig
      · rw [mem_missingColors_iff] at h_miss
        exact h_miss z hz_adj h2_orig
    · by_cases he2_v : e₂ = ⟨s(u, v), huv⟩
      · subst he2_v
        have hc' : some col = some c' := by simpa using h2
        have heq_c' : c' = col := (Option.some.inj hc').symm
        have he1_w : e₁ ≠ ⟨s(u, w), huw⟩ := by
          intro heq; subst heq
          simp [he_vw.symm] at h1
        have h1_orig : c.color e₁ = some col := by
          have : c.color e₁ = some c' := by simpa [he1_v, he1_w] using h1
          rwa [heq_c'] at this
        obtain ⟨z, hz_adj, rfl⟩ := edge_eq_of_mem G e₁ v₀ hv1
        have hv2_cases : v₀ = u ∨ v₀ = v := Sym2.mem_iff.mp hv2
        rcases hv2_cases with rfl | rfl
        · apply c.proper (e₁ := ⟨s(v₀, z), hz_adj⟩) (e₂ := ⟨s(v₀, w), huw⟩)
          · exact he1_w
          · exact ⟨v₀, Sym2.mem_mk_left v₀ z, Sym2.mem_mk_left v₀ w⟩
          · exact h1_orig
          · exact h_col
        · rw [mem_missingColors_iff] at h_miss
          exact h_miss z hz_adj h1_orig
      · by_cases he1_w : e₁ = ⟨s(u, w), huw⟩
        · subst he1_w
          simp [he1_v] at h1
        · by_cases he2_w : e₂ = ⟨s(u, w), huw⟩
          · subst he2_w
            simp [he2_v] at h2
          · have h1_orig : c.color e₁ = some c' := by simpa [he1_v, he1_w] using h1
            have h2_orig : c.color e₂ = some c' := by simpa [he2_v, he2_w] using h2
            exact c.proper hne ⟨v₀, hv1, hv2⟩ h1_orig h2_orig

lemma card_uncoloredEdges_shiftStep [Fintype G.edgeSet] (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (h_none : c.colorOf u v huv = none) :
    (c.shiftStep u v w huv huw col h_col h_miss).uncoloredEdges.card = c.uncoloredEdges.card := by
  have he_vw : (⟨s(u, v), huv⟩ : G.edgeSet) ≠ ⟨s(u, w), huw⟩ := by
    intro heq
    have hc : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq]; exact h_col
    dsimp [colorOf] at h_none
    rw [h_none] at hc; cases hc
  have he_v_mem : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
    simp [uncoloredEdges, colorOf] at h_none ⊢; exact h_none
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
  rw [heq_set]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_erase_of_mem he_v_mem]
    have hpos : 0 < c.uncoloredEdges.card := Finset.card_pos.mpr ⟨⟨s(u, v), huv⟩, he_v_mem⟩
    omega
  · simp [he_vw.symm, he_w_not_mem]

lemma shiftStep_colorOf_none (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) :
    (c.shiftStep u v w huv huw col h_col h_miss).colorOf u w huw = none := by
  dsimp [colorOf, shiftStep]
  have he_vw : (⟨s(u, w), huw⟩ : G.edgeSet) ≠ ⟨s(u, v), huv⟩ := by
    intro heq
    have hc : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq.symm]; exact h_col
    rw [mem_missingColors_iff] at h_miss
    exact h_miss u huv.symm (by
      dsimp [colorOf]
      have hswap : (⟨s(v, u), huv.symm⟩ : G.edgeSet) = ⟨s(u, v), huv⟩ := Subtype.ext Sym2.eq_swap
      rwa [hswap])
  split_ifs with he1 he2
  · exfalso; exact he_vw he1
  · rfl
  · exfalso; exact he2 rfl

lemma shiftStep_missing_u (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (α : Fin k) (hα : α ∈ c.missingColors u) :
    α ∈ (c.shiftStep u v w huv huw col h_col h_miss).missingColors u := by
  rw [mem_missingColors_iff] at hα ⊢
  intro z hz
  dsimp [colorOf, shiftStep]
  split_ifs with he1 he2
  · intro heq
    have hc_eq : col = α := Option.some.inj heq
    subst hc_eq
    exact hα w huw h_col
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
  dsimp [colorOf, shiftStep]
  simp [h_ne1, h_ne2]


lemma kempeSwap_color_none (α β : Fin k) (u : V) (e : G.edgeSet) (h : c.color e = none) :
    (c.kempeSwap α β u).color e = none := by
  dsimp [kempeSwap]
  split_ifs with h_in
  · dsimp [swapColor]; rw [h]
  · exact h

lemma bipartite_walk_length (b : V → Fin 2) (hb : ∀ x y, G.Adj x y → b x ≠ b y)
    (H : SimpleGraph V) (hH : H ≤ G) :
    ∀ {x y : V} (p : H.Walk x y), (b y).val = ((b x).val + p.length) % 2 := by
  intro x y p
  induction p with
  | nil =>
    dsimp [Walk.length]
    have : (b x).val < 2 := (b x).isLt
    omega
  | @cons u v w h p ih =>
    have hadj_G : G.Adj u v := hH h
    have h_ne : b u ≠ b v := hb u v hadj_G
    have hu_val : (b u).val < 2 := (b u).isLt
    have hv_val : (b v).val < 2 := (b v).isLt
    have hb_cases : ((b u).val = 0 ∧ (b v).val = 1) ∨ ((b u).val = 1 ∧ (b v).val = 0) := by
      revert h_ne hu_val hv_val
      have hu_cases : (b u).val = 0 ∨ (b u).val = 1 := by omega
      have hv_cases : (b v).val = 0 ∨ (b v).val = 1 := by omega
      intro h_ne hu_val hv_val
      rcases hu_cases with hu0 | hu1 <;> rcases hv_cases with hv0 | hv1
      · exfalso; apply h_ne; ext; rw [hu0, hv0]
      · left; exact ⟨hu0, hv1⟩
      · right; exact ⟨hu1, hv0⟩
      · exfalso; apply h_ne; ext; rw [hu1, hv1]
    rw [Walk.length_cons]
    rw [ih]
    rcases hb_cases with ⟨hu0, hv1⟩ | ⟨hu1, hv0⟩
    · rw [hv1, hu0]
      omega
    · rw [hv0, hu1]
      omega

/--
In any bipartite graph ($G.\text{Colorable } 2$), if $u v$ is an uncolored edge, no alternating
$(\alpha, \beta)$ path in the Kempe subgraph can connect $u$ and $v$.
-/
theorem kempe_not_reachable_bipartite (h_bip : G.Colorable 2) {u v : V} (hadj : G.Adj u v)
    {α β : Fin k} (hne : α ≠ β) (hα : α ∈ c.missingColors u) (hβ : β ∈ c.missingColors v) :
    ¬ (c.kempeGraph α β).Reachable u v := by
  intro hreach
  obtain ⟨bicol⟩ := h_bip
  have hb_adj : ∀ x y, G.Adj x y → bicol x ≠ bicol y := fun x y h => bicol.valid h
  let b : V → Fin 2 := fun x => if bicol x = bicol u then 0 else 1
  have hb : ∀ x y, G.Adj x y → b x ≠ b y := by
    intro x y hxy
    dsimp [b]
    have h_ne := hb_adj x y hxy
    split_ifs with h1 h2
    · exfalso; exact h_ne (h1.trans h2.symm)
    · decide
    · decide
    · exfalso
      have hu_cases : bicol u = 0 ∨ bicol u = 1 := by
        cases bicol u using Fin.cases with | zero => left; rfl | succ i => cases i using Fin.cases with | zero => right; rfl | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim
      have hx_cases : bicol x = 0 ∨ bicol x = 1 := by
        cases bicol x using Fin.cases with | zero => left; rfl | succ i => cases i using Fin.cases with | zero => right; rfl | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim
      have hy_cases : bicol y = 0 ∨ bicol y = 1 := by
        cases bicol y using Fin.cases with | zero => left; rfl | succ i => cases i using Fin.cases with | zero => right; rfl | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim
      rcases hu_cases with hu0 | hu1 <;>
      rcases hx_cases with hx0 | hx1 <;>
      rcases hy_cases with hy0 | hy1
      all_goals solve | contradiction | aesop
  have hbu : b u = 0 := by
    dsimp [b]; split_ifs with h; rfl; exfalso; exact h rfl
  have hbv : b v = 1 := by
    dsimp [b]; split_ifs with h1
    · exfalso; exact (hb_adj u v hadj) h1.symm
    · rfl
  obtain ⟨p, hp_path⟩ := hreach.exists_isPath
  have h_first : c.FirstColor α β p β := by
    cases p with
    | nil => dsimp [FirstColor]
    | cons h p' =>
      dsimp [FirstColor]
      rcases h.2 with hcolα | hcolβ
      · rw [mem_missingColors_iff] at hα
        exact (hα _ h.1 hcolα).elim
      · exact hcolβ
  have h_alt : c.IsAlternating α β p β :=
    isAlternating_of_isPath c hne p β hp_path (Or.inr rfl) h_first
  have h_len_eq := bipartite_walk_length b hb (c.kempeGraph α β) (c.kempeGraph_le α β) p
  have hbu_val : (b u).val = 0 := congr_arg Fin.val hbu
  have hbv_val : (b v).val = 1 := congr_arg Fin.val hbv
  rw [hbu_val, hbv_val] at h_len_eq
  have h_mod : p.length % 2 = 1 := by
    omega
  have h_len_pos : p.length > 0 := by
    omega
  obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p β h_alt (Or.inr rfl) h_len_pos
  rw [h_mod] at hz_col
  dsimp at hz_col
  rw [mem_missingColors_iff] at hβ
  exact hβ z hz_adj.symm (by
    dsimp [colorOf] at hz_col ⊢
    have heq : (⟨s(v, z), hz_adj.symm⟩ : G.edgeSet) = ⟨s(z, v), hz_adj⟩ := Subtype.ext Sym2.eq_swap
    rwa [heq])

/-- Extends a partial edge coloring by coloring uncolored edge $u v$ with a common missing color. -/
def extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) : PartialEdgeColoring G k where
  color e :=
    if e = ⟨s(u, v), hadj⟩ then
      some col
    else
      c.color e
  proper := by
    intro e₁ e₂ hne hshare c' h1 h2
    obtain ⟨v₀, hv1, hv2⟩ := hshare
    by_cases he1 : e₁ = ⟨s(u, v), hadj⟩ <;> by_cases he2 : e₂ = ⟨s(u, v), hadj⟩
    · subst he1; subst he2; exact hne rfl
    · subst he1
      have hc' : some col = some c' := by simpa using h1
      have heq_c' : c' = col := (Option.some.inj hc').symm
      have h2_orig : c.color e₂ = some col := by
        have : c.color e₂ = some c' := by simpa [he2] using h2
        rwa [heq_c'] at this
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₂ v₀ hv2
      rcases Sym2.mem_iff.mp hv1 with rfl | rfl
      · rw [mem_missingColors_iff] at hu
        exact hu w hw_adj h2_orig
      · rw [mem_missingColors_iff] at hv
        exact hv w hw_adj h2_orig
    · subst he2
      have hc' : some col = some c' := by simpa using h2
      have heq_c' : c' = col := (Option.some.inj hc').symm
      have h1_orig : c.color e₁ = some col := by
        have : c.color e₁ = some c' := by simpa [he1] using h1
        rwa [heq_c'] at this
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₁ v₀ hv1
      rcases Sym2.mem_iff.mp hv2 with rfl | rfl
      · rw [mem_missingColors_iff] at hu
        exact hu w hw_adj h1_orig
      · rw [mem_missingColors_iff] at hv
        exact hv w hw_adj h1_orig
    · have h1_orig : c.color e₁ = some c' := by
        simpa [he1] using h1
      have h2_orig : c.color e₂ = some c' := by
        simpa [he2] using h2
      exact c.proper hne ⟨v₀, hv1, hv2⟩ h1_orig h2_orig

lemma uncoloredEdges_extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) :
    (c.extendColor u v hadj col hu hv).uncoloredEdges = c.uncoloredEdges.erase ⟨s(u, v), hadj⟩ := by
  ext e
  simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  dsimp [extendColor]
  split_ifs with heq
  · simp [heq]
  · constructor
    · intro h
      exact ⟨heq, h⟩
    · intro ⟨_, h⟩
      exact h

/-- Any non-empty partial edge coloring on a bipartite graph can be extended to strictly fewer uncolored edges. -/
theorem exists_extended_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (hne : c.uncoloredEdges.Nonempty) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  obtain ⟨e, he⟩ := hne
  rcases e with ⟨e_val, he_prop⟩
  induction e_val using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := he_prop
    have he_none : c.colorOf u v hadj = none := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact he
    have he_mem_uncolored : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact he_none
    obtain ⟨α, hα⟩ := exists_missingColor_of_uncolored c hadj he_none h_max
    obtain ⟨β, hβ⟩ := exists_missingColor_of_uncolored c hadj.symm (by
      dsimp [colorOf] at he_none ⊢
      have heq : (⟨s(v, u), hadj.symm⟩ : G.edgeSet) = ⟨s(u, v), hadj⟩ := Subtype.ext Sym2.eq_swap
      rwa [heq]) h_max
    by_cases hab : α = β
    · subst hab
      let c' := c.extendColor u v hadj α hα hβ
      refine ⟨c', ?_⟩
      have heq_uncolored := uncoloredEdges_extendColor c u v hadj α hα hβ
      rw [heq_uncolored, Finset.card_erase_of_mem he_mem_uncolored]
      exact Nat.pred_lt (Finset.card_pos.mpr ⟨⟨s(u, v), hadj⟩, he_mem_uncolored⟩).ne'
    · have hnreach := kempe_not_reachable_bipartite c h_bip hadj hab hα hβ
      let c_swap := c.kempeSwap α β u
      have hβ_u : β ∈ c_swap.missingColors u := kempeSwap_missing_u c α β u hα
      have hβ_v : β ∈ c_swap.missingColors v := kempeSwap_missing_v c α β u v hnreach hβ
      have h_none_swap : c_swap.color ⟨s(u, v), hadj⟩ = none :=
        kempeSwap_colorOf_none c α β u v hadj hnreach he_none
      let c' := c_swap.extendColor u v hadj β hβ_u hβ_v
      refine ⟨c', ?_⟩
      have heq_uncolored := uncoloredEdges_extendColor c_swap u v hadj β hβ_u hβ_v
      rw [heq_uncolored]
      have he_swap_mem : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ c_swap.uncoloredEdges := by
        simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_none_swap
      rw [Finset.card_erase_of_mem he_swap_mem, uncoloredEdges_kempeSwap]
      exact Nat.pred_lt (Finset.card_pos.mpr ⟨⟨s(u, v), hadj⟩, he_mem_uncolored⟩).ne'

/-- By well-founded induction on uncolored edges, a bipartite graph admits a complete proper edge coloring. -/
theorem exists_full_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (c : PartialEdgeColoring G k) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
  have h_wf : ∀ n, ∀ c : PartialEdgeColoring G k, c.uncoloredEdges.card = n → ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      by_cases hemp : c.uncoloredEdges = ∅
      · exact ⟨c, hemp⟩
      · have hne : c.uncoloredEdges.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        obtain ⟨c', h_lt⟩ := c.exists_extended_coloring h_max h_bip hne
        rw [hc] at h_lt
        obtain ⟨c_full, hc_full⟩ := ih c'.uncoloredEdges.card h_lt c' rfl
        exact ⟨c_full, hc_full⟩
  exact h_wf c.uncoloredEdges.card c rfl

lemma exists_extended_of_fan (u : V) :
    ∀ (n : ℕ) (vs : List V) (cols : List (Fin k)) (c : PartialEdgeColoring G k)
      (hlen_vs : vs.length = n + 1)
      (hlen : cols.length = vs.length)
      (_hnodup : vs.Nodup)
      (hadj : ∀ v ∈ vs, G.Adj u v)
      (_hnone : ∀ (hne : vs ≠ []), c.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none)
      (_hstep : ∀ (i : ℕ) (hi : i + 1 < vs.length),
        c.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols[i])
      (_hmiss : ∀ (i : ℕ) (hi : i < vs.length),
        cols[i] ∈ c.missingColors vs[i])
      (_hend : ∀ (hne : cols ≠ []), cols.getLast hne ∈ c.missingColors u),
      ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  intro n
  induction n with
  | zero =>
    intro vs cols c hlen_vs hlen hnodup hadj hnone hstep hmiss hend
    rcases vs with _ | ⟨v₀, _ | ⟨v₁, vs'⟩⟩
    · cases hlen_vs
    · rcases cols with _ | ⟨β₀, _ | ⟨β₁, cols'⟩⟩
      · cases hlen
      · have hadj0 : G.Adj u v₀ := hadj v₀ (by simp)
        have hnone0 : c.colorOf u v₀ hadj0 = none := hnone (by simp)
        have hmiss0 : β₀ ∈ c.missingColors v₀ := by
          have := hmiss 0 (by simp)
          exact this
        have hend0 : β₀ ∈ c.missingColors u := by
          have := hend (by simp)
          exact this
        have he_mem : (⟨s(u, v₀), hadj0⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
          simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hnone0
        let c' := c.extendColor u v₀ hadj0 β₀ hend0 hmiss0
        refine ⟨c', ?_⟩
        have heq := uncoloredEdges_extendColor c u v₀ hadj0 β₀ hend0 hmiss0
        rw [heq, Finset.card_erase_of_mem he_mem]
        exact Nat.pred_lt (Finset.card_pos.mpr ⟨⟨s(u, v₀), hadj0⟩, he_mem⟩).ne'
      · cases hlen
    · cases hlen_vs
  | succ m ih =>
    intro vs cols c hlen_vs hlen hnodup hadj hnone hstep hmiss hend
    rcases vs with _ | ⟨v₀, _ | ⟨v₁, vs'⟩⟩
    · cases hlen_vs
    · cases hlen_vs
    · rcases cols with _ | ⟨β₀, _ | ⟨β₁, cols'⟩⟩
      · cases hlen
      · cases hlen
      · have hlen_tail : (β₁ :: cols').length = (v₁ :: vs').length := by
          simp only [List.length_cons] at hlen ⊢; omega
        have hlen_vs_tail : (v₁ :: vs').length = m + 1 := by
          simp only [List.length_cons] at hlen_vs ⊢; omega
        have hadj0 : G.Adj u v₀ := hadj v₀ (by simp)
        have hadj1 : G.Adj u v₁ := hadj v₁ (by simp)
        have hnone0 : c.colorOf u v₀ hadj0 = none := hnone (by simp)
        have hcol0 : c.colorOf u v₁ hadj1 = some β₀ := by
          have := hstep 0 (by simp [hlen_vs])
          exact this
        have hmiss0 : β₀ ∈ c.missingColors v₀ := by
          have := hmiss 0 (by simp [hlen_vs])
          exact this
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
            have : i < (β₁ :: cols').length := by omega
            c₁.colorOf u (v₁ :: vs')[i + 1] (hadj_tail _ (List.getElem_mem _)) = some (β₁ :: cols')[i] := by
          intro i hi
          have h_ne1 : (⟨s(u, (v₁ :: vs')[i + 1]), hadj_tail _ (List.getElem_mem _)⟩ : G.edgeSet) ≠ ⟨s(u, v₀), hadj0⟩ := by
            intro heq
            have : s(u, (v₁ :: vs')[i + 1]) = s(u, v₀) := Subtype.ext_iff.mp heq
            rw [Sym2.eq_iff] at this
            rcases this with ⟨-, heq_v⟩ | ⟨heq_u, heq_v⟩
            · have : (v₁ :: vs')[i + 1] ∈ v₁ :: vs' := List.getElem_mem (by omega)
              rw [heq_v] at this
              exact h_v0_not_in this
            · exact hadj0.ne heq_u
          have h_ne2 : (⟨s(u, (v₁ :: vs')[i + 1]), hadj_tail _ (List.getElem_mem _)⟩ : G.edgeSet) ≠ ⟨s(u, v₁), hadj1⟩ := by
            intro heq
            have : s(u, (v₁ :: vs')[i + 1]) = s(u, v₁) := Subtype.ext_iff.mp heq
            rw [Sym2.eq_iff] at this
            rcases this with ⟨-, heq_v⟩ | ⟨heq_u, heq_v⟩
            · have h_nodup_tail' := (List.nodup_cons.mp hnodup_cons).1
              have h_i_lt : i < vs'.length := by
                simp only [List.length_cons] at hi
                omega
              have : (v₁ :: vs')[i + 1] = vs'[i] := rfl
              rw [this] at heq_v
              have : vs'[i] ∈ vs' := List.getElem_mem h_i_lt
              rw [heq_v] at this
              exact h_nodup_tail' this
            · exact hadj1.ne heq_u
          rw [shiftStep_colorOf_of_ne c u v₀ v₁ _ _ hadj0 hadj1 β₀ hcol0 hmiss0 _ h_ne1 h_ne2]
          have := hstep (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
          exact this
        have hmiss_tail : ∀ (i : ℕ) (hi : i < (v₁ :: vs').length),
            have : i < (β₁ :: cols').length := by omega
            (β₁ :: cols')[i] ∈ c₁.missingColors (v₁ :: vs')[i] := by
          intro i hi
          have h_ne_v0 : (v₁ :: vs')[i] ≠ v₀ := by
            intro heq
            have : (v₁ :: vs')[i] ∈ v₁ :: vs' := List.getElem_mem (by omega)
            rw [heq] at this
            exact h_v0_not_in this
          apply shiftStep_missing_of_ne_v c u v₀ v₁ _ hadj0 hadj1 β₀ hcol0 hmiss0 h_ne_v0
          have := hmiss (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
          exact this
        have hend_tail : ∀ (hne : β₁ :: cols' ≠ []), (β₁ :: cols').getLast hne ∈ c₁.missingColors u := by
          intro hne'
          have h_last_eq : (β₁ :: cols').getLast hne' = (β₀ :: β₁ :: cols').getLast (by simp) := by
            rfl
          rw [h_last_eq]
          apply shiftStep_missing_u c u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0
          exact hend (by simp)
        obtain ⟨c', hlt⟩ := ih (v₁ :: vs') (β₁ :: cols') c₁ hlen_vs_tail hlen_tail hnodup_cons hadj_tail hnone_tail hstep_tail hmiss_tail hend_tail
        refine ⟨c', ?_⟩
        rwa [hcard_c1] at hlt

lemma list_take_head {α : Type*} (l : List α) (n : ℕ) (hne : l ≠ []) (hne' : l.take (n + 1) ≠ []) :
    (l.take (n + 1)).head hne' = l.head hne := by
  cases l with
  | nil => contradiction
  | cons x xs => rfl

lemma list_getElem_take {α : Type*} (l : List α) (n : ℕ) (i : ℕ) (hi : i < n + 1) (hi' : i < l.length) :
    (l.take (n + 1))[i]'(by simp [List.length_take]; omega) = l[i] := by
  simp [List.getElem_take]

lemma list_getLast_take {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) (hne : l.take (j + 1) ≠ []) :
    (l.take (j + 1)).getLast hne = l[j] := by
  have hlen : (l.take (j + 1)).length = j + 1 := by simp [hj]
  rw [List.getLast_eq_getElem]
  simp [hlen, List.getElem_take]

lemma list_getElem_set {α : Type*} (l : List α) (j : ℕ) (x : α) (i : ℕ) (hi : i < (l.set j x).length) :
    (l.set j x)[i] = if i = j then x else l[i]'(by simpa [List.length_set] using hi) := by
  simp [List.getElem_set]
  by_cases h : j = i <;> simp [h, eq_comm]

lemma list_getLast_set {α : Type*} (l : List α) (j : ℕ) (hj : j + 1 < l.length) (x : α) (hne1 : l.set j x ≠ []) (hne2 : l ≠ []) :
    (l.set j x).getLast hne1 = l.getLast hne2 := by
  rw [List.getLast_eq_getElem, List.getLast_eq_getElem]
  have hne_idx : j ≠ l.length - 1 := by omega
  simp [List.getElem_set, hne_idx]

lemma list_nodup_concat {α : Type*} (l : List α) (x : α) (hnodup : l.Nodup) (hx : x ∉ l) :
    (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hnodup, List.nodup_singleton x, ?_⟩
  intro a ha b hb
  have : b = x := List.mem_singleton.mp hb
  subst this
  rintro rfl
  exact hx ha

lemma list_getElem_concat_last {α : Type*} (l : List α) (x : α) :
    (l ++ [x])[l.length]'(by simp) = x := by
  simp

lemma list_getElem_concat_left {α : Type*} (l : List α) (x : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x])[i]'(by simp; omega) = l[i] := by
  simp [List.getElem_append_left hi]

lemma list_concat_head {α : Type*} (l : List α) (x : α) (hne : l ≠ []) (hne' : l ++ [x] ≠ []) :
    (l ++ [x]).head hne' = l.head hne := by
  cases l with
  | nil => contradiction
  | cons y ys => rfl

lemma colorOf_inj_neighbor (u v w : V) (hv : G.Adj u v) (hw : G.Adj u w) (col : Fin k)
    (h1 : c.colorOf u v hv = some col) (h2 : c.colorOf u w hw = some col) : v = w := by
  by_contra hne
  have he_ne : (⟨s(u, v), hv⟩ : G.edgeSet) ≠ ⟨s(u, w), hw⟩ := by
    intro heq
    have : s(u, v) = s(u, w) := Subtype.ext_iff.mp heq
    rw [Sym2.eq_iff] at this
    rcases this with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · exact hv.ne rfl
  have h_share : ShareVertex G ⟨s(u, v), hv⟩ ⟨s(u, w), hw⟩ := ⟨u, Sym2.mem_mk_left u v, Sym2.mem_mk_left u w⟩
  dsimp [colorOf] at h1 h2
  exact c.proper he_ne h_share h1 h2

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
    intro heq
    exact this heq.symm
  have hmiss_j : β ∈ c.missingColors vs[j] := by
    have := hmiss j hj_lt_vs
    exact this
  have hmiss_n : β ∈ c.missingColors vs[n] := by
    have := hmiss n hn_lt_vs
    rw [hβ_eq] at this
    exact this
  have h_vs_ne : vs[j] ≠ vs[n] := by
    intro heq
    have h_inj := (List.nodup_iff_injective_getElem.mp hnodup)
    have heq_idx : (⟨j, hj_lt_vs⟩ : Fin vs.length) = ⟨n, hn_lt_vs⟩ := h_inj heq
    have : j = n := Fin.ext_iff.mp heq_idx
    omega
  have h_not_reach_both := kempe_not_reachable_both c h_ne_α_β hα hmiss_j hmiss_n h_vs_ne
  let c_swap := c.kempeSwap α β u
  have h_card_swap : c_swap.uncoloredEdges.card = c.uncoloredEdges.card := by
    rw [uncoloredEdges_kempeSwap]
  have h_miss_u_swap : β ∈ c_swap.missingColors u := kempeSwap_missing_u c α β u hα
  have hnone_swap : ∀ (hne : vs ≠ []), c_swap.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none := by
    intro hne
    have h0 := hnone hne
    dsimp [colorOf] at h0 ⊢
    exact kempeSwap_color_none c α β u _ h0
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
        have h_get_cols' : cols'[i] = α := by
          rw [list_getElem_set cols i α i hi_lt_cols']
          simp
        rw [h_get_cols']
        apply kempeSwap_colorOf_alpha c α β u vs[i + 1] (hadj _ (List.getElem_mem _)) h_ne_α_β
        exact h_col_orig
      · have h_get_cols' : cols'[i] = cols[i] := by
          rw [list_getElem_set cols j α i hi_lt_cols']
          simp [heq_ij]
        rw [h_get_cols']
        have h1 : cols[i] ≠ α := h_col_ne_α i hi_lt_n
        have h2 : cols[i] ≠ β := h_diff i hi_lt_n heq_ij
        apply kempeSwap_colorOf_of_ne c α β (cols[i]) u u vs[i + 1] (hadj _ (List.getElem_mem _)) h1 h2
        exact h_col_orig
    have hmiss_swap : ∀ (i : ℕ) (hi : i < vs.length), cols'[i] ∈ c_swap.missingColors vs[i] := by
      intro i hi
      by_cases heq_ij : i = j
      · subst heq_ij
        have : i < cols'.length := by rw [hlen_cols']; exact hi
        have h_get_cols' : cols'[i] = α := by
          rw [list_getElem_set cols i α i this]
          simp
        rw [h_get_cols']
        exact hmiss_j_swap
      · by_cases heq_in : i = n
        · have h_get_cols' : cols'[i] = β := by
            have h_idx_eq : cols'[i] = cols'[n] := by congr 1
            rw [h_idx_eq]
            rw [list_getElem_set cols j α n hn_lt_cols']
            have : n ≠ j := ne_of_gt hj
            simp [this, hβ_eq]
          rw [h_get_cols']
          have : vs[i] = vs[n] := by congr 1
          rw [this]
          exact hmiss_n_swap
        · have hi_lt_n : i < n := by rw [hlen_vs] at hi; omega
          have : i < cols'.length := by rw [hlen_cols']; exact hi
          have h_get_cols' : cols'[i] = cols[i] := by
            rw [list_getElem_set cols j α i this]
            simp [heq_ij]
          rw [h_get_cols']
          have h1 : cols[i] ≠ α := h_col_ne_α i hi_lt_n
          have h2 : cols[i] ≠ β := h_diff i hi_lt_n heq_ij
          apply kempeSwap_missing_of_ne c α β (cols[i]) u vs[i] h1 h2
          exact hmiss i hi
    have hend_swap : ∀ (hne : cols' ≠ []), cols'.getLast hne ∈ c_swap.missingColors u := by
      intro hne
      have h_last : cols'.getLast hne = β := by
        have hne_cols : cols ≠ [] := List.ne_nil_of_length_pos (by rw [hlen, hlen_vs]; omega)
        have hj_lt_len : j + 1 < cols.length := by rw [hlen, hlen_vs]; omega
        rw [list_getLast_set cols j hj_lt_len α hne hne_cols]
        rw [List.getLast_eq_getElem]
        have : cols.length - 1 = n := by rw [hlen, hlen_vs]; omega
        have h_get : cols[cols.length - 1] = cols[n] := by congr 1
        rw [h_get, hβ_eq]
      rw [h_last]
      exact h_miss_u_swap
    obtain ⟨c', hlt⟩ := exists_extended_of_fan u n vs cols' c_swap hlen_vs hlen_cols' hnodup hadj hnone_swap' hstep_swap hmiss_swap hend_swap
    refine ⟨c', ?_⟩
    rwa [h_card_swap] at hlt
  · have hnreach_j : ¬ (c.kempeGraph α β).Reachable u vs[j] := h_reach_j
    have hmiss_j_swap : β ∈ c_swap.missingColors vs[j] := kempeSwap_missing_v c α β u vs[j] hnreach_j hmiss_j
    let vs_sub := vs.take (j + 1)
    let cols_sub := cols.take (j + 1)
    have hlen_vs_sub : vs_sub.length = j + 1 := by
      dsimp [vs_sub]; rw [List.length_take]; omega
    have hlen_cols_sub : cols_sub.length = vs_sub.length := by
      dsimp [cols_sub, vs_sub]; rw [List.length_take, List.length_take, hlen]
    have hnodup_sub : vs_sub.Nodup := List.Nodup.sublist (List.take_sublist (j + 1) vs) hnodup
    have hadj_sub : ∀ v ∈ vs_sub, G.Adj u v := fun v hv => hadj v (List.mem_of_mem_take hv)
    have hnone_swap_sub : ∀ (hne : vs_sub ≠ []), c_swap.colorOf u (vs_sub.head hne) (hadj_sub _ (List.head_mem hne)) = none := by
      intro hne
      have hne_vs : vs ≠ [] := List.ne_nil_of_length_pos (by rw [hlen_vs]; omega)
      have hhead : vs_sub.head hne = vs.head hne_vs := list_take_head vs j hne_vs hne
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
      have h_get_vs : vs_sub[i + 1] = vs[i + 1] := by
        rw [list_getElem_take vs j (i + 1) (by omega) (by rw [hlen_vs]; omega)]
      have h_get_cols : cols_sub[i] = cols[i] := by
        rw [list_getElem_take cols j i (by omega) (by rw [hlen, hlen_vs]; omega)]
      have heq_edge : (⟨s(u, vs_sub[i + 1]), hadj_sub _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, vs[i + 1]), hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))⟩ := by
        ext; simp [h_get_vs]
      dsimp [colorOf] at h_col_orig ⊢
      rw [heq_edge, h_get_cols]
      have h1 : cols[i] ≠ α := h_col_ne_α i hi_lt_n
      have h2 : cols[i] ≠ β := h_diff i hi_lt_n (ne_of_lt hi_lt_j)
      apply kempeSwap_colorOf_of_ne c α β (cols[i]) u u vs[i + 1] (hadj _ (List.getElem_mem _)) h1 h2
      exact h_col_orig
    have hmiss_swap_sub : ∀ (i : ℕ) (hi : i < vs_sub.length), cols_sub[i] ∈ c_swap.missingColors vs_sub[i] := by
      intro i hi
      have hi_le_j : i ≤ j := by rw [hlen_vs_sub] at hi; omega
      have h_get_vs : vs_sub[i] = vs[i] := by
        rw [list_getElem_take vs j i (by omega) (by rw [hlen_vs]; omega)]
      have h_get_cols : cols_sub[i] = cols[i] := by
        rw [list_getElem_take cols j i (by omega) (by rw [hlen, hlen_vs]; omega)]
      rw [h_get_vs, h_get_cols]
      by_cases heq_ij : i = j
      · subst heq_ij
        exact hmiss_j_swap
      · have hi_lt_j : i < j := Nat.lt_of_le_of_ne hi_le_j heq_ij
        have hi_lt_n : i < n := by omega
        have h1 : cols[i] ≠ α := h_col_ne_α i hi_lt_n
        have h2 : cols[i] ≠ β := h_diff i hi_lt_n heq_ij
        apply kempeSwap_missing_of_ne c α β (cols[i]) u vs[i] h1 h2
        exact hmiss i (by rw [hlen_vs]; omega)
    have hend_swap_sub : ∀ (hne : cols_sub ≠ []), cols_sub.getLast hne ∈ c_swap.missingColors u := by
      intro hne
      have h_last : cols_sub.getLast hne = β := by
        rw [list_getLast_take cols j hj_lt_cols hne]
      rw [h_last]
      exact h_miss_u_swap
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
          by_contra hm0
          have hm_zero : m = 0 := by omega
          have h_m0 : vs[m] = vs[0] := by congr 1
          have hne_vs : vs ≠ [] := List.ne_nil_of_length_pos (by rw [hlen_vs]; omega)
          have h_head_eq : vs.head hne_vs = vs[0] := List.head_eq_getElem hne_vs
          have h0 := hnone hne_vs
          dsimp [colorOf] at h0 hw_col
          have heq_edge : (⟨s(u, vs.head hne_vs), hadj _ (List.head_mem hne_vs)⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by
            ext; simp [h_head_eq, ← h_m0, hm_eq]
          rw [heq_edge] at h0
          rw [h0] at hw_col
          cases hw_col
        let j := m - 1
        have hj : j < n := by rw [hlen_vs] at hm_lt; omega
        have hm_j1 : m = j + 1 := by omega
        have h_cycle : cols[n]'(by rw [hlen, hlen_vs]; omega) = cols[j]'(by rw [hlen, hlen_vs]; omega) := by
          have h_step_j := hstep j (by rw [hlen_vs]; omega)
          have h_vs_j1 : vs[j + 1] = w := by
            have : vs[j + 1] = vs[m] := by congr 1; omega
            rw [this, hm_eq]
          dsimp [colorOf] at h_step_j hw_col
          have heq_edge : (⟨s(u, vs[j + 1]), hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by
            ext; simp [h_vs_j1]
          rw [heq_edge] at h_step_j
          rw [hw_col] at h_step_j
          exact Option.some.inj h_step_j
        have h_diff_cycle : ∀ (i : ℕ) (hi : i < n), i ≠ j → cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ cols[j]'(by rw [hlen, hlen_vs]; omega) := by
          intro i hi hne_ij
          rcases lt_or_gt_of_ne hne_ij with hlt | hgt
          · exact (h_diff j hj i hlt).symm
          · exact h_diff i hi j hgt
        exact exists_extended_of_fan_cycle u n vs cols c α j hlen_vs hlen hnodup hadj hnone hstep hmiss hα hj h_cycle h_diff_cycle
      · obtain ⟨β_next, hβ_next⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := w)
        let vs' := vs ++ [w]
        let cols' := cols ++ [β_next]
        let n' := n + 1
        have hlen_vs' : vs'.length = n' + 1 := by
          dsimp [vs', n']; rw [List.length_append, List.length_singleton, hlen_vs]
        have hlen_cols' : cols'.length = vs'.length := by
          dsimp [cols', vs']; rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton, hlen]
        have hnodup' : vs'.Nodup := list_nodup_concat vs w hnodup hw_in
        have hadj' : ∀ v ∈ vs', G.Adj u v := by
          intro v hv
          rcases List.mem_append.mp hv with hv | hv
          · exact hadj v hv
          · have : v = w := List.mem_singleton.mp hv
            subst this
            exact hw_adj
        have hnone' : ∀ (hne : vs' ≠ []), c.colorOf u (vs'.head hne) (hadj' _ (List.head_mem hne)) = none := by
          intro hne
          have hne_vs : vs ≠ [] := List.ne_nil_of_length_pos (by rw [hlen_vs]; omega)
          have hhead : vs'.head hne = vs.head hne_vs := list_concat_head vs w hne_vs hne
          have h0 := hnone hne_vs
          dsimp [colorOf] at h0 ⊢
          have heq_edge : (⟨s(u, vs'.head hne), hadj' _ (List.head_mem hne)⟩ : G.edgeSet) = ⟨s(u, vs.head hne_vs), hadj _ (List.head_mem hne_vs)⟩ := by
            ext; simp [hhead]
          rw [heq_edge]
          exact h0
        have hstep' : ∀ (i : ℕ) (hi : i + 1 < vs'.length),
            c.colorOf u vs'[i + 1] (hadj' _ (List.getElem_mem _)) = some cols'[i] := by
          intro i hi
          have hi_lt_n' : i < n' := by rw [hlen_vs'] at hi; omega
          by_cases heq_in : i = n
          · have h_len_eq : i + 1 = vs.length := by rw [heq_in, hlen_vs]
            have h_get_vs : vs'[i + 1] = w := by
              have h_eq : vs'[i + 1] = vs'[vs.length] := by congr 1
              rw [h_eq, list_getElem_concat_last vs w]
            have h_get_cols : cols'[i] = cols[n] := by
              have h_eq : cols'[i] = cols'[n] := by congr 1
              rw [h_eq, list_getElem_concat_left cols β_next n hn_lt_cols]
            dsimp [colorOf] at hw_col ⊢
            have heq_edge : (⟨s(u, vs'[i + 1]), hadj' _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by
              ext; simp [h_get_vs]
            rw [heq_edge, h_get_cols]
            exact hw_col
          · have hi_lt_n : i < n := by dsimp [n'] at hi_lt_n'; omega
            have h_get_vs : vs'[i + 1] = vs[i + 1] := by
              rw [list_getElem_concat_left vs w (i + 1) (by rw [hlen_vs]; omega)]
            have h_get_cols : cols'[i] = cols[i] := by
              rw [list_getElem_concat_left cols β_next i (by rw [hlen, hlen_vs]; omega)]
            have h_step_orig := hstep i (by rw [hlen_vs]; omega)
            dsimp [colorOf] at h_step_orig ⊢
            have heq_edge : (⟨s(u, vs'[i + 1]), hadj' _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, vs[i + 1]), hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))⟩ := by
              ext; simp [h_get_vs]
            rw [heq_edge, h_get_cols]
            exact h_step_orig
        have hmiss' : ∀ (i : ℕ) (hi : i < vs'.length), cols'[i] ∈ c.missingColors vs'[i] := by
          intro i hi
          by_cases heq_in : i = vs.length
          · have h_get_vs : vs'[i] = w := by
              have h_eq : vs'[i] = vs'[vs.length] := by congr 1
              rw [h_eq, list_getElem_concat_last vs w]
            have h_get_cols : cols'[i] = β_next := by
              have h_eq : cols'[i] = cols'[cols.length] := by
                have : i = cols.length := by rw [heq_in, hlen]
                congr 1
              rw [h_eq, list_getElem_concat_last cols β_next]
            rw [h_get_vs, h_get_cols]
            exact hβ_next
          · have hi_lt_vs : i < vs.length := by
              dsimp [vs'] at hi; rw [List.length_append, List.length_singleton] at hi; omega
            have h_get_vs : vs'[i] = vs[i] := list_getElem_concat_left vs w i hi_lt_vs
            have h_get_cols : cols'[i] = cols[i] := list_getElem_concat_left cols β_next i (by rw [hlen]; exact hi_lt_vs)
            rw [h_get_vs, h_get_cols]
            exact hmiss i hi_lt_vs
        have h_diff' : ∀ (i : ℕ) (hi : i < n') (j : ℕ) (hj : j < i),
            cols'[i]'(by rw [hlen_cols', hlen_vs']; omega) ≠ cols'[j]'(by rw [hlen_cols', hlen_vs']; omega) := by
          intro i hi j hj
          by_cases heq_in : i = n
          · have hj_lt_n : j < n := by omega
            have h_get_i : cols'[i] = cols[n] := by
              have h_eq : cols'[i] = cols'[n] := by congr 1
              rw [h_eq, list_getElem_concat_left cols β_next n hn_lt_cols]
            have h_get_j : cols'[j] = cols[j] := list_getElem_concat_left cols β_next j (by rw [hlen, hlen_vs]; omega)
            rw [h_get_i, h_get_j]
            intro heq_cols
            have h_step_j := hstep j (by rw [hlen_vs]; omega)
            have h_step_j' : c.colorOf u vs[j + 1] (hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))) = some (cols[n]) := by
              rw [h_step_j, heq_cols]
            have heq_w := colorOf_inj_neighbor c u vs[j + 1] w (hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))) hw_adj (cols[n]) h_step_j' hw_col
            have : w ∈ vs := by
              have : vs[j + 1] ∈ vs := List.getElem_mem (by rw [hlen_vs]; omega)
              rwa [heq_w] at this
            exact hw_in this
          · have hi_lt_n : i < n := by dsimp [n'] at hi; omega
            have h_get_i : cols'[i] = cols[i] := list_getElem_concat_left cols β_next i (by rw [hlen, hlen_vs]; omega)
            have h_get_j : cols'[j] = cols[j] := list_getElem_concat_left cols β_next j (by rw [hlen, hlen_vs]; omega)
            rw [h_get_i, h_get_j]
            exact h_diff i hi_lt_n j hj
        have h_card_le : vs'.length ≤ Fintype.card V := by
          rw [← List.toFinset_card_of_nodup hnodup']
          exact Finset.card_le_univ _
        have h_len_vs' : vs'.length = vs.length + 1 := by
          dsimp [vs']; rw [List.length_append, List.length_singleton]
        have hN' : Fintype.card V - vs'.length < N := by
          rw [← hN, h_len_vs']
          omega
        exact ih (Fintype.card V - vs'.length) hN' n' vs' cols' rfl hlen_vs' hlen_cols' hnodup' hadj' hnone' hstep' hmiss' h_diff'

/-- Any non-empty partial edge coloring with $k > \Delta(G)$ can be extended to strictly fewer uncolored edges. -/
theorem exists_extended_coloring_vizing (h_max : G.maxDegree < k)
    (hne : c.uncoloredEdges.Nonempty) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  obtain ⟨e, he⟩ := hne
  rcases e with ⟨e_val, he_prop⟩
  induction e_val using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := he_prop
    have he_none : c.colorOf u v hadj = none := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact he
    obtain ⟨α, hα⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := u)
    obtain ⟨β₀, hβ₀⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := v)
    have hadj_single : ∀ w ∈ [v], G.Adj u w := by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      exact hadj
    have hnone_single : ∀ (hne' : [v] ≠ []), c.colorOf u ([v].head hne') (hadj_single _ (List.head_mem hne')) = none := by
      intro _
      exact he_none
    have hstep_single : ∀ (i : ℕ) (hi : i + 1 < [v].length),
        c.colorOf u [v][i + 1] (hadj_single _ (List.getElem_mem _)) = some [β₀][i] := by
      intro i hi
      simp only [List.length_singleton] at hi
      omega
    have hmiss_single : ∀ (i : ℕ) (hi : i < [v].length),
        [β₀][i] ∈ c.missingColors [v][i] := by
      intro i hi
      have : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst this
      exact hβ₀
    have h_diff_single : ∀ (i : ℕ) (hi : i < 0) (j : ℕ) (hj : j < i),
        [β₀][i]'(by omega) ≠ [β₀][j]'(by omega) := by
      intro i hi
      omega
    exact c.exists_extended_coloring_of_fan u α hα h_max (Fintype.card V - 1) 0 [v] [β₀] rfl rfl rfl (List.nodup_singleton v) hadj_single hnone_single hstep_single hmiss_single h_diff_single

/-- By well-founded induction on uncolored edges, any graph admits a complete proper edge coloring with $k > \Delta(G)$ colors. -/
theorem exists_full_coloring_vizing (h_max : G.maxDegree < k)
    (c : PartialEdgeColoring G k) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
  have h_wf : ∀ n, ∀ c : PartialEdgeColoring G k, c.uncoloredEdges.card = n → ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      by_cases hemp : c.uncoloredEdges = ∅
      · exact ⟨c, hemp⟩
      · have hne : c.uncoloredEdges.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        obtain ⟨c', h_lt⟩ := c.exists_extended_coloring_vizing h_max hne
        rw [hc] at h_lt
        obtain ⟨c_full, hc_full⟩ := ih c'.uncoloredEdges.card h_lt c' rfl
        exact ⟨c_full, hc_full⟩
  exact h_wf c.uncoloredEdges.card c rfl

end PartialEdgeColoring

/-- Every bipartite graph $G$ admits a proper edge coloring with $\Delta(G)$ colors. -/
theorem edgeColorable_of_bipartite (h_bip : G.Colorable 2) :
    IsEdgeColorable G G.maxDegree := by
  obtain ⟨c_full, hc_empty⟩ := PartialEdgeColoring.exists_full_coloring (le_refl G.maxDegree) h_bip (PartialEdgeColoring.empty (G := G) (k := G.maxDegree))
  have h_all : ∀ e : G.edgeSet, ∃ col : Fin G.maxDegree, c_full.color e = some col := by
    intro e
    cases h : c_full.color e with
    | none =>
      have he_mem : e ∈ c_full.uncoloredEdges := by
        simp only [PartialEdgeColoring.uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h
      rw [hc_empty] at he_mem
      exact False.elim (Finset.notMem_empty e he_mem)
    | some col =>
      exact ⟨col, rfl⟩
  choose col hcol using h_all
  have h_proper : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ → col e₁ ≠ col e₂ := by
    intro e₁ e₂ hne hshare heq
    have h1 := hcol e₁
    have h2 := hcol e₂
    rw [heq] at h1
    exact c_full.proper hne hshare h1 h2
  exact ⟨⟨col, h_proper⟩⟩

/-- Every graph $G$ admits a proper edge coloring with $\Delta(G) + 1$ colors. -/
theorem edgeColorable_of_maxDegree_succ :
    IsEdgeColorable G (G.maxDegree + 1) := by
  have h_max : G.maxDegree < G.maxDegree + 1 := Nat.lt_succ_self G.maxDegree
  obtain ⟨c_full, hc_empty⟩ := PartialEdgeColoring.exists_full_coloring_vizing h_max (PartialEdgeColoring.empty (G := G) (k := G.maxDegree + 1))
  have h_all : ∀ e : G.edgeSet, ∃ col : Fin (G.maxDegree + 1), c_full.color e = some col := by
    intro e
    cases h : c_full.color e with
    | none =>
      have he_mem : e ∈ c_full.uncoloredEdges := by
        simp only [PartialEdgeColoring.uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h
      rw [hc_empty] at he_mem
      exact False.elim (Finset.notMem_empty e he_mem)
    | some col =>
      exact ⟨col, rfl⟩
  choose col hcol using h_all
  have h_proper : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ → col e₁ ≠ col e₂ := by
    intro e₁ e₂ hne hshare heq
    have h1 := hcol e₁
    have h2 := hcol e₂
    rw [heq] at h1
    exact c_full.proper hne hshare h1 h2
  exact ⟨⟨col, h_proper⟩⟩

/--
Vizing's Theorem (1964):
For any finite simple graph $G$ with maximum degree $\Delta(G)$, the edge chromatic number
(chromatic index) $\chi'(G)$ satisfies:
$$\Delta(G) \le \chi'(G) \le \Delta(G) + 1$$
-/
theorem vizings_theorem [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G ∧ chromaticIndex G ≤ G.maxDegree + 1 := by
  constructor
  · exact chromatic_index_ge_maxDegree G
  · dsimp [chromaticIndex]
    have h_colorable := edgeColorable_of_maxDegree_succ G
    have h_mem : G.maxDegree + 1 ∈ {k | IsEdgeColorable G k} := h_colorable
    exact csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ h_mem

/-- A graph is Class 1 if its edge chromatic number achieves the maximum degree $\Delta(G)$. -/
def IsClassOne [Fintype G.edgeSet] : Prop :=
  chromaticIndex G = G.maxDegree

/-- A graph is Class 2 if its edge chromatic number is $\Delta(G) + 1$. -/
def IsClassTwo [Fintype G.edgeSet] : Prop :=
  chromaticIndex G = G.maxDegree + 1

/-- Vizing's Classification: Every finite simple graph is either Class 1 or Class 2. -/
theorem vizing_classification [Fintype G.edgeSet] :
    IsClassOne G ∨ IsClassTwo G := by
  have ⟨hle, hub⟩ := vizings_theorem G
  dsimp [IsClassOne, IsClassTwo]
  omega

/--
König's Line Coloring Theorem (1916):
Every bipartite graph is Class 1, i.e., $\chi'(G) = \Delta(G)$.
-/
theorem konig_edge_coloring [Fintype G.edgeSet] (h_bip : G.Colorable 2) :
    IsClassOne G := by
  dsimp [IsClassOne]
  have h_ge := chromatic_index_ge_maxDegree G
  have h_le : chromaticIndex G ≤ G.maxDegree := by
    dsimp [chromaticIndex]
    have h_colorable := edgeColorable_of_bipartite G h_bip
    have h_mem : G.maxDegree ∈ {k | IsEdgeColorable G k} := h_colorable
    exact csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ h_mem
  omega

end SimpleGraph


