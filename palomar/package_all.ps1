param (
    [string]$TargetSlug = ""
)

$ErrorActionPreference = "Stop"
$root = (Get-Item $PSScriptRoot).Parent.FullName
$palomarDir = Join-Path $root "palomar"
$utf8NoBom = New-Object System.Text.UTF8Encoding($false)

function Write-PkgFile {
    param(
        [string]$Path,
        [string]$Content
    )
    $dir = Split-Path $Path -Parent
    if (!(Test-Path $dir)) {
        New-Item -ItemType Directory -Path $dir -Force | Out-Null
    }
    $lfContent = $Content.Replace("`r`n", "`n")
    if (!$lfContent.EndsWith("`n")) { $lfContent += "`n" }
    [System.IO.File]::WriteAllText($Path, $lfContent, $utf8NoBom)
}

# ==============================================================================
# 14. cayleys_formula
# ==============================================================================
$slug = "cayleys_formula"
$pkgDir = Join-Path $palomarDir $slug

$chal = @"
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Cayley's Tree Formula

This module formalizes **Cayley's Tree Formula** (Arthur Cayley, 1889) and the theory of
**Prüfer sequences** (Heinz Prüfer, 1918) in enumerative combinatorics without custom axioms.

## Mathematical Formulation

Let $V = \{1, 2, \dots, n\}$ be a set of $n \ge 2$ labeled vertices.
A **labeled tree** on $V$ is a connected, acyclic simple undirected graph $T = (V, E)$.

### The Main Theorem
Cayley's Tree Formula states that the number $T_n$ of distinct labeled trees on $n$ vertices is:
$$T_n = n^{n - 2}$$
-/

variable {n : ℕ}

/-- A labeled tree on vertex set `Fin n` is a simple graph that is both connected and acyclic. -/
structure LabeledTree (n : ℕ) where
  /-- The underlying simple graph on `Fin n` -/
  graph : SimpleGraph (Fin n)
  /-- The graph is connected -/
  connected : graph.Connected
  /-- The graph has no cycles -/
  is_acyclic : graph.IsAcyclic

/-- A Prüfer sequence of order $n$ is a sequence of $n - 2$ elements from `Fin n`. -/
abbrev PruferSequence (n : ℕ) := Fin (n - 2) → Fin n

/-- A rooted labeled tree is a labeled tree equipped with a distinguished root vertex. -/
structure RootedTree (n : ℕ) where
  /-- The underlying labeled tree -/
  tree : LabeledTree n
  /-- The designated root vertex -/
  root : Fin n

/--
**Cayley's Tree Formula (1889)**:
The number of labeled trees on $n \ge 2$ vertices is exactly $n^{n - 2}$.
-/
theorem cayleys_tree_formula (n : ℕ) (hn : 2 ≤ n) [Fintype (LabeledTree n)] :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := sorry

/-- Concrete instance of Cayley's formula for $n = 2$: $2^{2-2} = 1$. -/
theorem cayley_n2 [Fintype (LabeledTree 2)] : Fintype.card (LabeledTree 2) = 1 := sorry

/-- Concrete instance of Cayley's formula for $n = 3$: $3^{3-2} = 3$. -/
theorem cayley_n3 [Fintype (LabeledTree 3)] : Fintype.card (LabeledTree 3) = 3 := sorry

/-- Concrete instance of Cayley's formula for $n = 4$: $4^{4-2} = 16$. -/
theorem cayley_n4 [Fintype (LabeledTree 4)] : Fintype.card (LabeledTree 4) = 16 := sorry

/--
**Cayley's Rooted Tree Formula**:
The number of rooted labeled trees on $n \ge 2$ vertices is $n \cdot n^{n-2} = n^{n-1}$.
-/
theorem rooted_trees_count (n : ℕ) (hn : 2 ≤ n) [Fintype (LabeledTree n)] [Fintype (RootedTree n)] :
    Fintype.card (RootedTree n) = n ^ (n - 1) := sorry
"@

$sol = @"
import Formalization.CayleysFormula
"@

$comp = @"
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": [
    "cayleys_tree_formula",
    "cayley_n2",
    "cayley_n3",
    "cayley_n4",
    "rooted_trees_count"
  ],
  "permitted_axioms": [
    "propext",
    "Quot.sound",
    "Classical.choice"
  ]
}
"@

$yaml = @"
version: "v0.4"

project:
  name: "Cayley's Tree Formula and Prüfer Sequence Bijection"
  authors:
    - "Sneed & Feed Formalization Team"
  responsible_maintainers:
    - "sneed-and-feed"
  license: "CC0-1.0"
  description: >-
    A machine-checked Lean 4 formalization of Cayley's Tree Formula (1889) establishing that the number of
    labeled trees on n vertices is n^(n-2). Formalizes the Prüfer sequence correspondence (Heinz Prüfer 1918)
    encoding trees into sequences of length n-2 and decoding sequences into connected acyclic graphs, deriving
    the tree count and rooted tree count n^(n-1). To the maintainers' knowledge, the theorem was not found in
    an exact declaration name, docstring, and type signature search of the pinned Mathlib revision
    (Mathlib v4.34.0-rc1).

classification:
  arxiv: [math.CO]
  msc2020: ["05C05", "05C30", "05A19"]

sources:
  - title: "A theorem on trees"
    type: paper
    authors:
      - "Arthur Cayley"
    relationship: formalizes
  - title: "Neuer Beweis eines Satzes über Permutationen"
    type: paper
    authors:
      - "Heinz Prüfer"
    relationship: adapts

related_formalizations:
  - id: "https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean"
    relationship: builds-on
    note: >-
      Formalization builds on Mathlib's simple graph theory and acyclic graph definitions (IsAcyclic, IsTree)
      to formulate labeled tree structures and their bijective enumerations.

automation:
  methods:
    - method: agent
      tool_setup: >-
        Formalized using an agentic Lean 4 workflow with automated proof golfing and interactive
        Lean LSP checking under maintainer direction and human verification.
        All declarations rely strictly on standard Lean 4 kernel axioms (propext, Quot.sound, Classical.choice).

review:
  status: self-assessed
  reviewers:
    - "sneed-and-feed maintainers"
  notes: >-
    Challenge contains deliberate proof holes (`:= sorry` for automated benchmark evaluation),
    while all definitions and theorem statements are completely specified. Solution verified through
    human audit by the maintainers with 0 errors, 0 sorries, and strictly standard kernel axioms.
"@

Write-PkgFile (Join-Path $pkgDir "Challenge.lean") $chal
Write-PkgFile (Join-Path $pkgDir "Solution.lean") $sol
Write-PkgFile (Join-Path $pkgDir "comparator.json") $comp
Write-PkgFile (Join-Path $pkgDir "formalization.yaml") $yaml


# ==============================================================================
# 15. konig_matching
# ==============================================================================
$slug = "konig_matching"
$pkgDir = Join-Path $palomarDir $slug

$chal = @"
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

/-!
# Kőnig–Egerváry Duality Theorem

This module formalizes the **Kőnig–Egerváry Theorem** (Dénes Kőnig, 1931; Jenő Egerváry, 1931),
a cornerstone of combinatorial optimization and structural graph theory establishing strong
min-max duality between matchings and vertex covers in bipartite graphs.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/-- Two edges in $G$ share a common endpoint vertex. -/
def EdgesShareEndpoint (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v : V, v ∈ e₁ ∧ v ∈ e₂

/-- A set of edges $M \subseteq \operatorname{Sym2}(V)$ is a matching in $G$ if all edges belong to $G$
and no two distinct edges share a vertex. -/
def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ¬ EdgesShareEndpoint e₁ e₂)

/-- A set of vertices $C \subseteq V$ is a vertex cover of $G$ if every edge has at least
one endpoint in $C$. -/
def IsVertexCover (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ u v : V, G.Adj u v → u ∈ C ∨ v ∈ C

/-- The matching number $\nu(G)$: maximum size of a matching in $G$. -/
noncomputable def matchingNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ M : Finset (Sym2 V), IsMatching G M ∧ M.card = k }

/-- The vertex cover number $\tau(G)$: minimum size of a vertex cover in $G$. -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }

/-- An independent set in $G$ is a set of pairwise non-adjacent vertices. -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- The independence number $\alpha(G)$: maximum size of an independent set in $G$. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k }

/--
**Weak Duality for Matchings and Vertex Covers**:
Any matching $M$ and any vertex cover $C$ satisfy $|M| \le |C|$.
-/
theorem matching_card_le_vertexCover_card (G : SimpleGraph V) {M : Finset (Sym2 V)} {C : Finset V}
    (hM : IsMatching G M) (hC : IsVertexCover G C) :
    M.card ≤ C.card := sorry

/--
**Weak Duality Theorem**:
For any finite simple graph $G$, the matching number is bounded by the vertex cover number:
$$\nu(G) \le \tau(G)$$
-/
theorem weak_duality (G : SimpleGraph V) :
    matchingNumber G ≤ vertexCoverNumber G := sorry

/--
**Strong Duality Inequality in Bipartite Graphs**:
For any $2$-colorable graph $G$, the vertex cover number is bounded by the matching number:
$$\tau(G) \le \nu(G)$$
-/
theorem konig_duality_le (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    vertexCoverNumber G ≤ matchingNumber G := sorry

/--
**Kőnig–Egerváry Theorem (1931)**:
In any bipartite ($2$-colorable) graph $G$, the maximum size of a matching equals the minimum
size of a vertex cover (strong min-max duality):
$$\nu(G) = \tau(G)$$
-/
theorem konig_duality (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    matchingNumber G = vertexCoverNumber G := sorry

/--
**Gallai's Identity for Vertex Covers and Independent Sets (1959)**:
For any finite graph $G$, the independence number and vertex cover number sum to $|V|$:
$$\alpha(G) + \tau(G) = |V|$$
-/
theorem gallai_independence_vertex_cover (G : SimpleGraph V) :
    independenceNumber G + vertexCoverNumber G = Fintype.card V := sorry

/--
**Kőnig's Min-Max Formula for Independent Sets in Bipartite Graphs**:
In a bipartite graph, the independence number satisfies $\alpha(G) = |V| - \nu(G)$.
-/
theorem konig_independence_matching (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    independenceNumber G + matchingNumber G = Fintype.card V := sorry

end SimpleGraph
"@

$sol = @"
import Formalization.KonigMatching
"@

$comp = @"
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": [
    "SimpleGraph.matching_card_le_vertexCover_card",
    "SimpleGraph.weak_duality",
    "SimpleGraph.konig_duality_le",
    "SimpleGraph.konig_duality",
    "SimpleGraph.gallai_independence_vertex_cover",
    "SimpleGraph.konig_independence_matching"
  ],
  "permitted_axioms": [
    "propext",
    "Quot.sound",
    "Classical.choice"
  ]
}
"@

$yaml = @"
version: "v0.4"

project:
  name: "The Kőnig–Egerváry Theorem on Matchings and Vertex Covers in Bipartite Graphs"
  authors:
    - "Sneed & Feed Formalization Team"
  responsible_maintainers:
    - "sneed-and-feed"
  license: "CC0-1.0"
  description: >-
    A complete machine-checked Lean 4 formalization of the Kőnig–Egerváry Theorem (1931) and Gallai identities (1959).
    Proves strong min-max duality matchingNumber(G) = vertexCoverNumber(G) for 2-colorable graphs G via Hall's
    defect matching theorem, and formalizes Gallai's identity independenceNumber(G) + vertexCoverNumber(G) = |V(G)|.
    To the maintainers' knowledge, the theorem was not found in an exact declaration name, docstring, and type
    signature search of the pinned Mathlib revision (Mathlib v4.34.0-rc1).

classification:
  arxiv: [math.CO]
  msc2020: ["05C70", "05C69", "90C27"]

sources:
  - title: "Gráfok és mátrixok"
    type: paper
    authors:
      - "Dénes Kőnig"
    relationship: formalizes
  - title: "Matrixok kombinatorius tulajdonságairól"
    type: paper
    authors:
      - "Jenő Egerváry"
    relationship: formalizes
  - title: "Über extreme Punkt- und Kantenmengen"
    type: paper
    authors:
      - "Tibor Gallai"
    relationship: adapts

related_formalizations:
  - id: "https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/Hall/Basic.lean"
    relationship: builds-on
    note: >-
      Formalization builds on Mathlib's Hall marriage condition (all_card_le_biUnion_card_iff_exists_injective)
      to establish the defect matching reduction in bipartite graphs.

automation:
  methods:
    - method: agent
      tool_setup: >-
        Formalized using an agentic Lean 4 workflow with automated proof golfing and interactive
        Lean LSP checking under maintainer direction and human verification.
        All declarations rely strictly on standard Lean 4 kernel axioms (propext, Quot.sound, Classical.choice).

review:
  status: self-assessed
  reviewers:
    - "sneed-and-feed maintainers"
  notes: >-
    Challenge contains deliberate proof holes (`:= sorry` for automated benchmark evaluation),
    while all definitions and theorem statements are completely specified. Solution verified through
    human audit by the maintainers with 0 errors, 0 sorries, and strictly standard kernel axioms.
"@

Write-PkgFile (Join-Path $pkgDir "Challenge.lean") $chal
Write-PkgFile (Join-Path $pkgDir "Solution.lean") $sol
Write-PkgFile (Join-Path $pkgDir "comparator.json") $comp
Write-PkgFile (Join-Path $pkgDir "formalization.yaml") $yaml

Write-Output "==> Packaged cayleys_formula and konig_matching successfully!"
