/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystFramingStage89
public import PartitionedTriangleAbsorption.PairExchangeTraceStage87

/-! # Token-tracked configurations for catalyst insertion

Original tokens are the edges `e ∈ Y`; catalytic tokens are the three edges
`(y, 0) = co y – cs y`, `(y, 1) = co y – ct y`, `(y, 2) = cs y – ct y` of the
catalyst of each active vertex `y`. After the active vertices of `P` have been
processed (with carriers `cz y`, `cz' y`), the current position of a token is
given explicitly:

* an original token `e` sits at `curY e = e.map (rep · e)`, where an endpoint
  `u ∈ P` of `e` has been replaced by `cz u` if `e = u – nm u` and by `cz' u`
  otherwise, and an unprocessed endpoint is unchanged;
* the catalytic tokens of `y ∈ P` sit at `cz y – cs y`, `cz' y – ct y`,
  `cs y – ct y`; those of `y ∉ P` are unchanged.

`config P` is the set of all current token positions. The main lemma
`config_step` proves that processing one more active vertex `y` is exactly the
replacement of the four source edges `y a₀, y b₀, co y – cs y, co y – ct y` by
`z a₀, z – cs y, z' b₀, z' – ct y`, the replacement performed by the Stage87
exchange with roots `(y, co y, a₀, b₀, cs y, ct y)`. Every other token stays
where it is; in particular the edge `cs y – ct y` is untouched and the
identity of an original token is kept even when its other endpoint moves.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystInsertionStage89

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- Static data of the insertion: the deployed configuration `Y`, its active
vertices `A`, the two neighbours `nm y`, `np y` of each active vertex, and the
catalyst triangle `(co y, cs y, ct y)`. -/
structure Data (V : Type*) where
  Y : Finset (Sym2 V)
  A : Finset V
  nm : V → V
  np : V → V
  co : V → V
  cs : V → V
  ct : V → V

namespace Data

variable (S : Data V) (cz cz' : V → V) (P : Finset V)

/-- The current endpoint replacing the original endpoint `u` of token `e`. -/
def rep (u : V) (e : Sym2 V) : V :=
  if u ∈ P then (if e = s(u, S.nm u) then cz u else cz' u) else u

/-- Current position of the original token `e`. -/
def curY (e : Sym2 V) : Sym2 V := e.map fun u => S.rep cz cz' P u e

/-- Current position of the catalytic token `(y, i)`. -/
def catTok (y : V) (i : Fin 3) : Sym2 V :=
  ![if y ∈ P then s(cz y, S.cs y) else s(S.co y, S.cs y),
    if y ∈ P then s(cz' y, S.ct y) else s(S.co y, S.ct y), s(S.cs y, S.ct y)] i

/-- Current positions of the three catalytic tokens of `y`. -/
def catCur (y : V) : Finset (Sym2 V) :=
  if y ∈ P then {s(cz y, S.cs y), s(cz' y, S.ct y), s(S.cs y, S.ct y)}
  else catEdges (S.co y) (S.cs y) (S.ct y)

/-- The current configuration: all current token positions. -/
def config : Finset (Sym2 V) :=
  S.Y.image (S.curY cz cz' P) ∪ S.A.biUnion (S.catCur cz cz' P)

/-- The catalyst union `D` of the static data. -/
def cats : Finset (Sym2 V) := catUnion S.A S.co S.cs S.ct

theorem catCur_eq_image (y : V) :
    S.catCur cz cz' P y = (univ : Finset (Fin 3)).image (S.catTok cz cz' P y) := by
  unfold catCur catTok catEdges
  split_ifs <;> ext e <;> simp [Fin.exists_fin_succ, eq_comm]

theorem curY_mk (a b : V) :
    S.curY cz cz' P s(a, b) = s(S.rep cz cz' P a s(a, b), S.rep cz cz' P b s(a, b)) := rfl

theorem rep_of_not_mem {u : V} (hu : u ∉ P) (e : Sym2 V) : S.rep cz cz' P u e = u := by
  simp [rep, hu]

theorem rep_cases (u : V) (e : Sym2 V) :
    (u ∉ P ∧ S.rep cz cz' P u e = u) ∨
      (u ∈ P ∧ (S.rep cz cz' P u e = cz u ∨ S.rep cz cz' P u e = cz' u)) := by
  unfold rep
  by_cases hu : u ∈ P
  · right; refine ⟨hu, ?_⟩; split_ifs <;> simp
  · left; simp [hu]

theorem mem_curY {e : Sym2 V} {v : V} :
    v ∈ S.curY cz cz' P e ↔ ∃ u ∈ e, S.rep cz cz' P u e = v := by
  unfold curY
  rw [Sym2.mem_map]

/-- Before any processing every token is at its initial edge. -/
theorem config_empty : S.config cz cz' ∅ = S.Y ∪ S.cats := by
  have h1 : S.Y.image (S.curY cz cz' ∅) = S.Y := by
    have : S.curY cz cz' ∅ = id := by
      funext e
      unfold curY
      simp [rep, Sym2.map_id']
    rw [this, image_id]
  have h2 : S.A.biUnion (S.catCur cz cz' ∅) = S.cats := by
    unfold cats catUnion
    apply biUnion_congr rfl
    intro y _
    simp [catCur]
  unfold config
  rw [h1, h2]

end Data

/-- Properties of the carriers created so far (for the processed set `P`). -/
structure Carriers (Z₀ : Finset V) (cz cz' : V → V) (P : Finset V) : Prop where
  fresh : ∀ y ∈ P, cz y ∉ Z₀ ∧ cz' y ∉ Z₀
  ne : ∀ y ∈ P, cz y ≠ cz' y
  inj : ∀ y ∈ P, ∀ y' ∈ P, y ≠ y' → cz y ≠ cz y' ∧ cz y ≠ cz' y' ∧ cz' y ≠ cz' y'

variable [Fintype V]

/-- The static hypotheses on the deployed configuration and its catalysts. -/
structure Frame (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset (Sym2 V)) (S : Data V) (Z₀ : Finset V) : Prop where
  /-- Each active vertex has exactly the two original tokens `y – nm y`, `y – np y`. -/
  star : ∀ y ∈ S.A, S.Y.filter (fun e => y ∈ e) = {s(y, S.nm y), s(y, S.np y)}
  nm_ne_np : ∀ y ∈ S.A, S.nm y ≠ S.np y
  supp : ∀ e ∈ S.Y, ∀ u ∈ e, u ∈ S.A
  Y_real : S.Y ⊆ G.edgeFinset
  Y_forb : Disjoint S.Y B
  Y_link : ∀ u v, s(u, v) ∈ S.Y → ∃ k, Link F (p u) (p v) k
  label : ∀ y ∈ S.A, p (S.co y) = p y
  link : ∀ y ∈ S.A, Link F (p y) (p (S.cs y)) (p (S.ct y))
  distinct : ∀ y ∈ S.A, S.co y ≠ S.cs y ∧ S.co y ≠ S.ct y ∧ S.cs y ≠ S.ct y
  cat_real : ∀ y ∈ S.A, catEdges (S.co y) (S.cs y) (S.ct y) ⊆ G.edgeFinset
  cat_forb : ∀ y ∈ S.A, Disjoint (catEdges (S.co y) (S.cs y) (S.ct y)) B
  /-- Catalyst vertices are not active vertices. -/
  notA : ∀ y ∈ S.A, Disjoint (catVerts (S.co y) (S.cs y) (S.ct y)) S.A
  vdisj : ∀ y ∈ S.A, ∀ y' ∈ S.A, y ≠ y' →
    Disjoint (catVerts (S.co y) (S.cs y) (S.ct y)) (catVerts (S.co y') (S.cs y') (S.ct y'))
  /-- The forbidden vertex set contains all active vertices ... -/
  ZA : S.A ⊆ Z₀
  /-- ... and all catalyst vertices. -/
  Zcat : ∀ y ∈ S.A, catVerts (S.co y) (S.cs y) (S.ct y) ⊆ Z₀

/-- The invariant of the insertion induction after processing `P`, with
cumulative history `U` and forbidden vertex set `Z`. -/
structure Inv (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset (Sym2 V)) (S : Data V) (Z₀ : Finset V)
    (cz cz' : V → V) (P : Finset V) (U : Finset (Sym2 V)) (Z : Finset V) : Prop where
  sub : P ⊆ S.A
  hist : S.config cz cz' P ⊆ U
  real : S.config cz cz' P ⊆ G.edgeFinset
  forb : Disjoint (S.config cz cz' P) B
  /-- `Z` contains every vertex of the current configuration. -/
  supp : ∀ e ∈ S.config cz cz' P, ∀ v ∈ e, v ∈ Z
  base : Z₀ ⊆ Z
  links : ∀ u v, s(u, v) ∈ S.config cz cz' P → ∃ k, Link F (p u) (p v) k
  carriers : Carriers Z₀ cz cz' P
  carrier_mem : ∀ y ∈ P, cz y ∈ Z ∧ cz' y ∈ Z
  carrier_label : ∀ y ∈ P, p (cz y) = p y ∧ p (cz' y) = p y

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V}

theorem Frame.mem_cat {y : V} (fr : Frame p F G B S Z₀) (hy : y ∈ S.A) :
    S.co y ∈ Z₀ ∧ S.cs y ∈ Z₀ ∧ S.ct y ∈ Z₀ :=
  ⟨fr.Zcat y hy (by simp [catVerts]), fr.Zcat y hy (by simp [catVerts]),
    fr.Zcat y hy (by simp [catVerts])⟩

theorem Frame.cat_notA {y : V} (fr : Frame p F G B S Z₀) (hy : y ∈ S.A) :
    S.co y ∉ S.A ∧ S.cs y ∉ S.A ∧ S.ct y ∉ S.A := by
  have h := fr.notA y hy
  refine ⟨fun h' => disjoint_left.mp h (by simp [catVerts]) h',
    fun h' => disjoint_left.mp h (by simp [catVerts]) h',
    fun h' => disjoint_left.mp h (by simp [catVerts]) h'⟩

theorem Frame.nm_mem {y : V} (fr : Frame p F G B S Z₀) (hy : y ∈ S.A) :
    s(y, S.nm y) ∈ S.Y ∧ s(y, S.np y) ∈ S.Y := by
  have h := fr.star y hy
  have h1 : s(y, S.nm y) ∈ S.Y.filter (fun e => y ∈ e) := by rw [h]; simp
  have h2 : s(y, S.np y) ∈ S.Y.filter (fun e => y ∈ e) := by rw [h]; simp
  exact ⟨(mem_filter.mp h1).1, (mem_filter.mp h2).1⟩

theorem Frame.nm_A {y : V} (fr : Frame p F G B S Z₀) (hy : y ∈ S.A) :
    S.nm y ∈ S.A ∧ S.np y ∈ S.A :=
  ⟨fr.supp _ (fr.nm_mem hy).1 _ (Sym2.mem_mk_right _ _),
    fr.supp _ (fr.nm_mem hy).2 _ (Sym2.mem_mk_right _ _)⟩

theorem Frame.nm_ne {y : V} (fr : Frame p F G B S Z₀) (hy : y ∈ S.A) :
    S.nm y ≠ y ∧ S.np y ≠ y := by
  have h1 := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp
    (fr.Y_real (fr.nm_mem hy).1))
  have h2 := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp
    (fr.Y_real (fr.nm_mem hy).2))
  simp only [Sym2.mk_isDiag_iff] at h1 h2
  exact ⟨Ne.symm h1, Ne.symm h2⟩

/-- Current endpoints of distinct active vertices are distinct. -/
theorem rep_ne_of_ne (fr : Frame p F G B S Z₀) {cz cz' : V → V} {P : Finset V}
    (hc : Carriers Z₀ cz cz' P) {u u' : V} (hu : u ∈ S.A) (hu' : u' ∈ S.A) (hne : u ≠ u')
    (e e' : Sym2 V) : S.rep cz cz' P u e ≠ S.rep cz cz' P u' e' := by
  rcases S.rep_cases cz cz' P u e with ⟨hP, h⟩ | ⟨hP, h⟩ <;>
    rcases S.rep_cases cz cz' P u' e' with ⟨hP', h'⟩ | ⟨hP', h'⟩
  · rw [h, h']; exact hne
  · rw [h]
    intro heq
    rcases h' with h' | h' <;> rw [h'] at heq
    · exact (hc.fresh u' hP').1 (heq ▸ fr.ZA hu)
    · exact (hc.fresh u' hP').2 (heq ▸ fr.ZA hu)
  · rw [h']
    intro heq
    rcases h with h | h <;> rw [h] at heq
    · exact (hc.fresh u hP).1 (heq.symm ▸ fr.ZA hu')
    · exact (hc.fresh u hP).2 (heq.symm ▸ fr.ZA hu')
  · have hi := hc.inj u hP u' hP' hne
    have hi' := hc.inj u' hP' u hP (Ne.symm hne)
    rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h']
    · exact hi.1
    · exact hi.2.1
    · exact Ne.symm hi'.2.1
    · exact hi.2.2

/-- A current endpoint of an active vertex is never a catalyst vertex. -/
theorem rep_not_cat (fr : Frame p F G B S Z₀) {cz cz' : V → V} {P : Finset V}
    (hc : Carriers Z₀ cz cz' P) {u : V} (hu : u ∈ S.A) (e : Sym2 V) {y : V} (hy : y ∈ S.A)
    {w : V} (hw : w ∈ catVerts (S.co y) (S.cs y) (S.ct y)) : S.rep cz cz' P u e ≠ w := by
  rcases S.rep_cases cz cz' P u e with ⟨_, h⟩ | ⟨hP, h⟩
  · rw [h]
    intro heq
    exact disjoint_left.mp (fr.notA y hy) hw (heq ▸ hu)
  · intro heq
    rcases h with h | h <;> rw [h] at heq
    · exact (hc.fresh u hP).1 (heq ▸ fr.Zcat y hy hw)
    · exact (hc.fresh u hP).2 (heq ▸ fr.Zcat y hy hw)

end

end PartitionedTriangleAbsorption.CatalystInsertionStage89
