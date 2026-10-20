/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Transport
public import PartitionedTriangleAbsorption.ReserveCoverDown
public import PartitionedTriangleAbsorption.OnePartDivisibility
public import PartitionedTriangleAbsorption.ReturnedBridge
public import PartitionedTriangleAbsorption.Transformer
public import PartitionedTriangleAbsorption.RefinerAssembly

/-! # Stage105 basics for a physical one-level cover-down

A *reserve triple* `(x, z, z')` is an actual triangle with one outer vertex `x`
and two vertices `z, z'` of the next vortex set `U`. Its two *spokes* are
`xz, xz'`; its *internal edge* is `zz'`. A *spoke* of `U` is an edge with exactly
one endpoint in `U` (recorded in oriented form).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- The three physical edges of a reserve triple. -/
def resTri (r : V × V × V) : Finset (Sym2 V) :=
  {s(r.1, r.2.1), s(r.1, r.2.2), s(r.2.1, r.2.2)}

/-- The two spokes of a reserve triple. -/
def resSpokes (r : V × V × V) : Finset (Sym2 V) :=
  {s(r.1, r.2.1), s(r.1, r.2.2)}

/-- All physical edges of a reserve family. -/
def resEdges (T : Finset (V × V × V)) : Finset (Sym2 V) := T.biUnion resTri

/-- All spokes of a family of reserve triples. -/
def spokesOf (A : Finset (V × V × V)) : Finset (Sym2 V) := A.biUnion resSpokes

/-- An oriented spoke of `U`: one endpoint outside, one inside. -/
def IsSpoke (U : Finset V) (e : Sym2 V) : Prop := ∃ a b, a ∉ U ∧ b ∈ U ∧ e = s(a, b)

/-- Both endpoints lie in `U`. -/
def IsInner (U : Finset V) (e : Sym2 V) : Prop := ∀ v ∈ e, v ∈ U

theorem resSpokes_subset_resTri (r : V × V × V) : resSpokes r ⊆ resTri r := by
  intro e he
  simp only [resSpokes, resTri, mem_insert, mem_singleton] at he ⊢
  tauto

theorem spokesOf_subset_resEdges {A T : Finset (V × V × V)} (h : A ⊆ T) :
    spokesOf A ⊆ resEdges T := by
  intro e he
  obtain ⟨r, hr, he⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨r, h hr, resSpokes_subset_resTri r he⟩

theorem resEdges_mono {A T : Finset (V × V × V)} (h : A ⊆ T) :
    resEdges A ⊆ resEdges T := biUnion_subset_biUnion_of_subset_left _ h

theorem mem_resTri_self₁ (r : V × V × V) : s(r.1, r.2.1) ∈ resTri r := by simp [resTri]
theorem mem_resTri_self₂ (r : V × V × V) : s(r.1, r.2.2) ∈ resTri r := by simp [resTri]
theorem mem_resTri_self₃ (r : V × V × V) : s(r.2.1, r.2.2) ∈ resTri r := by simp [resTri]

/-! ### Degree bookkeeping -/

theorem incidentLoad_mono {S S' : Finset (Sym2 V)} (h : S ⊆ S') (w : V) :
    incidentLoad S w ≤ incidentLoad S' w :=
  card_le_card (filter_subset_filter _ h)

theorem incidentLoad_union_le (S S' : Finset (Sym2 V)) (w : V) :
    incidentLoad (S ∪ S') w ≤ incidentLoad S w + incidentLoad S' w := by
  unfold incidentLoad
  rw [filter_union]
  exact card_union_le _ _

theorem incidentLoad_insert {e : Sym2 V} {S : Finset (Sym2 V)} (he : e ∉ S) (w : V) :
    incidentLoad (insert e S) w = incidentLoad S w + if w ∈ e then 1 else 0 := by
  unfold incidentLoad
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => he (mem_filter.mp h').1)]
  · rfl

theorem incidentLoad_sdiff_add {S T : Finset (Sym2 V)} (h : T ⊆ S) (w : V) :
    incidentLoad (S \ T) w + incidentLoad T w = incidentLoad S w := by
  rw [← OnePart.incidentLoad_union disjoint_sdiff_self_left, sdiff_union_of_subset h]

/-- Charging an edge `ab` to the two edges `ca, cb`. -/
theorem ind_le_two (a b c w : V) :
    (if w ∈ s(a, b) then 1 else 0) ≤
      (if w ∈ s(c, a) then 1 else 0) + (if w ∈ s(c, b) then 1 else 0) := by
  simp only [Sym2.mem_iff]
  split_ifs <;> first | omega | (exfalso; tauto)

/-! ### Typed physical triangles -/

/-- In a host whose edges join distinct classes, every actual triangle is an `F3` piece. -/
theorem hasDecomp_tri (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ a b, s(a, b) ∈ E → p a ≠ p b) {a b c : V}
    (hab : s(a, b) ∈ E) (hac : s(a, c) ∈ E) (hbc : s(b, c) ∈ E) :
    HasDecomp p F3 {s(a, b), s(a, c), s(b, c)} := by
  have h1 := hcross a b hab
  have h2 := hcross a c hac
  have h3 := hcross b c hbc
  have nab : a ≠ b := fun h => h1 (h ▸ rfl)
  have nac : a ≠ c := fun h => h2 (h ▸ rfl)
  have nbc : b ≠ c := fun h => h3 (h ▸ rfl)
  rw [← triEdges_three nab nac nbc]
  apply ReserveCoverDown.hasDecomp_triEdges
  apply PrivateTemplateStage69.isTypedTri_F3_of_proper p
    (card_eq_three.mpr ⟨a, b, c, nab, nac, nbc, rfl⟩)
  intro u v huv
  rw [triEdges_three nab nac nbc] at huv
  simp only [mem_insert, mem_singleton, Sym2.eq_iff] at huv
  rcases huv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact h1
  · exact h1.symm
  · exact h2
  · exact h2.symm
  · exact h3
  · exact h3.symm

/-- A reserve triple whose edges lie in the host is an `F3` piece. -/
theorem hasDecomp_resTri (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ a b, s(a, b) ∈ E → p a ≠ p b) {r : V × V × V} (hr : resTri r ⊆ E) :
    HasDecomp p F3 (resTri r) :=
  hasDecomp_tri p E hcross (hr (mem_resTri_self₁ r)) (hr (mem_resTri_self₂ r))
    (hr (mem_resTri_self₃ r))

/-- Edge-disjoint reserve triples at the same outer vertex have distinct first
inner vertices. -/
theorem reserve_eq_of_fst {T : Finset (V × V × V)}
    (hdisj : (T : Set (V × V × V)).PairwiseDisjoint resTri) {r r' : V × V × V}
    (hr : r ∈ T) (hr' : r' ∈ T) (h1 : r.1 = r'.1) (h2 : r.2.1 = r'.2.1) : r = r' := by
  by_contra hne
  have := hdisj hr hr' hne
  have h : s(r.1, r.2.1) ∈ resTri r' := by rw [h1, h2]; exact mem_resTri_self₁ r'
  exact disjoint_left.mp this (mem_resTri_self₁ r) h

theorem reserve_eq_of_snd {T : Finset (V × V × V)}
    (hdisj : (T : Set (V × V × V)).PairwiseDisjoint resTri) {r r' : V × V × V}
    (hr : r ∈ T) (hr' : r' ∈ T) (h1 : r.1 = r'.1) (h2 : r.2.2 = r'.2.2) : r = r' := by
  by_contra hne
  have := hdisj hr hr' hne
  have h : s(r.1, r.2.2) ∈ resTri r' := by rw [h1, h2]; exact mem_resTri_self₂ r'
  exact disjoint_left.mp this (mem_resTri_self₂ r) h

end PartitionedTriangleAbsorption.CoverDownStage105
