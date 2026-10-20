/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ChildBalanceStage128
public import PartitionedTriangleAbsorption.GeometricRecutStage127

/-! # Stage131: the child-type balance bound transported to the ambient child

Stage128 bounds the balance of a graph `G ≤ host p` on the *child vertex
type*. The recut of Stage127 is stated for the ambient induced child
`E.filter (IsInner U)` on the ambient vertex type. This file proves the
transport: the induced child is the image of an explicit graph on the
subtype `U`, the balance functionals agree, and missing edges of the
subtype graph are charged to the ambient forbidden set `F`.

Consequently the two abstract recut inputs of Stage127 (the balance bound
`β` and the degree bound `D`) are discharged from class sizes and the
missing-edge load alone:

* `β = η |U|² + |U| f`,
* `D = |U|`.

No seed on the damaged child is assumed; Stage128 builds the uniform seed on
the complete reference host of `U`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.AmbientChildStage131

open Finset AntiEdgeSelection CoverDownStage105 FourColourStabilityStage84
open ClassRepresentativesStage65 ChildBalanceStage128 SeedDrivenTrimStage114
open F3ReserveTrimStage109 ReserveTrimStage109 TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

/-- The induced child of `E` on `U`, as a graph on the subtype `U`. Only
cross-coloured pairs are retained, so it lies below the reference host. -/
def childGraph (p : V → Fin 4) (U : Finset V) (E : Finset (Sym2 V)) : SimpleGraph U where
  Adj a b := p a.1 ≠ p b.1 ∧ s(a.1, b.1) ∈ E
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (p : V → Fin 4) (U : Finset V) (E : Finset (Sym2 V)) :
    DecidableRel (childGraph p U E).Adj := fun a b =>
  inferInstanceAs (Decidable (p a.1 ≠ p b.1 ∧ s(a.1, b.1) ∈ E))

/-- Embedding of child pairs into ambient pairs. -/
def valEmb (U : Finset V) : Sym2 U ↪ Sym2 V :=
  ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩

omit [DecidableEq V] in
theorem childGraph_le_host (p : V → Fin 4) (U : Finset V) (E : Finset (Sym2 V)) :
    childGraph p U E ≤ host (fun a : U => p a.1) := fun _ _ h => h.1

/-- The ambient induced child is exactly the image of the child graph. -/
theorem inner_eq_map (p : V → Fin 4) (U : Finset V) (E : Finset (Sym2 V))
    [DecidablePred (IsInner U)] (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v) :
    E.filter (IsInner U) = (childGraph p U E).edgeFinset.map (valEmb U) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_filter, mem_map, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨he, hin⟩
      have ha : a ∈ U := hin a (Sym2.mem_mk_left a b)
      have hb : b ∈ U := hin b (Sym2.mem_mk_right a b)
      exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ⟨hcross a b he, he⟩, rfl⟩
    · rintro ⟨e', he', hmap⟩
      induction e' using Sym2.ind with
      | _ x y =>
        have hxy : s(x.1, y.1) = s(a, b) := hmap
        rw [← hxy]
        refine ⟨he'.2, ?_⟩
        intro w hw
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact x.2
        · exact y.2

omit [DecidableEq V] in
/-- The balance functionals commute with the inclusion of the child. -/
theorem bal_map (p : V → Fin 4) (U : Finset V) (k : Fin 2) (E' : Finset (Sym2 U)) :
    bal p k (E'.map (valEmb U)) =
      bal (fun a : U => p a.1) k E' := by
  unfold bal
  rw [sum_map]
  apply sum_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ a b => rfl

omit [DecidableEq V] in
theorem card_classSet_child (p : V → Fin 4) (U : Finset V) (i : Fin 4) :
    (classSet (fun a : U => p a.1) i).card = (U.filter fun v => p v = i).card := by
  unfold classSet
  refine card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    exact mem_filter.mpr ⟨a.2, (mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨hxU, hpx⟩ := mem_filter.mp hx
    exact ⟨⟨x, hxU⟩, mem_filter.mpr ⟨mem_univ _, hpx⟩, rfl⟩

/-- Missing reference edges of the child are charged to the ambient
forbidden set. -/
theorem missing_load_le (p : V → Fin 4) (U : Finset V) (E F : Finset (Sym2 V))
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E) (a : U) :
    incidentLoad ((host (fun a : U => p a.1)).edgeFinset \ (childGraph p U E).edgeFinset) a ≤
      incidentLoad F a.1 := by
  unfold incidentLoad
  apply card_le_card_of_injOn (fun e => Sym2.map Subtype.val e)
  · intro e he
    have he' : e ∈ ((host (fun a : U => p a.1)).edgeFinset \
        (childGraph p U E).edgeFinset).filter (fun e => a ∈ e) := he
    obtain ⟨hd, hae⟩ := mem_filter.mp he'
    obtain ⟨hH, hG⟩ := mem_sdiff.mp hd
    rw [mem_coe, mem_filter]
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at hH hG
      have hpxy : p x.1 ≠ p y.1 := hH
      have hnot : s(x.1, y.1) ∉ E := fun h => hG ⟨hpxy, h⟩
      refine ⟨?_, ?_⟩
      · by_contra hF
        exact hnot (hE x.1 x.2 y.1 y.2 hpxy hF)
      · rcases Sym2.mem_iff.mp hae with rfl | rfl
        · exact Sym2.mem_mk_left _ _
        · exact Sym2.mem_mk_right _ _
  · intro e _ e' _ h
    exact Sym2.map.injective Subtype.val_injective h

/-- Every ambient vertex meets at most `|U|` edges of the induced child. -/
theorem inner_load_le_card (U : Finset V) (E : Finset (Sym2 V))
    [DecidablePred (IsInner U)] (v : V) :
    incidentLoad (E.filter (IsInner U)) v ≤ U.card := by
  unfold incidentLoad
  calc ((E.filter (IsInner U)).filter (fun e => v ∈ e)).card
      ≤ (U.image fun w => s(v, w)).card := by
        apply card_le_card
        intro e he
        obtain ⟨hin, hve⟩ := mem_filter.mp he
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
        exact mem_image.mpr ⟨w, (mem_filter.mp hin).2 w (Sym2.mem_mk_right v w), rfl⟩
    _ ≤ U.card := card_image_le

/-- **Ambient child balance.** If every class of `U` has size between
`(1-η)S` and `S`, every edge of `E` crosses two classes, and every missing
cross pair inside `U` is a forbidden edge of load at most `f`, then the
induced child has both F3 balance functionals bounded by `η|U|² + |U|f`.
The uniform reference seed lives on the complete host of `U`; no seed on
the child is assumed. -/
theorem inner_child_balance (p : V → Fin 4) (U : Finset V) (E F : Finset (Sym2 V))
    [DecidablePred (IsInner U)]
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E)
    (f S : ℕ) (hF : ∀ v, incidentLoad F v ≤ f) (hS : 0 < S) (eta : ℝ) (heta : eta ≤ 1 / 2)
    (hclass : ∀ i, (1 - eta) * S ≤ ((U.filter fun v => p v = i).card : ℝ) ∧
      ((U.filter fun v => p v = i).card : ℝ) ≤ S)
    (k : Fin 2) :
    |(bal p k (E.filter (IsInner U)) : ℝ)| ≤
      eta * (U.card : ℝ) ^ 2 + U.card * f := by
  have heta0 : 0 ≤ eta := by
    obtain ⟨h1, h2⟩ := hclass 0
    have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
    nlinarith
  have hb := sparse_child_balance (fun a : U => p a.1) (childGraph p U E)
    (childGraph_le_host p U E) S f hS eta heta
    (fun i => by rw [card_classSet_child]; exact hclass i)
    (fun a => (missing_load_le p U E F hE a).trans (hF a.1)) k
  rw [inner_eq_map p U E hcross, bal_map]
  have hcardU : Fintype.card U = U.card := Fintype.card_coe U
  rw [hcardU] at hb
  have hH : ((host (fun a : U => p a.1)).edgeFinset.card : ℝ) ≤ (U.card : ℝ) ^ 2 := by
    have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := host (fun a : U => p a.1))
    have h2 := Nat.choose_le_pow (Fintype.card U) 2
    rw [hcardU] at h1 h2
    exact_mod_cast h1.trans h2
  calc _ ≤ eta * ((host (fun a : U => p a.1)).edgeFinset.card : ℝ) + U.card * f := hb
    _ ≤ _ := by gcongr

end PartitionedTriangleAbsorption.AmbientChildStage131
