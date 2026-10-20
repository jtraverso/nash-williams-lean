/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Reduction
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.OrdinaryHost

@[expose] public section

/-!
# Edge sets on a vertex subset, and the triangle-count of a closed part class

* `liftE W E` transports an edge set on the subtype `↥W` to the host; `restrE W X` is the
  set of edges of `X` with both ends in `W`, seen on the subtype.  Incidences, evenness,
  looplessness and cardinalities are preserved.
* `three_dvd_card_classEdges`: if `L` is integrally `F`-divisible (card-three types) and the
  part set `S` is closed for every type (each type lies inside `S` or avoids it), then the
  number of edges of `L` with both ends in parts of `S` is divisible by three.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection

section Lift

variable {V : Type*} [DecidableEq V] (W : Finset V)

/-- Lifting an edge set from the subtype. -/
def liftE (E : Finset (Sym2 W)) : Finset (Sym2 V) := E.image (Sym2.map Subtype.val)

/-- Restricting an edge set to the subtype. -/
noncomputable def restrE [Fintype V] (X : Finset (Sym2 V)) : Finset (Sym2 W) := by
  classical exact univ.filter (fun e => Sym2.map Subtype.val e ∈ X)

variable {W}

omit [DecidableEq V] in
theorem sym2_map_val_injective : Function.Injective (Sym2.map (Subtype.val : W → V)) :=
  Sym2.map.injective Subtype.val_injective

theorem card_liftE (E : Finset (Sym2 W)) : (liftE W E).card = E.card :=
  card_image_of_injective _ sym2_map_val_injective

theorem mem_liftE {E : Finset (Sym2 W)} {e : Sym2 W} : Sym2.map Subtype.val e ∈ liftE W E ↔ e ∈ E :=
  (sym2_map_val_injective.mem_finset_image)

theorem liftE_mono {E E' : Finset (Sym2 W)} (h : E ⊆ E') : liftE W E ⊆ liftE W E' :=
  image_subset_image h

theorem liftE_union (E E' : Finset (Sym2 W)) : liftE W (E ∪ E') = liftE W E ∪ liftE W E' :=
  image_union _ _

theorem disjoint_liftE {E E' : Finset (Sym2 W)} (h : Disjoint E E') :
    Disjoint (liftE W E) (liftE W E') :=
  (disjoint_image sym2_map_val_injective).mpr h

theorem liftE_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (E : ι → Finset (Sym2 W)) :
    liftE W (s.biUnion E) = s.biUnion fun i => liftE W (E i) :=
  biUnion_image

theorem mem_W_of_mem_liftE {E : Finset (Sym2 W)} {e : Sym2 V} (he : e ∈ liftE W E) :
    ∀ v ∈ e, v ∈ W := by
  intro v hv
  obtain ⟨e', _, rfl⟩ := mem_image.mp he
  obtain ⟨w, _, rfl⟩ := Sym2.mem_map.mp hv
  exact w.2

theorem incidentLoad_liftE_of_mem (E : Finset (Sym2 W)) (w : W) :
    incidentLoad (liftE W E) w.1 = incidentLoad E w := by
  unfold incidentLoad liftE
  have : (E.image (Sym2.map Subtype.val)).filter (fun e => w.1 ∈ e) =
      (E.filter (fun e => w ∈ e)).image (Sym2.map Subtype.val) := by
    ext e
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨e', he', rfl⟩, hw⟩
      obtain ⟨x, hx, hxw⟩ := Sym2.mem_map.mp hw
      exact ⟨e', ⟨he', Subtype.ext hxw ▸ hx⟩, rfl⟩
    · rintro ⟨e', ⟨he', hw⟩, rfl⟩
      exact ⟨⟨e', he', rfl⟩, Sym2.mem_map.mpr ⟨w, hw, rfl⟩⟩
  rw [this, card_image_of_injective _ sym2_map_val_injective]

theorem incidentLoad_liftE_of_not (E : Finset (Sym2 W)) {v : V} (hv : v ∉ W) :
    incidentLoad (liftE W E) v = 0 := by
  unfold incidentLoad
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hve
  exact hv (mem_W_of_mem_liftE he v hve)

theorem incidentLoad_liftE_le (E : Finset (Sym2 W)) {d : ℕ} (h : ∀ w, incidentLoad E w ≤ d)
    (v : V) : incidentLoad (liftE W E) v ≤ d := by
  by_cases hv : v ∈ W
  · rw [show v = (⟨v, hv⟩ : W).1 from rfl, incidentLoad_liftE_of_mem]
    exact h _
  · rw [incidentLoad_liftE_of_not E hv]; exact Nat.zero_le _

theorem even_liftE {E : Finset (Sym2 W)} (h : ∀ w, Even (incidentLoad E w)) :
    ∀ v, Even (incidentLoad (liftE W E) v) :=
  even_image (VInjOn.of_injective Subtype.val_injective E) h

theorem loopless_liftE {E : Finset (Sym2 W)} (h : ∀ e ∈ E, ¬ e.IsDiag) :
    ∀ e ∈ liftE W E, ¬ e.IsDiag :=
  loopless_image (VInjOn.of_injective Subtype.val_injective E) h

variable [Fintype V]

theorem liftE_restrE (X : Finset (Sym2 V)) :
    liftE W (restrE W X) = X.filter (fun e => ∀ v ∈ e, v ∈ W) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    have : Sym2.map Subtype.val e' ∈ X := by
      unfold restrE at he'; exact (mem_filter.mp he').2
    exact mem_filter.mpr ⟨this, mem_W_of_mem_liftE he⟩
  · intro he
    obtain ⟨heX, hW⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      refine mem_image.mpr ⟨s(⟨a, hW a (Sym2.mem_mk_left a b)⟩, ⟨b, hW b (Sym2.mem_mk_right a b)⟩),
        ?_, rfl⟩
      unfold restrE
      exact mem_filter.mpr ⟨mem_univ _, heX⟩

theorem restrE_mono {X Y : Finset (Sym2 V)} (h : X ⊆ Y) : restrE W X ⊆ restrE W Y := by
  classical
  intro e he
  unfold restrE at he ⊢
  exact mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp he).2⟩

theorem incidentLoad_restrE_le (X : Finset (Sym2 V)) (w : W) :
    incidentLoad (restrE W X) w ≤ incidentLoad X w.1 := by
  rw [← incidentLoad_liftE_of_mem, liftE_restrE]
  exact ModThreeLayer.incidentLoad_mono (filter_subset _ _) _

end Lift

section ThreeDvd

variable {V : Type*} [DecidableEq V] {t : ℕ}

omit [DecidableEq V] in
open Classical in
theorem sum_sum_pairVec (p : V → Fin t) (S : Finset (Fin t)) (e : Sym2 V) :
    ∑ i ∈ S, ∑ j ∈ S, pairVec p e i j = if ∀ v ∈ e, p v ∈ S then 2 else 0 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk, sum_add_distrib, ite_and]
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    by_cases ha : p a ∈ S <;> by_cases hb : p b ∈ S <;> simp [ha, hb]

theorem sum_count_of_subset {τ : Multiset (Fin t)} {S : Finset (Fin t)} (h : ∀ i ∈ τ, i ∈ S) :
    ∑ i ∈ S, (τ.count i : ℤ) = Multiset.card τ := by
  have h1 : ∑ i ∈ S, τ.count i = Multiset.card τ := by
    rw [← Multiset.toFinset_sum_count_eq]
    symm
    apply sum_subset
    · intro i hi; exact h i (Multiset.mem_toFinset.mp hi)
    · intro i _ hi
      exact Multiset.count_eq_zero.mpr (fun h' => hi (Multiset.mem_toFinset.mpr h'))
  exact_mod_cast h1

theorem sum_count_of_disjoint {τ : Multiset (Fin t)} {S : Finset (Fin t)} (h : ∀ i ∈ τ, i ∉ S) :
    ∑ i ∈ S, (τ.count i : ℤ) = 0 := by
  refine sum_eq_zero fun i hi => ?_
  have : τ.count i = 0 := Multiset.count_eq_zero.mpr (fun h' => h i h' hi)
  rw [this]; rfl

theorem sum_sum_typeEdgeVec (τ : Multiset (Fin t)) (S : Finset (Fin t)) :
    ∑ i ∈ S, ∑ j ∈ S, typeEdgeVec τ i j =
      (∑ i ∈ S, (τ.count i : ℤ)) ^ 2 - ∑ i ∈ S, (τ.count i : ℤ) := by
  classical
  simp only [typeEdgeVec, sum_sub_distrib, sum_ite_eq, ← mul_sum, ← sum_mul]
  rw [sum_congr rfl fun i hi => if_pos hi]
  ring

theorem six_dvd_sum_typeEdgeVec {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3)
    {S : Finset (Fin t)} (h : (∀ i ∈ τ, i ∈ S) ∨ (∀ i ∈ τ, i ∉ S)) :
    (6 : ℤ) ∣ ∑ i ∈ S, ∑ j ∈ S, typeEdgeVec τ i j := by
  rw [sum_sum_typeEdgeVec]
  rcases h with h | h
  · rw [sum_count_of_subset h, hτ]; norm_num
  · rw [sum_count_of_disjoint h]; norm_num

open Classical in
/-- **Triangle count of a closed part class.** -/
theorem three_dvd_card_classEdges (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) {S : Finset (Fin t)}
    (hS : ∀ τ ∈ F, (∀ i ∈ τ, i ∈ S) ∨ (∀ i ∈ τ, i ∉ S)) {L : Finset (Sym2 V)}
    (hL : IsIntDiv p F L) : 3 ∣ (L.filter (fun e => ∀ v ∈ e, p v ∈ S)).card := by
  classical
  obtain ⟨c, hc⟩ := hL.1
  have h1 : ∑ i ∈ S, ∑ j ∈ S, edgeVec p L i j =
      2 * ((L.filter (fun e => ∀ v ∈ e, p v ∈ S)).card : ℤ) := by
    have : ∀ i j, edgeVec p L i j = ∑ e ∈ L, pairVec p e i j := fun i j => by
      simp only [edgeVec, Finset.sum_apply]
    simp only [this]
    calc ∑ i ∈ S, ∑ j ∈ S, ∑ e ∈ L, pairVec p e i j
        = ∑ i ∈ S, ∑ e ∈ L, ∑ j ∈ S, pairVec p e i j := sum_congr rfl fun i _ => sum_comm
      _ = ∑ e ∈ L, ∑ i ∈ S, ∑ j ∈ S, pairVec p e i j := sum_comm
      _ = ∑ e ∈ L, (if ∀ v ∈ e, p v ∈ S then (2 : ℤ) else 0) :=
          sum_congr rfl fun e _ => sum_sum_pairVec p S e
      _ = _ := by rw [← sum_filter, sum_const, nsmul_eq_mul]; ring
  have h2 : ∑ i ∈ S, ∑ j ∈ S, edgeVec p L i j =
      ∑ τ ∈ F, c τ * ∑ i ∈ S, ∑ j ∈ S, typeEdgeVec τ i j := by
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ i ∈ S, ∑ j ∈ S, ∑ τ ∈ F, c τ * typeEdgeVec τ i j
        = ∑ i ∈ S, ∑ τ ∈ F, ∑ j ∈ S, c τ * typeEdgeVec τ i j := sum_congr rfl fun i _ => sum_comm
      _ = ∑ τ ∈ F, ∑ i ∈ S, ∑ j ∈ S, c τ * typeEdgeVec τ i j := sum_comm
      _ = _ := by simp only [mul_sum]
  have h6 : (6 : ℤ) ∣ ∑ τ ∈ F, c τ * ∑ i ∈ S, ∑ j ∈ S, typeEdgeVec τ i j :=
    dvd_sum fun τ hτ => dvd_mul_of_dvd_right (six_dvd_sum_typeEdgeVec (hF3 τ hτ) (hS τ hτ)) _
  rw [← h2, h1] at h6
  have : (3 : ℤ) ∣ ((L.filter (fun e => ∀ v ∈ e, p v ∈ S)).card : ℤ) := by
    obtain ⟨k, hk⟩ := h6
    exact ⟨k, by linarith⟩
  exact_mod_cast this

end ThreeDvd

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
