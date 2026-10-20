/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveRetirementStage194

/-! # The opposite-edge shadow of saturated packing vertices

For an edge-disjoint triangle packing, opposite edges at one vertex form
a matching. Thus forbidding all opposite edges at a set S costs at most
|S| in degree, instead of the degree of the whole packing. Avoiding this
actual shadow prevents indirect retirement at S. This is a geometric
producer, not a decomposition of the terminal remainder.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingOppositeShadowStage211

open Finset AntiEdgeSelection ReserveRetirementStage194

variable {V : Type} [DecidableEq V]

noncomputable def atVertex (D : Finset (Finset V)) (v : V) : Finset (Sym2 V) := by
  classical
  exact (D.filter fun s => v ∈ s).biUnion fun s =>
    (triEdges s).filter fun e => v ∉ e

noncomputable def shadow (D : Finset (Finset V)) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact S.biUnion (atVertex D)

theorem opposite_edge_unique (s : Finset V) (hc : s.card = 3) (v : V) (hv : v ∈ s)
    (e f : Sym2 V) (he : e ∈ triEdges s) (hf : f ∈ triEdges s)
    (hve : v ∉ e) (hvf : v ∉ f) : e = f := by
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := TypedNibble.mem_triEdges_iff.mp he
    have hva : v ≠ a := fun h => hve (h ▸ Sym2.mem_mk_left a b)
    have hvb : v ≠ b := fun h => hve (h ▸ Sym2.mem_mk_right a b)
    have heq : ({v, a, b} : Finset V) = s := by
      apply eq_of_subset_of_card_le
      · simp only [insert_subset_iff, singleton_subset_iff]
        exact ⟨hv, ha, hb⟩
      · simp [hc, hva, hvb, hab]
    induction f using Sym2.ind with
    | _ c d =>
      obtain ⟨hcs, hds, hcd⟩ := TypedNibble.mem_triEdges_iff.mp hf
      have hcv : c ≠ v := fun h => hvf (h ▸ Sym2.mem_mk_left c d)
      have hdv : d ≠ v := fun h => hvf (h ▸ Sym2.mem_mk_right c d)
      rw [← heq] at hcs hds
      simp only [mem_insert, mem_singleton] at hcs hds
      rcases hcs with h | h | h
      · exact False.elim (hcv h)
      · subst c
        rcases hds with h | h | h
        · exact False.elim (hdv h)
        · exact False.elim (hcd h.symm)
        · subst d; rfl
      · subst c
        rcases hds with h | h | h
        · exact False.elim (hdv h)
        · subst d; exact Sym2.eq_swap
        · exact False.elim (hcd h.symm)

theorem atVertex_degree_le_one {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (v x : V) :
    incidentLoad (atVertex D v) x ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨he, hxe⟩ := mem_filter.mp he
  obtain ⟨hf, hxf⟩ := mem_filter.mp hf
  obtain ⟨s, hs, he⟩ := mem_biUnion.mp he
  obtain ⟨r, hr, hf⟩ := mem_biUnion.mp hf
  obtain ⟨hsD, hvs⟩ := mem_filter.mp hs
  obtain ⟨hrD, hvr⟩ := mem_filter.mp hr
  obtain ⟨he, hve⟩ := mem_filter.mp he
  obtain ⟨hf, hvf⟩ := mem_filter.mp hf
  have hx : x ≠ v := fun h => hve (h ▸ hxe)
  have hxs : x ∈ s := by
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, -⟩ := TypedNibble.mem_triEdges_iff.mp he
      rcases Sym2.mem_iff.mp hxe with h | h
      · exact h ▸ ha
      · exact h ▸ hb
  have hxr : x ∈ r := by
    induction f using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, -⟩ := TypedNibble.mem_triEdges_iff.mp hf
      rcases Sym2.mem_iff.mp hxf with h | h
      · exact h ▸ ha
      · exact h ▸ hb
  have hsx : s(v, x) ∈ triEdges s :=
    TypedNibble.mem_triEdges_iff.mpr ⟨hvs, hxs, hx.symm⟩
  have hrx : s(v, x) ∈ triEdges r :=
    TypedNibble.mem_triEdges_iff.mpr ⟨hvr, hxr, hx.symm⟩
  have hsr : s = r := by
    by_contra hne
    exact disjoint_left.mp (hD.2.1 hsD hrD hne) hsx hrx
  subst r
  exact opposite_edge_unique s (hD.1 s hsD).1 v hvs e f he hf hve hvf

theorem shadow_degree_bound {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (S : Finset V) (x : V) :
    incidentLoad (shadow D S) x ≤ S.card := by
  classical
  unfold incidentLoad shadow
  rw [filter_biUnion]
  calc
    _ ≤ ∑ v ∈ S, ((atVertex D v).filter fun e => x ∈ e).card := card_biUnion_le
    _ ≤ ∑ _v ∈ S, 1 := sum_le_sum fun v _ => atVertex_degree_le_one p F Q D hD v x
    _ = S.card := by simp

theorem avoiding_shadow_has_no_opposite_hits (D : Finset (Finset V))
    (S : Finset V) (A : Finset (Sym2 V)) (hA : Disjoint A (shadow D S))
    (v : V) (hv : v ∈ S) : oppositeHits D A v = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsD, hvs, e, he, heA, hve⟩ := mem_filter.mp hs
  have heS : e ∈ shadow D S := mem_biUnion.mpr ⟨v, hv,
    mem_biUnion.mpr ⟨s, mem_filter.mpr ⟨hsD, hvs⟩, mem_filter.mpr ⟨he, hve⟩⟩⟩
  exact disjoint_left.mp hA heA heS


end PartitionedTriangleAbsorption.PackingOppositeShadowStage211
