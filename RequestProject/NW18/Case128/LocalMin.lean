/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128Reduction

@[expose] public section

/-!
# Case (5): a locally optimal four-part partition

Among all partitions of `V` into four classes we take one with the fewest internal edges.
Closeness to `T₂(n/2)+T₂(n/2)` bounds its number of internal edges, and minimality makes it
locally optimal: every vertex has no more neighbours in its own class than in any other class
(otherwise moving it would decrease the number of internal edges).  This replaces the
partition `P` built in the proof of Theorem 12.8 from `P'` and the sets `A'_i`
(Claim 12.8.4 is the local optimality below).
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Internal edges split into those avoiding `v` and those at `v`. -/
lemma internal_card_split (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (internal p G.edgeFinset).card =
      (G.edgeFinset.filter (fun e => v ∉ e ∧ (e.map p).IsDiag)).card +
        classLoad p G v (p v) := by
  classical
  rw [internal_inventory p G v, AntiEdgeSelection.incidentLoad, add_comm,
    ← card_filter_add_card_filter_not (s := internal p G.edgeFinset) (fun e => v ∈ e)]
  congr 2
  ext e
  simp only [internal, mem_filter]
  tauto

lemma internal_card_update (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (j : Fin 4) :
    (internal (Function.update p v j) G.edgeFinset).card + classLoad p G v (p v) =
      (internal p G.edgeFinset).card + classLoad p G v j := by
  classical
  set p' := Function.update p v j
  rw [internal_card_split p' G v, internal_card_split p G v]
  have h1 : G.edgeFinset.filter (fun e => v ∉ e ∧ (e.map p').IsDiag) =
      G.edgeFinset.filter (fun e => v ∉ e ∧ (e.map p).IsDiag) := by
    apply filter_congr
    intro e _
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.mem_iff, not_or, Sym2.map_mk, Sym2.mk_isDiag_iff]
      constructor
      · rintro ⟨⟨ha, hb⟩, h⟩
        refine ⟨⟨ha, hb⟩, ?_⟩
        simpa [p', Function.update_of_ne (Ne.symm ha), Function.update_of_ne (Ne.symm hb)]
          using h
      · rintro ⟨⟨ha, hb⟩, h⟩
        refine ⟨⟨ha, hb⟩, ?_⟩
        simpa [p', Function.update_of_ne (Ne.symm ha), Function.update_of_ne (Ne.symm hb)]
          using h
  have h2 : classLoad p' G v (p' v) = classLoad p G v j := by
    unfold classLoad
    congr 1
    apply filter_congr
    intro w hw
    have hwv : w ≠ v := fun h => by
      subst h
      exact (G.loopless.irrefl w) ((G.mem_neighborFinset _ _).mp hw)
    simp [p', Function.update_of_ne hwv]
  rw [h1, h2]
  ring

/-- A partition with the fewest internal edges is locally optimal. -/
lemma classLoad_own_le_of_min (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ p' : V → Fin 4, (internal p G.edgeFinset).card ≤ (internal p' G.edgeFinset).card)
    (v : V) (j : Fin 4) : classLoad p G v (p v) ≤ classLoad p G v j := by
  have h := internal_card_update p G v j
  have h' := hmin (Function.update p v j)
  omega

/-- **Locally optimal partition.**  If `G` is `α`-close to `T₂(n/2)+T₂(n/2)`, there is a
partition into four classes with at most `α n²` internal edges in which every vertex has at
most as many neighbours in its own class as in any other class. -/
theorem exists_localMin_partition (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ)
    (hc : IsClose α G (T2T2 (Fintype.card V))) :
    ∃ p : V → Fin 4,
      ((internal p G.edgeFinset).card : ℝ) ≤ α * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_partition_internal_le_of_close α G hc
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image (univ : Finset (V → Fin 4))
    (fun p => (internal p G.edgeFinset).card) ⟨p₀, mem_univ _⟩
  refine ⟨p, ?_, fun v j => classLoad_own_le_of_min p G (fun p' => hp p' (mem_univ _)) v j⟩
  refine le_trans ?_ hp₀
  exact_mod_cast hp p₀ (mem_univ _)

omit [DecidableEq V] in
/-- Local optimality bounds the own-class load by a quarter of the degree. -/
lemma four_classLoad_own_le (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hloc : ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j) (v : V) :
    4 * classLoad p G v (p v) ≤ G.degree v := by
  have h := degree_inventory p G v
  rw [Fin.sum_univ_three] at h
  have h0 := hloc v (partner 0 (p v))
  have h1 := hloc v (partner 1 (p v))
  have h2 := hloc v (partner 2 (p v))
  omega

end NashWilliams18.C128
