/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourColourStabilityStage84
public import PartitionedTriangleAbsorption.ApproximateBalanceStage114
public import PartitionedTriangleAbsorption.ReserveAwareRecutStage120

/-! # Child balance from a complete reference host and sparse missing edges

The reference seed is constructed from colour-class sizes. No fractional
seed on the damaged child is assumed. These bounds supply inputs to the
recut interface, not a vertex vortex or an exact decomposition.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ChildBalanceStage128

open Finset AntiEdgeSelection CoverDownStage105 FourColourStabilityStage84
open FourClassSeedStage80 ClassRepresentativesStage65 TypedLoadNecessity
open TypedApplicationLinks ApproximateBalanceStage114 ReserveAwareRecutStage120

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem balance_le_card (p : V → Fin 4) (k : Fin 2) (E : Finset (Sym2 V)) :
    |(bal p k E : ℝ)| ≤ E.card := by
  simp only [bal, Int.cast_sum]
  calc
    _ ≤ ∑ e ∈ E, |(balEdge p k e : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ E, (1 : ℝ) := sum_le_sum fun e _ => balEdge_abs_le_one p k e
    _ = _ := by simp

/-- A deliberately loose bound, valid even for diagonal Sym2 entries. -/
theorem card_le_total_load (E : Finset (Sym2 V)) :
    E.card ≤ ∑ v : V, incidentLoad E v := by
  have hcover : E ⊆ univ.biUnion (fun v : V => E.filter fun e => v ∈ e) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      exact mem_biUnion.mpr ⟨u, mem_univ u, mem_filter.mpr ⟨he, by simp⟩⟩
  exact (card_le_card hcover).trans (card_biUnion_le)

theorem card_le_of_load (E : Finset (Sym2 V)) (f : ℕ)
    (h : ∀ v, incidentLoad E v ≤ f) : E.card ≤ Fintype.card V * f := by
  calc
    E.card ≤ ∑ v : V, incidentLoad E v := card_le_total_load E
    _ ≤ ∑ _v : V, f := sum_le_sum fun v _ => h v
    _ = _ := by simp

theorem sparse_child_balance (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G ≤ host p)
    (s f : ℕ) (hs : 0 < s) (eta : ℝ) (heta : eta ≤ 1 / 2)
    (hsize : ∀ i, (1 - eta) * s ≤ ((classSet p i).card : ℝ) ∧
      ((classSet p i).card : ℝ) ≤ s)
    (hF : ∀ v, incidentLoad ((host p).edgeFinset \ G.edgeFinset) v ≤ f)
    (k : Fin 2) :
    |(bal p k G.edgeFinset : ℝ)| ≤
      eta * (host p).edgeFinset.card + Fintype.card V * f := by
  have href := uniform_seed p (host p) (by intros; rfl) s hs eta heta hsize
  have hb := balance_bound p (host p) (fun _ => 1 / (2 * (s : ℝ))) eta (by
    intro e he
    have hh := href.2 e he
    change 1 - eta ≤ edgeLoad p F3 (host p) (fun _ => 1 / (2 * (s : ℝ))) e ∧
      edgeLoad p F3 (host p) (fun _ => 1 / (2 * (s : ℝ))) e ≤ 1 at hh
    rw [abs_le]
    constructor <;> linarith) k
  let F := (host p).edgeFinset \ G.edgeFinset
  have hsub := SimpleGraph.edgeFinset_mono hG
  have hdiff : (host p).edgeFinset \ F = G.edgeFinset := by
    ext e
    simp only [F, mem_sdiff]
    constructor
    · tauto
    · intro he
      exact ⟨hsub he, by tauto⟩
  have hid := bal_sdiff p k (sdiff_subset : F ⊆ (host p).edgeFinset)
  rw [hdiff] at hid
  have hc : (F.card : ℝ) ≤ Fintype.card V * f := by
    exact_mod_cast card_le_of_load F f hF
  have he := balance_le_card p k F
  have hidR : (bal p k G.edgeFinset : ℝ) =
      (bal p k (host p).edgeFinset : ℝ) - (bal p k F : ℝ) := by
    exact_mod_cast hid
  rw [hidR]
  exact (abs_sub _ _).trans (add_le_add hb (he.trans hc))

theorem child_degree_bound (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G ≤ host p) (v : V) :
    incidentLoad G.edgeFinset v ≤ Fintype.card V := by
  rw [incident_edgeFinset]
  have h := G.degree_le_of_le hG (v := v)
  have hh := host_degree_add_class p v
  omega

end PartitionedTriangleAbsorption.ChildBalanceStage128
