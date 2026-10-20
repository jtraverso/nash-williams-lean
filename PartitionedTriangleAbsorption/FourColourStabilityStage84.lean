/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourColourRigidityStage83
public import PartitionedTriangleAbsorption.FourClassDivisibilityStage82

/-! # Quantitative four-colour class bounds and the canonical missing edges

A proper colouring and a degree margin produce the nearly equal host and
its sparse defect. This does not construct a proper colouring or replace
the refined balances by ordinary triangle divisibility.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourColourStabilityStage84

open Finset ClassRepresentativesStage65 FourClassSeedStage80 AntiEdgeSelection

variable {V : Type*} [Fintype V]

def host (p : V → Fin 4) : SimpleGraph V :=
  SimpleGraph.comap p (⊤ : SimpleGraph (Fin 4))

instance (p : V → Fin 4) : DecidableRel (host p).Adj :=
  fun u v => inferInstanceAs (Decidable (p u ≠ p v))

theorem class_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4)) (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 - eps) * Fintype.card V ≤ (G.degree v : ℝ))
    (i : Fin 4) :
    ((classSet c i).card : ℝ) ≤ (1 / 4 + eps) * Fintype.card V := by
  classical
  by_cases hi : (classSet c i).Nonempty
  · obtain ⟨v, hv⟩ := hi
    have hvcol : c v = i := (mem_filter.mp hv).2
    have hb := FourColourRigidityStage83.degree_add_class_le G c v
    rw [hvcol] at hb
    have hbR : (G.degree v : ℝ) + (classSet c i).card ≤ Fintype.card V :=
      by exact_mod_cast hb
    nlinarith [hdeg v]
  · have hz := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hi)
    rw [hz, Nat.cast_zero]
    positivity

theorem class_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4)) (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 - eps) * Fintype.card V ≤ (G.degree v : ℝ))
    (i : Fin 4) :
    (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet c i).card : ℝ) := by
  have h0 := class_upper G c eps heps hdeg 0
  have h1 := class_upper G c eps heps hdeg 1
  have h2 := class_upper G c eps heps hdeg 2
  have h3 := class_upper G c eps heps hdeg 3
  have ht : ∑ j : Fin 4, ((classSet c j).card : ℝ) = Fintype.card V :=
    by exact_mod_cast sum_class_card (c : V → Fin 4)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ht
  change (classSet c 0).card + ((classSet c 1).card +
    ((classSet c 2).card + ((classSet c 3).card + (0 : ℝ)))) = Fintype.card V at ht
  fin_cases i
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet c 0).card : ℝ)
    nlinarith
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet c 1).card : ℝ)
    nlinarith
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet c 2).card : ℝ)
    nlinarith
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet c 3).card : ℝ)
    nlinarith

theorem nearly_equal_classes (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4)) (eps eta : ℝ) (heps : 0 ≤ eps)
    (hn : 0 < Fintype.card V) (hscale : 16 * eps ≤ eta)
    (hdeg : ∀ v, (3 / 4 - eps) * Fintype.card V ≤ (G.degree v : ℝ)) :
    ∃ s : ℕ, 0 < s ∧ ∀ i,
      (1 - eta) * s ≤ ((classSet c i).card : ℝ) ∧ ((classSet c i).card : ℝ) ≤ s := by
  classical
  obtain ⟨j, _, hj⟩ := exists_max_image univ (fun i : Fin 4 => (classSet c i).card)
    (by simp)
  let s := (classSet c j).card
  have hmax : ∀ i, (classSet c i).card ≤ s := fun i => hj i (mem_univ i)
  have hnhi : Fintype.card V ≤ 4 * s := by
    have hh := sum_le_sum (s := (univ : Finset (Fin 4)))
      (f := fun i => (classSet c i).card) (g := fun _ => s) (fun i _ => hmax i)
    rw [sum_class_card] at hh
    simpa using hh
  have hs : 0 < s := by omega
  have hnhiR : (Fintype.card V : ℝ) ≤ 4 * s := by exact_mod_cast hnhi
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hgap : 4 * eps * Fintype.card V ≤ eta * s := by
    have hh := mul_le_mul_of_nonneg_left hnhiR (by positivity : 0 ≤ 4 * eps)
    have ht := mul_le_mul_of_nonneg_right hscale hsR
    nlinarith
  have hjup := class_upper G c eps heps hdeg j
  refine ⟨s, hs, ?_⟩
  intro i
  have hilo := class_lower G c eps heps hdeg i
  have himax : ((classSet c i).card : ℝ) ≤ s := by exact_mod_cast hmax i
  dsimp only [s] at hjup ⊢
  constructor
  · nlinarith
  · exact himax

theorem incident_edgeFinset [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : incidentLoad G.edgeFinset v = G.degree v := by
  classical
  rw [incidentLoad, ← SimpleGraph.incidenceFinset_eq_filter,
    SimpleGraph.card_incidenceFinset_eq_degree]

theorem host_degree_add_class (p : V → Fin 4) (v : V) :
    (host p).degree v + (classSet p (p v)).card = Fintype.card V := by
  classical
  have hh : (host p).neighborFinset v = (classSet p (p v))ᶜ := by
    ext w
    simp only [SimpleGraph.neighborFinset, Set.mem_toFinset,
      mem_compl, classSet, mem_filter, mem_univ, true_and]
    change p v ≠ p w ↔ p w ≠ p v
    exact ne_comm
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hh, card_compl]
  have hc := card_le_card (subset_univ (classSet p (p v)))
  simp only [card_univ] at hc
  omega

theorem canonical_delete [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : G.Coloring (Fin 4)) :
    (host c).deleteEdges (((host c).edgeFinset \ G.edgeFinset : Finset (Sym2 V)) :
      Set (Sym2 V)) = G := by
  classical
  apply SimpleGraph.ext
  funext u v
  apply propext
  simp only [SimpleGraph.deleteEdges_adj, mem_coe, mem_sdiff,
    SimpleGraph.edgeFinset, Set.mem_toFinset, SimpleGraph.mem_edgeSet]
  change (c u ≠ c v) ∧ ¬((c u ≠ c v) ∧ ¬G.Adj u v) ↔ G.Adj u v
  have hh : G.Adj u v → c u ≠ c v := fun h => c.valid h
  tauto

theorem defect_account [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : G.Coloring (Fin 4)) (v : V) :
    incidentLoad ((host c).edgeFinset \ G.edgeFinset) v + G.degree v +
      (classSet c (c v)).card = Fintype.card V := by
  classical
  have hsub : G.edgeFinset ⊆ (host c).edgeFinset :=
    SimpleGraph.edgeFinset_mono (fun _ _ h => c.valid h)
  have hf : ((host c).edgeFinset \ G.edgeFinset).filter (fun e => v ∈ e) =
      ((host c).edgeFinset.filter (fun e => v ∈ e)) \
        (G.edgeFinset.filter (fun e => v ∈ e)) := by
    ext e
    simp only [mem_filter, mem_sdiff]
    tauto
  have hfs : G.edgeFinset.filter (fun e => v ∈ e) ⊆
      (host c).edgeFinset.filter (fun e => v ∈ e) := filter_subset_filter _ hsub
  have hh := host_degree_add_class (c : V → Fin 4) v
  have hdeg : G.degree v ≤ (host c).degree v :=
    G.degree_le_of_le (fun _ _ h => c.valid h)
  rw [incidentLoad, hf, card_sdiff_of_subset hfs,
    ← incidentLoad, ← incidentLoad, incident_edgeFinset, incident_edgeFinset]
  omega

theorem defect_degree_bound [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : G.Coloring (Fin 4)) (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 - eps) * Fintype.card V ≤ (G.degree v : ℝ)) :
    DegBounded ((host c).edgeFinset \ G.edgeFinset) (4 * eps * Fintype.card V) := by
  classical
  intro v
  have hh : (incidentLoad ((host c).edgeFinset \ G.edgeFinset) v : ℝ) +
      G.degree v + (classSet c (c v)).card = Fintype.card V :=
    by exact_mod_cast defect_account G c v
  have hlo := class_lower G c eps heps hdeg (c v)
  change (incidentLoad _ v : ℝ) ≤ _
  nlinarith [hdeg v]

end PartitionedTriangleAbsorption.FourColourStabilityStage84
