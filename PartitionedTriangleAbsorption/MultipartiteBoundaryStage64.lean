/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassAwareHingesStage64
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-! # A threshold host with physical hinges but no universal same-part queries

The complete graph in four equal structural classes has minimum degree 3n/4.
Grouping the classes into two parts permits abundant F0 hinges but makes a
two-root common-neighbour query in one part impossible.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.MultipartiteBoundaryStage64

open Finset TypedApplicationLinks F0Geometric SignedHinge ClassAwareHingesStage64

abbrev Vertex (s : ℕ) := Fin 4 × Fin s

abbrev graph (s : ℕ) : SimpleGraph (Vertex s) := SimpleGraph.completeEquipartiteGraph 4 s

def classPart (i : Fin 4) : Fin 2 := if i < 2 then 0 else 1

def part {s : ℕ} (v : Vertex s) : Fin 2 := classPart v.1

theorem fibre_card (s : ℕ) (v : Vertex s) : (fibre Prod.fst v).card = s := by
  have h : fibre Prod.fst v = ({v.1} : Finset (Fin 4)) ×ˢ univ := by
    ext ⟨i, j⟩
    simp [fibre, eq_comm]
  rw [h]
  simp

theorem neighbour_card (s : ℕ) (v : Vertex s) :
    (univ.filter fun w => (graph s).Adj v w).card = 3 * s := by
  have h : (univ.filter fun w => (graph s).Adj v w) =
      (univ.erase v.1) ×ˢ (univ : Finset (Fin s)) := by
    ext ⟨i, j⟩
    simp [graph, eq_comm]
  rw [h, card_product]
  simp

theorem common_class : ∀ a b : Fin 4, ∀ k : Fin 2,
    ({classPart a, classPart b, k} : Multiset (Fin 2)) ∈ F0 →
      ∃ c : Fin 4, c ≠ a ∧ c ≠ b ∧ classPart c = k := by decide

theorem admissible_common_card {s : ℕ} (u v : Vertex s) (k : Fin 2)
    (htype : ({part u, part v, k} : Multiset (Fin 2)) ∈ F0) :
    s ≤ (univ.filter fun w => (graph s).Adj u w ∧ (graph s).Adj w v ∧ part w = k).card := by
  obtain ⟨c, hcu, hcv, hck⟩ := common_class u.1 v.1 k htype
  have h := Finset.card_le_card_of_injOn (fun j : Fin s => (c, j))
    (s := univ) (t := univ.filter fun w =>
      (graph s).Adj u w ∧ (graph s).Adj w v ∧ part w = k)
    (fun j _ => by simp [graph, part, Ne.symm hcu, hcv, hck])
    (fun _ _ _ _ h => Prod.mk.inj h |>.2)
  simpa using h

theorem antiEdgeful (s : ℕ) : AntiEdgeful part F0 (graph s) (1 / 4) := by
  intro τ hτ i j k hijk u v _ hu hv
  have htype : ({part u, part v, k} : Multiset (Fin 2)) ∈ F0 := by
    rw [hu, hv, ← hijk]
    exact hτ
  have hc := admissible_common_card u v k htype
  have heq : (1 / 4 : ℝ) * Fintype.card (Vertex s) = s := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  rw [heq]
  exact_mod_cast hc

theorem hingeSupply (s : ℕ) (hs : 2 ≤ s) : HingeSupply part F0 (graph s) (1 / 64) 6 := by
  apply hingeSupply_of_class_fibres Prod.fst (fun _ _ => Iff.rfl)
    (fun a b h => by simp [part, h]) (s - 1)
  · intro v
    rw [fibre_card]
    omega
  · simp only [Fintype.card_prod, Fintype.card_fin]
    have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
    have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    push_cast
    nlinarith

theorem not_commonNbrRich_two {s : ℕ} (hs : 0 < s) {β : ℝ} (hβ : 0 < β) :
    ¬ CommonNbrRich 2 part (graph s) β := by
  intro h
  let u : Vertex s := (0, ⟨0, hs⟩)
  let v : Vertex s := (1, ⟨0, hs⟩)
  have he : (univ.filter (fun w : Vertex s => part w = 0 ∧
      ∀ x ∈ ({u, v} : Finset (Vertex s)), (graph s).Adj x w)) = ∅ := by
    ext ⟨i, j⟩
    fin_cases i <;> simp [part, classPart, graph, u, v]
  have hc := h {u, v} card_le_two 0
  rw [he] at hc
  simp only [card_empty, Nat.cast_zero, Fintype.card_prod, Fintype.card_fin] at hc
  have hpos : 0 < β * (4 * s : ℕ) := mul_pos hβ (by positivity)
  linarith

theorem not_cn6 {s : ℕ} (hs : 0 < s) {β : ℝ} (hβ : 0 < β) :
    ¬ CN6 part (graph s) β := by
  intro h
  exact not_commonNbrRich_two hs hβ
    (fun R hR i => h R (hR.trans (by decide)) i)

theorem not_commonNbrRich_five {s : ℕ} (hs : 0 < s) {β : ℝ} (hβ : 0 < β) :
    ¬ CommonNbrRich 5 part (graph s) β := by
  intro h
  exact not_commonNbrRich_two hs hβ (fun R hR i => h R (hR.trans (by decide)) i)

end PartitionedTriangleAbsorption.MultipartiteBoundaryStage64
