/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1TemplateBoundsStage233
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The complete F1 template graph and the balance functional

`templateGraph t` is the complete F1-allowed graph on `Fin 4 × Fin t`: all pairs inside a class
and all pairs between opposite sides of `{0,1} | {2,3}`. We prove that an edge vector of zero
signed charge on this graph (`+1` cross, `-2` internal) has balanced block means, i.e. lies in
the range of the constant-block system (`(blocksOf x).Balanced`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1TemplateStage233

open Finset TypedApplicationLinks F1GramInverseStage230 F1BalanceGateStage228

variable {t : ℕ}

/-- The complete F1 template graph. -/
def templateGraph (t : ℕ) : SimpleGraph (Fin 4 × Fin t) where
  Adj u v := u ≠ v ∧ (u.1 = v.1 ∨ Opp u.1 v.1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h' => Or.inl h'.symm) (fun h' => Or.inr (opp_symm h'))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (t : ℕ) : DecidableRel (templateGraph t).Adj := fun u v => by
  unfold templateGraph; infer_instance

theorem templateGraph_adj {u v : Fin 4 × Fin t} :
    (templateGraph t).Adj u v ↔ u ≠ v ∧ (u.1 = v.1 ∨ Opp u.1 v.1) := Iff.rfl

/-- A completing vertex is adjacent to both endpoints in the template. -/
theorem ok_template_adj {u v w : Fin 4 × Fin t} (h : Ok u v w) :
    (templateGraph t).Adj u w ∧ (templateGraph t).Adj v w := by
  obtain ⟨hwu, hwv, hf⟩ := h
  rw [f1_type_iff] at hf
  refine ⟨⟨Ne.symm hwu, ?_⟩, ⟨Ne.symm hwv, ?_⟩⟩
  · rcases hf with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact Or.inr h2
    · exact Or.inl h1
    · rw [← h1]; exact Or.inr (opp_symm h2)
  · rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [← h1]; exact Or.inr h2
    · rw [← h1]; exact Or.inr (opp_symm h2)
    · exact Or.inl h1

/-- Weighted handshake lemma (as in `BalanceLedgerF1.sum_edges_two`). -/
theorem sum_edges_two' {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℝ) :
    2 * ∑ e ∈ G.edgeFinset, f e = ∑ v, ∑ z ∈ univ.filter (G.Adj v), f s(v, z) := by
  have h1 : ∑ d : G.Dart, f d.edge = ∑ e ∈ G.edgeFinset, 2 * f e := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun d : G.Dart => d.edge) (t := G.edgeFinset)
      (fun d _ => by simp)]
    refine sum_congr rfl fun e he => ?_
    rw [sum_congr rfl (fun d hd => by rw [(mem_filter.mp hd).2])]
    rw [sum_const, G.dart_edge_fiber_card e (SimpleGraph.mem_edgeFinset.mp he)]
    simp
  have h2 : ∑ d : G.Dart, f d.edge = ∑ v, ∑ z ∈ univ.filter (G.Adj v), f s(v, z) := by
    rw [← Finset.sum_fiberwise (g := fun d : G.Dart => d.fst)]
    refine sum_congr rfl fun v _ => ?_
    refine Finset.sum_bij (fun d _ => d.snd) ?_ ?_ ?_ ?_
    · intro d hd; simp only [mem_filter, mem_univ, true_and] at hd ⊢; rw [← hd]; exact d.adj
    · intro d hd d' hd' h
      simp only [mem_filter, mem_univ, true_and] at hd hd'
      exact SimpleGraph.Dart.ext _ _ (Prod.ext (hd.trans hd'.symm) h)
    · intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      exact ⟨⟨(v, z), hz⟩, by simp, rfl⟩
    · intro d hd
      have hd' : d.fst = v := (mem_filter.mp hd).2
      show f s(d.fst, d.snd) = f s(v, d.snd)
      rw [hd']
  rw [mul_sum, ← h1, h2]

theorem pairCharge_of_eq (i : Fin 4) : pairCharge i i = -2 := by simp [pairCharge]

theorem pairCharge_of_opp {i j : Fin 4} (h : Opp i j) : pairCharge i j = 1 := by
  unfold pairCharge Opp at *; rw [if_neg h]

/-- The ordered charge sum at one vertex. -/
theorem vertex_charge_sum (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) :
    (∑ z ∈ univ.filter ((templateGraph t).Adj (i, a)), charge Prod.fst s((i, a), z) * x s((i, a), z))
      = -2 * rI x i a + (rC x i a (first1 i) + rC x i a (second1 i)) := by
  rw [sum_filter, Fintype.sum_prod_type]
  have hc : ∀ c : Fin 4, (∑ k : Fin t, if (templateGraph t).Adj (i, a) (c, k) then
      charge Prod.fst s((i, a), (c, k)) * x s((i, a), (c, k)) else 0) =
      (if c = i then -2 * rI x i a else 0) + (if Opp i c then rC x i a c else 0) := by
    intro c
    by_cases hci : c = i
    · subst hci
      have hno : ¬ Opp c c := fun h => h Iff.rfl
      rw [if_pos rfl, if_neg hno, add_zero, rI, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      by_cases hk : k = a
      · subst hk; simp
      · have hadj : (templateGraph t).Adj (c, a) (c, k) :=
          ⟨fun e => hk (Prod.ext_iff.mp e).2.symm, Or.inl rfl⟩
        rw [if_pos hadj, if_neg hk]
        simp [charge, pairCharge_of_eq]
    · rw [if_neg hci, zero_add]
      by_cases ho : Opp i c
      · rw [if_pos ho, rC]
        refine sum_congr rfl fun k _ => ?_
        have hadj : (templateGraph t).Adj (i, a) (c, k) :=
          ⟨fun e => hci (Prod.ext_iff.mp e).1.symm, Or.inr ho⟩
        rw [if_pos hadj]
        simp [charge, pairCharge_of_opp ho]
      · rw [if_neg ho]
        refine sum_eq_zero fun k _ => if_neg ?_
        rintro ⟨-, h | h⟩
        · exact hci h.symm
        · exact ho h
  rw [sum_congr rfl fun c _ => hc c, sum_add_distrib, sum_ite_eq', sum_opp]
  simp

/-- **Zero charge on the template forces balanced block means.** -/
theorem blocksOf_balanced (ht : 4 ≤ t) (x : Sym2 (Fin 4 × Fin t) → ℝ)
    (hx : ∑ e ∈ (templateGraph t).edgeFinset, charge Prod.fst e * x e = 0) :
    (blocksOf x).Balanced := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (t : ℝ) ≠ 0 := by linarith
  have h1 : (t : ℝ) - 1 ≠ 0 := by linarith
  have h2 := sum_edges_two' (templateGraph t) (fun e => charge Prod.fst e * x e)
  rw [hx, mul_zero, Fintype.sum_prod_type] at h2
  simp only [vertex_charge_sum] at h2
  simp only [sum_add_distrib, ← mul_sum, Fin.sum_univ_four] at h2
  have hmI : ∀ i, ∑ a, rI x i a = t * (t - 1) * mI x i := by
    intro i; unfold mI; field_simp
  have hmC : ∀ i j, ∑ a, rC x i a j = t * t * mC x i j := by
    intro i j; unfold mC; field_simp
  simp only [hmI, hmC] at h2
  simp only [show first1 0 = 2 from rfl, show first1 1 = 2 from rfl, show first1 2 = 0 from rfl,
    show first1 3 = 0 from rfl, show second1 0 = 3 from rfl, show second1 1 = 3 from rfl,
    show second1 2 = 1 from rfl, show second1 3 = 1 from rfl] at h2
  rw [mC_symm x 2 0, mC_symm x 2 1, mC_symm x 3 0, mC_symm x 3 1] at h2
  have : (t : ℝ) * (2 * ((t - 1) * (mI x 0 + mI x 1 + mI x 2 + mI x 3) -
      t * (mC x 0 2 + mC x 0 3 + mC x 1 2 + mC x 1 3))) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h0
  · unfold Blocks.Balanced blocksOf
    dsimp (config := { failIfUnchanged := false }) only
    rw [show 2 * (mI x 0 / (2 * t) + mI x 1 / (2 * t) + mI x 2 / (2 * t) + mI x 3 / (2 * t)) =
        (mI x 0 + mI x 1 + mI x 2 + mI x 3) / t by field_simp,
      show mC x 0 2 / (t - 1) + mC x 0 3 / (t - 1) + mC x 1 2 / (t - 1) + mC x 1 3 / (t - 1) =
        (mC x 0 2 + mC x 0 3 + mC x 1 2 + mC x 1 3) / (t - 1) by field_simp,
      div_eq_div_iff h0 h1]
    linear_combination h / 2

end PartitionedTriangleAbsorption.F1TemplateStage233
