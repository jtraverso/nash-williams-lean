/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1BalanceGateStage228

/-!
# The edge–triangle incidence of the complete F1 template

Vertices are `Fin 4 × Fin t` (class, index). The F1 triangles of the complete template are
all three-sets whose class multiset belongs to `F1`. For an edge vector `Y` we compute the
Gram operator `(B Bᵀ Y)(uv) = ∑_{T ∋ uv} ∑_{f ∈ T} Y f` of the REAL incidence `B` explicitly:

* on an internal edge (`u.1 = v.1`): `2t Y(uv) + ∑_{c opposite} (row_c(u) + row_c(v))`;
* on a cross edge (`u.1`, `v.1` opposite): `(2t-4) Y(uv) + row_{u.1}(u) + row_{v.1}(v) +
  row_{v.1}(u) + row_{u.1}(v)`,

where `row_c(u) = ∑_{k} Y(u,(c,k))` and `Y` vanishes on the diagonal.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1TemplateStage233

open Finset TypedApplicationLinks F1BalanceGateStage228

/-- Opposite sides of the coarse partition `{0,1} | {2,3}`. -/
def Opp (i j : Fin 4) : Prop := ¬ (i.val < 2 ↔ j.val < 2)

instance : DecidableRel Opp := fun i j => by unfold Opp; infer_instance

theorem opp_symm {i j : Fin 4} (h : Opp i j) : Opp j i := by
  unfold Opp at *; tauto

theorem opp_ne {i j : Fin 4} (h : Opp i j) : i ≠ j := by
  rintro rfl; exact h Iff.rfl

theorem f1_type_iff (a b c : Fin 4) : ({a, b, c} : Multiset (Fin 4)) ∈ F1 ↔
    (a = b ∧ Opp a c) ∨ (a = c ∧ Opp a b) ∨ (b = c ∧ Opp b a) := by
  revert a b c; decide

/-- The two classes opposite to `i`. -/
theorem sum_opp (i : Fin 4) (f : Fin 4 → ℝ) :
    (∑ c, if Opp i c then f c else 0) = f (first1 i) + f (second1 i) := by
  fin_cases i <;> simp [Fin.sum_univ_four, Opp, first1, second1]

theorem opp_first1 (i : Fin 4) : Opp i (first1 i) := by fin_cases i <;> decide
theorem opp_second1 (i : Fin 4) : Opp i (second1 i) := by fin_cases i <;> decide

variable {t : ℕ}

/-- `w` completes the pair `u v` to an F1 triangle. -/
def Ok (u v w : Fin 4 × Fin t) : Prop :=
  w ≠ u ∧ w ≠ v ∧ ({u.1, v.1, w.1} : Multiset (Fin 4)) ∈ F1

instance (u v w : Fin 4 × Fin t) : Decidable (Ok u v w) := by unfold Ok; infer_instance

/-- The F1 triangles of the complete template. -/
noncomputable def tstar (t : ℕ) : Finset (Finset (Fin 4 × Fin t)) := by
  classical exact univ.filter fun s => IsTypedTri Prod.fst F1 s

theorem mem_tstar {s : Finset (Fin 4 × Fin t)} : s ∈ tstar t ↔ IsTypedTri Prod.fst F1 s := by
  classical simp [tstar]

/-- Triangles of the template through `uv` are indexed by their third vertex. -/
theorem sum_tstar_edge (u v : Fin 4 × Fin t) (huv : u ≠ v) (g : Finset (Fin 4 × Fin t) → ℝ) :
    (∑ s ∈ tstar t with s(u, v) ∈ triEdges s, g s) =
      ∑ w, if Ok u v w then g {u, v, w} else 0 := by
  classical
  rw [← sum_filter]
  have hinj : Set.InjOn (fun w => ({u, v, w} : Finset (Fin 4 × Fin t)))
      (univ.filter (Ok u v) : Finset _) := by
    intro w hw w' hw' heq
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
    have : w' ∈ ({u, v, w} : Finset _) := by
      simp (config := { failIfUnchanged := false }) only at heq; rw [heq]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact absurd h hw'.1
    · exact absurd h hw'.2.1
    · exact h.symm
  rw [← sum_image hinj]
  congr 1
  ext s
  simp only [mem_image, mem_filter, mem_univ, true_and, mem_tstar]
  constructor
  · rintro ⟨⟨hcard, htype⟩, he⟩
    obtain ⟨hu, hv, -⟩ := TypedNibble.mem_triEdges_iff.mp he
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hcard
    have hrest : ∃ w, w ≠ u ∧ w ≠ v ∧ ({a, b, c} : Finset _) = {u, v, w} := by
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl huv
        | exact ⟨c, hac.symm, hbc.symm, rfl⟩
        | exact ⟨b, hab.symm, hbc, by ext; simp; tauto⟩
        | exact ⟨c, hbc.symm, hac.symm, by ext; simp; tauto⟩
        | exact ⟨a, hab, hac, by ext; simp; tauto⟩
        | exact ⟨b, hbc, hab.symm, by ext; simp; tauto⟩
        | exact ⟨a, hac, hab, by ext; simp; tauto⟩
    obtain ⟨w, hwu, hwv, hs⟩ := hrest
    refine ⟨w, ⟨hwu, hwv, ?_⟩, hs.symm⟩
    rw [hs, map_three Prod.fst huv hwu.symm hwv.symm] at htype
    exact htype
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [card_eq_three]; exact ⟨u, v, w, huv, hw.1.symm, hw.2.1.symm, rfl⟩
    · rw [map_three Prod.fst huv hw.1.symm hw.2.1.symm]; exact hw.2.2
    · exact TypedNibble.mem_triEdges_iff.mpr ⟨by simp, by simp, huv⟩

/-- The Gram operator `B Bᵀ` of the real edge–triangle incidence of the complete template. -/
noncomputable def gram (Y : Sym2 (Fin 4 × Fin t) → ℝ) (e : Sym2 (Fin 4 × Fin t)) : ℝ :=
  load (tstar t) (fun s => ∑ f ∈ triEdges s, Y f) e

theorem gram_mk (Y : Sym2 (Fin 4 × Fin t) → ℝ) (u v : Fin 4 × Fin t) (huv : u ≠ v) :
    gram Y s(u, v) =
      ∑ w, if Ok u v w then Y s(u, v) + Y s(u, w) + Y s(v, w) else 0 := by
  unfold gram load
  rw [sum_tstar_edge u v huv]
  refine sum_congr rfl fun w _ => ?_
  split_ifs with h
  · exact sum_triEdges_three Y huv h.1.symm h.2.1.symm
  · rfl

/-- Full row sum of an edge vector at `u` into class `c`. -/
def rowF (Y : Sym2 (Fin 4 × Fin t) → ℝ) (u : Fin 4 × Fin t) (c : Fin 4) : ℝ :=
  ∑ k, Y s(u, (c, k))

theorem ok_internal {u v w : Fin 4 × Fin t} (h : u.1 = v.1) :
    Ok u v w ↔ Opp u.1 w.1 := by
  unfold Ok
  rw [f1_type_iff, ← h]
  constructor
  · rintro ⟨-, -, h1 | h1 | h1⟩
    · exact h1.2
    · exact absurd h1.2 (fun h2 => h2 Iff.rfl)
    · exact absurd h1.2 (fun h2 => h2 Iff.rfl)
  · intro ho
    refine ⟨fun hw => ?_, fun hw => ?_, Or.inl ⟨rfl, ho⟩⟩
    · exact opp_ne ho (by rw [hw])
    · exact opp_ne ho (by rw [hw, h])

theorem ok_cross {u v w : Fin 4 × Fin t} (h : Opp u.1 v.1) :
    Ok u v w ↔ (w.1 = u.1 ∧ w ≠ u) ∨ (w.1 = v.1 ∧ w ≠ v) := by
  unfold Ok
  rw [f1_type_iff]
  have hne := opp_ne h
  constructor
  · rintro ⟨hwu, hwv, h1 | h1 | h1⟩
    · exact absurd h1.1 hne
    · exact Or.inl ⟨h1.1.symm, hwu⟩
    · exact Or.inr ⟨h1.1.symm, hwv⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨h2, fun hw => ?_, Or.inr (Or.inl ⟨h1.symm, h⟩)⟩
      exact hne (by rw [← h1, hw])
    · refine ⟨fun hw => ?_, h2, Or.inr (Or.inr ⟨h1.symm, opp_symm h⟩)⟩
      exact hne (by rw [← hw, h1])

/-- Removing one index from a sum over `Fin t`. -/
theorem sum_ne_index (f : Fin t → ℝ) (j : Fin t) :
    (∑ k, if k = j then 0 else f k) = (∑ k, f k) - f j := by
  calc (∑ k, if k = j then 0 else f k) = ∑ k, (f k - if k = j then f k else 0) :=
        sum_congr rfl fun k _ => by split_ifs <;> simp
    _ = (∑ k, f k) - f j := by rw [sum_sub_distrib, sum_ite_eq']; simp

/-- **Gram operator on an internal edge.** -/
theorem gram_internal (Y : Sym2 (Fin 4 × Fin t) → ℝ) (u v : Fin 4 × Fin t) (huv : u ≠ v)
    (h : u.1 = v.1) :
    gram Y s(u, v) = 2 * t * Y s(u, v) +
      ((rowF Y u (first1 u.1) + rowF Y v (first1 u.1)) +
        (rowF Y u (second1 u.1) + rowF Y v (second1 u.1))) := by
  rw [gram_mk Y u v huv]
  simp_rw [ok_internal h]
  rw [Fintype.sum_prod_type]
  simp (config := { failIfUnchanged := false }) only
  have : ∀ c : Fin 4, (∑ k : Fin t, if Opp u.1 c then
      Y s(u, v) + Y s(u, (c, k)) + Y s(v, (c, k)) else 0) =
      if Opp u.1 c then t * Y s(u, v) + (rowF Y u c + rowF Y v c) else 0 := by
    intro c
    split_ifs
    · simp [rowF, sum_add_distrib]; ring
    · simp
  rw [sum_congr rfl fun c _ => this c, sum_opp]
  ring

/-- **Gram operator on a cross edge** (for `Y` vanishing on the diagonal). -/
theorem gram_cross (Y : Sym2 (Fin 4 × Fin t) → ℝ) (hdiag : ∀ a, Y s(a, a) = 0)
    (u v : Fin 4 × Fin t) (h : Opp u.1 v.1) :
    gram Y s(u, v) = (2 * t - 4) * Y s(u, v) +
      (rowF Y u u.1 + rowF Y v v.1 + rowF Y u v.1 + rowF Y v u.1) := by
  have hne : u.1 ≠ v.1 := opp_ne h
  have huv : u ≠ v := fun e => hne (by rw [e])
  rw [gram_mk Y u v huv]
  simp_rw [ok_cross h]
  rw [Fintype.sum_prod_type]
  simp (config := { failIfUnchanged := false }) only
  have hsplit : ∀ c : Fin 4, (∑ k : Fin t,
      if (c = u.1 ∧ (c, k) ≠ u) ∨ (c = v.1 ∧ (c, k) ≠ v) then
        Y s(u, v) + Y s(u, (c, k)) + Y s(v, (c, k)) else 0) =
      (if c = u.1 then
        (∑ k : Fin t, if k = u.2 then 0 else Y s(u, v) + Y s(u, (c, k)) + Y s(v, (c, k)))
        else 0) +
      (if c = v.1 then
        (∑ k : Fin t, if k = v.2 then 0 else Y s(u, v) + Y s(u, (c, k)) + Y s(v, (c, k)))
        else 0) := by
    intro c
    by_cases hcu : c = u.1
    · subst hcu
      rw [if_pos rfl, if_neg hne, add_zero]
      refine sum_congr rfl fun k _ => ?_
      by_cases hk : k = u.2
      · rw [if_pos hk, if_neg]
        rintro (⟨-, h2⟩ | ⟨h1, -⟩)
        · exact h2 (by rw [hk])
        · exact hne h1
      · have : (u.1, k) ≠ u := fun e => hk (by rw [← e])
        rw [if_neg hk, if_pos (Or.inl ⟨rfl, this⟩)]
    · rw [if_neg hcu, zero_add]
      by_cases hcv : c = v.1
      · subst hcv
        rw [if_pos rfl]
        refine sum_congr rfl fun k _ => ?_
        by_cases hk : k = v.2
        · rw [if_pos hk, if_neg]
          rintro (⟨h1, -⟩ | ⟨-, h2⟩)
          · exact hcu h1
          · exact h2 (by rw [hk])
        · have : (v.1, k) ≠ v := fun e => hk (by rw [← e])
          rw [if_neg hk, if_pos (Or.inr ⟨rfl, this⟩)]
      · rw [if_neg hcv]
        exact sum_eq_zero fun k _ => if_neg (by
          rintro (⟨h1, -⟩ | ⟨h1, -⟩)
          · exact hcu h1
          · exact hcv h1)
  rw [sum_congr rfl fun c _ => hsplit c, sum_add_distrib, sum_ite_eq', sum_ite_eq']
  simp only [mem_univ, if_true]
  rw [sum_ne_index, sum_ne_index]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : ((u.1, u.2) : Fin 4 × Fin t) = u := rfl
  have e2 : ((v.1, v.2) : Fin 4 × Fin t) = v := rfl
  rw [e1, e2, hdiag u, hdiag v, Sym2.eq_swap (a := v) (b := u)]
  unfold rowF
  ring

end PartitionedTriangleAbsorption.F1TemplateStage233
