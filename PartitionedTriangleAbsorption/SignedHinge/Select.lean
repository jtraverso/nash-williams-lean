/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups
public import PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51
public import Mathlib.Tactic.Linarith

/-! # Explicit physical hinge supply and selection of a vertex-fresh hinge

`HingeSupply p F G β C0` is the **explicit additional hypothesis** of the Stage 53 target:
for every two actual `F`-copies `S, S'` of `G` sharing exactly one edge, some
`i ∈ [6, C0]` has at least `β n^(i-4)` distinct physical edge sets `H ⊆ E(G)` with
`IsHinge p F S S' H` and `|vertSet H| = i`. It is a new, separately named predicate; the
returned `Hingeful` (with its literal `n^(i-2)` convention) is not modified or used.

`exists_hinge_avoiding`: if `2^C(C0+1,2) |U| < β n`, a supplied hinge exists whose support
meets `U` only in its four roots. This is the **vertex-only** (`d = 0`, no blocked edges)
case of the exclusion count: it uses only the accepted Stage 51 count `one_extra_vertex`
and the four-root lemma, summed over the excluded vertices. The general union bound with
blocked edges (owned by the local team) is not needed and not reproduced.

`greedy_disjoint`: a generic greedy lemma producing pairwise vertex-disjoint fresh choices.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

open Classical in
/-- **Explicit physical hinge supply** (the extra hypothesis, counted over actual edge sets). -/
def HingeSupply (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : ℝ) (C0 : ℕ) : Prop :=
  ∀ S S' : Finset V, IsCopy p F G S → IsCopy p F G S' → (triEdges S ∩ triEdges S').card = 1 →
    ∃ i ∈ Icc 6 C0, β * (Fintype.card V : ℝ) ^ (i - 4) ≤
      ((G.edgeFinset.powerset.filter fun H => IsHinge p F S S' H ∧ (vertSet H).card = i).card :
        ℝ)

/-- **Selection of a hinge whose support avoids `U` outside its four roots.** -/
theorem exists_hinge_avoiding {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {β : ℝ} {C0 : ℕ}
    (hsup : HingeSupply p F G β C0) {u v w z : V} (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hS : IsCopy p F G {u, v, w}) (hS' : IsCopy p F G {u, v, z}) (U : Finset V)
    (hU : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * U.card < β * Fintype.card V) :
    ∃ H : Finset (Sym2 V), H ⊆ G.edgeFinset ∧ IsHinge p F {u, v, w} {u, v, z} H ∧
      (vertSet H).card ≤ C0 ∧ ∀ x ∈ vertSet H, x ∈ U → x = u ∨ x = v ∨ x = w ∨ x = z := by
  classical
  have hinter : (triEdges ({u, v, w} : Finset V) ∩ triEdges {u, v, z}).card = 1 := by
    simp [triEdges_three huv huw hvw, triEdges_three huv huz hvz,
      huv, huw, huz, hvw, hvz, hwz]
  obtain ⟨i, hi, hK⟩ := hsup _ _ hS hS' hinter
  obtain ⟨hi6, hiC⟩ := mem_Icc.mp hi
  set n := Fintype.card V with hn
  set K := G.edgeFinset.powerset.filter
    fun H => IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = i with hKdef
  set R : Finset V := {u, v, w, z} with hRdef
  have hRc : R.card = 4 := by simp [R, huv, huw, huz, hvw, hvz, hwz]
  set Bad := (U.filter (· ∉ R)).biUnion
    (fun x => K.filter fun H => x ∈ PhysicalHinge.support H) with hBaddef
  have hroot : ∀ H ∈ K, R ⊆ PhysicalHinge.support H := fun H hH =>
    IsHinge.four_roots H u v w z huv huw huz hvw hvz hwz (mem_filter.mp hH).2.1
  have horder : ∀ H ∈ K, (PhysicalHinge.support H).card = i := fun H hH => by
    rw [← vertSet_eq_support]; exact (mem_filter.mp hH).2.2
  have hone : ∀ x ∈ U.filter (· ∉ R),
      (K.filter fun H => x ∈ PhysicalHinge.support H).card ≤
        n ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2 := by
    intro x hx
    have h1 := RootedAvoidanceCountsStage51.one_extra_vertex K R i x (mem_filter.mp hx).2
      (by omega) hroot horder
    rw [hRc] at h1
    refine h1.trans (Nat.mul_le_mul ?_ ?_)
    · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
    · exact Nat.pow_le_pow_right (by norm_num)
        (Nat.choose_le_choose 2 (by omega))
  have hBadc : Bad.card ≤ U.card * (n ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2) := by
    refine card_biUnion_le.trans ?_
    calc ∑ x ∈ U.filter (· ∉ R), (K.filter fun H => x ∈ PhysicalHinge.support H).card
        ≤ ∑ _x ∈ U.filter (· ∉ R), n ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2 :=
          sum_le_sum hone
      _ = (U.filter (· ∉ R)).card * (n ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ U.card * (n ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2) :=
          Nat.mul_le_mul_right _ (card_filter_le _ _)
  have hnpos : 0 < n := Fintype.card_pos_iff.mpr ⟨u⟩
  have hex : ∃ H ∈ K, H ∉ Bad := by
    by_contra hcon
    push Not at hcon
    have hsub : K ⊆ Bad := fun H hH => hcon H hH
    have hKB : (K.card : ℝ) ≤ (U.card : ℝ) * ((n : ℝ) ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2) := by
      exact_mod_cast (card_le_card hsub).trans hBadc
    have hpow : (n : ℝ) ^ (i - 4) = (n : ℝ) * (n : ℝ) ^ (i - 5) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : (0 : ℝ) < (n : ℝ) ^ (i - 5) := by positivity
    have h2 : (U.card : ℝ) * ((n : ℝ) ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2) <
        β * (n : ℝ) ^ (i - 4) := by
      rw [hpow]
      have := mul_lt_mul_of_pos_right hU hpos
      calc (U.card : ℝ) * ((n : ℝ) ^ (i - 5) * 2 ^ Nat.choose (C0 + 1) 2)
          = 2 ^ Nat.choose (C0 + 1) 2 * U.card * (n : ℝ) ^ (i - 5) := by ring
        _ < β * n * (n : ℝ) ^ (i - 5) := this
        _ = β * (n * (n : ℝ) ^ (i - 5)) := by ring
    have h3 : β * (n : ℝ) ^ (i - 4) ≤ (K.card : ℝ) := by simpa [hKdef] using hK
    linarith
  obtain ⟨H, hHK, hHB⟩ := hex
  have hHK' := mem_filter.mp hHK
  refine ⟨H, mem_powerset.mp hHK'.1, hHK'.2.1, hHK'.2.2 ▸ hiC, ?_⟩
  intro x hxH hxU
  by_contra hxR
  have hxR' : x ∉ R := by
    simp only [R, mem_insert, mem_singleton]; exact hxR
  apply hHB
  refine mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨hxU, hxR'⟩, mem_filter.mpr ⟨hHK, ?_⟩⟩
  rw [← vertSet_eq_support]; exact hxH

omit [Fintype V] [DecidableEq V] in
/-- **Greedy selection of pairwise vertex-disjoint fresh choices.** -/
theorem greedy_disjoint {κ β : Type*} [Inhabited β] (s : Finset κ)
    (fv : κ → β → Finset V) (good : κ → β → Prop) (U₀ : Finset V) (B M : ℕ)
    (hstep : ∀ k ∈ s, ∀ U : Finset V, U₀ ⊆ U → U.card ≤ M →
      ∃ b, good k b ∧ Disjoint (fv k b) U ∧ (fv k b).card ≤ B)
    (hM : U₀.card + s.card * B ≤ M) :
    ∃ f : κ → β, (∀ k ∈ s, good k (f k) ∧ Disjoint (fv k (f k)) U₀ ∧ (fv k (f k)).card ≤ B) ∧
      ∀ k ∈ s, ∀ k' ∈ s, k ≠ k' → Disjoint (fv k (f k)) (fv k' (f k')) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => default, by simp, by simp⟩
  | insert a s ha ih =>
    rw [card_insert_of_notMem ha] at hM
    obtain ⟨f, hf, hfd⟩ := ih (fun k hk => hstep k (mem_insert_of_mem hk)) (by nlinarith)
    set U := U₀ ∪ s.biUnion (fun k => fv k (f k)) with hU
    have hUc : U.card ≤ M := by
      refine (card_union_le _ _).trans ?_
      have : (s.biUnion fun k => fv k (f k)).card ≤ s.card * B := by
        refine card_biUnion_le.trans ?_
        calc ∑ k ∈ s, (fv k (f k)).card ≤ ∑ _k ∈ s, B := sum_le_sum fun k hk => (hf k hk).2.2
          _ = s.card * B := by rw [sum_const, smul_eq_mul]
      nlinarith
    obtain ⟨b, hb, hbU, hbB⟩ := hstep a (mem_insert_self a s) U subset_union_left hUc
    refine ⟨Function.update f a b, ?_, ?_⟩
    · intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · simp only [Function.update_self]
        exact ⟨hb, hbU.mono_right subset_union_left, hbB⟩
      · have hka : k ≠ a := fun h => ha (h ▸ hk)
        simp only [Function.update_of_ne hka]
        exact hf k hk
    · have hfa : ∀ k ∈ s, Disjoint (fv a b) (fv k (f k)) := fun k hk =>
        hbU.mono_right ((subset_biUnion_of_mem (fun k => fv k (f k)) hk).trans
          subset_union_right)
      intro k hk k' hk' hkk'
      by_cases hka : k = a <;> by_cases hk'a : k' = a
      · exact absurd (hka.trans hk'a.symm) hkk'
      · subst hka
        have hk's : k' ∈ s := (mem_insert.mp hk').resolve_left hk'a
        simp only [Function.update_self, Function.update_of_ne hk'a]
        exact hfa k' hk's
      · subst hk'a
        have hks : k ∈ s := (mem_insert.mp hk).resolve_left hka
        simp only [Function.update_self, Function.update_of_ne hka]
        exact (hfa k hks).symm
      · have hks : k ∈ s := (mem_insert.mp hk).resolve_left hka
        have hk's : k' ∈ s := (mem_insert.mp hk').resolve_left hk'a
        simp only [Function.update_of_ne hka, Function.update_of_ne hk'a]
        exact hfd k hks k' hk's hkk'

end PartitionedTriangleAbsorption.SignedHinge
