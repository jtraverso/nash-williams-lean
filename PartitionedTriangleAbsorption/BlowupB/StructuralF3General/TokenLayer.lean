/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.TokenLedger

/-! # A charge layer with physically realized tokens

Input: a *predicate refiner* `E` of a reserve `X0` on an arbitrary vertex type `W`: a fixed
remainder `R0` and a fixed library of loopless even pieces such that every leftover `L ⊆ X0`
with `Q L` is exactly partitioned, together with `R0`, by pairwise disjoint library pieces.
A charge `χ` (with respect to a part function `p`) is given, and every piece charge is a
multiple of a unit `u ≠ 0`.

Tokens are **not** fresh vertices: a token realization `tokE` sends every token identity to an
actual edge set on `W` (for example a physical cycle of a host graph). It must be pairwise
disjoint on the token identities in use, avoid `R0 ∪ X0`, be loopless and even, and have
charge `+u` (plus tokens) or `-u` (minus tokens). A second charge `χ'` is required to vanish on
tokens, so that it is preserved by the layer.

`token_layer` builds a new predicate refiner for `Q L ∧ charge χ p L = 0` whose pieces all have
charge zero. The token identities and the robust matching graph (`exists_robust`) are fixed
before any leftover. The token realization is requested from a *supply hypothesis* for every
token set of a stated size; the supply is proved separately for the physical host.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset RefinerF0 TypedRefinerCharge AntiEdgeSelection

variable {W : Type*} [DecidableEq W] {κ : Type*}

/-- A refiner of the reserve `X0` for the leftovers satisfying `Q`. -/
structure PredRefiner (κ : Type*) (X0 : Finset (Sym2 W)) (Q : Finset (Sym2 W) → Prop) where
  lib : Finset κ
  P : κ → Finset (Sym2 W)
  R0 : Finset (Sym2 W)
  loopP : ∀ i ∈ lib, ∀ e ∈ P i, ¬ e.IsDiag
  evenP : ∀ i ∈ lib, ∀ w, Even (incidentLoad (P i) w)
  subP : ∀ i ∈ lib, P i ⊆ R0 ∪ X0
  disjRX : Disjoint R0 X0
  refines : ∀ L ⊆ X0, Q L → ∃ T ⊆ lib, (T : Set κ).PairwiseDisjoint P ∧ T.biUnion P = R0 ∪ L

/-- A predicate refiner refines every leftover whose divisibility implies `Q`. -/
theorem PredRefiner.refinesReserve {t : ℕ} {p : W → Fin t} {F : Finset (Multiset (Fin t))}
    {X0 : Finset (Sym2 W)} {Q : Finset (Sym2 W) → Prop} (E : PredRefiner κ X0 Q)
    (hQ : ∀ L ⊆ X0, IsIntDiv p F L → Q L) :
    RefinerAssembly.RefinesReserve (p := p) (F := F) E.lib E.P X0 E.R0 :=
  fun L hL hdiv => E.refines L hL (hQ L hL hdiv)

/-- A physical token realization of the token identities `S`. -/
structure TokReal {t : ℕ} (χ χ' : Fin t → Fin t → ℤ) (p : W → Fin t) (u : ℤ) (g : ℕ)
    (A : Finset (Sym2 W)) (S : Finset (Tok κ)) (tokE : Tok κ → Finset (Sym2 W)) : Prop where
  disj : (S : Set (Tok κ)).PairwiseDisjoint tokE
  avoid : ∀ τ ∈ S, Disjoint (tokE τ) A
  loop : ∀ τ ∈ S, ∀ e ∈ tokE τ, ¬ e.IsDiag
  even : ∀ τ ∈ S, ∀ w, Even (incidentLoad (tokE τ) w)
  chg : ∀ τ ∈ S, charge χ p (tokE τ) = if τ.sign then u else -u
  chg' : ∀ τ ∈ S, charge χ' p (tokE τ) = 0
  card : ∀ τ ∈ S, (tokE τ).card ≤ g

/-- Old edges of a library index. -/
def oldP (P : κ → Finset (Sym2 W)) : JIdx κ → Finset (Sym2 W)
  | Sum.inl i => P i
  | Sum.inr _ => ∅

/-- The new piece: old edges and the realized tokens. -/
noncomputable def newP [DecidableEq κ] (A : Ledger κ) (P : κ → Finset (Sym2 W))
    (tokE : Tok κ → Finset (Sym2 W)) (j : JIdx κ) : Finset (Sym2 W) :=
  oldP P j ∪ (A.ids j).biUnion tokE

section Lemmas

variable {t : ℕ} {χ χ' : Fin t → Fin t → ℤ} {p : W → Fin t} {u : ℤ} {g : ℕ}
  {B : Finset (Sym2 W)} {S : Finset (Tok κ)} {tokE : Tok κ → Finset (Sym2 W)}

theorem TokReal.disjoint_biUnion (h : TokReal χ χ' p u g B S tokE) {S1 S2 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) (h2 : S2 ⊆ S) (h12 : Disjoint S1 S2) :
    Disjoint (S1.biUnion tokE) (S2.biUnion tokE) := by
  rw [disjoint_biUnion_left]
  intro a ha
  rw [disjoint_biUnion_right]
  intro b hb
  exact h.disj (h1 ha) (h2 hb) (fun hab => disjoint_left.mp h12 ha (hab ▸ hb))

theorem TokReal.avoid_biUnion (h : TokReal χ χ' p u g B S tokE) {S1 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) : Disjoint (S1.biUnion tokE) B := by
  rw [disjoint_biUnion_left]
  exact fun a ha => h.avoid a (h1 ha)

theorem TokReal.even_biUnion (h : TokReal χ χ' p u g B S tokE) {S1 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) : ∀ w, Even (incidentLoad (S1.biUnion tokE) w) :=
  OnePart.even_incidentLoad_biUnion S1 tokE (h.disj.subset h1) (fun a ha => h.even a (h1 ha))

theorem TokReal.charge_biUnion (h : TokReal χ χ' p u g B S tokE) (χ0 : Fin t → Fin t → ℤ)
    {S1 : Finset (Tok κ)} (h1 : S1 ⊆ S) :
    charge χ0 p (S1.biUnion tokE) = ∑ τ ∈ S1, charge χ0 p (tokE τ) :=
  TypedRefinerCharge.charge_biUnion χ0 p S1 tokE (h.disj.subset h1)

theorem TokReal.card_biUnion_le (h : TokReal χ χ' p u g B S tokE) {S1 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) : (S1.biUnion tokE).card ≤ g * S1.card := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ a ∈ S1, (tokE a).card ≤ ∑ _a ∈ S1, g := sum_le_sum fun a ha => h.card a (h1 ha)
    _ = g * S1.card := by rw [sum_const, smul_eq_mul, mul_comm]

end Lemmas

theorem incidentLoad_biUnion_le {ι : Type*} (s : Finset ι) (E : ι → Finset (Sym2 W)) (w : W) :
    incidentLoad (s.biUnion E) w ≤ ∑ i ∈ s, incidentLoad (E i) w := by
  unfold incidentLoad
  rw [filter_biUnion]
  exact card_biUnion_le

/-- Charge of the token identities of a parity piece. -/
theorem sum_sign_idsPar [DecidableEq κ] (A : Ledger κ) {i : κ} (hi : i ∈ A.lib) (u : ℤ) :
    ∑ τ ∈ A.idsPar i, (if τ.sign then u else -u) = -u * A.mc i + u * A.pc i := by
  unfold Ledger.idsPar
  rw [sum_union]
  · rw [sum_image, sum_image]
    · simp [Tok.sign]; ring
    · intro a _ b _ h; simpa using h
    · intro a ha b hb h
      simp only [Tok.vm.injEq] at h
      have := A.slot_inj (A.mem_D_false hi (mem_range.mp ha)) (A.mem_D_false hi (mem_range.mp hb)) h
      simpa using this
  · rw [disjoint_left]
    intro τ h1 h2
    obtain ⟨k, -, rfl⟩ := mem_image.mp h1
    obtain ⟨k', -, h⟩ := mem_image.mp h2
    simp at h

/-- **The token layer.** -/
theorem token_layer {X0 : Finset (Sym2 W)} {Q : Finset (Sym2 W) → Prop}
    (E : PredRefiner κ X0 Q) (hQ0 : Q ∅) {t : ℕ} (χ χ' : Fin t → Fin t → ℤ) (p : W → Fin t)
    (u : ℤ) (hu : u ≠ 0) (hdvd : ∀ i ∈ E.lib, u ∣ charge χ p (E.P i)) (g : ℕ)
    (Extra : Finset (Tok κ) → (Tok κ → Finset (Sym2 W)) → Prop)
    (hsupply : ∀ S : Finset (Tok κ),
      S.card ≤ 9 * ∑ i ∈ E.lib, (charge χ p (E.P i) / u).natAbs →
      ∃ tokE, TokReal χ χ' p u g (E.R0 ∪ X0) S tokE ∧ Extra S tokE) :
    ∃ (S : Finset (Tok κ)) (tokE : Tok κ → Finset (Sym2 W))
      (E' : PredRefiner (JIdx κ) X0 (fun L => Q L ∧ charge χ p L = 0)),
      TokReal χ χ' p u g (E.R0 ∪ X0) S tokE ∧ Extra S tokE ∧
      S.card ≤ 9 * ∑ i ∈ E.lib, (charge χ p (E.P i) / u).natAbs ∧
      E'.R0 = E.R0 ∪ S.biUnion tokE ∧
      (∀ j ∈ E'.lib, charge χ p (E'.P j) = 0) ∧
      ((∀ i ∈ E.lib, charge χ' p (E.P i) = 0) → ∀ j ∈ E'.lib, charge χ' p (E'.P j) = 0) ∧
      (∀ j ∈ E'.lib, (E'.P j).card ≤ 2 * g ∨
        ∃ i ∈ E.lib, (E'.P j).card ≤ (E.P i).card + g * (charge χ p (E.P i) / u).natAbs) ∧
      (∀ w, ∑ j ∈ E'.lib, incidentLoad (E'.P j) w ≤
        ∑ i ∈ E.lib, incidentLoad (E.P i) w + 44 * ∑ τ ∈ S, incidentLoad (tokE τ) w) ∧
      E'.lib.card ≤ E.lib.card + 97 * ∑ i ∈ E.lib, (charge χ p (E.P i) / u).natAbs := by
  classical
  set A : Ledger κ := ⟨E.lib, fun i => charge χ p (E.P i) / u⟩ with hA
  have hAc : ∀ i ∈ E.lib, charge χ p (E.P i) = u * A.c i := fun i hi =>
    (Int.mul_ediv_cancel' (hdvd i hi)).symm
  set K : ℤ := charge χ p E.R0 / u with hK
  -- charge conservation for every valid selection
  have hcons : ∀ T ⊆ E.lib, (T : Set κ).PairwiseDisjoint E.P → ∀ L ⊆ X0,
      charge χ p L = 0 → T.biUnion E.P = E.R0 ∪ L → ∑ i ∈ T, A.c i = K := by
    intro T hT hdisT L hL hq hU
    have h1 : charge χ p (T.biUnion E.P) = ∑ i ∈ T, charge χ p (E.P i) :=
      TypedRefinerCharge.charge_biUnion _ _ _ _ hdisT
    have hdis : Disjoint E.R0 L := disjoint_of_subset_right hL E.disjRX
    rw [hU, charge_union _ _ hdis, hq, add_zero] at h1
    have h2 : charge χ p E.R0 = u * ∑ i ∈ T, A.c i := by
      rw [h1, mul_sum]; exact sum_congr rfl fun i hi => hAc i (hT hi)
    rw [hK, h2, Int.mul_ediv_cancel_left _ hu]
  obtain ⟨T0, hT0, hdis0, hU0⟩ := E.refines ∅ (empty_subset _) hQ0
  have hs : A.sNum K ≤ A.z := by
    rw [← A.card_Zs_eq hT0 (hcons T0 hT0 hdis0 ∅ (empty_subset _) (charge_empty _ _) hU0)]
    have := card_le_card (A.Zs_subset hT0)
    simpa using this
  obtain ⟨m, H, hm, hHfst, hHsnd, hdx, hdy, hmatch⟩ := exists_robust A.z (A.sNum K) hs
  set n := m + A.sNum K with hn
  set S0 := A.allIds n m with hS0
  have hzE : A.z = ∑ i ∈ E.lib, (charge χ p (E.P i) / u).natAbs := A.z_eq
  have hS0card : S0.card ≤ 9 * ∑ i ∈ E.lib, (charge χ p (E.P i) / u).natAbs := by
    have := A.card_allIds_le n m
    rw [← hS0] at this
    rw [← hzE]; omega
  obtain ⟨tokE, hreal, hextra⟩ := hsupply S0 hS0card
  have hidsS : ∀ j ∈ A.indices H, A.ids j ⊆ S0 := fun j hj =>
    A.ids_subset_allIds hHfst hHsnd hj
  have hlibI : ∀ i, (Sum.inl i : JIdx κ) ∈ A.indices H → i ∈ E.lib := by
    intro i hi
    simpa [Ledger.indices] using hi
  have holdSub : ∀ j ∈ A.indices H, oldP E.P j ⊆ E.R0 ∪ X0 := by
    intro j hj
    rcases j with i | j
    · exact E.subP i (hlibI i hj)
    · exact empty_subset _
  have holdLoop : ∀ j ∈ A.indices H, ∀ e ∈ oldP E.P j, ¬ e.IsDiag := by
    intro j hj
    rcases j with i | j
    · exact E.loopP i (hlibI i hj)
    · simp [oldP]
  have holdEven : ∀ j ∈ A.indices H, ∀ w, Even (incidentLoad (oldP E.P j) w) := by
    intro j hj
    rcases j with i | j
    · exact E.evenP i (hlibI i hj)
    · intro w; simp [oldP, incidentLoad]
  have hdisOT : ∀ j ∈ A.indices H, ∀ S1 ⊆ S0, Disjoint (oldP E.P j) (S1.biUnion tokE) :=
    fun j hj S1 hS1 => ((hreal.avoid_biUnion hS1).mono_right (holdSub j hj)).symm
  set Rn := E.R0 ∪ S0.biUnion tokE with hRn
  let E' : PredRefiner (JIdx κ) X0 (fun L => Q L ∧ charge χ p L = 0) :=
    { lib := A.indices H
      P := newP A E.P tokE
      R0 := Rn
      loopP := by
        intro j hj e he
        rcases mem_union.mp he with he | he
        · exact holdLoop j hj e he
        · obtain ⟨τ, hτ, he⟩ := mem_biUnion.mp he
          exact hreal.loop τ (hidsS j hj hτ) e he
      evenP := fun j hj => OnePart.even_incidentLoad_union (hdisOT j hj _ (hidsS j hj))
        (holdEven j hj) (hreal.even_biUnion (hidsS j hj))
      subP := by
        intro j hj
        refine union_subset ((holdSub j hj).trans ?_) ?_
        · exact union_subset_union subset_union_left le_rfl
        · exact (biUnion_subset_biUnion_of_subset_left _ (hidsS j hj)).trans
            (subset_union_left.trans (union_subset_union subset_union_right le_rfl))
      disjRX := disjoint_union_left.mpr ⟨E.disjRX,
        (hreal.avoid_biUnion le_rfl).mono_right subset_union_right⟩
      refines := by
        rintro L hL ⟨hQL, hqL⟩
        obtain ⟨T, hT, hdisT, hU⟩ := E.refines L hL hQL
        have hcard := A.card_Zs_eq hT (hcons T hT hdisT L hL hqL hU)
        obtain ⟨f, hinj, hedge, himg⟩ := hmatch (A.Zs T) (A.Zs_subset hT) hcard
        refine ⟨A.sel T n f, A.sel_subset_indices hT hedge, ?_, ?_⟩
        · intro j hj j' hj' hne
          have hjI := A.sel_subset_indices hT hedge hj
          have hj'I := A.sel_subset_indices hT hedge hj'
          have hids := A.pairwiseDisjoint_ids hT hinj himg hj hj' hne
          have hold : Disjoint (oldP E.P j) (oldP E.P j') := by
            rcases j with i | j <;> rcases j' with i' | j'
            · have hi : i ∈ T := by simpa [Ledger.sel] using hj
              have hi' : i' ∈ T := by simpa [Ledger.sel] using hj'
              exact hdisT hi hi' (fun h => hne (by rw [h]))
            · exact disjoint_empty_right _
            · exact disjoint_empty_left _
            · exact disjoint_empty_left _
          change Disjoint (oldP E.P j ∪ _) (oldP E.P j' ∪ _)
          rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
          exact ⟨⟨hold, hdisOT j hjI _ (hidsS j' hj'I)⟩,
            (hdisOT j' hj'I _ (hidsS j hjI)).symm,
            hreal.disjoint_biUnion (hidsS j hjI) (hidsS j' hj'I) hids⟩
        · have h1 : (A.sel T n f).biUnion (oldP E.P) = T.biUnion E.P := by
            ext e
            simp only [mem_biUnion, Ledger.sel, mem_union, mem_image, Function.comp_apply]
            constructor
            · rintro ⟨j, (⟨i, hi, rfl⟩ | ⟨r, -, rfl⟩) | ⟨x, -, rfl⟩, he⟩
              · exact ⟨i, hi, he⟩
              · simp [oldP] at he
              · simp [oldP] at he
            · rintro ⟨i, hi, he⟩
              exact ⟨Sum.inl i, Or.inl (Or.inl ⟨i, hi, rfl⟩), he⟩
          have h2 : (A.sel T n f).biUnion (fun j => (A.ids j).biUnion tokE) =
              S0.biUnion tokE := by
            rw [← biUnion_biUnion, A.biUnion_ids_sel hT himg]
          change (A.sel T n f).biUnion (fun j => oldP E.P j ∪ (A.ids j).biUnion tokE) = _
          rw [biUnion_union, h1, h2, hU, hRn]
          ext e; simp only [mem_union]; tauto }
  refine ⟨S0, tokE, E', hreal, hextra, hS0card, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- every new piece has zero charge
    intro j hj
    change charge χ p (oldP E.P j ∪ (A.ids j).biUnion tokE) = 0
    rw [charge_union _ _ (hdisOT j hj _ (hidsS j hj)), hreal.charge_biUnion χ (hidsS j hj),
      sum_congr rfl fun τ hτ => hreal.chg τ (hidsS j hj hτ)]
    change j ∈ A.indices H at hj
    simp only [Ledger.indices, mem_union, mem_image, Function.comp_apply] at hj
    rcases hj with (⟨i, hi, rfl⟩ | ⟨r, -, rfl⟩) | ⟨h, -, rfl⟩
    · simp only [oldP, Ledger.ids]
      rw [sum_sign_idsPar A hi u, hAc i hi, A.c_eq i]
      ring
    · simp only [oldP, Ledger.ids, Ledger.idsRel, charge_empty]
      rw [sum_pair (by simp)]
      simp [Tok.sign]
    · simp only [oldP, Ledger.ids, idsMt, charge_empty]
      rcases h with ⟨x, y | y⟩ <;>
      · rw [sum_pair (by simp [minusId])]
        simp [Tok.sign, minusId]
  · -- the secondary charge is preserved
    intro hold j hj
    change charge χ' p (oldP E.P j ∪ (A.ids j).biUnion tokE) = 0
    rw [charge_union _ _ (hdisOT j hj _ (hidsS j hj)), hreal.charge_biUnion χ' (hidsS j hj),
      sum_eq_zero fun τ hτ => hreal.chg' τ (hidsS j hj hτ), add_zero]
    rcases j with i | j
    · exact hold i (hlibI i hj)
    · exact charge_empty _ _
  · -- piece sizes
    intro j hj
    have hc : (newP A E.P tokE j).card ≤ (oldP E.P j).card + g * (A.ids j).card :=
      (card_union_le _ _).trans (Nat.add_le_add_left (hreal.card_biUnion_le (hidsS j hj)) _)
    rcases j with i | j
    · right
      refine ⟨i, hlibI i hj, hc.trans ?_⟩
      simp only [oldP]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left g (A.card_ids_inl i)) _
    · left
      refine hc.trans ?_
      simp only [oldP, card_empty, zero_add]
      have := A.card_ids_inr j
      nlinarith
  · -- vertex loads
    intro w
    have h1 : ∀ j ∈ A.indices H, incidentLoad (newP A E.P tokE j) w ≤
        incidentLoad (oldP E.P j) w + ∑ τ ∈ S0, if τ ∈ A.ids j then incidentLoad (tokE τ) w
          else 0 := by
      intro j hj
      refine (ModThreeLayer.incidentLoad_union_le _ _ w).trans (Nat.add_le_add_left ?_ _)
      refine (incidentLoad_biUnion_le _ _ w).trans (le_of_eq ?_)
      rw [← sum_filter]
      congr 1
      ext τ; simp only [mem_filter]
      exact ⟨fun h => ⟨hidsS j hj h, h⟩, fun h => h.2⟩
    have h2 : ∑ j ∈ A.indices H, incidentLoad (oldP E.P j) w ≤
        ∑ i ∈ E.lib, incidentLoad (E.P i) w := by
      unfold Ledger.indices
      rw [union_assoc]
      have hui := Finset.sum_union_inter (s₁ := A.lib.image Sum.inl)
        (s₂ := A.relIdx.image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr))
        (f := fun j => incidentLoad (oldP E.P j) w)
      refine (Nat.le.intro hui).trans ?_
      have hrest : ∑ j ∈ A.relIdx.image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr),
          incidentLoad (oldP E.P j) w = 0 := by
        refine sum_eq_zero fun j hj => ?_
        simp only [mem_union, mem_image, Function.comp_apply] at hj
        rcases hj with ⟨r, -, rfl⟩ | ⟨h, -, rfl⟩ <;> simp [oldP, incidentLoad]
      rw [hrest, add_zero, sum_image (fun a _ b _ h => Sum.inl_injective h)]
      exact le_rfl
    have h3 : ∑ j ∈ A.indices H, ∑ τ ∈ S0,
        (if τ ∈ A.ids j then incidentLoad (tokE τ) w else 0) ≤
        44 * ∑ τ ∈ S0, incidentLoad (tokE τ) w := by
      rw [sum_comm, mul_sum]
      refine sum_le_sum fun τ _ => ?_
      rw [← sum_filter, sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (A.card_filter_ids_le hdx hdy τ)
    calc ∑ j ∈ A.indices H, incidentLoad (newP A E.P tokE j) w
        ≤ ∑ j ∈ A.indices H, (incidentLoad (oldP E.P j) w + ∑ τ ∈ S0,
            if τ ∈ A.ids j then incidentLoad (tokE τ) w else 0) := sum_le_sum h1
      _ = ∑ j ∈ A.indices H, incidentLoad (oldP E.P j) w + ∑ j ∈ A.indices H, ∑ τ ∈ S0,
            (if τ ∈ A.ids j then incidentLoad (tokE τ) w else 0) := sum_add_distrib
      _ ≤ _ := Nat.add_le_add h2 h3
  · -- library size
    have h := A.card_indices_le hHfst hdx
    change (A.indices H).card ≤ _
    have hA' : A.lib = E.lib := rfl
    rw [hA'] at h
    rw [← hzE]
    omega

end PartitionedTriangleAbsorption.StructuralF3General
