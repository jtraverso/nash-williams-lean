/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.TokenLayer

/-!
# A group-valued token ledger layer

This is the shared switching network of the refiner, in a form that is no longer tied
to an integer-valued scalar charge.

Input: a predicate refiner `E` of a reserve `X0` (fixed remainder `R0`, fixed library of
loopless even pieces), an integer *demand* `c i` for every library piece, and a target
predicate `Q'` such that every leftover satisfying `Q'` is refined by a selection `T` of
pieces with the *conserved* total demand `∑ i ∈ T, c i = K` (`hsel`).

Tokens are realized physically (`TokRealV`): pairwise edge-disjoint, avoiding `R0 ∪ X0`,
loopless, even, of bounded size, and with value `+g` (plus tokens) or `-g` (minus tokens)
for an arbitrary additive edge valuation `val : Sym2 W → A` into an abelian group.

The proof reuses unchanged the host-independent token bookkeeping (`Ledger`,
`exists_robust`, the owner map) of `StructuralF3General.TokenLedger`; the only changes with
respect to `token_layer` are that the demands are abstract (conservation is a hypothesis,
not derived from a scalar charge) and that the value bookkeeping happens in `A`: every new
piece has value `val(P i) - c i • g` (parity pieces) or `g + (-g)` (release and matching
pieces), so it lies in any subgroup `H` containing all `val(P i) - c i • g`.

The token identities, the robust matching graph and hence the whole library are fixed
before any leftover is known.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0

variable {W : Type*} [DecidableEq W] {κ : Type*}

/-- Additive value of an edge set. -/
def edgeVal {A : Type*} [AddCommGroup A] (val : Sym2 W → A) (E : Finset (Sym2 W)) : A :=
  ∑ e ∈ E, val e

section EdgeVal

variable {A : Type*} [AddCommGroup A] (val : Sym2 W → A)

theorem edgeVal_empty : edgeVal val (∅ : Finset (Sym2 W)) = 0 := by
  simp [edgeVal]

theorem edgeVal_union {E F : Finset (Sym2 W)} (h : Disjoint E F) :
    edgeVal val (E ∪ F) = edgeVal val E + edgeVal val F := by
  simp only [edgeVal]
  exact sum_union h

theorem edgeVal_biUnion {ι : Type*} (s : Finset ι) (E : ι → Finset (Sym2 W))
    (h : (s : Set ι).PairwiseDisjoint E) :
    edgeVal val (s.biUnion E) = ∑ i ∈ s, edgeVal val (E i) := by
  simp only [edgeVal]
  exact sum_biUnion h

end EdgeVal

/-- A physical realization of the token identities `S` with values `±g`. -/
structure TokRealV {A : Type*} [AddCommGroup A] (val : Sym2 W → A) (g : A) (sz : ℕ)
    (B : Finset (Sym2 W)) (S : Finset (Tok κ)) (tokE : Tok κ → Finset (Sym2 W)) : Prop where
  disj : (S : Set (Tok κ)).PairwiseDisjoint tokE
  avoid : ∀ τ ∈ S, Disjoint (tokE τ) B
  loop : ∀ τ ∈ S, ∀ e ∈ tokE τ, ¬ e.IsDiag
  even : ∀ τ ∈ S, ∀ w, Even (incidentLoad (tokE τ) w)
  val : ∀ τ ∈ S, edgeVal val (tokE τ) = if τ.sign then g else -g
  card : ∀ τ ∈ S, (tokE τ).card ≤ sz

section TokLemmas

variable {A : Type*} [AddCommGroup A] {val : Sym2 W → A} {g : A} {sz : ℕ}
  {B : Finset (Sym2 W)} {S : Finset (Tok κ)} {tokE : Tok κ → Finset (Sym2 W)}

theorem TokRealV.disjoint_biUnion (h : TokRealV val g sz B S tokE) {S1 S2 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) (h2 : S2 ⊆ S) (h12 : Disjoint S1 S2) :
    Disjoint (S1.biUnion tokE) (S2.biUnion tokE) := by
  rw [disjoint_biUnion_left]
  intro a ha
  rw [disjoint_biUnion_right]
  intro b hb
  exact h.disj (h1 ha) (h2 hb) (fun hab => disjoint_left.mp h12 ha (hab ▸ hb))

theorem TokRealV.avoid_biUnion (h : TokRealV val g sz B S tokE) {S1 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) : Disjoint (S1.biUnion tokE) B := by
  rw [disjoint_biUnion_left]
  exact fun a ha => h.avoid a (h1 ha)

theorem TokRealV.even_biUnion (h : TokRealV val g sz B S tokE) {S1 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) : ∀ w, Even (incidentLoad (S1.biUnion tokE) w) :=
  OnePart.even_incidentLoad_biUnion S1 tokE (h.disj.subset h1) (fun a ha => h.even a (h1 ha))

theorem TokRealV.val_biUnion (h : TokRealV val g sz B S tokE) {S1 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) :
    edgeVal val (S1.biUnion tokE) = ∑ τ ∈ S1, (if τ.sign then g else -g) := by
  rw [edgeVal_biUnion val S1 tokE (h.disj.subset h1)]
  exact sum_congr rfl fun τ hτ => h.val τ (h1 hτ)

theorem TokRealV.card_biUnion_le (h : TokRealV val g sz B S tokE) {S1 : Finset (Tok κ)}
    (h1 : S1 ⊆ S) : (S1.biUnion tokE).card ≤ sz * S1.card := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ a ∈ S1, (tokE a).card ≤ ∑ _a ∈ S1, sz := sum_le_sum fun a ha => h.card a (h1 ha)
    _ = sz * S1.card := by rw [sum_const, smul_eq_mul, mul_comm]

end TokLemmas

/-- Value of the token identities of a parity piece. -/
theorem sum_sign_idsPar_val [DecidableEq κ] (L : Ledger κ) {i : κ} (hi : i ∈ L.lib)
    {A : Type*} [AddCommGroup A] (g : A) :
    ∑ τ ∈ L.idsPar i, (if τ.sign then g else -g) = (L.pc i : ℤ) • g - (L.mc i : ℤ) • g := by
  unfold Ledger.idsPar
  rw [sum_union]
  · rw [sum_image, sum_image]
    · simp only [Tok.sign, Bool.false_eq_true, if_false, if_true, sum_const, card_range,
        natCast_zsmul, smul_neg]
      abel
    · intro a _ b _ h; simpa using h
    · intro a ha b hb h
      simp only [Tok.vm.injEq] at h
      have := L.slot_inj (L.mem_D_false hi (mem_range.mp ha))
        (L.mem_D_false hi (mem_range.mp hb)) h
      simpa using this
  · rw [disjoint_left]
    intro τ h1 h2
    obtain ⟨k, -, rfl⟩ := mem_image.mp h1
    obtain ⟨k', -, h⟩ := mem_image.mp h2
    simp at h

/-- **The group-valued ledger layer.** -/
theorem ledger_layer [DecidableEq κ] {X0 : Finset (Sym2 W)} {Q Q' : Finset (Sym2 W) → Prop}
    (E : PredRefiner κ X0 Q) (c : κ → ℤ) (K : ℤ)
    (hsel : ∀ L ⊆ X0, Q' L → ∃ T ⊆ E.lib, (T : Set κ).PairwiseDisjoint E.P ∧
      T.biUnion E.P = E.R0 ∪ L ∧ ∑ i ∈ T, c i = K)
    (hQ0 : Q' ∅)
    {A : Type*} [AddCommGroup A] (val : Sym2 W → A) (g : A) (sz : ℕ)
    (Extra : Finset (Tok κ) → (Tok κ → Finset (Sym2 W)) → Prop)
    (hsupply : ∀ S : Finset (Tok κ), S.card ≤ 9 * ∑ i ∈ E.lib, (c i).natAbs →
      ∃ tokE, TokRealV val g sz (E.R0 ∪ X0) S tokE ∧ Extra S tokE) :
    ∃ (S : Finset (Tok κ)) (tokE : Tok κ → Finset (Sym2 W))
      (E' : PredRefiner (JIdx κ) X0 Q'),
      TokRealV val g sz (E.R0 ∪ X0) S tokE ∧ Extra S tokE ∧
      S.card ≤ 9 * ∑ i ∈ E.lib, (c i).natAbs ∧
      E'.R0 = E.R0 ∪ S.biUnion tokE ∧
      (∀ H : AddSubgroup A, (∀ i ∈ E.lib, edgeVal val (E.P i) - c i • g ∈ H) →
        ∀ j ∈ E'.lib, edgeVal val (E'.P j) ∈ H) ∧
      (∀ j ∈ E'.lib, (E'.P j).card ≤ 2 * sz ∨
        ∃ i ∈ E.lib, (E'.P j).card ≤ (E.P i).card + sz * (c i).natAbs) ∧
      (∀ w, ∑ j ∈ E'.lib, incidentLoad (E'.P j) w ≤
        ∑ i ∈ E.lib, incidentLoad (E.P i) w + 44 * ∑ τ ∈ S, incidentLoad (tokE τ) w) ∧
      E'.lib.card ≤ E.lib.card + 97 * ∑ i ∈ E.lib, (c i).natAbs := by
  classical
  set L : Ledger κ := ⟨E.lib, c⟩ with hL
  obtain ⟨T0, hT0, hdis0, hU0, hK0⟩ := hsel ∅ (empty_subset _) hQ0
  have hs : L.sNum K ≤ L.z := by
    rw [← L.card_Zs_eq hT0 hK0]
    have := card_le_card (L.Zs_subset hT0)
    simpa using this
  obtain ⟨m, H, hm, hHfst, hHsnd, hdx, hdy, hmatch⟩ := exists_robust L.z (L.sNum K) hs
  set n := m + L.sNum K with hn
  set S0 := L.allIds n m with hS0
  have hzE : L.z = ∑ i ∈ E.lib, (c i).natAbs := L.z_eq
  have hS0card : S0.card ≤ 9 * ∑ i ∈ E.lib, (c i).natAbs := by
    have := L.card_allIds_le n m
    rw [← hS0] at this
    rw [← hzE]; omega
  obtain ⟨tokE, hreal, hextra⟩ := hsupply S0 hS0card
  have hidsS : ∀ j ∈ L.indices H, L.ids j ⊆ S0 := fun j hj =>
    L.ids_subset_allIds hHfst hHsnd hj
  have hlibI : ∀ i, (Sum.inl i : JIdx κ) ∈ L.indices H → i ∈ E.lib := by
    intro i hi
    simpa [Ledger.indices] using hi
  have holdSub : ∀ j ∈ L.indices H, oldP E.P j ⊆ E.R0 ∪ X0 := by
    intro j hj
    rcases j with i | j
    · exact E.subP i (hlibI i hj)
    · exact empty_subset _
  have holdLoop : ∀ j ∈ L.indices H, ∀ e ∈ oldP E.P j, ¬ e.IsDiag := by
    intro j hj
    rcases j with i | j
    · exact E.loopP i (hlibI i hj)
    · simp [oldP]
  have holdEven : ∀ j ∈ L.indices H, ∀ w, Even (incidentLoad (oldP E.P j) w) := by
    intro j hj
    rcases j with i | j
    · exact E.evenP i (hlibI i hj)
    · intro w; simp [oldP, incidentLoad]
  have hdisOT : ∀ j ∈ L.indices H, ∀ S1 ⊆ S0, Disjoint (oldP E.P j) (S1.biUnion tokE) :=
    fun j hj S1 hS1 => ((hreal.avoid_biUnion hS1).mono_right (holdSub j hj)).symm
  set Rn := E.R0 ∪ S0.biUnion tokE with hRn
  let E' : PredRefiner (JIdx κ) X0 Q' :=
    { lib := L.indices H
      P := newP L E.P tokE
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
        · exact union_subset_union subset_union_left subset_rfl
        · exact (biUnion_subset_biUnion_of_subset_left _ (hidsS j hj)).trans
            (subset_union_left.trans (union_subset_union subset_union_right subset_rfl))
      disjRX := disjoint_union_left.mpr ⟨E.disjRX,
        (hreal.avoid_biUnion subset_rfl).mono_right subset_union_right⟩
      refines := by
        rintro Lf hL hQL
        obtain ⟨T, hT, hdisT, hU, hTK⟩ := hsel Lf hL hQL
        have hcard := L.card_Zs_eq hT hTK
        obtain ⟨f, hinj, hedge, himg⟩ := hmatch (L.Zs T) (L.Zs_subset hT) hcard
        refine ⟨L.sel T n f, L.sel_subset_indices hT hedge, ?_, ?_⟩
        · intro j hj j' hj' hne
          have hjI := L.sel_subset_indices hT hedge hj
          have hj'I := L.sel_subset_indices hT hedge hj'
          have hids := L.pairwiseDisjoint_ids hT hinj himg hj hj' hne
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
        · have h1 : (L.sel T n f).biUnion (oldP E.P) = T.biUnion E.P := by
            ext e
            simp only [mem_biUnion, Ledger.sel, mem_union, mem_image, Function.comp_apply]
            constructor
            · rintro ⟨j, (⟨i, hi, rfl⟩ | ⟨r, -, rfl⟩) | ⟨x, -, rfl⟩, he⟩
              · exact ⟨i, hi, he⟩
              · simp [oldP] at he
              · simp [oldP] at he
            · rintro ⟨i, hi, he⟩
              exact ⟨Sum.inl i, Or.inl (Or.inl ⟨i, hi, rfl⟩), he⟩
          have h2 : (L.sel T n f).biUnion (fun j => (L.ids j).biUnion tokE) =
              S0.biUnion tokE := by
            rw [← biUnion_biUnion, L.biUnion_ids_sel hT himg]
          change (L.sel T n f).biUnion (fun j => oldP E.P j ∪ (L.ids j).biUnion tokE) = _
          rw [biUnion_union, h1, h2, hU, hRn]
          ext e; simp only [mem_union]; tauto }
  refine ⟨S0, tokE, E', hreal, hextra, hS0card, rfl, ?_, ?_, ?_, ?_⟩
  · -- every new piece has its value in `H`
    intro Hs hold j hj
    change edgeVal val (oldP E.P j ∪ (L.ids j).biUnion tokE) ∈ Hs
    rw [edgeVal_union val (hdisOT j hj _ (hidsS j hj)), hreal.val_biUnion (hidsS j hj)]
    change j ∈ L.indices H at hj
    simp only [Ledger.indices, mem_union, mem_image, Function.comp_apply] at hj
    rcases hj with (⟨i, hi, rfl⟩ | ⟨r, -, rfl⟩) | ⟨h, -, rfl⟩
    · simp only [oldP, Ledger.ids]
      rw [sum_sign_idsPar_val L hi g]
      have hc : c i = (L.mc i : ℤ) - L.pc i := L.c_eq i
      have heq : edgeVal val (E.P i) + ((L.pc i : ℤ) • g - (L.mc i : ℤ) • g) =
          edgeVal val (E.P i) - c i • g := by
        rw [hc, sub_zsmul]; abel
      rw [heq]
      exact hold i hi
    · simp only [oldP, Ledger.ids, Ledger.idsRel, edgeVal_empty]
      rw [sum_pair (by simp)]
      simp [Tok.sign]
    · simp only [oldP, Ledger.ids, idsMt, edgeVal_empty]
      rcases h with ⟨x, y | y⟩ <;>
      · rw [sum_pair (by simp [minusId])]
        simp [Tok.sign, minusId]
  · -- piece sizes
    intro j hj
    have hc : (newP L E.P tokE j).card ≤ (oldP E.P j).card + sz * (L.ids j).card :=
      (card_union_le _ _).trans (Nat.add_le_add_left (hreal.card_biUnion_le (hidsS j hj)) _)
    rcases j with i | j
    · right
      refine ⟨i, hlibI i hj, hc.trans ?_⟩
      simp only [oldP]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left sz (L.card_ids_inl i)) _
    · left
      refine hc.trans ?_
      simp only [oldP, card_empty, zero_add]
      have := L.card_ids_inr j
      nlinarith
  · -- vertex loads
    intro w
    have h1 : ∀ j ∈ L.indices H, incidentLoad (newP L E.P tokE j) w ≤
        incidentLoad (oldP E.P j) w + ∑ τ ∈ S0, if τ ∈ L.ids j then incidentLoad (tokE τ) w
          else 0 := by
      intro j hj
      refine (ModThreeLayer.incidentLoad_union_le _ _ w).trans (Nat.add_le_add_left ?_ _)
      refine (incidentLoad_biUnion_le _ _ w).trans (le_of_eq ?_)
      rw [← sum_filter]
      congr 1
      ext τ; simp only [mem_filter]
      exact ⟨fun h => ⟨hidsS j hj h, h⟩, fun h => h.2⟩
    have h2 : ∑ j ∈ L.indices H, incidentLoad (oldP E.P j) w ≤
        ∑ i ∈ E.lib, incidentLoad (E.P i) w := by
      unfold Ledger.indices
      rw [union_assoc]
      have hui := Finset.sum_union_inter (s₁ := L.lib.image Sum.inl)
        (s₂ := L.relIdx.image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr))
        (f := fun j => incidentLoad (oldP E.P j) w)
      refine (Nat.le.intro hui).trans ?_
      have hrest : ∑ j ∈ L.relIdx.image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr),
          incidentLoad (oldP E.P j) w = 0 := by
        refine sum_eq_zero fun j hj => ?_
        simp only [mem_union, mem_image, Function.comp_apply] at hj
        rcases hj with ⟨r, -, rfl⟩ | ⟨h, -, rfl⟩ <;> simp [oldP, incidentLoad]
      rw [hrest, add_zero, sum_image (fun a _ b _ h => Sum.inl_injective h)]
      exact le_rfl
    have h3 : ∑ j ∈ L.indices H, ∑ τ ∈ S0,
        (if τ ∈ L.ids j then incidentLoad (tokE τ) w else 0) ≤
        44 * ∑ τ ∈ S0, incidentLoad (tokE τ) w := by
      rw [sum_comm, mul_sum]
      refine sum_le_sum fun τ _ => ?_
      rw [← sum_filter, sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (L.card_filter_ids_le hdx hdy τ)
    calc ∑ j ∈ L.indices H, incidentLoad (newP L E.P tokE j) w
        ≤ ∑ j ∈ L.indices H, (incidentLoad (oldP E.P j) w + ∑ τ ∈ S0,
            if τ ∈ L.ids j then incidentLoad (tokE τ) w else 0) := sum_le_sum h1
      _ = ∑ j ∈ L.indices H, incidentLoad (oldP E.P j) w + ∑ j ∈ L.indices H, ∑ τ ∈ S0,
            (if τ ∈ L.ids j then incidentLoad (tokE τ) w else 0) := sum_add_distrib
      _ ≤ _ := Nat.add_le_add h2 h3
  · -- library size
    have h := L.card_indices_le hHfst hdx
    change (L.indices H).card ≤ _
    have hA' : L.lib = E.lib := rfl
    rw [hA'] at h
    rw [← hzE]
    omega

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
