/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1ResidualQuotasStage169

/-! # Balanced selection of triangles to discard

The supply inequality is explicit. This leaf does not assert that an arbitrary
packing has that supply, nor derive degree control from total cardinality.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BalancedTrimStage170

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def incidence (D : Finset (Finset V)) (v : V) : ℕ :=
  (D.filter fun s => v ∈ s).card

theorem incidence_mass (D : Finset (Finset V))
    (htri : ∀ s ∈ D, s.card = 3) :
    (∑ v : V, incidence D v) = 3 * D.card := by
  simp only [incidence, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have h (s : Finset V) : (∑ v : V, if v ∈ s then (1 : ℕ) else 0) = s.card := by
    simp
  simp only [h]
  rw [sum_congr rfl htri, sum_const, nsmul_eq_mul]
  simp only [sum_const, nsmul_eq_mul, mul_comm, mul_one]

theorem saturated_mass (S : Finset (Finset V)) (d : ℕ)
    (htri : ∀ s ∈ S, s.card = 3) :
    d * (univ.filter fun v => d ≤ incidence S v).card ≤ 3 * S.card := by
  let Z := univ.filter fun v => d ≤ incidence S v
  calc
    _ = ∑ _v ∈ Z, d := by simp [Z, mul_comm]
    _ ≤ ∑ v ∈ Z, incidence S v := sum_le_sum fun v hv => (mem_filter.mp hv).2
    _ ≤ ∑ v : V, incidence S v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ Z) (by intros; positivity)
    _ = 3 * S.card := incidence_mass S htri

omit [Fintype V] in
theorem blocked_card (D : Finset (Finset V)) (Z : Finset V) (b : ℕ)
    (hinc : ∀ v, incidence D v ≤ b) :
    (D.filter fun s => ∃ v ∈ Z, v ∈ s).card ≤ b * Z.card := by
  have heq : (D.filter fun s => ∃ v ∈ Z, v ∈ s) =
      Z.biUnion (fun v => D.filter fun s => v ∈ s) := by
    ext s
    simp only [mem_filter, mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ v ∈ Z, (D.filter fun s => v ∈ s).card := card_biUnion_le
    _ ≤ ∑ _v ∈ Z, b := sum_le_sum fun v _ => hinc v
    _ = b * Z.card := by simp [mul_comm]

omit [Fintype V] in
/-- Greedy selection with a uniform incidence cap. The abundance premise is
strict only to guarantee one unused triangle at each step. -/
theorem balanced_selection [Finite V] (D : Finset (Finset V)) (k b d : ℕ)
    (htri : ∀ s ∈ D, s.card = 3) (hinc : ∀ v, incidence D v ≤ b)
    (hd : 0 < d) (hbudget : d * k + 3 * k * b < d * D.card) :
    ∃ S ⊆ D, S.card = k ∧ ∀ v, incidence S v ≤ d := by
  let := Fintype.ofFinite V
  induction k with
  | zero => exact ⟨∅, empty_subset D, rfl, by intro v; simp [incidence]⟩
  | succ k ih =>
    obtain ⟨S, hSD, hSk, hcap⟩ := ih (by nlinarith)
    let Z := univ.filter fun v => d ≤ incidence S v
    let B := D.filter fun s => ∃ v ∈ Z, v ∈ s
    have hz : d * Z.card ≤ 3 * k := by
      simpa only [Z, hSk] using saturated_mass S d (fun s hs => htri s (hSD hs))
    have hb : B.card ≤ b * Z.card := blocked_card D Z b hinc
    have hex : ∃ s ∈ D, s ∉ S ∧ s ∉ B := by
      by_contra hn
      have hcover : D ⊆ S ∪ B := by
        intro s hs
        by_cases h : s ∈ S
        · exact mem_union_left _ h
        · have : s ∈ B := by by_contra hB; exact hn ⟨s, hs, h, hB⟩
          exact mem_union_right _ this
      have hN : D.card ≤ k + b * Z.card :=
        (card_le_card hcover).trans ((card_union_le S B).trans (by omega))
      have hmul := Nat.mul_le_mul_left d hN
      have hzb := Nat.mul_le_mul_right b hz
      nlinarith
    obtain ⟨s, hsD, hsS, hsB⟩ := hex
    refine ⟨insert s S, insert_subset hsD hSD, by simp [hsS, hSk], ?_⟩
    intro v
    by_cases hv : v ∈ s
    · have hvZ : v ∉ Z := by
        intro hvZ
        exact hsB (mem_filter.mpr ⟨hsD, v, hvZ, hv⟩)
      have hlt : incidence S v < d := by
        simpa only [Z, mem_filter, mem_univ, true_and, not_le] using hvZ
      have hnot : s ∉ S.filter (fun s => v ∈ s) := fun hs => hsS (mem_filter.mp hs).1
      simp only [incidence, filter_insert, hv, ite_true, card_insert_of_notMem hnot]
      dsimp [incidence] at hlt
      omega
    · simpa only [incidence, filter_insert, hv, ite_false] using hcap v

omit [Fintype V] in
theorem incidence_biUnion {I : Type}
    (F : Finset I) (S : I → Finset (Finset V)) (d : ℕ)
    (hcap : ∀ i ∈ F, ∀ v, incidence (S i) v ≤ d) (v : V) :
    incidence (F.biUnion S) v ≤ F.card * d := by
  classical
  unfold incidence
  rw [filter_biUnion]
  calc
    _ ≤ ∑ i ∈ F, ((S i).filter fun s => v ∈ s).card := card_biUnion_le
    _ ≤ ∑ _i ∈ F, d := sum_le_sum fun i hi => hcap i hi v
    _ = F.card * d := by simp

omit [Fintype V] in
/-- Exact per-type capacities, with balanced discarded triangles. -/
theorem balanced_type_caps [Finite V] {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (c : Multiset (Fin t) → ℕ) (b d : ℕ) (hd : 0 < d)
    (hinc : ∀ tau ∈ F, ∀ v, incidence (D.filter fun s => triType p s = tau) v ≤ b)
    (hsupply : ∀ tau ∈ F,
      let N := (D.filter fun s => triType p s = tau).card
      let k := N - c tau
      k = 0 ∨ d * k + 3 * k * b < d * N) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p F Q' D' ∧
      (∀ tau ∈ F, (D'.filter fun s => triType p s = tau).card ≤ c tau) ∧
      (∀ v, incidence (D \ D') v ≤ F.card * d) ∧
      D.card - D'.card = ∑ tau ∈ F,
        ((D.filter fun s => triType p s = tau).card - c tau) := by
  classical
  let P (tau : Multiset (Fin t)) := D.filter fun s => triType p s = tau
  have hs : ∀ tau, ∃ S ⊆ P tau,
      S.card = (P tau).card - c tau ∧ ∀ v, incidence S v ≤ d := by
    intro tau
    by_cases htau : tau ∈ F
    · rcases hsupply tau htau with hz | hb
      · exact ⟨∅, empty_subset _, by simpa [P] using hz.symm,
          by intro v; simp [incidence]⟩
      · exact balanced_selection (P tau) _ b d
          (fun s hs => (hD.1 s (mem_filter.mp hs).1).1) (hinc tau htau) hd hb
    · have hempty : P tau = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        have hm := (hD.1 s (mem_filter.mp hs).1).2
        change triType p s ∈ F at hm
        rw [(mem_filter.mp hs).2] at hm
        exact htau hm
      exact ⟨∅, empty_subset _, by simp [hempty], by intro v; simp [incidence]⟩
  choose S hS hc hcap using hs
  let R := F.biUnion S
  have hRD : R ⊆ D := by
    intro s hs
    obtain ⟨tau, _, hs⟩ := mem_biUnion.mp hs
    exact (mem_filter.mp (hS tau hs)).1
  have hRfilt (tau : Multiset (Fin t)) (htau : tau ∈ F) :
      R.filter (fun s => triType p s = tau) = S tau := by
    ext s
    constructor
    · intro hs
      obtain ⟨hs, ht⟩ := mem_filter.mp hs
      obtain ⟨sigma, _, hs⟩ := mem_biUnion.mp hs
      have heq := (mem_filter.mp (hS sigma hs)).2
      have : sigma = tau := heq.symm.trans ht
      simpa only [this] using hs
    · intro hs
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨tau, htau, hs⟩,
        (mem_filter.mp (hS tau hs)).2⟩
  let D' := D \ R
  have hsub : D' ⊆ D := sdiff_subset
  have hleft (tau : Multiset (Fin t)) (htau : tau ∈ F) :
      (D'.filter fun s => triType p s = tau).card ≤ c tau := by
    have heq : (D'.filter fun s => triType p s = tau) = P tau \ S tau := by
      ext s
      have hf := hRfilt tau htau
      have : (s ∈ R ∧ triType p s = tau) ↔ s ∈ S tau := by
        rw [← hf]; simp
      simp only [D', P, mem_filter, mem_sdiff]
      tauto
    rw [heq, card_sdiff_of_subset (hS tau), hc tau]
    omega
  have hdiff : D \ D' = R := by ext s; simp only [D', mem_sdiff];
                                                constructor <;> aesop
  have hcard : R.card = ∑ tau ∈ F, ((P tau).card - c tau) := by
    rw [card_eq_sum_card_fiberwise (f := triType p) (t := F)
      (fun s hs => (hD.1 s (hRD hs)).2)]
    exact sum_congr rfl fun tau htau => by rw [hRfilt tau htau, hc tau]
  refine ⟨D', D'.biUnion triEdges, hsub, ?_,
    ⟨fun s hs => hD.1 s (hsub hs), hD.2.1.subset hsub, rfl⟩, hleft, ?_, ?_⟩
  · rw [← hD.2.2]
    exact biUnion_subset_biUnion_of_subset_left triEdges hsub
  · intro v
    rw [hdiff]
    exact incidence_biUnion F S d (fun tau _ => hcap tau) v
  · have hh := card_sdiff_of_subset hsub
    rw [hdiff, hcard] at hh
    exact hh.symm

omit [Fintype V] in
theorem triangle_incident_edges (s : Finset V) (hcard : s.card = 3) (v : V) :
    ((triEdges s).filter fun e => v ∈ e).card ≤ if v ∈ s then 2 else 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hcard
  rw [triEdges_three hab hac hbc]
  by_cases ha : v = a
  · subst v
    have hsub : (({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).filter fun e => a ∈ e) ⊆
        ({s(a, b), s(a, c)} : Finset (Sym2 V)) := by
      intro e he
      simp only [mem_filter, mem_insert, mem_singleton] at he ⊢
      rcases he.1 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · have hf : ¬ a ∈ s(b, c) := by simp [Sym2.mem_iff, hab, hac]
        exact (hf he.2).elim
    simpa only [mem_insert, mem_singleton, eq_self, true_or, ite_true] using
      (card_le_card hsub).trans card_le_two
  by_cases hb : v = b
  · subst v
    have hsub : (({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).filter fun e => b ∈ e) ⊆
        ({s(a, b), s(b, c)} : Finset (Sym2 V)) := by
      intro e he
      simp only [mem_filter, mem_insert, mem_singleton] at he ⊢
      rcases he.1 with rfl | rfl | rfl
      · exact Or.inl rfl
      · have hf : ¬ b ∈ s(a, c) := by simp [Sym2.mem_iff, ha, hbc]
        exact (hf he.2).elim
      · exact Or.inr rfl
    simpa only [mem_insert, mem_singleton, eq_self, true_or, or_true, ite_true] using
      (card_le_card hsub).trans card_le_two
  by_cases hc : v = c
  · subst v
    have hsub : (({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).filter fun e => c ∈ e) ⊆
        ({s(a, c), s(b, c)} : Finset (Sym2 V)) := by
      intro e he
      simp only [mem_filter, mem_insert, mem_singleton] at he ⊢
      rcases he.1 with rfl | rfl | rfl
      · have hf : ¬ c ∈ s(a, b) := by simp [Sym2.mem_iff, ha, hb]
        exact (hf he.2).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    simpa only [mem_insert, mem_singleton, eq_self, or_true, ite_true] using
      (card_le_card hsub).trans card_le_two
  have he : (({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).filter fun e => v ∈ e) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    simp only [mem_filter, mem_insert, mem_singleton] at he
    rcases he.1 with rfl | rfl | rfl
    all_goals simp only [Sym2.mem_iff] at he; tauto
  rw [he]
  simp [ha, hb, hc]

omit [Fintype V] in
theorem discarded_edge_degree (S : Finset (Finset V))
    (htri : ∀ s ∈ S, s.card = 3) (v : V) :
    (((S.biUnion triEdges).filter fun e => v ∈ e).card) ≤ 2 * incidence S v := by
  rw [filter_biUnion]
  calc
    _ ≤ ∑ s ∈ S, ((triEdges s).filter fun e => v ∈ e).card := card_biUnion_le
    _ ≤ ∑ s ∈ S, if v ∈ s then 2 else 0 :=
      sum_le_sum fun s hs => triangle_incident_edges s (htri s hs) v
    _ = 2 * incidence S v := by
      simp only [incidence, card_eq_sum_ones, sum_filter]
      rw [mul_sum]
      apply sum_congr rfl
      intro s _
      split_ifs <;> simp

omit [Fintype V] in
theorem residual_degree_after_subpacking {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E Q Q' : Finset (Sym2 V))
    (D D' : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (hD' : IsDecomp p F Q' D') (hsub : D' ⊆ D) (v : V) :
    ((E \ Q').filter fun e => v ∈ e).card ≤
      ((E \ Q).filter fun e => v ∈ e).card + 2 * incidence (D \ D') v := by
  have hcover : Q ⊆ Q' ∪ (D \ D').biUnion triEdges := by
    rw [← hD'.2.2, ← union_biUnion, union_sdiff_of_subset hsub, hD.2.2]
  have hedge : E \ Q' ⊆ (E \ Q) ∪ (D \ D').biUnion triEdges := by
    intro e he
    obtain ⟨heE, heQ'⟩ := mem_sdiff.mp he
    by_cases heQ : e ∈ Q
    · rcases mem_union.mp (hcover heQ) with he | he
      · exact (heQ' he).elim
      · exact mem_union_right _ he
    · exact mem_union_left _ (mem_sdiff.mpr ⟨heE, heQ⟩)
  calc
    _ ≤ (((E \ Q) ∪ (D \ D').biUnion triEdges).filter fun e => v ∈ e).card :=
      card_le_card (filter_subset_filter _ hedge)
    _ ≤ ((E \ Q).filter fun e => v ∈ e).card +
        (((D \ D').biUnion triEdges).filter fun e => v ∈ e).card := by
      rw [filter_union]; exact card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left
      (discarded_edge_degree (D \ D') (fun s hs => (hD.1 s (mem_sdiff.mp hs).1).1) v) _

theorem supply_from_residual_size (M N k b d : ℕ)
    (hk : k ≤ 8 * M) (hN : 16 * M ≤ N)
    (hslack : 48 * M * b < d * N) :
    d * k + 3 * k * b < d * N := by
  have hhalf : 2 * k ≤ N := by omega
  have h1 := Nat.mul_le_mul_left d hhalf
  have h2 := Nat.mul_le_mul_right (6 * b) hk
  nlinarith

omit [Fintype V] in
/-- F1 quotas and local degree control for one and the same physical subpacking.
Abundance is still a premise: this is not a complete host packing producer. -/
theorem repair_F1_balanced [Finite V] (p : V → Fin 4) (E Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hI : IsIntDiv p TypedApplicationLinks.F1 E)
    (hR : IsFracDiv p TypedApplicationLinks.F1 E)
    (hD : IsDecomp p TypedApplicationLinks.F1 Q D) (hQE : Q ⊆ E)
    (b d : ℕ) (hd : 0 < d)
    (hinc : ∀ tau ∈ TypedApplicationLinks.F1, ∀ v,
      incidence (D.filter fun s => triType p s = tau) v ≤ b)
    (hsupply : ∀ tau ∈ TypedApplicationLinks.F1,
      16 * (E \ Q).card ≤ (D.filter fun s => triType p s = tau).card ∧
      48 * (E \ Q).card * b < d * (D.filter fun s => triType p s = tau).card) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p TypedApplicationLinks.F1 Q' D' ∧
      IsIntDiv p TypedApplicationLinks.F1 (E \ Q') ∧
      (∃ a : Multiset (Fin 4) → ℕ, edgeVec p (E \ Q') =
        ∑ tau ∈ TypedApplicationLinks.F1, (a tau : ℤ) • typeEdgeVec tau) ∧
      D.card - D'.card ≤ 64 * (E \ Q).card ∧
      (E \ Q').card ≤ 193 * (E \ Q).card ∧
      (∀ v, ((E \ Q').filter fun e => v ∈ e).card ≤
        ((E \ Q).filter fun e => v ∈ e).card + 16 * d) := by
  open TypedApplicationLinks F1ResidualQuotasStage169 in
  obtain ⟨c, hc, hk⟩ := coefficients_near_packing p E Q D hI hR hD hQE
  have hs : ∀ tau ∈ TypedApplicationLinks.F1,
      let N := (D.filter fun s => triType p s = tau).card
      let k := N - c tau
      k = 0 ∨ d * k + 3 * k * b < d * N := by
    intro tau htau
    exact Or.inr (supply_from_residual_size _ _ _ b d (hk tau htau)
      (hsupply tau htau).1 (hsupply tau htau).2)
  obtain ⟨D', Q', hsub, hQsub, hD', hcap, hload, hloss⟩ :=
    balanced_type_caps p TypedApplicationLinks.F1 Q D hD c b d hd hinc hs
  have hQ'E := hQsub.trans hQE
  have hF : TypedApplicationLinks.F1.card = 8 := by decide
  have hexcess : (∑ tau ∈ TypedApplicationLinks.F1,
      ((D.filter fun s => triType p s = tau).card - c tau)) ≤ 64 * (E \ Q).card := by
    calc
      _ ≤ ∑ _tau ∈ TypedApplicationLinks.F1, 8 * (E \ Q).card := sum_le_sum hk
      _ = 64 * (E \ Q).card := by rw [sum_const, nsmul_eq_mul, hF]; omega
  have hsize := F1ResidualQuotasStage169.residual_card_after_subpacking
    p TypedApplicationLinks.F1 E Q Q' D D' hD hD' hsub
  refine ⟨D', Q', hsub, hQsub, hD',
    isIntDiv_sdiff_of_hasDecomp hI ⟨D', hD'⟩ hQ'E, ?_, by omega, by omega, ?_⟩
  · refine ⟨fun tau => c tau - (D'.filter fun s => triType p s = tau).card, ?_⟩
    rw [F1ResidualQuotasStage169.residual_representation p TypedApplicationLinks.F1
      E Q' D' hD' hQ'E (fun tau => (c tau : ℤ)) hc]
    apply sum_congr rfl
    intro tau htau
    rw [Nat.cast_sub (hcap tau htau)]
  · intro v
    have h := residual_degree_after_subpacking p TypedApplicationLinks.F1
      E Q Q' D D' hD hD' hsub v
    have hv := hload v
    rw [hF] at hv
    omega

end PartitionedTriangleAbsorption.BalancedTrimStage170

end

