/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Lemma156

/-!
# The internal surplus (Definition 15.1) and Claims 15.9.1, 15.9.2

* `intSurplus_eq_sum`, `edgeSurp_mk`: `IntSurplus(E) = 2·#internal − #cross`;
* `intSurplus_triEdges`, `intSurplus_biUnion`: an interior triangle has surplus `6`, a cross
  triangle `0`;
* `intSurplus_edgeFinset_eq`: `IntSurplus(G) = ∑_v d(v) − 3 e(V₁, V₂)`;
* `six_dvd_intSurplus`: `6 ∣ IntSurplus(G)` for triangle-divisible `G` (Proposition 15.2);
* `claim_15_9_1`: `IntSurplus(G) ≤ 3γ n²` for `γ`-extremal `G`;
* `claim_15_9_2`: `IntSurplus(G) ≥ 0.06 n |B|`, `B = {v : IntDeg(v) ≥ 0.371 n}`, when
  `δ(G) ≥ 3n/4` and both parts have size `≥ (1 − r) n/2`, `r ≤ 1/10`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Contribution of one edge to `IntSurplus`. -/
def edgeSurp (p : V → Fin 2) (e : Sym2 V) : ℤ :=
  pairVec p e 0 0 + pairVec p e 1 1 - pairVec p e 0 1

omit [Fintype V] [DecidableEq V] in
lemma intSurplus_eq_sum (p : V → Fin 2) (E : Finset (Sym2 V)) :
    intSurplus p E = ∑ e ∈ E, edgeSurp p e := by
  unfold intSurplus edgeVec edgeSurp
  simp only [Finset.sum_apply, sum_add_distrib, sum_sub_distrib]

omit [Fintype V] [DecidableEq V] in
lemma edgeSurp_mk (p : V → Fin 2) (x y : V) :
    edgeSurp p s(x, y) = if p x = p y then 2 else -1 := by
  simp only [edgeSurp, pairVec, Sym2.lift_mk]
  rcases fin2_cases (p x) with h1 | h1 <;> rcases fin2_cases (p y) with h2 | h2 <;>
    simp [h1, h2]

omit [Fintype V] in
lemma intSurplus_union (p : V → Fin 2) {E F : Finset (Sym2 V)} (h : Disjoint E F) :
    intSurplus p (E ∪ F) = intSurplus p E + intSurplus p F := by
  simp only [intSurplus_eq_sum, sum_union h]

omit [Fintype V] in
lemma intSurplus_sdiff (p : V → Fin 2) {E C : Finset (Sym2 V)} (h : C ⊆ E) :
    intSurplus p (E \ C) = intSurplus p E - intSurplus p C := by
  have := intSurplus_union p (sdiff_disjoint : Disjoint (E \ C) C)
  rw [sdiff_union_of_subset h] at this
  linarith

omit [Fintype V] in
lemma triEdges_three {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    triEdges ({x, y, z} : Finset V) = {s(x, y), s(x, z), s(y, z)} := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
  rw [mk_mem_triEdges]
  simp only [mem_insert, mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨ha, hb, hab⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
  · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Ne.symm]

/-- A triangle is *interior* if its three vertices lie in the same part. -/
def IsInteriorTri (p : V → Fin 2) (t : Finset V) : Prop := ∃ i, ∀ x ∈ t, p x = i

omit [Fintype V] [DecidableEq V] in
instance (p : V → Fin 2) (t : Finset V) : Decidable (IsInteriorTri p t) :=
  inferInstanceAs (Decidable (∃ i, ∀ x ∈ t, p x = i))

/-- An interior triangle has surplus `6`, a cross triangle surplus `0`. -/
lemma intSurplus_triEdges (p : V → Fin 2) {t : Finset V} (ht : t.card = 3) :
    intSurplus p (triEdges t) = if IsInteriorTri p t then 6 else 0 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp ht
  rw [triEdges_three hxy hxz hyz, intSurplus_eq_sum]
  have h1 : s(x, y) ∉ ({s(x, z), s(y, z)} : Finset (Sym2 V)) := by
    simp only [mem_insert, mem_singleton, Sym2.eq_iff]; tauto
  have h2 : s(x, z) ∉ ({s(y, z)} : Finset (Sym2 V)) := by
    simp only [mem_singleton, Sym2.eq_iff]; tauto
  rw [sum_insert h1, sum_insert h2, sum_singleton, edgeSurp_mk, edgeSurp_mk, edgeSurp_mk]
  have hint : IsInteriorTri p {x, y, z} ↔ (p x = p y ∧ p y = p z) := by
    constructor
    · rintro ⟨i, hi⟩
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hi
      exact ⟨hi.1.trans hi.2.1.symm, hi.2.1.trans hi.2.2.symm⟩
    · rintro ⟨hp1, hp2⟩
      refine ⟨p x, fun w hw => ?_⟩
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw | hw <;> rw [hw]
      · exact hp1.symm
      · exact (hp1.trans hp2).symm
  rw [if_congr hint rfl rfl]
  rcases fin2_cases (p x) with h1 | h1 <;> rcases fin2_cases (p y) with h2 | h2 <;>
    rcases fin2_cases (p z) with h3 | h3 <;> simp [h1, h2, h3]

/-- The surplus of the edge set of a triangle packing: `6` per interior triangle. -/
lemma intSurplus_biUnion (p : V → Fin 2) (T : Finset (Finset V))
    (hT3 : ∀ t ∈ T, t.card = 3) (hT : (T : Set (Finset V)).PairwiseDisjoint triEdges) :
    intSurplus p (T.biUnion triEdges) =
      6 * ((T.filter (fun t => IsInteriorTri p t)).card : ℤ) := by
  classical
  rw [intSurplus_eq_sum, sum_biUnion hT]
  rw [sum_congr rfl fun t ht => (intSurplus_eq_sum p (triEdges t)).symm.trans
    (intSurplus_triEdges p (hT3 t ht))]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  ring

/-- Summing a degree vector over a part gives the edge vector. -/
lemma sum_partClass_degVec (p : V → Fin 2) (E : Finset (Sym2 V)) (i j : Fin 2) :
    ∑ v ∈ partClass p i, degVec p E v j = edgeVec p E i j := by
  unfold degVec edgeVec
  simp only [Finset.sum_apply]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ x y =>
    simp only [degContrib, pairVec, Sym2.lift_mk]
    rw [sum_add_distrib]
    simp only [ite_and]
    rw [sum_ite_eq, sum_ite_eq]
    simp only [partClass, mem_filter, mem_univ, true_and]

/-- `IntSurplus(G) = ∑_{v ∈ V₁} d₁(v) + ∑_{v ∈ V₂} d₂(v) − e(V₁, V₂)`. -/
lemma intSurplus_edgeFinset_eq (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) :
    intSurplus p G.edgeFinset = (∑ v ∈ partClass p 0, (partDeg G p v 0 : ℤ)) +
      (∑ v ∈ partClass p 1, (partDeg G p v 1 : ℤ)) - cutSize G (partClass p 0) := by
  have h : ∀ i j, edgeVec p G.edgeFinset i j = ∑ v ∈ partClass p i, (partDeg G p v j : ℤ) := by
    intro i j
    rw [← sum_partClass_degVec]
    exact sum_congr rfl fun v _ => degVec_edgeFinset_eq_partDeg G p v j
  unfold intSurplus
  rw [h, h, h, (cutSize_eq_sum_partDeg G p).1]
  push_cast; ring

/-- The degree sum split into internal and cross parts. -/
lemma sum_degree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) :
    (∑ v, (G.degree v : ℤ)) = (∑ v ∈ partClass p 0, (partDeg G p v 0 : ℤ)) +
      (∑ v ∈ partClass p 1, (partDeg G p v 1 : ℤ)) + 2 * cutSize G (partClass p 0) := by
  have hdisj : Disjoint (partClass p 0) (partClass p 1) := by
    refine disjoint_left.mpr fun v h0 h1 => ?_
    simp only [partClass, mem_filter, mem_univ, true_and] at h0 h1
    rw [h0] at h1; exact absurd h1 (by decide)
  have hun : (univ : Finset V) = partClass p 0 ∪ partClass p 1 := by
    ext v; simp only [mem_univ, mem_union, partClass, mem_filter, true_and, true_iff]
    exact fin2_cases (p v)
  obtain ⟨hc0, hc1⟩ := cutSize_eq_sum_partDeg G p
  rw [hun, sum_union hdisj]
  have e : ∀ v, (G.degree v : ℤ) = partDeg G p v 0 + partDeg G p v 1 := fun v => by
    rw [← partDeg_add_partDeg G p v]; push_cast; ring
  simp only [e, sum_add_distrib]
  have h0 : (cutSize G (partClass p 0) : ℤ) = ∑ v ∈ partClass p 0, (partDeg G p v 1 : ℤ) := by
    rw [hc0]; push_cast; rfl
  have h1 : (cutSize G (partClass p 0) : ℤ) = ∑ v ∈ partClass p 1, (partDeg G p v 0 : ℤ) := by
    rw [hc1]; push_cast; rfl
  linarith

/-- `IntSurplus(G) = ∑_v d(v) − 3 e(V₁, V₂)`. -/
lemma intSurplus_eq_sum_degree (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) :
    intSurplus p G.edgeFinset = (∑ v, (G.degree v : ℤ)) - 3 * cutSize G (partClass p 0) := by
  rw [intSurplus_edgeFinset_eq, sum_degree_eq]; ring

/-- **Proposition 15.2.** For a triangle-divisible graph, `6 ∣ IntSurplus(G)`. -/
lemma six_dvd_intSurplus (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (hdiv : NashWilliams.IsTriangleDivisible G) : (6 : ℤ) ∣ intSurplus p G.edgeFinset := by
  rw [intSurplus_eq_sum_degree]
  have hsum : (∑ v, (G.degree v : ℤ)) = 2 * G.edgeFinset.card := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hdiv.1
  -- the cut is even
  have hev00 : Even (edgeVec p G.edgeFinset 0 0) := by
    unfold edgeVec
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.even_sum _ fun e _ => ?_
    induction e using Sym2.ind with
    | _ x y =>
      simp only [pairVec, Sym2.lift_mk]
      by_cases h : p x = 0 ∧ p y = 0
      · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; decide
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]; decide
  have h00 : edgeVec p G.edgeFinset 0 0 = ∑ v ∈ partClass p 0, (partDeg G p v 0 : ℤ) := by
    rw [← sum_partClass_degVec]
    exact sum_congr rfl fun v _ => degVec_edgeFinset_eq_partDeg G p v 0
  have hdeg0 : Even (∑ v ∈ partClass p 0, (G.degree v : ℤ)) :=
    Finset.even_sum _ fun v _ => by exact_mod_cast (hdiv.2 v).natCast
  have hsplit : (∑ v ∈ partClass p 0, (G.degree v : ℤ)) =
      ∑ v ∈ partClass p 0, (partDeg G p v 0 : ℤ) + cutSize G (partClass p 0) := by
    rw [(cutSize_eq_sum_partDeg G p).1]
    push_cast
    rw [← sum_add_distrib]
    exact sum_congr rfl fun v _ => by rw [← partDeg_add_partDeg G p v]; push_cast; ring
  have hcut : Even (cutSize G (partClass p 0) : ℤ) := by
    rw [hsplit, ← h00] at hdeg0
    exact (Int.even_add.mp hdeg0).mp hev00
  obtain ⟨c, hc⟩ := hcut
  rw [hsum, hk, hc]
  push_cast
  exact ⟨k - c, by ring⟩

/-- **Claim 15.9.1.** A `γ`-extremal graph has `IntSurplus(G) ≤ 3γ n²` (the paper states
`2γ n²`; the elementary bound obtained here is `11γ n²/4`). -/
lemma claim_15_9_1 (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {γ : ℝ}
    (hγ : 0 ≤ γ) (hext : IsTwoExtremal γ G p) :
    (intSurplus p G.edgeFinset : ℝ) ≤ 3 * γ * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set good := univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + γ) * Fintype.card V)
  have hdeg : ∀ v, (G.degree v : ℝ) ≤ (3 / 4 + γ) * n + (if v ∈ good then 0 else n) := by
    intro v
    have hdn : (G.degree v : ℝ) ≤ n := by
      have : G.degree v ≤ Fintype.card V := (G.degree_lt_card_verts v).le
      rw [hndef]; exact_mod_cast this
    split_ifs with h
    · simp only [good, mem_filter, mem_univ, true_and] at h; linarith
    · nlinarith
  have hsumdeg : (∑ v, (G.degree v : ℝ)) ≤ n * ((3 / 4 + γ) * n) + (univ \ good).card * n := by
    calc (∑ v, (G.degree v : ℝ)) ≤ ∑ v, ((3 / 4 + γ) * n + (if v ∈ good then 0 else n)) :=
          sum_le_sum fun v _ => hdeg v
      _ = n * ((3 / 4 + γ) * n) + (univ \ good).card * n := by
          have hf : univ.filter (fun v => v ∉ good) = univ \ good := by ext v; simp
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite, sum_const_zero,
            zero_add, sum_const, nsmul_eq_mul, hf]
  have hbad : ((univ \ good).card : ℝ) ≤ γ * n := by
    have h1 : ((univ \ good).card : ℝ) + good.card = n := by
      have := card_sdiff_add_card_eq_card (subset_univ good)
      rw [card_univ] at this; rw [hndef]; exact_mod_cast this
    have h2 := hext.1
    linarith
  have hcut := hext.2
  have hIS := intSurplus_eq_sum_degree G p
  have hIS' : (intSurplus p G.edgeFinset : ℝ) =
      (∑ v, (G.degree v : ℝ)) - 3 * cutSize G (partClass p 0) := by
    rw [hIS]; push_cast; ring
  have hbn : ((univ \ good).card : ℝ) * n ≤ γ * n * n := mul_le_mul_of_nonneg_right hbad hn0
  rw [hIS']
  nlinarith

/-- **Claim 15.9.2.** If `δ(G) ≥ 3n/4` and both parts have size at least `(1 − r) n/2` with
`r ≤ 1/10`, then `IntSurplus(G) ≥ 0.06 n |B|` with `B = {v : IntDeg(v) ≥ 0.371 n}`. -/
lemma claim_15_9_2 (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {r : ℝ}
    (hr : r ≤ 1 / 10) (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree)
    (hcl : ∀ i, (1 - r) * Fintype.card V / 2 ≤ ((partClass p i).card : ℝ)) :
    0.06 * (Fintype.card V : ℝ) *
        ((univ.filter (fun v => 0.371 * (Fintype.card V : ℝ) ≤
          (partDeg G p v (p v) : ℝ))).card : ℝ) ≤
      (intSurplus p G.edgeFinset : ℝ) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set B := univ.filter (fun v => 0.371 * (Fintype.card V : ℝ) ≤ (partDeg G p v (p v) : ℝ))
  set P : V → ℝ := fun v => ((partClass p (p v)).card : ℝ) with hP
  set I : V → ℝ := fun v => (partDeg G p v (p v) : ℝ) with hI
  set d : V → ℝ := fun v => (G.degree v : ℝ) with hd
  -- per-vertex quantities
  have hsize : ((partClass p 0).card : ℝ) + (partClass p 1).card = n := by
    have := card_partClass_add p; simp only [hndef]; exact_mod_cast this
  have hcross : ∀ v, d v - I v ≤ n - P v := by
    intro v
    have h1 := partDeg_add_partDeg G p v
    have h2 := partDeg_le_card_partClass G p v 0
    have h3 := partDeg_le_card_partClass G p v 1
    simp only [hd, hI, hP]
    rcases fin2_cases (p v) with h | h <;> rw [h]
    · have : (G.degree v : ℝ) = partDeg G p v 0 + partDeg G p v 1 := by exact_mod_cast h1.symm
      have : (partDeg G p v 1 : ℝ) ≤ (partClass p 1).card := by exact_mod_cast h3
      linarith
    · have : (G.degree v : ℝ) = partDeg G p v 0 + partDeg G p v 1 := by exact_mod_cast h1.symm
      have : (partDeg G p v 0 : ℝ) ≤ (partClass p 0).card := by exact_mod_cast h2
      linarith
  have hdmin : ∀ v, 3 / 4 * n ≤ d v := by
    intro v
    have h1 := G.minDegree_le_degree v
    have : (3 : ℝ) * n ≤ 4 * G.minDegree := by simp only [hndef]; exact_mod_cast hδ
    have : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast h1
    simp only [hd]; linarith
  have hPv : ∀ v, (1 - r) * n / 2 ≤ n - P v := by
    intro v
    simp only [hP]
    rcases fin2_cases (p v) with h | h <;> rw [h]
    · have := hcl 1; linarith
    · have := hcl 0; linarith
  -- `2 IntSurplus = ∑ (3 I − d)`
  have hIS2 : 2 * (intSurplus p G.edgeFinset : ℝ) = ∑ v, (3 * I v - d v) := by
    have e1 := intSurplus_edgeFinset_eq G p
    have e2 := sum_degree_eq G p
    have hdisj : Disjoint (partClass p 0) (partClass p 1) := by
      refine disjoint_left.mpr fun v h0 h1 => ?_
      simp only [partClass, mem_filter, mem_univ, true_and] at h0 h1
      rw [h0] at h1; exact absurd h1 (by decide)
    have hun : (univ : Finset V) = partClass p 0 ∪ partClass p 1 := by
      ext v; simp only [mem_univ, mem_union, partClass, mem_filter, true_and, true_iff]
      exact fin2_cases (p v)
    have hIsum : (∑ v, I v) = (∑ v ∈ partClass p 0, (partDeg G p v 0 : ℝ)) +
        ∑ v ∈ partClass p 1, (partDeg G p v 1 : ℝ) := by
      rw [hun, sum_union hdisj]
      congr 1
      · refine sum_congr rfl fun v hv => ?_
        simp only [partClass, mem_filter, mem_univ, true_and] at hv
        simp only [hI, hv]
      · refine sum_congr rfl fun v hv => ?_
        simp only [partClass, mem_filter, mem_univ, true_and] at hv
        simp only [hI, hv]
    have e1' : (intSurplus p G.edgeFinset : ℝ) = (∑ v ∈ partClass p 0, (partDeg G p v 0 : ℝ)) +
        (∑ v ∈ partClass p 1, (partDeg G p v 1 : ℝ)) - cutSize G (partClass p 0) := by
      rw [e1]; push_cast; ring
    have e2' : (∑ v, d v) = (∑ v ∈ partClass p 0, (partDeg G p v 0 : ℝ)) +
        (∑ v ∈ partClass p 1, (partDeg G p v 1 : ℝ)) + 2 * cutSize G (partClass p 0) := by
      simp only [hd]; exact_mod_cast e2
    rw [sum_sub_distrib, ← mul_sum, hIsum, e1', e2']
    ring
  -- `∑ (3P − 3n/2) ≥ 0`
  have hPsum : 0 ≤ ∑ v, (3 * P v - 3 / 2 * n) := by
    have hdisj : Disjoint (partClass p 0) (partClass p 1) := by
      refine disjoint_left.mpr fun v h0 h1 => ?_
      simp only [partClass, mem_filter, mem_univ, true_and] at h0 h1
      rw [h0] at h1; exact absurd h1 (by decide)
    have hun : (univ : Finset V) = partClass p 0 ∪ partClass p 1 := by
      ext v; simp only [mem_univ, mem_union, partClass, mem_filter, true_and, true_iff]
      exact fin2_cases (p v)
    have e : ∑ v, (3 * P v - 3 / 2 * n) =
        3 * (((partClass p 0).card : ℝ) ^ 2 + ((partClass p 1).card : ℝ) ^ 2) -
          3 / 2 * n * n := by
      rw [sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, hun,
        sum_union hdisj]
      have a0 : ∑ v ∈ partClass p 0, P v = ((partClass p 0).card : ℝ) ^ 2 := by
        have hc : ∀ v ∈ partClass p 0, P v = ((partClass p 0).card : ℝ) := fun v hv => by
          simp only [partClass, mem_filter, mem_univ, true_and] at hv
          simp only [hP, hv]
        rw [sum_congr rfl hc, sum_const, nsmul_eq_mul]; ring
      have a1 : ∑ v ∈ partClass p 1, P v = ((partClass p 1).card : ℝ) ^ 2 := by
        have hc : ∀ v ∈ partClass p 1, P v = ((partClass p 1).card : ℝ) := fun v hv => by
          simp only [partClass, mem_filter, mem_univ, true_and] at hv
          simp only [hP, hv]
        rw [sum_congr rfl hc, sum_const, nsmul_eq_mul]; ring
      rw [a0, a1, hndef]
      ring
    rw [e, ← hsize]
    nlinarith [sq_nonneg (((partClass p 0).card : ℝ) - (partClass p 1).card)]
  -- per-vertex lower bound
  set g : V → ℝ := fun v => 3 * I v - d v - (3 * P v - 3 / 2 * n) with hg
  have hg0 : ∀ v, 0 ≤ g v := by
    intro v
    have := hcross v; have := hdmin v
    simp only [hg]; linarith
  have hgB : ∀ v ∈ B, 0.12 * n ≤ g v := by
    intro v hv
    simp only [B, mem_filter, mem_univ, true_and] at hv
    have h1 := hcross v; have h2 := hPv v
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hrn : r * n ≤ 1 / 10 * n := mul_le_mul_of_nonneg_right hr hn0
    simp only [hg]
    simp only [hI] at hv h1 ⊢
    linarith
  have hsumg : 0.12 * n * B.card ≤ ∑ v, g v := by
    calc 0.12 * n * B.card = ∑ v ∈ B, 0.12 * n := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ v ∈ B, g v := sum_le_sum hgB
      _ ≤ ∑ v, g v := sum_le_sum_of_subset_of_nonneg (subset_univ B) fun v _ _ => hg0 v
  have hsplit : ∑ v, (3 * I v - d v) = ∑ v, g v + ∑ v, (3 * P v - 3 / 2 * n) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => by simp only [hg]; ring
  linarith

end NashWilliams18
