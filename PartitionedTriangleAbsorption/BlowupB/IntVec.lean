/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Defs

/-! # BlowupB.IntVec — aggregate divisibility and physical certificates for integer edge vectors

The reduction of the "Theorem B" route manipulates `ℤ`-valued edge functions (indicators of edge
sets with multiplicities and signs). This module provides:

* `edgeVecZ`, `degVecZ` — the aggregate vectors of an integer edge function, agreeing with
  `edgeVec`, `degVec` on indicators, and linear;
* `AggDivZ` — Definition 13.5 for integer edge functions; a lattice (closed under `+`, `-`, `•`),
  agreeing with `IsIntDiv` on indicators, containing every copy;
* `PhysCertZ`, `PhysCostZ` — physical certificates of integer edge functions with cost bounds,
  closed under sums with additive cost, and implying `AggDivZ`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### Aggregate vectors of integer edge functions -/

/-- The edge-count vector of an integer edge function. -/
def edgeVecZ (p : V → Fin t) (w : Sym2 V → ℤ) : Fin t → Fin t → ℤ :=
  ∑ e, w e • pairVec p e

/-- The degree vector of an integer edge function at `v`. -/
def degVecZ (p : V → Fin t) (w : Sym2 V → ℤ) (v : V) : Fin t → ℤ :=
  ∑ e, w e • degContrib p v e

theorem edgeVecZ_indZ (p : V → Fin t) (E : Finset (Sym2 V)) :
    edgeVecZ p (indZ E) = edgeVec p E :=
  (edgeVec_eq_sum_indZ p E).symm

theorem degVecZ_indZ (p : V → Fin t) (E : Finset (Sym2 V)) (v : V) :
    degVecZ p (indZ E) v = degVec p E v :=
  (degVec_eq_sum_indZ p E v).symm

omit [DecidableEq V] in
theorem edgeVecZ_add (p : V → Fin t) (w₁ w₂ : Sym2 V → ℤ) :
    edgeVecZ p (w₁ + w₂) = edgeVecZ p w₁ + edgeVecZ p w₂ := by
  simp only [edgeVecZ, Pi.add_apply, add_smul, sum_add_distrib]

omit [DecidableEq V] in
theorem edgeVecZ_smul (p : V → Fin t) (a : ℤ) (w : Sym2 V → ℤ) :
    edgeVecZ p (a • w) = a • edgeVecZ p w := by
  simp only [edgeVecZ, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum]

omit [DecidableEq V] in
theorem edgeVecZ_neg (p : V → Fin t) (w : Sym2 V → ℤ) :
    edgeVecZ p (-w) = -edgeVecZ p w := by
  simp only [edgeVecZ, Pi.neg_apply, neg_smul, sum_neg_distrib]

omit [DecidableEq V] in
theorem edgeVecZ_sub (p : V → Fin t) (w₁ w₂ : Sym2 V → ℤ) :
    edgeVecZ p (w₁ - w₂) = edgeVecZ p w₁ - edgeVecZ p w₂ := by
  rw [sub_eq_add_neg, edgeVecZ_add, edgeVecZ_neg, sub_eq_add_neg]

omit [DecidableEq V] in
theorem edgeVecZ_zero (p : V → Fin t) : edgeVecZ p (0 : Sym2 V → ℤ) = 0 := by
  simp [edgeVecZ]

theorem degVecZ_add (p : V → Fin t) (w₁ w₂ : Sym2 V → ℤ) (v : V) :
    degVecZ p (w₁ + w₂) v = degVecZ p w₁ v + degVecZ p w₂ v := by
  simp only [degVecZ, Pi.add_apply, add_smul, sum_add_distrib]

theorem degVecZ_smul (p : V → Fin t) (a : ℤ) (w : Sym2 V → ℤ) (v : V) :
    degVecZ p (a • w) v = a • degVecZ p w v := by
  simp only [degVecZ, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum]

theorem degVecZ_neg (p : V → Fin t) (w : Sym2 V → ℤ) (v : V) :
    degVecZ p (-w) v = -degVecZ p w v := by
  simp only [degVecZ, Pi.neg_apply, neg_smul, sum_neg_distrib]

theorem degVecZ_sub (p : V → Fin t) (w₁ w₂ : Sym2 V → ℤ) (v : V) :
    degVecZ p (w₁ - w₂) v = degVecZ p w₁ v - degVecZ p w₂ v := by
  rw [sub_eq_add_neg, degVecZ_add, degVecZ_neg, sub_eq_add_neg]

theorem degVecZ_zero (p : V → Fin t) (v : V) : degVecZ p (0 : Sym2 V → ℤ) v = 0 := by
  simp [degVecZ]

/-! ### Aggregate divisibility of integer edge functions -/

/-- **Aggregate `F`-divisibility** of an integer edge function (Definition 13.5): the edge-count
vector lies in the lattice of the type edge vectors and every degree vector lies in the lattice of
the corresponding type degree vectors. -/
def AggDivZ (p : V → Fin t) (F : Finset (Multiset (Fin t))) (w : Sym2 V → ℤ) : Prop :=
  (∃ c : Multiset (Fin t) → ℤ, edgeVecZ p w = ∑ τ ∈ F, c τ • typeEdgeVec τ) ∧
    ∀ v : V, ∃ c : Multiset (Fin t) → ℤ,
      degVecZ p w v = ∑ τ ∈ F with p v ∈ τ, c τ • typeDegVec τ (p v)

theorem aggDivZ_indZ_iff (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (E : Finset (Sym2 V)) : AggDivZ p F (indZ E) ↔ IsIntDiv p F E := by
  unfold AggDivZ IsIntDiv
  rw [edgeVecZ_indZ]
  simp_rw [degVecZ_indZ]

theorem AggDivZ.zero (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    AggDivZ p F (0 : Sym2 V → ℤ) :=
  ⟨⟨0, by simp [edgeVecZ_zero]⟩, fun v => ⟨0, by simp [degVecZ_zero]⟩⟩

theorem AggDivZ.add {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w₁ w₂ : Sym2 V → ℤ}
    (h₁ : AggDivZ p F w₁) (h₂ : AggDivZ p F w₂) : AggDivZ p F (w₁ + w₂) := by
  obtain ⟨⟨c₁, hc₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨c₂, hc₂⟩, hl₂⟩ := h₂
  refine ⟨⟨c₁ + c₂, ?_⟩, fun v => ?_⟩
  · rw [edgeVecZ_add, hc₁, hc₂, ← sum_add_distrib]
    exact sum_congr rfl fun τ _ => by rw [Pi.add_apply, add_smul]
  · obtain ⟨d₁, hd₁⟩ := hl₁ v
    obtain ⟨d₂, hd₂⟩ := hl₂ v
    refine ⟨d₁ + d₂, ?_⟩
    rw [degVecZ_add, hd₁, hd₂, ← sum_add_distrib]
    exact sum_congr rfl fun τ _ => by rw [Pi.add_apply, add_smul]

theorem AggDivZ.smul {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w : Sym2 V → ℤ}
    (h : AggDivZ p F w) (a : ℤ) : AggDivZ p F (a • w) := by
  obtain ⟨⟨c, hc⟩, hl⟩ := h
  refine ⟨⟨a • c, ?_⟩, fun v => ?_⟩
  · rw [edgeVecZ_smul, hc, smul_sum]
    exact sum_congr rfl fun τ _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  · obtain ⟨d, hd⟩ := hl v
    refine ⟨a • d, ?_⟩
    rw [degVecZ_smul, hd, smul_sum]
    exact sum_congr rfl fun τ _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

theorem AggDivZ.neg {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w : Sym2 V → ℤ}
    (h : AggDivZ p F w) : AggDivZ p F (-w) := by
  have := h.smul (-1)
  rwa [neg_one_smul] at this

theorem AggDivZ.sub {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w₁ w₂ : Sym2 V → ℤ}
    (h₁ : AggDivZ p F w₁) (h₂ : AggDivZ p F w₂) : AggDivZ p F (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

theorem AggDivZ.sum {p : V → Fin t} {F : Finset (Multiset (Fin t))} {ι : Type*}
    (s : Finset ι) (f : ι → Sym2 V → ℤ) (h : ∀ i ∈ s, AggDivZ p F (f i)) :
    AggDivZ p F (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact AggDivZ.zero p F
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- The indicator of a typed triangle is aggregate divisible. -/
theorem aggDivZ_triEdges {p : V → Fin t} {F : Finset (Multiset (Fin t))} {s : Finset V}
    (hs : s.card = 3) (hF : triType p s ∈ F) : AggDivZ p F (indZ (triEdges s)) := by
  rw [aggDivZ_indZ_iff]
  exact isIntDiv_of_hasDecomp ⟨{s}, ⟨fun x hx => by
      rw [mem_singleton] at hx; subst hx; exact ⟨hs, hF⟩,
    by simp [Set.PairwiseDisjoint, Set.Pairwise], by simp⟩⟩

/-! ### Physical certificates of integer edge functions -/

/-- **Physical certificate** of an integer edge function `w`: `F`-copies `T j` of `G` and integer
coefficients with `w = ∑ j, c j · ind (E(T j))`. -/
def PhysCertZ (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (w : Sym2 V → ℤ) {ι : Type*} [Fintype ι] (T : ι → Finset V) (c : ι → ℤ) : Prop :=
  (∀ j, IsCopy p F G (T j)) ∧ ∀ e, w e = ∑ j, c j * indZ (triEdges (T j)) e

/-- `w` has a physical certificate of cost at most `K`. -/
def PhysCostZ (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (w : Sym2 V → ℤ) (K : ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : ι → Finset V) (c : ι → ℤ),
    PhysCertZ p F G w T c ∧ ∑ j, |c j| ≤ K

omit [Fintype V] in
theorem physCertZ_indZ_iff {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {E : Finset (Sym2 V)} {ι : Type*} [Fintype ι] {T : ι → Finset V} {c : ι → ℤ} :
    PhysCertZ p F G (indZ E) T c ↔ PhysCert p F G E T c := Iff.rfl

omit [Fintype V] in
theorem physDivCost_iff_physCostZ {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {E : Finset (Sym2 V)} {K : ℤ} :
    PhysDivCost p F G E K ↔ PhysCostZ p F G (indZ E) K := Iff.rfl

omit [Fintype V] in
/-- A single copy certifies its own indicator at cost `1`. -/
theorem physCostZ_of_isCopy {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {s : Finset V} (hs : IsCopy p F G s) : PhysCostZ p F G (indZ (triEdges s)) 1 :=
  ⟨Unit, inferInstance, fun _ => s, fun _ => 1, ⟨fun _ => hs, fun e => by simp⟩, by simp⟩

omit [Fintype V] in
theorem PhysCostZ.zero (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) :
    PhysCostZ p F G (0 : Sym2 V → ℤ) 0 :=
  ⟨Fin 0, inferInstance, fun j => absurd j.2 (Nat.not_lt_zero _), fun _ => 0,
    ⟨fun j => absurd j.2 (Nat.not_lt_zero _), fun e => by simp⟩, by simp⟩

omit [Fintype V] in
theorem PhysCostZ.mono {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K K' : ℤ} (h : PhysCostZ p F G w K) (hK : K ≤ K') :
    PhysCostZ p F G w K' := by
  obtain ⟨ι, hι, T, c, hc, hK₀⟩ := h
  exact ⟨ι, hι, T, c, hc, hK₀.trans hK⟩

omit [Fintype V] in
theorem PhysCostZ.congr {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w w' : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) (hw : w = w') :
    PhysCostZ p F G w' K := hw ▸ h

omit [Fintype V] in
theorem PhysCostZ.add {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w₁ w₂ : Sym2 V → ℤ} {K₁ K₂ : ℤ} (h₁ : PhysCostZ p F G w₁ K₁) (h₂ : PhysCostZ p F G w₂ K₂) :
    PhysCostZ p F G (w₁ + w₂) (K₁ + K₂) := by
  obtain ⟨ι₁, hι₁, T₁, c₁, ⟨hT₁, hw₁⟩, hK₁⟩ := h₁
  obtain ⟨ι₂, hι₂, T₂, c₂, ⟨hT₂, hw₂⟩, hK₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim T₁ T₂, Sum.elim c₁ c₂, ⟨?_, fun e => ?_⟩, ?_⟩
  · rintro (j | j)
    · exact hT₁ j
    · exact hT₂ j
  · rw [Pi.add_apply, hw₁ e, hw₂ e, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_le_add hK₁ hK₂

omit [Fintype V] in
theorem PhysCostZ.smul {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) (a : ℤ) :
    PhysCostZ p F G (a • w) (|a| * K) := by
  obtain ⟨ι, hι, T, c, ⟨hT, hw⟩, hK⟩ := h
  refine ⟨ι, hι, T, a • c, ⟨hT, fun e => ?_⟩, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, hw e, mul_sum]
    exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · calc ∑ j, |(a • c) j| = |a| * ∑ j, |c j| := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      _ ≤ |a| * K := mul_le_mul_of_nonneg_left hK (abs_nonneg a)

omit [Fintype V] in
theorem PhysCostZ.neg {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) : PhysCostZ p F G (-w) K := by
  have := h.smul (-1)
  rwa [neg_one_smul, abs_neg, abs_one, one_mul] at this

omit [Fintype V] in
theorem PhysCostZ.sub {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w₁ w₂ : Sym2 V → ℤ} {K₁ K₂ : ℤ} (h₁ : PhysCostZ p F G w₁ K₁) (h₂ : PhysCostZ p F G w₂ K₂) :
    PhysCostZ p F G (w₁ - w₂) (K₁ + K₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

omit [Fintype V] in
theorem PhysCostZ.sum {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ) (K : ι → ℤ)
    (h : ∀ i ∈ s, PhysCostZ p F G (f i) (K i)) :
    PhysCostZ p F G (∑ i ∈ s, f i) (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact PhysCostZ.zero p F G
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-! ### Physical ⇒ aggregate, for integer edge functions -/

/-- A physical certificate of an integer edge function yields aggregate divisibility. -/
theorem aggDivZ_of_physCertZ {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {ι : Type*} [Fintype ι] {T : ι → Finset V} {c : ι → ℤ}
    (h : PhysCertZ p F G w T c) : AggDivZ p F w := by
  obtain ⟨hcopy, hid⟩ := h
  have hw : w = ∑ j, c j • indZ (triEdges (T j)) := by
    funext e; rw [hid e, Finset.sum_apply]
    exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]
  rw [hw]
  exact AggDivZ.sum univ _ fun j _ =>
    (aggDivZ_triEdges (hcopy j).1.card_eq (hcopy j).2).smul (c j)

theorem aggDivZ_of_physCostZ {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) : AggDivZ p F w := by
  obtain ⟨ι, _, T, c, hc, _⟩ := h
  exact aggDivZ_of_physCertZ hc

end PartitionedTriangleAbsorption.BlowupB
