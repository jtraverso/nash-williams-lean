/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.RepHost

/-! # BlowupB.Rainbow — the unconditional case of rainbow families

A family `F` is **rainbow** when every type consists of three distinct classes (as the family
`F₃` of the four triangles of `K₄`). For rainbow families one representative per class suffices
and the residual on the representatives is trivially physical, so the reduction needs no finite
hypothesis: `physDiv_of_isIntDiv_rainbow` — in any complete `F`-blowup (`F` rainbow, every class
non-empty), integral `F`-divisibility implies physical divisibility.

The file first records the generic shape of steps 1 and 2 for an arbitrary *spoke system*
`S : V → Fin t → (Sym2 V → ℤ)` (`step1_of`, `step2_of`), then instantiates it with the spokes
`ind1 s(x, r k)` of a transversal `r`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### Generic spoke systems -/

section Generic

variable (p : V → Fin t) (S : V → Fin t → Sym2 V → ℤ)

/-- The two spokes of an edge in a spoke system `S`: each endpoint into the class of the other. -/
def spkOf (e : Sym2 V) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun u v => S u (p v) + S v (p u), fun _ _ => add_comm _ _⟩ e

omit [Fintype V] [DecidableEq V] in
theorem spkOf_mk (u v : V) : spkOf p S s(u, v) = S u (p v) + S v (p u) := rfl

theorem spkOf_eq_sum (e : Sym2 V) :
    spkOf p S e = ∑ x, ∑ k, degContrib p x e k • S x k := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [spkOf_mk]
    simp only [degContrib, Sym2.lift_mk, add_smul, sum_add_distrib]
    rw [sum_sum_ite_pair, sum_sum_ite_pair]

theorem sum_spkOf (E : Finset (Sym2 V)) :
    ∑ e ∈ E, spkOf p S e = ∑ x, ∑ k, degVec p E x k • S x k := by
  simp_rw [spkOf_eq_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [degVec, Finset.sum_apply, sum_smul]

variable {p S}

/-- Generic step 1: if every edge of `E` reduces to its spokes at cost `K₀`, then `E` reduces
to the canonical form at cost `K₀ |E|`. -/
theorem step1_of {q : ℕ} {R : Reps p q} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {K₀ : ℤ} {E : Finset (Sym2 V)}
    (hedge : ∀ e ∈ E, ∃ w : Sym2 V → ℤ, OnReps R w ∧
      PhysCostZ p F G (ind1 e - (spkOf p S e + w)) K₀) :
    ∃ wRR : Sym2 V → ℤ, OnReps R wRR ∧
      PhysCostZ p F G (indZ E - (∑ x, ∑ k, degVec p E x k • S x k + wRR)) (K₀ * E.card) := by
  have key : ∀ e : Sym2 V, ∃ w : Sym2 V → ℤ, e ∈ E →
      OnReps R w ∧ PhysCostZ p F G (ind1 e - (spkOf p S e + w)) K₀ := by
    intro e
    by_cases he : e ∈ E
    · obtain ⟨w, hw, hc⟩ := hedge e he
      exact ⟨w, fun _ => ⟨hw, hc⟩⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose w hw using key
  refine ⟨∑ e ∈ E, w e, OnReps.sum _ _ (fun e he => (hw e he).1), ?_⟩
  have hrw : indZ E - (∑ x, ∑ k, degVec p E x k • S x k + ∑ e ∈ E, w e) =
      ∑ e ∈ E, (ind1 e - (spkOf p S e + w e)) := by
    rw [← sum_spkOf, indZ_eq_sum_ind1, sum_sub_distrib, sum_add_distrib]
  rw [hrw]
  refine (PhysCostZ.sum E _ (fun _ => K₀) (fun e he => (hw e he).2)).mono ?_
  rw [sum_const, nsmul_eq_mul, mul_comm]

omit [Fintype V] in
/-- Generic step 2 at a vertex. -/
theorem star_vertex_of {q : ℕ} {R : Reps p q} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {K₀ : ℤ} (x : V)
    (hS : ∀ τ ∈ F, p x ∈ τ → ∃ w : Sym2 V → ℤ, OnReps R w ∧
      PhysCostZ p F G (∑ l, typeDegVec τ (p x) l • S x l - w) K₀)
    {d : Fin t → ℤ} {c : Multiset (Fin t) → ℤ}
    (hd : d = ∑ τ ∈ F with p x ∈ τ, c τ • typeDegVec τ (p x)) :
    ∃ wRR : Sym2 V → ℤ, OnReps R wRR ∧
      PhysCostZ p F G (∑ l, d l • S x l - wRR) (K₀ * ∑ τ ∈ F with p x ∈ τ, |c τ|) := by
  have hexp : ∑ l, d l • S x l =
      ∑ τ ∈ F with p x ∈ τ, c τ • ∑ l, typeDegVec τ (p x) l • S x l := by
    subst hd
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_smul, mul_smul, smul_sum]
    rw [sum_comm]
  have key : ∀ τ : Multiset (Fin t), ∃ w : Sym2 V → ℤ, τ ∈ F.filter (p x ∈ ·) →
      OnReps R w ∧ PhysCostZ p F G (∑ l, typeDegVec τ (p x) l • S x l - w) K₀ := by
    intro τ
    by_cases hτ : τ ∈ F.filter (p x ∈ ·)
    · obtain ⟨hτF, hxτ⟩ := mem_filter.mp hτ
      obtain ⟨w, hw, hc⟩ := hS τ hτF hxτ
      exact ⟨w, fun _ => ⟨hw, hc⟩⟩
    · exact ⟨0, fun h => absurd h hτ⟩
  choose w hw using key
  refine ⟨∑ τ ∈ F with p x ∈ τ, c τ • w τ,
    OnReps.sum _ _ (fun τ hτ => ((hw τ hτ).1).smul _), ?_⟩
  rw [hexp, ← sum_sub_distrib]
  simp_rw [← smul_sub]
  refine (PhysCostZ.sum _ _ (fun τ => |c τ| * K₀) (fun τ hτ => ((hw τ hτ).2).smul (c τ))).mono ?_
  rw [mul_sum]
  exact le_of_eq (sum_congr rfl fun τ _ => mul_comm _ _)

/-- Generic step 2. -/
theorem step2_of {q : ℕ} {R : Reps p q} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {K₀ : ℤ}
    (hS : ∀ x : V, ∀ τ ∈ F, p x ∈ τ → ∃ w : Sym2 V → ℤ, OnReps R w ∧
      PhysCostZ p F G (∑ l, typeDegVec τ (p x) l • S x l - w) K₀)
    {E : Finset (Sym2 V)} (hdiv : IsIntDiv p F E) :
    ∃ (wRR : Sym2 V → ℤ) (K : ℤ), OnReps R wRR ∧
      PhysCostZ p F G (∑ x, ∑ l, degVec p E x l • S x l - wRR) K := by
  choose c hc using hdiv.2
  have key : ∀ x : V, ∃ w : Sym2 V → ℤ, OnReps R w ∧
      PhysCostZ p F G (∑ l, degVec p E x l • S x l - w)
        (K₀ * ∑ τ ∈ F with p x ∈ τ, |c x τ|) :=
    fun x => star_vertex_of x (hS x) (hc x)
  choose w hw using key
  refine ⟨∑ x, w x, ∑ x, K₀ * ∑ τ ∈ F with p x ∈ τ, |c x τ|,
    OnReps.sum _ _ (fun x _ => (hw x).1), ?_⟩
  rw [← sum_sub_distrib]
  exact PhysCostZ.sum _ _ _ (fun x _ => (hw x).2)

end Generic

/-! ### Rainbow families and transversals -/

/-- Every type of `F` has three distinct classes. -/
def IsRainbow (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ τ ∈ F, Multiset.card τ = 3 ∧ τ.Nodup

theorem IsRainbow.card3 {F : Finset (Multiset (Fin t))} (hR : IsRainbow F) :
    ∀ τ ∈ F, Multiset.card τ = 3 := fun τ hτ => (hR τ hτ).1

theorem allowedPair_ne {F : Finset (Multiset (Fin t))} (hR : IsRainbow F) {i j : Fin t}
    (h : AllowedPair F i j) : i ≠ j := by
  obtain ⟨τ, hτ, _, hle⟩ := h
  intro hij
  subst hij
  have h1 := Multiset.nodup_iff_count_le_one.mp (hR τ hτ).2 i
  have h2 := Multiset.le_iff_count.mp hle i
  simp at h2
  omega

theorem nodup_three_iff {α : Type*} (x y z : α) :
    ({x, y, z} : Multiset α).Nodup ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
    Multiset.mem_singleton, Multiset.nodup_singleton, not_or, and_true]
  tauto

theorem third_ne {F : Finset (Multiset (Fin t))} (hR : IsRainbow F) {i j : Fin t}
    (h : AllowedPair F i j) : third F i j h ≠ i ∧ third F i j h ≠ j := by
  have hnd := (hR _ (third_spec F i j h)).2
  rw [nodup_three_iff] at hnd
  exact ⟨fun e => hnd.2.1 e.symm, fun e => hnd.2.2 e.symm⟩

variable {p : V → Fin t}

/-- One representative per class as a `Reps p 1`. -/
def Reps.ofTransversal (r : Fin t → V) (hr : ∀ i, p (r i) = i) : Reps p 1 where
  rep i _ := r i
  inj i _ i' _ h := ⟨by have := congrArg p h; rwa [hr, hr] at this, Subsingleton.elim _ _⟩
  cls i _ := hr i

omit [Fintype V] in
theorem Reps.ofTransversal_mem (r : Fin t → V) (hr : ∀ i, p (r i) = i) (i : Fin t) :
    r i ∈ (Reps.ofTransversal r hr).set :=
  (Reps.ofTransversal r hr).rep_mem i 0

omit [Fintype V] in
theorem Reps.ofTransversal_mem_iff (r : Fin t → V) (hr : ∀ i, p (r i) = i) {v : V} :
    v ∈ (Reps.ofTransversal r hr).set ↔ ∃ i, r i = v := by
  rw [Reps.mem_set_iff]
  constructor
  · rintro ⟨i, _, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨i, 0, h⟩

omit [Fintype V] [DecidableEq V] in
theorem ne_r_of_cls {r : Fin t → V} (hr : ∀ i, p (r i) = i) {x : V} {k : Fin t}
    (h : p x ≠ k) : x ≠ r k := fun e => h (by rw [e, hr])

omit [Fintype V] [DecidableEq V] in
theorem r_inj {r : Fin t → V} (hr : ∀ i, p (r i) = i) {a b : Fin t} (e : r a = r b) : a = b := by
  have := congrArg p e; rwa [hr, hr] at this

omit [Fintype V] [DecidableEq V] in
theorem r_injective {r : Fin t → V} (hr : ∀ i, p (r i) = i) : Function.Injective r :=
  fun _ _ e => r_inj hr e

/-- The spokes of a transversal. -/
def sp (r : Fin t → V) (x : V) (k : Fin t) : Sym2 V → ℤ := ind1 s(x, r k)

/-! ### Step 1 (rainbow) -/

omit [Fintype V] in
theorem rect_identity_rb {u v a b c : V} (huv : u ≠ v) (hua : u ≠ a) (huc : u ≠ c)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ind1 s(u, v) - (ind1 s(u, c) + ind1 s(v, b) + (-(ind1 s(b, c)))) =
      indZ (triEdges {u, a, v}) - indZ (triEdges {u, a, c}) - indZ (triEdges {b, a, v}) +
        indZ (triEdges {b, a, c}) := by
  rw [indZ_triEdges_three hua huv hva.symm, indZ_triEdges_three hua huc hac,
    indZ_triEdges_three hab.symm hvb.symm hva.symm, indZ_triEdges_three hab.symm hbc hac,
    ind1_swap b v]
  abel

omit [Fintype V] in
theorem edge_step_rb {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) (hR : IsRainbow F) (r : Fin t → V) (hr : ∀ i, p (r i) = i)
    {u v : V} (huv : G.Adj u v) :
    ∃ wRR : Sym2 V → ℤ, OnReps (Reps.ofTransversal r hr) wRR ∧
      PhysCostZ p F G (ind1 s(u, v) - (spkOf p (sp r) s(u, v) + wRR)) 4 := by
  have hne : u ≠ v := G.ne_of_adj huv
  have hA : AllowedPair F (p u) (p v) := allowedPair_of_adj hG huv
  have hij : p u ≠ p v := allowedPair_ne hR hA
  have hτ := third_spec F (p u) (p v) hA
  obtain ⟨hki, hkj⟩ := third_ne hR hA
  set k := third F (p u) (p v) hA with hk
  have hτ' : ({p u, k, p v} : Multiset (Fin t)) ∈ F := by rw [three_swap23]; exact hτ
  have hua : u ≠ r k := ne_r_of_cls hr (Ne.symm hki)
  have huc : u ≠ r (p v) := ne_r_of_cls hr hij
  have hva : v ≠ r k := ne_r_of_cls hr (Ne.symm hkj)
  have hvb : v ≠ r (p u) := ne_r_of_cls hr (Ne.symm hij)
  have hab : r k ≠ r (p u) := fun e => hki (r_inj hr e)
  have hac : r k ≠ r (p v) := fun e => hkj (r_inj hr e)
  have hbc : r (p u) ≠ r (p v) := fun e => hij (r_inj hr e)
  have hT1 := physCostZ_of_isCopy (isCopy_of_complete hG hua hne hva.symm
    (by simp only [hr]; exact hτ'))
  have hT2 := physCostZ_of_isCopy (isCopy_of_complete hG hua huc hac
    (by simp only [hr]; exact hτ'))
  have hT3 := physCostZ_of_isCopy (isCopy_of_complete hG hab.symm hvb.symm hva.symm
    (by simp only [hr]; exact hτ'))
  have hT4 := physCostZ_of_isCopy (isCopy_of_complete hG hab.symm hbc hac
    (by simp only [hr]; exact hτ'))
  have hsum := ((hT1.sub hT2).sub hT3).add hT4
  refine ⟨-(ind1 s(r (p u), r (p v))),
    (OnReps.ind1 (Reps.ofTransversal_mem r hr _) (Reps.ofTransversal_mem r hr _)).neg, ?_⟩
  refine (hsum.congr ?_).mono (by norm_num)
  rw [spkOf_mk]
  unfold sp
  exact (rect_identity_rb hne hua huc hva hvb hab hac hbc).symm

/-! ### Step 2 (rainbow) -/

omit [Fintype V] in
theorem sum_typeDegVec_sp (r : Fin t → V) (x : V) (k k' : Fin t) :
    ∑ l, typeDegVec {p x, k, k'} (p x) l • sp r x l = sp r x k + sp r x k' := by
  simp only [typeDegVec_three, add_smul, sum_add_distrib, ite_smul, one_smul, zero_smul,
    sum_ite_eq, mem_univ, if_true]

omit [Fintype V] in
theorem star_type_rb {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) (hR : IsRainbow F) (r : Fin t → V) (hr : ∀ i, p (r i) = i)
    (x : V) {τ : Multiset (Fin t)} (hτ : τ ∈ F) (hi : p x ∈ τ) :
    ∃ wRR : Sym2 V → ℤ, OnReps (Reps.ofTransversal r hr) wRR ∧
      PhysCostZ p F G (∑ l, typeDegVec τ (p x) l • sp r x l - wRR) 1 := by
  obtain ⟨hc, hnd⟩ := hR τ hτ
  obtain ⟨τ', rfl⟩ := Multiset.exists_cons_of_mem hi
  have hc' : Multiset.card τ' = 2 := by rw [Multiset.card_cons] at hc; omega
  obtain ⟨k, k', rfl⟩ := Multiset.card_eq_two.mp hc'
  have hτ3 : ({p x, k, k'} : Multiset (Fin t)) ∈ F := hτ
  have hnd3 : ({p x, k, k'} : Multiset (Fin t)).Nodup := hnd
  rw [nodup_three_iff] at hnd3
  obtain ⟨hxk, hxk', hkk'⟩ := hnd3
  rw [show (p x ::ₘ {k, k'} : Multiset (Fin t)) = {p x, k, k'} from rfl, sum_typeDegVec_sp]
  have hxρ : x ≠ r k := ne_r_of_cls hr hxk
  have hxρ' : x ≠ r k' := ne_r_of_cls hr hxk'
  have hρρ' : r k ≠ r k' := fun e => hkk' (r_inj hr e)
  have hT := physCostZ_of_isCopy (isCopy_of_complete hG hxρ hxρ' hρρ'
    (by simp only [hr]; exact hτ3))
  refine ⟨-(ind1 s(r k, r k')),
    (OnReps.ind1 (Reps.ofTransversal_mem r hr _) (Reps.ofTransversal_mem r hr _)).neg, ?_⟩
  refine (hT.congr ?_).mono (by norm_num)
  unfold sp
  exact (star_identity_ne hxρ hxρ' hρρ').symm

/-! ### Step 3 (rainbow): the residual on a transversal is physical -/

omit [Fintype V] [DecidableEq V] in
theorem pairVec_r_apply {r : Fin t → V} (hr : ∀ i, p (r i) = i) (a b i j : Fin t) :
    pairVec p s(r a, r b) i j =
      (if a = i ∧ b = j then 1 else 0) + (if b = i ∧ a = j then 1 else 0) := by
  simp [pairVec, hr]

/-- On a transversal, an edge function is determined by its edge-count vector. -/
theorem edgeVecZ_apply_transversal {r : Fin t → V} (hr : ∀ i, p (r i) = i) {w : Sym2 V → ℤ}
    (hw : OnReps (Reps.ofTransversal r hr) w) (i j : Fin t) :
    edgeVecZ p w i j = w s(r i, r j) * ((if i = j then 1 else 0) + 1) := by
  unfold edgeVecZ
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single s(r i, r j)]
  · simp only [Pi.smul_apply, smul_eq_mul, pairVec_r_apply hr]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · intro e _ hne
    by_cases hwe : w e = 0
    · simp [hwe]
    · induction e using Sym2.ind with
      | _ x y =>
        obtain ⟨a, rfl⟩ := (Reps.ofTransversal_mem_iff r hr).mp
          (hw _ hwe x (Sym2.mem_mk_left x y))
        obtain ⟨b, rfl⟩ := (Reps.ofTransversal_mem_iff r hr).mp
          (hw _ hwe _ (Sym2.mem_mk_right _ _))
        simp only [Pi.smul_apply, smul_eq_mul, pairVec_r_apply hr]
        have h1 : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
        have h2 : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2, Sym2.eq_swap])
        simp [h1, h2]
  · intro h; exact absurd (mem_univ _) h

theorem eq_of_edgeVecZ_eq_transversal {r : Fin t → V} (hr : ∀ i, p (r i) = i)
    {w w' : Sym2 V → ℤ} (hw : OnReps (Reps.ofTransversal r hr) w)
    (hw' : OnReps (Reps.ofTransversal r hr) w') (h : edgeVecZ p w = edgeVecZ p w') : w = w' := by
  funext e
  by_cases h0 : w e = 0 ∧ w' e = 0
  · rw [h0.1, h0.2]
  · have hmem : ∀ x ∈ e, ∃ i, r i = x := by
      intro x hx
      rcases not_and_or.mp h0 with hne | hne
      · exact (Reps.ofTransversal_mem_iff r hr).mp (hw e hne x hx)
      · exact (Reps.ofTransversal_mem_iff r hr).mp (hw' e hne x hx)
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨a, rfl⟩ := hmem x (Sym2.mem_mk_left x y)
      obtain ⟨b, rfl⟩ := hmem _ (Sym2.mem_mk_right _ _)
      have e1 := edgeVecZ_apply_transversal hr hw a b
      have e2 := edgeVecZ_apply_transversal hr hw' a b
      rw [h] at e1
      rw [e1] at e2
      by_cases hab : a = b
      · subst hab; simp at e2; omega
      · simp [hab] at e2; exact e2

/-- The triangle of a rainbow type on the transversal. -/
def triOf (r : Fin t → V) (hr : ∀ i, p (r i) = i) (τ : Multiset (Fin t)) : Finset V :=
  τ.toFinset.map ⟨r, r_injective hr⟩

omit [Fintype V] [DecidableEq V] in
theorem triOf_val {r : Fin t → V} (hr : ∀ i, p (r i) = i) {τ : Multiset (Fin t)}
    (hnd : τ.Nodup) : (triOf r hr τ).val.map p = τ := by
  rw [triOf, map_val, Multiset.map_map, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  conv_rhs => rw [← Multiset.map_id' τ]
  refine Multiset.map_congr rfl fun i _ => ?_
  exact hr i

omit [Fintype V] [DecidableEq V] in
theorem triOf_card {r : Fin t → V} (hr : ∀ i, p (r i) = i) {τ : Multiset (Fin t)}
    (hc : Multiset.card τ = 3) (hnd : τ.Nodup) : (triOf r hr τ).card = 3 := by
  rw [triOf, card_map, Multiset.toFinset_card_of_nodup hnd, hc]

omit [Fintype V] [DecidableEq V] in
theorem isCopy_triOf {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) (hR : IsRainbow F) {r : Fin t → V} (hr : ∀ i, p (r i) = i)
    {τ : Multiset (Fin t)} (hτ : τ ∈ F) : IsCopy p F G (triOf r hr τ) := by
  obtain ⟨hc, hnd⟩ := hR τ hτ
  refine ⟨?_, by rw [triOf_val hr hnd]; exact hτ⟩
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, triOf_card hr hc hnd⟩
  intro x hx y hy hxy
  rw [mem_coe, triOf, mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  simp only [Function.Embedding.coeFn_mk, Multiset.mem_toFinset] at ha hb hxy ⊢
  have hab : a ≠ b := fun e => hxy (by rw [e])
  rw [hG]
  refine ⟨hxy, τ, hτ, hc, ?_⟩
  rw [hr, hr, Multiset.le_iff_subset (by simp [Multiset.nodup_cons, hab])]
  intro z hz
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact ha
  · exact hb

omit [Fintype V] in
theorem onReps_triOf {r : Fin t → V} (hr : ∀ i, p (r i) = i) (τ : Multiset (Fin t)) :
    OnReps (Reps.ofTransversal r hr) (indZ (triEdges (triOf r hr τ))) := by
  intro e he x hx
  rw [Reps.ofTransversal_mem_iff]
  have hmem : e ∈ triEdges (triOf r hr τ) := by
    by_contra h; exact he (indZ_not_mem h)
  induction e using Sym2.ind with
  | _ y z =>
    obtain ⟨hy, hz, _⟩ := Reps.mem_triEdges_mk.mp hmem
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · obtain ⟨a, _, ha⟩ := mem_map.mp hy; exact ⟨a, ha⟩
    · obtain ⟨b, _, hb⟩ := mem_map.mp hz; exact ⟨b, hb⟩

omit [DecidableEq V] in
theorem edgeVecZ_sum (p : V → Fin t) {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ) :
    edgeVecZ p (∑ i ∈ s, f i) = ∑ i ∈ s, edgeVecZ p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [edgeVecZ_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, edgeVecZ_add, ih]

/-- **Step 3 (rainbow).** An edge function on a transversal whose edge-count vector lies in the
lattice of the types is a combination of the type triangles on the transversal. -/
theorem physDivZ_of_transversal {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) (hR : IsRainbow F) {r : Fin t → V} (hr : ∀ i, p (r i) = i)
    {w : Sym2 V → ℤ} (hw : OnReps (Reps.ofTransversal r hr) w)
    (hagg : ∃ c : Multiset (Fin t) → ℤ, edgeVecZ p w = ∑ τ ∈ F, c τ • typeEdgeVec τ) :
    PhysDivZ p F G w := by
  obtain ⟨c, hc⟩ := hagg
  have hw' : w = ∑ τ ∈ F, c τ • indZ (triEdges (triOf r hr τ)) := by
    refine eq_of_edgeVecZ_eq_transversal hr hw
      (OnReps.sum _ _ fun τ _ => (onReps_triOf hr τ).smul _) ?_
    rw [hc, edgeVecZ_sum]
    refine sum_congr rfl fun τ hτ => ?_
    obtain ⟨hc3, hnd⟩ := hR τ hτ
    rw [edgeVecZ_smul, edgeVecZ_indZ, edgeVec_triEdges p (triOf_card hr hc3 hnd), triType,
      triOf_val hr hnd]
  refine ⟨{τ // τ ∈ F}, inferInstance, fun τ => triOf r hr τ.1, fun τ => c τ.1,
    fun τ => isCopy_triOf hG hR hr τ.2, fun e => ?_⟩
  rw [hw', Finset.sum_apply, ← Finset.sum_coe_sort F]
  exact sum_congr rfl fun τ _ => by rw [Pi.smul_apply, smul_eq_mul]

/-! ### The rainbow theorem -/

/-- **Rainbow reduction theorem (unconditional).** Let `F` be a rainbow family (three distinct
classes in every type), `G` the complete `F`-blowup of `p`, with every class non-empty
(a transversal `r`). Then every integrally `F`-divisible edge set of `G` lies in the physical
lattice generated by the `F`-copies of `G`. -/
theorem physDiv_of_isIntDiv_rainbow {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : IsCompleteBlowup p F G) (hR : IsRainbow F) (r : Fin t → V)
    (hr : ∀ i, p (r i) = i) {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset)
    (hdiv : IsIntDiv p F E) : PhysDiv p F G E := by
  have hedge : ∀ e ∈ E, ∃ w : Sym2 V → ℤ, OnReps (Reps.ofTransversal r hr) w ∧
      PhysCostZ p F G (ind1 e - (spkOf p (sp r) e + w)) 4 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v => exact edge_step_rb hG hR r hr (SimpleGraph.mem_edgeFinset.mp (hE he))
  obtain ⟨w₁, hw₁, hc₁⟩ := step1_of hedge
  obtain ⟨w₂, K₂, hw₂, hc₂⟩ := step2_of (S := sp r)
    (fun x τ hτ hi => star_type_rb hG hR r hr x hτ hi) hdiv
  have hc := hc₁.add hc₂
  have heq : indZ E - (∑ x, ∑ k, degVec p E x k • sp r x k + w₁) +
      (∑ x, ∑ l, degVec p E x l • sp r x l - w₂) = indZ E - (w₁ + w₂) := by abel
  have hc' := hc.congr heq
  have hw₃ : OnReps (Reps.ofTransversal r hr) (w₁ + w₂) := hw₁.add hw₂
  have hagg : AggDivZ p F (w₁ + w₂) := by
    have h0 : AggDivZ p F (indZ E) := (aggDivZ_indZ_iff p F E).mpr hdiv
    have h1 : AggDivZ p F (indZ E - (w₁ + w₂)) := aggDivZ_of_physCostZ hc'
    have := h0.sub h1
    convert this using 1
    abel
  have hres : PhysDivZ p F G (w₁ + w₂) := physDivZ_of_transversal hG hR hr hw₃ hagg.1
  rw [physDiv_iff_physDivZ]
  have := (physDivZ_of_physCostZ hc').add hres
  exact this.congr (by abel)

end PartitionedTriangleAbsorption.BlowupB
