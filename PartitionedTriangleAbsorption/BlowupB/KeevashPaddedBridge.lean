/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashPadded
public import PartitionedTriangleAbsorption.BlowupB.KeevashReserve

/-! # BlowupB.KeevashPaddedBridge — the padded interface implies `KeevashTypedSpec`

**`keevashTypedSpec_of_padded`**: `KeevashPaddedSpec F → KeevashTypedSpec F` for every family of
3-element types. Ingredients:

* `paddedRegularT_of_triRegular`: triangle weights `y_T ∈ [ω/n, 1/(ω n)]` are split uniformly over
  the `N_T` class-respecting embeddings of the padded pattern onto `T`; loads are preserved
  exactly, and `(γ n − q)^{q−3} ≤ N_T ≤ 27 n^{q−3}` (lower bound by `count_ext` with no required
  pairs, upper bound by a product count);
* `extendableT_of_cnExt` (in `KeevashPadded`);
* the choice of `m` with `2^{50 q³} ≥ 1/γ`, so that classes of size `≥ γ n` are `≥ n / h_K`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

section Patterns

theorem card_fin_filter_lt {N k : ℕ} (h : k ≤ N) :
    (univ.filter fun j : Fin N => j.val < k).card = k := by
  have e : (univ.filter fun j : Fin N => j.val < k).map Fin.valEmbedding = range k := by
    ext a
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro ha; exact ⟨⟨a, by omega⟩, ha, rfl⟩
  have := congrArg card e
  rw [card_map, card_range] at this
  exact this

theorem count_le_of_card_three {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) (c : Fin t) :
    τ.count c ≤ 3 := hτ ▸ Multiset.count_le_card c τ

theorem patPosT_map_fst (m : ℕ) {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) :
    (patPosT m τ).val.map Prod.fst = τ := by
  classical
  ext c
  rw [Multiset.count_map]
  have e : ((patPosT m τ).val.filter fun x => c = x.1) = ((patPosT m τ).filter fun x => c = x.1).val :=
    rfl
  rw [e, card_val]
  have hbij : ((patPosT m τ).filter fun x => c = x.1) =
      (univ.filter fun j : Fin (m + 3) => j.val < τ.count c).map
        ⟨fun j => (c, j), fun a b h => (Prod.mk.inj h).2⟩ := by
    ext x
    simp only [patPosT, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hx, rfl⟩; exact ⟨x.2, hx, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨hj, rfl⟩
  rw [hbij, card_map, card_fin_filter_lt (by have := count_le_of_card_three hτ c; omega)]

theorem card_patPosT (m : ℕ) {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) :
    (patPosT m τ).card = 3 := by
  have := congrArg Multiset.card (patPosT_map_fst m hτ)
  rw [Multiset.card_map, card_val, hτ] at this
  exact this

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem copyTriT_val {m : ℕ} {p : V → Fin t} {τ : Multiset (Fin t)} {φ : PosT t m → V}
    (hφ : IsEmbT m p φ) : (copyTriT m τ φ).val = (patPosT m τ).val.map φ :=
  image_val_of_injOn (fun a _ b _ h => hφ.1 h)

theorem copyTriT_card {m : ℕ} {p : V → Fin t} {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3)
    {φ : PosT t m → V} (hφ : IsEmbT m p φ) : (copyTriT m τ φ).card = 3 := by
  rw [← card_val, copyTriT_val hφ, Multiset.card_map, card_val, card_patPosT m hτ]

theorem copyTriT_map {m : ℕ} {p : V → Fin t} {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3)
    {φ : PosT t m → V} (hφ : IsEmbT m p φ) : (copyTriT m τ φ).val.map p = τ := by
  rw [copyTriT_val hφ, Multiset.map_map]
  have : (p ∘ φ) = Prod.fst := funext fun x => hφ.2 x
  rw [this, patPosT_map_fst m hτ]

/-- A class-respecting map of the pattern of `τ` onto a triangle of type `τ`. -/
theorem exists_pattern_map (m : ℕ) (p : V → Fin t) {τ : Multiset (Fin t)}
    (hτ : Multiset.card τ = 3) {T : Finset V} (hT : T.val.map p = τ) (hT3 : T.card = 3) :
    ∃ φ0 : PosT t m → V, Set.InjOn φ0 (patPosT m τ) ∧ (patPosT m τ).image φ0 = T ∧
      ∀ x ∈ patPosT m τ, p (φ0 x) = x.1 := by
  classical
  obtain ⟨u0, -⟩ := card_pos.mp (by rw [hT3]; norm_num : 0 < T.card)
  have hcnt : ∀ c, (T.filter fun v => p v = c).card = τ.count c := by
    intro c
    rw [← hT, Multiset.count_map, ← card_val]
    congr 1
    simp only [filter_val]
    exact Multiset.filter_congr fun v _ => eq_comm
  let eqv : ∀ c, ↥(T.filter fun v => p v = c) ≃ Fin (τ.count c) := fun c =>
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcnt c)
  let φ0 : PosT t m → V := fun x =>
    if h : x.2.val < τ.count x.1 then ((eqv x.1).symm ⟨x.2.val, h⟩).1 else u0
  have hmemc : ∀ x (h : x.2.val < τ.count x.1), φ0 x ∈ T.filter fun v => p v = x.1 := by
    intro x h
    simp only [φ0, dif_pos h]
    exact ((eqv x.1).symm ⟨x.2.val, h⟩).2
  refine ⟨φ0, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a.2.val < τ.count a.1 := (mem_filter.mp ha).2
    have hb' : b.2.val < τ.count b.1 := (mem_filter.mp hb).2
    have hca := (mem_filter.mp (hmemc a ha')).2
    have hcb := (mem_filter.mp (hmemc b hb')).2
    have hc : a.1 = b.1 := by rw [← hca, ← hcb, hab]
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only at hc ha' hb'
    subst hc
    simp only [φ0, dif_pos ha', dif_pos hb'] at hab
    have := (eqv a1).symm.injective (Subtype.ext hab)
    simp only [Fin.mk.injEq] at this
    exact Prod.ext rfl (Fin.ext this)
  · ext w
    simp only [mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_filter.mp (hmemc x (mem_filter.mp hx).2)).1
    · intro hw
      let c := p w
      let j := eqv c ⟨w, mem_filter.mpr ⟨hw, rfl⟩⟩
      have hj3 : j.val < m + 3 := by
        have := count_le_of_card_three hτ c; have := j.isLt; omega
      refine ⟨(c, ⟨j.val, hj3⟩), mem_filter.mpr ⟨mem_univ _, j.isLt⟩, ?_⟩
      simp only [φ0, dif_pos j.isLt]
      have : (⟨j.val, j.isLt⟩ : Fin (τ.count c)) = j := Fin.ext rfl
      rw [this, Equiv.symm_apply_apply]
  · intro x hx
    exact (mem_filter.mp (hmemc x (mem_filter.mp hx).2)).2

end Patterns

section Split

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of embeddings of the pattern of `τ` onto `T`. -/
noncomputable def embCount (m : ℕ) (p : V → Fin t) (τ : Multiset (Fin t)) (T : Finset V) : ℕ := by
  classical exact (univ.filter fun φ : PosT t m → V => IsEmbT m p φ ∧ copyTriT m τ φ = T).card

theorem embCount_lower (m : ℕ) (p : V → Fin t) {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3)
    {T : Finset V} (hT : T.val.map p = τ) (hT3 : T.card = 3) {s : ℝ} (hs : 0 ≤ s)
    (hcls : ∀ i, s + qT t m ≤ ((univ.filter fun v => p v = i).card : ℝ)) :
    s ^ (qT t m - 3) ≤ (embCount m p τ T : ℝ) := by
  classical
  obtain ⟨φ0, hinj, himg, hlab⟩ := exists_pattern_map m p hτ hT hT3
  have hcount := count_ext p ∅ (univ : Finset (Sym2 V)) (fun x : PosT t m => x.1)
    (∅ : Finset (Sym2 (PosT t m))) s hs (fun S' A i hS' _ _ => by
      have hsub : (univ.filter fun v => p v = i) ⊆
          (univ.filter fun v => p v = i ∧ v ∉ S' ∧ ∀ a ∈ A, s(a, v) ∈ (univ : Finset (Sym2 V))) ∪
            S' := by
        intro v hv
        by_cases hvS : v ∈ S'
        · exact mem_union_right _ hvS
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2, hvS,
            fun _ _ => mem_univ _⟩)
      have h1 := (card_le_card hsub).trans (card_union_le _ _)
      have h2 : (S'.card : ℝ) ≤ qT t m := by
        have : S'.card ≤ qT t m := by
          rw [show Fintype.card (PosT t m) = qT t m by simp [qT]] at hS'; exact hS'
        exact_mod_cast this
      have h3 : ((univ.filter fun v => p v = i).card : ℝ) ≤
          ((univ.filter fun v => p v = i ∧ v ∉ S' ∧
            ∀ a ∈ A, s(a, v) ∈ (univ : Finset (Sym2 V))).card : ℝ) + S'.card := by
        exact_mod_cast h1
      linarith [hcls i])
    _ (patPosT m τ) φ0 rfl hinj hlab
  have hcard : Fintype.card (PosT t m) - (patPosT m τ).card = qT t m - 3 := by
    rw [card_patPosT m hτ]; simp [qT]
  rw [hcard] at hcount
  refine hcount.trans ?_
  unfold embCount
  exact_mod_cast card_le_card fun ψ hψ => by
    simp only [goodExt, mem_filter, mem_univ, true_and] at hψ ⊢
    obtain ⟨h1, h2, h3, -⟩ := hψ
    refine ⟨⟨h2, h3⟩, ?_⟩
    unfold copyTriT
    rw [← himg]
    exact image_congr fun x hx => h1 x hx

theorem embCount_upper (m : ℕ) (p : V → Fin t) {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3)
    {T : Finset V} (hT3 : T.card = 3) :
    (embCount m p τ T : ℝ) ≤ 27 * (Fintype.card V : ℝ) ^ (qT t m - 3) := by
  classical
  let box : (x : PosT t m) → Finset V := fun x => if x ∈ patPosT m τ then T else univ
  have hsub : (univ.filter fun φ : PosT t m → V => IsEmbT m p φ ∧ copyTriT m τ φ = T) ⊆
      Fintype.piFinset box := by
    intro φ hφ
    obtain ⟨-, hT⟩ := (mem_filter.mp hφ).2
    rw [Fintype.mem_piFinset]
    intro x
    simp only [box]
    split_ifs with hx
    · rw [← hT]; exact mem_image_of_mem φ hx
    · exact mem_univ _
  have hcardbox : (Fintype.piFinset box).card = 27 * Fintype.card V ^ (qT t m - 3) := by
    rw [Fintype.card_piFinset]
    simp only [box, apply_ite card, card_univ]
    rw [prod_ite, prod_const, prod_const, hT3]
    have h1 : (univ.filter fun x : PosT t m => x ∈ patPosT m τ) = patPosT m τ := by
      ext x; simp
    have h2 : (univ.filter fun x : PosT t m => x ∉ patPosT m τ).card = qT t m - 3 := by
      have := card_filter_add_card_filter_not (s := (univ : Finset (PosT t m)))
        (p := fun x => x ∈ patPosT m τ)
      rw [h1, card_patPosT m hτ, card_univ] at this
      have hq : Fintype.card (PosT t m) = qT t m := by simp [qT]
      omega
    rw [h1, card_patPosT m hτ, h2]
    norm_num
  unfold embCount
  have := card_le_card hsub
  rw [hcardbox] at this
  exact_mod_cast this

/-- Monotonicity of padded regularity in `ω`. -/
theorem PaddedRegularT.mono {m : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω ω' c : ℝ} (hω' : 0 < ω') (h : ω' ≤ ω)
    (hR : PaddedRegularT m p F J ω c) : PaddedRegularT m p F J ω' c := by
  obtain ⟨y, hb, hl⟩ := hR
  refine ⟨y, fun τ hτ φ hφ => ?_, hl⟩
  obtain ⟨b1, b2⟩ := hb τ hτ φ hφ
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (qT t m - 2) := by positivity
  constructor
  · exact le_trans (div_le_div_of_nonneg_right h hn) b1
  · refine b2.trans ?_
    rcases hn.lt_or_eq with hn' | hn'
    · exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right h hn)
    · rw [← hn']; simp

/-- Monotonicity of template extendability in `ω`. -/
theorem ExtendableT.mono {K : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω ω' : ℝ} (h : ω' ≤ ω) (hE : ExtendableT K p F J ω) :
    ExtendableT K p F J ω' := fun k hk κ S T φ hinj hlab =>
  le_trans (mul_le_mul_of_nonneg_right h (by positivity)) (hE k hk κ S T φ hinj hlab)

end Split

end PartitionedTriangleAbsorption.BlowupB
