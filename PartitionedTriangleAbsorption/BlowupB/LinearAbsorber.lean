/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LinearTrails

/-! # BlowupB.LinearAbsorber — absorbers for linear families, without `ThreeStepLinks`

`linear_private_absorber`: for a linear family `F` with an orientation, in every graph `G` inside
the `F`-blowup in which every vertex misses at most `d` allowed neighbours and every class has
more than `|Z| + 6K + (4K + 2)(d + 1)` vertices, every integrally `F`-divisible `P ⊆ E(G)` with
`|P| ≤ K` has an absorber `A ⊆ E(G)`, disjoint from `P`, with `A` and `A ∪ P` decomposable, on at
most `4K` fresh vertices outside `Z ∪ V(P)`, each edge of `A` meeting them.

The construction is that of the rainbow type, run along the cycle of the type of each trail
(`LinearTrails`), with the windmill decomposed type by type (`windmill_hasDecomp_gen`).
`linear_terminal_absorber` stacks the private absorbers of all divisible subsets of a bounded
`X`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset Equiv

/-! ### The windmill for an arbitrary family -/

section WindGen

variable {I : Type*} [Fintype I] [DecidableEq I] {σ : Perm I} {W : Type*} [DecidableEq W]
  {g : Slot3 σ → W} {κ : I → Fin 3} {t : ℕ}

theorem windmill_hasDecomp_gen (hκ : ∀ i, κ (σ i) = κ i + 1) (hg : Function.Injective g)
    {F : Finset (Multiset (Fin t))} {p : W → Fin t}
    (hτ : ∀ j, κ j = 0 → ({p (g (Sum.inl ⟦j⟧)), p (g (Sum.inr (Sum.inl j))),
      p (g (Sum.inr (Sum.inr j)))} : Multiset (Fin t)) ∈ F) :
    HasDecomp p F (srcE σ (windY g κ)) := by
  rw [srcE_windmill hκ hg]
  refine hasDecomp_biUnion _ _ (fun j hj => hasDecomp_tri ?_ ?_) ?_
  · exact Finset.card_eq_three.mpr ⟨_, _, _, fun h => by simpa using hg h,
      fun h => by simpa using hg h, fun h => by simpa using hg h, rfl⟩
  · unfold windTri
    rw [map_three p (fun h => by simpa using hg h) (fun h => by simpa using hg h)
      (fun h => by simpa using hg h)]
    exact hτ j (mem_filter.mp hj).2
  · intro j hj j' hj' hjj
    rw [windTri_edges hκ hg, windTri_edges hκ hg, disjoint_left]
    intro e he he'
    simp only [mem_insert, mem_singleton] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with h0 | h0 | h0 <;>
      rcases slot_pair_eq hκ hg h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h1 h2 <;>
      first
      | exact hjj h1
      | exact hjj h2

end WindGen

/-! ### Assembly -/

section

variable {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} (O : Orientation F) {P : Finset (Sym2 V)}
  (hL : IsLinearFam F) (hdiv : IsIntDiv p F P)

/-- Slots: target vertices and path vertices. -/
abbrev LSlot : Type _ := Slot3 (linPerm (O := O) hL hdiv) ⊕ ArcL (p := p) O P

/-- Classes of the slots. -/
noncomputable def lcls : LSlot O hL hdiv → Fin t
  | Sum.inl (Sum.inl o) => (O.ord (Quotient.out o).typ).1
  | Sum.inl (Sum.inr (Sum.inl j)) => (O.ord j.typ).2.1
  | Sum.inl (Sum.inr (Sum.inr j)) => (O.ord j.typ).2.2
  | Sum.inr i => p i.head

/-- The slot of the target vertex at a position. -/
noncomputable def lySlot (i : ArcL (p := p) O P) : LSlot O hL hdiv :=
  if i.phase = 0 then Sum.inl (Sum.inl (Quotient.mk _ i))
  else if i.phase = 1 then Sum.inl (Sum.inr (Sum.inl ((linPerm hL hdiv).symm i)))
  else Sum.inl (Sum.inr (Sum.inr ((linPerm hL hdiv).symm ((linPerm hL hdiv).symm i))))

theorem lySlot_inl (i : ArcL (p := p) O P) : ∃ s, lySlot O hL hdiv i = Sum.inl s := by
  unfold lySlot; split_ifs <;> exact ⟨_, rfl⟩

theorem windY_eq_lySlot (f : LSlot O hL hdiv → V) (i : ArcL (p := p) O P) :
    windY (f ∘ Sum.inl) ArcL.phase i = f (lySlot O hL hdiv i) := by
  unfold windY lySlot; split_ifs <;> rfl

theorem typ_linPerm_pow (n : ℕ) (i : ArcL (p := p) O P) :
    ((linPerm hL hdiv ^ n) i).typ = i.typ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, typ_linPerm hL hdiv _, ih]

theorem typ_of_sameCycle {i j : ArcL (p := p) O P} (h : Perm.SameCycle (linPerm hL hdiv) i j) :
    j.typ = i.typ := by
  obtain ⟨n, _, hn⟩ := h.exists_pow_eq'
  rw [← hn, typ_linPerm_pow]

theorem typ_out (i : ArcL (p := p) O P) :
    (Quotient.out (Quotient.mk (Perm.SameCycle.setoid (linPerm hL hdiv)) i)).typ = i.typ :=
  (typ_of_sameCycle O hL hdiv (Quotient.mk_out (s := Perm.SameCycle.setoid (linPerm hL hdiv)) i)).symm

theorem typ_symm (i : ArcL (p := p) O P) : ((linPerm hL hdiv).symm i).typ = i.typ := by
  have := typ_linPerm hL hdiv ((linPerm hL hdiv).symm i)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

theorem lcls_lySlot (i : ArcL (p := p) O P) : lcls O hL hdiv (lySlot O hL hdiv i) = p i.tail := by
  have hd := i.dist hL
  have hm := i.tail_mem hL
  unfold lySlot
  split_ifs with h0 h1
  · simp only [lcls]
    rw [typ_out]
    exact ((phase_eq_zero_iff hd hm).mp h0).symm
  · simp only [lcls]
    rw [typ_symm]
    exact ((phase_eq_one_iff hd hm).mp h1).symm
  · simp only [lcls]
    rw [typ_symm, typ_symm]
    have h2 : i.phase = 2 := by
      rcases fin3_cases3 i.phase with h | h | h
      · exact absurd h h0
      · exact absurd h h1
      · exact h
    exact ((phase_eq_two_iff hd hm).mp h2).symm

/-- Class of the tail of the preceding arc. -/
theorem tail_symm_cls (i : ArcL (p := p) O P) :
    p ((linPerm hL hdiv).symm i).tail = cycNext (O.ord i.typ) (cycNext (O.ord i.typ) (p i.tail)) := by
  have hd := i.dist hL
  set j := (linPerm hL hdiv).symm i with hj
  have hji : linPerm hL hdiv j = i := Equiv.apply_symm_apply _ _
  have htyp : j.typ = i.typ := typ_symm O hL hdiv i
  have hc := cls_linPerm hL hdiv j
  rw [hji, htyp] at hc
  have hm : p j.tail ∈ ({(O.ord i.typ).1, (O.ord i.typ).2.1, (O.ord i.typ).2.2} :
      Multiset (Fin t)) := by rw [← htyp]; exact j.tail_mem hL
  rw [hc, cycNext3 hd hm]

include hL in
theorem allowed_of_ord {τ : Multiset (Fin t)} (hτ : τ ∈ F) {a b : Fin t}
    (ha : a ∈ ({(O.ord τ).1, (O.ord τ).2.1, (O.ord τ).2.2} : Multiset (Fin t)))
    (hb : b ∈ ({(O.ord τ).1, (O.ord τ).2.1, (O.ord τ).2.2} : Multiset (Fin t))) (hab : a ≠ b) :
    AllowedPair F a b := by
  refine ⟨τ, hτ, hL.card3 τ hτ, ?_⟩
  rw [← O.spec τ hτ, Multiset.le_iff_subset (by simp [hab])]
  intro z hz
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact ha
  · exact hb

/-- Directed requirements between slots. -/
noncomputable def lE0 (j j' : LSlot O hL hdiv) : Prop :=
  ∃ i : ArcL (p := p) O P, (j = Sum.inr i ∧ (j' = lySlot O hL hdiv i ∨
      j' = lySlot O hL hdiv ((linPerm hL hdiv).symm i) ∨ j' = Sum.inr (linPerm hL hdiv i))) ∨
    (j = lySlot O hL hdiv i ∧ j' = lySlot O hL hdiv (linPerm hL hdiv i))

/-- The symmetric need relation. -/
noncomputable def lNeed (j j' : LSlot O hL hdiv) : Prop := lE0 O hL hdiv j j' ∨ lE0 O hL hdiv j' j

/-- Needed pairs have distinct classes of a common type. -/
theorem lE0_allowed {j j' : LSlot O hL hdiv} (h : lE0 O hL hdiv j j') :
    lcls O hL hdiv j ≠ lcls O hL hdiv j' ∧ AllowedPair F (lcls O hL hdiv j) (lcls O hL hdiv j') := by
  obtain ⟨i, ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  all_goals
    have hd := i.dist hL
    have hm := i.tail_mem hL
    have hτ := i.typ.2
  · have hne : p i.head ≠ p i.tail := by rw [i.head_cls]; exact cycNext_ne hd hm
    rw [lcls_lySlot]; simp only [lcls]
    exact ⟨hne, allowed_of_ord O hL hτ (by rw [i.head_cls]; exact cycNext_mem hd hm) hm hne⟩
  · rw [lcls_lySlot]; simp only [lcls]; rw [tail_symm_cls O hL hdiv, i.head_cls]
    have hne : cycNext (O.ord i.typ) (p i.tail) ≠
        cycNext (O.ord i.typ) (cycNext (O.ord i.typ) (p i.tail)) :=
      (cycNext_cycNext_ne' hd hm).symm
    exact ⟨hne, allowed_of_ord O hL hτ (cycNext_mem hd hm) (cycNext_mem hd (cycNext_mem hd hm)) hne⟩
  · simp only [lcls]
    rw [i.head_cls, (linPerm hL hdiv i).head_cls, typ_linPerm hL hdiv _, cls_linPerm hL hdiv _]
    have hne : cycNext (O.ord i.typ) (p i.tail) ≠
        cycNext (O.ord i.typ) (cycNext (O.ord i.typ) (p i.tail)) :=
      (cycNext_cycNext_ne' hd hm).symm
    exact ⟨hne, allowed_of_ord O hL hτ (cycNext_mem hd hm) (cycNext_mem hd (cycNext_mem hd hm)) hne⟩
  · rw [lcls_lySlot, lcls_lySlot, cls_linPerm hL hdiv _]
    have hne : p i.tail ≠ cycNext (O.ord i.typ) (p i.tail) := (cycNext_ne hd hm).symm
    exact ⟨hne, allowed_of_ord O hL hτ hm (cycNext_mem hd hm) hne⟩

theorem lNeed_allowed {j j' : LSlot O hL hdiv} (h : lNeed O hL hdiv j j') :
    lcls O hL hdiv j ≠ lcls O hL hdiv j' ∧ AllowedPair F (lcls O hL hdiv j') (lcls O hL hdiv j) := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := lE0_allowed O hL hdiv h
    exact ⟨h1, h2.symm⟩
  · obtain ⟨h1, h2⟩ := lE0_allowed O hL hdiv h
    exact ⟨Ne.symm h1, h2⟩

/-- Fixed roots of the path slots. -/
noncomputable def lRoots : LSlot O hL hdiv → Finset V
  | Sum.inl _ => ∅
  | Sum.inr i => {i.tail, ((linPerm hL hdiv).symm i).tail}

theorem tail_mem_vertsOfL (i : ArcL (p := p) O P) : i.tail ∈ vertsOf P :=
  mem_biUnion.mpr ⟨_, i.2.1, mem_filter.mpr ⟨mem_univ _, Sym2.mem_mk_left _ _⟩⟩

include hL hdiv in
theorem card_arcL_le : Fintype.card (ArcL (p := p) O P) ≤ P.card := by
  have hinj : Function.Injective fun i : ArcL (p := p) O P =>
      (⟨s(i.1.1, i.1.2.1), i.2.1⟩ : {e // e ∈ P}) := by
    intro i j h
    apply lin_edge_injective hL hdiv
    simp only [linPerm_edge]
    exact congrArg Subtype.val h
  have := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_coe] at this

end

/-- **Linear-family private absorber.** -/
theorem linear_private_absorber {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} (hL : IsLinearFam F) (O : Orientation F)
    {G : SimpleGraph V} [DecidableRel G.Adj] {d K : ℕ}
    (hsub : ∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) (hmiss : ∀ v, missDeg p F G v ≤ d)
    {P : Finset (Sym2 V)} (Z : Finset V) (hPG : P ⊆ G.edgeFinset) (hdiv : IsIntDiv p F P)
    (hK : P.card ≤ K)
    (hcls : ∀ c, Z.card + 6 * K + (4 * K + 2) * (d + 1) <
      (univ.filter fun v => p v = c).card) :
    ∃ A ⊆ G.edgeFinset, Disjoint A P ∧ HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧
      ∃ U : Finset V, U.card ≤ 4 * K ∧ Disjoint U (Z ∪ vertsOf P) ∧
        (∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf P ∨ v ∈ U) ∧ ∀ e ∈ A, ∃ u ∈ e, u ∈ U := by
  classical
  have hJ : Fintype.card (LSlot O hL hdiv) ≤ 4 * K := by
    have h1 : Fintype.card (Orb (linPerm (O := O) hL hdiv)) ≤ Fintype.card (ArcL (p := p) O P) :=
      Fintype.card_le_of_surjective _ Quotient.mk_surjective
    have h2 := card_arcL_le O hL hdiv
    simp only [LSlot, Slot3, Fintype.card_sum]
    omega
  set σ := linPerm (O := O) hL hdiv with hσ
  set S : Finset V := Z ∪ vertsOf P with hS
  have hSc : S.card ≤ Z.card + 2 * K :=
    (card_union_le _ _).trans (add_le_add le_rfl ((card_vertsOf_le).trans (by omega)))
  obtain ⟨f, hfinj, hf⟩ := greedy_embed (p := p) (F := F) (G := G) (lNeed O hL hdiv)
    (fun j j' h => h.symm) (fun j h => (lNeed_allowed O hL hdiv h).1 rfl) (lcls O hL hdiv)
    (lRoots O hL hdiv) S (D := Fintype.card (LSlot O hL hdiv) + 2) hmiss
    (by
      intro j
      have h1 : (lRoots O hL hdiv j).card ≤ 2 := by
        rcases j with _ | i
        · simp [lRoots]
        · exact card_le_two
      have h2 : (univ.filter (lNeed O hL hdiv j)).card ≤ Fintype.card (LSlot O hL hdiv) :=
        card_le_univ _
      omega)
    (by
      intro j v hv
      rcases j with _ | i
      · simp [lRoots] at hv
      · have hd := i.dist hL
        have hm := i.tail_mem hL
        simp only [lRoots, mem_insert, mem_singleton] at hv
        simp only [lcls]
        rw [i.head_cls]
        rcases hv with rfl | rfl
        · exact allowed_of_ord O hL i.typ.2 hm (cycNext_mem hd hm) (cycNext_ne hd hm).symm
        · rw [tail_symm_cls O hL hdiv]
          exact allowed_of_ord O hL i.typ.2 (cycNext_mem hd (cycNext_mem hd hm)) (cycNext_mem hd hm)
            (cycNext_cycNext_ne' hd hm)
    )
    (fun j j' h => (lNeed_allowed O hL hdiv h).2)
    (by
      intro c
      have := hcls c
      have h3 : (Fintype.card (LSlot O hL hdiv) + 2) * (d + 1) ≤ (4 * K + 2) * (d + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  set κ : ArcL (p := p) O P → Fin 3 := ArcL.phase with hκdef
  have hκ : ∀ i, κ (σ i) = κ i + 1 := phase_linPerm hL hdiv
  set g : Slot3 σ → V := f ∘ Sum.inl with hgdef
  set y : ArcL (p := p) O P → V := windY g κ with hydef
  set a : ArcL (p := p) O P → ℕ → V := fun i _ => f (Sum.inr i) with hadef
  have hg : Function.Injective g := hfinj.comp Sum.inl_injective
  have hy : ∀ i, y i = f (lySlot O hL hdiv i) := windY_eq_lySlot O hL hdiv f
  have hcl : ∀ j, p (f j) = lcls O hL hdiv j := fun j => (hf j).1
  have hnS : ∀ j, f j ∉ S := fun j => (hf j).2.1
  have hroot : ∀ j, ∀ v ∈ lRoots O hL hdiv j, G.Adj v (f j) := fun j => (hf j).2.2.1
  have hneed : ∀ j j', lNeed O hL hdiv j j' → G.Adj (f j) (f j') := fun j j' => (hf j).2.2.2 j'
  have hxS : ∀ i : ArcL (p := p) O P, i.tail ∈ S := fun i => mem_union_right _ (tail_mem_vertsOfL O i)
  have hfy : ∀ i j, f (Sum.inr i) ≠ y j := by
    intro i j h
    rw [hy] at h
    obtain ⟨s, hs⟩ := lySlot_inl O hL hdiv j
    rw [hs] at h
    exact absurd (hfinj h) (by simp)
  have htri : ∀ i : ArcL (p := p) O P,
      ({p i.tail, cycNext (O.ord i.typ) (p i.tail),
        cycNext (O.ord i.typ) (cycNext (O.ord i.typ) (p i.tail))} : Multiset (Fin t)) ∈ F := by
    intro i
    rw [tri_rot (i.dist hL) (i.tail_mem hL), O.spec _ i.typ.2]
    exact i.typ.2
  have hdata : OddTransformerData σ ArcL.tail y 0 a := by
    refine ⟨tail_ne_tail_linPerm hL hdiv, windY_ne hκ hg, lin_edge_injective hL hdiv,
      windY_edge_injective hκ hg, ?_, ?_, ?_, ?_⟩
    · intro i j k l hk hl h
      exact ⟨Sum.inr_injective (hfinj h), by omega⟩
    · intro i k j _ h
      exact hnS _ (h ▸ hxS j)
    · intro i k j _; exact hfy i j
    · intro i j h
      rw [hy] at h
      exact hnS _ (h ▸ hxS i)
  have htypes : OddTypes p F σ ArcL.tail y 0 a := by
    refine ⟨fun i => by rw [hy, hcl, lcls_lySlot], fun i => ?_, fun i k hk => ?_⟩
    · show ({p i.tail, p (σ i).tail, p (f (Sum.inr (σ i)))} : Multiset (Fin t)) ∈ F
      rw [hcl]; simp only [lcls]
      rw [(σ i).head_cls, typ_linPerm hL hdiv _, cls_linPerm hL hdiv _]
      exact htri i
    · obtain rfl : k = 0 := by omega
      rw [oddPath_le (by omega), show (0 + 1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
      show ({p i.tail, p (f (Sum.inr i)), p (f (Sum.inr (σ i)))} : Multiset (Fin t)) ∈ F
      rw [hcl, hcl]; simp only [lcls]
      rw [i.head_cls, (σ i).head_cls, typ_linPerm hL hdiv _, cls_linPerm hL hdiv _]
      exact htri i
  have hQ : HasDecomp p F (srcE σ y) := by
    refine windmill_hasDecomp_gen hκ hg fun j hj => ?_
    have hd := j.dist hL
    have hm := j.tail_mem hL
    show ({p (f (Sum.inl (Sum.inl ⟦j⟧))), p (f (Sum.inl (Sum.inr (Sum.inl j)))),
      p (f (Sum.inl (Sum.inr (Sum.inr j))))} : Multiset (Fin t)) ∈ F
    rw [hcl, hcl, hcl]
    simp only [lcls]
    rw [typ_out, O.spec _ j.typ.2]
    exact j.typ.2
  have hPsrc : srcE σ ArcL.tail = P := srcE_linPerm hL hdiv fun a b h =>
    hsub a b (SimpleGraph.mem_edgeFinset.mp (hPG h))
  have hpath : ∀ i k, k < 2 → oddPath σ 0 a i k = f (Sum.inr i) ∨
      oddPath σ 0 a i k = f (Sum.inr (σ i)) := by
    intro i k hk
    unfold oddPath
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hyE : ∀ e ∈ srcE σ y, ∀ v ∈ e, v ∉ S ∧ ∃ s, v = f (Sum.inl s) := by
    intro e he v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · rw [hy]; obtain ⟨s, hs⟩ := lySlot_inl O hL hdiv i; rw [hs]; exact ⟨hnS _, s, rfl⟩
    · rw [hy]; obtain ⟨s, hs⟩ := lySlot_inl O hL hdiv (σ i); rw [hs]; exact ⟨hnS _, s, rfl⟩
  have hTE : ∀ e ∈ oddT σ ArcL.tail y 0 a, ∃ u ∈ e, u ∉ S ∧ ∃ i, u = f (Sum.inr i) := by
    intro e he
    simp only [oddT, spokesE, pathE, mem_union, mem_biUnion, mem_univ, true_and, mem_image,
      mem_range] at he
    rcases he with (⟨i, k, hk, rfl⟩ | ⟨i, k, hk, rfl⟩) | ⟨i, k, hk, rfl⟩
    · rcases hpath i k (by omega) with h | h <;> rw [h] <;>
        exact ⟨_, Sym2.mem_mk_right _ _, hnS _, _, rfl⟩
    · rcases hpath i k (by omega) with h | h <;> rw [h] <;>
        exact ⟨_, Sym2.mem_mk_right _ _, hnS _, _, rfl⟩
    · rcases hpath i k (by omega) with h | h <;> rw [h] <;>
        exact ⟨_, Sym2.mem_mk_left _ _, hnS _, _, rfl⟩
  have hdisj : Disjoint (oddT σ ArcL.tail y 0 a ∪ srcE σ ArcL.tail) (srcE σ y) := by
    rw [disjoint_left]
    intro e he he'
    rcases mem_union.mp he with he | he
    · obtain ⟨u, hu, _, i, rfl⟩ := hTE e he
      obtain ⟨_, s, hs⟩ := hyE e he' _ hu
      exact absurd (hfinj hs) (by simp)
    · rw [hPsrc] at he
      have hsub' : ∀ v ∈ e, v ∈ S := by
        intro v hv
        exact mem_union_right _ (mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨mem_univ _, hv⟩⟩)
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := by
        induction e using Sym2.ind with | _ x _ => exact ⟨x, Sym2.mem_mk_left _ _⟩
      exact (hyE e he' v hv).1 (hsub' v hv)
  obtain ⟨hA, hAP⟩ := absorber_of_oddTransformer hdata htypes hQ hdisj
  refine ⟨oddT σ ArcL.tail y 0 a ∪ srcE σ y, ?_, ?_, hA, ?_, ?_⟩
  · intro e he
    rw [SimpleGraph.mem_edgeFinset]
    rcases mem_union.mp he with he | he
    · simp only [oddT, spokesE, pathE, mem_union, mem_biUnion, mem_univ, true_and, mem_image,
        mem_range] at he
      rcases he with (⟨i, k, hk, rfl⟩ | ⟨i, k, hk, rfl⟩) | ⟨i, k, hk, rfl⟩
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · rw [oddPath_le (by omega)]
          exact hroot (Sum.inr i) i.tail (by simp [lRoots])
        · rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
          exact hroot (Sum.inr (σ i)) i.tail (by simp [lRoots, hσ])
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · rw [oddPath_le (by omega), hy]
          exact (hneed _ _ (Or.inl ⟨i, Or.inl ⟨rfl, Or.inl rfl⟩⟩)).symm
        · rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top, hy]
          refine (hneed _ _ (Or.inl ⟨σ i, Or.inl ⟨rfl, Or.inr (Or.inl ?_)⟩⟩)).symm
          rw [hσ, Equiv.symm_apply_apply]
      · obtain rfl : k = 0 := by omega
        rw [oddPath_le (by omega), show (0 + 1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
        exact hneed _ _ (Or.inl ⟨i, Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩⟩)
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      rw [hy, hy]
      exact hneed _ _ (Or.inl ⟨i, Or.inr ⟨rfl, rfl⟩⟩)
  · have hD : Disjoint (oddT σ ArcL.tail y 0 a ∪ srcE σ y) (srcE σ ArcL.tail) := by
      rw [disjoint_left]
      intro e he he'
      have hall : ∀ v ∈ e, v ∈ S := by
        intro v hv
        rw [hPsrc] at he'
        exact mem_union_right _ (mem_biUnion.mpr ⟨e, he', mem_filter.mpr ⟨mem_univ _, hv⟩⟩)
      rcases mem_union.mp he with he | he
      · obtain ⟨u, hu, huS, _⟩ := hTE e he
        exact huS (hall u hu)
      · obtain ⟨v, hv⟩ : ∃ v, v ∈ e := by
          induction e using Sym2.ind with | _ x _ => exact ⟨x, Sym2.mem_mk_left _ _⟩
        exact (hyE e he v hv).1 (hall v hv)
    rw [hPsrc] at hD; exact hD
  · rw [hPsrc] at hAP; exact hAP
  · have hUm : ∀ j, f j ∈ univ.image f := fun j => mem_image_of_mem f (mem_univ j)
    refine ⟨univ.image f, ?_, ?_, ?_, ?_⟩
    · exact card_image_le.trans (by rw [card_univ]; exact hJ)
    · rw [disjoint_left]
      intro v hv hvS
      obtain ⟨j, _, rfl⟩ := mem_image.mp hv
      exact hnS j hvS
    · intro e he v hv
      rcases mem_union.mp he with he | he
      · simp only [oddT, spokesE, pathE, mem_union, mem_biUnion, mem_univ, true_and, mem_image,
          mem_range] at he
        rcases he with (⟨i, k, hk, rfl⟩ | ⟨i, k, hk, rfl⟩) | ⟨i, k, hk, rfl⟩ <;>
          rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact Or.inl (tail_mem_vertsOfL O i)
        · right; rcases hpath i k (by omega) with h | h <;> rw [h] <;> exact hUm _
        · right; rw [hy]; exact hUm _
        · right; rcases hpath i k (by omega) with h | h <;> rw [h] <;> exact hUm _
        · right; rcases hpath i k (by omega) with h | h <;> rw [h] <;> exact hUm _
        · right; rcases hpath i (k + 1) (by omega) with h | h <;> rw [h] <;> exact hUm _
      · obtain ⟨_, s', hs'⟩ := hyE e he v hv
        right; rw [hs']; exact hUm _
    · intro e he
      rcases mem_union.mp he with he | he
      · obtain ⟨u, hu, _, i, rfl⟩ := hTE e he
        exact ⟨_, hu, hUm _⟩
      · obtain ⟨v, hv⟩ : ∃ v, v ∈ e := by
          induction e using Sym2.ind with | _ x _ => exact ⟨x, Sym2.mem_mk_left _ _⟩
        obtain ⟨_, s', hs'⟩ := hyE e he v hv
        exact ⟨v, hv, by rw [hs']; exact hUm _⟩

/-- **Linear-family terminal absorber.** -/
theorem linear_terminal_absorber {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} (hL : IsLinearFam F) (O : Orientation F)
    {G : SimpleGraph V} [DecidableRel G.Adj] {d K : ℕ}
    (hsub : ∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) (hmiss : ∀ v, missDeg p F G v ≤ d)
    (X : Finset (Sym2 V)) (Z : Finset V) (hXG : X ⊆ G.edgeFinset) (hK : X.card ≤ K)
    (hcls : ∀ c, Z.card + 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) * (d + 1) <
      (univ.filter fun v => p v = c).card) :
    ∃ A ⊆ G.edgeFinset, Disjoint A X ∧ HasDecomp p F A ∧
      (∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)) ∧
      ∃ U : Finset V, U.card ≤ 4 * K * 2 ^ K ∧ Disjoint U (Z ∪ vertsOf X) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf X ∨ v ∈ U := by
  classical
  set D := X.powerset.filter (IsIntDiv p F) with hD
  have hDc : D.card ≤ 2 ^ K := (card_filter_le _ _).trans
    (by rw [card_powerset]; exact Nat.pow_le_pow_right (by norm_num) hK)
  have key : ∀ 𝓛 : Finset (Finset (Sym2 V)), 𝓛 ⊆ D → ∃ A ⊆ G.edgeFinset, Disjoint A X ∧
      HasDecomp p F A ∧ (∀ L ∈ 𝓛, HasDecomp p F (A ∪ L)) ∧
      ∃ U : Finset V, U.card ≤ 4 * K * 𝓛.card ∧ Disjoint U (Z ∪ vertsOf X) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf X ∨ v ∈ U := by
    intro 𝓛
    induction 𝓛 using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, empty_subset _, disjoint_empty_left _, hasDecomp_empty',
        fun L h => absurd h (notMem_empty _), ∅, by simp, disjoint_empty_left _,
        fun e he => absurd he (notMem_empty _)⟩
    | insert L 𝓛 hL' ih =>
      intro h𝓛
      obtain ⟨A, hAG, hAX, hAdec, hAall, U, hUc, hUZ, hAv⟩ :=
        ih (subset_trans (subset_insert _ _) h𝓛)
      obtain ⟨hLX, hLdiv⟩ := mem_filter.mp (h𝓛 (mem_insert_self L 𝓛))
      have hLX' : L ⊆ X := mem_powerset.mp hLX
      have hLc : L.card ≤ K := (card_le_card hLX').trans hK
      have h𝓛c : 𝓛.card ≤ 2 ^ K := by
        have := card_le_card h𝓛
        rw [card_insert_of_notMem hL'] at this
        omega
      have hVX : (vertsOf X).card ≤ 2 * K := card_vertsOf_le.trans (by omega)
      have hZ' : (Z ∪ U ∪ vertsOf X).card ≤ Z.card + 4 * K * 2 ^ K + 2 * K := by
        have h1 := card_union_le (Z ∪ U) (vertsOf X)
        have h2 := card_union_le Z U
        have h3 : 4 * K * 𝓛.card ≤ 4 * K * 2 ^ K := Nat.mul_le_mul_left _ h𝓛c
        omega
      obtain ⟨B, hBG, hBL, hBdec, hBLdec, UL, hULc, hULZ, hBv, hBu⟩ :=
        linear_private_absorber hL O hsub hmiss (Z ∪ U ∪ vertsOf X) (subset_trans hLX' hXG)
          hLdiv hLc (fun c => by have := hcls c; omega)
      have hUL_out : ∀ u ∈ UL, u ∉ U ∧ u ∉ vertsOf X := by
        intro u hu
        have := disjoint_left.mp hULZ hu
        simp only [mem_union, not_or] at this
        exact ⟨this.1.1.2, this.1.2⟩
      have hBA : Disjoint B A := by
        rw [disjoint_left]
        intro e heB heA
        obtain ⟨u, hu, huUL⟩ := hBu e heB
        obtain ⟨h1, h2⟩ := hUL_out u huUL
        rcases hAv e heA u hu with h | h
        · exact h2 h
        · exact h1 h
      have hBX : Disjoint B X := by
        rw [disjoint_left]
        intro e heB heX
        obtain ⟨u, hu, huUL⟩ := hBu e heB
        exact (hUL_out u huUL).2 (mem_vertsOf_of heX hu)
      refine ⟨A ∪ B, union_subset hAG hBG, disjoint_union_left.mpr ⟨hAX, hBX⟩,
        hasDecomp_union hAdec hBdec hBA.symm, ?_, U ∪ UL, ?_, ?_, ?_⟩
      · intro L'' hL''
        rcases mem_insert.mp hL'' with rfl | hL''
        · rw [union_assoc]
          refine hasDecomp_union hAdec hBLdec ?_
          exact disjoint_union_right.mpr ⟨hBA.symm, disjoint_of_subset_right hLX' hAX⟩
        · have hL''X : L'' ⊆ X :=
            mem_powerset.mp (mem_filter.mp (h𝓛 (mem_insert_of_mem hL''))).1
          have e : A ∪ B ∪ L'' = (A ∪ L'') ∪ B := by
            ext x; simp only [mem_union]; tauto
          rw [e]
          refine hasDecomp_union (hAall L'' hL'') hBdec ?_
          exact disjoint_union_left.mpr ⟨hBA.symm, (disjoint_of_subset_left hL''X hBX.symm)⟩
      · rw [card_insert_of_notMem hL']
        have := card_union_le U UL
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · rw [disjoint_union_left]
        refine ⟨hUZ, ?_⟩
        rw [disjoint_left]
        intro u hu hu'
        have := disjoint_left.mp hULZ hu
        simp only [mem_union, not_or] at this hu'
        rcases hu' with h | h
        · exact this.1.1.1 h
        · exact this.1.2 h
      · intro e he v hv
        rcases mem_union.mp he with he | he
        · rcases hAv e he v hv with h | h
          · exact Or.inl h
          · exact Or.inr (mem_union_left _ h)
        · rcases hBv e he v hv with h | h
          · exact Or.inl (vertsOf_mono hLX' h)
          · exact Or.inr (mem_union_right _ h)
  obtain ⟨A, hAG, hAX, hAdec, hAall, U, hUc, hUZ, hAv⟩ := key D (subset_refl _)
  refine ⟨A, hAG, hAX, hAdec, fun L hL hLdiv => hAall L ?_, U,
    hUc.trans (Nat.mul_le_mul_left _ hDc), hUZ, hAv⟩
  exact mem_filter.mpr ⟨mem_powerset.mpr hL, hLdiv⟩

end PartitionedTriangleAbsorption.BlowupB
