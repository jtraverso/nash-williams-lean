/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LinearAbsorber

/-! # BlowupB.PhasedAbsorber — absorbers from phased trails, for every family

A **phased trail system** for `P` (`PhasedTrail`) is a permutation `σ` of positions `I`, a trail
`x` with `srcE σ x = P` (injective edges), and a phase `κ : I → Fin 3` increasing by one along
`σ`, such that

* every three consecutive classes `p (x i), p (x (σ i)), p (x (σ (σ i)))` form a type of `F`;
* along each cycle of `σ`, all positions of phase `0` lie in one class (the centre class).

`phased_private_absorber`: in every `G` inside the `F`-blowup with `missDeg ≤ d` and classes of
size more than `|Z| + 6K + (4K + 2)(d + 1)`, a set `P ⊆ E(G)` with a phased trail system and
`|P| ≤ K` has an absorber `A ⊆ E(G)` on at most `4K` fresh vertices outside `Z ∪ V(P)`.

No hypothesis on `F` is used (repeated classes allowed, no linearity, no `ThreeStepLinks`).
The construction is the one of `LinearAbsorber` (odd transformer with walks of length `1`,
windmill target with one centre per cycle); the family enters only through the existence of
phased trail systems.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset Equiv

universe u

variable {t : ℕ}

/-- A phased trail system for `P` on the positions `I`. -/
structure PhasedTrail {V : Type*} [DecidableEq V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (P : Finset (Sym2 V)) (I : Type*) [Fintype I]
    [DecidableEq I] where
  σ : Perm I
  x : I → V
  κ : I → Fin 3
  hx : ∀ i, x i ≠ x (σ i)
  hinj : Function.Injective fun i => s(x i, x (σ i))
  hsrc : srcE σ x = P
  hκ : ∀ i, κ (σ i) = κ i + 1
  hcen : ∀ i j, σ.SameCycle i j → κ i = 0 → κ j = 0 → p (x i) = p (x j)
  htrip : ∀ i, ({p (x i), p (x (σ i)), p (x (σ (σ i)))} : Multiset (Fin t)) ∈ F

section Pairs

variable {F : Finset (Multiset (Fin t))} {a b c : Fin t}

theorem allowed01 (h : ({a, b, c} : Multiset (Fin t)) ∈ F) : AllowedPair F a b :=
  ⟨_, h, by simp, Multiset.cons_le_cons a (Multiset.singleton_le.mpr (by simp))⟩

theorem allowed02 (h : ({a, b, c} : Multiset (Fin t)) ∈ F) : AllowedPair F a c :=
  ⟨_, h, by simp, Multiset.cons_le_cons a (Multiset.singleton_le.mpr (by simp))⟩

theorem allowed12 (h : ({a, b, c} : Multiset (Fin t)) ∈ F) : AllowedPair F b c :=
  ⟨_, h, by simp, Multiset.le_cons_self _ _⟩

end Pairs

theorem sameCycle_block {I : Type*} [Fintype I] [DecidableEq I] {σ : Perm I} {κ : I → Fin 3}
    (i : I) : σ.SameCycle (block (κ := κ) (σ := σ) i) i := by
  rcases block_spec (κ := κ) (σ := σ) i with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩
  · rw [e]
  · have h := Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl σ (block (κ := κ) (σ := σ) i))
    rwa [e] at h
  · have h := Perm.sameCycle_apply_right.mpr (Perm.sameCycle_apply_right.mpr
      (Perm.SameCycle.refl σ (block (κ := κ) (σ := σ) i)))
    rwa [e] at h

section Assembly

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 V)} {I : Type*} [Fintype I] [DecidableEq I]
  (T : PhasedTrail p F P I)

/-- Slots: target vertices and path vertices. -/
abbrev PSlot : Type _ := Slot3 T.σ ⊕ I

/-- Classes of the slots. -/
noncomputable def pcls : PSlot T → Fin t
  | Sum.inl (Sum.inl o) => p (T.x (block (κ := T.κ) (σ := T.σ) (Quotient.out o)))
  | Sum.inl (Sum.inr (Sum.inl j)) => p (T.x (T.σ j))
  | Sum.inl (Sum.inr (Sum.inr j)) => p (T.x (T.σ (T.σ j)))
  | Sum.inr i => p (T.x (T.σ i))

/-- The slot of the target vertex at a position. -/
noncomputable def pySlot (i : I) : PSlot T := windY (Sum.inl : Slot3 T.σ → PSlot T) T.κ i

theorem pySlot_inl (i : I) : ∃ s, pySlot T i = Sum.inl s := by
  unfold pySlot windY; split_ifs <;> exact ⟨_, rfl⟩

theorem windY_eq_pySlot {W : Type*} (f : PSlot T → W) (i : I) :
    windY (f ∘ Sum.inl) T.κ i = f (pySlot T i) := by
  unfold pySlot windY; split_ifs <;> rfl

theorem pcls_pySlot (i : I) : pcls T (pySlot T i) = p (T.x i) := by
  unfold pySlot windY
  split_ifs with h0 h1
  · simp only [pcls]
    exact T.hcen _ _ ((sameCycle_block _).trans
      (Quotient.mk_out (s := Perm.SameCycle.setoid T.σ) i)) (kappa_block T.hκ _) h0
  · simp only [pcls, Equiv.apply_symm_apply]
  · simp only [pcls, Equiv.apply_symm_apply]

theorem pySlot_ne (i : I) : pySlot T i ≠ pySlot T (T.σ i) := by
  classical
  exact windY_ne T.hκ Sum.inl_injective i

theorem sigma_ne (i : I) : T.σ i ≠ i := fun h => T.hx i (by rw [h])

/-- Directed requirements between slots. -/
def pE0 (j j' : PSlot T) : Prop :=
  ∃ i : I, (j = Sum.inr i ∧ (j' = pySlot T i ∨ j' = pySlot T (T.σ.symm i) ∨
      j' = Sum.inr (T.σ i))) ∨ (j = pySlot T i ∧ j' = pySlot T (T.σ i))

/-- The symmetric, irreflexive need relation. -/
def pNeed (j j' : PSlot T) : Prop := (pE0 T j j' ∨ pE0 T j' j) ∧ j ≠ j'

theorem pE0_allowed {j j' : PSlot T} (h : pE0 T j j') : AllowedPair F (pcls T j) (pcls T j') := by
  obtain ⟨i, ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · rw [pcls_pySlot]; simp only [pcls]; exact (allowed01 (T.htrip i)).symm
  · rw [pcls_pySlot]; simp only [pcls]
    have h := allowed02 (T.htrip (T.σ.symm i))
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  · simp only [pcls]; exact allowed12 (T.htrip i)
  · rw [pcls_pySlot, pcls_pySlot]; exact allowed01 (T.htrip i)

theorem pNeed_allowed {j j' : PSlot T} (h : pNeed T j j') :
    AllowedPair F (pcls T j') (pcls T j) := by
  rcases h.1 with h | h
  · exact (pE0_allowed T h).symm
  · exact pE0_allowed T h

/-- Fixed roots of the path slots. -/
def pRoots : PSlot T → Finset V
  | Sum.inl _ => ∅
  | Sum.inr i => {T.x i, T.x (T.σ.symm i)}

theorem x_mem_vertsOf (i : I) : T.x i ∈ vertsOf P := by
  have h := mem_vertsOf_of (mem_image_of_mem (fun i => s(T.x i, T.x (T.σ i))) (mem_univ i))
    (Sym2.mem_mk_left (T.x i) (T.x (T.σ i)))
  have e : univ.image (fun i => s(T.x i, T.x (T.σ i))) = P := T.hsrc
  rwa [e] at h

include T in
theorem card_I_eq : Fintype.card I = P.card := by
  rw [← T.hsrc, srcE, card_image_of_injective _ T.hinj, card_univ]

end Assembly

/-- **Private absorber from a phased trail system**, for every family. -/
theorem phased_private_absorber {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 V)} {I : Type*} [Fintype I]
    [DecidableEq I] (T : PhasedTrail p F P I)
    {G : SimpleGraph V} [DecidableRel G.Adj] {d K : ℕ}
    (hmiss : ∀ v, missDeg p F G v ≤ d) (Z : Finset V) (hPG : P ⊆ G.edgeFinset)
    (hK : P.card ≤ K)
    (hcls : ∀ c, Z.card + 6 * K + (4 * K + 2) * (d + 1) <
      (univ.filter fun v => p v = c).card) :
    ∃ A ⊆ G.edgeFinset, Disjoint A P ∧ HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧
      ∃ U : Finset V, U.card ≤ 4 * K ∧ Disjoint U (Z ∪ vertsOf P) ∧
        (∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf P ∨ v ∈ U) ∧ ∀ e ∈ A, ∃ u ∈ e, u ∈ U := by
  classical
  have hIK : Fintype.card I ≤ K := (card_I_eq T).trans_le hK
  have hJ : Fintype.card (PSlot T) ≤ 4 * K := by
    have h1 : Fintype.card (Orb T.σ) ≤ Fintype.card I :=
      Fintype.card_le_of_surjective _ Quotient.mk_surjective
    simp only [PSlot, Slot3, Fintype.card_sum]
    omega
  set σ := T.σ with hσ
  set S : Finset V := Z ∪ vertsOf P with hS
  have hSc : S.card ≤ Z.card + 2 * K :=
    (card_union_le _ _).trans (add_le_add le_rfl ((card_vertsOf_le).trans (by omega)))
  obtain ⟨f, hfinj, hf⟩ := greedy_embed (p := p) (F := F) (G := G) (pNeed T)
    (fun j j' h => ⟨h.1.symm, h.2.symm⟩) (fun j h => h.2 rfl) (pcls T)
    (pRoots T) S (D := Fintype.card (PSlot T) + 2) hmiss
    (by
      intro j
      have h1 : (pRoots T j).card ≤ 2 := by
        rcases j with _ | i
        · simp [pRoots]
        · exact card_le_two
      have h2 : (univ.filter (pNeed T j)).card ≤ Fintype.card (PSlot T) := card_le_univ _
      omega)
    (by
      intro j v hv
      rcases j with _ | i
      · simp [pRoots] at hv
      · simp only [pRoots, mem_insert, mem_singleton] at hv
        simp only [pcls]
        rcases hv with rfl | rfl
        · exact allowed01 (T.htrip i)
        · have h := allowed02 (T.htrip (T.σ.symm i))
          simp only [Equiv.apply_symm_apply] at h
          exact h)
    (fun j j' h => pNeed_allowed T h)
    (by
      intro c
      have := hcls c
      have h3 : (Fintype.card (PSlot T) + 2) * (d + 1) ≤ (4 * K + 2) * (d + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  set κ := T.κ with hκdef
  have hκ : ∀ i, κ (σ i) = κ i + 1 := T.hκ
  set g : Slot3 σ → V := f ∘ Sum.inl with hgdef
  set y : I → V := windY g κ with hydef
  set a : I → ℕ → V := fun i _ => f (Sum.inr i) with hadef
  have hg : Function.Injective g := hfinj.comp Sum.inl_injective
  have hy : ∀ i, y i = f (pySlot T i) := windY_eq_pySlot T f
  have hcl : ∀ j, p (f j) = pcls T j := fun j => (hf j).1
  have hnS : ∀ j, f j ∉ S := fun j => (hf j).2.1
  have hroot : ∀ j, ∀ v ∈ pRoots T j, G.Adj v (f j) := fun j => (hf j).2.2.1
  have hneed : ∀ j j', pNeed T j j' → G.Adj (f j) (f j') := fun j j' => (hf j).2.2.2 j'
  have hxS : ∀ i : I, T.x i ∈ S := fun i => mem_union_right _ (x_mem_vertsOf T i)
  have hfy : ∀ i j, f (Sum.inr i) ≠ y j := by
    intro i j h
    rw [hy] at h
    obtain ⟨s, hs⟩ := pySlot_inl T j
    rw [hs] at h
    exact absurd (hfinj h) (by simp)
  have hdata : OddTransformerData σ T.x y 0 a := by
    refine ⟨T.hx, windY_ne hκ hg, T.hinj, windY_edge_injective hκ hg, ?_, ?_, ?_, ?_⟩
    · intro i j k l hk hl h
      exact ⟨Sum.inr_injective (hfinj h), by omega⟩
    · intro i k j _ h
      exact hnS _ (h ▸ hxS j)
    · intro i k j _; exact hfy i j
    · intro i j h
      rw [hy] at h
      exact hnS _ (h ▸ hxS i)
  have htypes : OddTypes p F σ T.x y 0 a := by
    refine ⟨fun i => by rw [hy, hcl, pcls_pySlot], fun i => ?_, fun i k hk => ?_⟩
    · show ({p (T.x i), p (T.x (σ i)), p (f (Sum.inr (σ i)))} : Multiset (Fin t)) ∈ F
      rw [hcl]; simp only [pcls]
      exact T.htrip i
    · obtain rfl : k = 0 := by omega
      rw [oddPath_le (by omega), show (0 + 1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
      show ({p (T.x i), p (f (Sum.inr i)), p (f (Sum.inr (σ i)))} : Multiset (Fin t)) ∈ F
      rw [hcl, hcl]; simp only [pcls]
      exact T.htrip i
  have hQ : HasDecomp p F (srcE σ y) := by
    refine windmill_hasDecomp_gen hκ hg fun j hj => ?_
    show ({p (f (Sum.inl (Sum.inl ⟦j⟧))), p (f (Sum.inl (Sum.inr (Sum.inl j)))),
      p (f (Sum.inl (Sum.inr (Sum.inr j))))} : Multiset (Fin t)) ∈ F
    rw [hcl, hcl, hcl]
    simp only [pcls]
    rw [T.hcen _ _ ((sameCycle_block _).trans
      (Quotient.mk_out (s := Perm.SameCycle.setoid T.σ) j)) (kappa_block T.hκ _) hj]
    exact T.htrip j
  have hPsrc : srcE σ T.x = P := T.hsrc
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
    · rw [hy]; obtain ⟨s, hs⟩ := pySlot_inl T i; rw [hs]; exact ⟨hnS _, s, rfl⟩
    · rw [hy]; obtain ⟨s, hs⟩ := pySlot_inl T (σ i); rw [hs]; exact ⟨hnS _, s, rfl⟩
  have hTE : ∀ e ∈ oddT σ T.x y 0 a, ∃ u ∈ e, u ∉ S ∧ ∃ i, u = f (Sum.inr i) := by
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
  have hdisj : Disjoint (oddT σ T.x y 0 a ∪ srcE σ T.x) (srcE σ y) := by
    rw [disjoint_left]
    intro e he he'
    rcases mem_union.mp he with he | he
    · obtain ⟨u, hu, _, i, rfl⟩ := hTE e he
      obtain ⟨_, s, hs⟩ := hyE e he' _ hu
      exact absurd (hfinj hs) (by simp)
    · rw [hPsrc] at he
      have hsub' : ∀ v ∈ e, v ∈ S := fun v hv => mem_union_right _ (mem_vertsOf_of he hv)
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := by
        induction e using Sym2.ind with | _ x _ => exact ⟨x, Sym2.mem_mk_left _ _⟩
      exact (hyE e he' v hv).1 (hsub' v hv)
  obtain ⟨hA, hAP⟩ := absorber_of_oddTransformer hdata htypes hQ hdisj
  have hrinr' : ∀ i j, (Sum.inr i : PSlot T) ≠ pySlot T j := by
    intro i j h; obtain ⟨s, hs⟩ := pySlot_inl T j; rw [hs] at h; exact absurd h (by simp)
  refine ⟨oddT σ T.x y 0 a ∪ srcE σ y, ?_, ?_, hA, ?_, ?_⟩
  · intro e he
    rw [SimpleGraph.mem_edgeFinset]
    rcases mem_union.mp he with he | he
    · simp only [oddT, spokesE, pathE, mem_union, mem_biUnion, mem_univ, true_and, mem_image,
        mem_range] at he
      rcases he with (⟨i, k, hk, rfl⟩ | ⟨i, k, hk, rfl⟩) | ⟨i, k, hk, rfl⟩
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · rw [oddPath_le (by omega)]
          exact hroot (Sum.inr i) (T.x i) (by simp [pRoots])
        · rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
          exact hroot (Sum.inr (σ i)) (T.x i) (by simp [pRoots, hσ])
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · rw [oddPath_le (by omega), hy]
          exact (hneed _ _ ⟨Or.inl ⟨i, Or.inl ⟨rfl, Or.inl rfl⟩⟩, hrinr' _ _⟩).symm
        · rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top, hy]
          refine (hneed _ _ ⟨Or.inl ⟨σ i, Or.inl ⟨rfl, Or.inr (Or.inl ?_)⟩⟩, hrinr' _ _⟩).symm
          rw [hσ, Equiv.symm_apply_apply]
      · obtain rfl : k = 0 := by omega
        rw [oddPath_le (by omega), show (0 + 1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
        refine hneed _ _ ⟨Or.inl ⟨i, Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩⟩, ?_⟩
        intro h
        exact sigma_ne T i (Sum.inr_injective h).symm
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      rw [hy, hy]
      exact hneed _ _ ⟨Or.inl ⟨i, Or.inr ⟨rfl, rfl⟩⟩, pySlot_ne T i⟩
  · have hD : Disjoint (oddT σ T.x y 0 a ∪ srcE σ y) (srcE σ T.x) := by
      rw [disjoint_left]
      intro e he he'
      have hall : ∀ v ∈ e, v ∈ S := by
        intro v hv
        rw [hPsrc] at he'
        exact mem_union_right _ (mem_vertsOf_of he' hv)
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
        · exact Or.inl (x_mem_vertsOf T i)
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

/-- **Terminal absorber from phased trail systems**: if every divisible `L ⊆ X` has a phased
trail system, one edge set absorbs all of them. -/
theorem phased_terminal_absorber {t : ℕ} {V : Type u} [Fintype V] [DecidableEq V] {p : V → Fin t}
    {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {d K : ℕ} (hmiss : ∀ v, missDeg p F G v ≤ d)
    (X : Finset (Sym2 V)) (Z : Finset V) (hXG : X ⊆ G.edgeFinset) (hK : X.card ≤ K)
    (hPD : ∀ L ⊆ X, IsIntDiv p F L →
      ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I), Nonempty (PhasedTrail p F L I))
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
      obtain ⟨I, _, _, ⟨T⟩⟩ := hPD L hLX' hLdiv
      obtain ⟨B, hBG, hBL, hBdec, hBLdec, UL, hULc, hULZ, hBv, hBu⟩ :=
        phased_private_absorber T hmiss (Z ∪ U ∪ vertsOf X) (subset_trans hLX' hXG)
          hLc (fun c => by have := hcls c; omega)
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
