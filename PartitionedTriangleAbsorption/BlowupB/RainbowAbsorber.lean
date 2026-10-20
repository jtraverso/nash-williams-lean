/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.RainbowTarget
public import PartitionedTriangleAbsorption.BlowupB.GreedyEmbed

/-! # BlowupB.RainbowAbsorber — absorbers for the rainbow type, without `ThreeStepLinks`

`R3 = {{0,1,2}}` fails `ThreeStepLinks` (`not_threeStepLinks_rainbow`), so the tree's absorbers do
not apply. Here: in every graph `G` inside the rainbow blowup in which every vertex misses at most
`d` allowed neighbours, every integrally `R3`-divisible `P ⊆ E(G)` with `|P| ≤ K` has an absorber
`A` (`rainbow_private_absorber`): `A ⊆ E(G)`, `A ∩ P = ∅`, `A` and `A ∪ P` decompose, and every
vertex of `A` is a vertex of `P` or avoids a prescribed set `Z`, provided every class has more
than `|Z| + 6K + (4K + 2)(d + 1)` vertices.

Construction: the cyclic trails of `P` (`RainbowTrails`), the odd transformer with `m = 0`
(`OddTransformer`), the windmill target (`RainbowTarget`), and the greedy embedding of all fresh
vertices (`GreedyEmbed`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset Equiv

theorem fin3_succ_ne' : ∀ c : Fin 3, c + 1 ≠ c := by decide
theorem fin3_succ2_ne_succ : ∀ c : Fin 3, c + 2 ≠ c + 1 := by decide
theorem fin3_succ_succ_eq : ∀ c : Fin 3, c + 1 + 1 = c + 2 := by decide
theorem fin3_cases3 : ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide

section

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 3} {P : Finset (Sym2 V)}
  (hdiv : IsIntDiv p R3 P)

/-- Slots: target vertices and path vertices. -/
abbrev RSlot : Type _ := Slot3 (trailPerm hdiv) ⊕ Arc p P

/-- Classes of the slots. -/
def rcls : RSlot hdiv → Fin 3
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr (Sum.inl _)) => 1
  | Sum.inl (Sum.inr (Sum.inr _)) => 2
  | Sum.inr i => p i.tail + 1

/-- The slot of the target vertex at a position. -/
noncomputable def ySlot (i : Arc p P) : RSlot hdiv :=
  if p i.tail = 0 then Sum.inl (Sum.inl (Quotient.mk _ i))
  else if p i.tail = 1 then Sum.inl (Sum.inr (Sum.inl ((trailPerm hdiv).symm i)))
  else Sum.inl (Sum.inr (Sum.inr ((trailPerm hdiv).symm ((trailPerm hdiv).symm i))))

theorem ySlot_inl (i : Arc p P) : ∃ s, ySlot hdiv i = Sum.inl s := by
  unfold ySlot; split_ifs <;> exact ⟨_, rfl⟩

theorem rcls_ySlot (i : Arc p P) : rcls hdiv (ySlot hdiv i) = p i.tail := by
  unfold ySlot
  split_ifs with h1 h2
  · simp [rcls, h1]
  · simp [rcls, h2]
  · rcases fin3_cases3 (p i.tail) with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · simp [rcls, h]

theorem windY_eq_ySlot (f : RSlot hdiv → V) (i : Arc p P) :
    windY (f ∘ Sum.inl) (fun j => p j.tail) i = f (ySlot hdiv i) := by
  unfold windY ySlot; split_ifs <;> rfl

theorem kappa_trail (i : Arc p P) : p (trailPerm hdiv i).tail = p i.tail + 1 :=
  cls_trailPerm hdiv i

theorem kappa_trail_symm (i : Arc p P) : p ((trailPerm hdiv).symm i).tail = p i.tail + 2 :=
  kappa_symm (κ := fun j => p (Arc.tail j)) (kappa_trail hdiv) i

/-- Directed requirements between slots. -/
noncomputable def rE0 (j j' : RSlot hdiv) : Prop :=
  ∃ i : Arc p P, (j = Sum.inr i ∧ (j' = ySlot hdiv i ∨ j' = ySlot hdiv ((trailPerm hdiv).symm i) ∨
      j' = Sum.inr (trailPerm hdiv i))) ∨ (j = ySlot hdiv i ∧ j' = ySlot hdiv (trailPerm hdiv i))

/-- The symmetric need relation. -/
noncomputable def rNeed (j j' : RSlot hdiv) : Prop := rE0 hdiv j j' ∨ rE0 hdiv j' j

theorem rcls_ne_of_rE0 {j j' : RSlot hdiv} (h : rE0 hdiv j j') : rcls hdiv j ≠ rcls hdiv j' := by
  obtain ⟨i, ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · rw [rcls_ySlot]; exact fin3_succ_ne' _
  · rw [rcls_ySlot, kappa_trail_symm hdiv]; exact (fin3_succ2_ne_succ _).symm
  · simp only [rcls]; rw [kappa_trail hdiv, fin3_succ_succ_eq]; exact (fin3_succ2_ne_succ _).symm
  · rw [rcls_ySlot, rcls_ySlot, kappa_trail hdiv]; exact (fin3_succ_ne' _).symm

theorem rcls_ne_of_rNeed {j j' : RSlot hdiv} (h : rNeed hdiv j j') : rcls hdiv j ≠ rcls hdiv j' :=
  h.elim (rcls_ne_of_rE0 hdiv) fun h' => (rcls_ne_of_rE0 hdiv h').symm

/-- Fixed roots of the path slots: the two trail vertices around the position. -/
noncomputable def rRoots : RSlot hdiv → Finset V
  | Sum.inl _ => ∅
  | Sum.inr i => {i.tail, ((trailPerm hdiv).symm i).tail}

/-- The vertices of `P`. -/
def vertsOf (P : Finset (Sym2 V)) : Finset V := P.biUnion fun e => univ.filter fun v => v ∈ e

theorem tail_mem_vertsOf (i : Arc p P) : i.tail ∈ vertsOf P :=
  mem_biUnion.mpr ⟨_, i.2.1, mem_filter.mpr ⟨mem_univ _, Sym2.mem_mk_left _ _⟩⟩

theorem card_vertsOf_le : (vertsOf P).card ≤ 2 * P.card := by
  refine card_biUnion_le.trans ?_
  calc ∑ e ∈ P, (univ.filter fun v => v ∈ e).card ≤ ∑ _e ∈ P, 2 :=
        sum_le_sum fun e _ => card_filter_mem_sym2_le e
    _ = 2 * P.card := by rw [sum_const, smul_eq_mul, mul_comm]

include hdiv in
theorem card_arc_le : Fintype.card (Arc p P) ≤ P.card := by
  have hinj : Function.Injective fun i : Arc p P => (⟨s(i.1.1, i.1.2), i.2.1⟩ : {e // e ∈ P}) := by
    intro i j h
    have := trail_edge_injective hdiv (a₁ := i) (a₂ := j)
    apply this
    simp only [trailPerm_edge]
    exact congrArg Subtype.val h
  have := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_coe] at this

end

/-- **Rainbow absorber** in nearly complete rainbow blowups. -/
theorem rainbow_private_absorber {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 3}
    {G : SimpleGraph V} [DecidableRel G.Adj] {d K : ℕ}
    (hsub : ∀ u v, G.Adj u v → p u ≠ p v) (hmiss : ∀ v, missDeg p R3 G v ≤ d)
    {P : Finset (Sym2 V)} (Z : Finset V) (hPG : P ⊆ G.edgeFinset) (hdiv : IsIntDiv p R3 P)
    (hK : P.card ≤ K)
    (hcls : ∀ c, Z.card + 6 * K + (4 * K + 2) * (d + 1) <
      (univ.filter fun v => p v = c).card) :
    ∃ A ⊆ G.edgeFinset, Disjoint A P ∧ HasDecomp p R3 A ∧ HasDecomp p R3 (A ∪ P) ∧
      ∃ U : Finset V, U.card ≤ 4 * K ∧ Disjoint U (Z ∪ vertsOf P) ∧
        (∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf P ∨ v ∈ U) ∧ ∀ e ∈ A, ∃ u ∈ e, u ∈ U := by
  classical
  have hJ : Fintype.card (RSlot hdiv) ≤ 4 * K := by
    have h1 : Fintype.card (Orb (trailPerm hdiv)) ≤ Fintype.card (Arc p P) :=
      Fintype.card_le_of_surjective _ Quotient.mk_surjective
    have h2 := card_arc_le hdiv
    simp only [RSlot, Slot3, Fintype.card_sum]
    omega
  set σ := trailPerm hdiv with hσ
  set κ : Arc p P → Fin 3 := fun j => p j.tail with hκdef
  have hκ : ∀ i, κ (σ i) = κ i + 1 := cls_trailPerm hdiv
  set S : Finset V := Z ∪ vertsOf P with hS
  have hSc : S.card ≤ Z.card + 2 * K :=
    (card_union_le _ _).trans (add_le_add le_rfl ((card_vertsOf_le).trans (by omega)))
  -- greedy embedding of all fresh vertices
  obtain ⟨f, hfinj, hf⟩ := greedy_embed (p := p) (F := R3) (G := G) (rNeed hdiv)
    (fun j j' h => h.symm) (fun j h => rcls_ne_of_rNeed hdiv h rfl) (rcls hdiv) (rRoots hdiv) S
    (D := Fintype.card (RSlot hdiv) + 2) hmiss
    (by
      intro j
      have h1 : (rRoots hdiv j).card ≤ 2 := by
        rcases j with _ | i
        · simp [rRoots]
        · exact card_le_two
      have h2 : (univ.filter (rNeed hdiv j)).card ≤ Fintype.card (RSlot hdiv) := card_le_univ _
      omega)
    (by
      intro j v hv
      rcases j with _ | i
      · simp [rRoots] at hv
      · rw [allowedPair_R3_iff]
        simp only [rRoots, mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact (fin3_succ_ne' _).symm
        · simp only [rcls]; rw [kappa_trail_symm hdiv]; exact (fin3_succ2_ne_succ _)
    )
    (fun j j' h => (allowedPair_R3_iff _ _).mpr (rcls_ne_of_rNeed hdiv h).symm)
    (by
      intro c
      have := hcls c
      have h3 : (Fintype.card (RSlot hdiv) + 2) * (d + 1) ≤ (4 * K + 2) * (d + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  -- the data
  set g : Slot3 σ → V := f ∘ Sum.inl with hgdef
  set y : Arc p P → V := windY g κ with hydef
  set a : Arc p P → ℕ → V := fun i _ => f (Sum.inr i) with hadef
  have hg : Function.Injective g := hfinj.comp Sum.inl_injective
  have hy : ∀ i, y i = f (ySlot hdiv i) := windY_eq_ySlot hdiv f
  have hcl : ∀ j, p (f j) = rcls hdiv j := fun j => (hf j).1
  have hnS : ∀ j, f j ∉ S := fun j => (hf j).2.1
  have hroot : ∀ j, ∀ v ∈ rRoots hdiv j, G.Adj v (f j) := fun j => (hf j).2.2.1
  have hneed : ∀ j j', rNeed hdiv j j' → G.Adj (f j) (f j') := fun j j' => (hf j).2.2.2 j'
  have hxS : ∀ i : Arc p P, i.tail ∈ S := fun i => mem_union_right _ (tail_mem_vertsOf i)
  have hgcls : ∀ s, p (g s) = slotCls s := by
    intro s; rcases s with _ | _ | _ <;> simp [hgdef, hcl, rcls, slotCls]
  have hfy : ∀ i j, f (Sum.inr i) ≠ y j := by
    intro i j h
    rw [hy] at h
    obtain ⟨s, hs⟩ := ySlot_inl hdiv j
    rw [hs] at h
    exact absurd (hfinj h) (by simp)
  have hdata : OddTransformerData σ Arc.tail y 0 a := by
    refine ⟨tail_ne_tail_trailPerm hdiv, windY_ne hκ hg, trail_edge_injective hdiv,
      windY_edge_injective hκ hg, ?_, ?_, ?_, ?_⟩
    · intro i j k l hk hl h
      exact ⟨Sum.inr_injective (hfinj h), by omega⟩
    · intro i k j _ h
      exact hnS _ (h ▸ hxS j)
    · intro i k j _; exact hfy i j
    · intro i j h
      rw [hy] at h
      exact hnS _ (h ▸ hxS i)
  have htypes : OddTypes p R3 σ Arc.tail y 0 a := by
    refine ⟨fun i => by rw [hy, hcl, rcls_ySlot], fun i => ?_, fun i k hk => ?_⟩
    · show ({p i.tail, p (σ i).tail, p (f (Sum.inr (σ i)))} : Multiset (Fin 3)) ∈ R3
      rw [hcl]; simp only [rcls]
      rw [kappa_trail hdiv, fin3_succ_succ_eq]
      exact three_cycle_mem_R3 _
    · obtain rfl : k = 0 := by omega
      rw [oddPath_le (by omega), show (0 + 1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
      show ({p i.tail, p (f (Sum.inr i)), p (f (Sum.inr (σ i)))} : Multiset (Fin 3)) ∈ R3
      rw [hcl, hcl]; simp only [rcls]
      rw [kappa_trail hdiv, fin3_succ_succ_eq]
      exact three_cycle_mem_R3 _
  have hQ : HasDecomp p R3 (srcE σ y) := windmill_hasDecomp hκ hg hgcls
  have hPsrc : srcE σ Arc.tail = P := srcE_trailPerm hdiv fun a b h =>
    hsub a b (SimpleGraph.mem_edgeFinset.mp (hPG h))
  -- endpoints
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
    · rw [hy]; obtain ⟨s, hs⟩ := ySlot_inl hdiv i; rw [hs]; exact ⟨hnS _, s, rfl⟩
    · rw [hy]; obtain ⟨s, hs⟩ := ySlot_inl hdiv (σ i); rw [hs]; exact ⟨hnS _, s, rfl⟩
  have hTE : ∀ e ∈ oddT σ Arc.tail y 0 a, ∃ u ∈ e, u ∉ S ∧ ∃ i, u = f (Sum.inr i) := by
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
  have hdisj : Disjoint (oddT σ Arc.tail y 0 a ∪ srcE σ Arc.tail) (srcE σ y) := by
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
  refine ⟨oddT σ Arc.tail y 0 a ∪ srcE σ y, ?_, ?_, hA, ?_, ?_⟩
  · -- inside the host
    intro e he
    rw [SimpleGraph.mem_edgeFinset]
    rcases mem_union.mp he with he | he
    · simp only [oddT, spokesE, pathE, mem_union, mem_biUnion, mem_univ, true_and, mem_image,
        mem_range] at he
      rcases he with (⟨i, k, hk, rfl⟩ | ⟨i, k, hk, rfl⟩) | ⟨i, k, hk, rfl⟩
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · rw [oddPath_le (by omega)]
          exact hroot (Sum.inr i) i.tail (by simp [rRoots])
        · rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, oddPath_top]
          exact hroot (Sum.inr (σ i)) i.tail (by simp [rRoots, hσ])
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
  · -- disjoint from P
    have hD : Disjoint (oddT σ Arc.tail y 0 a ∪ srcE σ y) (srcE σ Arc.tail) := by
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
  · -- fresh vertices
    have hUm : ∀ j, f j ∈ univ.image f := fun j => mem_image_of_mem f (mem_univ j)
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
        · exact Or.inl (tail_mem_vertsOf i)
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

end PartitionedTriangleAbsorption.BlowupB
