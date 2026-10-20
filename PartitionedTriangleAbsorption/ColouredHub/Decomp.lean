/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Classes

/-! # Coloured hubs V: the two exact typed decompositions

* empty mode: `A = (P₁ ∪ P₂) ∪ (T_P ∪ J) ∪ (T_Q ∪ Q₂) ∪ (Q₁ ∪ Q)`;
* absorbing mode: `A ∪ P = (P ∪ P₁) ∪ (P₂ ∪ T_P) ∪ (J ∪ T_Q) ∪ (Q₂ ∪ Q₁) ∪ Q`.

Every triangle used has an allowed type: the subdivision triangles of position `i` all have
type `{r, s, c}`, the comparison triangles have their prescribed types, and the transformer
triangles have the auxiliary types supplied by `exists_auxiliary_types` (hypotheses `haP`,
`haQ`, discharged in `ColouredHub.Main`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate TypedTransformer

variable {t : ℕ}

/-! ### Typed subdivision blocks on an arbitrary vertex type -/

section GenericBlocks

variable {W : Type*} [DecidableEq W]

/-- `H ∪ ∇H` with typed middles. -/
theorem hasDecomp_single_typed {I : Type*} [Fintype I] (q : W → Fin t)
    (F : Finset (Multiset (Fin t))) (a b c : I → W) (hab : ∀ i, a i ≠ b i)
    (hinj : Function.Injective fun i => s(a i, b i)) (hc : Function.Injective c)
    (hca : ∀ i j, c i ≠ a j) (hcb : ∀ i j, c i ≠ b j)
    (hl : ∀ i, Link F (q (a i)) (q (b i)) (q (c i))) :
    HasDecomp q F (posEdges a b ∪ (posEdges a c ∪ posEdges c b)) := by
  rw [← labelEdges_subdivision]
  exact ⟨_, goodLabels_typed (goodLabels_subdivision a b c hab hinj hc hca hcb) q F hl⟩

/-- `∇H ∪ ∇∇H` with typed middles, presented along a trail system. -/
theorem hasDecomp_double_typed {m : ℕ} (q : W → Fin t) (F : Finset (Multiset (Fin t)))
    (base c1 c2 c3 : Fin m → W) (σ : Equiv.Perm (Fin m))
    (hc1 : Function.Injective c1) (hc2 : Function.Injective c2) (hc3 : Function.Injective c3)
    (h12 : ∀ i j, c1 i ≠ c2 j) (h13 : ∀ i j, c1 i ≠ c3 j) (h23 : ∀ i j, c2 i ≠ c3 j)
    (hb1 : ∀ i j, base i ≠ c1 j) (hb2 : ∀ i j, base i ≠ c2 j) (hb3 : ∀ i j, base i ≠ c3 j)
    (hne : ∀ j, base j ≠ base (σ j))
    (hl1 : ∀ i, Link F (q (base i)) (q (c2 i)) (q (c1 i)))
    (hl2 : ∀ i, Link F (q (c2 i)) (q (base (σ i))) (q (c3 i))) :
    HasDecomp q F ((posEdges base c2 ∪ posEdges c2 fun j => base (σ j)) ∪
      srcEdges (blowPerm σ) (fourPath base c1 c2 c3)) := by
  let a : Fin m × Fin 2 → W := fun z => ![base z.1, c2 z.1] z.2
  let b : Fin m × Fin 2 → W := fun z => ![c2 z.1, base (σ z.1)] z.2
  let c : Fin m × Fin 2 → W := fun z => ![c1 z.1, c3 z.1] z.2
  have hab : ∀ z, a z ≠ b z := by
    rintro ⟨j, k⟩
    fin_cases k
    · exact hb2 j j
    · exact fun h => hb2 (σ j) j h.symm
  have hinj : Function.Injective fun z => s(a z, b z) := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp only [a, b] at h <;>
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · cases hc2 h2; rfl
    · exact absurd h1 (hb2 _ _)
    · exact absurd h1 (hb2 _ _)
    · cases hc2 h2; exact absurd h1 (hne _)
    · exact absurd h1.symm (hb2 _ _)
    · cases hc2 h1; exact absurd h2.symm (hne _)
    · cases hc2 h1; rfl
    · exact absurd h1.symm (hb2 _ _)
  have hc : Function.Injective c := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp only [c] at h
    · cases hc1 h; rfl
    · exact absurd h (h13 _ _)
    · exact absurd h.symm (h13 _ _)
    · cases hc3 h; rfl
  have hca : ∀ z z', c z ≠ a z' := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp only [a, c] at h
    · exact hb1 _ _ h.symm
    · exact h12 _ _ h
    · exact hb3 _ _ h.symm
    · exact h23 _ _ h.symm
  have hcb : ∀ z z', c z ≠ b z' := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp only [b, c] at h
    · exact h12 _ _ h
    · exact hb1 _ _ h.symm
    · exact h23 _ _ h.symm
    · exact hb3 _ _ h.symm
  have hl : ∀ z, Link F (q (a z)) (q (b z)) (q (c z)) := by
    rintro ⟨j, k⟩
    fin_cases k
    · exact hl1 j
    · exact hl2 j
  have h := hasDecomp_single_typed q F a b c hab hinj hc hca hcb hl
  convert h using 1
  have e1 : posEdges a b = posEdges base c2 ∪ posEdges c2 fun j => base (σ j) := by
    ext e
    simp only [mem_union, mem_posEdges, Prod.exists, Fin.exists_fin_two, a, b]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    constructor
    · rintro ⟨j, h | h⟩
      exacts [Or.inl ⟨j, h⟩, Or.inr ⟨j, h⟩]
    · rintro (⟨j, h⟩ | ⟨j, h⟩)
      exacts [⟨j, Or.inl h⟩, ⟨j, Or.inr h⟩]
  have e2 : posEdges a c ∪ posEdges c b = srcEdges (blowPerm σ) (fourPath base c1 c2 c3) := by
    ext e
    rw [mem_srcEdges_fourPath]
    simp only [mem_union, mem_posEdges, Prod.exists, Fin.exists_fin_two, a, b, c]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    constructor
    · rintro (⟨j, h | h⟩ | ⟨j, h | h⟩)
      · exact ⟨j, Or.inl h⟩
      · exact ⟨j, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨j, Or.inr (Or.inl h)⟩
      · exact ⟨j, Or.inr (Or.inr (Or.inr h))⟩
    · rintro ⟨j, h | h | h | h⟩
      · exact Or.inl ⟨j, Or.inl h⟩
      · exact Or.inr ⟨j, Or.inl h⟩
      · exact Or.inl ⟨j, Or.inr h⟩
      · exact Or.inr ⟨j, Or.inr h⟩
  rw [e1, e2]

end GenericBlocks

/-! ### The blocks of the coloured-hub template -/

variable {V : Type*} [DecidableEq V] {m : ℕ} {T : Type*}
variable {F : Finset (Multiset (Fin t))} {p : V → Fin t} {σ : Equiv.Perm (Fin m)}
  {X : Fin m → V} {w : T → Fin 3 → Fin t} {π : Fin m ≃ T × Fin 3}
  {aP aQ : (Fin m × Fin 4) × Fin 3 → Fin t}

/-- The comparison graph is decomposed by its triangles, with their prescribed types. -/
theorem hasDecomp_blkQ [Finite T] (q : HV V m t → Fin t)
    (hl : ∀ x, Link F (q (ax (π.symm (x, 0)) .q)) (q (ax (π.symm (x, 1)) .q))
      (q (ax (π.symm (x, 2)) .q))) :
    HasDecomp q F (blkQ (V := V) π) := by
  classical
  have := Fintype.ofFinite T
  let ta : T → HV V m t := fun x => ax (π.symm (x, 0)) .q
  let tb : T → HV V m t := fun x => ax (π.symm (x, 1)) .q
  let tc : T → HV V m t := fun x => ax (π.symm (x, 2)) .q
  have key : ∀ x e, e ∈ tri3 (ta x) (tb x) (tc x) → ∀ v ∈ e,
      ∃ a : Fin 3, v = ax (π.symm (x, a)) .q := by
    intro x e he v hv
    rw [mem_tri3] at he
    rcases he with rfl | rfl | rfl <;> rcases Sym2.mem_iff.mp hv with rfl | rfl <;>
      first
      | exact ⟨0, rfl⟩
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
  have hne : ∀ x (a a' : Fin 3), a ≠ a' →
      (ax (π.symm (x, a)) .q : HV V m t) ≠ ax (π.symm (x, a')) .q := by
    intro x a a' haa h
    simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact haa h.2
  have hg : GoodLabels ta tb tc := by
    refine ⟨fun x => hne x 0 1 (by decide), fun x => hne x 0 2 (by decide),
      fun x => hne x 1 2 (by decide), ?_⟩
    intro x x' e he he'
    induction e using Sym2.ind with
    | _ u v =>
    obtain ⟨a, rfl⟩ := key x _ he u (Sym2.mem_mk_left u v)
    obtain ⟨a', ha'⟩ := key x' _ he' _ (Sym2.mem_mk_left _ v)
    simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true,
      EmbeddingLike.apply_eq_iff_eq] at ha'
    exact ha'.1
  have heq : labelEdges ta tb tc = blkQ π := by
    ext e
    rw [mem_labelEdges, blkQ, mem_posEdges]
    constructor
    · rintro ⟨x, he⟩
      rw [mem_tri3] at he
      rcases he with rfl | rfl | rfl
      · refine ⟨π.symm (x, 0), ?_⟩
        have : qPerm π (π.symm (x, 0)) = π.symm (x, 1) := by
          apply π.injective; simp
        rw [this]
      · refine ⟨π.symm (x, 2), ?_⟩
        have : qPerm π (π.symm (x, 2)) = π.symm (x, 0) := by
          apply π.injective; simp
        rw [this]; exact Sym2.eq_swap
      · refine ⟨π.symm (x, 1), ?_⟩
        have : qPerm π (π.symm (x, 1)) = π.symm (x, 2) := by
          apply π.injective; simp
        rw [this]
    · rintro ⟨i, rfl⟩
      obtain ⟨⟨x, a⟩, hπ⟩ : ∃ z, π i = z := ⟨_, rfl⟩
      have hi : i = π.symm (x, a) := by rw [← hπ]; simp
      have hq : qPerm π i = π.symm (x, a + 1) := by
        apply π.injective; simp [hπ]
      refine ⟨x, ?_⟩
      rw [mem_tri3, hq, hi]
      rcases (by decide : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2) a with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl Sym2.eq_swap)
  rw [← heq]
  exact ⟨_, goodLabels_typed hg q F hl⟩

/-! ### Part preservation of the two trail maps onto `J` -/

omit [DecidableEq V] in
theorem hpart_pathP_pathJ (z : Fin m × Fin 4) :
    hpart p σ X w π aP aQ (pathP X z) = hpart p σ X w π aP aQ (pathJ p X z) := by
  obtain ⟨i, k⟩ := z
  fin_cases k <;> rfl

omit [DecidableEq V] in
theorem hpart_pathQ_pathJQ (hM : Matched p σ X w π) (z : Fin m × Fin 4) :
    hpart p σ X w π aP aQ (pathQ z) = hpart p σ X w π aP aQ (pathJQ p X w π z) := by
  obtain ⟨i, k⟩ := z
  by_cases hf : pq w π i = rP p X i
  · have h2 := orient_fwd hM i hf
    rw [pathJQ_fwd hf]
    fin_cases k
    · exact hf
    · exact h2
    · rfl
    · exact hf
  · obtain ⟨h1, h2⟩ := orient_rev hM i hf
    rw [pathJQ_rev hf]
    fin_cases k
    · rfl
    · exact h2
    · rfl
    · exact h1

/-- `T_P`: both exact typed decompositions, `T_P ∪ P₂` and `T_P ∪ J`. -/
theorem isTransformer_TP
    (haP : AuxiliaryTypes F (blowPerm σ) (fun z => hpart p σ X w π aP aQ (pathP X z))
      (fun z => hpart p σ X w π aP aQ (auxTP z))) :
    IsTransformer (p := hpart p σ X w π aP aQ) (F := F) (blkTP p σ X) (blkP2 σ X)
      (blkJ p σ X) :=
  transformer_typed tdata_P _ F hpart_pathP_pathJ haP

/-- `T_Q`: both exact typed decompositions, `T_Q ∪ Q₂` and `T_Q ∪ J`. -/
theorem isTransformer_TQ (hM : Matched p σ X w π)
    (haQ : AuxiliaryTypes F (blowPerm (qPerm π)) (fun z => hpart p σ X w π aP aQ (pathQ z))
      (fun z => hpart p σ X w π aP aQ (auxTQ z))) :
    IsTransformer (p := hpart p σ X w π aP aQ) (F := F) (blkTQ p X w π) (blkQ2 π)
      (blkJ p σ X) := by
  have h := transformer_typed (tdata_Q hM) (hpart p σ X w π aP aQ) F
    (hpart_pathQ_pathJQ hM) haQ
  rwa [srcEdges_pathJQ hM] at h

/-! ### The subdivision blocks -/

theorem hasDecomp_P_P1 (hne : ∀ i, X i ≠ X (σ i))
    (hinj : Function.Injective fun i => s(X i, X (σ i)))
    (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) (hM : Matched p σ X w π) :
    HasDecomp (hpart p σ X w π aP aQ) F (blkP σ X ∪ blkP1 σ X) :=
  hasDecomp_single_typed _ F (fun i => old (X i)) (fun i => old (X (σ i))) (fun i => ax i .p1)
    (fun i h => hne i (Sum.inl.inj h))
    (fun i j h => hinj (by simpa only [Sym2.eq_iff, Sum.inl.injEq] using h))
    (fun i j h => by simpa using h) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun i => (link_of_mem (matched_mem hw hM i)).1)

theorem hasDecomp_P1_P2 (hne : ∀ i, X i ≠ X (σ i))
    (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) (hM : Matched p σ X w π) :
    HasDecomp (hpart p σ X w π aP aQ) F (blkP1 σ X ∪ blkP2 σ X) :=
  hasDecomp_double_typed _ F (fun i => old (X i)) (fun i => ax i .p2a) (fun i => ax i .p1)
    (fun i => ax i .p2b) σ (fun i j h => by simpa using h) (fun i j h => by simpa using h)
    (fun i j h => by simpa using h) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun i h => hne i (Sum.inl.inj h))
    (fun i => (link_of_mem (matched_mem hw hM i)).2.2.2.1)
    (fun i => (link_of_mem (matched_mem hw hM i)).2.2.2.2.2)

omit [DecidableEq V] in
theorem qEdge_injective' :
    Function.Injective fun i : Fin m => s((ax i .q : HV V m t), ax (qPerm π i) .q) := by
  intro i j h
  simp only [Sym2.eq_iff, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] at h
  rcases h with ⟨h, -⟩ | ⟨h1, h2⟩
  · exact h
  · subst h1
    exact absurd h2 (qPerm_ne2 π j)

theorem hasDecomp_Q_Q1 (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) :
    HasDecomp (hpart p σ X w π aP aQ) F (blkQ (V := V) π ∪ blkQ1 π) :=
  hasDecomp_single_typed _ F (fun i => ax i .q) (fun i => ax (qPerm π i) .q)
    (fun i => ax i .q1) (fun i h => qPerm_ne π i (by simpa using h.symm))
    qEdge_injective' (fun i j h => by simpa using h) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun i => (link_of_mem (pq_mem hw π i)).1)

theorem hasDecomp_Q1_Q2 (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) :
    HasDecomp (hpart p σ X w π aP aQ) F (blkQ1 (V := V) π ∪ blkQ2 π) :=
  hasDecomp_double_typed _ F (fun i => ax i .q) (fun i => ax i .q2a) (fun i => ax i .q1)
    (fun i => ax i .q2b) (qPerm π) (fun i j h => by simpa using h)
    (fun i j h => by simpa using h) (fun i j h => by simpa using h) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun i h => qPerm_ne π i (by simpa using h.symm))
    (fun i => (link_of_mem (pq_mem hw π i)).2.2.2.1)
    (fun i => (link_of_mem (pq_mem hw π i)).2.2.2.2.2)

theorem hasDecomp_Q [Finite T] (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) :
    HasDecomp (hpart p σ X w π aP aQ) F (blkQ (V := V) π) := by
  refine hasDecomp_blkQ _ fun x => ?_
  have e : ∀ a, hpart p σ X w π aP aQ (ax (π.symm (x, a)) .q) = w x a := fun a => by
    simp [hpart, tagPart, pq]
  rw [e, e, e]
  exact hw x

/-! ### The two modes -/

/-- **Empty mode.** `A = (P₁ ∪ P₂) ∪ (T_P ∪ J) ∪ (T_Q ∪ Q₂) ∪ (Q₁ ∪ Q)`. -/
theorem hasDecomp_hubTemplate [Finite T] (hne : ∀ i, X i ≠ X (σ i))
    (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) (hM : Matched p σ X w π)
    (haP : AuxiliaryTypes F (blowPerm σ) (fun z => hpart p σ X w π aP aQ (pathP X z))
      (fun z => hpart p σ X w π aP aQ (auxTP z)))
    (haQ : AuxiliaryTypes F (blowPerm (qPerm π)) (fun z => hpart p σ X w π aP aQ (pathQ z))
      (fun z => hpart p σ X w π aP aQ (auxTQ z))) :
    HasDecomp (hpart p σ X w π aP aQ) F (hubTemplate p σ X w π) := by
  have hB1 := hasDecomp_P1_P2 (aP := aP) (aQ := aQ) hne hw hM
  have hB2 := (isTransformer_TP haP).2.2
  have hB3 := (isTransformer_TQ hM haQ).2.1
  have hB4 : HasDecomp (hpart p σ X w π aP aQ) F (blkQ1 (V := V) π ∪ blkQ π) := by
    rw [union_comm]; exact hasDecomp_Q_Q1 hw
  have i1 := (pieceIn_P1 (t := t) σ X).union (pieceIn_P2 σ X)
  have i2 := (pieceIn_TP p σ X).union (pieceIn_J p σ X)
  have i3 := (pieceIn_TQ p X w π).union (pieceIn_Q2 π)
  have i4 := (pieceIn_Q1 (V := V) (t := t) π).union (pieceIn_Q π)
  have h12 := hB1.union hB2 (i1.disjoint i2 (by decide))
  have h123 := h12.union hB3 ((i1.union i2).disjoint i3 (by decide))
  have h1234 := h123.union hB4 (((i1.union i2).union i3).disjoint i4 (by decide))
  convert h1234 using 1
  simp only [hubTemplate, union_assoc]

/-- **Absorbing mode.** `A ∪ P = (P ∪ P₁) ∪ (P₂ ∪ T_P) ∪ (J ∪ T_Q) ∪ (Q₂ ∪ Q₁) ∪ Q`. -/
theorem hasDecomp_hubTemplate_union [Finite T] (hne : ∀ i, X i ≠ X (σ i))
    (hinj : Function.Injective fun i => s(X i, X (σ i)))
    (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) (hM : Matched p σ X w π)
    (haP : AuxiliaryTypes F (blowPerm σ) (fun z => hpart p σ X w π aP aQ (pathP X z))
      (fun z => hpart p σ X w π aP aQ (auxTP z)))
    (haQ : AuxiliaryTypes F (blowPerm (qPerm π)) (fun z => hpart p σ X w π aP aQ (pathQ z))
      (fun z => hpart p σ X w π aP aQ (auxTQ z))) :
    HasDecomp (hpart p σ X w π aP aQ) F (hubTemplate p σ X w π ∪ blkP σ X) := by
  have hC1 := hasDecomp_P_P1 (aP := aP) (aQ := aQ) hne hinj hw hM
  have hC2 : HasDecomp (hpart p σ X w π aP aQ) F (blkP2 σ X ∪ blkTP p σ X) := by
    rw [union_comm]; exact (isTransformer_TP haP).2.1
  have hC3 : HasDecomp (hpart p σ X w π aP aQ) F (blkJ p σ X ∪ blkTQ p X w π) := by
    rw [union_comm]; exact (isTransformer_TQ hM haQ).2.2
  have hC4 : HasDecomp (hpart p σ X w π aP aQ) F (blkQ2 (V := V) π ∪ blkQ1 π) := by
    rw [union_comm]; exact hasDecomp_Q1_Q2 hw
  have hC5 := hasDecomp_Q (V := V) (p := p) (σ := σ) (X := X) (π := π) (aP := aP) (aQ := aQ) hw
  have i1 := (pieceIn_P (t := t) σ X).union (pieceIn_P1 σ X)
  have i2 := (pieceIn_P2 (t := t) σ X).union (pieceIn_TP p σ X)
  have i3 := (pieceIn_J p σ X).union (pieceIn_TQ p X w π)
  have i4 := (pieceIn_Q2 (V := V) (t := t) π).union (pieceIn_Q1 π)
  have i5 := pieceIn_Q (V := V) (t := t) π
  have h12 := hC1.union hC2 (i1.disjoint i2 (by decide))
  have h123 := h12.union hC3 ((i1.union i2).disjoint i3 (by decide))
  have h1234 := h123.union hC4 (((i1.union i2).union i3).disjoint i4 (by decide))
  have h12345 := h1234.union hC5 ((((i1.union i2).union i3).union i4).disjoint i5 (by decide))
  convert h12345 using 1
  simp only [hubTemplate]
  ac_rfl

end PartitionedTriangleAbsorption.ColouredHub
