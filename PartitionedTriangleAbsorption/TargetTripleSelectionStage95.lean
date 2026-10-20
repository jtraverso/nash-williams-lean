/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Fibre
public import PartitionedTriangleAbsorption.TypedCatalystBridgeStage93

/-! # Selecting target triples of actual original tokens

Nonnegative type coefficients specify a disjoint family of abstract triangle
slots. The accepted fibre equivalence matches these slots to actual original
edges. This constructs their partition into target triples, including repeated
labels. The insertion invariant then transports the assignment to the current
physical token positions. No physical cut or terminal decomposition is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TargetTripleSelectionStage95

open Finset ColouredHub CatalystInsertionStage89

variable {t : ℕ} {V : Type*}

abbrev Slots (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℕ) :=
  Tri F c × Fin 3

/-- Read the actual finite original edges as the accepted fibre vector. -/
theorem edgeVec_eq_vecOf (p : V → Fin t) (Y : Finset (Sym2 V)) :
    vecOf (fun e : Y => Sym2.map p e.val) = edgeVec p Y := by
  classical
  have hpair (e : Sym2 V) : pv (Sym2.map p e) = pairVec p e := by
    induction e using Sym2.ind with
    | _ u v => rfl
  unfold vecOf edgeVec
  simp_rw [hpair]
  exact Y.sum_coe_sort (fun e => pairVec p e)

/-- Produce the global slot assignment from nonnegative coefficients, not
from a supplied token partition or a decomposition of the physical graph. -/
theorem exists_assignment (p : V → Fin t) (Y : Finset (Sym2 V))
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (c : Multiset (Fin t) → ℕ)
    (hvec : edgeVec p Y = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ) :
    ∃ f : Slots F c ≃ Y, ∀ x a,
      Sym2.map p (f (x,a)).val = slotPair (triWord F hF c) (x,a) := by
  classical
  have h : vecOf (slotPair (triWord F hF c)) =
      vecOf (fun e : Y => Sym2.map p e.val) := by
    rw [vecOf_slotPair, edgeVec_eq_vecOf, hvec]
  obtain ⟨f, hf⟩ := exists_fibre_equiv h
  exact ⟨f, fun x a => hf (x,a)⟩

/-- The three original edge tokens assigned to a target triangle. -/
noncomputable def group {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (x : Tri F c) : Finset (Sym2 V) := by
  classical
  exact univ.image (fun a : Fin 3 => (f (x,a)).val)

theorem group_card {F : Finset (Multiset (Fin t))} {c : Multiset (Fin t) → ℕ}
    {Y : Finset (Sym2 V)} (f : Slots F c ≃ Y) (x : Tri F c) :
    (group f x).card = 3 := by
  classical
  rw [group, card_image_of_injective]
  · simp
  · intro a b h
    have he := f.injective (Subtype.ext h)
    exact congrArg Prod.snd he

theorem group_subset {F : Finset (Multiset (Fin t))} {c : Multiset (Fin t) → ℕ}
    {Y : Finset (Sym2 V)} (f : Slots F c ≃ Y) (x : Tri F c) :
    group f x ⊆ Y := by
  classical
  intro e he
  obtain ⟨a, -, rfl⟩ := mem_image.mp he
  exact (f (x,a)).property

theorem groups_disjoint {F : Finset (Multiset (Fin t))} {c : Multiset (Fin t) → ℕ}
    {Y : Finset (Sym2 V)} (f : Slots F c ≃ Y) {x y : Tri F c} (hxy : x ≠ y) :
    Disjoint (group f x) (group f y) := by
  classical
  rw [disjoint_left]
  intro e hx hy
  obtain ⟨a, -, ha⟩ := mem_image.mp hx
  obtain ⟨b, -, hb⟩ := mem_image.mp hy
  have he := f.injective (Subtype.ext (ha.trans hb.symm))
  exact hxy (congrArg Prod.fst he)

open Classical in
theorem groups_cover {F : Finset (Multiset (Fin t))} {c : Multiset (Fin t) → ℕ}
    {Y : Finset (Sym2 V)} (f : Slots F c ≃ Y) :
    univ.biUnion (group f) = Y := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨x, -, hx⟩ := mem_biUnion.mp he
    exact group_subset f x hx
  · intro he
    obtain ⟨⟨x,a⟩, hf⟩ := f.surjective ⟨e,he⟩
    apply mem_biUnion.mpr
    refine ⟨x, mem_univ _, mem_image.mpr ⟨a, mem_univ _, ?_⟩⟩
    exact congrArg Subtype.val hf

/-- A physical edge with a prescribed unordered label pair can be oriented
to those labels. Repeated labels cause no failure of distinctness. -/
theorem ordered_endpoints (p : V → Fin t) (e : Sym2 V) (i j : Fin t)
    (htype : Sym2.map p e = s(i, j)) (hloop : ¬ e.IsDiag) :
    ∃ u v, e = s(u, v) ∧ u ≠ v ∧ p u = i ∧ p v = j := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := fun h => hloop (by simp [h])
    change s(p u, p v) = s(i, j) at htype
    rcases Sym2.eq_iff.mp htype with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact ⟨u,v,rfl,huv,hu,hv⟩
    · exact ⟨v,u,Sym2.eq_swap,huv.symm,hv,hu⟩

section Inserted

variable [Fintype V] [DecidableEq V]
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)}
variable {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}
variable {U : Finset (Sym2 V)} {Z : Finset V}

/-- Different original tokens still occupy different physical edges. -/
theorem original_positions_injective (fr : Frame p F G B S Z₀)
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z) :
    Function.Injective (fun e : S.Y => S.curY cz cz' S.A e.val) := by
  intro e e' he
  have ht := tokPos_injOn fr inv.carriers
    ((mem_tokens_inl e.val).mpr e.property)
    ((mem_tokens_inl e'.val).mpr e'.property) he
  exact Subtype.ext (Sum.inl.inj ht)

/-- Distinct original tokens have disjoint endpoint supports after insertion.
This is stronger than injectivity of their edge positions. -/
theorem original_positions_separated (fr : Frame p F G B S Z₀)
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z) (e e' : S.Y) (hne : e ≠ e') :
    ∀ v, v ∈ S.curY cz cz' S.A e.val → v ∉ S.curY cz cz' S.A e'.val := by
  intro v hv hv'
  obtain ⟨y,hy,rfl | rfl⟩ := curY_carrier fr e.property hv
  · have h1 := (cz_mem_curY fr inv.carriers hy e.property).mp hv
    have h2 := (cz_mem_curY fr inv.carriers hy e'.property).mp hv'
    exact hne (Subtype.ext (h1.trans h2.symm))
  · have h1 := (cz'_mem_curY fr inv.carriers hy e.property).mp hv
    have h2 := (cz'_mem_curY fr inv.carriers hy e'.property).mp hv'
    exact hne (Subtype.ext (h1.trans h2.symm))

/-- Select triples in the current physical configuration after actual
catalyst insertion. The original positions are injective and have exactly
the required types; their image contains all and only original positions. -/
theorem exists_inserted_assignment (fr : Frame p F G B S Z₀)
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z)
    (hF : ∀ τ ∈ F, τ.card = 3) (c : Multiset (Fin t) → ℕ)
    (hvec : edgeVec p S.Y = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ) :
    ∃ f : Slots F c ≃ S.Y,
      (∀ x a, Sym2.map p (S.curY cz cz' S.A (f (x,a)).val) =
        slotPair (triWord F hF c) (x,a)) ∧
      Function.Injective (fun z => S.curY cz cz' S.A (f z).val) ∧
      univ.image (fun z => S.curY cz cz' S.A (f z).val) =
        S.Y.image (S.curY cz cz' S.A) := by
  classical
  obtain ⟨f,hf⟩ := exists_assignment p S.Y F hF c hvec
  refine ⟨f, ?_, (original_positions_injective fr inv).comp f.injective, ?_⟩
  · intro x a
    rw [TypedCatalystBridgeStage93.original_token_type inv, hf]
  · ext e
    constructor
    · intro he
      obtain ⟨z, -, rfl⟩ := mem_image.mp he
      exact mem_image.mpr ⟨(f z).val, (f z).property, rfl⟩
    · intro he
      obtain ⟨y,hy,rfl⟩ := mem_image.mp he
      obtain ⟨z,hz⟩ := f.surjective ⟨y,hy⟩
      exact mem_image.mpr ⟨z, mem_univ _, congrArg (fun e : S.Y => S.curY cz cz' S.A e.val) hz⟩

/-- The prescribed corner labels can be read on two distinct actual
endpoints of each current original position, even when labels repeat. -/
theorem exists_inserted_ordered_assignment (fr : Frame p F G B S Z₀)
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z)
    (hF : ∀ τ ∈ F, τ.card = 3) (c : Multiset (Fin t) → ℕ)
    (hvec : edgeVec p S.Y = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ) :
    ∃ f : Slots F c ≃ S.Y, ∃ l r : Slots F c → V,
      (∀ z, S.curY cz cz' S.A (f z).val = s(l z, r z) ∧
        l z ≠ r z ∧ p (l z) = triWord F hF c z.1 z.2 ∧
        p (r z) = triWord F hF c z.1 (z.2 + 1)) ∧
      (∀ z z', z ≠ z' → ∀ v, v ∈ S.curY cz cz' S.A (f z).val →
        v ∉ S.curY cz cz' S.A (f z').val) ∧
      Function.Injective (fun z => S.curY cz cz' S.A (f z).val) ∧
      univ.image (fun z => S.curY cz cz' S.A (f z).val) =
        S.Y.image (S.curY cz cz' S.A) := by
  classical
  obtain ⟨f,hf,hi,hcov⟩ := exists_inserted_assignment fr inv hF c hvec
  have hend (z : Slots F c) : ∃ u v,
      S.curY cz cz' S.A (f z).val = s(u, v) ∧ u ≠ v ∧
      p u = triWord F hF c z.1 z.2 ∧
      p v = triWord F hF c z.1 (z.2 + 1) := by
    have hm : S.curY cz cz' S.A (f z).val ∈ S.config cz cz' S.A :=
      mem_union.mpr (Or.inl (mem_image.mpr ⟨(f z).val, (f z).property, rfl⟩))
    have hloop := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (inv.real hm))
    exact ordered_endpoints p _ _ _ (hf z.1 z.2) hloop
  choose l r hrep hne hl hr using hend
  refine ⟨f,l,r,fun z => ⟨hrep z,hne z,hl z,hr z⟩,?_,hi,hcov⟩
  intro z z' hzz'
  exact original_positions_separated fr inv (f z) (f z')
    (fun h => hzz' (f.injective h))

end Inserted

end PartitionedTriangleAbsorption.TargetTripleSelectionStage95
