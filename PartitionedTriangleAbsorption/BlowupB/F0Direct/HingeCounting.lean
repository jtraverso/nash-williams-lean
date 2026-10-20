/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.HingeTemplates
import PartitionedTriangleAbsorption.PhysicalHingeSupply.Supply
import Mathlib.Data.Fintype.BigOperators

/-! # Counting physical hinges from bounded fibres of labelled templates

The finite templates are transported injectively.  The counting argument
allows several vertex choices to give the same physical edge set; each fibre
has at most `i^k` elements when its `k` free vertices belong to an `i`-vertex
physical support.  Consequently no equality between labelled and physical
counts is assumed.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HingeCounting

open Finset PhysicalHingeSupply

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem injective_of_two_blocks {A B D : Type*} (f : D → V) (left : A → D) (right : B → D)
    (hcover : ∀ j, (∃ a, j = left a) ∨ ∃ b, j = right b)
    (hleft : Function.Injective (fun a => f (left a)))
    (hright : Function.Injective (fun b => f (right b)))
    (hdis : ∀ a b, f (left a) ≠ f (right b)) : Function.Injective f := by
  intro j k hjk
  rcases hcover j with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;>
    rcases hcover k with ⟨c, rfl⟩ | ⟨d, rfl⟩
  · exact congrArg left (hleft hjk)
  · exact False.elim (hdis a d hjk)
  · exact False.elim (hdis c b hjk.symm)
  · exact congrArg right (hright hjk)

theorem vertSet_image {W : Type*} [Fintype W] [DecidableEq W]
    (E : Finset (Sym2 W)) (f : W → V) :
    vertSet (E.image (Sym2.map f)) = (vertSet E).image f := by
  ext v
  constructor
  · intro hv
    obtain ⟨-, e, he, hve⟩ := mem_filter.mp hv
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hve
    exact mem_image.mpr ⟨w, mem_filter.mpr ⟨mem_univ _, e', he', hw⟩, rfl⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    obtain ⟨-, e, he, hwe⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨mem_univ _, Sym2.map f e,
      mem_image.mpr ⟨e, he, rfl⟩, Sym2.mem_map.mpr ⟨w, hwe, rfl⟩⟩

theorem card_vertSet_image {W : Type*} [Fintype W] [DecidableEq W]
    (E : Finset (Sym2 W)) (hE : vertSet E = univ) (f : W → V)
    (hf : Function.Injective f) :
    (vertSet (E.image (Sym2.map f))).card = Fintype.card W := by
  rw [vertSet_image, hE, card_image_of_injective _ hf, card_univ]

theorem isHinge_image {W : Type*} [DecidableEq W] {t : ℕ}
    (p : V → Fin t) (pW : W → Fin t) (F : Finset (Multiset (Fin t)))
    (S S' : Finset W) (E : Finset (Sym2 W)) (f : W → V)
    (hf : Function.Injective f) (hp : ∀ w, p (f w) = pW w)
    (h : IsHinge pW F S S' E) :
    IsHinge p F (S.image f) (S'.image f) (E.image (Sym2.map f)) := by
  let fe : W ↪ V := ⟨f, hf⟩
  have hm := isHinge_map fe hp h
  simpa only [map_eq_image, edgeEmb, Function.Embedding.coeFn_mk, fe] using hm

theorem coordinate_fiber_count {ι : Type*} [DecidableEq ι] (k i : ℕ)
    (P : Finset ι) (K : Finset (Finset (Sym2 V)))
    (H : ι → Finset (Sym2 V)) (coord : ι → Fin k → V)
    (hinj : Set.InjOn coord P) (hmap : ∀ q ∈ P, H q ∈ K)
    (hsupport : ∀ q ∈ P, ∀ j, coord q j ∈ vertSet (H q))
    (hK : ∀ E ∈ K, (vertSet E).card = i) :
    P.card ≤ i^k * K.card := by
  have hfiber : ∀ E ∈ K, (P.filter fun q => H q = E).card ≤ i^k := by
    intro E hE
    have hb : (P.filter fun q => H q = E).card ≤
        (Fintype.piFinset (fun _ : Fin k => vertSet E)).card := by
      apply card_le_card_of_injOn coord
      · intro q hq
        obtain ⟨hqP, hqE⟩ := mem_filter.mp hq
        apply Fintype.mem_piFinset.mpr
        intro j
        rw [← hqE]
        exact hsupport q hqP j
      · intro q hq q' hq' heq
        exact hinj (mem_filter.mp hq).1 (mem_filter.mp hq').1 heq
    simpa [Fintype.card_piFinset, hK E hE] using hb
  have hsum := card_eq_sum_card_fiberwise (f := H) (s := P) (t := K) hmap
  rw [hsum]
  calc
    (∑ E ∈ K, (P.filter fun q => H q = E).card) ≤ ∑ _E ∈ K, i^k := sum_le_sum hfiber
    _ = i^k * K.card := by simp [Nat.mul_comm]

theorem physical_count_of_coordinates {ι : Type*} [DecidableEq ι]
    (k i : ℕ) (hi : 0 < i) (P : Finset ι) (K : Finset (Finset (Sym2 V)))
    (H : ι → Finset (Sym2 V)) (coord : ι → Fin k → V)
    (hinj : Set.InjOn coord P) (hmap : ∀ q ∈ P, H q ∈ K)
    (hsupport : ∀ q ∈ P, ∀ j, coord q j ∈ vertSet (H q))
    (hK : ∀ E ∈ K, (vertSet E).card = i) (c : ℝ)
    (hcount : c * (i : ℝ)^k ≤ P.card) : c ≤ K.card := by
  have hn := coordinate_fiber_count k i P K H coord hinj hmap hsupport hK
  have hr : (P.card : ℝ) ≤ (i : ℝ)^k * K.card := by exact_mod_cast hn
  have hipos : (0 : ℝ) < (i : ℝ)^k := pow_pos (by exact_mod_cast hi) _
  have hmul : c * (i : ℝ)^k ≤ (K.card : ℝ) * (i : ℝ)^k := by nlinarith only [hcount, hr]
  exact (mul_le_mul_iff_left₀ hipos).mp (by simpa [mul_comm] using hmul)

noncomputable def countedHinges {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (S S' : Finset V) (i : ℕ) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact G.edgeFinset.powerset.filter (fun E => IsHinge p F S S' E ∧ (vertSet E).card = i)

theorem mem_countedHinges {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (S S' : Finset V) (i : ℕ)
    (E : Finset (Sym2 V)) : E ∈ countedHinges p F G S S' i ↔
      E ⊆ G.edgeFinset ∧ IsHinge p F S S' E ∧ (vertSet E).card = i := by
  classical
  simp only [countedHinges, mem_filter, mem_powerset]

theorem template_count {ι : Type*} [DecidableEq ι] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (S S' : Finset V)
    (k i : ℕ) (hi : 0 < i) (E : Finset (Sym2 (Fin i))) (hE : vertSet E = univ)
    (P : Finset ι) (f : ι → Fin i → V) (loc : Fin k → Fin i)
    (hcoords : Set.InjOn (fun q j => f q (loc j)) P)
    (hfinj : ∀ q ∈ P, Function.Injective (f q))
    (hhinge : ∀ q ∈ P, IsHinge p F S S' (E.image (Sym2.map (f q))))
    (hhost : ∀ q ∈ P, E.image (Sym2.map (f q)) ⊆ G.edgeFinset)
    (c : ℝ) (hcount : c * (i : ℝ)^k ≤ P.card) :
    c ≤ (countedHinges p F G S S' i).card := by
  classical
  apply physical_count_of_coordinates k i hi P (countedHinges p F G S S' i)
    (fun q => E.image (Sym2.map (f q))) (fun q j => f q (loc j)) hcoords
  · intro q hq
    apply (mem_countedHinges p F G S S' i _).mpr
    refine ⟨hhost q hq, hhinge q hq, ?_⟩
    simpa only [Fintype.card_fin] using card_vertSet_image E hE (f q) (hfinj q hq)
  · intro q hq j
    rw [vertSet_image, hE]
    exact mem_image.mpr ⟨loc j, mem_univ _, rfl⟩
  · intro H hH
    exact ((mem_countedHinges p F G S S' i H).mp hH).2.2
  · exact hcount

#print axioms coordinate_fiber_count
#print axioms physical_count_of_coordinates
#print axioms isHinge_image
#print axioms template_count

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HingeCounting
