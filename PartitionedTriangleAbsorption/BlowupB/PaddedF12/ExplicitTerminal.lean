/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.ExplicitHub
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedTerminal

/-!
# Terminal F1/F2 absorbers with an explicit uniform size and order

The bounded negative mass proved from the original edge vector replaces the
existential finite-choice bound. All embeddings fix the original roots.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General

universe u

theorem guarded_terminal_absorber_of_mass {t : ℕ} (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hF : ThreeStepLinks F) (K B : ℕ)
    (hcoeff : ∀ {W : Type} [DecidableEq W] (p : W → Fin t) (P : Finset (Sym2 W)),
      P.card ≤ K → IsIntDiv p F P → ∃ c : Multiset (Fin t) → ℤ,
        edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧ negativeMass F c ≤ B) :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
        (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V),
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) (terminalOrder K B t) a →
      DegBounded L d → 0 ≤ d →
      (terminalOrder K B t : ℝ) + Z.card + terminalOrder K B t * d < a →
      ∀ P : Finset (Sym2 V), P.card ≤ K → (∀ e ∈ P, ¬ e.IsDiag) →
      IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), TerminalAbsorber p F G P L Z (terminalSize K B) A := by
  classical
  intro V instFin instEq p G instAdj a d L Z hs hL hd hbudget P hK hloop hdiv
  by_cases hzero : P = ∅
  · subst P
    refine ⟨∅, ⟨by simp, by simp, by simp, hasDecomp_empty, ?_, by simp, ?_, ?_, ?_⟩⟩
    · simpa using (hasDecomp_empty (p := p) (F := F))
    · simp [vertSet]
    · simp [vertSet]
    · simp [vertSet]
  · have hV : Nonempty V := by
      obtain ⟨e, _⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
      induction e using Sym2.ind with
      | _ v w => exact ⟨v⟩
    let fallback : V := Classical.choice hV
    let W := Fin (vertSet P).card
    let r : W ↪ V := supportEmbedding P
    let PW : Finset (Sym2 W) := compactPiece P
    let pW : W → Fin t := p ∘ r
    have hPWcard : PW.card ≤ K := (compactPiece_card P).trans_le hK
    have hPWloop : ∀ e ∈ PW, ¬ e.IsDiag := compactPiece_loopless P hloop
    have hPWdiv : IsIntDiv pW F PW := compactPiece_isIntDiv P p F hdiv
    have hPWeven : ∀ w, Even (incidentLoad PW w) :=
      even_of_isIntDiv hF3 hPWloop hPWdiv
    obtain ⟨c, m', label, A, hlabel, hnoold, hdis, hA, hAP, hAsize, hAux, hrootload⟩ :=
      bounded_lattice_absorber_of_mass F hF3 hF K B pW PW hPWcard hPWloop hPWeven
        (hcoeff pW PW hPWcard hPWdiv)
    let X := ColouredHub.HV (TypedLatticePadding.Ext W (TypedPaddingProducer.Index F c)) m' t
    let ι : W ↪ X := ⟨fun w => Sum.inl (Sum.inl w), by
      intro w w' h
      exact Sum.inl_injective (Sum.inl_injective h)⟩
    let R : Finset X := univ.image ι
    let rootMap : X → V := fun x => match x with
      | Sum.inl (Sum.inl w) => r w
      | _ => fallback
    let T : SimpleGraph X := SimpleGraph.fromEdgeSet A
    have hrootMap (w : W) : rootMap (ι w) = r w := rfl
    have hrootmem (w : W) : ι w ∈ R := mem_image.mpr ⟨w, mem_univ _, rfl⟩
    have hArloop : ∀ e ∈ A, ¬ e.IsDiag := ColouredHub.loopless_of_hasDecomp hA
    have hadj (x y : X) (hxy : s(x, y) ∈ A) : T.Adj x y := by
      apply (SimpleGraph.fromEdgeSet_adj _).mpr
      refine ⟨hxy, ?_⟩
      intro heq
      exact hArloop _ hxy (by simp [heq])
    have hproper : ∀ x y, T.Adj x y → ∃ k, Link F (label x) (label y) k := by
      intro x y hxy
      exact active_of_isIntDiv hF3 (isIntDiv_of_hasDecomp hA) x y
        ((SimpleGraph.fromEdgeSet_adj _).mp hxy).1
    have hcardX : Fintype.card X ≤ terminalOrder K B t := by
      have hrootcard : Fintype.card W ≤ 2 * K := by
        simpa only [W, Fintype.card_fin] using
          (SignedHinge.card_vertSet_le P).trans (Nat.mul_le_mul_left 2 hK)
      simp only [X, ColouredHub.HV, TypedLatticePadding.Ext, Fintype.card_sum] at hAux ⊢
      unfold terminalOrder
      omega
    have hcardXR : (Fintype.card X : ℝ) ≤ terminalOrder K B t := by exact_mod_cast hcardX
    have hbudgetX : (Fintype.card X : ℝ) + Z.card + Fintype.card X * d < a := by
      have hmul := mul_le_mul_of_nonneg_right hcardXR hd
      linarith
    have hpartial : PartialEmbedding T G L R rootMap := by
      constructor
      · intro x hx y hy hxy
        obtain ⟨w, _, rfl⟩ := mem_image.mp hx
        obtain ⟨w', _, rfl⟩ := mem_image.mp hy
        exact congrArg ι (r.injective (by simpa only [hrootMap] using hxy))
      · intro x hx y hy hxy
        obtain ⟨w, _, rfl⟩ := mem_image.mp hx
        obtain ⟨w', _, rfl⟩ := mem_image.mp hy
        exact False.elim (hnoold w w' ((SimpleGraph.fromEdgeSet_adj _).mp hxy).1)
    have hrootlabel : ∀ x ∈ R, p (rootMap x) = label x := by
      intro x hx
      obtain ⟨w, _, rfl⟩ := mem_image.mp hx
      exact (hlabel w).symm
    obtain ⟨f, hflabel, hffix, hfedges, hfavoid⟩ := guarded_exists_embedding
      T G p label (fun i j => ∃ k, Link F i j k) hproper a d
      (hs.mono hcardX le_rfl) L Z hL hd hbudgetX R rootMap hpartial hrootlabel
    have hfix (w : W) : f (ι w) = r w := (hffix _ (hrootmem w)).trans (hrootMap w)
    let A' : Finset (Sym2 V) := A.image (Sym2.map f)
    have hPQ : ColouredHub.liftOld m' (TypedLatticePadding.liftE
        (T := TypedPaddingProducer.Index F c) PW) = PW.image (Sym2.map ι) := by
      simp only [ColouredHub.liftOld, TypedLatticePadding.liftE, image_image]
      congr 1
      funext e
      induction e using Sym2.ind with
      | _ x y => rfl
    have hPimage : (ColouredHub.liftOld m' (TypedLatticePadding.liftE
        (T := TypedPaddingProducer.Index F c) PW)).image (Sym2.map f) = P := by
      rw [hPQ, image_image]
      change PW.image (fun e => Sym2.map f (Sym2.map ι e)) = P
      have heq : (fun e => Sym2.map f (Sym2.map ι e)) = Sym2.map r := by
        funext e
        induction e using Sym2.ind with
        | _ x y => simp only [Sym2.map_mk, hfix]
      rw [heq]
      exact compactPiece_image P
    have hAhost : A' ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨e', he', rfl⟩ := mem_image.mp he
      induction e' using Sym2.ind with
      | _ x y =>
        exact SimpleGraph.mem_edgeFinset.mpr ((hfedges x y (hadj x y he')).1)
    have hAL : Disjoint A' L := by
      rw [disjoint_left]
      intro e he hle
      obtain ⟨e', he', rfl⟩ := mem_image.mp he
      induction e' using Sym2.ind with
      | _ x y => exact (hfedges x y (hadj x y he')).2 hle
    have hAPdis : Disjoint A' P := by
      have himage := (disjoint_image (Sym2.map.injective f.injective)).mpr hdis
      rw [hPimage] at himage
      exact himage
    have hdecomp : HasDecomp p F A' :=
      ColouredHub.hasDecomp_image_typed f f.injective hflabel A hA
    have hdecompP : HasDecomp p F (A' ∪ P) := by
      have h := ColouredHub.hasDecomp_image_typed f f.injective hflabel _ hAP
      rwa [image_union, hPimage] at h
    have hvertices : ∀ v ∈ vertSet A', v ∈ vertSet P ∨ v ∉ Z := by
      intro v hv
      obtain ⟨e, he, hve⟩ := SignedHinge.mem_vertSet.mp hv
      obtain ⟨e', he', rfl⟩ := mem_image.mp he
      obtain ⟨x, _, rfl⟩ := Sym2.mem_map.mp hve
      by_cases hx : x ∈ R
      · obtain ⟨w, _, rfl⟩ := mem_image.mp hx
        rw [hfix]
        exact Or.inl (supportEmbedding_mem P w)
      · exact Or.inr (hfavoid x hx)
    have hnoroot : ∀ v ∈ vertSet P, ∀ w ∈ vertSet P, s(v, w) ∉ A' := by
      intro v hv w hw hedge
      obtain ⟨i, hi⟩ := supportEmbedding_surjective P hv
      obtain ⟨j, hj⟩ := supportEmbedding_surjective P hw
      change r i = v at hi
      change r j = w at hj
      obtain ⟨e, he, heq⟩ := mem_image.mp hedge
      have hmap : Sym2.map f e = Sym2.map f s(ι i, ι j) := by
        simpa only [Sym2.map_mk, hfix, hi, hj] using heq
      have heq' := Sym2.map.injective f.injective hmap
      subst e
      exact hnoold i j he
    have hloads : ∀ v ∈ vertSet P, incidentLoad A' v = 4 * incidentLoad P v := by
      intro v hv
      obtain ⟨w, hw⟩ := supportEmbedding_surjective P hv
      calc
        incidentLoad A' v = incidentLoad A' (f (ι w)) := by rw [hfix, hw]
        _ = incidentLoad A (ι w) := ColouredHub.incidentLoad_image_apply f f.injective A (ι w)
        _ = 4 * incidentLoad PW w := hrootload w
        _ = 4 * incidentLoad P v := by rw [compactPiece_incidentLoad, hw]
    refine ⟨A', ⟨hAhost, hAL, hAPdis, hdecomp, hdecompP, ?_, hvertices, hnoroot, hloads⟩⟩
    exact (card_image_le).trans hAsize


/-- An explicit family-uniform coefficient package for F1 and F2. -/
theorem f12_bounded_coefficients (F : Finset (Multiset (Fin 4))) (hF : F = F1 ∨ F = F2)
    (K : ℕ) {W : Type*} [DecidableEq W] (p : W → Fin 4) (P : Finset (Sym2 W))
    (hK : P.card ≤ K) (hdiv : IsIntDiv p F P) :
    ∃ c : Multiset (Fin 4) → ℤ, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧
      negativeMass F c ≤ 32 * K := by
  rcases hF with rfl | rfl
  · obtain ⟨c, hc, hm, _⟩ := f1_bounded_coefficients K p P hK hdiv
    exact ⟨c, hc, hm⟩
  · obtain ⟨c, hc, hm, _⟩ := f2_bounded_coefficients K p P hK hdiv
    exact ⟨c, hc, hm⟩

/-- Both the full template order and edge count fit in the fixed budget `2^21`. -/
theorem f12_terminal_budgets :
    terminalOrder 144 (32 * 144) 4 = 489028 ∧
    terminalSize 144 (32 * 144) = 1480464 ∧
    terminalOrder 144 (32 * 144) 4 ≤ 2 ^ 21 ∧
    terminalSize 144 (32 * 144) ≤ 2 ^ 21 := by decide

/-- A uniform numerical terminal producer for the 144-edge F1/F2 library. -/
theorem guarded_terminal_F12 (F : Finset (Multiset (Fin 4))) (hF : F = F1 ∨ F = F2)
    {V : Type u} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) a)
    (hL : DegBounded L d) (hd : 0 ≤ d)
    (hbudget : (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a)
    (P : Finset (Sym2 V)) (hK : P.card ≤ 144) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (hdiv : IsIntDiv p F P) :
    ∃ A : Finset (Sym2 V), TerminalAbsorber p F G P L Z (2 ^ 21) A := by
  have hF3 : ∀ τ ∈ F, Multiset.card τ = 3 := by
    rcases hF with rfl | rfl
    · exact TypedTransportExamples.F1_card
    · exact TypedTransportExamples.F2_card
  have hlinks : ThreeStepLinks F := by
    rcases hF with rfl | rfl
    · exact F1_three_step
    · exact F2_three_step
  have hq : terminalOrder 144 (32 * 144) 4 ≤ 2 ^ 21 := f12_terminal_budgets.2.2.1
  have hqR : (terminalOrder 144 (32 * 144) 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hq
  have hbudget' : (terminalOrder 144 (32 * 144) 4 : ℝ) + Z.card +
      terminalOrder 144 (32 * 144) 4 * d < a := by
    have hm := mul_le_mul_of_nonneg_right hqR hd
    linarith
  obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass F hF3 hlinks 144 (32 * 144)
    (fun pW PW hKW hdivW => f12_bounded_coefficients F hF 144 pW PW hKW hdivW)
    p G a d L Z (hs.mono hq le_rfl) hL hd hbudget' P hK hloop hdiv
  exact ⟨A, { hA with card_le := hA.card_le.trans f12_terminal_budgets.2.2.2 }⟩

#print axioms f12_bounded_coefficients
#print axioms f12_terminal_budgets
#print axioms guarded_terminal_F12

#print axioms guarded_terminal_absorber_of_mass

end PaddedF12
