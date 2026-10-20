/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateAssembly
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateSupport
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateSelection
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateColumns

@[expose] public section

/-! # Linear signed certificates in the original nonextreme host

The source is an arbitrary bounded divisible physical edge set.  All auxiliary
triangles belong to the actual host.  The proof chooses an internal edge seeing
all active good roots, then an anchor and a reference column, and applies the
bounded integral incidence repair inside each physical common-neighbour graph.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks CloneSupply

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε : ℝ}

private theorem residual_nonzero_cases {A B : Type*} [DecidableEq B]
    (R : A → B → ℤ) (r : A → ℤ) (b b' : B) (a : A) (c : B)
    (h : rowResidual R r b b' a c ≠ 0) :
    R a c ≠ 0 ∨ (r a ≠ 0 ∧ (c = b ∨ c = b')) := by
  by_cases hR : R a c = 0
  · right
    constructor
    · intro hr
      exact h (by simp [rowResidual, rowCorrection, hR, hr])
    · by_contra hc
      push_neg at hc
      exact h (by simp [rowResidual, rowCorrection, vertexUnit, hR, hc.1, hc.2])
  · exact Or.inl hR

/-- The physical certificate required by the signed-hinge terminal consumer.
The only extra scalar bounds control the finite number of simultaneous root
conditions; they are independent of the number of vertices. -/
theorem signed_certificate_of_host (h : HostHyp p G α ε) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hεθ : 100 * ε ≤ θ) (hscale : 100 * θ ≤ α)
    (hn : 4096 ≤ θ * Fintype.card V) (m : ℕ)
    (hroot : ε * (10 * (m : ℝ) + 10) ≤ 1 / 100)
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset) (hPm : P.card ≤ m)
    (hDiv : IsIntDiv p F0 P) :
    ∃ k : ℕ, ∃ t : Fin k → Finset V, ∃ c : Fin k → ℤ,
      IsSignedCert p G P t c ∧ certWeight c ≤ 126 * P.card := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by nlinarith only [hn, hθ0]
  have hnN : 0 < Fintype.card V := by exact_mod_cast hnR
  obtain ⟨L, f, hL, hPeel, hLK, hFK, hInternal, hEven, hCharge⟩ :=
    peel_of_antiEdgeful p G (1 / 8) (h.antiEdgeful (by linarith))
      (by positivity) P hPG hDiv
  have hOff := peeled_off_host p G P hPG L hL f hPeel
  obtain ⟨i, hext⟩ := h.good_part
  let A := PartVertex p i
  let B := PartVertex p (other0 i)
  let R : A → B → ℤ := crossingMatrix p i f
  have hRI : matrixCost R ≤ 4 * P.card := by
    change matrixCost (crossingMatrix p i f) ≤ _
    rw [crossingMatrix_cost p i f hInternal]
    exact hFK
  have hRowEven : ∀ a : A, Even (∑ c, R a c) := by
    intro a
    change Even (∑ c, crossingMatrix p i f a c)
    rw [crossingMatrix_rowSum p i f hInternal]
    exact hEven a.val
  obtain ⟨r, hr⟩ := halfRows R hRowEven
  have hTotal : ∑ a, ∑ c, R a c = 0 := by
    change (∑ a, ∑ c, crossingMatrix p i f a c) = 0
    rw [crossingMatrix_total p i f hInternal]
    exact hCharge
  have hr0 := halfRows_sum_zero R r hr hTotal
  have hRoots : (functionRoots f).card ≤ 8 * m := by
    have hc := functionRoots_card f
    have hm : (P.card : ℤ) ≤ m := by exact_mod_cast hPm
    have hb : ((functionRoots f).card : ℤ) ≤ 8 * m := by omega
    exact_mod_cast hb
  let Rg := (functionRoots f).filter (fun u => p u = i)
  let Rb := (functionRoots f).filter (fun u => p u = other0 i)
  have hRg : Rg.card ≤ 8 * m := (card_filter_le _ _).trans hRoots
  have hRb : Rb.card ≤ 8 * m := (card_filter_le _ _).trans hRoots
  have budget (Q : Finset V) (hQ : Q.card ≤ 10 * m + 10) :
      (Q.card : ℝ) * ε ≤ 1 / 100 := by
    have hQr : (Q.card : ℝ) ≤ 10 * (m : ℝ) + 10 := by exact_mod_cast hQ
    calc
      _ ≤ (10 * (m : ℝ) + 10) * ε := mul_le_mul_of_nonneg_right hQr hε0
      _ = ε * (10 * (m : ℝ) + 10) := mul_comm _ _
      _ ≤ _ := hroot
  have hRgpart : ∀ u ∈ Rg, p u = i := fun _ hu => (mem_filter.mp hu).2
  have hRbpart : ∀ u ∈ Rb, p u = other0 i := fun _ hu => (mem_filter.mp hu).2
  have hrRoot (a : A) (ha : r a ≠ 0) : a.val ∈ Rg := by
    exact mem_filter.mpr ⟨halfRow_root p i f r hr a ha, a.property⟩
  obtain ⟨bv, bv', hbi, hb'i, hbb', hbR, hb'R⟩ :=
    exists_internal_edge_commonRoots h hε hnN (other0 i) Rg
      (fun u hu => by rw [hRgpart u hu]; exact (other0_ne i).symm)
      (budget Rg (by omega))
  let b : B := ⟨bv, hbi⟩
  let b' : B := ⟨bv', hb'i⟩
  let Kb := Rb ∪ {bv,bv'}
  have hKb : Kb.card ≤ 10 * m + 10 := by
    have hc := card_union_le Rb {bv,bv'}
    have hp : ({bv,bv'} : Finset V).card ≤ 2 := by
      simpa using (card_insert_le bv {bv'})
    change (Rb ∪ {bv,bv'}).card ≤ _
    omega
  have hKbpart : ∀ u ∈ Kb, p u = other0 i := by
    intro u hu
    rcases mem_union.mp hu with hu | hu
    · exact hRbpart u hu
    · simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
  obtain ⟨a0v, ha0i, ha0R⟩ := exists_commonRoots h hε hnN i Kb
    (fun u hu => by rw [hKbpart u hu]; exact other0_ne i) (budget Kb hKb)
  let a0 : A := ⟨a0v, ha0i⟩
  let Kg := Rg ∪ {a0v}
  have hKg : Kg.card ≤ 10 * m + 10 := by
    have hc := card_union_le Rg {a0v}
    have hp : ({a0v} : Finset V).card = 1 := card_singleton _
    change (Rg ∪ {a0v}).card ≤ _
    omega
  have hKgpart : ∀ u ∈ Kg, p u = i := by
    intro u hu
    rcases mem_union.mp hu with hu | hu
    · exact hRgpart u hu
    · have hu' : u = a0v := mem_singleton.mp hu
      exact hu' ▸ ha0i
  obtain ⟨b0, hb0i, hb0R⟩ := exists_commonRoots h hε hnN (other0 i) Kg
    (fun u hu => by rw [hKgpart u hu]; exact (other0_ne i).symm) (budget Kg hKg)
  have hRow : ∀ a : A, r a ≠ 0 → IsCopy p F0 G {a.val,b.val,b'.val} := by
    intro a ha
    apply IntegerCertificate.isCopy_of_adj (hbR a.val (hrRoot a ha))
      (hb'R a.val (hrRoot a ha)) hbb'
    rintro ⟨hm, _⟩
    exact (other0_ne i) (hbi.symm.trans (hm.symm.trans a.property))
  have hEntry (a : A) (c : B) (hac : R a c ≠ 0) :
      a.val ∈ Rg ∧ c.val ∈ Rb ∧ G.Adj a.val c.val := by
    exact ⟨mem_filter.mpr ⟨mem_functionRoots_left f a.val c.val hac, a.property⟩,
      mem_filter.mpr ⟨mem_functionRoots_right f a.val c.val hac, c.property⟩,
      crossingMatrix_adj p i G f hOff a c hac⟩
  have hResidual (a : A) (c : B) (hac : rowResidual R r b b' a c ≠ 0) :
      a.val ∈ Rg ∧ c.val ∈ Kb ∧ G.Adj a.val c.val := by
    rcases residual_nonzero_cases R r b b' a c hac with hR | ⟨hrA, hc⟩
    · obtain ⟨haR, hcR, haG⟩ := hEntry a c hR
      exact ⟨haR, mem_union_left _ hcR, haG⟩
    · have haR := hrRoot a hrA
      rcases hc with rfl | rfl
      · exact ⟨haR, mem_union_right _ (by simp [b]), hbR a.val haR⟩
      · exact ⟨haR, mem_union_right _ (by simp [b']), hb'R a.val haR⟩
  have hColumn : ∀ c : B, ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ a, rowResidual R r b b' a c *
          (physicalEdgeUnit a.val c.val e - physicalEdgeUnit a.val b0 e)) ∧
      T.cost ≤ 13 * ∑ a, |rowResidual R r b b' a c| := by
    intro c
    by_cases hz : ∀ a, rowResidual R r b b' a c = 0
    · refine ⟨[], valid_nil _, ?_, ?_⟩ <;> simp [hz]
    · push_neg at hz
      obtain ⟨a, ha⟩ := hz
      have hcKb := (hResidual a c ha).2.1
      have ha0c : G.Adj c.val a0.val := ha0R c.val hcKb
      have hb0a0 : G.Adj b0 a0.val :=
        (hb0R a0v (mem_union_right _ (mem_singleton_self _))).symm
      have hCE : Even (∑ a, rowResidual R r b b' a c) := by
        rw [rowResidual_columns R r b b' c hr0]
        change Even (∑ a, crossingMatrix p i f a c)
        rw [crossingMatrix_columnSum p i f hInternal]
        exact hEven c.val
      exact column_repair_of_host h hε0 hε θ hθ0 hθ1 hεθ hscale hn i hext
        c.val b0 c.property hb0i a0 ⟨ha0c, hb0a0⟩
        (fun a => rowResidual R r b b' a c) hCE (fun u hu => by
          obtain ⟨huR, _, huG⟩ := hResidual u c hu
          exact ⟨huG.symm, (hb0R u.val (mem_union_left _ huR)).symm⟩)
  apply signed_certificate_from_peeling p G P L R r b b' Subtype.val Subtype.val b0
    hL ?_ hLK hRI hr hTotal hRow hColumn
  intro e
  rw [crossingMatrix_evaluate p i f hInternal]
  exact hPeel e

#print axioms signed_certificate_of_host

end PartitionedTriangleAbsorption.BlowupB.F0Direct
