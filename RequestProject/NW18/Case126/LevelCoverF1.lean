/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.LevelCountsF1

@[expose] public section

/-!
# The protected `F₁` level, part 3: the protected cover outside the child

`level_of_supply_data` (proved) is the body of the consumer `F1_vortex_cover_down_of_supply`
stated for explicit data: an `F₁` packing `D₀` with no edge inside `U`, an exact leftover
`Hout ∪ Q` outside `U` and the numerical inputs of `F1_spread_level_cover_down` give an actual
`F₁`-decomposable `D ⊆ E(H)` covering every edge not inside `U`, using no edge inside `U'`, whose
edges inside `U` have maximum degree `≤ L`.

`enum_edges` / `enum_verts` index finite edge and vertex sets by `ℕ`.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption LinkPairing CrossingCover SpreadGen ApexF1
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Index a finite set of non-diagonal edges by `ℕ`. -/
theorem enum_edges (S : Finset (Sym2 V)) (hS : ∀ e ∈ S, ¬ e.IsDiag) (v0 : V) :
    ∃ x y : ℕ → V, (range S.card).image (fun i => s(x i, y i)) = S ∧
      (∀ i < S.card, x i ≠ y i) ∧
      (∀ i < S.card, ∀ j < S.card, s(x i, y i) = s(x j, y j) → i = j) ∧
      (∀ i < S.card, s(x i, y i) ∈ S) := by
  let e : ℕ → Sym2 V := fun i => if h : i < S.card then (S.equivFin.symm ⟨i, h⟩ : Sym2 V)
    else s(v0, v0)
  have he : ∀ i, s((e i).out.1, (e i).out.2) = e i := fun i => Quot.out_eq (e i)
  have hmem : ∀ i < S.card, e i ∈ S := by
    intro i hi
    simp only [e, dif_pos hi]
    exact (S.equivFin.symm ⟨i, hi⟩).2
  refine ⟨fun i => (e i).out.1, fun i => (e i).out.2, ?_, ?_, ?_, ?_⟩
  · ext f
    simp only [mem_image, mem_range, he]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hmem i hi
    · intro hf
      refine ⟨(S.equivFin ⟨f, hf⟩ : ℕ), (S.equivFin ⟨f, hf⟩).2, ?_⟩
      simp [e]
  · intro i hi heq
    have hd := hS _ (hmem i hi)
    rw [← he i] at hd
    exact hd (Sym2.mk_isDiag_iff.mpr heq)
  · intro i hi j hj hij
    have hij' : e i = e j := by rw [← he i, ← he j]; exact hij
    simp only [e, dif_pos hi, dif_pos hj] at hij'
    have := S.equivFin.symm.injective (Subtype.ext hij')
    simpa using congrArg Fin.val this
  · intro i hi; rw [he]; exact hmem i hi

omit [Fintype V] [DecidableEq V] in
/-- Index a finite vertex set by `ℕ`. -/
theorem enum_verts (S : Finset V) (v0 : V) :
    ∃ r : ℕ → V, (∀ i < S.card, ∀ j < S.card, r i = r j → i = j) ∧
      (∀ j < S.card, r j ∈ S) ∧ (∀ x ∈ S, ∃ j < S.card, r j = x) := by
  let r : ℕ → V := fun i => if h : i < S.card then (S.equivFin.symm ⟨i, h⟩ : V) else v0
  refine ⟨r, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    simp only [r, dif_pos hi, dif_pos hj] at hij
    have := S.equivFin.symm.injective (Subtype.ext hij)
    simpa using congrArg Fin.val this
  · intro j hj; simp only [r, dif_pos hj]; exact (S.equivFin.symm ⟨j, hj⟩).2
  · intro x hx
    refine ⟨(S.equivFin ⟨x, hx⟩ : ℕ), (S.equivFin ⟨x, hx⟩).2, ?_⟩
    simp [r]

/-- **Assembly of one protected level from explicit supply data** (proved; the body of the
consumer `F1_vortex_cover_down_of_supply`). -/
theorem level_of_supply_data (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (U U' : Finset V) (hU'U : U' ⊆ U)
    (hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) (hHG : H ≤ G)
    (hdiv : IsIntDiv p F1 H.edgeFinset)
    (D₀ : Finset (Sym2 V)) (k : ℕ) (x y : ℕ → V) (kr : ℕ) (r : ℕ → V)
    (Q R : Finset (Sym2 V)) (s γ β' γ₀ K B ω L : ℕ)
    (hD₀H : D₀ ⊆ H.edgeFinset) (hD₀dec : HasDecomp p F1 D₀) (hD₀U : ∀ e ∈ D₀, ¬ ∀ v ∈ e, v ∈ U)
    (hLH : (range k).image (fun i => s(x i, y i)) ∪ Q ⊆ H.edgeFinset)
    (hLD₀ : Disjoint ((range k).image (fun i => s(x i, y i)) ∪ Q) D₀)
    (hleft : ∀ e ∈ H.edgeFinset, (¬ ∀ v ∈ e, v ∈ U) → e ∉ D₀ →
      e ∈ (range k).image (fun i => s(x i, y i)) ∪ Q)
    (hRH : R ⊆ H.edgeFinset) (hRU : ∀ e ∈ R, ∀ v ∈ e, v ∈ U) (hRU' : ∀ e ∈ R, ¬ ∀ v ∈ e, v ∈ U')
    (hxy : ∀ i < k, x i ≠ y i)
    (hinj : ∀ i < k, ∀ j < k, s(x i, y i) = s(x j, y j) → i = j)
    (hxU : ∀ i < k, x i ∉ U) (hyU : ∀ i < k, y i ∉ U)
    (hdegH : ∀ v, ((range k).filter (fun i => v = x i ∨ v = y i)).card ≤ γ)
    (hsup : ∀ i < k, s ≤ (U.filter (fun z => s(x i, z) ∈ Q ∧ s(y i, z) ∈ Q ∧
      ({p (x i), p (y i), p z} : Multiset (Fin 4)) ∈ F1)).card)
    (hβ' : 0 < β') (hs : 2 * γ + k / β' < s)
    (hQ : ∀ e ∈ Q, ∃ j < kr, ∃ u ∈ U, e = s(r j, u))
    (hr : ∀ i < kr, ∀ j < kr, r i = r j → i = j)
    (hrU : ∀ j < kr, r j ∉ U)
    (hK : 0 < K)
    (hdense : ∀ j < kr, ∀ v ∈ tgt U Q (r j), ∀ c : Fin 4, LinkPair (p (r j)) (p v) c →
      ((tgt U Q (r j)).filter fun z => p z = c ∧ ¬ (z ≠ v ∧ s(v, z) ∈ R)).card ≤ γ₀)
    (hmarg : ∀ j < kr, MarginsSlack p (p (r j)) (tgt U Q (r j)) (γ₀ + (B + K)) γ)
    (hover : ∀ i < kr, ∀ j < kr, i ≠ j → ((tgt U Q (r i)) ∩ (tgt U Q (r j))).card ≤ ω)
    (hload : ∀ v, visits (fun j => tgt U Q (r j)) kr v ≤ L)
    (hB : (Real.exp 1 - 1) * ω * L / K +
      Real.log (∑ j ∈ range kr, ((tgt U Q (r j)).card : ℝ)) ≤ B) :
    ∃ D ⊆ H.edgeFinset, HasDecomp p F1 D ∧
      (∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) ∧
      (∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ U') ∧
      ∀ v, ((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card ≤ L := by
  classical
  set Hout := (range k).image (fun i => s(x i, y i)) with hHout
  have hloopH : ∀ e ∈ H.edgeFinset, ¬ e.IsDiag := fun e he =>
    H.not_isDiag_of_mem_edgeFinset he
  have hpar : ∀ j < kr, Even (deg (Hout ∪ Q) (r j)) := by
    intro j hj
    have hH : Even (deg H.edgeFinset (r j)) := by
      rw [deg_eq_card_nbrs]
      exact F1_degree_even_of_intDiv p _ hloopH hdiv (r j)
    have hD : Even (deg D₀ (r j)) := even_deg_of_hasDecomp hD₀dec (r j)
    have hsplit : H.edgeFinset.filter (fun e => r j ∈ e) =
        D₀.filter (fun e => r j ∈ e) ∪ (Hout ∪ Q).filter (fun e => r j ∈ e) := by
      ext e
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨he, hre⟩
        by_cases heD : e ∈ D₀
        · exact Or.inl ⟨heD, hre⟩
        · exact Or.inr ⟨mem_union.mp (hleft e he (fun hall => hrU j hj (hall _ hre)) heD), hre⟩
      · rintro (⟨he, hre⟩ | ⟨he, hre⟩)
        · exact ⟨hD₀H he, hre⟩
        · exact ⟨hLH (mem_union.mpr he), hre⟩
    have hcount : deg H.edgeFinset (r j) = deg D₀ (r j) + deg (Hout ∪ Q) (r j) := by
      unfold deg
      rw [hsplit, card_union_of_disjoint (disjoint_filter_filter hLD₀.symm)]
    rw [hcount] at hH
    exact (Nat.even_add.mp hH).mp hD
  have hcls : ∀ j < kr, ∀ u ∈ tgt U Q (r j),
      p u = p (r j) ∨ p u = partner1 (p (r j)) ∨ p u = partner2 (p (r j)) := by
    intro j _ u hu
    have hQe : s(r j, u) ∈ Q := (mem_filter.mp hu).2
    have hHe : H.Adj (r j) u := SimpleGraph.mem_edgeFinset.mp (hLH (mem_union_right _ hQe))
    exact allowed_F1_classes _ _ (hGF _ _ (hHG hHe))
  obtain ⟨M, hMR, hMdeg, hMdec⟩ := F1_spread_level_cover_down p U Q R k x y kr r s γ β' γ₀ K B ω L
    hxy hinj hxU hyU hdegH hsup hβ' hs hQ hr hrU hpar hRU hK hcls hdense hmarg hover hload hB
  refine ⟨D₀ ∪ (Hout ∪ Q ∪ M), ?_, ?_, ?_, ?_, ?_⟩
  · exact union_subset hD₀H (union_subset hLH (hMR.trans hRH))
  · refine hD₀dec.union hMdec ?_
    rw [disjoint_union_right]
    refine ⟨hLD₀.symm, ?_⟩
    rw [disjoint_left]
    intro e heD heM
    exact hD₀U e heD (hRU e (hMR heM))
  · intro e he hne v hv
    by_contra hvU
    have hnot : ¬ ∀ w ∈ e, w ∈ U := fun hall => hvU (hall v hv)
    by_cases heD : e ∈ D₀
    · exact hne (mem_union_left _ heD)
    · exact hne (mem_union_right _ (mem_union_left _ (hleft e he hnot heD)))
  · intro e he hall
    rcases mem_union.mp he with heD | he
    · exact hD₀U e heD (fun v hv => hU'U (hall v hv))
    rcases mem_union.mp he with heL | heM
    · rcases mem_union.mp heL with heH | heQ
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp heH
        exact hxU i (mem_range.mp hi) (hU'U (hall _ (Sym2.mem_mk_left _ _)))
      · obtain ⟨j, hj, u, -, rfl⟩ := hQ e heQ
        exact hrU j hj (hU'U (hall _ (Sym2.mem_mk_left _ _)))
    · exact hRU' e (hMR heM) hall
  · intro v
    have hsub : ((D₀ ∪ (Hout ∪ Q ∪ M)).filter fun e => ∀ w ∈ e, w ∈ U).filter (fun e => v ∈ e)
        ⊆ M.filter (fun e => v ∈ e) := by
      intro e he
      simp only [mem_filter, mem_union] at he ⊢
      obtain ⟨⟨he, hall⟩, hve⟩ := he
      refine ⟨?_, hve⟩
      rcases he with heD | (heH | heQ) | heM
      · exact absurd hall (hD₀U e heD)
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp heH
        exact absurd (hall _ (Sym2.mem_mk_left _ _)) (hxU i (mem_range.mp hi))
      · obtain ⟨j, hj, u, -, rfl⟩ := hQ e heQ
        exact absurd (hall _ (Sym2.mem_mk_left _ _)) (hrU j hj)
      · exact heM
    exact (card_le_card hsub).trans (hMdeg v)

end NashWilliams18.SpreadF1
