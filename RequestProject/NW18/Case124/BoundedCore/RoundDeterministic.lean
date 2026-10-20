/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.BoundedCore.RoundAssembly
import RequestProject.NW18.Case124.BoundedCore.CrossResK3
import RequestProject.NW18.Case124.BoundedCore.RoundTargetAssembly
import RequestProject.NW18.Case124.BoundedCore.RoundGeometry
import RequestProject.NW18.Case124.BoundedCore.ReserveTypicality
import RequestProject.NW18.Case124.BoundedCore.ApexIncidence
import RequestProject.NW18.Case124.ReserveCover.Greedy

/-!
# One protected round from a concrete sample, packing and leftover bound

`round_of_sample` (deterministic): on a whole vertex type, given

* a good radial reserve `Res` (the output of `SpreadK3.crossResK3_exists`) for the roots outside
  `W`, the interior `W \ Z` and the available edges `E(G) \ F`;
* a triangle-decomposable packing `Ep` of the protected graph
  `(E(G) \ F) \ (E(G[W]) ∪ Res)` whose leftover has maximum degree at most `D`;
* explicit numerical budgets (natural numbers `γ₀ B K ω Lv M Kg` with real inequalities in terms of
  `|V|`, `|W|`, `|Z|`, `ρ`, `ε`, `θ`, `κ`, `D`),

the greedy apex cover (`ReserveCover.greedy_apex_cover`), the target budgets
(`round_target_degree_budgets`) and the deterministic assembly (`round_cover_assembly`) produce
the round output `Q`.  Every input of `round_cover_assembly` is derived here from the sample and
the graph hypotheses.
-/

namespace NashWilliams18.Case124.BoundedCore

open Finset PartitionedTriangleAbsorption NashWilliams18

variable {V : Type} [Fintype V] [DecidableEq V]

lemma mem_EH_iff {G : SimpleGraph V} [DecidableRel G.Adj] {F : Finset (Sym2 V)} {x z : V} :
    s(x, z) ∈ G.edgeFinset \ F ↔ G.Adj x z ∧ s(x, z) ∉ F := by
  simp [mem_sdiff, SimpleGraph.mem_edgeFinset]

omit [Fintype V] in
/-- Reserve neighbourhood of a root, rewritten as a sampled candidate set. -/
lemma reserve_nbhd_eq {EH Res : Finset (Sym2 V)} {X S W : Finset V}
    (hsub : Res ⊆ EH) (hcross : ∀ e ∈ Res, ∃ x ∈ X, ∃ z ∈ S, e = s(x, z))
    (hSW : S ⊆ W) {x : V} (hx : x ∉ W) :
    W.filter (fun z => s(x, z) ∈ Res) = S.filter (fun z => s(x, z) ∈ EH ∧ s(x, z) ∈ Res) := by
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨hzW, hR⟩
    obtain ⟨a, ha, b, hb, he⟩ := hcross _ hR
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hb, hsub hR, hR⟩
    · exact absurd (hSW hb) hx
  · rintro ⟨hzS, -, hR⟩
    exact ⟨hSW hzS, hR⟩

omit [Fintype V] in
/-- Reserved roots at an interior vertex, rewritten as a sampled set. -/
lemma reserve_load_eq {EH Res : Finset (Sym2 V)} {X : Finset V}
    (hsub : Res ⊆ EH) (v : V) :
    X.filter (fun x => s(x, v) ∈ Res) = X.filter (fun x => s(x, v) ∈ EH ∧ s(x, v) ∈ Res) := by
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hx, hR⟩; exact ⟨hx, hsub hR, hR⟩
  · rintro ⟨hx, -, hR⟩; exact ⟨hx, hR⟩

omit [Fintype V] in
lemma reserve_load_zero {Res : Finset (Sym2 V)} {X S : Finset V}
    (hcross : ∀ e ∈ Res, ∃ x ∈ X, ∃ z ∈ S, e = s(x, z))
    {v : V} (hvS : v ∉ S) (hvX : v ∉ X) (Y : Finset V) :
    Y.filter (fun x => s(x, v) ∈ Res) = ∅ := by
  rw [filter_eq_empty_iff]
  intro x _ hR
  obtain ⟨a, ha, b, hb, he⟩ := hcross _ hR
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hvS hb
  · exact hvX ha

omit [Fintype V] in
/-- The degree of the reserve at a vertex is bounded by its reserved neighbourhood. -/
lemma reserve_degree_le_root {Res : Finset (Sym2 V)} {X S : Finset V}
    (hcross : ∀ e ∈ Res, ∃ x ∈ X, ∃ z ∈ S, e = s(x, z)) (hXS : Disjoint X S)
    {v : V} (hv : v ∈ X) :
    (Res.filter (fun e => v ∈ e)).card ≤ (S.filter (fun z => s(v, z) ∈ Res)).card := by
  have hsub : Res.filter (fun e => v ∈ e) ⊆
      (S.filter (fun z => s(v, z) ∈ Res)).image (fun z => s(v, z)) := by
    intro e he
    obtain ⟨hR, hve⟩ := mem_filter.mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := hcross _ hR
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact mem_image.mpr ⟨b, mem_filter.mpr ⟨hb, hR⟩, rfl⟩
    · exact absurd hb (disjoint_left.mp hXS hv)
  exact (card_le_card hsub).trans card_image_le

omit [Fintype V] in
lemma reserve_degree_le_interior {Res : Finset (Sym2 V)} {X S : Finset V}
    (hcross : ∀ e ∈ Res, ∃ x ∈ X, ∃ z ∈ S, e = s(x, z)) (hXS : Disjoint X S)
    {v : V} (hv : v ∈ S) :
    (Res.filter (fun e => v ∈ e)).card ≤ (X.filter (fun x => s(x, v) ∈ Res)).card := by
  have hsub : Res.filter (fun e => v ∈ e) ⊆
      (X.filter (fun x => s(x, v) ∈ Res)).image (fun x => s(x, v)) := by
    intro e he
    obtain ⟨hR, hve⟩ := mem_filter.mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := hcross _ hR
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact absurd hv (disjoint_left.mp hXS ha)
    · exact mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, hR⟩, rfl⟩
  exact (card_le_card hsub).trans card_image_le

/-- **Reserve degree bound** from the sampler monitors k1 and k4. -/
theorem reserve_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj] (EH : Finset (Sym2 V))
    (W Z : Finset V) (Res : Finset (Sym2 V)) (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hgood : SpreadK3.CrossResK3Good G EH (univ \ W) (W \ Z) Res ρ ε) (v : V) :
    ((Res.filter (fun e => v ∈ e)).card : ℝ) ≤ ρ * Fintype.card V + ε * Fintype.card V := by
  have hXS : Disjoint (univ \ W) (W \ Z) := by
    rw [disjoint_left]; intro a ha hb; exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  have hn0 : (0 : ℝ) ≤ ε * Fintype.card V := by positivity
  by_cases hvX : v ∈ univ \ W
  · have h1 := reserve_degree_le_root hgood.cross hXS hvX
    have heq : (W \ Z).filter (fun z => s(v, z) ∈ Res) =
        (W \ Z).filter (fun z => s(v, z) ∈ EH ∧ s(v, z) ∈ Res) := by
      ext z; simp only [mem_filter]
      constructor
      · rintro ⟨h, hR⟩; exact ⟨h, hgood.sub hR, hR⟩
      · rintro ⟨h, -, hR⟩; exact ⟨h, hR⟩
    rw [heq] at h1
    have hk1 := (abs_le.mp (hgood.k1 v hvX)).2
    have hC : (((W \ Z).filter fun z => s(v, z) ∈ EH).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast card_le_univ _
    have : ((Res.filter (fun e => v ∈ e)).card : ℝ) ≤
        (((W \ Z).filter fun z => s(v, z) ∈ EH ∧ s(v, z) ∈ Res).card : ℝ) := by exact_mod_cast h1
    nlinarith
  · by_cases hvS : v ∈ W \ Z
    · have h1 := reserve_degree_le_interior hgood.cross hXS hvS
      rw [reserve_load_eq hgood.sub v] at h1
      have hk4 := (abs_le.mp (hgood.k4 v hvS)).2
      have hC : (((univ \ W).filter fun x => s(x, v) ∈ EH).card : ℝ) ≤ Fintype.card V := by
        exact_mod_cast card_le_univ _
      have : ((Res.filter (fun e => v ∈ e)).card : ℝ) ≤
          (((univ \ W).filter fun x => s(x, v) ∈ EH ∧ s(x, v) ∈ Res).card : ℝ) := by
        exact_mod_cast h1
      nlinarith
    · have : Res.filter (fun e => v ∈ e) = ∅ := by
        rw [filter_eq_empty_iff]
        intro e hR hve
        obtain ⟨a, ha, b, hb, rfl⟩ := hgood.cross _ hR
        rcases Sym2.mem_iff.mp hve with rfl | rfl
        · exact hvX ha
        · exact hvS hb
      rw [this, card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ ρ * Fintype.card V := by positivity
      linarith


/-- Candidate count of a root: at least its child degree minus `|Z|` and its damage degree. -/
lemma root_candidates_ge (G : SimpleGraph V) [DecidableRel G.Adj] (W Z : Finset V)
    (F : Finset (Sym2 V)) (x : V) :
    ((W.filter (G.Adj x)).card : ℝ) ≤
      (((W \ Z).filter fun z => s(x, z) ∈ G.edgeFinset \ F).card : ℝ) + Z.card +
        (F.filter (fun e => x ∈ e)).card := by
  have h := root_candidate_count G W Z F x
  have heq : (W \ Z).filter (fun z => G.Adj x z ∧ s(x, z) ∉ F) =
      (W \ Z).filter (fun z => s(x, z) ∈ G.edgeFinset \ F) := by
    ext z; simp only [mem_filter, mem_EH_iff]
  rw [heq] at h
  exact_mod_cast h

/-- **Deterministic protected round from a concrete sample.** -/
theorem round_of_sample (G : SimpleGraph V) [DecidableRel G.Adj] (W Z : Finset V)
    (F Res Ep : Finset (Sym2 V)) (ρ ε θ κ κW : ℝ) (D γ₀ B K ω Lv M Kg : ℕ)
    (hZW : Z ⊆ W) (hFW : Disjoint F (insideEdges G W))
    (hFdeg : ∀ v, ((F.filter (fun e => v ∈ e)).card : ℝ) ≤ κ * Fintype.card V)
    (hpar : ∀ v, (3 / 4 - θ) * (W.card : ℝ) ≤ ((W.filter (G.Adj v)).card : ℝ))
    (heven : ∀ x, x ∉ W → Even (((G.edgeFinset \ F).filter fun e => x ∈ e).card))
    (hgood : SpreadK3.CrossResK3Good G (G.edgeFinset \ F) (univ \ W) (W \ Z) Res ρ ε)
    (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hEp : HasDecomp onePart K3fam Ep)
    (hEpsub : Ep ⊆ ((G.edgeFinset \ F) \ insideEdges G W) \ Res)
    (hD : ∀ v, (((((G.edgeFinset \ F) \ insideEdges G W) \ Res) \ Ep).filter
      (fun e => v ∈ e)).card ≤ D)
    (hγ : ρ * (1 / 4 + θ) * W.card + 2 * (ε * Fintype.card V) + D + 1 ≤ γ₀)
    (hmarg : 2 * ((γ₀ : ℝ) + B + K) ≤
      ρ * ((3 / 4 - θ) * W.card - Z.card - κ * Fintype.card V) - ε * Fintype.card V - D)
    (hω : ρ ^ 2 * W.card + ε * Fintype.card V + 2 * D ≤ ω)
    (hL : ρ * Fintype.card V + ε * Fintype.card V + D ≤ Lv)
    (hLκ : (Lv : ℝ) ≤ κW)
    (hK : 0 < K)
    (hB : (Real.exp 1 - 1) * ω * Lv / K + 2 * Real.log (Fintype.card V) ≤ B)
    (hM : (M : ℝ) ≤
      ρ ^ 2 * ((1 / 2 - 2 * θ) * W.card - 2 * Z.card - 2 * (κ * Fintype.card V)) -
        ε * Fintype.card V)
    (hKg : 3 * (Fintype.card V * D) + 12 * (Kg * (Kg + D)) < 2 * (Kg * M)) :
    ∃ Q ⊆ G.edgeFinset \ F, HasDecomp onePart K3fam Q ∧
      ((G.edgeFinset \ F) \ insideEdges G W) ⊆ Q ∧ Disjoint Q (insideEdges G Z) ∧
      DegBounded (Q ∩ insideEdges G W) κW := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set u : ℝ := (W.card : ℝ) with hu
  set EH := G.edgeFinset \ F with hEH
  set avail := EH \ insideEdges G W with havail
  set X := univ \ W with hX
  set S := W \ Z with hS
  have hXS : Disjoint X S := by
    rw [disjoint_left]; intro a ha hb; exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  have hXW : Disjoint X W := by
    rw [disjoint_left]; intro a ha hb; exact (mem_sdiff.mp ha).2 hb
  have hSW : S ⊆ W := sdiff_subset
  have hmemX : ∀ {x}, x ∉ W → x ∈ X := fun hx => mem_sdiff.mpr ⟨mem_univ _, hx⟩
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hεn : 0 ≤ ε * n := mul_nonneg hε hn0
  -- reserve facts
  have hResEH : Res ⊆ EH := hgood.sub
  have hResW : ∀ e ∈ Res, e ∉ insideEdges G W := by
    intro e he hin
    obtain ⟨x, hx, z, -, rfl⟩ := hgood.cross e he
    exact (mem_sdiff.mp hx).2 (mem_of_mem_insideEdges hin (Sym2.mem_mk_left _ _))
  have hResav : Res ⊆ avail := fun e he => mem_sdiff.mpr ⟨hResEH he, hResW e he⟩
  have hRescross : ∀ e ∈ Res, ∃ x, x ∉ W ∧ ∃ z ∈ W \ Z, e = s(x, z) := by
    intro e he
    obtain ⟨x, hx, z, hz, rfl⟩ := hgood.cross e he
    exact ⟨x, (mem_sdiff.mp hx).2, z, hz, rfl⟩
  have hRescross' : ∀ e ∈ Res, ∃ x, x ∉ W ∧ ∃ z ∈ W, e = s(x, z) := by
    intro e he
    obtain ⟨x, hx, z, hz, rfl⟩ := hRescross e he
    exact ⟨x, hx, z, hSW hz, rfl⟩
  have hEpRes : Disjoint Res Ep := by
    rw [disjoint_left]; intro e hR hE; exact (mem_sdiff.mp (hEpsub hE)).2 hR
  have hEdiag : ∀ e ∈ EH, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1)
  -- the leftover with both ends outside `W`
  set L := ((avail \ Res) \ Ep).filter (fun e => ∀ v ∈ e, v ∉ W) with hLdef
  have hLsub : L ⊆ (avail \ Res) \ Ep := filter_subset _ _
  have hLEH : L ⊆ EH := fun e he => (mem_sdiff.mp (mem_sdiff.mp (mem_sdiff.mp (hLsub he)).1).1).1
  have hLRes : Disjoint L Res := by
    rw [disjoint_left]; intro e hL hR
    exact (mem_sdiff.mp (mem_sdiff.mp (hLsub hL)).1).2 hR
  have hLD : ∀ v, (L.filter (fun e => v ∈ e)).card ≤ D := fun v =>
    (card_le_card (filter_subset_filter _ hLsub)).trans (hD v)
  have hLcard : 2 * L.card ≤ Fintype.card V * D :=
    twice_leftover_card_le L (fun e he => hEdiag e (hLEH he)) D hLD
  -- common reserve apexes of a leftover edge
  have hCge : ∀ x, x ∉ W → (3 / 4 - θ) * u - Z.card - κ * n ≤
      ((S.filter fun z => s(x, z) ∈ EH).card : ℝ) := by
    intro x hx
    have h1 := root_candidates_ge G W Z F x
    have h2 := hpar x
    have h3 := hFdeg x
    linarith
  have hSu : (S.card : ℝ) ≤ u := by rw [hu]; exact_mod_cast card_le_card hSW
  have hM' : ∀ x y, s(x, y) ∈ L →
      M ≤ (univ.filter fun z => s(x, z) ∈ Res ∧ s(y, z) ∈ Res).card := by
    intro x y hxy
    have hxW : x ∉ W := (mem_filter.mp hxy).2 x (Sym2.mem_mk_left _ _)
    have hyW : y ∉ W := (mem_filter.mp hxy).2 y (Sym2.mem_mk_right _ _)
    have hne : x ≠ y := by
      intro h; subst h; exact hEdiag _ (hLEH hxy) (Sym2.mk_isDiag_iff.mpr rfl)
    have hk3 := (abs_le.mp (hgood.k3 x (hmemX hxW) y (hmemX hyW) hne)).1
    have hinter : (((S.filter fun z => s(x, z) ∈ EH).card : ℝ)) +
        ((S.filter fun z => s(y, z) ∈ EH).card : ℝ) ≤
        S.card + ((S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH).card : ℝ) := by
      have h := card_union_add_card_inter (S.filter fun z => s(x, z) ∈ EH)
        (S.filter fun z => s(y, z) ∈ EH)
      rw [← filter_and, ← filter_or] at h
      have h2 : (S.filter fun z => s(x, z) ∈ EH ∨ s(y, z) ∈ EH).card ≤ S.card :=
        card_filter_le _ _
      exact_mod_cast (show _ ≤ _ by omega)
    have hcx := hCge x hxW
    have hcy := hCge y hyW
    have hsub : (S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH ∧ s(x, z) ∈ Res ∧
        s(y, z) ∈ Res) ⊆ univ.filter fun z => s(x, z) ∈ Res ∧ s(y, z) ∈ Res := by
      intro z hz
      obtain ⟨-, -, -, h1, h2⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_univ _, h1, h2⟩
    have hsubR : ((S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH ∧ s(x, z) ∈ Res ∧
        s(y, z) ∈ Res).card : ℝ) ≤
        ((univ.filter fun z => s(x, z) ∈ Res ∧ s(y, z) ∈ Res).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    have hcom : (1 / 2 - 2 * θ) * u - 2 * Z.card - 2 * (κ * n) ≤
        ((S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH).card : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left hcom hρ2
    exact_mod_cast (show (M : ℝ) ≤
      ((univ.filter fun z => s(x, z) ∈ Res ∧ s(y, z) ∈ Res).card : ℝ) by linarith)
  have hKg' : 3 * L.card + 6 * Kg * (Kg + D) < Kg * M := by
    have e1 : 6 * Kg * (Kg + D) = 6 * (Kg * (Kg + D)) := by ring
    rw [e1]
    generalize Kg * (Kg + D) = P at hKg ⊢
    generalize Kg * M = Qm at hKg ⊢
    generalize Fintype.card V * D = R at hKg hLcard
    omega
  obtain ⟨T, hT3, hTdisj, hTcov, hTsub⟩ := ReserveCover.greedy_apex_cover L Res hLRes
    (fun e he => hEdiag e (hLEH he)) (fun e he => hEdiag e (hResEH he)) D Kg M hLD hM' hKg'
  set Ta := T.biUnion triEdges with hTa
  have hTadec : HasDecomp onePart K3fam Ta :=
    ⟨T, fun t ht => ⟨hT3 t ht, by rw [map_onePart (hT3 t ht)]; exact mem_singleton_self _⟩,
      hTdisj, rfl⟩
  -- target budgets
  have hsd : avail \ (Res ∪ Ep) = (avail \ Res) \ Ep := by
    ext e; simp only [mem_sdiff, mem_union, not_or, and_assoc]
  have hD' : ∀ v, ((avail \ (Res ∪ Ep)).filter (fun e => v ∈ e)).card ≤ D := by
    intro v; rw [hsd]; exact hD v
  have hLsub' : L ⊆ avail \ (Res ∪ Ep) := by rw [hsd]; exact hLsub
  obtain ⟨hdiff, hinv⟩ := round_target_degree_budgets W X avail L Res Ep D
    (fun e he => (mem_filter.mp he).2) hLsub' hRescross' hResav hEpRes T hT3 hTdisj hTsub hD'
  -- notation for the targets
  set Tg : V → Finset V := fun x => W.filter (fun z => s(x, z) ∈ avail \ (Ep ∪ Ta)) with hTg
  set Rx : V → Finset V := fun x => W.filter (fun z => s(x, z) ∈ Res) with hRx
  have hRxeq : ∀ x, x ∉ W → Rx x = S.filter (fun z => s(x, z) ∈ EH ∧ s(x, z) ∈ Res) :=
    fun x hx => reserve_nbhd_eq hResEH hgood.cross hSW hx
  have hRxS : ∀ x, x ∉ W → Rx x ⊆ S := by
    intro x hx z hz; rw [hRxeq x hx] at hz; exact (mem_filter.mp hz).1
  have hRxsize : ∀ x, x ∉ W →
      |((Rx x).card : ℝ) - ρ * (S.filter fun z => s(x, z) ∈ EH).card| ≤ ε * n := by
    intro x hx; rw [hRxeq x hx]; exact hgood.k1 x (hmemX hx)
  have hTlow : ∀ x, x ∉ W →
      ρ * ((3 / 4 - θ) * u - Z.card - κ * n) - ε * n - D ≤ ((Tg x).card : ℝ) := by
    intro x hx
    have h1 := card_reserve_le (Tg x) (Rx x) D (hdiff x hx).1
    have h1' : ((Rx x).card : ℝ) ≤ (Tg x).card + D := by exact_mod_cast h1
    have h2 := (abs_le.mp (hRxsize x hx)).1
    have h3 := mul_le_mul_of_nonneg_left (hCge x hx) hρ
    linarith
  -- assembly
  refine round_cover_assembly G W Z F Res Ep Ta γ₀ K B ω Lv κW hZW hFW hEp ?_ hResEH hRescross
    hTadec ?_ ?_ heven hK ?_ ?_ ?_ ?_ ?_ hLκ
  · -- packing support
    intro e he
    have h := hEpsub he
    refine mem_sdiff.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp h).1).1, ?_⟩
    rw [mem_union, not_or]
    exact ⟨(mem_sdiff.mp h).2, (mem_sdiff.mp (mem_sdiff.mp h).1).2⟩
  · -- apex cover support
    intro e he
    rcases mem_union.mp (hTsub he) with h | h
    · refine mem_union_left _ ?_
      have h' := hLsub h
      obtain ⟨h1, h2⟩ := mem_sdiff.mp h'
      obtain ⟨h3, h4⟩ := mem_sdiff.mp h1
      obtain ⟨h5, h6⟩ := mem_sdiff.mp h3
      refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨h5, ?_⟩, h2⟩
      rw [mem_union, not_or]
      exact ⟨h4, h6⟩
    · exact mem_union_right _ h
  · -- apex cover covers the exterior leftover
    intro e he hext
    apply hTcov
    refine mem_filter.mpr ⟨?_, hext⟩
    obtain ⟨he1, he2⟩ := mem_sdiff.mp he
    obtain ⟨he3, he4⟩ := mem_sdiff.mp he1
    rw [mem_union, not_or] at he4
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨he3, he4.2⟩, he4.1⟩, he2⟩
  · -- density inside a target
    intro x hx y hy
    have hbad : ((Tg x).filter fun z => ¬ (z ≠ y ∧ s(y, z) ∈ insideEdges G W \ insideEdges G Z))
        ⊆ {y} ∪ ((Tg x \ Rx x) ∪ (Rx x).filter (fun z => ¬ G.Adj y z)) := by
      intro z hz
      obtain ⟨hzT, hzbad⟩ := mem_filter.mp hz
      by_cases hzy : z = y
      · exact mem_union_left _ (mem_singleton.mpr hzy)
      refine mem_union_right _ ?_
      by_cases hzR : z ∈ Rx x
      · refine mem_union_right _ (mem_filter.mpr ⟨hzR, fun hadj => hzbad ⟨hzy, ?_⟩⟩)
        have hzS := hRxS x hx hzR
        have hyW : y ∈ W := (mem_filter.mp hy).1
        refine mem_sdiff.mpr ⟨?_, fun hin => (mem_sdiff.mp hzS).2
          (mem_of_mem_insideEdges hin (Sym2.mem_mk_right _ _))⟩
        rw [insideEdges, mem_inter, triEdges, mem_filter, Finset.mk_mem_sym2_iff]
        exact ⟨SimpleGraph.mem_edgeFinset.mpr hadj, ⟨hyW, hSW hzS⟩, by
          simpa [Sym2.mk_isDiag_iff] using fun h => hzy h.symm⟩
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hzT, hzR⟩)
    have h1 := (card_le_card hbad).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
    rw [card_singleton] at h1
    have h2 := (hdiff x hx).2
    -- sampled defect
    have hdef := sampled_defect_bound (S.filter fun z => s(x, z) ∈ EH) (Rx x) (G.Adj y) ρ (ε * n)
      (hRxsize x hx) (by
        have := hgood.k2 x (hmemX hx) y
        rw [hRxeq x hx, filter_filter, filter_filter]
        convert this using 4
        · congr 1; ext z; simp only [mem_filter]; tauto)
    have hnon : ((S.filter fun z => s(x, z) ∈ EH).filter (fun z => ¬ G.Adj y z)).card ≤
        W.card - (W.filter (G.Adj y)).card := by
      rw [← card_sdiff_of_subset (filter_subset _ _)]
      refine card_le_card ?_
      intro z hz
      obtain ⟨hz1, hz2⟩ := mem_filter.mp hz
      exact mem_sdiff.mpr ⟨hSW (mem_filter.mp hz1).1, fun h => hz2 (mem_filter.mp h).2⟩
    have hWy : (W.filter (G.Adj y)).card ≤ W.card := card_filter_le _ _
    have hnon' : (((S.filter fun z => s(x, z) ∈ EH).filter (fun z => ¬ G.Adj y z)).card : ℝ) ≤
        u - (W.filter (G.Adj y)).card := by
      have := Nat.cast_le (α := ℝ) |>.mpr hnon
      rw [Nat.cast_sub hWy] at this
      exact this
    have hpy := hpar y
    have h3 := mul_le_mul_of_nonneg_left hnon' hρ
    have h1' : (((Tg x).filter fun z => ¬ (z ≠ y ∧ s(y, z) ∈ insideEdges G W \
        insideEdges G Z)).card : ℝ) ≤ 1 + (D + ((Rx x).filter (fun z => ¬ G.Adj y z)).card) := by
      have : (((Tg x).filter fun z => ¬ (z ≠ y ∧ s(y, z) ∈ insideEdges G W \
          insideEdges G Z)).card : ℝ) ≤ 1 + ((Tg x \ Rx x).card +
            ((Rx x).filter (fun z => ¬ G.Adj y z)).card) := by exact_mod_cast h1
      have h2' : ((Tg x \ Rx x).card : ℝ) ≤ D := by exact_mod_cast h2
      linarith
    have : (((Tg x).filter fun z => ¬ (z ≠ y ∧ s(y, z) ∈ insideEdges G W \
        insideEdges G Z)).card : ℝ) ≤ γ₀ := by nlinarith
    exact_mod_cast this
  · -- Dirac margin
    intro x hx
    have h := hTlow x hx
    have h2 : 2 * (γ₀ + (B + K)) ≤ (Tg x).card := by
      have : (2 * ((γ₀ : ℝ) + (B + K))) ≤ (Tg x).card := by linarith
      exact_mod_cast this
    show γ₀ + (B + K) + (Tg x).card / 2 ≤ (Tg x).card
    omega
  · -- overlaps
    intro x hx y hy hxy
    have h1 := target_overlap_le (Tg x) (Tg y) (Rx x) (Rx y) D (hdiff x hx).2 (hdiff y hy).2
    have hRR : Rx x ∩ Rx y = S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH ∧ s(x, z) ∈ Res ∧
        s(y, z) ∈ Res := by
      rw [hRxeq x hx, hRxeq y hy, ← filter_and]
      congr 1; ext z; tauto
    rw [hRR] at h1
    have hk3 := (abs_le.mp (hgood.k3 x (hmemX hx) y (hmemX hy) hxy)).2
    have hc : ((S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH).card : ℝ) ≤ u :=
      (by exact_mod_cast card_filter_le _ _ : ((S.filter fun z => s(x, z) ∈ EH ∧
        s(y, z) ∈ EH).card : ℝ) ≤ S.card).trans hSu
    have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    have h3 := mul_le_mul_of_nonneg_left hc hρ2
    have h1' : (((Tg x) ∩ (Tg y)).card : ℝ) ≤ ((S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH ∧
        s(x, z) ∈ Res ∧ s(y, z) ∈ Res).card : ℝ) + 2 * D := by exact_mod_cast h1
    have : (((Tg x) ∩ (Tg y)).card : ℝ) ≤ ω := by linarith
    exact_mod_cast this
  · -- inverse load
    intro v
    by_cases hvW : v ∈ W
    · have heq : (univ \ W).filter (fun x => s(x, v) ∈ avail \ (Ep ∪ Ta) ∧ v ∈ W) =
          X.filter (fun x => s(x, v) ∈ avail \ (Ep ∪ Ta)) := by
        ext x; simp [hvW, hX]
      rw [heq]
      have h1 := hinv v
      have hres : ((X.filter (fun x => s(x, v) ∈ Res)).card : ℝ) ≤ ρ * n + ε * n := by
        by_cases hvS : v ∈ S
        · rw [reserve_load_eq hResEH v]
          have hk4 := (abs_le.mp (hgood.k4 v hvS)).2
          have hc : (((univ \ W).filter fun x => s(x, v) ∈ EH).card : ℝ) ≤ n := by
            rw [hn]; exact_mod_cast card_le_univ _
          have := mul_le_mul_of_nonneg_left hc hρ
          linarith
        · rw [reserve_load_zero hgood.cross hvS (fun h => (mem_sdiff.mp h).2 hvW) X,
            card_empty, Nat.cast_zero]
          have : 0 ≤ ρ * n := mul_nonneg hρ hn0
          linarith
      have h1' : ((X.filter (fun x => s(x, v) ∈ avail \ (Ep ∪ Ta))).card : ℝ) ≤
          (X.filter (fun x => s(x, v) ∈ Res)).card + D := by exact_mod_cast h1
      have : ((X.filter (fun x => s(x, v) ∈ avail \ (Ep ∪ Ta))).card : ℝ) ≤ Lv := by linarith
      exact_mod_cast this
    · have : (univ \ W).filter (fun x => s(x, v) ∈ avail \ (Ep ∪ Ta) ∧ v ∈ W) = ∅ := by
        rw [filter_eq_empty_iff]; intro x _ h; exact hvW h.2
      rw [this]; exact Nat.zero_le _
  · -- potential budget
    refine le_trans ?_ hB
    suffices hlog : Real.log (∑ x ∈ univ \ W, ((Tg x).card : ℝ)) ≤ 2 * Real.log n by
      linarith
    have hsum : ∑ x ∈ univ \ W, ((Tg x).card : ℝ) ≤ n ^ 2 := by
      calc ∑ x ∈ univ \ W, ((Tg x).card : ℝ) ≤ ∑ _x ∈ univ \ W, n :=
            sum_le_sum fun x _ => by rw [hn]; exact_mod_cast card_le_univ _
        _ = ((univ \ W).card : ℝ) * n := by rw [sum_const, nsmul_eq_mul]
        _ ≤ n * n := by
            apply mul_le_mul_of_nonneg_right _ hn0
            rw [hn]; exact_mod_cast card_le_univ _
        _ = n ^ 2 := by ring
    rcases (sum_nonneg (fun x _ => Nat.cast_nonneg ((Tg x).card)) :
        (0 : ℝ) ≤ ∑ x ∈ univ \ W, ((Tg x).card : ℝ)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero]
      have := Real.log_natCast_nonneg (Fintype.card V)
      linarith
    · calc Real.log (∑ x ∈ univ \ W, ((Tg x).card : ℝ)) ≤ Real.log (n ^ 2) :=
            Real.log_le_log hpos hsum
        _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

end NashWilliams18.Case124.BoundedCore
