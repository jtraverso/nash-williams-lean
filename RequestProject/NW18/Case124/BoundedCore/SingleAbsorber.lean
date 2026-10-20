/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.BoundedCore.Assembly
import PartitionedTriangleAbsorption.SignedHinge.Main

/-!
# One terminal absorber for the ordinary triangle family, from a signed certificate

`absorber_onePart` is the one-part (`K₃`) version of the signed hinge absorber
`SignedHinge.absorber_of_budget`, for an arbitrary forbidden vertex set `Z`:

* every certificate term `c_j t_j` gives `|c_j|` occurrences of the actual triangle `t_j`, each
  with three signed slots (`exists_slot_matching_gen` resolves the multiplicities edge by edge);
* every occurrence and every negative slot receives a supplied hinge whose non-root support is
  fresh: disjoint from `Z`, from the certificate roots and from all other gadgets;
* `core_absorber` gives `A` with `A` and `A ∪ P` triangle-decomposable.

Every edge of `A` has an endpoint outside `Z` (`A` contains no root–root edge: hinges are
edge-disjoint from their root triangles), so `A` avoids every edge inside `Z`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.SignedHinge
  PartitionedTriangleAbsorption.SignedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- **Edge-preserving slot matching** from any signed triangle identity (the identity is the
only input; the part structure plays no role). -/
theorem exists_slot_matching_gen {ι : Type*} [Fintype ι] {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ}
    (hid : ∀ e : Sym2 V, ind P e = ∑ j, c j * ind (triEdges (t j)) e) (r : ι → Fin 3 → V)
    (hr : ∀ j, r j 0 ≠ r j 1 ∧ r j 0 ≠ r j 2 ∧ r j 1 ≠ r j 2 ∧
      t j = {r j 0, r j 1, r j 2}) :
    ∃ μ : {σ : Occ c × Fin 3 // 0 < c σ.1.1} ≃
        {f // f ∈ P} ⊕ {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1},
      ∀ σ, Sum.elim (fun f => f.1) (fun τ => slotBase r τ.1) (μ σ) = slotBase r σ.1 := by
  classical
  have hfib : ∀ e : Sym2 V,
      Fintype.card {σ : {σ : Occ c × Fin 3 // 0 < c σ.1.1} // slotBase r σ.1 = e} =
        Fintype.card {x : {f // f ∈ P} ⊕ {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} //
          Sum.elim (fun f => f.1) (fun τ => slotBase r τ.1) x = e} := by
    intro e
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun σ : Occ c × Fin 3 => 0 < c σ.1.1) (fun σ => slotBase r σ = e)),
      Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hnegCard := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun σ : Occ c × Fin 3 => ¬ 0 < c σ.1.1) (fun σ => slotBase r σ = e))
    change Fintype.card {σ : Occ c × Fin 3 // 0 < c σ.1.1 ∧ slotBase r σ = e} =
      Fintype.card {f : {f // f ∈ P} // f.1 = e} +
        Fintype.card {τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} // slotBase r τ.1 = e}
    rw [hnegCard]
    have hP : Fintype.card {f : {f // f ∈ P} // f.1 = e} = if e ∈ P then 1 else 0 := by
      split_ifs with he
      · rw [Fintype.card_eq_one_iff]
        exact ⟨⟨⟨e, he⟩, rfl⟩, fun x => Subtype.ext (Subtype.ext x.2)⟩
      · rw [Fintype.card_eq_zero_iff]
        exact ⟨fun x => he (x.2 ▸ x.1.2)⟩
    rw [hP, Fintype.card_subtype, Fintype.card_subtype]
    have hpos := card_slots_on_edge (c := c) r hr (fun j => 0 < c j) e
    have hneg := card_slots_on_edge (c := c) r hr (fun j => ¬ 0 < c j) e
    have hc := hid e
    have key : ∀ j, (if 0 < c j then ((c j).natAbs : ℤ) else 0) * ind (triEdges (t j)) e =
        c j * ind (triEdges (t j)) e +
          (if ¬ 0 < c j then ((c j).natAbs : ℤ) else 0) * ind (triEdges (t j)) e := by
      intro j
      by_cases hj : 0 < c j
      · simp [hj, abs_of_pos hj]
      · simp only [hj, ite_false, ite_true, zero_mul, not_false_eq_true]
        rw [Int.natCast_natAbs, abs_of_nonpos (not_lt.mp hj)]; ring
    rw [Finset.sum_congr rfl fun j _ => key j, sum_add_distrib, ← hc, ← hneg] at hpos
    have : ((univ.filter fun σ : Occ c × Fin 3 => 0 < c σ.1.1 ∧ slotBase r σ = e).card : ℤ) =
        ((if e ∈ P then 1 else 0 : ℕ) : ℤ) +
          ((univ.filter fun σ : Occ c × Fin 3 => ¬ 0 < c σ.1.1 ∧ slotBase r σ = e).card : ℤ) := by
      rw [hpos, ind]; split_ifs <;> simp
    exact_mod_cast this
  exact ⟨Equiv.ofFiberEquiv fun e => Fintype.equivOfCardEq (hfib e),
    fun σ => Equiv.ofFiberEquiv_map _ σ⟩

/-- **One `K₃` terminal absorber from a signed certificate**, avoiding a forbidden set `Z`.

Hypotheses: codegrees `≥ α n`, the explicit hinge supply `HingeSupply onePart K3fam G β C0`, a
signed certificate `ind P = ∑ c_j ind(t_j)` by actual triangles `t_j` of `G` of weight
`≤ K`, `P` inside `Z`, `|Z| ≤ z` and the two budget conditions.  Conclusion: some `A ⊆ E(G)`,
disjoint from `P`, with `A` and `A ∪ P` triangle-decomposable, every edge of `A` having an
endpoint outside `Z`, and `|A| ≤ 4K (C(C0+1,2) + 2)`. -/
theorem absorber_onePart (α β : ℝ) (C0 K z : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcand : ∀ u v w0 : V, u ≠ v → α * Fintype.card V ≤
      (univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ onePart w = onePart w0).card)
    (hsup : HingeSupply onePart K3fam G β C0) {ι : Type*} [Fintype ι] (P : Finset (Sym2 V))
    (t : ι → Finset V) (c : ι → ℤ) (hcopy : ∀ j, IsCopy onePart K3fam G (t j))
    (hid : ∀ e, ind P e = ∑ j, c j * ind (triEdges (t j)) e)
    (hK : certWeight c ≤ K) (Z : Finset V) (hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z) (hZ : Z.card ≤ z)
    (hαM : ((z + 3 * K + 4 * K * C0 + 1 : ℕ) : ℝ) < α * Fintype.card V)
    (hβM : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * ((z + 3 * K + 4 * K * C0 + 1 : ℕ) : ℝ) <
      β * Fintype.card V) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A P ∧
      HasDecomp onePart K3fam A ∧ HasDecomp onePart K3fam (A ∪ P) ∧
      (∀ e ∈ A, ∃ v ∈ e, v ∉ Z) ∧ A.card ≤ 4 * K * (Nat.choose (C0 + 1) 2 + 2) := by
  classical
  set n := Fintype.card V with hn
  set m := Nat.choose (C0 + 1) 2 with hm
  set B : ℕ := z + 3 * K + 4 * K * C0 + 1 with hB
  have hnpos : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    have : (0 : ℝ) ≤ (B : ℝ) := by positivity
    rw [h0] at hαM
    simp at hαM
    linarith
  have : Inhabited V := ⟨Classical.choice (Fintype.card_pos_iff.mp hnpos)⟩
  have hOcc := card_occ_le hK
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hr0 : ∀ j, ∃ r : Fin 3 → V,
      r 0 ≠ r 1 ∧ r 0 ≠ r 2 ∧ r 1 ≠ r 2 ∧ t j = {r 0, r 1, r 2} := by
    intro j
    obtain ⟨a, b, c', hab, hac, hbc, he⟩ := Finset.card_eq_three.mp (hcopy j).1.card_eq
    exact ⟨![a, b, c'], hab, hac, hbc, he⟩
  choose r hr using hr0
  set a : Occ c → V := fun o => r o.1 0 with ha
  set b : Occ c → V := fun o => r o.1 1 with hb
  set c3 : Occ c → V := fun o => r o.1 2 with hc3
  have hcopy' : ∀ o : Occ c, IsCopy onePart K3fam G {a o, b o, c3 o} := fun o =>
    (hr o.1).2.2.2 ▸ hcopy o.1
  have hdist : ∀ o, a o ≠ b o ∧ a o ≠ c3 o ∧ b o ≠ c3 o := fun o =>
    ⟨(hr o.1).1, (hr o.1).2.1, (hr o.1).2.2.1⟩
  have hcand' : ∀ o, α * n ≤
      (univ.filter fun w => G.Adj (a o) w ∧ G.Adj w (b o) ∧ onePart w = onePart (c3 o)).card :=
    fun o => hcand _ _ _ (hdist o).1
  -- the root region
  set Z' : Finset V := Z ∪ univ.biUnion (fun o : Occ c => ({a o, b o, c3 o} : Finset V))
    with hZ'
  have hZ'card : Z'.card ≤ z + 3 * K := by
    refine (card_union_le _ _).trans ?_
    have : (univ.biUnion (fun o : Occ c => ({a o, b o, c3 o} : Finset V))).card ≤
        3 * Fintype.card (Occ c) := by
      refine card_biUnion_le.trans ?_
      calc ∑ o : Occ c, ({a o, b o, c3 o} : Finset V).card ≤ ∑ _o : Occ c, 3 :=
            sum_le_sum fun o _ => card_le_three
        _ = 3 * Fintype.card (Occ c) := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]
    omega
  have hroots : ∀ o, ({a o, b o, c3 o} : Finset V) ⊆ Z' := fun o =>
    (subset_biUnion_of_mem (fun o : Occ c => ({a o, b o, c3 o} : Finset V)) (mem_univ o)).trans
      subset_union_right
  -- budgets
  have hbudR : ∀ k : ℕ, k ≤ z + 3 * K + 4 * K * C0 → (k : ℝ) < α * n ∧
      (2 ^ m : ℝ) * (k + 1) < β * n := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ B := by
      rw [hB]; exact_mod_cast Nat.succ_le_succ hk
    refine ⟨by linarith, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hk' h2m) hβM⟩
  -- occurrence apices and hinges
  obtain ⟨x, H, hxH, hHd⟩ := exists_occurrence_hinges hsup a b c3 hcopy' hdist hcand' Z' hroots
    (z + 3 * K + K * C0)
    (by have := Nat.mul_le_mul_right C0 hOcc; omega)
    (hbudR _ (by nlinarith)).1 (hbudR _ (by nlinarith)).2
  -- the occurrence gadgets
  have hgad := fun o => hinge_gadget (p := onePart) (F := K3fam) (hdist o).1 (hdist o).2.1
    (hdist o).2.2
    (fun h => (mem_sdiff.mp (hxH o).2.2.2.2.2.2.1).2 (by simp [h]))
    (fun h => (mem_sdiff.mp (hxH o).2.2.2.2.2.2.1).2 (by simp [h]))
    (fun h => (mem_sdiff.mp (hxH o).2.2.2.2.2.2.1).2 (by simp [h]))
    (hxH o).2.2.2.2.1
  choose y z' hyz using hgad
  set D : OccData V (Occ c) := ⟨a, b, c3, x, y, z', H⟩ with hD
  have hgood : ∀ o, OccGood onePart K3fam G Z' D o := fun o =>
    { hab := (hdist o).1
      hac := (hdist o).2.1
      hbc := (hdist o).2.2
      copy := hcopy' o
      roots := hroots o
      adj_ax := (hxH o).1
      adj_xb := (hxH o).2.1
      part_x := (hxH o).2.2.1
      sub := fun e he => SimpleGraph.mem_edgeFinset.mp ((hxH o).2.2.2.1 he)
      hinge := (hxH o).2.2.2.2.1
      x_fresh := (hxH o).2.2.2.2.2.2.1
      fresh_disj := (hxH o).2.2.2.2.2.2.2
      ya := (hyz o).1
      yb := (hyz o).2.1
      yc := (hyz o).2.2.1
      yx := (hyz o).2.2.2.1
      za := (hyz o).2.2.2.2.1
      zb := (hyz o).2.2.2.2.2.1
      zc := (hyz o).2.2.2.2.2.2.1
      zx := (hyz o).2.2.2.2.2.2.2.1
      yz := (hyz o).2.2.2.2.2.2.2.2.1
      triY := (hyz o).2.2.2.2.2.2.2.2.2.1
      triZ := (hyz o).2.2.2.2.2.2.2.2.2.2.1
      ay := (hyz o).2.2.2.2.2.2.2.2.2.2.2.1
      cy := (hyz o).2.2.2.2.2.2.2.2.2.2.2.2.1
      bz := (hyz o).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      cz := (hyz o).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      dec_core := (hyz o).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      dec_block := (hyz o).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }
  have hF : ∀ o o', o ≠ o' → Disjoint (D.fresh o) (D.fresh o') := hHd
  have hfresh_card : ∀ o, (D.fresh o).card ≤ C0 := fun o =>
    (card_le_card sdiff_subset).trans (hxH o).2.2.2.2.2.1
  -- the slot matching
  obtain ⟨μ, hμ⟩ := exists_slot_matching_gen hid r hr
  have hμ' : ∀ σ, Sum.elim (fun f => f.1) (fun τ => s(D.bu τ.1, D.bv τ.1)) (μ σ) =
      s(D.bu σ.1, D.bv σ.1) := by
    have hbase : ∀ σ : Occ c × Fin 3, slotBase r σ = s(D.bu σ, D.bv σ) := fun σ =>
      (D.base_eq σ).symm
    intro σ
    have := hμ σ
    simp only [hbase] at this
    exact this
  set pt : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} → Occ c × Fin 3 :=
    fun τ => (μ.symm (Sum.inr τ)).1 with hpt
  have hbase_pt : ∀ τ, s(D.bu (pt τ), D.bv (pt τ)) = s(D.bu τ.1, D.bv τ.1) := by
    intro τ
    have := hμ' (μ.symm (Sum.inr τ))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hap_ne : ∀ τ, D.ap τ.1 ≠ D.ap (pt τ) := by
    intro τ he
    have := D.ap_inj hgood hF he
    exact τ.2 (this ▸ (μ.symm (Sum.inr τ)).2)
  have hNcard : Fintype.card {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} ≤ 3 * K := by
    refine (Fintype.card_subtype_le _).trans ?_
    rw [Fintype.card_prod, Fintype.card_fin]
    omega
  have hU₀card : (Z' ∪ univ.biUnion D.fresh).card ≤ z + 3 * K + K * C0 := by
    refine (card_union_le _ _).trans ?_
    have : (univ.biUnion D.fresh).card ≤ Fintype.card (Occ c) * C0 := by
      refine card_biUnion_le.trans ?_
      calc ∑ o : Occ c, (D.fresh o).card ≤ ∑ _o : Occ c, C0 := sum_le_sum fun o _ =>
            hfresh_card o
        _ = Fintype.card (Occ c) * C0 := by rw [sum_const, card_univ, smul_eq_mul]
    have := Nat.mul_le_mul_right C0 hOcc
    omega
  -- slot hinges
  obtain ⟨Hs, hHs, hHsd⟩ := exists_slot_hinges hsup
    (fun τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} => D.bu τ.1)
    (fun τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} => D.bv τ.1)
    (fun τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} => D.ap τ.1)
    (fun τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} => D.ap (pt τ))
    (fun τ => ⟨D.bu_ne_bv hgood _, D.bu_ne_ap hgood _ _, D.bu_ne_ap hgood _ _,
      D.bv_ne_ap hgood _ _, D.bv_ne_ap hgood _ _, hap_ne τ⟩)
    (fun τ => D.tri_copy hgood τ.1)
    (fun τ => by
      show IsCopy onePart K3fam G {D.bu τ.1, D.bv τ.1, D.ap (pt τ)}
      rw [← triple_eq_of_sym2_eq (D.ap (pt τ)) (hbase_pt τ)]
      exact D.tri_copy hgood (pt τ))
    (Z' ∪ univ.biUnion D.fresh) (z + 3 * K + 4 * K * C0)
    (by have := Nat.mul_le_mul_right C0 hNcard; nlinarith)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by
      rw [hB]; push_cast; linarith) h2m) hβM)
  -- the core absorber
  have hPZ' : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z' := fun e he v hv => mem_union_left _ (hPZ e he v hv)
  obtain ⟨hdA, hdB, hdis, hsubX, hvX, hXsub⟩ := core_absorber D hgood hF
    (fun o => 0 < c o.1) P hPZ' μ hμ' Hs
    (fun τ e he => SimpleGraph.mem_edgeFinset.mp ((hHs τ).1 he))
    (fun τ => (hHs τ).2.1) (fun τ => (hHs τ).2.2.2) hHsd
  set X := univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs with hX
  have hHm : ∀ E : Finset (Sym2 V), (vertSet E).card ≤ C0 → E.card ≤ m := fun E hE =>
    (card_le_choose_vertSet E).trans (Nat.choose_le_choose 2 (by omega))
  have hXcard : X.card ≤ 4 * K * (m + 2) := by
    refine (card_le_card hXsub).trans ((card_union_le _ _).trans ?_)
    have hB' : (univ.biUnion fun o => D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)}).card ≤
        Fintype.card (Occ c) * (m + 2) := by
      refine card_biUnion_le.trans ?_
      calc _ ≤ ∑ _o : Occ c, (m + 2) := sum_le_sum fun o _ => by
            refine (card_union_le _ _).trans ?_
            have := hHm (D.H o) (hxH o).2.2.2.2.2.1
            have : ({s(D.a o, D.x o), s(D.b o, D.x o)} : Finset (Sym2 V)).card ≤ 2 :=
              card_le_two
            omega
        _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
    have hHs' : (univ.biUnion Hs).card ≤
        Fintype.card {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} * m := by
      refine card_biUnion_le.trans ?_
      calc _ ≤ ∑ _τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1}, m :=
            sum_le_sum fun τ _ => hHm (Hs τ) (hHs τ).2.2.1
        _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
    have e1 := Nat.mul_le_mul_right (m + 2) hOcc
    have e2 := Nat.mul_le_mul_right m hNcard
    nlinarith
  -- no edge of `X` lies inside `Z'`
  have hout : ∀ e ∈ X, ∃ v ∈ e, v ∉ Z' := by
    intro e he
    by_contra hcon
    push_neg at hcon
    rcases mem_union.mp (hXsub he) with hb' | hs'
    · obtain ⟨o, -, heo⟩ := mem_biUnion.mp hb'
      exact D.block_no_inside hgood o e heo hcon
    · obtain ⟨τ, -, heτ⟩ := mem_biUnion.mp hs'
      have hG : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp ((hHs τ).1 heτ)
      have hbase : ∀ v ∈ e, v ∈ ({D.bu τ.1, D.bv τ.1, D.ap τ.1} : Finset V) := by
        intro v hv
        have hvZ := hcon v hv
        have hvR : v ∈ ({D.bu τ.1, D.bv τ.1, D.ap τ.1, D.ap (pt τ)} : Finset V) := by
          by_contra hvR
          exact disjoint_left.mp (hHs τ).2.2.2
            (mem_sdiff.mpr ⟨mem_vertSet_of_mem heτ hv, hvR⟩) (mem_union_left _ hvZ)
        simp only [mem_insert, mem_singleton] at hvR ⊢
        rcases hvR with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd (h ▸ hvZ) (D.ap_not_Z' hgood _)
        · exact absurd (h ▸ hvZ) (D.ap_not_Z' hgood _)
      exact disjoint_left.mp (hHs τ).2.1.1 heτ
        (mem_union_left _ (mem_triEdges_of_endpoints hG hbase))
  refine ⟨X, fun e he => SimpleGraph.mem_edgeFinset.mpr (hsubX e he), hdis, hdA, hdB, ?_,
    hXcard⟩
  intro e he
  obtain ⟨v, hv, hvZ⟩ := hout e he
  exact ⟨v, hv, fun h => hvZ (mem_union_left _ h)⟩

end NashWilliams18
