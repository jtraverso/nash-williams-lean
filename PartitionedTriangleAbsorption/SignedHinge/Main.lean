/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Core
public import PartitionedTriangleAbsorption.SignedHinge.SlotSelect
public import PartitionedTriangleAbsorption.SignedCertificate.Packing
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Stage 53: the bounded signed physical absorber under explicit physical hinge supply

`absorber_of_budget` is the construction for a fixed host, under the two explicit size
conditions `M < α n` and `2^C(C0+1,2) M < β n` with `M = 9K + 4K C0 + 1`.
`signed_hinge_absorber` packages it with uniform constants `C, N` chosen from
`α, β, C0, K` only (before the host, the edge set and the certificate).

The construction:
1. every certificate term `c_j t_j` gives `|c_j|` occurrences; each occurrence of
   `t = {a,b,c}` gets a fresh apex `x` and a supplied hinge `H` for `{a,b,c}, {a,b,x}`
   (vertex-fresh outside its roots); `hinge_gadget` turns it into three slot wedges and a
   decomposable local closure `Y` (`exists_occurrence_hinges`, `hinge_gadget`);
2. the certificate identity gives an edge-preserving bijection
   `positive slots ≃ P ⊕ negative slots` (`exists_slot_matching`);
3. every negative slot gets a supplied slot hinge to its matched positive slot
   (`exists_slot_hinges`);
4. `core_absorber` (via `two_mode_assembly`) gives `A = X` with `X` and `X ∪ P` decomposable;
5. `Q` is a vertex-disjoint fresh F0 packing with the same physical `00/11/01` counts as `P`
   (`exists_fresh_destination`), so `A ∪ Q` is decomposable.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset SignedCertificate TypedApplicationLinks

/-- The uniform constant of the Stage 53 absorber. -/
def absorberConst (C0 : ℕ) : ℕ := 8 * (Nat.choose (C0 + 1) 2 + 2) + 6

/-- The vertex budget of the Stage 53 absorber. -/
def absorberBudget (C0 K : ℕ) : ℕ := 9 * K + 4 * K * C0 + 1

theorem card_occ_le {ι : Type*} [Fintype ι] {c : ι → ℤ} {K : ℕ} (hK : certWeight c ≤ K) :
    Fintype.card (Occ c) ≤ K := by
  have h1 : Fintype.card (Occ c) = ∑ j, (c j).natAbs := by
    simp [Occ, Fintype.card_sigma]
  have h2 : ((∑ j, (c j).natAbs : ℕ) : ℤ) = certWeight c := by
    simp [certWeight]
  omega

theorem arith_A (K m : ℕ) : 4 * K * (m + 2) ≤ (8 * (m + 2) + 6) * K := by nlinarith

theorem arith_Q (K m : ℕ) : 3 * K ≤ (8 * (m + 2) + 6) * K := by nlinarith

theorem arith_V {K m a q v : ℕ} (ha : a ≤ 4 * K * (m + 2)) (hq : q ≤ 3 * K)
    (hv : v ≤ 2 * (a + q)) : v ≤ (8 * (m + 2) + 6) * K := by nlinarith

/-- **Fixed-host construction under explicit size conditions.** -/
theorem absorber_of_budget (α β : ℝ) (C0 K : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hparts : ∀ j : Fin 2, ∃ v, p v = j) (hanti : AntiEdgeful p F0 G α)
    (hsup : HingeSupply p F0 G β C0) {ι : Type*} [Fintype ι] (P : Finset (Sym2 V))
    (t : ι → Finset V) (c : ι → ℤ) (Z : Finset V) (hcert : IsSignedCert p G P t c)
    (hK : certWeight c ≤ K) (hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z) (hZ : Z.card ≤ 3 * K)
    (hαM : (absorberBudget C0 K : ℝ) < α * Fintype.card V)
    (hβM : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * absorberBudget C0 K < β * Fintype.card V) :
    ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
      Disjoint P A ∧ Disjoint P Q ∧ Disjoint A Q ∧ (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
      (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
      HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ HasDecomp p F0 (A ∪ Q) ∧
      A.card ≤ absorberConst C0 * K ∧ Q.card ≤ absorberConst C0 * K ∧
      (vertSet (A ∪ Q)).card ≤ absorberConst C0 * K ∧
      pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
      pairCount p Q 0 1 = pairCount p P 0 1 := by
  classical
  set n := Fintype.card V with hn
  set m := Nat.choose (C0 + 1) 2 with hm
  have : Inhabited V := ⟨(hparts 0).choose⟩
  have hOcc := card_occ_le hK
  have hMdef : absorberBudget C0 K = 9 * K + 4 * K * C0 + 1 := rfl
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  -- labelled vertices of the certificate triangles
  have hr0 : ∀ j, ∃ r : Fin 3 → V,
      r 0 ≠ r 1 ∧ r 0 ≠ r 2 ∧ r 1 ≠ r 2 ∧ t j = {r 0, r 1, r 2} := by
    intro j
    obtain ⟨a, b, c', hab, hac, hbc, he⟩ :=
      Finset.card_eq_three.mp (card_three_of_isCopy (hcert.1 j))
    exact ⟨![a, b, c'], hab, hac, hbc, he⟩
  choose r hr using hr0
  set a : Occ c → V := fun o => r o.1 0 with ha
  set b : Occ c → V := fun o => r o.1 1 with hb
  set c3 : Occ c → V := fun o => r o.1 2 with hc3
  have hcopy : ∀ o : Occ c, IsCopy p F0 G {a o, b o, c3 o} := fun o =>
    (hr o.1).2.2.2 ▸ hcert.1 o.1
  have hdist : ∀ o, a o ≠ b o ∧ a o ≠ c3 o ∧ b o ≠ c3 o := fun o =>
    ⟨(hr o.1).1, (hr o.1).2.1, (hr o.1).2.2.1⟩
  have hcand : ∀ o, α * n ≤
      (univ.filter fun w => G.Adj (a o) w ∧ G.Adj w (b o) ∧ p w = p (c3 o)).card := by
    intro o
    obtain ⟨h1, h2, h3⟩ := hdist o
    have hF := (hcopy o).2
    rw [map_three p h1 h2 h3] at hF
    exact hanti _ hF _ _ _ rfl _ _ h1 rfl rfl
  -- the root region
  set Z' : Finset V := Z ∪ univ.biUnion (fun o : Occ c => ({a o, b o, c3 o} : Finset V))
    with hZ'
  have hZ'card : Z'.card ≤ 6 * K := by
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
  have hbudR : ∀ k : ℕ, k ≤ 9 * K + 4 * K * C0 → (k : ℝ) < α * n ∧
      (2 ^ m : ℝ) * (k + 1) < β * n := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ absorberBudget C0 K := by
      rw [hMdef]; exact_mod_cast Nat.succ_le_succ hk
    refine ⟨by linarith, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hk' h2m) hβM⟩
  -- occurrence apices and hinges
  obtain ⟨x, H, hxH, hHd⟩ := exists_occurrence_hinges hsup a b c3 hcopy hdist hcand Z' hroots
    (6 * K + K * C0)
    (by have := Nat.mul_le_mul_right C0 hOcc; omega)
    (hbudR _ (by nlinarith)).1 (hbudR _ (by nlinarith)).2
  -- the occurrence gadgets
  have hgad := fun o => hinge_gadget (p := p) (F := F0) (hdist o).1 (hdist o).2.1
    (hdist o).2.2
    (fun h => (mem_sdiff.mp (hxH o).2.2.2.2.2.2.1).2 (by simp [h]))
    (fun h => (mem_sdiff.mp (hxH o).2.2.2.2.2.2.1).2 (by simp [h]))
    (fun h => (mem_sdiff.mp (hxH o).2.2.2.2.2.2.1).2 (by simp [h]))
    (hxH o).2.2.2.2.1
  choose y z hyz using hgad
  set D : OccData V (Occ c) := ⟨a, b, c3, x, y, z, H⟩ with hD
  have hgood : ∀ o, OccGood p F0 G Z' D o := fun o =>
    { hab := (hdist o).1
      hac := (hdist o).2.1
      hbc := (hdist o).2.2
      copy := hcopy o
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
  obtain ⟨μ, hμ⟩ := exists_slot_matching p G hcert r hr
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
  have hU₀card : (Z' ∪ univ.biUnion D.fresh).card ≤ 6 * K + K * C0 := by
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
      show IsCopy p F0 G {D.bu τ.1, D.bv τ.1, D.ap (pt τ)}
      rw [← triple_eq_of_sym2_eq (D.ap (pt τ)) (hbase_pt τ)]
      exact D.tri_copy hgood (pt τ))
    (Z' ∪ univ.biUnion D.fresh) (6 * K + 4 * K * C0)
    (by have := Nat.mul_le_mul_right C0 hNcard; nlinarith)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by
      rw [hMdef]; push_cast; nlinarith) h2m) hβM)
  -- the core absorber
  have hPZ' : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z' := fun e he v hv => mem_union_left _ (hPZ e he v hv)
  obtain ⟨hdA, hdB, hdis, hsubX, hvX, hXsub⟩ := core_absorber D hgood hF
    (fun o => 0 < c o.1) P hPZ' μ hμ' Hs
    (fun τ e he => SimpleGraph.mem_edgeFinset.mp ((hHs τ).1 he))
    (fun τ => (hHs τ).2.1) (fun τ => (hHs τ).2.2.2) hHsd
  set X := univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs with hX
  set W := Z' ∪ univ.biUnion D.fresh ∪ univ.biUnion (fun τ => vertSet (Hs τ) \
    {D.bu τ.1, D.bv τ.1, D.ap τ.1, D.ap (μ.symm (Sum.inr τ)).1}) with hW
  have hWcard : W.card ≤ 6 * K + 4 * K * C0 := by
    refine (card_union_le _ _).trans ?_
    have : (univ.biUnion (fun τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} => vertSet (Hs τ) \
        {D.bu τ.1, D.bv τ.1, D.ap τ.1, D.ap (μ.symm (Sum.inr τ)).1})).card ≤
        Fintype.card {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} * C0 := by
      refine card_biUnion_le.trans ?_
      calc _ ≤ ∑ _τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1}, C0 :=
            sum_le_sum fun τ _ => (card_le_card sdiff_subset).trans (hHs τ).2.2.1
        _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
    have := Nat.mul_le_mul_right C0 hNcard
    nlinarith
  have hPcard : P.card ≤ 3 * K := by
    have h1 := card_eq_of_cert p G hcert
    have h2 : ∑ j, c j ≤ certWeight c := sum_le_sum fun j _ => le_abs_self _
    omega
  obtain ⟨Q, DQ, hQdec, hQpd, hQG, hQW, hQcard, h00, h11, h01⟩ :=
    exists_fresh_destination p G α hanti hparts hcert W (by
      have := (hbudR (W.card + P.card) (by omega)).1
      push_cast at this
      exact this)
  have hZW : Z ⊆ W := fun v hv => mem_union_left _ (mem_union_left _ (mem_union_left _ hv))
  have hXW : ∀ e ∈ X, ∀ v ∈ e, v ∈ W := fun e he v hv => hvX (mem_vertSet_of_mem he hv)
  have hAQ : Disjoint X Q := by
    rw [disjoint_left]
    intro e he hq
    induction e using Sym2.ind with
    | _ u v => exact hQW _ hq u (Sym2.mem_mk_left _ _) (hXW _ he u (Sym2.mem_mk_left _ _))
  have hPQ : Disjoint P Q := by
    rw [disjoint_left]
    intro e he hq
    induction e using Sym2.ind with
    | _ u v => exact hQW _ hq u (Sym2.mem_mk_left _ _) (hZW (hPZ _ he u (Sym2.mem_mk_left _ _)))
  have hHm : ∀ E : Finset (Sym2 V), (vertSet E).card ≤ C0 → E.card ≤ m := fun E hE =>
    (card_le_choose_vertSet E).trans (Nat.choose_le_choose 2 (by omega))
  have hXcard : X.card ≤ 4 * K * (m + 2) := by
    refine (card_le_card hXsub).trans ((card_union_le _ _).trans ?_)
    have hB : (univ.biUnion fun o => D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)}).card ≤
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
  have hC : absorberConst C0 = 8 * (m + 2) + 6 := rfl
  refine ⟨X, Q, fun e he => SimpleGraph.mem_edgeFinset.mpr (hsubX e he), hQG, hdis.symm, hPQ,
    hAQ, fun e he v hv hvZ => hQW e he v hv (hZW hvZ), ⟨DQ, hQdec, hQpd⟩, hdA, hdB,
    HasDecomp.union hdA ⟨DQ, hQdec⟩ hAQ, ?_, ?_, ?_, h00, h11, h01⟩
  · rw [hC]; exact hXcard.trans (arith_A K m)
  · rw [hC, hQcard]; exact hPcard.trans (arith_Q K m)
  · rw [hC]
    have h1 := card_vertSet_le (X ∪ Q)
    have h2 := card_union_le X Q
    rw [hQcard] at h2
    exact arith_V hXcard hPcard (h1.trans (Nat.mul_le_mul_left 2 h2))

end PartitionedTriangleAbsorption.SignedHinge

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset SignedCertificate TypedApplicationLinks

/-- **Stage 53: bounded signed physical absorber under explicit physical hinge supply.**

`α, β > 0`, `C0` and `K` are fixed first; `C = absorberConst C0` and `N` depend only on
them. For every host with both parts inhabited, `AntiEdgeful p F0 G α` and the explicit
physical hinge supply `HingeSupply p F0 G β C0`, every `P ⊆ E(G)` with a signed physical
certificate of weight `≤ K` and every `Z ⊇ support(P)` with `|Z| ≤ 3K` have some `A, Q ⊆ E(G)`
with `P, A, Q` pairwise edge-disjoint, `Q` outside `Z` and vertex-disjointly decomposable,
`A`, `A ∪ P`, `A ∪ Q` decomposable (the same `A`), `|A|, |Q|, |vertSet (A ∪ Q)| ≤ C K`, and
the physical `00/11/01` counts of `Q` equal to those of `P`.

The requested side condition `6 ≤ C0` is not needed by the proof and has been dropped, so
the statement is slightly more general (for `C0 < 6` the supply hypothesis can only hold on
hosts without two `F0`-copies sharing exactly one edge, since `Icc 6 C0` is empty). -/
theorem signed_hinge_absorber (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (C0 : ℕ) (K : ℕ) :
    ∃ C N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ j : Fin 2, ∃ v, p v = j) → AntiEdgeful p F0 G α → HingeSupply p F0 G β C0 →
        ∀ {ι : Type} [Fintype ι] (P : Finset (Sym2 V)) (t : ι → Finset V) (c : ι → ℤ)
          (Z : Finset V), IsSignedCert p G P t c → certWeight c ≤ K →
          (∀ e ∈ P, ∀ v ∈ e, v ∈ Z) → Z.card ≤ 3 * K →
          ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
            Disjoint P A ∧ Disjoint P Q ∧ Disjoint A Q ∧ (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
            (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
            HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ HasDecomp p F0 (A ∪ Q) ∧
            A.card ≤ C * K ∧ Q.card ≤ C * K ∧ (vertSet (A ∪ Q)).card ≤ C * K ∧
            pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
            pairCount p Q 0 1 = pairCount p P 0 1 := by
  set M : ℝ := (absorberBudget C0 K : ℝ)
  set B : ℝ := (2 : ℝ) ^ Nat.choose (C0 + 1) 2
  refine ⟨absorberConst C0, ⌈M / α⌉₊ + ⌈B * M / β⌉₊ + 1, ?_⟩
  intro V _ _ hN p G _ hparts hanti hsup ι _ P t c Z hcert hK hPZ hZ
  have hn1 : M / α < Fintype.card V := by
    have := Nat.le_ceil (M / α)
    have h' : (⌈M / α⌉₊ : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast (by omega)
    linarith
  have hn2 : B * M / β < Fintype.card V := by
    have := Nat.le_ceil (B * M / β)
    have h' : (⌈B * M / β⌉₊ : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast (by omega)
    linarith
  exact absorber_of_budget α β C0 K p G hparts hanti hsup P t c Z hcert hK hPZ hZ
    ((div_lt_iff₀ hα).mp hn1 |>.trans_eq (mul_comm _ _))
    ((div_lt_iff₀ hβ).mp hn2 |>.trans_eq (mul_comm _ _))

end PartitionedTriangleAbsorption.SignedHinge
