/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostWalkQueries
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HingeCounting

@[expose] public section

/-! # Physical F0 hinge supply from the original host hypotheses -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges

open Finset CloneSupply TypedApplicationLinks WalkSupply SimplePathCounts
open HostWalkQueries HingeCounting HingeTemplates

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε θ : ℝ}

structure Budget (α ε θ : ℝ) (n : ℕ) : Prop where
  eps_nonneg : 0 ≤ ε
  theta_pos : 0 < θ
  theta_le : θ ≤ 1 / 100
  eps_theta : 100 * ε ≤ θ
  theta_alpha : 100 * θ ≤ α
  order : 4096 ≤ θ * n

theorem Budget.eps_le (b : Budget α ε θ (Fintype.card V)) : ε ≤ 1 / 100 := by
  linarith only [b.eps_theta, b.theta_le]

theorem Budget.order_large (b : Budget α ε θ (Fintype.card V)) :
    (96 : ℝ) ≤ Fintype.card V := by
  have ht := mul_le_mul_of_nonneg_right b.theta_le
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)
  nlinarith only [ht, b.order]

theorem Budget.part_size (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) :
    1024 ≤ θ * (partSet p i).card ∧ (12 : ℝ) ≤ (partSet p i).card := by
  have hn := order_le_four_part h (by linarith only [b.eps_le]) i
  have hnt := mul_le_mul_of_nonneg_left hn b.theta_pos.le
  have hm : 1024 ≤ θ * (partSet p i).card := by nlinarith only [hnt, b.order]
  have hmt := mul_le_mul_of_nonneg_right b.theta_le
    (Nat.cast_nonneg (partSet p i).card : (0 : ℝ) ≤ (partSet p i).card)
  exact ⟨hm, by nlinarith only [hm, hmt]⟩

theorem Budget.fresh_lower (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) (u : V) (R Q : Finset V)
    (hR : R.card ≤ 3) (hRpart : ∀ r ∈ R, p r ≠ i) (hQ : Q.card ≤ 6) :
    (Fintype.card V : ℝ) / 8 ≤ (freshInternal p G i u R Q).card :=
  freshInternal_lower h b.eps_nonneg (by linarith only [b.eps_le]) b.order_large i u R Q
    hR hRpart hQ

theorem Budget.three_lower (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) (hext : Nonextreme G (partSet p i) α)
    (a c u v : V) (ha : p a ≠ i) (hc : p c ≠ i)
    (hu : u ∈ commonPart p G i a c) (hv : v ∈ commonPart p G i a c) :
    θ * ((partSet p i).card : ℝ)^2 / 4 ≤
      (threeCandidates G (commonPart p G i a c) u v).card := by
  have hs := common_walk_supply h b.eps_nonneg b.eps_le θ b.theta_pos b.theta_le
    b.eps_theta b.theta_alpha b.order i hext a c ha hc
  exact threeCandidates_lower G (commonPart p G i a c) u v _ θ (Nat.cast_nonneg _)
    (Nat.cast_le.mpr (card_le_card (commonPart_subset p G i a c)))
    (by linarith only [hs.1]) (hs.2 u hu v hv)

theorem Budget.four_lower (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) (hext : Nonextreme G (partSet p i) α)
    (a c u v : V) (ha : p a ≠ i) (hc : p c ≠ i)
    (hu : u ∈ commonPart p G i a c) (hv : v ∈ commonPart p G i a c) :
    θ * ((partSet p i).card : ℝ)^3 / 16 ≤
      (fourCandidates G (commonPart p G i a c) u v).card := by
  have hs := common_walk_supply h b.eps_nonneg b.eps_le θ b.theta_pos b.theta_le
    b.eps_theta b.theta_alpha b.order i hext a c ha hc
  apply fourCandidates_lower G (commonPart p G i a c) u v _ θ b.theta_pos.le
    (b.part_size h i).2 (Nat.cast_le.mpr (card_le_card (commonPart_subset p G i a c))) hv
    (by linarith only [hs.1])
  · exact common_degree_lower h b.eps_le i a c ha hc ((commonPart_subset p G i a c) hu)
  · intro w hw
    exact hs.2 w hw v hv

theorem good_internal_count (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) (hext : Nonextreme G (partSet p i) α)
    (u v x y : V) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (pu : p u = i) (pv : p v = i) (px : p x = other0 i) (py : p y = other0 i)
    (huxG : G.Adj u x) (huyG : G.Adj u y) (hvxG : G.Adj v x) (hvyG : G.Adj v y) :
    θ / 2^30 * (Fintype.card V : ℝ)^2 ≤
      (countedHinges p F0 G {u, v, x} {u, v, y} 6).card := by
  classical
  let S := commonPart p G i x y
  let P := threeCandidates G S u v
  let f : (V × V) → Fin 6 → V := fun q => ![u, v, x, y, q.1, q.2]
  have hi : i ≠ other0 i := (other0_ne i).symm
  have huS : u ∈ S := mem_commonPart.mpr ⟨pu, huxG.symm, huyG.symm⟩
  have hvS : v ∈ S := mem_commonPart.mpr ⟨pv, hvxG.symm, hvyG.symm⟩
  have hmem : ∀ q ∈ P,
      (p q.1 = i ∧ G.Adj x q.1 ∧ G.Adj y q.1) ∧
      (p q.2 = i ∧ G.Adj x q.2 ∧ G.Adj y q.2) ∧
      q.1 ≠ u ∧ q.1 ≠ v ∧ q.2 ≠ u ∧ q.2 ≠ v ∧
      G.Adj u q.1 ∧ G.Adj q.1 q.2 ∧ G.Adj q.2 v := by
    intro q hq
    obtain ⟨hq1, hQ1, hq2, hQ2, h1, h2, h3⟩ :=
      (avoidingPairs_mem G S u v {u, v} q).mp hq
    simp only [mem_insert, mem_singleton, not_or] at hQ1 hQ2
    exact ⟨mem_commonPart.mp hq1, mem_commonPart.mp hq2,
      hQ1.1, hQ1.2, hQ2.1, hQ2.2, h1, h2, h3⟩
  have hpart_ne {a c : V} (ha : p a = i) (hc : p c = other0 i) : a ≠ c := by
    intro hac
    have hh := congrArg p hac
    rw [ha, hc] at hh
    exact hi hh
  have hfinj : ∀ q ∈ P, Function.Injective (f q) := by
    intro q hq
    obtain ⟨⟨p1, -, -⟩, ⟨p2, -, -⟩, h1, h2, h3, h4, -, h12, -⟩ := hmem q hq
    exact PhysicalHingeSupply.sixMap_injective
      ⟨huv, hux, huy, h1.symm, h3.symm, hvx, hvy, h2.symm, h4.symm, hxy,
        (hpart_ne p1 px).symm, (hpart_ne p2 px).symm,
        (hpart_ne p1 py).symm, (hpart_ne p2 py).symm, G.ne_of_adj h12⟩
  have hhinge : ∀ q ∈ P,
      IsHinge p F0 {u, v, x} {u, v, y} (Good.edges.image (Sym2.map (f q))) := by
    intro q hq
    have hp : ∀ j, p (f q j) = Good.part i j := by
      intro j
      have h1 := (hmem q hq).1.1
      have h2 := (hmem q hq).2.1.1
      fin_cases j <;> simp [f, Good.part, pu, pv, px, py, h1, h2]
    have ht := isHinge_image p (Good.part i) F0 Good.firstRoot Good.secondRoot Good.edges
      (f q) (hfinj q hq) hp (Good.hinge i)
    simpa [Good.firstRoot, Good.secondRoot, f] using ht
  have hhost : ∀ q ∈ P, Good.edges.image (Sym2.map (f q)) ⊆ G.edgeFinset := by
    intro q hq e he
    obtain ⟨⟨-, hx1, hy1⟩, ⟨-, hx2, hy2⟩, -, -, -, -, hu1, h12, h2v⟩ := hmem q hq
    simp only [Good.edges, image_insert, image_singleton, Sym2.map_mk, f,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exacts [hu1, h12, h2v, hx1.symm, hy1.symm, hx2.symm, hy2.symm]
  refine template_count p F0 G {u, v, x} {u, v, y} 2 6 (by decide)
    Good.edges Good.support P f ![4, 5] ?_ hfinj hhinge hhost
    (θ / 2^30 * (Fintype.card V : ℝ)^2) ?_
  · intro q hq q' hq' heq
    apply Prod.ext
    · exact congrFun heq 0
    · exact congrFun heq 1
  · have hP := b.three_lower h i hext x y u v (by simpa [px] using other0_ne i)
      (by simpa [py] using other0_ne i) huS hvS
    have hn := order_le_four_part h (by linarith only [b.eps_le]) i
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ (partSet p i).card := Nat.cast_nonneg _
    have hsq : (Fintype.card V : ℝ)^2 ≤ 16 * ((partSet p i).card : ℝ)^2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hsq b.theta_pos.le
    have hnθ := mul_nonneg b.theta_pos.le (sq_nonneg (Fintype.card V : ℝ))
    change θ / 2^30 * (Fintype.card V : ℝ)^2 * (6 : ℝ)^2 ≤ (P.card : ℝ)
    change θ * ((partSet p i).card : ℝ)^2 / 4 ≤ (P.card : ℝ) at hP
    norm_num
    nlinarith only [hP, ht, hnθ]

#print axioms good_internal_count

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges
