/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges

open Finset CloneSupply TypedApplicationLinks WalkSupply SimplePathCounts
open HostWalkQueries HingeCounting HingeTemplates

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε θ : ℝ}

private theorem triple_injective {a c d : V} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, c, d] : Fin 3 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem bad_internal_count (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) (hext : Nonextreme G (partSet p (other0 i)) α)
    (u v x y : V) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (pu : p u = i) (pv : p v = i) (px : p x = other0 i) (py : p y = other0 i)
    (huxG : G.Adj u x) (huyG : G.Adj u y) (hvxG : G.Adj v x) (hvyG : G.Adj v y) :
    θ / 2^30 * (Fintype.card V : ℝ)^4 ≤
      (countedHinges p F0 G {u, v, x} {u, v, y} 8).card := by
  classical
  let Q := freshInternal p G i u {x, y} {u, v, x, y}
  let T : V → Finset V := fun q => commonPart p G (other0 i) q v
  let P : Finset (Σ _q : V, Σ _c : V, V × V) := Q.sigma (fun q => fourCandidates G (T q) x y)
  let f : (Σ _q : V, Σ _c : V, V × V) → Fin 8 → V :=
    fun z => ![u, v, x, y, z.1, z.2.1, z.2.2.1, z.2.2.2]
  have hi : i ≠ other0 i := (other0_ne i).symm
  have hqprop : ∀ q ∈ Q, p q = i ∧ G.Adj u q ∧ q ≠ u ∧ q ≠ v ∧
      G.Adj q x ∧ G.Adj q y := by
    intro q hq
    obtain ⟨hpq, huq, hqR, hqxy⟩ := (freshInternal_mem p G i u {x, y} {u, v, x, y} q).mp hq
    simp only [mem_insert, mem_singleton, not_or] at hqR
    exact ⟨hpq, huq, hqR.1, hqR.2.1,
      (hqxy x (by simp)).symm, (hqxy y (by simp)).symm⟩
  have hrprop : ∀ q : V, ∀ r ∈ fourCandidates G (T q) x y,
      (p r.1 = other0 i ∧ G.Adj q r.1 ∧ G.Adj v r.1) ∧
      (p r.2.1 = other0 i ∧ G.Adj q r.2.1 ∧ G.Adj v r.2.1) ∧
      (p r.2.2 = other0 i ∧ G.Adj q r.2.2 ∧ G.Adj v r.2.2) ∧
      G.Adj x r.1 ∧ G.Adj r.1 r.2.1 ∧ G.Adj r.2.1 r.2.2 ∧ G.Adj r.2.2 y := by
    intro q r hr
    obtain ⟨hc, hxc, -, hp⟩ := (fourCandidates_mem G (T q) x y r).mp hr
    obtain ⟨ha, -, hd, -, hca, had, hdy⟩ :=
      (avoidingPairs_mem G (T q) r.1 y {x, r.1, y} r.2).mp hp
    exact ⟨mem_commonPart.mp hc, mem_commonPart.mp ha, mem_commonPart.mp hd,
      hxc, hca, had, hdy⟩
  have hfinj : ∀ z ∈ P, Function.Injective (f z) := by
    intro z hz
    obtain ⟨hzQ, hzP⟩ := mem_sigma.mp hz
    obtain ⟨pq, -, hqu, hqv, -, -⟩ := hqprop z.1 hzQ
    obtain ⟨⟨pc, -, -⟩, ⟨pa, -, -⟩, ⟨pd, -, -⟩, -, -, -, -⟩ := hrprop z.1 z.2 hzP
    have hA : (fun j : Fin 3 => f z (![0, 1, 4] j)) = ![u, v, z.1] := by
      funext j
      fin_cases j <;> rfl
    have hB : (fun j : Fin 5 => f z (![2, 5, 6, 7, 3] j)) = fourMap x y z.2 := by
      funext j
      fin_cases j <;> rfl
    apply injective_of_two_blocks (f z) (![0, 1, 4] : Fin 3 → Fin 8)
      (![2, 5, 6, 7, 3] : Fin 5 → Fin 8) (by decide)
    · rw [hA]
      exact triple_injective huv hqu.symm hqv.symm
    · rw [hB]
      exact fourMap_injective G (T z.1) hxy hzP
    · intro j k heq
      have ha : p (f z (![0, 1, 4] j)) = i := by
        fin_cases j <;> simp [f, pu, pv, pq]
      have hb : p (f z (![2, 5, 6, 7, 3] k)) = other0 i := by
        fin_cases k <;> simp [f, px, py, pc, pa, pd]
      have hh := congrArg p heq
      rw [ha, hb] at hh
      exact hi hh
  have hhinge : ∀ z ∈ P,
      IsHinge p F0 {u, v, x} {u, v, y} (Bad.edges.image (Sym2.map (f z))) := by
    intro z hz
    obtain ⟨hzQ, hzP⟩ := mem_sigma.mp hz
    have pq := (hqprop z.1 hzQ).1
    have pc := (hrprop z.1 z.2 hzP).1.1
    have pa := (hrprop z.1 z.2 hzP).2.1.1
    have pd := (hrprop z.1 z.2 hzP).2.2.1.1
    have hp : ∀ j, p (f z j) = Bad.part i j := by
      intro j
      fin_cases j <;> simp [f, Bad.part, pu, pv, px, py, pq, pc, pa, pd]
    have ht := isHinge_image p (Bad.part i) F0 Bad.firstRoot Bad.secondRoot Bad.edges
      (f z) (hfinj z hz) hp (Bad.hinge i)
    simpa [Bad.firstRoot, Bad.secondRoot, f] using ht
  have hhost : ∀ z ∈ P, Bad.edges.image (Sym2.map (f z)) ⊆ G.edgeFinset := by
    intro z hz e he
    obtain ⟨hzQ, hzP⟩ := mem_sigma.mp hz
    obtain ⟨-, huq, -, -, hqx, hqy⟩ := hqprop z.1 hzQ
    obtain ⟨⟨-, hqc, hvc⟩, ⟨-, hqa, hva⟩, ⟨-, hqd, hvd⟩, hxc, hca, had, hdy⟩ :=
      hrprop z.1 z.2 hzP
    simp only [Bad.edges, image_insert, image_singleton, Sym2.map_mk, f,
      Matrix.cons_val_zero, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exacts [huq, hqx, hqy, hxc, hca, had, hdy, hqc, hqa, hqd, hvc, hva, hvd]
  refine template_count p F0 G {u, v, x} {u, v, y} 4 8 (by decide)
    Bad.edges Bad.support P f ![4, 5, 6, 7] ?_ hfinj hhinge hhost
    (θ / 2^30 * (Fintype.card V : ℝ)^4) ?_
  · intro z hz z' hz' heq
    have hq : z.1 = z'.1 := congrFun heq 0
    have hc : z.2.1 = z'.2.1 := congrFun heq 1
    have ha : z.2.2.1 = z'.2.2.1 := congrFun heq 2
    have hd : z.2.2.2 = z'.2.2.2 := congrFun heq 3
    exact Sigma.ext hq (heq_of_eq (Sigma.ext hc (heq_of_eq (Prod.ext ha hd))))
  · have hQ : (Fintype.card V : ℝ) / 8 ≤ Q.card := by
      apply b.fresh_lower h i u {x, y} {u, v, x, y}
        (card_le_two.trans (by decide)) _ (card_le_four.trans (by decide))
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl <;> simpa [px, py] using other0_ne i
    have hper : ∀ q ∈ Q, θ * ((partSet p (other0 i)).card : ℝ)^3 / 16 ≤
        (fourCandidates G (T q) x y).card := by
      intro q hq
      obtain ⟨pq, -, -, -, hqx, hqy⟩ := hqprop q hq
      apply b.four_lower h (other0 i) hext q v x y
        (by simpa [pq] using hi) (by simpa [pv] using hi)
      · exact mem_commonPart.mpr ⟨px, hqx, hvxG⟩
      · exact mem_commonPart.mpr ⟨py, hqy, hvyG⟩
    have hsum := sum_le_sum hper
    simp only [sum_const, nsmul_eq_mul] at hsum
    have hP : (P.card : ℝ) = ∑ q ∈ Q, ((fourCandidates G (T q) x y).card : ℝ) := by
      simp only [P, card_sigma, Nat.cast_sum]
    have hQmul := mul_le_mul_of_nonneg_right hQ
      (show 0 ≤ θ * ((partSet p (other0 i)).card : ℝ)^3 / 16 by
        apply div_nonneg (mul_nonneg b.theta_pos.le (pow_nonneg (Nat.cast_nonneg _) _)) (by norm_num))
    have hn := order_le_four_part h (by linarith only [b.eps_le]) (other0 i)
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hpow := pow_le_pow_left₀ hn0 hn 3
    have hpowθ := mul_le_mul_of_nonneg_left hpow (mul_nonneg b.theta_pos.le hn0)
    have hnθ := mul_nonneg b.theta_pos.le (pow_nonneg hn0 4)
    change θ / 2^30 * (Fintype.card V : ℝ)^4 * (8 : ℝ)^4 ≤ (P.card : ℝ)
    norm_num
    nlinarith only [hP, hsum, hQmul, hpowθ, hnθ]

#print axioms bad_internal_count

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges
