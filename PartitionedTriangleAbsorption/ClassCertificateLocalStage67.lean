/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassCertificate.Producer
public import PartitionedTriangleAbsorption.ClassRepresentativesStage65

/-! # Local physical certificates after bounded edge deletion

The certificate uses only source edges, source-to-representative edges and the
representative tetrahedron. Missing edges elsewhere in the host are irrelevant.
Structural F3 divisibility remains an explicit hypothesis, not coarse F0 divisibility.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassCertificateLocalStage67

open Finset TypedApplicationLinks SignedCertificate IntegerCertificate
open ClassCertificate ClassLatticeStage65 LocalCycleTransportStage62 ParityBalanceStage63

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {cls : V → Fin 4} {G : SimpleGraph V} {r : Fin 4 → V}

theorem local_tri {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (hbc : G.Adj b c) (h1 : cls a ≠ cls b) (h2 : cls a ≠ cls c)
    (h3 : cls b ≠ cls c) : Realizes (coarse cls) G (triF a b c) 1 :=
  realizes_triangle hab hac hbc (classPart_not_mono _ _ _ h1 h2 h3)

theorem local_rect (hr : ∀ i, cls (r i) = i)
    (hrr : ∀ i j, i ≠ j → G.Adj (r i) (r j)) {a b : V}
    (hab : cls a ≠ cls b) (hedge : G.Adj a b)
    (ha : ∀ j, cls a ≠ j → G.Adj a (r j))
    (hb : ∀ j, cls b ≠ j → G.Adj b (r j)) :
    Realizes (coarse cls) G (rectE cls r s(a, b)) 4 := by
  obtain ⟨hki, hkj⟩ := third_ne (cls a) (cls b) hab
  let k := third (cls a) (cls b)
  have T1 := local_tri (cls := cls) (ha k hki.symm) hedge (hb k hkj.symm).symm
    (by simpa [k, hr] using hki.symm) hab (by simpa [k, hr] using hkj)
  have T2 := local_tri (cls := cls) (ha k hki.symm) (ha (cls b) hab) (hrr k (cls b) hkj)
    (by simpa [k, hr] using hki.symm) (by simpa [hr] using hab)
    (by simpa [k, hr] using hkj)
  have T3 := local_tri (cls := cls) (hrr (cls a) k hki.symm) (hb (cls a) hab.symm).symm
    (hb k hkj.symm).symm (by simpa [k, hr] using hki.symm)
    (by simpa [hr] using hab) (by simpa [k, hr] using hkj)
  have T4 := local_tri (cls := cls) (hrr (cls a) k hki.symm) (hrr (cls a) (cls b) hab)
    (hrr k (cls b) hkj) (by simpa [k, hr] using hki.symm)
    (by simpa [hr] using hab) (by simpa [k, hr] using hkj)
  refine (((T1.sub T2).sub T3).add T4).congr ?_
  funext f
  have key := rectangle_identity (fun x y => edgeInd x y f) a (r (cls a)) b
    (r (cls b)) (r k)
  simp only [rect] at key
  simp only [rectE, halfE_mk, repE_mk, Pi.add_apply, Pi.sub_apply, triF_apply]
  rw [← key, edgeInd_comm b (r (cls a))]
  simp only [edgeInd]
  ring

theorem local_star_pair (hr : ∀ i, cls (r i) = i)
    (hrr : ∀ i j, i ≠ j → G.Adj (r i) (r j)) {v : V}
    (hv : ∀ j, cls v ≠ j → G.Adj v (r j)) {x y : Fin 4}
    (hx : x ≠ cls v) (hy : y ≠ cls v) (hxy : x ≠ y) :
    Realizes (coarse cls) G (edgeInd v (r x) + edgeInd v (r y) -
      (edgeInd (r (cls v)) (r x) + edgeInd (r (cls v)) (r y))) 2 := by
  have T1 := local_tri (cls := cls) (hv x hx.symm) (hv y hy.symm) (hrr x y hxy)
    (by simpa [hr] using hx.symm) (by simpa [hr] using hy.symm)
    (by simpa [hr] using hxy)
  have T2 := local_tri (cls := cls) (hrr (cls v) x hx.symm) (hrr (cls v) y hy.symm)
    (hrr x y hxy) (by simpa [hr] using hx.symm) (by simpa [hr] using hy.symm)
    (by simpa [hr] using hxy)
  refine (T1.sub T2).congr ?_
  funext f
  have key := star_difference (fun a b => edgeInd a b f) v (r (cls v)) (r x) (r y)
  simp only [Pi.add_apply, Pi.sub_apply, triF_apply] at key ⊢
  rw [key]
  ring

theorem degVec_zero_outside {P : Finset (Sym2 V)} {v : V} (hv : v ∉ vertSet P)
    (j : Fin 4) : degVec cls P v j = 0 := by
  simp only [degVec, Finset.sum_apply]
  refine sum_eq_zero fun e he => ?_
  have hve : v ∉ e := by
    intro h
    exact hv (mem_filter.mpr ⟨mem_univ v, e, he, h⟩)
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ≠ v := by intro h; subst a; exact hve (by simp)
    have hb : b ≠ v := by intro h; subst b; exact hve (by simp)
    simp [degContrib_mk, ha, hb]

theorem local_star (hr : ∀ i, cls (r i) = i)
    (hrr : ∀ i j, i ≠ j → G.Adj (r i) (r j)) {P : Finset (Sym2 V)}
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) (hdiv : IsIntDiv cls F3 P)
    (hsrc : ∀ v ∈ vertSet P, ∀ j, cls v ≠ j → G.Adj v (r j)) (v : V) :
    Realizes (coarse cls) G (starE cls r P v) (3 * ∑ j, degVec cls P v j) := by
  by_cases hv : v ∈ vertSet P
  · have hself := degVec_self_eq_zero cls P hP v
    obtain ⟨h0, h1, h2, h01, h02, h12⟩ := others3_ne (cls v)
    obtain ⟨s, hs⟩ := sum_degVec_eq_two_mul hdiv v
    have hsum := sum_fin4_others (cls v) (degVec cls P v) hself
    have hs' := hsum ▸ hs
    have hbud := star_budget _ _ _ s hs'
    have hn₀ := degVec_nonneg cls P v (others3 (cls v) 0)
    have hn₁ := degVec_nonneg cls P v (others3 (cls v) 1)
    have hn₂ := degVec_nonneg cls P v (others3 (cls v) 2)
    have D₀₁ := (local_star_pair hr hrr (hsrc v hv) h0 h1 h01).smul
      (s - degVec cls P v (others3 (cls v) 2))
    have D₀₂ := (local_star_pair hr hrr (hsrc v hv) h0 h2 h02).smul
      (s - degVec cls P v (others3 (cls v) 1))
    have D₁₂ := (local_star_pair hr hrr (hsrc v hv) h1 h2 h12).smul
      (s - degVec cls P v (others3 (cls v) 0))
    refine ((D₀₁.add D₀₂).add D₁₂).congr ?_ |>.mono ?_
    · rw [starE, sum_fin4_others (cls v) _ (by rw [hself, zero_smul])]
      exact (star_combo _ _ _ _ _ _ _ _ s hs').symm
    · rw [hsum]
      rw [abs_of_nonneg hn₀, abs_of_nonneg hn₁, abs_of_nonneg hn₂] at hbud
      linarith
  · simpa [starE, degVec_zero_outside hv] using
      (Realizes.zero : Realizes (coarse cls) G 0 0)

theorem local_residual (hr : ∀ i, cls (r i) = i)
    (hrr : ∀ i j, i ≠ j → G.Adj (r i) (r j)) {P : Finset (Sym2 V)}
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) (hdiv : IsIntDiv cls F3 P) :
    Realizes (coarse cls) G (∑ e ∈ P, repE cls r e) (2 * P.card) := by
  have hsym : ∀ i j : Fin 4, edgeInd (r i) (r j) = edgeInd (r j) (r i) :=
    fun i j => edgeInd_comm _ _
  have hres : ∑ e ∈ P, repE cls r e =
      six (fun i j => edgeVec cls P i j • edgeInd (r i) (r j)) := by
    rw [six_edgeVec cls P hP _ hsym]
    refine sum_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b => rfl
  obtain ⟨a, b, c, d, h01, h02, h03, h12, h13, h23⟩ := edgeVec_F3_six hdiv
  have hbud := tetrahedron_budget _ _ _ _ _ _ a b c d h01 h02 h03 h12 h13 h23
  have hsix := edgeVec_six_sum cls P hP
  have hn : ∀ i j, |edgeVec cls P i j| = edgeVec cls P i j :=
    fun i j => abs_of_nonneg (edgeVec_nonneg cls P i j)
  have hne : ∀ x y : Fin 4, x ≠ y → cls (r x) ≠ cls (r y) := fun x y h => by
    rw [hr, hr]; exact h
  have T012 := (local_tri (cls := cls) (hrr 0 1 (by decide)) (hrr 0 2 (by decide))
    (hrr 1 2 (by decide)) (hne 0 1 (by decide)) (hne 0 2 (by decide))
    (hne 1 2 (by decide))).smul a
  have T013 := (local_tri (cls := cls) (hrr 0 1 (by decide)) (hrr 0 3 (by decide))
    (hrr 1 3 (by decide)) (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 1 3 (by decide))).smul b
  have T023 := (local_tri (cls := cls) (hrr 0 2 (by decide)) (hrr 0 3 (by decide))
    (hrr 2 3 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 2 3 (by decide))).smul c
  have T123 := (local_tri (cls := cls) (hrr 1 2 (by decide)) (hrr 1 3 (by decide))
    (hrr 2 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
    (hne 2 3 (by decide))).smul d
  refine (((T012.add T013).add T023).add T123).congr ?_ |>.mono ?_
  · rw [hres]
    funext f
    simp only [six, h01, h02, h03, h12, h13, h23, triF, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · simp only [six, hn] at hsix hbud
    simp only [mul_one]
    linarith

/-- Complete adjacency is needed only at the local gadgets, not in the whole host. -/
theorem local_certificate_realizes [DecidableRel G.Adj] (hr : ∀ i, cls (r i) = i)
    (hrr : ∀ i j, i ≠ j → G.Adj (r i) (r j)) {P : Finset (Sym2 V)}
    (hPG : P ⊆ G.edgeFinset) (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b)
    (hdiv : IsIntDiv cls F3 P)
    (hsrc : ∀ v ∈ vertSet P, ∀ j, cls v ≠ j → G.Adj v (r j)) :
    Realizes (coarse cls) G (ind P) (12 * P.card) := by
  have R1 := Realizes.sum P (rectE cls r) (fun _ => 4) fun e he => by
    induction e using Sym2.ind with
    | _ a b =>
      have ha : a ∈ vertSet P := mem_filter.mpr ⟨mem_univ a, s(a, b), he, by simp⟩
      have hb : b ∈ vertSet P := mem_filter.mpr ⟨mem_univ b, s(a, b), he, by simp⟩
      exact local_rect hr hrr (hP a b he) (SimpleGraph.mem_edgeFinset.mp (hPG he))
        (hsrc a ha) (hsrc b hb)
  have R2 := Realizes.sum univ (starE cls r P) (fun v => 3 * ∑ j, degVec cls P v j)
    fun v _ => local_star hr hrr hP hdiv hsrc v
  have R3 := local_residual hr hrr hP hdiv
  refine ((R1.add R2).add R3).congr (ind_decomposition r P).symm |>.mono ?_
  rw [← mul_sum, sum_degVec_one P, sum_const, nsmul_eq_mul]
  ring_nf
  rfl

/-- Discharge the local geometry using a bounded deletion budget. The size budget
depends on the source support; this is not a certificate for arbitrary quadratic residues. -/
theorem certificate_after_deletion (cls : V → Fin 4)
    (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
    (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b) (d : ℝ) (hd : 0 ≤ d)
    (hdel : ∀ v, ((univ.filter fun w => G₀.Adj v w ∧ ¬ G.Adj v w).card : ℝ) ≤ d)
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset)
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) (hdiv : IsIntDiv cls F3 P)
    (b : ℝ) (hsize : ∀ i, b ≤ ((ClassRepresentativesStage65.classSet cls i).card : ℝ))
    (hbudget : ((vertSet P).card + 3 : ℕ) * d < b) :
    Realizes (coarse cls) G (ind P) (12 * P.card) := by
  obtain ⟨r, hr, hsrc, hrr⟩ := ClassRepresentativesStage65.structural_representatives
    cls G₀ G hG₀ d hd hdel (vertSet P) b hsize hbudget
  exact local_certificate_realizes hr hrr hPG hP hdiv (fun v hv j hj => hsrc j v hv hj)

/-- The physical signed certificate in a subgraph of the four-class host. -/
theorem signed_certificate_after_deletion (cls : V → Fin 4)
    (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
    (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b) (hsub : G ≤ G₀)
    (d : ℝ) (hd : 0 ≤ d)
    (hdel : ∀ v, ((univ.filter fun w => G₀.Adj v w ∧ ¬ G.Adj v w).card : ℝ) ≤ d)
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset) (hdiv : IsIntDiv cls F3 P)
    (b : ℝ) (hsize : ∀ i, b ≤ ((ClassRepresentativesStage65.classSet cls i).card : ℝ))
    (hbudget : ((vertSet P).card + 3 : ℕ) * d < b) :
    ∃ (ι : Type u) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
      IsSignedCert (coarse cls) G P t c ∧ certWeight c ≤ 12 * P.card ∧
      ∀ j, IsCopy cls F3 G (t j) := by
  have hcross : ∀ a b, G.Adj a b → cls a ≠ cls b :=
    fun a b h => (hG₀ a b).mp (hsub h)
  have hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b :=
    fun a b he => hcross a b (SimpleGraph.mem_edgeFinset.mp (hPG he))
  obtain ⟨ι, hι, t, c, hc, hw⟩ :=
    (certificate_after_deletion cls G₀ G hG₀ d hd hdel P hPG hP hdiv b hsize hbudget).signedCert
  refine ⟨ι, hι, t, c, hc, hw, ?_⟩
  intro j
  have hs := (hc.1 j).1
  refine ⟨hs, ?_⟩
  obtain ⟨a, a', a'', ha, hb, hab, heq⟩ := card_eq_three.mp hs.card_eq
  rw [heq] at hs ⊢
  obtain ⟨h1, h2, h3⟩ := SimpleGraph.is3Clique_triple_iff.mp hs
  rw [map_three cls ha hb hab]
  exact distinct_mem_F3 _ _ _ (hcross _ _ h1) (hcross _ _ h2) (hcross _ _ h3)

end PartitionedTriangleAbsorption.ClassCertificateLocalStage67
