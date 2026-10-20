/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.StructuralF3.HostLayer
public import PartitionedTriangleAbsorption.StructuralF3.Numeric

/-! # The structural F3 shared refiner in the complete four-class host

`exists_structural_refiner`. Host: `cls : V → Fin 4`, `G.Adj a b ↔ cls a ≠ cls b`, every
class of size at least `γ n`. Parameters `0 < λ ≤ 1/64`, `32 λ ≤ γ`, `0 < ρ`, `2^42 ρ ≤ λ²`,
`ρ n ≥ 1`, `λ n ≥ 256` (all fixed before the reserve). For every reserve `X ⊆ E(G)` of maximum
degree at most `2ρn` there are a remainder `R ⊆ E(G) \ X` and a library of pieces
`B j ⊆ X ∪ R`, all fixed before the leftover, such that

* every leftover `L ⊆ X` with the **structural** divisibility `IsIntDiv cls F3 L` is exactly
  partitioned, together with `R`, by pairwise disjoint library pieces
  (`RefinerAssembly.RefinesReserve (p := cls) (F := F3)`);
* every piece is structurally divisible, `IsIntDiv cls F3 (B j)`, with at most `1050` edges;
* `Δ(R) ≤ 8 λ n`, the library has at most `2^35 ρ n²` pieces, and every vertex has total
  library incidence at most `4200 λ n`.

Construction (three fixed layers, all before `L`):

1. the ordinary (one-part) refiner of `UniversalRefiner`, re-run for anti-edge constant `2γ`
   (`exists_universal_refiner_alpha`): even pieces of at most `42` edges;
2. a physical charge layer for `chi3a`, tokens = rectangles of kinds `2` / `1+3`;
3. a physical charge layer for `chi3b`, tokens = rectangles of kinds `3` / `1+2`,
   which preserves `chi3a = 0`.

By `isIntDiv_F3_iff`, even cross-class pieces with both charges zero are exactly the
structurally divisible ones. This result is restricted to the exactly complete four-class host
and to the structural family F3; it is not Theorem 13.16 and does not supply the private
absorbers or the fractional input.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3

open Finset AntiEdgeSelection TypedApplicationLinks TypedRefinerCharge TypedRefinerF0 OnePart

/-- Library indices of the structural refiner. -/
abbrev SIdx := JIdx (JIdx (ℕ × Bool × Fin 3 × Fin 3))

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem root_nat (cls : V → Fin 4) (γ lam rho : ℝ)
    (hcls : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (hlam : 0 < lam) (hlamγ : 32 * lam ≤ γ) (hrho : 0 ≤ rho) (hscale : 2 ^ 42 * rho ≤ lam ^ 2)
    (hn : (0 : ℝ) < Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (N : ℕ)
    (hN : (N : ℝ) ≤ 2 ^ 32 * rho * (Fintype.card V : ℝ) ^ 2) (r : ℕ)
    (hr : lam * Fintype.card V < r + 1) (i : Fin 4) :
    4 * (2 * N / (classSet cls i).card + 1) ≤ r := by
  have h := token_root_real N (classSet cls i).card (Fintype.card V) γ lam rho hlam hlamγ hrho
    hscale hn hn2 hN (hcls i)
  have hdiv : (((2 * N / (classSet cls i).card : ℕ)) : ℝ) ≤
      ((2 * N : ℕ) : ℝ) / ((classSet cls i).card : ℝ) := Nat.cast_div_le
  have hcast : (((4 * (2 * N / (classSet cls i).card + 1) : ℕ)) : ℝ) < (r : ℝ) + 1 := by
    push_cast at hdiv ⊢
    linarith
  have : 4 * (2 * N / (classSet cls i).card + 1) < r + 1 := by exact_mod_cast hcast
  omega

theorem sum_le_mul_card {ι : Type*} (s : Finset ι) (f : ι → ℕ) (k : ℕ)
    (h : ∀ i ∈ s, f i ≤ k) : ∑ i ∈ s, f i ≤ k * s.card := by
  refine (sum_le_sum h).trans ?_
  rw [sum_const, smul_eq_mul, mul_comm]

/-- **The structural F3 shared refiner in the complete four-class host.** -/
theorem exists_structural_refiner (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) (γ lam rho : ℝ)
    (hcls : ∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => cls v = i).card : ℝ))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hlamγ : 32 * lam ≤ γ) (hrho : 0 < rho)
    (hscale : 2 ^ 42 * rho ≤ lam ^ 2) (hn1 : 1 ≤ rho * Fintype.card V)
    (hn2 : 256 ≤ lam * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (indices : Finset SIdx) (B : SIdx → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := cls) (F := F3) indices B X R ∧
      (∀ j ∈ indices, B j ⊆ X ∪ R ∧ IsIntDiv cls F3 (B j) ∧ (B j).card ≤ 1050) ∧
      DegBounded R (8 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 2 ^ 35 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ indices, incidentLoad (B j) v : ℕ) : ℝ) ≤ 4200 * lam * Fintype.card V := by
  classical
  set n := Fintype.card V with hn
  have hcls' : ∀ i, γ * n ≤ ((classSet cls i).card : ℝ) := hcls
  have hnpos : (0 : ℝ) < n := by
    by_contra h
    push Not at h
    nlinarith
  have hscale24 : 2 ^ 24 * rho ≤ lam ^ 2 := by nlinarith
  have hrholam : 2 * rho * n ≤ lam * n / 1024 := by
    have : 2 * rho * 1024 ≤ lam := by nlinarith
    nlinarith
  have hpos : ∀ i, 0 < (classSet cls i).card := by
    intro i
    have h1 := hcls' i
    have h2 : (0 : ℝ) < γ * n := by nlinarith
    have : (0 : ℝ) < (classSet cls i).card := h2.trans_le h1
    exact_mod_cast this
  -- quota and root bound
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = ⌊lam * n / 64⌋₊ := ⟨_, rfl⟩
  have hqhi : (q : ℝ) ≤ lam * n / 64 := by rw [hqdef]; exact Nat.floor_le (by positivity)
  have hqlo : lam * n / 128 ≤ (q : ℝ) := by
    have := Nat.lt_floor_add_one (lam * n / 64)
    rw [hqdef]
    linarith
  have hq : 0 < q := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = ⌊lam * n⌋₊ := ⟨_, rfl⟩
  have hrhi : (r : ℝ) ≤ lam * n := by rw [hrdef]; exact Nat.floor_le (by positivity)
  have hrlo : lam * n < r + 1 := by rw [hrdef]; exact Nat.lt_floor_add_one _
  have hrq : ((r + 2 * q : ℕ) : ℝ) ≤ lam * n + lam * n / 32 := by push_cast; linarith
  -- stage A: the ordinary refiner
  obtain ⟨I0, P0, R0, hR0G, hR0X, href0, hpc0, hR0deg, hcard0, hinc0⟩ :=
    exists_universal_refiner_alpha G X hXG lam rho hlam hlam64 hrho hscale24 hn1 hn2 hX (2 * γ)
      (by linarith) (antiEdgeful_part1_host cls G hG γ hcls)
  let E0 : PredRefiner (ℕ × Bool × Fin 3 × Fin 3) X (IsIntDiv part1 triFam) :=
    { lib := I0
      P := P0
      R0 := R0
      loopP := fun j hj => (hpc0 j hj).2.1
      evenP := fun j hj => (hpc0 j hj).2.2.1
      subP := fun j hj => by rw [union_comm]; exact (hpc0 j hj).1
      disjRX := hR0X
      refines := href0 }
  have hR0XG : R0 ∪ X ⊆ G.edgeFinset := union_subset hR0G hXG
  set L0 := I0.card with hL0def
  have hL0 : (L0 : ℝ) ≤ 1224 * rho * (n : ℝ) ^ 2 := hcard0
  -- first charge layer
  have hcross0 : ∀ i ∈ E0.lib, CrossClass cls (E0.P i) := fun i hi =>
    crossClass_of_subset_edges hG ((E0.subP i hi).trans hR0XG)
  have hdvdA : ∀ i ∈ E0.lib, (4 : ℤ) ∣ charge chi3a cls (E0.P i) := fun i hi =>
    four_dvd_chi3a (hcross0 i hi) (E0.evenP i hi)
  have habsA : ∀ i ∈ E0.lib, (charge chi3a cls (E0.P i) / 4).natAbs ≤ 21 := by
    intro i hi
    have h1 := two_mul_natAbs_div_four_le chi3a_bound cls (E0.P i) (hdvdA i hi)
    have h2 := (hpc0 i hi).2.2.2.2
    change (P0 i).card ≤ 42 at h2
    change 2 * (charge chi3a cls (P0 i) / 4).natAbs ≤ (P0 i).card at h1
    change (charge chi3a cls (P0 i) / 4).natAbs ≤ 21
    omega
  have hsumA : ∑ i ∈ E0.lib, (charge chi3a cls (E0.P i) / 4).natAbs ≤ 21 * L0 :=
    sum_le_mul_card _ _ _ habsA
  have hNAR : ((189 * L0 : ℕ) : ℝ) ≤ 2 ^ 32 * rho * (n : ℝ) ^ 2 := by
    push_cast; nlinarith
  have hdA : DegBounded (E0.R0 ∪ X) (4 * lam * n + 2 * rho * n) := degBounded_union hR0deg hX
  have cv := c4charge_values
  obtain ⟨SA, tA, E1, hR1, hTAG, hTAdis, hTAload, hchgA, -, hcardA, hloadA, hlibA⟩ :=
    host_layer cls G hG γ hcls' hpos E0 RefinerAssembly.empty_isIntDiv
      (4 * lam * n + 2 * rho * n) hdA chi3a chi3b hdvdA 2 1 3 (by decide) (by decide)
      (by decide) cv.2.2.1 (by linarith [cv.1, cv.2.2.2.2.1]) cv.2.2.2.1
      (by linarith [cv.2.1, cv.2.2.2.2.2]) (189 * L0) (by omega) q r hq
      (root_nat cls γ lam rho hcls' hlam hlamγ hrho.le hscale hnpos hn2 _ hNAR r hrlo)
      (token_budget_real _ _ _ _ _ _ _ _ hlam hlamγ hrho.le hscale hnpos hNAR hqlo hqhi hrhi
        (by linarith))
  -- the remainder after the first layer
  set TA := SA.biUnion tA with hTA
  have hE1R : E1.R0 = R0 ∪ TA := hR1
  have hR1XG : E1.R0 ∪ X ⊆ G.edgeFinset := by
    rw [hE1R]; exact union_subset (union_subset hR0G hTAG) hXG
  have hTAdeg : DegBounded TA ((r + 2 * q : ℕ) : ℝ) := fun v => by exact_mod_cast hTAload v
  have hdB : DegBounded (E1.R0 ∪ X) (4 * lam * n + 2 * rho * n + ((r + 2 * q : ℕ) : ℝ)) := by
    have h := degBounded_union hdA hTAdeg
    rw [hE1R]
    have heq : R0 ∪ TA ∪ X = (E0.R0 ∪ X) ∪ TA := by
      ext e; simp only [mem_union]; change _ ↔ (e ∈ R0 ∨ e ∈ X) ∨ e ∈ TA; tauto
    rw [heq]; exact h
  -- second charge layer
  have hcross1 : ∀ j ∈ E1.lib, CrossClass cls (E1.P j) := fun j hj =>
    crossClass_of_subset_edges hG ((E1.subP j hj).trans hR1XG)
  have hdvdB : ∀ j ∈ E1.lib, (4 : ℤ) ∣ charge chi3b cls (E1.P j) := fun j hj =>
    four_dvd_chi3b (hcross1 j hj) (E1.evenP j hj)
  have hsize1 : ∀ j ∈ E1.lib, (E1.P j).card ≤ 210 := by
    intro j hj
    rcases hcardA j hj with h | ⟨i, hi, h⟩
    · omega
    · have h1 := habsA i hi
      have h2 := (hpc0 i hi).2.2.2.2
      change (P0 i).card ≤ 42 at h2
      change (E1.P j).card ≤ (P0 i).card + 8 * (charge chi3a cls (P0 i) / 4).natAbs at h
      change (charge chi3a cls (P0 i) / 4).natAbs ≤ 21 at h1
      omega
  have habsB : ∀ j ∈ E1.lib, (charge chi3b cls (E1.P j) / 4).natAbs ≤ 105 := by
    intro j hj
    have h1 := two_mul_natAbs_div_four_le chi3b_bound cls (E1.P j) (hdvdB j hj)
    have h2 := hsize1 j hj
    omega
  set L1 := E1.lib.card with hL1def
  have hL1 : L1 ≤ 2038 * L0 := by
    have := hlibA
    change E1.lib.card ≤ L0 + 97 * _ at this
    omega
  have hsumB : ∑ j ∈ E1.lib, (charge chi3b cls (E1.P j) / 4).natAbs ≤ 105 * L1 :=
    sum_le_mul_card _ _ _ habsB
  have hNBR : ((945 * L1 : ℕ) : ℝ) ≤ 2 ^ 32 * rho * (n : ℝ) ^ 2 := by
    have : (L1 : ℝ) ≤ 2038 * L0 := by exact_mod_cast hL1
    push_cast; nlinarith
  obtain ⟨SB, tB, E2, hR2, hTBG, hTBdis, hTBload, hchgB, hchgB', hcardB, hloadB, hlibB⟩ :=
    host_layer cls G hG γ hcls' hpos E1 ⟨RefinerAssembly.empty_isIntDiv, charge_empty _ _⟩
      _ hdB chi3b chi3a hdvdB 3 1 2 (by decide) (by decide) (by decide) cv.2.2.2.2.2
      (by linarith [cv.2.1, cv.2.2.2.1]) cv.2.2.2.2.1 (by linarith [cv.1, cv.2.2.1])
      (945 * L1) (by omega) q r hq
      (root_nat cls γ lam rho hcls' hlam hlamγ hrho.le hscale hnpos hn2 _ hNBR r hrlo)
      (token_budget_real _ _ _ _ _ _ _ _ hlam hlamγ hrho.le hscale hnpos hNBR hqlo hqhi hrhi
        (by linarith))
  set TB := SB.biUnion tB with hTB
  have hE2R : E2.R0 = R0 ∪ TA ∪ TB := by rw [hR2, hE1R]
  refine ⟨E2.lib, E2.P, E2.R0, ?_, E2.disjRX, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE2R]; exact union_subset (union_subset hR0G hTAG) hTBG
  · refine E2.refinesReserve fun L hL hdiv => ?_
    have hcr : CrossClass cls L := crossClass_of_subset_edges hG (hL.trans hXG)
    refine ⟨⟨(isIntDiv_part1_iff L hcr.loopless).mpr (even3_of_isIntDiv_F3 hcr hdiv),
      charge_eq_zero_of_isIntDiv kills_chi3a hdiv⟩, charge_eq_zero_of_isIntDiv kills_chi3b hdiv⟩
  · intro j hj
    have hsub : E2.P j ⊆ E2.R0 ∪ X := E2.subP j hj
    have hR2XG : E2.R0 ∪ X ⊆ G.edgeFinset := by
      rw [hE2R]; exact union_subset (union_subset (union_subset hR0G hTAG) hTBG) hXG
    have hcr : CrossClass cls (E2.P j) := crossClass_of_subset_edges hG (hsub.trans hR2XG)
    refine ⟨by rw [union_comm]; exact hsub, (isIntDiv_F3_iff hcr).mpr
      ⟨E2.evenP j hj, hchgB' hchgA j hj, hchgB j hj⟩, ?_⟩
    rcases hcardB j hj with h | ⟨i, hi, h⟩
    · omega
    · have h1 := habsB i hi
      have h2 := hsize1 i hi
      omega
  · intro v
    rw [hE2R]
    have h1 := ModThreeLayer.incidentLoad_union_le (R0 ∪ TA) TB v
    have h2 := ModThreeLayer.incidentLoad_union_le R0 TA v
    have h3 : (incidentLoad R0 v : ℝ) ≤ 4 * lam * n := hR0deg v
    have h4 := hTAload v
    have h5 := hTBload v
    have h6 : ((incidentLoad (R0 ∪ TA ∪ TB) v : ℕ) : ℝ) ≤
        (incidentLoad R0 v : ℝ) + ((r + 2 * q : ℕ) : ℝ) + ((r + 2 * q : ℕ) : ℝ) := by
      have : incidentLoad (R0 ∪ TA ∪ TB) v ≤ incidentLoad R0 v + (r + 2 * q) + (r + 2 * q) := by
        omega
      exact_mod_cast this
    change ((incidentLoad (R0 ∪ TA ∪ TB) v : ℕ) : ℝ) ≤ _
    linarith
  · have h1 : E2.lib.card ≤ 10186 * L1 := by
      have := hlibB
      change E2.lib.card ≤ L1 + 97 * _ at this
      omega
    have h2 : (E2.lib.card : ℝ) ≤ 10186 * 2038 * L0 := by
      have : E2.lib.card ≤ 10186 * 2038 * L0 := by omega
      exact_mod_cast this
    nlinarith
  · intro v
    have h1 := hloadB v
    have h2 := hloadA v
    have h3 : ((∑ i ∈ I0, incidentLoad (P0 i) v : ℕ) : ℝ) ≤ 4096 * lam * n := hinc0 v
    have h4 : ∑ j ∈ E2.lib, incidentLoad (E2.P j) v ≤
        ∑ i ∈ I0, incidentLoad (P0 i) v + 88 * (r + 2 * q) := by
      have h0 : ∑ i ∈ E0.lib, incidentLoad (E0.P i) v = ∑ i ∈ I0, incidentLoad (P0 i) v := rfl
      omega
    have h5 : ((∑ j ∈ E2.lib, incidentLoad (E2.P j) v : ℕ) : ℝ) ≤
        ((∑ i ∈ I0, incidentLoad (P0 i) v : ℕ) : ℝ) + 88 * ((r + 2 * q : ℕ) : ℝ) := by
      exact_mod_cast h4
    linarith

end PartitionedTriangleAbsorption.StructuralF3
