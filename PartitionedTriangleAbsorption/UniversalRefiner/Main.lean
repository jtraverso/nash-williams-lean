/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Loads
public import PartitionedTriangleAbsorption.RefinerConstructionBudget
public import Mathlib.Data.Nat.Log

/-!
# The universal bounded ordinary refiner (one-part triangle family)

`exists_universal_refiner`: for a finite host `G` on `n` vertices of minimum degree at least
`3n/4`, a reserve `X ⊆ E(G)` of maximum degree at most `2ρn`, and parameters
`0 < λ ≤ 1/64`, `0 < ρ`, `2^24 ρ ≤ λ²`, `ρn ≥ 1`, `λn ≥ 256`, there is one fixed library
`P` (indexed by `indices`) and one fixed remainder `R ⊆ E(G) \ X` such that every integrally
divisible `L ⊆ X` is exactly partitioned by `R ∪ L`-covering disjoint pieces of the library
(`RefinerAssembly.RefinesReserve`), with bounded pieces, `Δ(R) ≤ 4λn`,
`|indices| ≤ 1224 ρ n²`, and total incidence at most `4096 λn` at every vertex.

The hub hierarchy is the binary heap of `UniversalRefiner.Heap` with
`2^p = 2^⌊log₂ ⌊128ρn/λ⌋⌋`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection OnePart

/-- Choice of the number `p` of interior hub levels. -/
theorem exists_heap_height (n : ℕ) (lam rho : ℝ) (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64)
    (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hn1 : 1 ≤ rho * n) :
    ∃ p : ℕ, 1 ≤ p ∧ 2 ^ (p + 1) ≤ n ∧ 64 * rho * n ≤ lam * 2 ^ p ∧
      lam * 2 ^ p ≤ 128 * rho * n := by
  set y : ℝ := 128 * rho * n / lam with hy
  have hy0 : 0 ≤ y := by positivity
  have hy8 : 8192 ≤ y := by
    rw [hy, le_div_iff₀ hlam]
    nlinarith
  set m := ⌊y⌋₊ with hm
  have hm2 : 2 ≤ m := Nat.le_floor (by norm_num; linarith)
  set p := Nat.log 2 m with hp
  have hp1 : 1 ≤ p := Nat.log_pos (by norm_num) hm2
  have hpow : 2 ^ p ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hlt : m < 2 ^ (p + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hpowR : (2 : ℝ) ^ p ≤ y := by
    calc (2 : ℝ) ^ p = ((2 ^ p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (m : ℝ) := by exact_mod_cast hpow
      _ ≤ y := Nat.floor_le hy0
  have hltR : y < 2 * (2 : ℝ) ^ p := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((2 ^ (p + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at h2
    rw [pow_succ] at h2
    linarith
  have hlam2 : lam ^ 2 ≤ lam / 64 := by nlinarith
  have hrl : 256 * rho ≤ lam := by nlinarith
  refine ⟨p, hp1, ?_, ?_, ?_⟩
  · have : (2 : ℝ) ^ (p + 1) ≤ n := by
      rw [pow_succ]
      have h1 : 2 * y ≤ n := by
        rw [hy, mul_div_assoc', div_le_iff₀ hlam]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      linarith
    exact_mod_cast this
  · have := (div_lt_iff₀ hlam).mp (show 128 * rho * n / lam < 2 * 2 ^ p by rw [← hy]; exact hltR)
    linarith
  · have := (le_div_iff₀ hlam).mp (show (2 : ℝ) ^ p ≤ 128 * rho * n / lam by rw [← hy]; exact hpowR)
    linarith


/-- Real estimate for the size of the hierarchy. -/
theorem size_bound_real (xc S p n : ℕ) (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hS : S ≤ xc + 2 ^ (p + 1) * 2 ^ p)
    (hX : (xc : ℝ) ≤ rho * (n : ℝ) ^ 2) (hP2 : lam * 2 ^ p ≤ 128 * rho * n) :
    (S : ℝ) ≤ 2 * rho * (n : ℝ) ^ 2 := by
  set P2 : ℝ := (2 : ℝ) ^ p with hP2def
  have h1 : (S : ℝ) ≤ xc + 2 * P2 * P2 := by
    have : ((xc + 2 ^ (p + 1) * 2 ^ p : ℕ) : ℝ) = xc + 2 * P2 * P2 := by
      push_cast; rw [pow_succ]; ring
    rw [← this]; exact_mod_cast hS
  have h2'' : 2 * P2 * P2 * lam ^ 2 ≤ rho * (n : ℝ) ^ 2 * lam ^ 2 := by
    have hlp0 : 0 ≤ lam * P2 := by positivity
    have hsq : (lam * P2) ^ 2 ≤ (128 * rho * n) ^ 2 := pow_le_pow_left₀ hlp0 hP2 2
    nlinarith
  have h3 : 2 * P2 * P2 ≤ rho * (n : ℝ) ^ 2 :=
    le_of_mul_le_mul_right h2'' (by positivity)
  linarith

/-- Real estimate for the root load. -/
theorem root_bound_real (n p D N : ℕ) (lam rho : ℝ) (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64)
    (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hn2 : 256 ≤ lam * n)
    (hnR : (4 : ℝ) ≤ n) (hP1 : 64 * rho * n ≤ lam * 2 ^ p) (hP2 : lam * 2 ^ p ≤ 128 * rho * n)
    (hDR : (D : ℝ) ≤ 2 * rho * n) (hNR : (N : ℝ) ≤ 34 * rho * (n : ℝ) ^ 2 + 2) :
    ((2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) + 8 +
      12 * ((N + 1) / n + 1) : ℕ) : ℝ) ≤ lam * n := by
  set P2 : ℝ := (2 : ℝ) ^ p with hP2def
  have hnpos : (0 : ℝ) < n := by linarith
  have hlam2 : lam ^ 2 ≤ lam / 64 := by nlinarith
  have hrl : 2 ^ 30 * rho ≤ lam := by nlinarith
  have hrn : rho * n ≤ lam * n / 2 ^ 30 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  set A : ℝ := ((n / 2 ^ p : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hAP : A * P2 ≤ n := by
    have : ((n / 2 ^ p * 2 ^ p : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n (2 ^ p)
    push_cast at this; exact this
  have hAD : A * (2 * rho * n) ≤ lam * n / 32 := by
    rw [le_div_iff₀ (by norm_num)]
    have : A * (64 * rho * n) ≤ A * (lam * P2) := mul_le_mul_of_nonneg_left hP1 hA0
    nlinarith
  set B : ℝ := (((N + 1) / n : ℕ) : ℝ) with hB
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hBn : B * n ≤ N + 1 := by
    have : (((N + 1) / n * n : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (N + 1) n
    push_cast at this; exact this
  have hBR : B ≤ 34 * rho * n + 1 := by
    have e : (34 * rho * n + 1) * n = 34 * rho * (n : ℝ) ^ 2 + n := by ring
    have : B * n ≤ (34 * rho * n + 1) * n := by rw [e]; linarith
    exact le_of_mul_le_mul_right this hnpos
  have hP44 : 44 * P2 ≤ lam * n / 2000 := by
    rw [le_div_iff₀ (by norm_num)]
    have h1 : lam * (44 * P2 * 2000) ≤ 11264000 * (rho * n) := by linarith
    have h2' : 11264000 * rho ≤ lam * lam := by nlinarith
    have h3 : 11264000 * (rho * n) ≤ lam * (lam * n) := by
      have := mul_le_mul_of_nonneg_right h2' hnpos.le
      linarith
    exact le_of_mul_le_mul_left (h1.trans h3) hlam
  have hrcast : ((2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) + 8 +
      12 * ((N + 1) / n + 1) : ℕ) : ℝ) =
      2 * D + 10 * ((A + 1) * D) + 22 * (2 * P2) + 8 + 12 * (B + 1) := by
    simp only [hA, hB, hP2def]
    push_cast
    ring
  rw [hrcast]
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have h1 : (A + 1) * D ≤ lam * n / 32 + 2 * rho * n := by
    have : (A + 1) * D ≤ (A + 1) * (2 * rho * n) := mul_le_mul_of_nonneg_left hDR (by linarith)
    have e : (A + 1) * (2 * rho * n) = A * (2 * rho * n) + 2 * rho * n := by ring
    linarith
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The universal bounded ordinary refiner.** -/
theorem exists_universal_refiner (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset) (lam rho : ℝ)
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (hX : DegBounded X (2 * rho * Fintype.card V))
    (hmin : ∀ u, 3 / 4 * (Fintype.card V : ℝ) ≤ ((univ.filter (G.Adj u)).card : ℝ)) :
    ∃ (indices : Finset (ℕ × Bool × Fin 3 × Fin 3))
      (P : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := part1) (F := triFam) indices P X R ∧
      (∀ j ∈ indices, P j ⊆ X ∪ R ∧ (∀ e ∈ P j, ¬ e.IsDiag) ∧
        (∀ v, Even (incidentLoad (P j) v)) ∧ 3 ∣ (P j).card ∧ (P j).card ≤ 42) ∧
      DegBounded R (4 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ indices, incidentLoad (P j) v : ℕ) : ℝ) ≤ 4096 * lam * Fintype.card V := by
  set n := Fintype.card V with hn
  obtain ⟨p, hp1, h2, hP1, hP2⟩ := exists_heap_height n lam rho hlam hlam64 hrho hscale hn1
  set P2 : ℝ := (2 : ℝ) ^ p with hP2def
  have hP2pos : 0 < P2 := by positivity
  have hn4 : 4 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨u0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hlam2 : lam ^ 2 ≤ lam / 64 := by nlinarith
  have hrl : 2 ^ 30 * rho ≤ lam := by nlinarith
  have hrn : rho * n ≤ lam * n / 2 ^ 30 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hrn2 : 1 ≤ rho * (n : ℝ) ^ 2 := by nlinarith
  -- the construction
  set hmap := heapMap u0 p with hhmap
  set mdr := mdRoots u0 with hmdr
  set adr : V × V := (vtx u0 0, vtx u0 1) with hadr
  have had : adr.1 ≠ adr.2 := by
    intro h
    have := congrArg idx h
    simp only [hadr] at this
    rw [idx_vtx u0 (by omega), idx_vtx u0 (by omega)] at this
    exact absurd this (by norm_num)
  have hXloop : ∀ e ∈ X, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG he))
  set D := ⌊2 * rho * n⌋₊ with hDdef
  have hD : ∀ u, (vChain X u).card ≤ D := fun u => Nat.le_floor (hX u)
  have hDR : (D : ℝ) ≤ 2 * rho * n := Nat.floor_le (by positivity)
  -- size of the reserve
  have hXcard : (X.card : ℝ) ≤ rho * (n : ℝ) ^ 2 := by
    have h1 := sum_vChain_card_eq X hXloop
    have h2' : ∀ u, ((vChain X u).card : ℝ) ≤ 2 * rho * n := fun u => hX u
    have h3 : ((∑ u, (vChain X u).card : ℕ) : ℝ) ≤ n * (2 * rho * n) := by
      push_cast
      calc ∑ u, ((vChain X u).card : ℝ) ≤ ∑ _u : V, 2 * rho * n := sum_le_sum fun u _ => h2' u
        _ = n * (2 * rho * n) := by rw [sum_const, card_univ, nsmul_eq_mul]
    rw [h1] at h3
    push_cast at h3
    nlinarith
  -- size of the hierarchy
  set S := ∑ l ∈ range (p + 1), (links X hmap l).card with hSdef
  have hS : S ≤ X.card + 2 ^ (p + 1) * 2 ^ p := heap_sum_links h2
  have hSR : (S : ℝ) ≤ 2 * rho * (n : ℝ) ^ 2 :=
    size_bound_real X.card S p n lam rho hlam hrho hscale hS hXcard hP2
  set N := (theLib X hmap (p + 1) mdr adr).card with hNdef
  have hN : N ≤ 17 * S + 2 := card_theLib_le X hmap (p + 1) mdr adr
  have hNR : (N : ℝ) ≤ 34 * rho * (n : ℝ) ^ 2 + 2 := by
    have : (N : ℝ) ≤ 17 * S + 2 := by exact_mod_cast hN
    linarith
  have hM : (theReqs X hmap (p + 1) mdr adr).card ≤ 110 * S + 16 :=
    card_theReqs_le X hmap (p + 1) mdr adr
  have hMR : ((theReqs X hmap (p + 1) mdr adr).card : ℝ) ≤ 512 * rho * (n : ℝ) ^ 2 := by
    have : ((theReqs X hmap (p + 1) mdr adr).card : ℝ) ≤ 110 * S + 16 := by exact_mod_cast hM
    nlinarith
  -- root load
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = 2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) + 8 +
    12 * ((N + 1) / n + 1) := ⟨_, rfl⟩
  have hroot : ∀ x, rootLoad (theReqs X hmap (p + 1) mdr adr)
      (fun r => (rootPair hmap mdr adr r).1) (fun r => (rootPair hmap mdr adr r).2) x ≤ r := by
    intro x
    have h1 : rootLoad (theReqs X hmap (p + 1) mdr adr)
        (fun r => (rootPair hmap mdr adr r).1) (fun r => (rootPair hmap mdr adr r).2) x ≤
        ∑ l ∈ range (p + 1), (2 * (vChain (links X hmap l) x).card +
          10 * hubWeight (links X hmap l) (hmap l) x) + 8 + 12 * ((N + 1) / n + 1) :=
      rootLoad_theReqs_le u0 (by omega) X hmap (p + 1) adr x
    have h3 : ∑ l ∈ range (p + 1), (2 * (vChain (links X hmap l) x).card +
          10 * hubWeight (links X hmap l) (hmap l) x) ≤
        2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) :=
      heap_root (u0 := u0) (X := X) h2 D hD x
    omega
  have hrR : (r : ℝ) ≤ lam * n := by
    rw [hrdef]
    exact root_bound_real n p D N lam rho hlam hlam64 hrho hscale hn2 hnR hP1 hP2 hDR hNR
  -- quota and budget
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = ⌊lam * n / 64⌋₊ := ⟨_, rfl⟩
  have hqhi : (q : ℝ) ≤ lam * n / 64 := by rw [hqdef]; exact Nat.floor_le (by positivity)
  have hqlo : lam * n / 128 ≤ (q : ℝ) := by
    have := Nat.lt_floor_add_one (lam * n / 64)
    rw [hqdef]
    linarith
  have hq : 0 < q := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  have hbudget : ((theReqs X hmap (p + 1) mdr adr).card : ℝ) / q +
      2 * (2 * rho * n + r + 2 * q) < 1 / 2 * (n : ℝ) := by
    have hr3 : (r : ℝ) ≤ 3 * lam * n := by linarith
    have hsc : 16777216 * rho ≤ lam * lam := by nlinarith
    generalize ((theReqs X hmap (p + 1) mdr adr).card : ℝ) = Mv at hMR ⊢
    generalize (r : ℝ) = rv at hr3 ⊢
    generalize (q : ℝ) = qv at hqlo hqhi ⊢
    generalize (n : ℝ) = nv at hnpos hMR hr3 hqlo hqhi ⊢
    have := RefinerConstructionBudget.physical_family_budget lam rho nv Mv (2 * rho * nv) rv qv
      hlam hlam64 hrho.le hsc hnpos hMR le_rfl hr3 hqlo hqhi
    linarith only [this]
  obtain ⟨indices, P, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    producer_of_hierarchy G X hXG hmap (p + 1) (links_last h2) (heap_fix hp1 h2) mdr
      (mdRoots_ne u0 (by omega)) adr had (antiEdgeful_of_minDegree G hmin) (2 * rho * n) hX
      r q hq hroot hbudget
  refine ⟨indices, P, R, hRG, hRX, href, hpieces, ?_, ?_, ?_⟩
  · intro v
    have h1 : ((incidentLoad R v : ℕ) : ℝ) ≤ r + 2 * q := by exact_mod_cast hRdeg v
    change ((incidentLoad R v : ℕ) : ℝ) ≤ _
    linarith only [h1, hrR, hqhi, hn2]
  · have h1 : (indices.card : ℝ) ≤ 18 * N := by exact_mod_cast hcard
    linarith only [h1, hNR, hrn2]
  · intro v
    have h1 : ((∑ j ∈ indices, incidentLoad (P j) v : ℕ) : ℝ) ≤
        594 * incidentLoad X v + 630 * (r + 2 * q) := by exact_mod_cast hinc v
    have h2' : (incidentLoad X v : ℝ) ≤ 2 * rho * n := hX v
    have h3 : 594 * (incidentLoad X v : ℝ) ≤ 1188 * (rho * n) := by linarith only [h2']
    have h4 : 630 * ((r : ℝ) + 2 * q) ≤ 650 * (lam * n) := by linarith only [hrR, hqhi, hn2]
    have h5 : 1188 * (rho * n) ≤ lam * n := by linarith only [hrn, hn2]
    linarith only [h1, h3, h4, h5, hn2]

end PartitionedTriangleAbsorption.UniversalRefiner
