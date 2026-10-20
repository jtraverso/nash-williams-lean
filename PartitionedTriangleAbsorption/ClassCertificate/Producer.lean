/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassCertificate.Extraction
public import PartitionedTriangleAbsorption.IntegerCertificate.Assembly

/-! # Structural-lattice physical certificates in the complete four-class host

Let `cls : V → Fin 4` with representatives `r i` (`cls (r i) = i`), and let `G` be the
complete four-class graph, `G.Adj u v ↔ cls u ≠ cls v`. For every `P ⊆ E(G)` with the
**structural** divisibility `IsIntDiv cls F3 P`, the indicator of `P` is an integer
combination of actual triangles of `G` with total absolute coefficient at most `12 |P|`,
equal at every `Sym2` coordinate. Every triangle has three distinct classes, so it is an F3
copy for `cls` and an F0 copy for the coarse labels `classPart ∘ cls`.

The proof follows the three physical stages of the Stage65 note:

1. `realizes_rectE`: per source edge `uv`, the rectangle
   `[uv] - [u r_j] - [r_i v] + [r_i r_j]` costs `4` (four triangles through `r_k`).
2. `realizes_starE`: per vertex `v` of class `i`, the star `Σ_j d_j ([v r_j] - [r_i r_j])`
   costs at most `3 Σ_j d_j`, using the even degree from `IsIntDiv` and the star system of
   `ClassLatticeStage65`; the source signed degrees `d_j = degVec cls P v j` are used.
3. `realizes_residual`: the remaining representative edges carry the six class-pair counts;
   the F3 edge equation and `tetrahedron_budget` give cost at most `2 |P|`.

`ind_decomposition` is the exact identity `ind P = Σ rect + Σ star + residual`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassCertificate

open Finset TypedApplicationLinks SignedCertificate IntegerCertificate
open LocalCycleTransportStage62 ParityBalanceStage63 ClassLatticeStage65
open MultipartiteBoundaryStage64

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Coarse labels: structural classes `0, 1` in part `0`, classes `2, 3` in part `1`. -/
def coarse (cls : V → Fin 4) (v : V) : Fin 2 := classPart (cls v)

/-- A third class distinct from two given classes. -/
def third (i j : Fin 4) : Fin 4 :=
  if 0 ≠ i ∧ 0 ≠ j then 0 else if 1 ≠ i ∧ 1 ≠ j then 1 else 2

theorem third_ne : ∀ i j : Fin 4, i ≠ j → third i j ≠ i ∧ third i j ≠ j := by decide

theorem classPart_not_mono : ∀ x y z : Fin 4, x ≠ y → x ≠ z → y ≠ z →
    ¬ (classPart x = classPart y ∧ classPart y = classPart z) := by decide

theorem distinct_mem_F3 : ∀ x y z : Fin 4, x ≠ y → x ≠ z → y ≠ z →
    ({x, y, z} : Multiset (Fin 4)) ∈ F3 := by decide

/-- The edge function of a triangle, as a sum of its three edge indicators. -/
def triF (a b c : V) : Sym2 V → ℤ := edgeInd a b + edgeInd a c + edgeInd b c

omit [Fintype V] in
theorem triF_apply (a b c : V) (f : Sym2 V) :
    triF a b c f = tri (fun x y => edgeInd x y f) a b c := rfl

section Host

variable {cls : V → Fin 4} {G : SimpleGraph V}

/-- Every triangle on three distinct classes is an actual coarse-F0 triangle of `G`. -/
theorem realizes_triF (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {a b c : V}
    (hab : cls a ≠ cls b) (hac : cls a ≠ cls c) (hbc : cls b ≠ cls c) :
    Realizes (coarse cls) G (triF a b c) 1 :=
  realizes_triangle ((hG a b).mpr hab) ((hG a c).mpr hac) ((hG b c).mpr hbc)
    (classPart_not_mono _ _ _ hab hac hbc)

/-! ### Stage 1: rectangles -/

/-- Half-star term of an edge: `[u r_{cls v}] + [v r_{cls u}]` at `e = s(u, v)`. -/
def halfE (cls : V → Fin 4) (r : Fin 4 → V) (e : Sym2 V) : Sym2 V → ℤ :=
  ∑ v, ∑ j, degContrib cls v e j • edgeInd v (r j)

/-- Representative image of an edge: `[r_{cls u} r_{cls v}]` at `e = s(u, v)`. -/
def repE (cls : V → Fin 4) (r : Fin 4 → V) (e : Sym2 V) : Sym2 V → ℤ :=
  edgeOf (e.map fun x => r (cls x))

/-- The rectangle of an edge: `[uv] - [u r_j] - [r_i v] + [r_i r_j]`. -/
def rectE (cls : V → Fin 4) (r : Fin 4 → V) (e : Sym2 V) : Sym2 V → ℤ :=
  edgeOf e - halfE cls r e + repE cls r e

theorem halfE_mk (r : Fin 4 → V) (a b : V) :
    halfE cls r s(a, b) = edgeInd a (r (cls b)) + edgeInd b (r (cls a)) :=
  sum_degContrib_mk cls (fun v j => edgeInd v (r j)) a b

omit [Fintype V] in
theorem repE_mk (r : Fin 4 → V) (a b : V) :
    repE cls r s(a, b) = edgeInd (r (cls a)) (r (cls b)) := rfl

/-- **Stage 1.** The rectangle of a cross-class edge is realized by four actual triangles
through the representative of a third class. -/
theorem realizes_rectE (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {r : Fin 4 → V}
    (hr : ∀ i, cls (r i) = i) {a b : V} (hab : cls a ≠ cls b) :
    Realizes (coarse cls) G (rectE cls r s(a, b)) 4 := by
  obtain ⟨hki, hkj⟩ := third_ne (cls a) (cls b) hab
  have hh : cls (r (third (cls a) (cls b))) = third (cls a) (cls b) := hr _
  have hri : cls (r (cls a)) = cls a := hr _
  have hrj : cls (r (cls b)) = cls b := hr _
  have T1 := realizes_triF hG (a := a) (b := r (third (cls a) (cls b))) (c := b)
    (by rw [hh]; exact hki.symm) hab (by rw [hh]; exact hkj)
  have T2 := realizes_triF hG (a := a) (b := r (third (cls a) (cls b))) (c := r (cls b))
    (by rw [hh]; exact hki.symm) (by rw [hrj]; exact hab) (by rw [hh, hrj]; exact hkj)
  have T3 := realizes_triF hG (a := r (cls a)) (b := r (third (cls a) (cls b))) (c := b)
    (by rw [hri, hh]; exact hki.symm) (by rw [hri]; exact hab) (by rw [hh]; exact hkj)
  have T4 := realizes_triF hG (a := r (cls a)) (b := r (third (cls a) (cls b)))
    (c := r (cls b)) (by rw [hri, hh]; exact hki.symm) (by rw [hri, hrj]; exact hab)
    (by rw [hh, hrj]; exact hkj)
  refine (((T1.sub T2).sub T3).add T4).congr ?_
  funext f
  have key := rectangle_identity (fun x y => edgeInd x y f) a (r (cls a)) b (r (cls b))
    (r (third (cls a) (cls b)))
  simp only [rect] at key
  simp only [rectE, halfE_mk, repE_mk, Pi.add_apply, Pi.sub_apply, triF_apply]
  rw [← key, edgeInd_comm b (r (cls a))]
  simp only [edgeInd]
  ring

/-! ### Stage 2: stars -/

/-- The star of `v` after Stage 1, minus its transport to the class representative:
`Σ_j d_j ([v r_j] - [r_{cls v} r_j])`, with the **source** signed degrees `d_j`. -/
def starE (cls : V → Fin 4) (r : Fin 4 → V) (P : Finset (Sym2 V)) (v : V) : Sym2 V → ℤ :=
  ∑ j, degVec cls P v j • (edgeInd v (r j) - edgeInd (r (cls v)) (r j))

theorem sum_fin4_others {M : Type*} [AddCommMonoid M] (i : Fin 4) (f : Fin 4 → M)
    (hf : f i = 0) : ∑ j, f j = f (others3 i 0) + f (others3 i 1) + f (others3 i 2) := by
  fin_cases i <;> simp_all [Fin.sum_univ_four, others3, add_assoc]

theorem others3_ne : ∀ i : Fin 4, others3 i 0 ≠ i ∧ others3 i 1 ≠ i ∧ others3 i 2 ≠ i ∧
    others3 i 0 ≠ others3 i 1 ∧ others3 i 0 ≠ others3 i 2 ∧ others3 i 1 ≠ others3 i 2 := by
  decide

/-- A star-difference triangle pair `Δ(v, r_x, r_y) - Δ(r_i, r_x, r_y)` costs `2`. -/
theorem realizes_star_pair (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {r : Fin 4 → V}
    (hr : ∀ i, cls (r i) = i) {v : V} {x y : Fin 4} (hx : x ≠ cls v) (hy : y ≠ cls v)
    (hxy : x ≠ y) :
    Realizes (coarse cls) G (edgeInd v (r x) + edgeInd v (r y) -
      (edgeInd (r (cls v)) (r x) + edgeInd (r (cls v)) (r y))) 2 := by
  have T1 := realizes_triF hG (a := v) (b := r x) (c := r y) (by rw [hr]; exact hx.symm)
    (by rw [hr]; exact hy.symm) (by rw [hr, hr]; exact hxy)
  have T2 := realizes_triF hG (a := r (cls v)) (b := r x) (c := r y)
    (by rw [hr, hr]; exact hx.symm) (by rw [hr, hr]; exact hy.symm) (by rw [hr, hr]; exact hxy)
  refine (T1.sub T2).congr ?_
  funext f
  have key := star_difference (fun a b => edgeInd a b f) v (r (cls v)) (r x) (r y)
  simp only [Pi.add_apply, Pi.sub_apply, triF_apply] at key ⊢
  rw [key]
  ring

omit [Fintype V] in
/-- The star system of `ClassLatticeStage65`, as an identity of edge functions. -/
theorem star_combo (v w x₀ x₁ x₂ : V) (d₀ d₁ d₂ s : ℤ) (hs : d₀ + d₁ + d₂ = 2 * s) :
    d₀ • (edgeInd v x₀ - edgeInd w x₀) + d₁ • (edgeInd v x₁ - edgeInd w x₁) +
        d₂ • (edgeInd v x₂ - edgeInd w x₂) =
      (s - d₂) • (edgeInd v x₀ + edgeInd v x₁ - (edgeInd w x₀ + edgeInd w x₁)) +
      (s - d₁) • (edgeInd v x₀ + edgeInd v x₂ - (edgeInd w x₀ + edgeInd w x₂)) +
      (s - d₀) • (edgeInd v x₁ + edgeInd v x₂ - (edgeInd w x₁ + edgeInd w x₂)) := by
  obtain ⟨e₀, e₁, e₂⟩ := star_coefficients d₀ d₁ d₂ s hs
  funext f
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(edgeInd v x₀ f - edgeInd w x₀ f)) * e₀ +
    (-(edgeInd v x₁ f - edgeInd w x₁ f)) * e₁ + (-(edgeInd v x₂ f - edgeInd w x₂ f)) * e₂

/-- **Stage 2.** The star of every vertex is realized with cost at most three times its
source degree. Parity comes from `IsIntDiv cls F3 P`. -/
theorem realizes_starE (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {r : Fin 4 → V}
    (hr : ∀ i, cls (r i) = i) {P : Finset (Sym2 V)}
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) (hdiv : IsIntDiv cls F3 P) (v : V) :
    Realizes (coarse cls) G (starE cls r P v) (3 * ∑ j, degVec cls P v j) := by
  have hself := degVec_self_eq_zero cls P hP v
  obtain ⟨h0, h1, h2, h01, h02, h12⟩ := others3_ne (cls v)
  obtain ⟨s, hs⟩ := sum_degVec_eq_two_mul hdiv v
  have hsum := sum_fin4_others (cls v) (degVec cls P v) hself
  have hs' := hsum ▸ hs
  have hbud := star_budget _ _ _ s hs'
  have hn₀ := degVec_nonneg cls P v (others3 (cls v) 0)
  have hn₁ := degVec_nonneg cls P v (others3 (cls v) 1)
  have hn₂ := degVec_nonneg cls P v (others3 (cls v) 2)
  have D₀₁ := (realizes_star_pair hG hr (v := v) h0 h1 h01).smul
    (s - degVec cls P v (others3 (cls v) 2))
  have D₀₂ := (realizes_star_pair hG hr (v := v) h0 h2 h02).smul
    (s - degVec cls P v (others3 (cls v) 1))
  have D₁₂ := (realizes_star_pair hG hr (v := v) h1 h2 h12).smul
    (s - degVec cls P v (others3 (cls v) 0))
  refine ((D₀₁.add D₀₂).add D₁₂).congr ?_ |>.mono ?_
  · rw [starE, sum_fin4_others (cls v) _ (by rw [hself, zero_smul])]
    exact (star_combo _ _ _ _ _ _ _ _ s hs').symm
  · rw [hsum]
    rw [abs_of_nonneg hn₀, abs_of_nonneg hn₁, abs_of_nonneg hn₂] at hbud
    linarith

/-! ### Stage 3: the representative tetrahedron -/

/-- **Stage 3.** The representative residual `Σ_{e ∈ P} [r_{cls u} r_{cls v}]` is realized by
the four representative triangles, with cost at most `2 |P|`. -/
theorem realizes_residual (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {r : Fin 4 → V}
    (hr : ∀ i, cls (r i) = i) {P : Finset (Sym2 V)}
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
  have T012 := (realizes_triF hG (hne 0 1 (by decide)) (hne 0 2 (by decide))
    (hne 1 2 (by decide))).smul a
  have T013 := (realizes_triF hG (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 1 3 (by decide))).smul b
  have T023 := (realizes_triF hG (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 2 3 (by decide))).smul c
  have T123 := (realizes_triF hG (hne 1 2 (by decide)) (hne 1 3 (by decide))
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

/-! ### The exact identity and the producer -/

theorem sum_degVec_one (P : Finset (Sym2 V)) :
    ∑ v, ∑ j, degVec cls P v j = 2 * P.card := by
  have h := degVec_swap cls P (fun _ _ => (1 : ℤ))
  simp only [smul_eq_mul, mul_one] at h
  rw [h]
  have : ∀ e : Sym2 V, ∑ v, ∑ j, degContrib cls v e j = 2 := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
    have := sum_degContrib_mk cls (fun _ _ => (1 : ℤ)) a b
    simpa using this
  simp [this, mul_comm]

/-- **Exact identity** at every `Sym2` coordinate:
`ind P = Σ_{e ∈ P} rect e + Σ_v star v + Σ_{e ∈ P} rep e`. -/
theorem ind_decomposition (r : Fin 4 → V) (P : Finset (Sym2 V)) :
    ind P = ∑ e ∈ P, rectE cls r e + ∑ v, starE cls r P v + ∑ e ∈ P, repE cls r e := by
  have hhalf : ∑ e ∈ P, halfE cls r e = ∑ v, ∑ j, degVec cls P v j • edgeInd v (r j) :=
    (degVec_swap cls P (fun v j => edgeInd v (r j))).symm
  have hrep2 : ∑ v, ∑ j, degVec cls P v j • edgeInd (r (cls v)) (r j) =
      ∑ e ∈ P, (2 : ℤ) • repE cls r e := by
    rw [degVec_swap cls P (fun v j => edgeInd (r (cls v)) (r j))]
    refine sum_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
    rw [sum_degContrib_mk cls (fun v j => edgeInd (r (cls v)) (r j)) a b, repE_mk,
      edgeInd_comm (r (cls b)), two_smul]
  have hstar : ∑ v, starE cls r P v =
      ∑ v, ∑ j, degVec cls P v j • edgeInd v (r j) -
        ∑ v, ∑ j, degVec cls P v j • edgeInd (r (cls v)) (r j) := by
    simp only [starE, smul_sub, sum_sub_distrib]
  rw [hstar, hrep2, ← hhalf, ← Finset.smul_sum]
  simp only [rectE, sum_add_distrib, sum_sub_distrib, ← ind_eq_sum_edgeOf]
  abel

/-- **Structural-lattice certificate as a realization.** In the complete four-class host,
every `P ⊆ E(G)` with `IsIntDiv cls F3 P` is an integer combination of actual coarse-F0
triangles of `G` of total weight at most `12 |P|`. -/
theorem class_lattice_realizes (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {r : Fin 4 → V}
    (hr : ∀ i, cls (r i) = i) [DecidableRel G.Adj] {P : Finset (Sym2 V)}
    (hPG : P ⊆ G.edgeFinset) (hdiv : IsIntDiv cls F3 P) :
    Realizes (coarse cls) G (ind P) (12 * P.card) := by
  have hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b := fun a b h =>
    (hG a b).mp (SimpleGraph.mem_edgeFinset.mp (hPG h))
  have R1 := Realizes.sum P (rectE cls r) (fun _ => 4) fun e he => by
    induction e using Sym2.ind with
    | _ a b => exact realizes_rectE hG hr (hP a b he)
  have R2 := Realizes.sum univ (starE cls r P) (fun v => 3 * ∑ j, degVec cls P v j)
    fun v _ => realizes_starE hG hr hP hdiv v
  have R3 := realizes_residual hG hr hP hdiv
  refine ((R1.add R2).add R3).congr (ind_decomposition r P).symm |>.mono ?_
  rw [← mul_sum, sum_degVec_one P, sum_const, nsmul_eq_mul]
  ring_nf
  rfl

omit [Fintype V] [DecidableEq V] in
/-- A triangle of the complete four-class host is a structural F3 copy. -/
theorem isCopy_F3_of_clique (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {s : Finset V}
    (hs : G.IsNClique 3 s) : IsCopy cls F3 G s := by
  classical
  refine ⟨hs, ?_⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hs.card_eq
  obtain ⟨h1, h2, h3⟩ := SimpleGraph.is3Clique_triple_iff.mp hs
  rw [map_three cls hab hac hbc]
  exact distinct_mem_F3 _ _ _ ((hG _ _).mp h1) ((hG _ _).mp h2) ((hG _ _).mp h3)

/-- **Main theorem (Stage65 Job A).** Let `cls : V → Fin 4` have representatives `r`, and let
`G` be the complete four-class graph. Every `P ⊆ E(G)` with structural divisibility
`IsIntDiv cls F3 P` has a signed physical certificate for the coarse labels
`v ↦ classPart (cls v)` of weight at most `12 |P|`. The identity holds at every `Sym2`
coordinate, and every certificate triangle is an actual structural F3 triangle of `G`. -/
theorem class_lattice_certificate (cls : V → Fin 4) (r : Fin 4 → V)
    (hr : ∀ i, cls (r i) = i) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) (P : Finset (Sym2 V))
    (hPG : P ⊆ G.edgeFinset) (hdiv : IsIntDiv cls F3 P) :
    ∃ (ι : Type u) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
      IsSignedCert (fun v => classPart (cls v)) G P t c ∧
      certWeight c ≤ 12 * P.card ∧ ∀ j, IsCopy cls F3 G (t j) := by
  obtain ⟨ι, hι, t, c, hc, hw⟩ := (class_lattice_realizes hG hr hPG hdiv).signedCert
  exact ⟨ι, hι, t, c, hc, hw, fun j => isCopy_F3_of_clique hG (hc.1 j).1⟩

end Host

end PartitionedTriangleAbsorption.ClassCertificate
