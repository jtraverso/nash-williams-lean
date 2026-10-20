/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Pseudorandom.Theorem12
public import RequestProject.NW18.Case124.BKLOInterface

@[expose] public section

/-!
# External interface A (EGJ Theorem 1.2) applied to physical triangle hypergraphs

`Pseudorandom.theorem_1_2` (Ehard–Glock–Joos, Theorem 1.2) is **already proved in this
project** (no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`), so interface A is used
here as a theorem, not as a parameter.

The hypergraph: hypergraph vertices are graph edges (`Sym2 V`), hyperedges are the edge sets
`triEdges t` of a chosen family `𝒯` of 3-vertex sets (`triHyp 𝒯 = 𝒯.image triEdges`).  It is a
`Finset`, hence a *simple* 3-uniform hypergraph, its codegrees are at most `1`
(`codegree_triHyp_le_one`), and `triEdges` is injective on 3-sets (`triEdges_injOn`), so a
matching of `triHyp 𝒯` projects to a physical edge-disjoint triangle packing `Pk ⊆ 𝒯`.

Monitors: for an edge set `S`, `w_S(T) = |T ∩ S|`.  For a matching `M`, `w_S(M)` is the number of
edges of `S` covered by `M` (`weight_monitor_matching`), and `w_S(triHyp 𝒯) = ∑_{e∈S} deg(e)`
(`weight_monitor_hyp`).

* `egj_triangle_packing`: one edge-disjoint packing `Pk ⊆ 𝒯` such that for every monitored set
  `S_k` (at most `exp(Δ^{ε²})` of them, `ε = δ/450`) with `∑_{e∈S_k} deg(e) ≥ 3Δ^{1+δ}`, the number
  of covered edges of `S_k` is `(1 ± Δ^{-ε}) ∑_{e∈S_k} deg(e) / Δ`.
* `egj_nibble_leftover`: if moreover every monitored edge has `deg_𝒯(e) ≥ (1-η)Δ` (a *regular
  seed*), every monitored set with `|S_k| ≥ 6Δ^δ` keeps at most `(η + Δ^{-ε})|S_k|` uncovered edges.

The regular seed itself (a triangle family whose edge degrees are all within `(1-η)Δ` and `Δ`)
is **not** produced by EGJ; see `NW18_CASE124_EGJ_BKLO_REDUCTION.md`.
-/

namespace NashWilliams18.EGJTriangle

open Finset Pseudorandom NashWilliams18.BKLOIface

section Basic

variable {V : Type*} [DecidableEq V]

/-- The physical triangle hypergraph of a family `𝒯` of vertex triples. -/
def triHyp (𝒯 : Finset (Finset V)) : Finset (Finset (Sym2 V)) := 𝒯.image triEdges

lemma mk_mem_triEdges {t : Finset V} {a b : V} :
    s(a, b) ∈ triEdges t ↔ a ∈ t ∧ b ∈ t ∧ a ≠ b := mk_mem_triEdges'

lemma mem_of_mem_triEdges {t : Finset V} {e : Sym2 V} (he : e ∈ triEdges t) {v : V}
    (hv : v ∈ e) : v ∈ t := by
  have := (mem_filter.mp he).1
  exact Finset.mem_sym2_iff.mp this v hv

/-- Two distinct edges inside a 3-set determine it. -/
lemma eq_of_two_edges {t : Finset V} (ht : t.card = 3) {a b c d : V} (ha : a ∈ t) (hb : b ∈ t)
    (hc : c ∈ t) (hd : d ∈ t) (hab : a ≠ b) (hcd : c ≠ d) (hne : s(a, b) ≠ s(c, d)) :
    t = {a, b, c, d} := by
  have hsub : ({a, b, c, d} : Finset V) ⊆ t := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  refine (eq_of_subset_of_card_le hsub ?_).symm
  rw [ht]
  by_cases hca : c = a
  · subst hca
    have hdb : d ≠ b := fun h => hne (by rw [h])
    have h3 : ({c, b, d} : Finset V).card = 3 := by
      rw [card_insert_of_notMem (by simp [hab, hcd]), card_pair (Ne.symm hdb)]
    calc 3 = ({c, b, d} : Finset V).card := h3.symm
      _ ≤ _ := card_le_card (by intro x; simp only [mem_insert, mem_singleton]; tauto)
  by_cases hcb : c = b
  · subst hcb
    have hda : d ≠ a := fun h => hne (by rw [h, Sym2.eq_swap])
    have h3 : ({a, c, d} : Finset V).card = 3 := by
      rw [card_insert_of_notMem (by simp [hab, Ne.symm hda]), card_pair hcd]
    calc 3 = ({a, c, d} : Finset V).card := h3.symm
      _ ≤ _ := card_le_card (by intro x; simp only [mem_insert, mem_singleton]; tauto)
  · have h3 : ({a, b, c} : Finset V).card = 3 := by
      rw [card_insert_of_notMem (by simp [hab, Ne.symm hca]), card_pair (Ne.symm hcb)]
    calc 3 = ({a, b, c} : Finset V).card := h3.symm
      _ ≤ _ := card_le_card (by intro x; simp only [mem_insert, mem_singleton]; tauto)

lemma triEdges_card {t : Finset V} (ht : t.card = 3) : (triEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht
  have : triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [mk_mem_triEdges]
      simp only [mem_insert, mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨hx, hy, hxy⟩
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
      · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [eq_comm]
  rw [this, card_insert_of_notMem, card_pair]
  · intro h; rw [Sym2.eq_iff] at h; tauto
  · simp only [mem_insert, mem_singleton, Sym2.eq_iff]; tauto

/-- A vertex lies in `t` iff it lies in an edge of `t` (for `|t| ≥ 2`). -/
lemma mem_iff_exists_triEdge {t : Finset V} (ht : 2 ≤ t.card) (v : V) :
    v ∈ t ↔ ∃ e ∈ triEdges t, v ∈ e := by
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := exists_mem_ne ht v
    exact ⟨s(v, w), mk_mem_triEdges.mpr ⟨hv, hw, Ne.symm hwv⟩, Sym2.mem_mk_left _ _⟩
  · rintro ⟨e, he, hv⟩; exact mem_of_mem_triEdges he hv

lemma triEdges_injOn : Set.InjOn (triEdges (V := V)) {t | 2 ≤ t.card} := by
  intro t ht t' ht' h
  ext v
  rw [mem_iff_exists_triEdge ht, mem_iff_exists_triEdge ht', h]

lemma isUniform_triHyp {𝒯 : Finset (Finset V)} (h3 : ∀ t ∈ 𝒯, t.card = 3) :
    IsUniform (triHyp 𝒯) 3 := by
  intro T hT
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
  exact triEdges_card (h3 t ht)

/-- Codegrees of the triangle hypergraph are at most one. -/
lemma codegree_triHyp_le_one {𝒯 : Finset (Finset V)} (h3 : ∀ t ∈ 𝒯, t.card = 3)
    {e f : Sym2 V} (hef : e ≠ f) : codegree (triHyp 𝒯) e f ≤ 1 := by
  unfold codegree
  rw [card_le_one]
  intro T hT T' hT'
  rw [mem_filter] at hT hT'
  obtain ⟨⟨t, ht, rfl⟩, he, hf⟩ := And.imp_left mem_image.mp hT
  obtain ⟨⟨t', ht', rfl⟩, he', hf'⟩ := And.imp_left mem_image.mp hT'
  induction e using Sym2.ind with
  | _ a b =>
  induction f using Sym2.ind with
  | _ c d =>
  rw [mk_mem_triEdges] at he hf he' hf'
  rw [eq_of_two_edges (h3 t ht) he.1 he.2.1 hf.1 hf.2.1 he.2.2 hf.2.2 hef,
    eq_of_two_edges (h3 t' ht') he'.1 he'.2.1 hf'.1 hf'.2.1 he'.2.2 hf'.2.2 hef]

/-- The monitor weight `w_S(T) = |T ∩ S|`. -/
def monitor (S : Finset (Sym2 V)) : Finset (Sym2 V) → ℝ := fun T => ((T ∩ S).card : ℝ)

/-- For a matching, the monitor weight counts the covered edges of `S`. -/
lemma weight_monitor_matching (S : Finset (Sym2 V)) {M : Finset (Finset (Sym2 V))}
    (hM : IsMatching M) : weight (monitor S) M = ((M.biUnion id ∩ S).card : ℝ) := by
  unfold weight monitor
  rw [biUnion_inter, card_biUnion]
  · push_cast; rfl
  · intro T hT T' hT' hne
    exact Disjoint.mono inter_subset_left inter_subset_left (hM T hT T' hT' hne)

/-- The total monitor weight is the sum of the degrees over `S`. -/
lemma weight_monitor_hyp (S : Finset (Sym2 V)) (H : Finset (Finset (Sym2 V))) :
    weight (monitor S) H = ∑ e ∈ S, (degree H e : ℝ) := by
  unfold weight monitor degree
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun T _ => ?_
  push_cast
  rw [sum_ite_mem, inter_comm]

end Basic

/-- **EGJ Theorem 1.2 on a physical triangle hypergraph.**  For `δ ∈ (0,1)`, `ε = δ/450`, there
is `Δ₀` such that for every `Δ ≥ Δ₀` and every family `𝒯` of vertex triples whose triangle
hypergraph has all edge-degrees `≤ Δ` and `|𝒯| ≤ exp(Δ^{ε²})`, and every family of at most
`exp(Δ^{ε²})` monitored edge sets `S_k`, there is **one** edge-disjoint packing `Pk ⊆ 𝒯` such that
every monitored `S_k` with `∑_{e∈S_k} deg(e) ≥ 3Δ^{1+δ}` has `(1 ± Δ^{-ε}) ∑_{e∈S_k} deg(e)/Δ`
covered edges. -/
theorem egj_triangle_packing (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (𝒯 : Finset (Finset V)),
      (∀ t ∈ 𝒯, t.card = 3) →
      (∀ e, (degree (triHyp 𝒯) e : ℝ) ≤ Δ) →
      (𝒯.card : ℝ) ≤ Real.exp (Δ ^ ((δ / 450) ^ 2)) →
      ∀ (ι : Type) [Fintype ι] (S : ι → Finset (Sym2 V)),
      (Fintype.card ι : ℝ) ≤ Real.exp (Δ ^ ((δ / 450) ^ 2)) →
      ∃ Pk ⊆ 𝒯, (∀ t ∈ Pk, ∀ t' ∈ Pk, t ≠ t' → Disjoint (triEdges t) (triEdges t')) ∧
        ∀ k, 3 * Δ ^ (1 + δ) ≤ ∑ e ∈ S k, (degree (triHyp 𝒯) e : ℝ) →
          |((Pk.biUnion triEdges ∩ S k).card : ℝ) - (∑ e ∈ S k, (degree (triHyp 𝒯) e : ℝ)) / Δ|
            ≤ Δ ^ (-(δ / 450)) * ((∑ e ∈ S k, (degree (triHyp 𝒯) e : ℝ)) / Δ) := by
  obtain ⟨Δ₀, hΔ₀⟩ := theorem_1_2 δ hδ0 hδ1 3 (by norm_num)
  have h450 : δ / (50 * ((3 : ℕ) : ℝ) ^ 2) = δ / 450 := by norm_num
  refine ⟨max Δ₀ 1, fun Δ hΔ V _ _ 𝒯 h3 hdeg hcard ι _ S hι => ?_⟩
  have hΔ1 : 1 ≤ Δ := le_trans (le_max_right _ _) hΔ
  have hΔ0 : 0 < Δ := by linarith
  set H := triHyp 𝒯 with hHdef
  have hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 - δ) := by
    intro u v huv
    have h1 : (codegree H u v : ℝ) ≤ 1 := by exact_mod_cast codegree_triHyp_le_one h3 huv
    exact h1.trans (Real.one_le_rpow hΔ1 (by linarith))
  have hHcard : (H.card : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * ((3 : ℕ) : ℝ) ^ 2)) ^ 2)) := by
    rw [h450]; exact le_trans (by exact_mod_cast card_image_le) hcard
  obtain ⟨M, hMH, hM, hW⟩ := hΔ₀ Δ (le_trans (le_max_left _ _) hΔ) (Sym2 V) H
    (isUniform_triHyp h3) hdeg hcod hHcard ι (fun k => monitor (S k))
    (fun k e _ => by unfold monitor; positivity) (by rw [h450]; exact hι)
  -- project the matching to a physical packing
  refine ⟨𝒯.filter (fun t => triEdges t ∈ M), filter_subset _ _, ?_, ?_⟩
  · intro t ht t' ht' hne
    rw [mem_filter] at ht ht'
    refine hM _ ht.2 _ ht'.2 fun h => hne ?_
    exact triEdges_injOn (by simp [h3 t ht.1]) (by simp [h3 t' ht'.1]) h
  · intro k hk
    have hbu : (𝒯.filter (fun t => triEdges t ∈ M)).biUnion triEdges = M.biUnion id := by
      ext e
      simp only [mem_biUnion, mem_filter, id]
      constructor
      · rintro ⟨t, ⟨_, htM⟩, he⟩; exact ⟨_, htM, he⟩
      · rintro ⟨T, hTM, he⟩
        obtain ⟨t, ht, rfl⟩ := mem_image.mp (hMH hTM)
        exact ⟨t, ⟨ht, hTM⟩, he⟩
    have hheavy : ∀ e ∈ H, monitor (S k) e * Δ ^ (1 + δ) ≤ weight (monitor (S k)) H := by
      intro T hT
      rw [weight_monitor_hyp]
      have hT3 : (T ∩ S k).card ≤ 3 := by
        rw [← isUniform_triHyp h3 T hT]; exact card_le_card inter_subset_left
      have : monitor (S k) T ≤ 3 := by unfold monitor; exact_mod_cast hT3
      have hp : 0 ≤ Δ ^ (1 + δ) := by positivity
      nlinarith
    have := hW k hheavy
    rw [weight_monitor_matching _ hM, weight_monitor_hyp, h450] at this
    rw [hbu]
    exact this

/-- **Nibble with simultaneous local leftover control** (EGJ + a regular seed).  If every
monitored edge has degree at least `(1-η)Δ` in the triangle hypergraph (`0 ≤ η ≤ 1/2`), then one
edge-disjoint packing `Pk ⊆ 𝒯` leaves at most `(η + Δ^{-ε})|S_k|` edges of each monitored set
`S_k` with `|S_k| ≥ 6Δ^δ` uncovered. -/
theorem egj_nibble_leftover (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (𝒯 : Finset (Finset V)) (η : ℝ),
      0 ≤ η → η ≤ 1 / 2 →
      (∀ t ∈ 𝒯, t.card = 3) →
      (∀ e, (degree (triHyp 𝒯) e : ℝ) ≤ Δ) →
      (𝒯.card : ℝ) ≤ Real.exp (Δ ^ ((δ / 450) ^ 2)) →
      ∀ (ι : Type) [Fintype ι] (S : ι → Finset (Sym2 V)),
      (Fintype.card ι : ℝ) ≤ Real.exp (Δ ^ ((δ / 450) ^ 2)) →
      (∀ k, ∀ e ∈ S k, (1 - η) * Δ ≤ (degree (triHyp 𝒯) e : ℝ)) →
      ∃ Pk ⊆ 𝒯, (∀ t ∈ Pk, ∀ t' ∈ Pk, t ≠ t' → Disjoint (triEdges t) (triEdges t')) ∧
        ∀ k, 6 * Δ ^ δ ≤ ((S k).card : ℝ) →
          (((S k) \ Pk.biUnion triEdges).card : ℝ) ≤ (η + Δ ^ (-(δ / 450))) * (S k).card := by
  obtain ⟨Δ₀, hΔ₀⟩ := egj_triangle_packing δ hδ0 hδ1
  refine ⟨max Δ₀ 1, fun Δ hΔ V _ _ 𝒯 η hη0 hη1 h3 hdeg hcard ι _ S hι hreg => ?_⟩
  have hΔ1 : 1 ≤ Δ := le_trans (le_max_right _ _) hΔ
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨Pk, hPk, hdisj, hcov⟩ := hΔ₀ Δ (le_trans (le_max_left _ _) hΔ) V 𝒯 h3 hdeg hcard ι S hι
  refine ⟨Pk, hPk, hdisj, fun k hk => ?_⟩
  set D := ∑ e ∈ S k, (degree (triHyp 𝒯) e : ℝ) with hD
  set a := Δ ^ (-(δ / 450)) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΔ1 (by linarith)
  have hDlow : (1 - η) * Δ * (S k).card ≤ D := by
    calc (1 - η) * Δ * (S k).card = ∑ _e ∈ S k, (1 - η) * Δ := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ D := sum_le_sum (hreg k)
  have hpow : Δ ^ (1 + δ) = Δ * Δ ^ δ := by
    rw [Real.rpow_add hΔ0, Real.rpow_one]
  have hheavy : 3 * Δ ^ (1 + δ) ≤ D := by
    rw [hpow]
    have : 3 * (Δ * Δ ^ δ) ≤ (1 - η) * Δ * (S k).card := by
      have h6 := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ Δ / 2)
      have h7 : 0 ≤ (1 / 2 - η) * Δ * ((S k).card : ℝ) :=
        mul_nonneg (mul_nonneg (by linarith) hΔ0.le) (Nat.cast_nonneg _)
      nlinarith
    linarith
  have hc := hcov k hheavy
  have hcov' : (1 - a) * (D / Δ) ≤ ((Pk.biUnion triEdges ∩ S k).card : ℝ) := by
    have := (abs_le.mp hc).1; linarith
  have hDΔ : (1 - η) * (S k).card ≤ D / Δ := by
    rw [le_div_iff₀ hΔ0]; linarith
  have hsplit : ((S k \ Pk.biUnion triEdges).card : ℝ) +
      ((Pk.biUnion triEdges ∩ S k).card : ℝ) = (S k).card := by
    have := card_sdiff_add_card_inter (S k) (Pk.biUnion triEdges)
    rw [inter_comm] at this
    exact_mod_cast this
  have h1 : (1 - a) * ((1 - η) * (S k).card) ≤ (1 - a) * (D / Δ) :=
    mul_le_mul_of_nonneg_left hDΔ (by linarith)
  have hS0 : (0 : ℝ) ≤ (S k).card := by positivity
  nlinarith [mul_nonneg (mul_nonneg ha0 hη0) hS0]

end NashWilliams18.EGJTriangle
