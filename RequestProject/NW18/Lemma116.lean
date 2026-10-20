/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Sampling.Deterministic
public import RequestProject.NW18.Sampling.Counts
public import RequestProject.NW18.Sampling.MaxCut

@[expose] public section

/-!
# Lemma 11.6 (random induced subgraphs of a non-extremal graph)

Proof of Lemma 11.6 of the paper, in counting form.  A uniformly random sequence `ω` of `m`
vertices (other than `u, v`) is considered; with probability at least `1 - ρ/2`
* every sampled vertex keeps about the expected number of sampled neighbours
  (`deg_lower`), and so do `u` and `v` (`count_lower`);
* if `G` has many vertices of degree above `(3/4 + σ) n`, the sample contains many of them
  (`count_lower`);
* if every cut of `G` is small, every cut of the sample is small (`maxcut_sample`, the direction
  of the estimability of max-cut, Theorem 11.4 of the paper, that the proof uses).

On these events the set `S = {u, v} ∪ {ω j}` is good (`mindeg_of_events`,
`not_ext_i_of_events`, `not_ext_ii_of_events`), and the conversion from sequences to sets is
`card_sets_ge`.
-/

namespace NashWilliams18

open Finset Pseudorandom NashWilliams18.Sampling

/-- A vertex set `S` is *good* (for `ε, σ`) if `G[S]` has minimum degree at least
`(3/4 - 2ε)|S|` and is not `σ/2`-extremal. -/
def IsGoodSet {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε σ : ℝ) (S : Finset V) : Prop :=
  (3 / 4 - 2 * ε) * (S.card : ℝ) ≤ ((G.induce (S : Set V)).minDegree : ℝ) ∧
    ¬ IsExtremal (σ / 2) (G.induce (S : Set V))

lemma isExtremal_of_one_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {σ : ℝ} (hσ : 1 ≤ σ) : IsExtremal σ G := by
  refine ⟨le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    (by positivity), ∅, le_trans ?_ (by positivity)⟩
  have : (1 - σ) * (Fintype.card V : ℝ) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

set_option maxHeartbeats 2000000 in
open Classical in
/-- **Lemma 11.6** (counting form), proof. -/
theorem lemma_11_6_proof :
    ∀ ε ρ σ : ℝ, 0 < ε → 0 < ρ → 0 < σ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ n₁ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₁ ≤ Fintype.card V → (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ¬ IsExtremal σ G → ∀ u v, G.Adj u v →
        (1 - ρ) * ((Fintype.card V - 2).choose (k - 2) : ℝ) ≤
          ((((univ : Finset V).powersetCard k).filter
            (fun S => u ∈ S ∧ v ∈ S ∧ IsGoodSet G ε σ S)).card : ℝ) := by
  intro ε ρ σ hε hρ hσ
  rcases le_or_gt 1 σ with hσ1 | hσ1
  · exact ⟨0, fun k _ => ⟨0, fun V _ _ G _ _ _ hext => absurd (isExtremal_of_one_le G hσ1) hext⟩⟩
  set c := min ε σ / 8 with hc
  have hc0 : 0 < c := by positivity
  set η := min (ρ / 8) (σ / 16) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨m₀, N₀, hmc⟩ := maxcut_sample hη0
  obtain ⟨M₁, hM₁⟩ := eventually_pow_mul_exp_le 1 (c := c ^ 2 / (2 * (1 + c))) (by positivity)
    (ε := ρ / 16) (by positivity)
  refine ⟨⌈96 / σ⌉₊ + ⌈5 / ε⌉₊ + m₀ + M₁ + 6, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hmk : ⌈96 / σ⌉₊ + ⌈5 / ε⌉₊ + m₀ + M₁ + 4 ≤ m := by omega
  refine ⟨N₀ + 2 * m ^ 2 + ⌈20 / σ⌉₊ + 3, fun V _ _ G _ hn hδ hext u v huv => ?_⟩
  classical
  have huv' : u ≠ v := G.ne_of_adj huv
  have hN : Fintype.card (Rest u v) = Fintype.card V - 2 := card_rest huv'
  set n := Fintype.card V with hndef
  set N := Fintype.card (Rest u v) with hNdef
  have hNbig : N₀ + 2 * m ^ 2 + ⌈20 / σ⌉₊ + 1 ≤ N := by omega
  have hNr : (n : ℝ) = N + 2 := by
    have : N + 2 = n := by omega
    rw [← this]; push_cast; ring
  haveI : Nonempty (Rest u v) := Fintype.card_pos_iff.mp (by omega)
  have hm1 : 1 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hσm : 96 ≤ σ * m := by
    have h1 : 96 / σ ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈96 / σ⌉₊ ≤ m))
    rw [div_le_iff₀ hσ] at h1; linarith
  have hεm : 5 ≤ ε * m := by
    have h1 : 5 / ε ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈5 / ε⌉₊ ≤ m))
    rw [div_le_iff₀ hε] at h1; linarith
  have hσN : 20 ≤ σ * N := by
    have h1 : 20 / σ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈20 / σ⌉₊ ≤ N))
    rw [div_le_iff₀ hσ] at h1; linarith
  have h2m : 2 * m ^ 2 ≤ Fintype.card V - 2 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNn : (N : ℝ) ≤ n := by rw [hNr]; linarith
  have hmN : (m : ℝ) ≤ N := by
    have : m ≤ N := by nlinarith
    exact_mod_cast this
  have hN4 : (4 : ℝ) ≤ N := by
    have : 4 ≤ N := by nlinarith
    exact_mod_cast this
  have hnN2 : (n : ℝ) ^ 2 ≤ (1 + σ / 4) * (N : ℝ) ^ 2 := by
    rw [hNr]; nlinarith [mul_le_mul_of_nonneg_right hσN hNpos.le]
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set t := c * (m : ℝ) with htdef
  have ht0 : 0 < t := by positivity
  have htε : t ≤ ε * m / 8 := by
    have : c ≤ ε / 8 := by rw [hc]; have := min_le_left ε σ; linarith
    nlinarith
  have htσ : t ≤ σ * m / 8 := by
    have : c ≤ σ / 8 := by rw [hc]; have := min_le_right ε σ; linarith
    nlinarith
  have hEeq : t ^ 2 / (2 * (m + t)) = c ^ 2 / (2 * (1 + c)) * m := by
    rw [htdef]; field_simp
  have hmE : (m : ℝ) * Real.exp (-(t ^ 2 / (2 * (m + t)))) ≤ ρ / 32 := by
    have := hM₁ m (by omega)
    rw [hEeq]
    rw [pow_one] at this
    linarith
  have hE : Real.exp (-(t ^ 2 / (2 * (m + t)))) ≤ ρ / 32 :=
    le_trans (le_mul_of_one_le_left (Real.exp_pos _).le hmr) hmE
  have hP := unif_isPMF (ι := Fin m) (α := Rest u v)
  have hcardS : ∀ ω : Fin m → Rest u v, Function.Injective ω →
      ((setOf u v ω).card : ℝ) = m + 2 := fun ω hω => by
    rw [card_setOf huv' ω hω]; push_cast; ring
  have hmindeg : ∀ ω : Fin m → Rest u v, Function.Injective ω →
      (∀ i, (m - 1) * ((univ.filter fun b : Rest u v => G.Adj (ω i).val b.val).card : ℝ) /
        Fintype.card (Rest u v) - t ≤
        (((univ.filter fun j => G.Adj (ω i).val (ω j).val).card : ℕ) : ℝ)) →
      (m * ((univ.filter fun b : Rest u v => G.Adj u b.val).card : ℝ) /
        Fintype.card (Rest u v) - t ≤
        (((univ.filter fun j => G.Adj u (ω j).val).card : ℕ) : ℝ)) →
      (m * ((univ.filter fun b : Rest u v => G.Adj v b.val).card : ℝ) /
        Fintype.card (Rest u v) - t ≤
        (((univ.filter fun j => G.Adj v (ω j).val).card : ℕ) : ℝ)) →
      (3 / 4 - 2 * ε) * ((setOf u v ω).card : ℝ) ≤
        ((G.induce (setOf u v ω : Set V)).minDegree : ℝ) := by
    intro ω hω hd hu hv
    rw [hcardS ω hω]
    rcases lt_or_ge ε (3 / 8) with h38 | h38
    · refine mindeg_of_events G hω ?_ ?_ ?_ hm1 h38 htε hεm ?_ ?_ ?_
      · exact hNpos
      · exact hNn
      · exact hmN
      · exact hδ
      · exact hd
      · rintro x (rfl | rfl) <;> assumption
    · have : (3 / 4 - 2 * ε) * ((m : ℝ) + 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith only [h38]) (by linarith only [hmr])
      exact this.trans (Nat.cast_nonneg _)
  have hfinal : ∀ (Bad : (Fin m → Rest u v) → Prop),
      pProb (unif (Fin m) (Rest u v)) Bad ≤ ρ / 2 →
      (∀ ω : Fin m → Rest u v, Function.Injective ω → ¬ Bad ω → IsGoodSet G ε σ (setOf u v ω)) →
      (1 - ρ) * ((Fintype.card V - 2).choose (m + 2 - 2) : ℝ) ≤
        ((((univ : Finset V).powersetCard (m + 2)).filter
          (fun S => u ∈ S ∧ v ∈ S ∧ IsGoodSet G ε σ S)).card : ℝ) := by
    intro Bad hBad hgood
    have := card_sets_ge huv' m h2m (fun S => IsGoodSet G ε σ S) Bad (ρ / 2) hBad hgood
    rw [show m + 2 - 2 = m by omega]
    convert this using 2
    ring
  unfold IsExtremal at hext
  rw [not_and_or] at hext
  rcases hext with hi | hii
  · -- many high-degree vertices
    have hB : σ * n < ((univ.filter fun x => (3 / 4 + σ) * (n : ℝ) < G.degree x).card : ℝ) := by
      push_neg at hi
      have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
        (fun x => (G.degree x : ℝ) ≤ (3 / 4 + σ) * n)
      have h2 : (univ.filter fun x => ¬ ((G.degree x : ℝ) ≤ (3 / 4 + σ) * n)) =
          univ.filter fun x => (3 / 4 + σ) * (n : ℝ) < G.degree x := by
        ext x; simp
      rw [h2, card_univ] at h1
      have h3 : ((univ.filter fun x => (G.degree x : ℝ) ≤ (3 / 4 + σ) * n).card : ℝ) +
          ((univ.filter fun x => (3 / 4 + σ) * (n : ℝ) < G.degree x).card : ℝ) = n := by
        exact_mod_cast h1
      linarith
    have hBP := count_lower (α := Rest u v) m
      (fun b : Rest u v => (3 / 4 + σ) * (n : ℝ) < G.degree b.val) t ht0
    refine hfinal (fun ω => (∃ i, (((univ.filter fun j => G.Adj (ω i).val (ω j).val).card : ℕ) : ℝ) <
        (m - 1) * ((univ.filter (fun b : Rest u v => G.Adj (ω i).val b.val)).card : ℝ) /
          Fintype.card (Rest u v) - t) ∨
      ((((univ.filter fun j => G.Adj u (ω j).val).card : ℕ) : ℝ) <
        m * ((univ.filter fun b : Rest u v => G.Adj u b.val).card : ℝ) /
          Fintype.card (Rest u v) - t) ∨
      ((((univ.filter fun j => G.Adj v (ω j).val).card : ℕ) : ℝ) <
        m * ((univ.filter fun b : Rest u v => G.Adj v b.val).card : ℝ) /
          Fintype.card (Rest u v) - t) ∨
      ((((univ.filter fun j => (3 / 4 + σ) * (n : ℝ) < G.degree (ω j).val).card : ℕ) : ℝ) <
        m * ((univ.filter fun b : Rest u v => (3 / 4 + σ) * (n : ℝ) < G.degree b.val).card : ℝ) /
          Fintype.card (Rest u v) - t)) ?_ ?_
    · have hdegP := deg_lower (α := Rest u v) m (fun a b => G.Adj a.val b.val)
        (fun a => G.loopless.irrefl _) t ht0
      have huP := count_lower (α := Rest u v) m (fun b => G.Adj u b.val) t ht0
      have hvP := count_lower (α := Rest u v) m (fun b => G.Adj v b.val) t ht0
      refine (pProb_or_le hP _ _).trans ?_
      refine (add_le_add hdegP ((pProb_or_le hP _ _).trans (add_le_add huP
        ((pProb_or_le hP _ _).trans (add_le_add hvP hBP))))).trans ?_
      linarith only [hmE, hE, hρ]
    · intro ω hω hnb
      simp only [not_or, not_exists, not_lt] at hnb
      obtain ⟨hd, hu, hv, hb⟩ := hnb
      refine ⟨hmindeg ω hω hd hu hv, fun hX => ?_⟩
      exact not_ext_i_of_events G huv' hω hNpos hNn hmN hm1 hσ hσ1 htσ (by linarith) hB hd hb
        hX.1
  · -- all cuts are small
    have hcut : ∀ T : Finset V, (cutSize G T : ℝ) < ((1 - σ) * (n : ℝ) ^ 2 / 2) / 2 := by
      intro T
      push_neg at hii
      have := hii T
      linarith only [this]
    have hKX := doubled_cut_rest_le G u v hcut
    have hσ' : 0 ≤ 1 - σ := by linarith only [hσ1]
    have hK0 : 0 ≤ (1 - σ) * (n : ℝ) ^ 2 / 2 := by positivity
    have hmcP := hmc m (by omega) (Rest u v) (G.comap (Subtype.val : Rest u v → V)) _
      (by omega) hK0 hKX
    have hKN : (1 - σ) * (n : ℝ) ^ 2 / 2 / (Fintype.card (Rest u v) : ℝ) ^ 2 ≤
        (1 - σ) * (1 + σ / 4) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hnN2 hσ']
    have hηρ : η ≤ ρ / 8 := min_le_left _ _
    have hησ : η ≤ σ / 16 := min_le_right _ _
    refine hfinal (fun ω => (∃ i, (((univ.filter fun j => G.Adj (ω i).val (ω j).val).card : ℕ) : ℝ) <
        (m - 1) * ((univ.filter (fun b : Rest u v => G.Adj (ω i).val b.val)).card : ℝ) /
          Fintype.card (Rest u v) - t) ∨
      ((((univ.filter fun j => G.Adj u (ω j).val).card : ℕ) : ℝ) <
        m * ((univ.filter fun b : Rest u v => G.Adj u b.val).card : ℝ) /
          Fintype.card (Rest u v) - t) ∨
      ((((univ.filter fun j => G.Adj v (ω j).val).card : ℕ) : ℝ) <
        m * ((univ.filter fun b : Rest u v => G.Adj v b.val).card : ℝ) /
          Fintype.card (Rest u v) - t) ∨
      (∃ a : Fin m → Bool, (m : ℝ) ^ 2 * ((1 - σ) * (n : ℝ) ^ 2 / 2 /
          (Fintype.card (Rest u v) : ℝ) ^ 2) + η * (m : ℝ) ^ 2 ≤
        cutQ (G.comap (Subtype.val : Rest u v → V)) ω a)) ?_ ?_
    · have hdegP := deg_lower (α := Rest u v) m (fun a b => G.Adj a.val b.val)
        (fun a => G.loopless.irrefl _) t ht0
      have huP := count_lower (α := Rest u v) m (fun b => G.Adj u b.val) t ht0
      have hvP := count_lower (α := Rest u v) m (fun b => G.Adj v b.val) t ht0
      refine (pProb_or_le hP _ _).trans ?_
      refine (add_le_add hdegP ((pProb_or_le hP _ _).trans (add_le_add huP
        ((pProb_or_le hP _ _).trans (add_le_add hvP hmcP))))).trans ?_
      linarith only [hmE, hE, hρ, hηρ]
    · intro ω hω hnb
      simp only [not_or, not_exists, not_lt, not_le] at hnb
      obtain ⟨hd, hu, hv, hb⟩ := hnb
      refine ⟨hmindeg ω hω hd hu hv, fun hX => ?_⟩
      exact not_ext_ii_of_events G huv' hω hσ hσ1 hησ hm4 hσm hKN hb hX.2


end NashWilliams18
