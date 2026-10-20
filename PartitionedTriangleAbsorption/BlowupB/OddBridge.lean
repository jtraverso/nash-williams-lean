/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.OddTransformer

/-! # BlowupB.OddBridge — from odd link walks to the type data of the odd transformer

* `LinkWalk.pad`: an odd walk can be lengthened by `2` (back and forth along its last edge);
* `uniform_odd_length`: there is `m₀ = m₀(F)` such that every odd pair `a, b` in every link is
  joined by a walk of length exactly `2m + 1` for every `m ≥ m₀` — one transformer length
  serves all positions;
* `LinkWalk.labels`: a walk as a label sequence;
* `oddTypes_of_labels`: if the path vertices carry the labels of such walks, the type
  conditions `OddTypes` of the odd transformer hold.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedTransformer

variable {t : ℕ} {F : Finset (Multiset (Fin t))} {r : Fin t}

theorem LinkWalk.pad {n : ℕ} {a b c : Fin t} (w : LinkWalk F r n a b) (hc : Link F r b c) :
    LinkWalk F r (n + 2) a b := by
  have := w.append ((LinkWalk.single hc).append (LinkWalk.single ((link_swap F r b c).mp hc)))
  rwa [show n + (1 + 1) = n + 2 by omega] at this

theorem LinkWalk.last_link {n : ℕ} {a b : Fin t} (w : LinkWalk F r (n + 1) a b) :
    ∃ c, Link F r b c := by
  rcases w.reverse with _ | ⟨hl, _⟩
  exact ⟨_, hl⟩

theorem OddR.walk_ge {a b : Fin t} (h : OddR F r a b) :
    ∃ N, ∀ m, N ≤ m → LinkWalk F r (2 * m + 1) a b := by
  obtain ⟨n, w⟩ := h
  obtain ⟨c, hc⟩ := w.last_link
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => simpa using w
  | succ k ih =>
    have := (ih (by omega)).pad hc
    rwa [show 2 * (n + k) + 1 + 2 = 2 * (n + (k + 1)) + 1 by omega] at this

/-- **One odd length for the whole family.** -/
theorem uniform_odd_length (F : Finset (Multiset (Fin t))) :
    ∃ m₀ : ℕ, ∀ r a b : Fin t, OddR F r a b → ∀ m, m₀ ≤ m → LinkWalk F r (2 * m + 1) a b := by
  classical
  let N : Fin t × Fin t × Fin t → ℕ := fun x =>
    if h : OddR F x.1 x.2.1 x.2.2 then h.walk_ge.choose else 0
  refine ⟨univ.sup N, fun r a b h m hm => ?_⟩
  have hN : N (r, a, b) ≤ m := (le_sup (f := N) (mem_univ (r, a, b))).trans hm
  have hdef : N (r, a, b) = h.walk_ge.choose := by simp only [N, dif_pos h]
  exact h.walk_ge.choose_spec m (hdef ▸ hN)

theorem LinkWalk.labels {n : ℕ} {a b : Fin t} (w : LinkWalk F r n a b) :
    ∃ f : ℕ → Fin t, f 0 = a ∧ f n = b ∧ ∀ k, k < n → Link F r (f k) (f (k + 1)) := by
  induction w with
  | nil a => exact ⟨fun _ => a, rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | @cons n a b c hl _ ih =>
    obtain ⟨f, hf0, hfn, hfl⟩ := ih
    refine ⟨fun k => if k = 0 then a else f (k - 1), by simp, by simp [hfn], fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa [hf0] using hl
    · have := hfl (k - 1) (by omega)
      simpa [show k ≠ 0 by omega, show k - 1 + 1 = k by omega] using this

/-- **Type data from link walks.** -/
theorem oddTypes_of_labels {W : Type*} [DecidableEq W] {I : Type*} [Fintype I] [DecidableEq I]
    {p : W → Fin t} {σ : Equiv.Perm I} {x y : I → W} {m : ℕ} {a : I → ℕ → W}
    (hpy : ∀ i, p (y i) = p (x i))
    (hA : ∀ i, ({p (x i), p (x (σ i)), p (a (σ i) 0)} : Multiset (Fin t)) ∈ F)
    (f : I → ℕ → Fin t) (hlab : ∀ i k, k ≤ 2 * m → p (a i k) = f i k)
    (htop : ∀ i, f i (2 * m + 1) = p (a (σ i) 0))
    (hlink : ∀ i k, k ≤ 2 * m → Link F (p (x i)) (f i k) (f i (k + 1))) :
    OddTypes p F σ x y m a := by
  refine ⟨hpy, hA, fun i k hk => ?_⟩
  have h1 : p (oddPath σ m a i k) = f i k := by rw [oddPath_le hk, hlab i k hk]
  have h2 : p (oddPath σ m a i (k + 1)) = f i (k + 1) := by
    by_cases hk' : k + 1 ≤ 2 * m
    · rw [oddPath_le hk', hlab i (k + 1) hk']
    · rw [show k + 1 = 2 * m + 1 by omega, oddPath_top, htop]
  rw [h1, h2]
  exact hlink i k hk

end PartitionedTriangleAbsorption.BlowupB
