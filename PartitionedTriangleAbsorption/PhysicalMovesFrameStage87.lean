/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalMovesStage86

/-! # Framing physical move traces

A trace may be run inside a larger configuration: an untouched edge set `W`
is carried along unchanged, while the forbidden set and the history are
enlarged. The only requirement is that every edge the trace may add lies in a
host set `E` that avoids the new forbidden edges and the new history.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalMovesStage86

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Enlarging the physical host preserves a trace. -/
theorem PhysicalMoves.mono_host {E E' B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) (hE : E ⊆ E') :
    PhysicalMoves p F E' B U X Y n := by
  induction h with
  | stop U X => exact .stop U X
  | step hX hQ hf hphys hm hH hR _ ih =>
    exact .step hX hQ hf (hphys.trans hE) hm hH hR ih

/-- Added edges always avoid the initial history, so the host may be cut down
to the edges outside any part of that history. -/
theorem PhysicalMoves.restrict {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) {U₀ : Finset (Sym2 V)} (hU₀ : U₀ ⊆ U) :
    PhysicalMoves p F (E \ U₀) B U X Y n := by
  induction h generalizing U₀ with
  | stop U X => exact .stop U X
  | @step U X Y Q R H n hX hQ hf hphys hm hH hR _ ih =>
    refine .step hX hQ hf ?_ hm hH hR (ih (hU₀.trans ?_))
    · intro e he
      refine mem_sdiff.mpr ⟨hphys he, fun hu => ?_⟩
      exact disjoint_left.mp hf he (mem_union.mpr (Or.inr (hU₀ hu)))
    · intro e he
      simp only [mem_union]
      exact Or.inl (Or.inl he)

/-- Carry an untouched edge set `W` through a trace, adding `B'` to the
forbidden edges and `U'` to the history. No edge of `W` is ever moved, and
every new edge still avoids the full cumulative history. -/
theorem PhysicalMoves.frame {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) {E' B' U' W : Finset (Sym2 V)}
    (hE : E ⊆ E') (hfresh : Disjoint E (B' ∪ U')) (hW : W ⊆ U')
    (hXW : Disjoint X W) :
    PhysicalMoves p F E' (B ∪ B') (U ∪ U') (X ∪ W) (Y ∪ W) n := by
  induction h with
  | stop U X => exact .stop _ _
  | @step U X Y Q R H n hX hQ hf hphys hm hH hR _ ih =>
    have hRW : Disjoint R W := by
      rw [disjoint_left]
      intro e he hw
      exact disjoint_left.mp hfresh (hphys (mem_union.mpr (Or.inr he)))
        (mem_union.mpr (Or.inr (hW hw)))
    have hQW : Disjoint Q W := hXW.mono_left hQ
    have hnext : Disjoint ((X \ Q) ∪ R) W :=
      disjoint_union_left.mpr ⟨hXW.mono_left sdiff_subset, hRW⟩
    have htail := ih hnext
    have hcfg : (X ∪ W) \ Q ∪ R = ((X \ Q) ∪ R) ∪ W := by
      ext e
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro (⟨he | he, hq⟩ | he) <;> tauto
      · rintro ((⟨he, hq⟩ | he) | he)
        · exact Or.inl ⟨Or.inl he, hq⟩
        · exact Or.inr he
        · exact Or.inl ⟨Or.inr he, fun hq => disjoint_left.mp hQW hq he⟩
    have hhist : U ∪ U' ∪ H ∪ R = (U ∪ H ∪ R) ∪ U' := by
      ext e
      simp only [mem_union]
      tauto
    refine .step ?_ (hQ.trans subset_union_left) ?_ (hphys.trans hE) hm hH hR ?_
    · exact union_subset_union hX hW
    · rw [disjoint_left]
      intro e he hb
      simp only [mem_union] at hb
      rcases hb with (hb | hb) | (hb | hb)
      · exact disjoint_left.mp hf he (mem_union.mpr (Or.inl hb))
      · exact disjoint_left.mp hfresh (hphys he) (mem_union.mpr (Or.inl hb))
      · exact disjoint_left.mp hf he (mem_union.mpr (Or.inr hb))
      · exact disjoint_left.mp hfresh (hphys he) (mem_union.mpr (Or.inr hb))
    · rw [hcfg, hhist]
      exact htail

end PartitionedTriangleAbsorption.PhysicalMovesStage86
