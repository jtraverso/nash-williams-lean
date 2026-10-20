/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.Fractional.Status

/-!
# Lemma 6.1, case (1)

Notation of the paper: `x ∈ N⁺(u) ∩ N⁻(v)`, `y ∈ N⁺(v) ∩ N⁻(u)`, `z ∈ N⁺(u) ∩ N⁺(v)` and
`g1 = ux, g2 = uz, g3 = vz, g4 = vy, g5 = xy, g6 = xz, g7 = f = uv, g8 = yz, g9 = vx, g10 = uy`.
-/

namespace NashWilliams.Frac

lemma core1_expand {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (hf : f < 0) (s1 : 0 < g1)
    (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 =
      (-f) * (normT g1 g10 g5 + normT g4 g9 g5 + normT g1 g2 g6 + normT g4 g3 g8) +
      demF g2 f g3 * (normT g2 g1 g6 + normT g2 g10 g8) +
      demF g3 f g2 * (normT g3 g9 g6 + normT g3 g4 g8) := by
  unfold ValT ValE vterm
  rw [demF_obtuse s1 hf s9, demF_of_nonpos s9.le, demF_of_nonpos s10.le, demF_obtuse s4 hf s10]
  ring

set_option maxHeartbeats 4000000 in
/-- Lemma 6.1 (1a): the negative edges of `T` are `xz` and `yz`. -/
lemma core1a {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s5 : 0 < g5) (s6 : g6 < 0) (s8 : g8 < 0) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, -, -, n12, n13, n15, -, -⟩, -, -, ⟨n42, n43, n45, -, -⟩,
    ⟨n23, -, -, n28⟩, ⟨-, n36, -⟩, -⟩ := hnd
  rw [core1_expand h.hf s1 s9 s10 s4, normT_comm g1 g2 g6, normT_comm g2 g1 g6,
    normT_comm g4 g3 g8, normT_comm g3 g4 g8]
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have b1 := normT_nonneg g1 g10 g5; have b1' := normT_le_one g1 g10 g5 (by linarith)
  have b2 := normT_nonneg g4 g9 g5; have b2' := normT_le_one g4 g9 g5 (by linarith)
  have b3 := normT_nonneg g1 g6 g2; have b3' := normT_le_one g1 g6 g2 (by linarith)
  have b4 := normT_nonneg g4 g8 g3; have b4' := normT_le_one g4 g8 g3 (by linarith)
  have b5 := normT_nonneg g2 g6 g1; have b5' := normT_le_one g2 g6 g1 (by linarith)
  have b6 := normT_nonneg g2 g10 g8; have b6' := normT_le_one g2 g10 g8 (by linarith)
  have b7 := normT_nonneg g3 g9 g6; have b7' := normT_le_one g3 g9 g6 (by linarith)
  have b8 := normT_nonneg g3 g8 g4; have b8' := normT_le_one g3 g8 g4 (by linarith)
  have hA := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA2 := demF_nonneg g2 f g3
  have hA3 := demF_nonneg g3 f g2
  have F1 : normT g1 g6 g2 * g1 = -g6 → normT g4 g8 g3 * g4 = -g8 → g5 < g1 → g5 < g4 →
      normT g1 g6 g2 + normT g4 g8 g3 ≤ 1 :=
    fun hX hY he he' => frac_pair hX hY he he' (by linarith) b3 b4 s5
  have F2 : normT g1 g6 g2 * g1 = -g6 → normT g3 g8 g4 * g3 = -g8 → g5 < g1 → g5 < g3 →
      normT g1 g6 g2 + normT g3 g8 g4 ≤ 1 :=
    fun hX hY he he' => frac_pair hX hY he he' (by linarith) b3 b8 s5
  have F3 : normT g2 g6 g1 * g2 = -g6 → normT g4 g8 g3 * g4 = -g8 → g5 < g2 → g5 < g4 →
      normT g2 g6 g1 + normT g4 g8 g3 ≤ 1 :=
    fun hX hY he he' => frac_pair hX hY he he' (by linarith) b5 b4 s5
  have F4 : normT g2 g6 g1 * g2 = -g6 → normT g3 g8 g4 * g3 = -g8 → g5 < g2 → g5 < g3 →
      normT g2 g6 g1 + normT g3 g8 g4 ≤ 1 :=
    fun hX hY he he' => frac_pair hX hY he he' (by linarith) b5 b8 s5
  rcases acute_status s1 s5 s10 n15 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s5 s9 n45 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s1 s2 s6 n12 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s3 s8 n43 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (try have := F1 ‹_› ‹_› (by linarith) (by linarith)
     try have := F2 ‹_› ‹_› (by linarith) (by linarith)
     try have := F3 ‹_› ‹_› (by linarith) (by linarith)
     try have := F4 ‹_› ‹_› (by linarith) (by linarith)
     refine le_trans (fin_gen hA hA2 hA3 ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | (right; linarith))

set_option maxHeartbeats 4000000 in
/-- Lemma 6.1 (b). -/
lemma core1b {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s5 : g5 < 0) (s6 : g6 < 0) (s8 : 0 < g8) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, -, -, n12, n13, n15, -, -⟩, -, -, ⟨n42, n43, n45, -, -⟩,
    ⟨n23, -, -, n28⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hA := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA2 := demF_nonneg g2 f g3
  have hA3 := demF_nonneg g3 f g2
  rw [core1_expand h.hf s1 s9 s10 s4]
  rw [normT_comm g1 g2 g6, normT_comm g2 g1 g6, normT_of_nonneg s3.le s8.le, normT_of_nonneg s4.le s8.le]
  have := normT_nonneg g1 g10 g5; have := normT_le_one g1 g10 g5 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g1 g6 g2; have := normT_le_one g1 g6 g2 (by linarith)
  have := normT_nonneg g2 g6 g1; have := normT_le_one g2 g6 g1 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g2 g10 g8; have := normT_le_one g2 g10 g8 (by linarith)
  rcases acute_status s1 s2 s6 n12 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s2 s8 s10 n28 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen hA hA2 hA3 ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | (right; linarith))

set_option maxHeartbeats 4000000 in
/-- Lemma 6.1 (c). -/
lemma core1c {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s6 : 0 < g6) (s8 : 0 < g8) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, -, -, n12, n13, n15, -, -⟩, -, -, ⟨n42, n43, n45, -, -⟩,
    ⟨n23, -, -, n28⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hA := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA2 := demF_nonneg g2 f g3
  have hA3 := demF_nonneg g3 f g2
  rw [core1_expand h.hf s1 s9 s10 s4]
  rw [normT_of_nonneg s2.le s6.le, normT_of_nonneg s1.le s6.le, normT_of_nonneg s3.le s8.le, normT_of_nonneg s4.le s8.le]
  have := normT_nonneg g1 g10 g5; have := normT_le_one g1 g10 g5 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g2 g10 g8; have := normT_le_one g2 g10 g8 (by linarith)
  rcases acute_status s3 s6 s9 n36 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s2 s8 s10 n28 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen hA hA2 hA3 ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | (right; linarith))

set_option maxHeartbeats 4000000 in
/-- Lemma 6.1 (d). -/
lemma core1d {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s5 : 0 < g5) (s6 : g6 < 0) (s8 : 0 < g8) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, -, -, n12, n13, n15, -, -⟩, -, -, ⟨n42, n43, n45, -, -⟩,
    ⟨n23, -, -, n28⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hA := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA2 := demF_nonneg g2 f g3
  have hA3 := demF_nonneg g3 f g2
  rw [core1_expand h.hf s1 s9 s10 s4]
  rw [normT_comm g1 g2 g6, normT_comm g2 g1 g6, normT_of_nonneg s3.le s8.le, normT_of_nonneg s4.le s8.le]
  have := normT_nonneg g1 g10 g5; have := normT_le_one g1 g10 g5 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g1 g6 g2; have := normT_le_one g1 g6 g2 (by linarith)
  have := normT_nonneg g2 g6 g1; have := normT_le_one g2 g6 g1 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g2 g10 g8; have := normT_le_one g2 g10 g8 (by linarith)
  rcases acute_status s1 s5 s10 n15 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s5 s9 n45 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s1 s2 s6 n12 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s2 s8 s10 n28 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen hA hA2 hA3 ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | (right; linarith))

set_option maxHeartbeats 4000000 in
/-- Lemma 6.1 (e). -/
lemma core1e {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s5 : 0 < g5) (s6 : 0 < g6) (s8 : 0 < g8) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, -, -, n12, n13, n15, -, -⟩, -, -, ⟨n42, n43, n45, -, -⟩,
    ⟨n23, -, -, n28⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hA := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA2 := demF_nonneg g2 f g3
  have hA3 := demF_nonneg g3 f g2
  rw [core1_expand h.hf s1 s9 s10 s4]
  rw [normT_of_nonneg s2.le s6.le, normT_of_nonneg s1.le s6.le, normT_of_nonneg s3.le s8.le, normT_of_nonneg s4.le s8.le]
  have := normT_nonneg g1 g10 g5; have := normT_le_one g1 g10 g5 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g2 g10 g8; have := normT_le_one g2 g10 g8 (by linarith)
  rcases acute_status s1 s5 s10 n15 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s5 s9 n45 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s3 s6 s9 n36 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s2 s8 s10 n28 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen hA hA2 hA3 ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | (right; linarith))

set_option maxHeartbeats 4000000 in
/-- Lemma 6.1 (1b, symmetric form: negative edges `xy`, `yz`). -/
lemma core1f {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s5 : g5 < 0) (s6 : 0 < g6) (s8 : g8 < 0) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, -, -, n12, n13, n15, -, -⟩, -, -, ⟨n42, n43, n45, -, -⟩,
    ⟨n23, -, -, n28⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hA := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA2 := demF_nonneg g2 f g3
  have hA3 := demF_nonneg g3 f g2
  rw [core1_expand h.hf s1 s9 s10 s4]
  rw [normT_of_nonneg s2.le s6.le, normT_of_nonneg s1.le s6.le, normT_comm g4 g3 g8, normT_comm g3 g4 g8]
  have := normT_nonneg g1 g10 g5; have := normT_le_one g1 g10 g5 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g4 g8 g3; have := normT_le_one g4 g8 g3 (by linarith)
  have := normT_nonneg g3 g8 g4; have := normT_le_one g3 g8 g4 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g2 g10 g8; have := normT_le_one g2 g10 g8 (by linarith)
  rcases acute_status s4 s3 s8 n43 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s3 s6 s9 n36 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen hA hA2 hA3 ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | (right; linarith))

set_option maxHeartbeats 4000000 in
/-- Lemma 6.1 (1d, symmetric form: the only negative edge is `yz`). -/
lemma core1g {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s5 : 0 < g5) (s6 : 0 < g6) (s8 : g8 < 0) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, -, -, n12, n13, n15, -, -⟩, -, -, ⟨n42, n43, n45, -, -⟩,
    ⟨n23, -, -, n28⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hA := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA2 := demF_nonneg g2 f g3
  have hA3 := demF_nonneg g3 f g2
  rw [core1_expand h.hf s1 s9 s10 s4]
  rw [normT_of_nonneg s2.le s6.le, normT_of_nonneg s1.le s6.le, normT_comm g4 g3 g8, normT_comm g3 g4 g8]
  have := normT_nonneg g1 g10 g5; have := normT_le_one g1 g10 g5 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g4 g8 g3; have := normT_le_one g4 g8 g3 (by linarith)
  have := normT_nonneg g3 g8 g4; have := normT_le_one g3 g8 g4 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g2 g10 g8; have := normT_le_one g2 g10 g8 (by linarith)
  rcases acute_status s1 s5 s10 n15 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s5 s9 n45 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s3 s8 n43 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s3 s6 s9 n36 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen hA hA2 hA3 ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | (right; linarith))

/-- Lemma 6.1, case (1), all sign patterns of `xy`, `xz`, `yz`. -/
lemma core1 {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : g10 < 0) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  obtain ⟨-, -, -, -, -, -, z5, z6, z8⟩ := h.nz
  have := h.cwxy
  rcases z5.lt_or_gt with s5 | s5 <;> rcases z6.lt_or_gt with s6 | s6 <;>
    rcases z8.lt_or_gt with s8 | s8
  · linarith
  · exact core1b h s1 s9 s10 s4 s2 s3 s5 s6 s8
  · exact core1f h s1 s9 s10 s4 s2 s3 s5 s6 s8
  · exact core1c h s1 s9 s10 s4 s2 s3 s6 s8
  · exact core1a h s1 s9 s10 s4 s2 s3 s5 s6 s8
  · exact core1d h s1 s9 s10 s4 s2 s3 s5 s6 s8
  · exact core1g h s1 s9 s10 s4 s2 s3 s5 s6 s8
  · exact core1e h s1 s9 s10 s4 s2 s3 s5 s6 s8

end NashWilliams.Frac
