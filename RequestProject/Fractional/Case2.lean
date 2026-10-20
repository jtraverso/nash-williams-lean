/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.Fractional.Status

/-!
# Lemma 6.1, case (2)

Notation of the paper: `x ∈ N⁺(u) ∩ N⁻(v)`, `y, z ∈ N⁺(u) ∩ N⁺(v)`, the edge `yz` is negative,
and `g1 = ux, g2 = uz, g3 = vz, g4 = vy, g5 = xy, g6 = xz, g7 = f = uv, g8 = yz, g9 = vx,
g10 = uy`.
-/

namespace NashWilliams.Frac

lemma core2_expand {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (hf : f < 0) (s1 : 0 < g1)
    (s9 : g9 < 0) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 =
      (-f) * (normT g1 g10 g5 + normT g1 g2 g6) +
      demF g10 f g4 * (normT g10 g1 g5 + normT g10 g2 g8) +
      demF g4 f g10 * (normT g4 g9 g5 + normT g4 g3 g8) +
      demF g2 f g3 * (normT g2 g1 g6 + normT g2 g10 g8) +
      demF g3 f g2 * (normT g3 g9 g6 + normT g3 g4 g8) := by
  unfold ValT ValE vterm
  rw [demF_obtuse s1 hf s9, demF_of_nonpos s9.le]
  ring

set_option maxHeartbeats 8000000 in
/-- Lemma 6.1 (2a: negative edges `xy`, `yz`). -/
lemma core2a {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : 0 < g10) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s8 : g8 < 0) (s5 : g5 < 0) (s6 : 0 < g6) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, n1a, -, n12, -, -, -, -⟩, -, ⟨na4, na2, -, -, -, -⟩, ⟨-, n43, n45, -, -⟩,
    ⟨n23, -, -, -⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hF : 0 < -f := by linarith [h.hf]
  have hA := demF_pair h.hf (ne_of_gt s10) (ne_of_gt s4) na4 h.cx
  have hB := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA1 := demF_nonneg g10 f g4
  have hA2 := demF_nonneg g4 f g10
  have hB1 := demF_nonneg g2 f g3
  have hB2 := demF_nonneg g3 f g2
  rw [core2_expand h.hf s1 s9]
  rw [normT_comm g10 g2 g8, normT_comm g2 g10 g8, normT_comm g4 g3 g8, normT_comm g3 g4 g8]
  rw [normT_comm g1 g10 g5, normT_comm g10 g1 g5, normT_of_nonneg s2.le s6.le, normT_of_nonneg s1.le s6.le]
  have := normT_nonneg g1 g5 g10; have := normT_le_one g1 g5 g10 (by linarith)
  have := normT_nonneg g10 g5 g1; have := normT_le_one g10 g5 g1 (by linarith)
  have := normT_nonneg g10 g8 g2; have := normT_le_one g10 g8 g2 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g4 g8 g3; have := normT_le_one g4 g8 g3 (by linarith)
  have := normT_nonneg g2 g8 g10; have := normT_le_one g2 g8 g10 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g3 g8 g4; have := normT_le_one g3 g8 g4 (by linarith)
  rcases acute_status s1 s10 s5 n1a with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s10 s2 s8 na2 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s3 s8 n43 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s3 s6 s9 n36 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s10 s4 h.hf na4 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen2 hF hA hB hA1 hA2 hB1 hB2 ?_ ?_ ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | exact Or.inr (Or.inl ‹_›)
     | (right; right; linarith))

set_option maxHeartbeats 8000000 in
/-- Lemma 6.1 (2a, symmetric form: negative edges `xz`, `yz`). -/
lemma core2c {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : 0 < g10) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s8 : g8 < 0) (s5 : 0 < g5) (s6 : g6 < 0) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, n1a, -, n12, -, -, -, -⟩, -, ⟨na4, na2, -, -, -, -⟩, ⟨-, n43, n45, -, -⟩,
    ⟨n23, -, -, -⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hF : 0 < -f := by linarith [h.hf]
  have hA := demF_pair h.hf (ne_of_gt s10) (ne_of_gt s4) na4 h.cx
  have hB := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA1 := demF_nonneg g10 f g4
  have hA2 := demF_nonneg g4 f g10
  have hB1 := demF_nonneg g2 f g3
  have hB2 := demF_nonneg g3 f g2
  rw [core2_expand h.hf s1 s9]
  rw [normT_comm g10 g2 g8, normT_comm g2 g10 g8, normT_comm g4 g3 g8, normT_comm g3 g4 g8]
  rw [normT_of_nonneg s10.le s5.le, normT_of_nonneg s1.le s5.le, normT_comm g1 g2 g6, normT_comm g2 g1 g6]
  have := normT_nonneg g1 g6 g2; have := normT_le_one g1 g6 g2 (by linarith)
  have := normT_nonneg g10 g8 g2; have := normT_le_one g10 g8 g2 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g4 g8 g3; have := normT_le_one g4 g8 g3 (by linarith)
  have := normT_nonneg g2 g6 g1; have := normT_le_one g2 g6 g1 (by linarith)
  have := normT_nonneg g2 g8 g10; have := normT_le_one g2 g8 g10 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g3 g8 g4; have := normT_le_one g3 g8 g4 (by linarith)
  rcases acute_status s1 s2 s6 n12 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s10 s2 s8 na2 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s5 s9 n45 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s3 s8 n43 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s10 s4 h.hf na4 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen2 hF hA hB hA1 hA2 hB1 hB2 ?_ ?_ ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | exact Or.inr (Or.inl ‹_›)
     | (right; right; linarith))

set_option maxHeartbeats 8000000 in
/-- Lemma 6.1 (2b: the only negative edge is `yz`). -/
lemma core2b {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : 0 < g10) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s8 : g8 < 0) (s5 : 0 < g5) (s6 : 0 < g6) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨-, ⟨-, n1a, -, n12, -, -, -, -⟩, -, ⟨na4, na2, -, -, -, -⟩, ⟨-, n43, n45, -, -⟩,
    ⟨n23, -, -, -⟩, ⟨-, n36, -⟩, -⟩ := hnd
  have c1 := h.cuwx; have c2 := h.cvwx; have c3 := h.cuwy; have c4 := h.cvxy
  have c5 := h.cvwy; have c6 := h.cuxy; have c7 := h.cwxy
  have c8 := h.cw; have c9 := h.cx; have c10 := h.cy
  have hF : 0 < -f := by linarith [h.hf]
  have hA := demF_pair h.hf (ne_of_gt s10) (ne_of_gt s4) na4 h.cx
  have hB := demF_pair h.hf (ne_of_gt s2) (ne_of_gt s3) n23 h.cy
  have hA1 := demF_nonneg g10 f g4
  have hA2 := demF_nonneg g4 f g10
  have hB1 := demF_nonneg g2 f g3
  have hB2 := demF_nonneg g3 f g2
  rw [core2_expand h.hf s1 s9]
  rw [normT_comm g10 g2 g8, normT_comm g2 g10 g8, normT_comm g4 g3 g8, normT_comm g3 g4 g8]
  rw [normT_of_nonneg s10.le s5.le, normT_of_nonneg s1.le s5.le, normT_of_nonneg s2.le s6.le, normT_of_nonneg s1.le s6.le]
  have := normT_nonneg g10 g8 g2; have := normT_le_one g10 g8 g2 (by linarith)
  have := normT_nonneg g4 g9 g5; have := normT_le_one g4 g9 g5 (by linarith)
  have := normT_nonneg g4 g8 g3; have := normT_le_one g4 g8 g3 (by linarith)
  have := normT_nonneg g2 g8 g10; have := normT_le_one g2 g8 g10 (by linarith)
  have := normT_nonneg g3 g9 g6; have := normT_le_one g3 g9 g6 (by linarith)
  have := normT_nonneg g3 g8 g4; have := normT_le_one g3 g8 g4 (by linarith)
  rcases acute_status s10 s2 s8 na2 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s5 s9 n45 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s4 s3 s8 n43 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases acute_status s3 s6 s9 n36 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s10 s4 h.hf na4 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  rcases dem_status s2 s3 h.hf n23 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;>
  first
  | (exfalso; linarith)
  | (refine le_trans (fin_gen2 hF hA hB hA1 hA2 hB1 hB2 ?_ ?_ ?_ ?_) (le_of_eq (by ring)) <;>
     first
     | exact Or.inl ‹_›
     | exact Or.inr (Or.inl ‹_›)
     | (right; right; linarith))

/-- Lemma 6.1, case (2), all sign patterns of `xy`, `xz`. -/
lemma core2 {f g1 g9 g10 g4 g2 g3 g5 g6 g8 : ℝ} (h : LH f g1 g9 g10 g4 g2 g3 g5 g6 g8)
    (s1 : 0 < g1) (s9 : g9 < 0) (s10 : 0 < g10) (s4 : 0 < g4) (s2 : 0 < g2) (s3 : 0 < g3)
    (s8 : g8 < 0) :
    ValT f g1 g9 g10 g4 g2 g3 g5 g6 g8 ≤ -4 * f := by
  obtain ⟨-, -, -, -, -, -, z5, z6, -⟩ := h.nz
  have := h.cwxy
  rcases z5.lt_or_gt with s5 | s5 <;> rcases z6.lt_or_gt with s6 | s6
  · linarith
  · exact core2a h s1 s9 s10 s4 s2 s3 s8 s5 s6
  · exact core2c h s1 s9 s10 s4 s2 s3 s8 s5 s6
  · exact core2b h s1 s9 s10 s4 s2 s3 s8 s5 s6

end NashWilliams.Frac
