-- To Prove: Spivak 1 problem 21

-- if |x-x0| < min(ε / 2 (|y_0| + 1), 1)
-- and |y-y0| < (ε / 2 (|x_0| + 1)
-- then |xy - x0y0| < ε

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

def norm (x y : ℝ) : ℝ := |x| + |y|

theorem spivak_1_21 (x0 y0 x y : ℝ) (ε : ℝ) (hε : ε > 0)
  (hx : |x - x0| < min (ε / (2 * (|y0| + 1))) 1)
  (hy : |y - y0| < ε / (2 * (|x0| + 1))) :
  |x * y - x0 * y0| < ε := by
  -- declare εx and εy
  set εx := (x - x0) with hεx
  set εy := (y - y0) with hεy
  have hxx : x = εx + x0 := by linarith
  have hyy : y = εy + y0 := by linarith
  -- substitute for x and y everywhere
  rw [hxx, hyy]
  ring_nf
  -- split the minimum into two hypotheses
  have hx₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ := lt_of_lt_of_le hx (min_le_right _ _)
  -- Build the constraints multipled by |y0| and |x0| respectively
  have h2 : |εx| * |y0| <= (ε / (2 * (|y0| + 1))) * |y0| := by
    apply mul_le_mul_of_nonneg_right
    · apply le_of_lt
      exact hx₁
    · apply abs_nonneg
  have h3 : |εy| * |x0| <= (ε / (2 * (|x0| + 1))) * |x0| := by
    apply mul_le_mul_of_nonneg_right
    · apply le_of_lt
      exact hy
    · apply abs_nonneg
  -- Form a useful bound on a function of |x| that will occur
  have bound : ∀ x : ℝ, |x| / (|x| + 1) + 1 < 2 := by
    intro x
    have h3 : |x| / (|x| + 1) < (|x| + 1) / (|x| + 1) := by
      apply div_lt_div_of_pos_right
      · linarith
      · positivity
    rw [div_self (by positivity)] at h3
    linarith
  -- Now we can combine to get the final result by calculation
  calc |εx * εy + εx * y0 + x0 * εy|
    _ ≤ |εx * εy + εx * y0| + |x0 * εy| := by
      simpa using abs_add_le (εx * εy + εx * y0) (x0 * εy)
    _ ≤ |εx * εy| + |εx * y0| + |x0 * εy| := by
      simpa using abs_add_le (εx * εy) (εx * y0)
    _ ≤ |εy| + |εx * y0| + |x0 * εy| := by
      apply add_le_add_left
      apply add_le_add_left
      rw [abs_mul]
      apply mul_le_of_le_one_left
      · apply abs_nonneg
      · apply le_of_lt
        exact hx₂
    _ ≤ |εy| + |εx| * |y0| + |x0| * |εy| := by
      rw [abs_mul]
      rw [abs_mul]
    _ < (ε / (2 * (|y0| + 1))) * |y0|
      + (ε / (2 * (|x0| + 1))) * |x0| +
      (ε / (2 * (|x0| + 1))) := by
      linarith -- uses h2 and h3 and hy
    _ = (ε / 2) * (|y0| / (|y0| + 1) + 1) := by
      field_simp
      ring
    _ < (ε / 2) * (2) := by
      apply mul_lt_mul_of_pos_left
      · apply bound
      · simpa [Nat.ofNat_pos, div_pos_iff_of_pos_right]
    _ = ε := by
      simp


-- To Prove: Spivak 1 problem 22

-- if y0 ne 0 and |y-y0| < min (|y0| / 2, ε |y0|^2 / 2)
-- then |1/y - 1/y0| < ε

theorem spivak_1_22 (y0 y : ℝ) (ε : ℝ) (hε : ε > 0) (hy0 : y0 ≠ 0)
  (hy : |y - y0| < min (|y0| / 2) (ε * |y0|^2 / 2)) :
  |1 / y - 1 / y0| < ε := by
  have hy₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy₂ := lt_of_lt_of_le hy (min_le_right _ _)
