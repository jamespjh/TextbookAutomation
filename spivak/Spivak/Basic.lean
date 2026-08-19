-- To Prove: Spivak 1 problem 21

-- if |x-x0| < min(ε / 2 (|y_0| + 1), 1)
-- and |y-y0| < (ε / 2 (|x_0| + 1)
-- then |xy - x0y0| < ε

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

def norm (x y : ℝ) : ℝ := |x| + |y|

theorem spivak_1_21 (x0 y0 x y : ℝ) (ε : ℝ)
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
  -- establish ε +ve
  have εp : 0 < ε := by
    field_simp at hy
    have : 0 < 2 * (|x0| + 1) := by
      apply mul_pos
      · linarith
      · positivity
    have : 0 <= |εy| * (2 * (|x0| + 1)) := by
      apply mul_nonneg
      · apply abs_nonneg
      · linarith
    linarith
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
      · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right]
        assumption
    _ = ε := by
      simp


-- To Prove: Spivak 1 problem 22

-- if y0 ne 0 and |y-y0| < min (|y0| / 2, ε |y0|^2 / 2)
-- then |1/y - 1/y0| < ε

theorem delpos (y0 y : ℝ)
  (hy : |y - y0| < |y0| / 2) : |y| ≥ |y0|/2 := by
    -- establish the key lemmas for magnitudes
  have lem1: ∀ a b : ℝ, |a + b| ≥ |a| - |b| := by
    intro a b
    have sub := abs_add_le (-b) (a+b)
    simp at sub ; linarith
  have lem2 : |y| ≥ |y0| - |(y - y0)| := by
      have := lem1 (y0) (y - y0)
      simp only [ge_iff_le, tsub_le_iff_right]
      simp at this
      assumption
  linarith

theorem y0p (y0 : ℝ) (hy0 : y0 ≠ 0) : 0 < |y0|/2 := by
  apply div_pos
  · apply abs_pos.mpr ; assumption
  · simp

theorem spivak_1_22 (y0 y : ℝ) (ε : ℝ) (hy0 : y0 ≠ 0)
  (hy : |y - y0| < min (|y0| / 2) (ε * |y0| ^ 2 / 2)) :
  |1 / y - 1 / y0| < ε := by
  -- split the minimum into two hypotheses
  have hy₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy₂ := lt_of_lt_of_le hy (min_le_right _ _)
  -- Establish y /ne 0
  have key := delpos y0 y hy₁
  have y0p := y0p y0 hy0
  have nelem := ne_of_gt (lt_of_lt_of_le y0p key)
  have : y ≠ 0 := by
    apply abs_ne_zero.mp ; assumption
  -- substitute a new variable for y - y0
  set εy := (y - y0) with hεy
  have hyy : y = εy + y0 := by linarith
  rw [hyy]
  rw [hyy] at key
  rw [hyy] at nelem
  rw [hyy] at this
  -- And prove by calculation:
  calc |(1 / (εy + y0)) - 1 / y0|
    _ = |(y0 - (εy + y0)) / ((εy + y0) * y0)| := by
      field_simp
    _ = |(-εy) / ((εy + y0) * y0)| := by
      ring_nf
    _ = |εy| / |(εy + y0) * y0| := by
      rw [abs_div]
      rw [abs_neg]
    _ = |εy| / (|εy + y0| * |y0|) := by
      rw [abs_mul]
    _ = (|εy| / |y0|)/ (|εy + y0|) := by
      field_simp
    _ ≤ (|εy| / |y0|) / ((|y0|/2) ) := by
      -- Pull off the multiplying factor so we're left with the key proof
      apply mul_le_mul_of_nonneg_left
      -- Tidy up so form matches the key result
      · rw [inv_eq_one_div]
        rw [inv_eq_one_div]
      -- Apply our key result
        apply one_div_le_one_div_of_le (?_) (key)
        assumption
      -- Tidy up the nonnegativity conditions
      · apply div_nonneg <;> apply abs_nonneg
    _ = 2 * |εy| / (|y0| * |y0|) := by
      field_simp
    _ < ε := by
      field_simp
      field_simp at hy₂
      linarith

-- Spivak 1 problem 23
-- Choose the minimal constraints A and B to just satisfy:
-- Given y0 ne 0 and |y-y0| < A and |x-x0| < B
-- then |x/y - x0/y0| < ε
theorem spivak_1_23 (x0 y0 x y : ℝ) (ε : ℝ) (hy0 : y0 ≠ 0)
  (hy : |y - y0| < min (|y0| / 2) (ε / (2 * (|x0| + 1)) * |y0| ^ 2 / 2))
  (hx : |x - x0| < min (ε / (2 * (1 / |y0| + 1))) 1) :
  |x / y - x0 / y0| < ε := by
  -- The aim is to apply theorems 1_21 and 1_22 to the two terms of the difference
  -- Applying 21 will create a constraint on the error in y, which will
  -- Input into the error term on 21.
  have hy₁ := lt_of_lt_of_le hy (min_le_left _ _)
  -- Establish y /ne 0
  have key := delpos y0 y hy₁
  have y0p := y0p y0 hy0
  have nelem := ne_of_gt (lt_of_lt_of_le y0p key)
  have : y ≠ 0 := by
    apply abs_ne_zero.mp ; assumption
  -- substitute a new variable for 1/y
  set z := 1/y with hz
  set z0 := 1/y0 with hz0
  have znz : z ≠ 0 := by
    apply one_div_ne_zero
    assumption
  have hzz : y = 1/z := by
    field_simp
    field_simp at hz
    rw [mul_comm]
    assumption
  have hz0nz : z0 ≠ 0 := by
    apply one_div_ne_zero
    assumption
  have hzz0 : y0 = 1/z0 := by
    field_simp
    field_simp at hz0
    rw [mul_comm]
    assumption
  have hzy0 : 1 / |y0| = |z0| := by
    rw [abs_div]
    rw [abs_one]
  rw [hzz, hzz0]
  have zA : |z - z0| < ε / (2 * (|x0| + 1)) := by
    -- Rewrite ε / (2 * (|x0| + 1)) as ε'
    set ε' := ε / (2 * (|x0| + 1)) with hε'
    -- Convert back to ys
    rw [hz, hz0]
    -- Apply spivak_1_22 to get the constraint
    exact spivak_1_22 y0 y ε' hy0 hy
  simp only [one_div, div_inv_eq_mul, gt_iff_lt]
  rw [hzy0] at hx
  exact spivak_1_21 x0 z0 x z ε hx zA
