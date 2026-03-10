-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Basic

-- We will end up proving there's a common factor of p and q
-- we would then need the fact that thus we can divide it out, creating new p and q
-- this would be able to continue forever which doesn't make sense
theorem tower_means_fail (f : Nat -> Prop) (hyp : ∀ p: ℕ,
    f p -> ∃ n, n < p ∧ f n) : ∀ k, ¬ f k := by
  intro k hk
  induction' k using Nat.strong_induction_on with l ih
  have hyp2 := hyp l hk
  rcases hyp2 with ⟨ z, hlt, hzf ⟩
  exact ih z hlt hzf

def are_rational_root_two (p q : ℤ) : Prop :=
   q ≠ 0 ∧ p ^ 2 = q ^ 2 * 2

lemma even_square (n : ℕ ) : Even (n^2) → Even n := by
  intro h
  rw [pow_two] at h
  have a := Nat.even_mul.mp h
  rcases a with a | a
  exact a; exact a

lemma exists_half (n : ℕ  ) (hn : Even n) : ∃ k : ℕ  , n = k * 2 := by
  rcases hn with ⟨ k, hk ⟩
  use k
  rw [mul_comm,two_mul]
  assumption

theorem tower_of_rationals (p q : ℕ ) (h : are_rational_root_two p q) :
    ∃ (x y : ℕ ), x * 2 = p ∧ y * 2 = q ∧ are_rational_root_two x y := by
  rcases h with ⟨ qnz, h ⟩
  norm_cast at h
  norm_cast at qnz
  have qgz : 0 < q := by
    exact Nat.pos_of_ne_zero qnz
  have ep2 : Even (p^2) := by
    use q^2
    rw [<-two_mul, mul_comm]
    assumption
  rcases exists_half p (even_square p ep2) with ⟨ x, px2 ⟩
  have q2e : q ^ 2 = x ^ 2 * 2 := by
    rw [px2] at h
    ring_nf at h
    have : q ^ 2 * 2 = (x ^ 2 * 2) * 2 := by rw [<-h]; ring
    exact Nat.mul_right_cancel (by decide) this
  have eq2 : Even (q^2) := by
    use x ^ 2
    rw [q2e]
    rw [mul_comm, two_mul]
  rcases exists_half q (even_square q eq2) with ⟨ y, qy2 ⟩
  use x, y
  unfold are_rational_root_two
  refine ⟨ px2.symm, qy2.symm, ?y_positive ,?x_y_root⟩
  . rw [qy2] at qgz
    norm_cast
    exact (Nat.pos_of_mul_pos_right qgz).ne.symm
  . ring_nf
    norm_cast
    rw [px2, qy2] at h
    ring_nf at h
    have : x ^ 2 * 4 = (y ^ 2 * 2) * 4 := by rw [h]; ring
    exact Nat.mul_right_cancel (by decide) this

def part_of_root_of_two (n : ℕ ) : Prop :=
  ∃ p : ℕ, are_rational_root_two p n

theorem part_implies_tower (n : ℕ) (h : part_of_root_of_two n) :
    ∃ m < n, part_of_root_of_two m := by
  unfold part_of_root_of_two at h
  rcases h with ⟨ p, hp ⟩
  have tower := tower_of_rationals p n hp
  rcases tower with ⟨ x, y, _, defy, _ ⟩
  use y
  constructor
  . unfold are_rational_root_two at hp
    rcases hp with ⟨ nnz, _ ⟩
    have ynz : y ≠ 0 := by
      intro yz
      norm_cast at nnz
      rw [<-defy, yz, zero_mul] at nnz
      contradiction
    rw [<-defy]
    have := Nat.mul_lt_mul_of_pos_left (by decide: 1<2) (Nat.pos_of_ne_zero ynz)
    rw [Nat.mul_one] at this
    assumption
  . unfold part_of_root_of_two
    use x

theorem no_rational_root_of_two (a b : ℕ ): ¬ are_rational_root_two a b := by
  intro h
  have prb: part_of_root_of_two b := by
    unfold part_of_root_of_two
    use a
  have := tower_means_fail part_of_root_of_two part_implies_tower b prb
  contradiction

theorem negate_denom_also_root (p q : ℤ) (h : are_rational_root_two p q ) :
    are_rational_root_two p (-q) := by
  rcases h with ⟨ qnz, hsq ⟩
  unfold are_rational_root_two
  constructor
  . intro qz
    rw [neg_eq_zero] at qz
    exact qnz qz
  . rw [hsq]
    ring

theorem negate_num_also_root (p q : ℤ) (h : are_rational_root_two p q):
    are_rational_root_two (-p) q := by
  rcases h with ⟨ qnz, hsq ⟩
  unfold are_rational_root_two
  constructor
  . exact qnz
  . ring
    assumption

theorem negate_both_also_root (p q : ℤ) (h : are_rational_root_two p q):
    are_rational_root_two (-p) (-q) :=
  negate_num_also_root (p) (-q) (negate_denom_also_root p q h)

lemma lt_dichotomy (a : ℤ) (hyp: a ≠ 0) : a > 0 ∨ a < 0 := by
  rcases lt_trichotomy a 0 with h | _ | h
  . exact Or.inr h
  . contradiction
  . exact Or.inl h

theorem nat_root_two_of_int_root_two (p q : ℤ) (h: are_rational_root_two p q):
    ∃ (a b : ℕ ), are_rational_root_two a b := by
  have qne0: q ≠ 0 := by
    rcases h with ⟨qnz, _⟩
    exact qnz
  have pne0: p ≠ 0 := by
    unfold are_rational_root_two at h
    intro pz
    rcases h with ⟨qne0, hsq⟩
    rw [pz] at hsq
    ring_nf at hsq
    have := mul_eq_zero.mp hsq.symm
    rcases this with h | h
    . rw [sq_eq_zero_iff] at h
      exact qne0 h
    . contradiction
  rcases lt_dichotomy p pne0 with pg0 | pl0 <;>
  rcases lt_dichotomy q qne0 with qg0 | ql0
  . use p.toNat, q.toNat
    simpa [Int.toNat_of_nonneg pg0.le, Int.toNat_of_nonneg qg0.le]
  . use p.toNat, (-q).toNat
    have := negate_denom_also_root p q h
    have : 0 ≤ -q := by
      rw [le_neg]
      exact ql0.le
    simpa [Int.toNat_of_nonneg pg0.le, Int.toNat_of_nonneg this]
  . use (-p).toNat, q.toNat
    have := negate_num_also_root p q h
    have : 0 ≤ -p := by
      rw [le_neg]
      exact pl0.le
    simpa [Int.toNat_of_nonneg this , Int.toNat_of_nonneg qg0.le]
  . use (-p).toNat, (-q).toNat
    have := negate_both_also_root p q h
    have a : 0 ≤ -p := by
      rw [le_neg]
      exact pl0.le
    have b : 0 ≤ -q := by
      rw [le_neg]
      exact ql0.le
    simpa [Int.toNat_of_nonneg a , Int.toNat_of_nonneg b]

theorem no_rational_int_root_two (a b : ℤ ): ¬ are_rational_root_two a b := by
  intro h
  have := nat_root_two_of_int_root_two a b h
  rcases this with ⟨ x, y, hy ⟩
  have := no_rational_root_of_two x y hy
  contradiction

theorem root_two_irrational : ¬ ∃ (r : ℚ ), r ^ 2 = 2 := by
  intro h
  rw [Rat.exists] at h
  rcases h with ⟨ p, q, qnz, r_eq ⟩
  have : p ^ 2 = q ^ 2 * 2 := by
    field_simp [qnz] at r_eq
    norm_cast at r_eq
  have : are_rational_root_two p q := by
    unfold are_rational_root_two
    constructor
    . exact qnz
    . exact this
  have := no_rational_int_root_two p q this
  contradiction
