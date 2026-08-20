-- Theorem 1: Every number has at least one prime factorisation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic

def myprime (n : ℕ) : Prop := n > 1 ∧ ∀ m : ℕ, m ∣ n → m = 1 ∨ m = n

theorem eq_of_div_eq_one' (m n : ℕ) (hdvd : m ∣ n) (h : n / m = 1) : n = m := by
  have := Nat.mul_div_cancel' hdvd
  rw [h, mul_one] at this
  exact this.symm

theorem composite_has_two_factors (n : ℕ) (h : ¬ myprime n) (hn : n > 1) :
  ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n := by
  unfold myprime at h
  have := not_and.mp h
  have := this (hn)
  have := not_forall.mp this
  rcases this with ⟨ m, hm ⟩
  have := Classical.not_imp.mp hm
  rcases this with ⟨ h1, h2 ⟩
  have := not_or.mp h2
  rcases this with ⟨ h3, h4 ⟩
  have ⟨p, hp ⟩ := h1
  use m, p
  have hn0 : m ≠ 0 := by
    exact ne_zero_of_dvd_ne_zero (by positivity) h1
  refine ⟨?_, ?_, ?_⟩
  · have := and_imp.mp ((Nat.two_le_iff m).mpr) (by positivity) h3
    linarith
  · have : p ≠ 0 := by
      by_contra neg
      rw [neg] at hp
      simp at hp
      have := ne_of_gt (lt_trans zero_lt_one hn)
      contradiction
    have : p ≠ 1 := by
      by_contra neg
      rw [neg] at hp
      simp at hp
      exact h4 hp.symm
    have := and_imp.mp ((Nat.two_le_iff (p)).mpr) (by positivity) this
    linarith
  · exact hp.symm

def has_prime_factorisation (n : ℕ) : Prop :=
  -- exists a list of primes such that the product is n
  ∃ (l : List ℕ), (∀ p ∈ l, myprime p) ∧ l.prod = n

theorem lem_prime_has_prime_factorisation (p : ℕ) (hp : myprime p) : has_prime_factorisation p := by
  use [p]
  constructor
  · intros q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]
    assumption
  · simp

theorem one_has_prime_factorisation : has_prime_factorisation 1 := by
  use []
  constructor
  · intros p h
    apply List.forall_mem_nil
    assumption
  · simp

theorem all_has_prime_factorisation (n : ℕ) (hn : n > 1) : has_prime_factorisation n := by
  -- cases, either n is prime, in which case the list is just [n],
  -- or n is composite, in which case we can factor it into two smaller numbers,
  -- and then recursively factor those.
  induction n using Nat.strong_induction_on with
  | h l ih =>
      by_cases prime : myprime l
      · apply lem_prime_has_prime_factorisation l prime
      -- l is composite, so it has a factorisation into two smaller numbers
      have comp := composite_has_two_factors l prime (hn)
      rcases comp with ⟨ a, b, ha1, hb1, h2 ⟩
      have ln0 := ((Nat.two_le_iff l).mp hn).left
      have := dvd_of_mul_left_eq a h2
      have ble := Nat.le_of_dvd (lt_trans zero_lt_one hn) this
      have := dvd_of_mul_right_eq b h2
      have ale := Nat.le_of_dvd (lt_trans zero_lt_one hn) this
      have f1 : a * b = l * 1 := by rw [h2, mul_one]
      have anl : a ≠ l := by
        by_contra neg
        rw [neg] at f1
        have := Nat.mul_left_cancel (by positivity) f1
        exact ne_of_gt hb1 this
      have bnl : b ≠ l := by
        by_contra neg
        rw [neg, mul_comm] at f1
        have := Nat.mul_left_cancel (by positivity) f1
        exact ne_of_gt ha1 this
      have al : a < l := lt_of_le_of_ne ale anl
      have bl : b < l := lt_of_le_of_ne ble bnl
      -- apply the induction hypothesis to a and b
      have hpfa := ih a al ha1
      rw [mul_comm] at h2
      have hpfb := ih b bl hb1
      -- combine the two lists of prime factors
      unfold has_prime_factorisation at hpfa hpfb
      rcases hpfa with ⟨ la, hla, hla2⟩
      rcases hpfb with ⟨ lb, hlb, hlb2⟩
      use (la ++ lb)
      constructor
      · intro p hp
        have := List.mem_append.mp hp
        cases this
        · apply hla; assumption
        · apply hlb; assumption
      · rw [List.prod_append, hla2, hlb2, mul_comm]
        assumption

-- Note we've used a few fairly strong facts that it would be nice to prove independently:
-- List.prod_append, List.mem_append, Nat.le_of_dvd
