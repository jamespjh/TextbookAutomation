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

theorem composite_has_two_factors (n : ℕ) (h : ¬ myprime n) (hn : n > 1) : ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n := by
  unfold myprime at h
  have := not_and.mp h
  have := this (hn)
  have := not_forall.mp this
  rcases this with ⟨ m, hm ⟩
  have := Classical.not_imp.mp hm
  rcases this with ⟨ h1, h2 ⟩
  have := not_or.mp h2
  rcases this with ⟨ h3, h4 ⟩
  use m, n / m
  refine ⟨?_, ?_, ?_⟩
  have : m ≠ 0 := by
    exact ne_zero_of_dvd_ne_zero (by positivity) h1
  · have := and_imp.mp ((Nat.two_le_iff m).mpr) (by positivity) h3
    linarith
  · have n1 := mt (eq_of_div_eq_one' m n h1) (mt Eq.symm h4)
    have : n / m ≠ 0 := by
      sorry
    have := and_imp.mp ((Nat.two_le_iff (n / m)).mpr) (by positivity) n1
    linarith
  · apply Nat.mul_div_cancel' h1

theorem factor_is_less (n a b: ℕ) (h : a * b = n) (h2 : 1 < a) (h3 : 1 < b) :
  a < n := by
  sorry

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
  induction' n using Nat.strong_induction_on with l ih
  by_cases prime : myprime l
  · apply lem_prime_has_prime_factorisation l prime
  -- l is composite, so it has a factorisation into two smaller numbers
  have comp := composite_has_two_factors l prime (hn)
  rcases comp with ⟨ a, b, ha1, hb1, h2 ⟩
  -- apply the induction hypothesis to a and b
  have hpfa := ih a (factor_is_less l a b h2 ha1 hb1) ha1
  rw [mul_comm] at h2
  have hpfb := ih b (factor_is_less l b a h2 hb1 ha1) hb1
  -- combine the two lists of prime factors
  unfold has_prime_factorisation at hpfa hpfb
  rcases hpfa with ⟨ la, hla, hla2⟩
  rcases hpfb with ⟨ lb, hlb, hlb2⟩
  use (la ++ lb)
  constructor
  · sorry
  · sorry
