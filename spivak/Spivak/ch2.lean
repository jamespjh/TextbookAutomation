-- Theorem 1: Every number has at least one prime factorisation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic

def myprime (n : ℕ) : Prop := n > 1 ∧ ∀ m : ℕ, m ∣ n → m = 1 ∨ m = n

theorem composite_has_two_factors (n : ℕ) (h : ¬ myprime n) : ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n := by
  sorry

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

theorem all_has_prime_factorisation (n : ℕ) : has_prime_factorisation n := by
  -- cases, either n is prime, in which case the list is just [n],
  -- or n is composite, in which case we can factor it into two smaller numbers,
  -- and then recursively factor those.
  induction' n using Nat.strong_induction_on with l ih
  by_cases prime : myprime l
  · apply lem_prime_has_prime_factorisation l prime
  -- l is composite, so it has a factorisation into two smaller numbers
  have comp := composite_has_two_factors l prime
  rcases comp with ⟨ a, b, ha1, hb1, h2 ⟩
  have hpfa := ih a (factor_is_less l a b h2 ha1 hb1)
  rw [mul_comm] at h2
  have hpfb := ih b (factor_is_less l b a h2 hb1 ha1)
  -- apply the induction hypothesis to a and b
