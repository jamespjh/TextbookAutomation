-- Working through Numerical Analysis by Burden and Faires
-- Chapter 1: Mathematical Preliminaries

-- 1.1 Review of calculus

-- Definition 1.1 to 1.4: limits and continuity of functions

-- definition of a limit of a function
-- state the definition from the book and then find the corresponding
-- definition in Mathlib and prove them equivalent

-- Basically, take the sophisticated theory of filters
-- (see https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html#filters)
-- and prove that it matches the epsilon-delta definition

import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Real.Basic

import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Basic

namespace Burden
  def Tendsto (f : ℝ → ℝ) (x₀ L : ℝ) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ x, (0 < |x - x₀| ∧ |x - x₀| < δ) → |f x - L| < ε
  def ContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
    Tendsto f x₀ (f x₀)
  def TendstoSequence (f : ℕ → ℝ) (L : ℝ) : Prop :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n - L| < ε
end Burden

open Topology Filter

namespace FilterBased
  def Tendsto (f : ℝ → ℝ) (x₀ L : ℝ) : Prop := Filter.Tendsto f (𝓝[≠] x₀) (𝓝 L)
  def PContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop := Filter.Tendsto f (𝓝[≠] x₀) (𝓝 (f x₀))
  -- def ContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop := Filter.Tendsto f (𝓝 x₀) (𝓝 (f x₀)) -- in mathlib
  def TendstoSequence (f : ℕ → ℝ) (L : ℝ) : Prop := Filter.Tendsto f Filter.atTop (𝓝 L)
end FilterBased

-- State a set-theoretic definition of the definitions as well, as it
-- helps to show the stages

namespace SetBased
  def Tendsto (f : ℝ → ℝ) (x₀ L : ℝ) : Prop :=
    ∀ ε > 0, ∃ δ > 0, {x₀}ᶜ ∩ (Metric.ball x₀ δ )   ⊆ f ⁻¹' (Metric.ball L ε)
  def TendstoSequence (f : ℕ → ℝ) (L : ℝ) : Prop :=
    ∀ ε > 0, ∃ N, {n | n ≥ N} ⊆ f ⁻¹' (Metric.ball L ε)
end SetBased

-- Prove equivalence of filter-based and epsilon-delta definitions
-- by going via the set-theoretic ball-based definition
-- to show the stages

theorem SetBasedTendsto_iff_BurdenTendsto (f : ℝ → ℝ) (x₀ L : ℝ) :
    Burden.Tendsto f x₀ L ↔ SetBased.Tendsto f x₀ L := by
  unfold SetBased.Tendsto
  unfold Burden.Tendsto
  simp [Real.dist_eq,  Set.subset_def, sub_eq_zero]

theorem FilterTendsto_iff_SetBasedTendsto (f : ℝ → ℝ) (x₀ L : ℝ) :
  SetBased.Tendsto f x₀ L ↔ FilterBased.Tendsto f x₀ L := by
  unfold FilterBased.Tendsto
  unfold SetBased.Tendsto
  unfold Tendsto
  simp [Filter.le_def,  Metric.mem_nhds_iff, Metric.mem_nhdsWithin_iff, Set.inter_comm]
  apply Iff.intro
  · intro h cn ε εp hcn
    have := h ε εp
    rcases this with ⟨δ, δp, hδ⟩
    use δ
    constructor
    . exact δp
    exact Set.Subset.trans hδ (Set.preimage_mono hcn)
  · intro h ε εp
    have := h (Metric.ball L ε) ε εp
    simp at this
    rcases this with ⟨δ, δp, hδ⟩
    use δ

theorem FilterTendsto_iff_BurdenTendsto (f : ℝ → ℝ) (x₀ L : ℝ) :
    Burden.Tendsto f x₀ L ↔ FilterBased.Tendsto f x₀ L := by
    apply Iff.intro <;> simp [FilterTendsto_iff_SetBasedTendsto, SetBasedTendsto_iff_BurdenTendsto]

theorem FilterPuncturedContinuousAt_iff_BurdenContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) :
    Burden.ContinuousAt f x₀ ↔ FilterBased.PContinuousAt f x₀ := by
  unfold FilterBased.PContinuousAt
  unfold Burden.ContinuousAt
  simp [FilterTendsto_iff_BurdenTendsto]
  unfold FilterBased.Tendsto
  unfold Tendsto
  trivial

-- Not to do with Burden, but worth noting that the punctured
-- and non-punctured definitions of continuity are equivalent.

-- A reminder of the key fact: a neighbourhood is any set that contains a ball
-- Not the balls themselves, but any set that contains a ball.

example: Metric.ball (1: ℝ) 0.1 ∪ {2} ∈ 𝓝 (1: ℝ) := by
  simp [Metric.mem_nhds_iff]
  use 0.1
  constructor
  . norm_num
  . simp

-- So a set which is a neighbourhood is also a punctured neighbourhood
-- even though a ball is not a punctured neighbourhood it still contains a punctured neighbourhood, and so is a neighbourhood.
-- and so is a punctured neighbourhood.

example: x ∈ 𝓝 x₀ → x ∈ 𝓝[≠] (x₀ : ℝ) := by
  have : 𝓝[≠] x₀ ≤ 𝓝 x₀ := by
    exact nhdsWithin_le_nhds
  apply Filter.le_def.mp
  exact this

-- Proving the punctured and non-punctured definitions of continuity are equivalent is a bit more work, but it is just a matter of unpacking the definitions and using the fact that a neighbourhood contains a punctured neighbourhood.
-- One direction is easy - use transitivity with the definition of the <= relation on filters
-- The other requires the fact that the image neighbourhood is unpunctured,
-- so we can prove the limit point image goes where it should, and fill in the hole

-- Two key lemmas:

theorem mem_lemma {a b: Set α} {x: α} : a ∩ {x}ᶜ ⊆ b → x ∈ b → a ⊆ b := by
  intro h1 h2 y hy
  by_cases h3: y = x
  . rw [h3]
    exact h2
  . have : y ∈ ({x}ᶜ : Set α) := by
      simp [Set.mem_compl_iff]
      exact h3
    have : y ∈ a ∩ {x}ᶜ := by
      simp [Set.mem_inter_iff]
      constructor <;> assumption
    exact Set.subset_def.mp h1 y this

theorem in_nhd_lemma [TopologicalSpace α] {x: α} : s ∈ 𝓝 x → x ∈ s := by
    -- prove using definition of neighbourhoods
    intro h
    simp [mem_nhds_iff] at h
    rcases h with ⟨t, ht, hts, htss⟩
    exact Set.subset_def.mpr ht htss

-- And the proof

theorem PFContinuousAt_iff_ContinuousAt [TopologicalSpace α] [TopologicalSpace β] (f : α → β) (x₀ : α) :
    ContinuousAt f x₀ ↔ Filter.Tendsto f (𝓝[≠] x₀) (𝓝 (f x₀)) := by
  unfold ContinuousAt
  unfold Filter.Tendsto
  apply Iff.intro
  . apply le_trans
    apply Filter.map_mono
    apply nhdsWithin_le_nhds
  . simp [Filter.le_def]
    intro h s sp
    have h2 := h s sp
    have := in_nhd_lemma sp
    have h4 : x₀ ∈ f ⁻¹' s := by
      simpa [Set.mem_setOf_eq]
    simp [mem_nhds_iff]
    simp [mem_nhdsWithin] at h2
    rcases h2 with ⟨t, ht, hts, htss⟩
    use t
    constructor
    . exact mem_lemma htss h4
    . constructor <;> assumption

theorem PContinContinuousAt_iff_ContinuousAt (f : ℝ  → ℝ ) (x₀ : ℝ ) :
    ContinuousAt f x₀ ↔ FilterBased.PContinuousAt f x₀ := by
  unfold FilterBased.PContinuousAt
  simp [PFContinuousAt_iff_ContinuousAt]

-- The equivalence of the sequence definitions:

theorem SetBasedTendstoSequence_iff_BurdenTendstoSequence (f : ℕ → ℝ) (L : ℝ) :
    Burden.TendstoSequence f L ↔ SetBased.TendstoSequence f L := by
  unfold SetBased.TendstoSequence
  unfold Burden.TendstoSequence
  simp [Real.dist_eq, Set.subset_def]

theorem FilterTendstoSequence_iff_SetBasedTendstoSequence (f : ℕ → ℝ) (L : ℝ) :
    SetBased.TendstoSequence f L ↔ FilterBased.TendstoSequence f L := by
  unfold FilterBased.TendstoSequence
  unfold SetBased.TendstoSequence
  unfold Tendsto
  simp [Filter.le_def, Metric.mem_nhds_iff]
  apply Iff.intro
  . intro h s ε εp hcn
    simp [Set.subset_def] at hcn
    have := h ε εp
    rcases this with ⟨N, hN⟩
    use N
    intro n ltn
    have := hN ltn
    exact hcn (f n) this
  . intro h ε εp
    have := h (Metric.ball L ε) ε εp
    simp at this
    rcases this with ⟨N, hb⟩
    use N
    intro m
    exact hb m

-- Theorem 1.4: the equivalence of continuity of a function at a point and the limit of the function along any sequence converging to that point

-- This is tendsto_nhds_iff_seq_tendsto in Mathlib.Topology.Sequences,
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Sequences.lean

-- The trick, for the harder converse, is to go from statments about countable sets (the sequences)
-- to statements about uncountable sets (the neighbourhoods).

-- Define the filter which is the sets that contain all sequences that tend to x₀,
-- and show that it is precisely the sets that contain a ball at x₀, and so is the same as the neighbourhood filter at x₀.

def all_seq_tendsto_filter (x₀ : ℝ) : Filter ℝ :=
  -- { s | ∀ (xi : ℕ → ℝ), ( map xi atTop ≤ 𝓝 x₀) → s ∈ map xi atTop xi}
  -- plus the proofs that this is a valid filter.
  -- But a filter that contains all the sets in two other filters, is defined as the supremum of those two filters
  -- so we can just define it as the supremum of the filters generated by the sequences that tend to x₀
  ⨆ (xi : ℕ → ℝ) (_ : map xi atTop ≤ 𝓝 x₀), map xi atTop

-- a quick example showing the definition is as intended

example (x₀ : ℝ) (xii : ℕ → ℝ) (h : map xii atTop ≤ 𝓝 x₀) : map xii atTop ≤ all_seq_tendsto_filter x₀ := by
  unfold all_seq_tendsto_filter
  refine le_iSup_of_le xii ?x
  have : Nonempty (map xii atTop ≤ 𝓝 x₀) := by use h
  rw [iSup_const]

-- with this notation, the fact that it might be equal to the neighborhood filter is reasonable.

-- We need the Frechet-Urysohn property for ℝ, which is a metric space, and so first countable, and so Frechet-Urysohn

-- We will prove directly using epsilon-delta arguments for balls and sequences in the reals
-- that a set containing all sequences that tend to x₀ is a neighbourhood of x₀

noncomputable def xi (x₀ : ℝ) (n : ℕ) : ℝ := x₀ + ((n:ℝ) + 1)⁻¹

theorem inv_mono : ∀ (n N: ℕ), N ≤ n → ((n: ℝ ) + 1)⁻¹ ≤ ((N : ℝ ) + 1)⁻¹ := by
  intro n N ltn
  gcongr

theorem inv_range : ∀ (δ : ℝ), 0 < δ → ∃ n:ℕ, ((n: ℝ )+1)⁻¹ < δ := by
  intro δ δp
  have := exists_nat_one_div_lt δp
  norm_num at this
  norm_cast at *

theorem inv_conv_zero : ∀ (δ : ℝ), 0 < δ → ∃ N, ∀ (n: ℕ), N ≤ n → ((n:ℝ )+1)⁻¹ < δ := by
  intro δ δp
  have := inv_range δ δp
  rcases this with ⟨N, hN⟩
  use N
  intro n ltn
  have := inv_mono n N ltn
  exact lt_of_le_of_lt this hN

theorem pos_lem : ∀ n: ℕ, |(n: ℝ ) + 1| = n + 1 := by
    intro n
    norm_num
    positivity

theorem xi_dist_pos : ∀ n, 0 < |xi x₀ n - x₀| := by
  intro n
  simp [xi]
  positivity

theorem xi_tends_to_x₀ : ∀ δ, 0 < δ → ∃ N, ∀ (n: ℕ), N ≤ n → |xi x₀ n - x₀| < δ := by
  intro δ δp
  unfold xi
  norm_num
  simp_rw [pos_lem]
  exact inv_conv_zero δ δp

theorem set_containing_all_sequences_tending_to_x₀_is_nhd (s : Set ℝ) (x₀ : ℝ) :
  (∀ (xi : ℕ → ℝ), (∀ δ, 0 < δ → ∃ N, ∀ n, N ≤ n → |xi n - x₀| < δ) ->
  ∃ N1, ∀ n, N1 ≤ n -> xi n ∈ s) -> ∃ ε, 0 < ε ∧ ∀ (x : ℝ), |x - x₀| < ε → x ∈ s := by
    intro h
    by_contra h1
    simp at h1
    have := fun n => h1 |(xi x₀ n)-x₀| (xi_dist_pos n)
    simp [xi] at this
    choose badn b c using this
    have badn_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, |badn n - x₀| < ε := by
      intro ε εp
      have := (inv_range ε εp)
      rcases this with ⟨N, hN⟩
      use N
      intro n ltn
      have b2 := b n
      have := inv_mono n N ltn
      norm_num at *
      have := lt_of_le_of_lt this hN
      simp_rw [pos_lem] at *
      exact lt_trans b2 this
    have h2 := h badn badn_conv
    rcases h2 with ⟨N, hN⟩
    have := hN N (le_refl N)
    have := c N
    contradiction

theorem nhd_contains_all_seq_tending_to_x₀ (s : Set ℝ) (x₀ : ℝ) :
  (∃ ε, 0 < ε ∧ ∀ (x : ℝ), |x - x₀| < ε → x ∈ s) -> ∀ (xi : ℕ → ℝ), (∀ δ, 0 < δ → ∃ N, ∀ n, N ≤ n → |xi n - x₀| < δ) ->
  ∃ N1, ∀ n, N1 ≤ n -> xi n ∈ s := by
    intro h xi hxi
    rcases h with ⟨ε, εp, hε⟩
    have := hxi ε εp
    rcases this with ⟨N1, hN1⟩
    use N1
    intro n ltn
    have := hN1 n ltn
    exact hε (xi n) this

theorem nhd_is_set_containing_all_seq_tending_to_x₀ (s : Set ℝ) (x₀ : ℝ) :
  (∃ ε, 0 < ε ∧ ∀ (x : ℝ), |x - x₀| < ε → x ∈ s) ↔ ∀ (xi : ℕ → ℝ), (∀ δ, 0 < δ → ∃ N, ∀ n, N ≤ n → |xi n - x₀| < δ) ->
  ∃ N1, ∀ n, N1 ≤ n -> xi n ∈ s := by
    apply Iff.intro
    . exact nhd_contains_all_seq_tending_to_x₀ s x₀
    . exact set_containing_all_sequences_tending_to_x₀_is_nhd s x₀

-- We can now prove our supremum filter is the same as the neighborhood filter

theorem all_seq_tendsto_filter_eq_nhds (x₀ : ℝ) : all_seq_tendsto_filter x₀ = 𝓝 x₀ := by
  unfold all_seq_tendsto_filter
  apply le_antisymm
  . simp only [iSup_le_iff, imp_self, implies_true]
  . intro s hs
    simp at hs --mem_iSup, mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage
    simp [Metric.mem_nhds_iff, Metric.ball, Real.dist_eq]
    have : ∀ xii: ℕ → ℝ, map xii atTop ≤ 𝓝 x₀ ↔ Tendsto xii atTop (𝓝 x₀) := by
      unfold Tendsto; simp
    simp_rw [this] at hs
    simp [Metric.tendsto_nhds, Real.dist_eq] at hs
    -- We are now in a pure epsilon-delta world --
    have := set_containing_all_sequences_tending_to_x₀_is_nhd s x₀ hs
    simp [Set.subset_def]
    assumption

theorem FilterBasedContinuous_iff_FilterBasedTendstoSequence (f : ℝ → ℝ)  (x₀: ℝ):
    ContinuousAt f x₀ ↔ ∀ (xs : ℕ → ℝ), ( FilterBased.TendstoSequence xs x₀) → FilterBased.TendstoSequence (f ∘ xs) (f x₀) := by
      unfold ContinuousAt
      unfold FilterBased.TendstoSequence
      unfold Tendsto
      apply Iff.intro
      . intro lt1 hxi lt2
        have h1 : map (f ∘ hxi) atTop = map f (map hxi atTop) := by
            apply Filter.map_map
        have h2 : map f (map hxi atTop) ≤ map f (𝓝 x₀) := by
            exact Filter.map_mono lt2
        rw [<-h1] at h2
        exact le_trans h2 lt1
      . intro lt1
        have : map f (all_seq_tendsto_filter x₀) ≤ 𝓝 (f x₀) := by
          unfold all_seq_tendsto_filter
          simp_rw [map_iSup, iSup_le_iff, map_map]
          assumption
        rw [all_seq_tendsto_filter_eq_nhds] at this
        exact this

theorem BurdenContinuousAt_iff_BurdenTendstoSequence (f : ℝ → ℝ)  (x₀: ℝ):
  ContinuousAt f x₀ ↔ ∀ (xi : ℕ → ℝ), ( Burden.TendstoSequence xi x₀) → Burden.TendstoSequence (f ∘ xi) (f x₀) := by
    simp [FilterBasedContinuous_iff_FilterBasedTendstoSequence,
          SetBasedTendstoSequence_iff_BurdenTendstoSequence,
          FilterTendstoSequence_iff_SetBasedTendstoSequence]

-- It is nice to show the whole thing in epsilon-delta form as well
theorem BurdenContinuousAt_iff_BurdenTendstoSequence' (f : ℝ → ℝ)  (x₀: ℝ):
  ContinuousAt f x₀ ↔ ∀ (xi : ℕ → ℝ), ( Burden.TendstoSequence xi x₀) → Burden.TendstoSequence (f ∘ xi) (f x₀) := by
    unfold Burden.TendstoSequence
    unfold ContinuousAt
    unfold Tendsto
    simp [Filter.le_def,  Metric.mem_nhds_iff]
    unfold Metric.ball
    simp [Real.dist_eq]
    unfold Set.preimage
    apply Iff.intro
    . intro h1 xi h2 ε lt
      have := h1 {y | |y - f x₀| < ε} ε lt
      simp at this
      rcases this with ⟨δ, δp, hδ⟩
      have := h2 δ δp
      rcases this with ⟨N, hN⟩
      use N
      intro n ltn
      have := hN n ltn
      exact hδ (xi n) this
    . intro h1 s ε lt b
      simp [Set.subset_def] at *
      simp_rw [<-Set.mem_preimage]
      rw [nhd_is_set_containing_all_seq_tending_to_x₀ (f⁻¹' s) x₀]
      intro xi hxi
      have := h1 xi hxi ε lt
      rcases this with ⟨N, hN⟩
      use N
      intro n ltn
      have := b (f (xi n)) (hN n ltn)
      assumption
