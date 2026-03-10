-- Working through Numerical Analysis by Burden and Faires
-- Chapter 1: Mathematical Preliminaries

-- 1.1 Review of calculus

-- Definition 1.1

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
end Burden

-- State a set-theoretic definition of burden's limit definition

def STendsto (f : ℝ → ℝ) (x₀ L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, {x₀}ᶜ ∩ (Metric.ball x₀ δ )   ⊆ f ⁻¹' (Metric.ball L ε)

-- Prove equivalence of set-theoretic and epsilon-delta definitions

theorem STendtso_iff_BurdenTendsto (f : ℝ → ℝ) (x₀ L : ℝ) :
    Burden.Tendsto f x₀ L ↔ STendsto f x₀ L := by
  unfold STendsto
  unfold Burden.Tendsto
  simp [Real.dist_eq,  Set.subset_def, sub_eq_zero]

open Topology Filter

def RTendsto (f : ℝ → ℝ) (x₀ L : ℝ) : Prop := Filter.Tendsto f (𝓝[≠] x₀) (𝓝 L)
def RContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop := ContinuousAt f x₀
def PContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop := Filter.Tendsto f (𝓝[≠] x₀) (𝓝 (f x₀))

theorem RTendsto_iff_STendsto (f : ℝ → ℝ) (x₀ L : ℝ) :
  STendsto f x₀ L ↔ RTendsto f x₀ L := by
  unfold RTendsto
  unfold STendsto
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

theorem RTendsto_iff_BurdenTendsto (f : ℝ → ℝ) (x₀ L : ℝ) :
    Burden.Tendsto f x₀ L ↔ RTendsto f x₀ L := by
    apply Iff.intro <;> simp [RTendsto_iff_STendsto, STendtso_iff_BurdenTendsto]

-- The two continuity definitions are not quite equivalent.
-- The burden definition allows for a point discontinuity, while the filter definition does not.

theorem PContinuousAt_iff_BurdenContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) :
    Burden.ContinuousAt f x₀ ↔ PContinuousAt f x₀ := by
  unfold PContinuousAt
  unfold Burden.ContinuousAt
  simp [RTendsto_iff_BurdenTendsto]
  unfold RTendsto
  unfold Tendsto
  trivial

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

theorem mem_lemma {a b: Set ℝ} {x: ℝ} : a ∩ {x}ᶜ ⊆ b → x ∈ b → a ⊆ b := by
  intro h1 h2 y hy
  by_cases h3: y = x
  . rw [h3]
    exact h2
  . have : y ∈ ({x}ᶜ : Set ℝ) := by
      simp [Set.mem_compl_iff]
      exact h3
    have : y ∈ a ∩ {x}ᶜ := by
      simp [Set.mem_inter_iff]
      constructor <;> assumption
    exact Set.subset_def.mp h1 y this

theorem in_nhd_lemma (x: ℝ) : s ∈ 𝓝 x → x ∈ s := by
    -- prove using definition of neighbourhoods
    intro h
    simp [mem_nhds_iff] at h
    rcases h with ⟨t, ht, hts, htss⟩
    exact Set.subset_def.mpr ht htss

-- And the proof:

theorem PContinuousAt_iff_RContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) :
    RContinuousAt f x₀ ↔ PContinuousAt f x₀ := by
  unfold PContinuousAt
  unfold RContinuousAt
  unfold ContinuousAt
  unfold Tendsto
  apply Iff.intro
  . apply le_trans
    apply Filter.map_mono
    apply nhdsWithin_le_nhds
  . simp [Filter.le_def]
    intro h s sp
    have h2 := h s sp
    have := in_nhd_lemma (f x₀) sp
    have h4 : x₀ ∈ f ⁻¹' s := by
      simpa [Set.mem_setOf_eq]
    simp [mem_nhds_iff]
    simp [mem_nhdsWithin] at h2
    rcases h2 with ⟨t, ht, hts, htss⟩
    use t
    constructor
    . exact mem_lemma htss h4
    . constructor <;> assumption
