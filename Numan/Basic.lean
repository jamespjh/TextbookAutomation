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

namespace Burden
  def Tendsto (f : ℝ → ℝ) (x₀ L : ℝ) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ x, (0 < |x - x₀| ∧ |x - x₀| < δ) → |f x - L| < ε
end Burden

open Topology Filter

def RTendsto (f : ℝ → ℝ) (x₀ L : ℝ) : Prop := Filter.Tendsto f (𝓝[≠] x₀) (𝓝 L)

theorem RTendsto_iff_BurdenTendsto (f : ℝ → ℝ) (x₀ L : ℝ) :
    Burden.Tendsto f x₀ L ↔ RTendsto f x₀ L := by
  apply Iff.intro
  · unfold RTendsto
    unfold Tendsto
    intro h
    unfold Burden.Tendsto at h
    simp [sub_ne_zero] at h

    -- Unpack the filter definition of tendsto --
    apply Filter.le_def.mpr
    simp
    unfold Set.preimage
    intro cn cnh

    -- Use the definition of neighborhood in the metric space of reals --
    apply Metric.mem_nhds_iff.mp at cnh
    apply Metric.mem_nhdsWithin_iff.mpr
    simp only [Metric.ball, Real.dist_eq] at *
    rcases cnh with ⟨ε₂, ε₂pos, hε₂⟩

    -- Clean up set member expressions in the goal and hypothesis --
    change (∃ δ > 0, ∀ x, x∈ ({y | |y - x₀| < δ}  ∩ {x₀}ᶜ ) -> f x ∈ cn)
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    have hε₂' : ∀ y , |y - L| < ε₂ → y ∈ cn :=
      Set.mem_setOf_eq.mpr hε₂

    -- Invoke the epsilon-delta definition --
    have k := h ε₂ ε₂pos
    rcases k with ⟨δ, δpos, hδ⟩
    use δ
    constructor
    exact δpos

    -- Finish the proof --
    intro x hx
    rcases hx with ⟨hx₁, hx₂⟩

    exact hε₂' (f x) (hδ x hx₂ hx₁)

  ------------ Work the other way ----------
  . unfold RTendsto
    unfold Tendsto
    intro h
    unfold Burden.Tendsto
    simp [sub_ne_zero]

    -- Unpack the filter definition --
    apply Filter.le_def.mp at h
    simp at h
    unfold Set.preimage at h

    -- Use the definition of neighborhood in the metric space of reals --
    simp only [Metric.mem_nhdsWithin_iff,Metric.mem_nhds_iff] at h
    simp only [Metric.ball, Real.dist_eq] at h

    -- Introduce our objective epsilon --
    intro ε₂ εpos

    -- Choose a ball around L as our chosen neighborhood --
    have cnh := h {y | |y - L| < ε₂}
    have : (∃ ε > 0, {y | |y - L| < ε} ⊆ {y | |y - L| < ε₂}) := by
      use ε₂
    have cnh' := cnh this
    rcases cnh' with ⟨δ, δpos, hδ⟩
    use δ
    constructor
    exact δpos

    -- Finish the proof --

    intro x hx h3
    simp [Set.subset_def] at hδ
    exact hδ x h3 hx
