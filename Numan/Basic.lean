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


-- We will be able to reduce the equivalence of the two continuity definitions
-- (which differ only because of the inclusion of the limit point in the
-- neighborhood filter) to this:

theorem punctured_ok_if_continuous: ∀ f: ℝ -> ℝ,
    map f (𝓝[≠] x₀) ≤ 𝓝 (f x₀) ↔ map f (𝓝 x₀) ≤ 𝓝 (f x₀) := by
  intro f
  apply Iff.intro
  . intro h
    apply Filter.le_def.mpr
    apply Filter.le_def.mp at h
    simp at *
    unfold Set.preimage
    unfold Set.preimage at h
    intro cn cnh
    have := h cn cnh


theorem RContinuousAt_iff_BurdenContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) :
    Burden.ContinuousAt f x₀ ↔ RContinuousAt f x₀ := by
  unfold RContinuousAt
  unfold Burden.ContinuousAt
  unfold ContinuousAt
  simp [RTendsto_iff_BurdenTendsto]
  unfold RTendsto
  unfold Tendsto
  exact punctured_ok_if_continuous f
