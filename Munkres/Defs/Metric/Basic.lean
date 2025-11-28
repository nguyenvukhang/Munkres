import Mathlib.Topology.MetricSpace.Bounded -- for `Metric.diam`
import Mathlib.Topology.UniformSpace.Cauchy -- for `TotallyBounded`
import Mathlib.Topology.Metrizable.Basic -- for `Metrizable`

import Munkres.Defs.Basic

namespace Munkres

-- import Dino.Core.Topology.IsCountableBasisAt
-- import Dino.Core.Set.Subcollection

open Topology Filter ENNReal NNReal TopologicalSpace

universe u

variable {α : Type u}

-- Equivalence of the idea of convergence. WOH.
example [TopologicalSpace α] (f : ℕ → α) (x : α)
  : Tendsto f atTop (𝓝 x) ↔ ∀ U, x ∈ U → IsOpen U → ∃ N, ∀ k ≥ N, f k ∈ U
  := by --
  rw [tendsto_atTop_nhds] -- ∎

theorem Metric.isComplete_iff [MetricSpace α] {X : Set α}
  : IsComplete X ↔ ∀ (f : ℕ → X), CauchySeq f → ∃ x, Tendsto f atTop (𝓝 x)
  := by --
  constructor
  · intro h f hf
    have : CompleteSpace X := IsComplete.completeSpace_coe h
    rw [<-cauchy_map_iff_exists_tendsto]
    exact hf
  · intro h
    rw [<-completeSpace_coe_iff_isComplete]
    exact UniformSpace.complete_of_cauchySeq_tendsto h -- ∎

-- theorem Metric.isCompleteSpace_iff [MetricSpace α]
--   : CompleteSpace α ↔ ∀ (f : ℕ → α), CauchySeq f → ∃ x, Tendsto f atTop (𝓝 x)
--   := by --
--   rw [completeSpace_iff_isComplete_univ, Metric.isComplete_iff]
--   constructor
--   · intro h f hf
--     let X : Set α := Set.univ; let φ : X ≃ α := Equiv.Set.univ α
--     let f' : ℕ → X := (φ.invFun <| f ·)
--     have hf' : CauchySeq f' := by
--       rw [cauchySeq_iff'] at hf ⊢
--       exact hf
--     obtain ⟨x, hx⟩ := h f' hf'
--     use x
--     rw [tendsto_atTop] at hx ⊢
--     exact hx
--   · intro h f' hf'
--     let X : Set α := Set.univ; let φ : X ≃ α := Equiv.Set.univ α
--     let f : ℕ → α := φ ∘ f'
--     have hf : CauchySeq f := by rw [cauchySeq_iff'] at hf' ⊢; exact hf'
--     obtain ⟨x, hx⟩ := h f hf
--     use ⟨x, trivial⟩
--     exact tendsto_subtype_rng.mpr hx -- ∎

section LebesgueNumber

universe v
variable [MetricSpace α] {ι : Sort v} {c : ι → Set α} {U : Set (Set α)}

/-- Tells us if `δ` is a lebesgue number of the open cover `c`. -/
class LebesgueNumber (δ : ℝ≥0) (ho : ∀ i, IsOpen (c i)) (hc : Set.univ ⊆ ⋃ i, c i) : Prop where
  ne_zero : δ ≠ 0
  out : ∀ s : Set α, EMetric.diam s < δ → ∃ i, s ⊆ c i

lemma LebesgueNumber.pos {δ : ℝ≥0} {ho : ∀ i, IsOpen (c i)} {hc : Set.univ ⊆ ⋃ i, c i}
  (h : LebesgueNumber δ ho hc) : δ > 0 := pos_of_ne_zero h.ne_zero

protected theorem LebesgueNumber.iff {δ : ℝ≥0} {ho : ∀ i, IsOpen (c i)} {hc : Set.univ ⊆ ⋃ i, c i}
  : LebesgueNumber δ ho hc ↔ δ > 0 ∧ ∀ s : Set α, EMetric.diam s < δ → ∃ i, s ⊆ c i
  := by --
  constructor
  · intro h
    exact ⟨h.pos, h.out⟩
  · intro ⟨pos, out⟩
    exact {ne_zero := pos.ne', out} -- ∎

-- For more info in Mathlib, look for `lebesgue_number_lemma_of_emetric`.

end LebesgueNumber

-- Equivalence for the idea of total boundedness.
example [MetricSpace α] {X : Set α} :
  TotallyBounded X ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ X ⊆ ⋃ y ∈ t, Metric.ball y ε
  := by --
  exact Metric.totallyBounded_iff -- ∎

end Munkres
