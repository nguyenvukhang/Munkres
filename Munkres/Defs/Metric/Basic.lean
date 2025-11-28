import Mathlib.Topology.MetricSpace.Bounded -- for `Metric.diam`
import Mathlib.Topology.UniformSpace.Cauchy -- for `TotallyBounded`
import Mathlib.Topology.Metrizable.Basic -- for `Metrizable`

import Munkres.Defs.Basic

namespace Munkres

open Topology Filter NNReal

universe u

variable {α : Type u} [MetricSpace α] {X : Set α}

protected theorem Metric.isComplete_iff
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

protected theorem Metric.CompleteSpace_iff
  : CompleteSpace α ↔ ∀ (f : ℕ → α), CauchySeq f → ∃ x, Tendsto f atTop (𝓝 x)
  := by --
  rw [completeSpace_iff_isComplete_univ, Metric.isComplete_iff]
  simp only [Metric.cauchySeq_iff', tendsto_subtype_rng]
  simp only [Subtype.exists, Set.mem_univ, exists_const]
  let φ := Equiv.Set.univ α
  -- exact ⟨fun h f ↦ h (φ.symm ∘ f), fun h f' ↦ h (φ ∘ f')⟩
  exact ⟨(· <| φ.symm ∘ ·), (· <| φ ∘ ·)⟩ -- ∎

-- Equivalence for the idea of total boundedness.
example : TotallyBounded X ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ X ⊆ ⋃ y ∈ t, Metric.ball y ε
  := by --
  exact Metric.totallyBounded_iff -- ∎

section LebesgueNumber

universe v
variable {ι : Sort v} {c : ι → Set α} {δ : ℝ≥0}
  {U : Set (Set α)} {ho : ∀ i, IsOpen (c i)} {hc : Set.univ ⊆ ⋃ i, c i}

/-- Tells us if `δ` is a lebesgue number of the open cover `c`. -/
class LebesgueNumber (δ : ℝ≥0) (ho : ∀ i, IsOpen (c i)) (hc : Set.univ ⊆ ⋃ i, c i) : Prop where
  ne_zero : δ ≠ 0
  out : ∀ s : Set α, EMetric.diam s < δ → ∃ i, s ⊆ c i

lemma LebesgueNumber.pos (h : LebesgueNumber δ ho hc) : δ > 0 := pos_of_ne_zero h.ne_zero

protected theorem LebesgueNumber.iff : LebesgueNumber δ ho hc
  ↔ δ ≠ 0 ∧ ∀ s : Set α, EMetric.diam s < δ → ∃ i, s ⊆ c i
  := by --
  constructor
  · intro h
    exact ⟨h.ne_zero, h.out⟩
  · intro ⟨ne_zero, out⟩
    exact {ne_zero, out} -- ∎

-- For more info in Mathlib, look for `lebesgue_number_lemma_of_emetric`.

end LebesgueNumber

end Munkres
