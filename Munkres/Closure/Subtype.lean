import Mathlib.Topology.Constructions
import Munkres.Mathlib.Set.As

universe u

variable {α : Type u} [TopologicalSpace α] {Y A : Set α}

example (A : Set Y) {x : Y} : x ∈ closure A ↔ ↑x ∈ closure (Subtype.val '' A) := closure_subtype

--* Theorem 17.4: the closure of A in Y equals (closure A) ∩ Y.
theorem closure_subtype₂ (A : Set Y) : closure A = closure (A : Set α) ∩ Y
  := by --
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subtype.coe_image] at hx
    obtain ⟨hxY, hx⟩ := hx
    exact ⟨closure_subtype.mp hx, hxY⟩
  · intro x ⟨hx, hxY⟩
    exact ⟨⟨x, hxY⟩, closure_subtype.mpr hx, rfl⟩ -- ∎

--* Theorem 17.4: If A ⊆ Y, the closure of A in Y equals (closure A) ∩ Y.
theorem closure_subtype₃ {hAY : A ⊆ Y} : closure (A.as Y) = closure A ∩ Y
  := by --
  rw [closure_subtype₂ (A.as Y)]
  refine congrArg (closure · ∩ Y) ?_
  exact Set.as_subtype_subset_eq hAY -- ∎
