import Munkres.Subtype.Induced

import Munkres.Defs.Subtype

open Set

namespace Munkres

universe u

variable {α : Type u}

section SimpleCases
variable {X A : Set α} [TopologicalSpace X]

-- Empty and univ lemmas.

lemma isOpenIn_empty : IsOpenIn ∅ X
  := by --
  exact { isOpen' := isOpen_const, subset' := empty_subset X } -- ∎
lemma isOpenIn_univ : IsOpenIn X X
  := by --
  refine { isOpen' := ?_, subset' := le_rfl }
  rw [Subtype.coe_preimage_self]
  exact isOpen_univ -- ∎

lemma isClosedIn_empty : IsClosedIn ∅ X
  := by --
  exact { isClosed' := isClosed_const, subset' := empty_subset X } -- ∎
lemma isClosedIn_univ : IsClosedIn X X
  := by --
  refine { isClosed' := ?_, subset' := le_rfl }
  rw [Subtype.coe_preimage_self]
  exact isClosed_univ -- ∎

lemma isCompactIn_empty : IsCompactIn ∅ X
  := by --
  refine { isCompact' := ?_, subset' := empty_subset X }
  rw [preimage_empty]
  exact isCompact_empty -- ∎

-- Complement lemmas.

lemma IsClosedIn.isOpen_compl (h : IsClosedIn A X) : IsOpenIn (X \ A) X
  := by --
  refine { isOpen' := ?_, subset' := diff_subset }
  rw [<-Subtype.compl]
  exact h.isClosed'.isOpen_compl -- ∎
lemma IsOpenIn.isClosed_compl (h : IsOpenIn A X) : IsClosedIn (X \ A) X
  := by --
  refine { isClosed' := ?_, subset' := diff_subset }
  rw [<-Subtype.compl]
  exact h.isOpen'.isClosed_compl -- ∎

lemma IsClosedIn.iff_compl : IsClosedIn A X ↔ IsOpenIn (X \ A) X ∧ A ⊆ X
  := by --
  refine ⟨fun h ↦ ⟨h.isOpen_compl, h.subset'⟩, ?_⟩
  intro ⟨h, subset'⟩
  rw [<-Set.diff_diff_cancel_left subset']
  exact h.isClosed_compl -- ∎
lemma IsOpenIn.iff_compl : IsOpenIn A X ↔ IsClosedIn (X \ A) X ∧ A ⊆ X
  := by --
  refine ⟨fun h ↦ ⟨h.isClosed_compl, h.subset'⟩, ?_⟩
  intro ⟨h, subset'⟩
  rw [<-Set.diff_diff_cancel_left subset']
  exact h.isOpen_compl -- ∎

end SimpleCases

example [TopologicalSpace α] {A X : Set α}
  : IsOpenIn A X → IsOpen X → IsOpen A
  := by
  intro hAX hX
  have hA := hAX.isOpen'
  rw [isOpen_induced_iff₂] at hA
  obtain ⟨U, hU, hA⟩ := hA
  rw [Subtype.image_preimage_val] at hA
  -- have : X ∩ A = A := inter_eq_self_of_subset_right hAX.subset'
  rw [inter_eq_self_of_subset_right hAX.subset'] at hA
  subst hA
  refine hX.inter hU

section IsOpenIn
variable {X Y A : Set α}

theorem IsOpenIn.lift [TopologicalSpace α]
  : IsOpenIn A X → IsOpen X → IsOpen A
  := by --
  intro hAX hX
  have hA := hAX.isOpen'
  rw [isOpen_induced_iff₂] at hA
  obtain ⟨U, hU, hA⟩ := hA
  rw [Subtype.image_preimage_val] at hA
  rw [inter_eq_self_of_subset_right hAX.subset'] at hA
  subst hA
  exact hX.inter hU -- ∎

end IsOpenIn
section IsClosedIn
variable {X Y A : Set α}

theorem IsClosedIn.lift [TopologicalSpace α]
  : IsClosedIn A X → IsClosed X → IsClosed A
  := by --
  intro hAX hX
  have hA := hAX.isClosed'
  rw [isClosed_induced_iff₂] at hA
  obtain ⟨U, hU, hA⟩ := hA
  rw [Subtype.image_preimage_val] at hA
  rw [inter_eq_self_of_subset_right hAX.subset'] at hA
  subst hA
  exact hX.inter hU -- ∎

end IsClosedIn
end Munkres
