import Munkres.Disjoint
import Munkres.Mathlib.AccPt.Basic
import Munkres.Separation.Basic

open Filter Topology

universe u

variable {α : Type u} [TopologicalSpace α] {Y : Set α} {A B : Set Y}

section NotMem
variable (h : IsSeparation A B)

include h in
theorem IsSeparation.accPt_notMem_right : ∀ x, AccPt x (𝓟 A) → x ∉ B
  := by --
  intro x hx
  let A' : Set α := A
  have hA : closure A = closure A' ∩ Y := closure_subtype₂ A
  rw [closure_eq_iff_isClosed.mpr h.isClosed_left] at hA
  have hAB₀ := (h.disjoint'.eq_closure_iff_disjoint h.isClosed_left).mp hA
  have : ↑x ∈ closure A' := closure_subtype.mp hx.mem_closure
  have hx : ↑x ∉ Subtype.val '' B := hAB₀.notMem_of_mem_left this
  contrapose! hx
  exact ⟨x, hx, rfl⟩ -- ∎

include h in
theorem IsSeparation.accPt_notMem_left : ∀ x, AccPt x (𝓟 B) → x ∉ A
  := by --
  exact h.symm.accPt_notMem_right -- ∎

end NotMem

theorem IsSeparation.iff₂ : IsSeparation A B ↔ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B
  ∧ A ∪ B = Y ∧ (∀ x, AccPt x (𝓟 A) → x ∉ B) ∧ (∀ x, AccPt x (𝓟 B) → x ∉ A)
  := by --
  constructor
  · intro h
    refine ⟨h.left'.2,
            h.right'.2,
            h.disjoint',
            by rw [h.union']; exact Subtype.coe_image_univ Y,
            h.accPt_notMem_right,
            h.accPt_notMem_left⟩
  · intro ⟨hA₀, hB₀, disjoint', union', hapA, hapB⟩
    let A' := closure (A : Set α)
    let B' := closure (B : Set α)

    have hdA'B : Disjoint A' B := by
      rw [<-Set.image_val_inter_self_right_eq_coe]
      rw [<-disjoint_assoc₂]
      rw [<-closure_subtype₂]
      rw [<-AccPt.union_eq_closure]
      rw [Set.disjoint_image_subtype_iff]
      refine Set.disjoint_union_left.mpr ⟨disjoint', ?_⟩
      exact Set.disjoint_left.mpr hapA

    have hdB'A : Disjoint B' A := by
      rw [<-Set.image_val_inter_self_right_eq_coe]
      rw [<-disjoint_assoc₂]
      rw [<-closure_subtype₂]
      rw [<-AccPt.union_eq_closure]
      rw [Set.disjoint_image_subtype_iff]
      refine Set.disjoint_union_left.mpr ⟨disjoint'.symm, ?_⟩
      exact Set.disjoint_left.mpr hapB

    have hA'eq : A' ∩ Y = A := by
      conv => lhs; rw [<-union']
      rw [Set.image_val_union]
      rw [Set.inter_union_distrib_left]
      rw [hdA'B.inter_eq]
      rw [Set.union_empty]
      exact Set.inter_eq_self_of_subset_right subset_closure

    have hB'eq : B' ∩ Y = B := by
      conv => lhs; rw [<-union']
      rw [Set.image_val_union]
      rw [Set.inter_union_distrib_left]
      rw [hdB'A.inter_eq]
      rw [Set.empty_union]
      exact Set.inter_eq_self_of_subset_right subset_closure

    have hA : IsClosed A := by
      rw [<-closure_eq_iff_isClosed, <-Set.image_val_inj, closure_subtype₂]
      exact hA'eq

    have hB : IsClosed B := by
      rw [<-closure_eq_iff_isClosed, <-Set.image_val_inj, closure_subtype₂]
      exact hB'eq

    have union' := Set.eq_univ_of_image_val_eq union'
    rw [<-disjoint'.union_eq_univ_left_compl union'] at hB
    rw [<-disjoint'.union_eq_univ_right_compl union'] at hA

    exact {
      left' := ⟨isClosed_compl_iff.mp hB, hA₀⟩
      right' := ⟨isClosed_compl_iff.mp hA, hB₀⟩
      disjoint',
      union',
    } -- ∎
