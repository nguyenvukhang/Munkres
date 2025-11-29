/-
This file seeks to reconcile the definition of `first countability` between
Mathlib and Munkres.
-/
import Mathlib.Topology.Bases

import Munkres.Defs.IsBasisAt

open Filter Topology TopologicalSpace Munkres

universe u

variable {α : Type u} [TopologicalSpace α]

example {s : Set α} (hs : s.Countable) (hs₀ : s.Nonempty)
  : ∃ (f : ℕ → α), s = Set.range f := hs.exists_eq_range hs₀
example {x : α} : ∀ u ∈ 𝓝 x, x ∈ u := fun _ ↦ mem_of_mem_nhds

theorem IsCountablyGenerated.iff {x : α} :
  (𝓝 x).IsCountablyGenerated ↔ ∃ B, B.Countable ∧ IsBasisAt B x
  := by --
  constructor
  · intro h
    obtain ⟨g, hg, heq⟩ := h.out

    let F := {s | s.Finite ∧ s ⊆ g}
    have hF : F.Countable := Set.countable_setOf_finite_subset hg
    let B := {interior (⋂₀ s) | s ∈ F}
    have hB_countable : B.Countable := hF.image (interior <| ⋂₀ ·)

    refine ⟨B, hB_countable, ?_⟩
    exact {
      isOpen' := by
        intro b ⟨s, _, heq⟩
        subst heq
        exact isOpen_interior
      mem' := by
        intro b ⟨s, ⟨hsf, hsg⟩, heq⟩
        subst heq
        rw [hsf.interior_sInter, Set.mem_iInter₂]
        intro u hu
        replace hsg : u ∈ generate g := mem_generate_of_mem (hsg hu)
        rw [<-heq, mem_nhds_iff] at hsg
        obtain ⟨t, htu, ht, hxt⟩ := hsg
        rw [<-ht.subset_interior_iff] at htu
        exact htu hxt
      exists_mem_subset' := by
        intro u hu hxu
        replace hu : u ∈ 𝓝 x := hu.mem_nhds hxu
        rw [heq, mem_generate_iff] at hu
        obtain ⟨s, hsg, hsf, hsu⟩ := hu
        replace hsf : s ∈ F := Set.mem_sep hsf hsg
        have : interior (⋂₀ s) ∈ B := ⟨s, hsf, rfl⟩
        exact ⟨interior (⋂₀ s), this, interior_subset.trans hsu⟩
    }
  · intro ⟨B, hB_countable, hB⟩
    refine ⟨B, hB_countable, ?_⟩
    refine le_antisymm ?_ ?_
    · intro u hu
      rw [mem_generate_iff] at hu
      rw [mem_nhds_iff]
      obtain ⟨t, htB, htf, htu⟩ := hu
      refine ⟨⋂₀ t, htu, ?_, ?_⟩
      · refine Set.Finite.isOpen_sInter htf ?_
        intro u hu
        exact hB.isOpen' (htB hu)
      · rw [Set.mem_sInter]
        intro u hu
        exact hB.mem' (htB hu)
    · intro u hu
      rw [mem_generate_iff]
      rw [mem_nhds_iff] at hu
      obtain ⟨t, htu, ht, hxt⟩ := hu
      obtain ⟨b, hbB, hbt⟩ := hB.exists_mem_subset' ht hxt
      rw [<-Set.singleton_subset_iff] at hbB
      refine ⟨{b}, hbB, Set.finite_singleton b, ?_⟩
      rw [Set.sInter_singleton]
      exact hbt.trans htu -- ∎

protected theorem FirstCountableTopology.iff
  : FirstCountableTopology α ↔ ∀ x : α, ∃ B, B.Countable ∧ IsBasisAt B x
  := by --
  refine ⟨(IsCountablyGenerated.iff.mp <| ·.nhds_generated_countable ·), ?_⟩
  intro h
  exact ⟨(IsCountablyGenerated.iff.mpr <| h ·)⟩ -- ∎

protected theorem SecondCountableTopology.iff
  : SecondCountableTopology α ↔ ∃ B : Set (Set α), B.Countable ∧ IsTopologicalBasis B
  := by --
  constructor
  · intro h
    -- hard carry:
    --   * isTopologicalBasis_of_subbasis
    --   * exists_countable_basis
    obtain ⟨B, hB_countable, _, hB⟩ := exists_countable_basis α
    exact ⟨B, hB_countable, hB⟩
  · intro ⟨B, hB_countable, hB_basis⟩
    exact { is_open_generated_countable := ⟨B, hB_countable, hB_basis.eq_generateFrom⟩ } -- ∎
