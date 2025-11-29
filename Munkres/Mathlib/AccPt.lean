import Munkres.Defs.Countable

open Filter Set Munkres
open scoped Topology

universe u v

variable {α : Type u} [TopologicalSpace α]
  {β : Type v}
  {A : Set α} {x : α}

/-- Munkres defines that x is a limit point of A if every open U ⊆ X containing
x intersects with A \ {x}. This is equivalent to Mathlib's `AccPt x (𝓟 A)`. -/
protected theorem AccPt.iff {x : α} : AccPt x (𝓟 A) ↔ ∀ U ∈ nhds' x, (U ∩ (A \ {x})).Nonempty
  := by --
  rw [accPt_principal_iff_clusterPt, clusterPt_principal_iff]
  simp only [mem_nhds_iff]
  refine ⟨fun h U ⟨hU, hxU⟩ ↦ (h U ⟨U, le_refl _, hU, hxU⟩), ?_⟩
  intro h S ⟨U, hUS, hU, hxU⟩
  let ⟨t, htU, htA, hne⟩ := h U ⟨hU, hxU⟩
  exact ⟨t, hUS htU, htA, hne⟩ -- ∎

--* closure A = A ∪ A'
theorem AccPt.union_eq_closure : A ∪ { x | AccPt x (𝓟 A)} = closure A
  := by --
  refine le_antisymm ?_ ?_
  · intro x hx
    rcases hx with h | (h : AccPt x (𝓟 A))
    · exact subset_closure h
    · rw [AccPt.iff] at h
      rw [mem_closure_iff]
      intro U hU hxU
      obtain ⟨t, htU, htA, htx⟩ := h U ⟨hU, hxU⟩
      exact ⟨t, htU, htA⟩
  · intro x hx
    refine or_iff_not_imp_left.mpr fun h ↦ ?_
    simp
    refine AccPt.iff.mpr ?_
    intro U ⟨hU, hxU⟩
    rw [mem_closure_iff] at hx
    obtain ⟨y, hyU, hyA⟩ := hx U hU hxU
    have : y ≠ x := ne_of_mem_of_not_mem hyA h
    refine ⟨y, hyU, hyA, this⟩ -- ∎

theorem AccPt.mem_closure (h : AccPt x (𝓟 A)) : x ∈ closure A
  := by --
  exact mem_closure_iff_clusterPt.mpr h.clusterPt -- ∎

-- Alternative proof.
example (h : AccPt x (𝓟 A)) : x ∈ closure A
  := by --
  have : x ∈ A ∪ { x | AccPt x (𝓟 A) } := Set.mem_union_right A h
  rw [AccPt.union_eq_closure] at this
  exact this -- ∎

theorem AccPt.of_tendsto [Nonempty β] [SemilatticeSup β] {f : β → α}
  (hA : ∀ᶠ n in atTop, f n ∈ A) (htt : Tendsto f atTop (𝓝[≠] x))
  : AccPt x (𝓟 A)
  := by --
  rw [AccPt.iff]
  intro U ⟨hU, hxU⟩
  rw [tendsto_nhdsWithin_iff] at htt
  obtain ⟨htt, hne⟩ := htt
  rw [tendsto_atTop_nhds] at htt
  rw [eventually_atTop] at hne hA
  specialize htt U hxU hU
  obtain ⟨N₁, htt⟩ := htt
  obtain ⟨N₂, hne⟩ := hne
  obtain ⟨N₃, hA⟩ := hA
  let N := (N₁ ⊔ N₂) ⊔ N₃
  have hN₁ : N₁ ≤ N := le_sup_left.trans le_sup_left
  have hN₂ : N₂ ≤ N := le_sup_right.trans le_sup_left
  have hN₃ : N₃ ≤ N := le_sup_right
  specialize htt N hN₁
  specialize hne N hN₂
  specialize hA N hN₃
  exact ⟨f N, htt, hA, hne⟩ -- ∎

theorem AccPt.of_tendsto_nat {f : ℕ → α} (hA : ∀ᶠ n in atTop, f n ∈ A)
  (htt : Tendsto f atTop (𝓝[≠] x)) : AccPt x (𝓟 A)
  := by --
  exact AccPt.of_tendsto hA htt -- ∎

-- And this is the reason why we need (𝓝[≠] x) above, and not just (𝓝 x).
example [h₀ : Nonempty α] : ∃ (A : Set α) (x : α) (f : ℕ → α),
  (∀ᶠ n in atTop, f n ∈ A) ∧ Tendsto f atTop (𝓝 x) ∧ ¬AccPt x (𝓟 A)
  := by --
  let x := h₀.some
  refine ⟨{x}, x, fun _ ↦ x, ?_, ?_, ?_⟩
  · exact eventually_const.mpr rfl
  · exact tendsto_const_nhds
  · by_contra! h
    rw [AccPt.iff] at h
    specialize h univ ⟨isOpen_univ, trivial⟩
    rw [sdiff_self, bot_eq_empty, inter_empty] at h
    exact Set.not_nonempty_empty h -- ∎

theorem AccPt.exists_tendsto [h₁ : FirstCountableTopology α]
  : AccPt x (𝓟 A) → ∃ (f : ℕ → α), (∀ n, f n ∈ A) ∧ Tendsto f atTop (𝓝 x)
  := by --
  intro hx
  rw [AccPt.iff] at hx
  rw [FirstCountableTopology.iff] at h₁
  specialize h₁ x
  obtain ⟨β, hβ_countable, hβx⟩ := h₁
  haveI : Countable β := hβ_countable
  obtain ⟨B, hB_anti, hB⟩ := hβx.exists_antitone_eq_range
  let hδ (n : ℕ) := hx (B n) (hB.nhds' ⟨n, rfl⟩)
  let f (n : ℕ) : α := (hδ n).some
  use f
  refine ⟨?_, ?_⟩
  · intro n
    obtain ⟨hfB : f n ∈ B n, hfA : f n ∈ A \ {x}⟩ := (hδ n).some_mem
    exact hfA.1
  · rw [tendsto_atTop_nhds]
    intro U hxU hU
    obtain ⟨b, ⟨N, heq⟩, hbU⟩ := hB.exists_mem_subset' hU hxU
    subst heq
    use N
    intro n hn
    obtain ⟨hfB : f n ∈ B n, hfA : f n ∈ A \ {x}⟩ := (hδ n).some_mem
    exact hbU <| hB_anti hn hfB -- ∎
