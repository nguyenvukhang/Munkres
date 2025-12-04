import Munkres.Defs
import Munkres.Mathlib.Prelude

open Set Filter Topology TopologicalSpace

variable {x : ℕ → ℝ}

private def IsPeak (x : ℕ → ℝ) (n : ℕ) := ∀ m ≥ n, x m ≤ x n

private noncomputable def ζ {x : ℕ → ℝ} {N : ℕ}
  (h : ∀ n ≥ N, ¬IsPeak x n) : ℕ → ℕ
  | 0 => N
  | n + 1 => by
    let m := N + (ζ h n + 1)
    specialize h m (Nat.le_add_right N (ζ h n + 1))
    rw [IsPeak] at h
    push_neg at h
    exact h.choose

noncomputable example {x : ℕ → ℝ} : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (x ∘ φ)
  := by
  let P := { n | IsPeak x n }
  if hPf : P.Finite then
    let P' := hPf.toFinset
    have : ∃ N, ∀ n ∈ P, n < N := by
      if hP₀ : P'.Nonempty then
        use P'.max' hP₀ + 1
        intro n hn
        rw [<-hPf.mem_toFinset] at hn
        rw [Order.lt_add_one_iff]
        exact P'.le_max' n hn
      else
      have hP₀ : P = ∅ := by
        have : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP₀
        exact Finite.toFinset_eq_empty.mp this
      use 0
      intro n hn
      rw [hP₀] at hn
      exact False.elim hn
    obtain ⟨N, hN⟩ := this
    have hδ : ∀ n ≥ N, ¬IsPeak x n := by
      intro n hn
      by_contra! h
      exact hn.not_gt (hN n h)

    let φ (n : ℕ) : ℕ := ζ hδ n

    refine ⟨φ, ?_, ?_⟩
    · refine strictMono_nat_of_lt_succ ?_
      intro n
      let m := N + (ζ hδ n + 1)
      have h := hδ m (Nat.le_add_right N (ζ hδ n + 1))
      rw [IsPeak] at h
      push_neg at h
      have : m ≤ φ (n + 1) := h.choose_spec.1
      refine this.trans_lt' ?_
      exact (Nat.le_add_left (φ n + 1) N).trans le_rfl
    · refine monotone_nat_of_le_succ ?_
      intro n
      let m := N + (ζ hδ n + 1)
      have h := hδ m (Nat.le_add_right N (ζ hδ n + 1))
      rw [IsPeak] at h
      push_neg at h
      have : x m < x (φ (n + 1)) := h.choose_spec.2
      refine this.le.trans' ?_
      sorry

    -- let ψ : ℕ ↪o ℕ := {
    --   toFun := φ
    --   inj' := sorry
    --   map_rel_iff' {m n} := by
    --     rw [Function.Embedding.coeFn_mk]
    --     constructor
    --     · intro h
    --       sorry
    --     · sorry
    -- }

  else
  sorry
