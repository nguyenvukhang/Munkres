import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Cauchy

import Munkres.Defs

open Set Filter Topology

universe u v

variable {α : Type u} {β : Type v} [M : MetricSpace α] {x y z : α}

private def B (M : MetricSpace α) := @Metric.ball α M.toPseudoMetricSpace

private def d (x y : α) := M.dist x y
private noncomputable def f (t : ℝ) : ℝ := t / (1 + t)
private noncomputable def ρ (x y : α) : ℝ := f (d x y)

private lemma hd₁ {x y : α} : 0 < 1 + dist x y := add_pos_of_pos_of_nonneg zero_lt_one dist_nonneg

private lemma hf : MonotoneOn f (Ici 0)
  := by --
  intro a (ha : 0 ≤ a) b (hb : 0 ≤ b) hab
  refine (div_le_div_iff₀ ?_ ?_).mpr ?_
  · exact add_pos_of_pos_of_nonneg zero_lt_one ha
  · exact add_pos_of_pos_of_nonneg zero_lt_one hb
  · simp only [left_distrib, mul_one]
    refine add_le_add hab ?_
    rw [mul_comm] -- ∎

-- ρ = d / (1 + d) is a metric.
private noncomputable def M' (α : Type u) [MetricSpace α] : MetricSpace α
  := by --
  -- have hd₁ (x y : α) : 0 < 1 + d x y := by
  --   refine zero_lt_one.trans_le ?_
  --   exact (le_add_iff_nonneg_right 1).mpr dist_nonneg
  exact {
    dist := ρ
    dist_comm x y := by dsimp only [ρ, d]; rw [dist_comm]
    dist_self x := by dsimp only [ρ, d, f]; rw [dist_self, zero_div]
    eq_of_dist_eq_zero {x y} h₀ := by
      dsimp only [ρ, f] at h₀
      rw [div_eq_zero_iff] at h₀
      rcases h₀ with h₀ | h₀
      · exact eq_of_dist_eq_zero h₀
      · exact False.elim (hd₁.ne' h₀)
    dist_triangle x y z := by
      have : f (d x z) ≤ f (d x y + d y z) := by
        refine hf dist_nonneg ?_ ?_
        · exact add_nonneg dist_nonneg dist_nonneg
        · exact dist_triangle _ _ _
      refine this.trans ?_
      dsimp only [f]
      rw [add_div] -- the crux
      refine add_le_add ?_ ?_
      · refine div_le_div_of_nonneg_left ?_ hd₁ ?_
        · exact dist_nonneg
        · refine add_le_add_left ?_ 1
          exact (le_add_iff_nonneg_right _).mpr dist_nonneg
      · refine div_le_div_of_nonneg_left ?_ hd₁ ?_
        · exact dist_nonneg
        · refine add_le_add_left ?_ 1
          exact (le_add_iff_nonneg_left _).mpr dist_nonneg
  } -- ∎
private noncomputable def P := M.toPseudoMetricSpace
private noncomputable def P' := (M' α).toPseudoMetricSpace
private noncomputable def U := M.toPseudoMetricSpace.toUniformSpace
private noncomputable def U' := (M' α).toPseudoMetricSpace.toUniformSpace
private noncomputable def T := M.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
private noncomputable def T' := (M' α).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

private lemma ρ_le_d : ρ x y ≤ d x y
  := by --
  dsimp only [ρ, f]
  refine div_le_self dist_nonneg ?_
  exact (le_add_iff_nonneg_right 1).mpr dist_nonneg -- ∎

private lemma d_le_ρ (hle : d x y ≤ 1) : d x y ≤ 2 * ρ x y
  := by --
  have : d x y / (1 + 1) ≤ d x y / (1 + d x y) := by
    refine div_le_div_of_nonneg_left dist_nonneg ?_ ?_
    · exact add_pos_of_pos_of_nonneg zero_lt_one dist_nonneg
    · exact add_le_add_left hle 1
  refine (mul_le_mul_of_nonneg_left this zero_le_two).trans' ?_
  rw [one_add_one_eq_two, mul_div_cancel₀ _ two_ne_zero] -- ∎

private lemma d_le_ρ' (hle : ρ x y ≤ 1 / 2) : d x y ≤ 2 * ρ x y
  := by --
  have h : 2 * ρ x y ≤ 1 := by
    rw [<-mul_div_cancel₀ (1 : ℝ) two_ne_zero]
    exact mul_le_mul_of_nonneg_left hle zero_le_two
  dsimp only [ρ, f] at h
  rw [mul_div] at h
  have h : 2 * d x y ≤ 1 * (1 + d x y) := (div_le_iff₀ hd₁).mp h
  rw [one_mul, two_mul] at h
  rw [add_le_add_iff_right (d x y)] at h
  exact d_le_ρ h -- ∎

private theorem t₁ {ε : ℝ} (hε : ε ≤ 1) : B (M' α) x (ε / 2) ⊆ B M x ε
  := by --
  intro y (hy : ρ y x < ε / 2)
  -- change d y x < ε
  have hy' : 2 * ρ y x < ε := by
    rw [<-mul_div_cancel₀ ε two_ne_zero]
    exact mul_lt_mul_of_pos_left hy zero_lt_two
  refine (d_le_ρ' ?_).trans_lt hy'
  refine hy.le.trans ?_
  exact div_le_div_of_nonneg_right hε zero_le_two -- ∎

private theorem t₂ {ε : ℝ} : B M x ε ⊆ B (M' α) x ε
  := by --
  intro y (hy : d y x < ε)
  -- change ρ y x < ε
  exact ρ_le_d.trans_lt hy -- ∎

private def MetricSpace.CauchySeq (M : MetricSpace β) (f : ℕ → β) := _root_.CauchySeq f

private theorem cauchy_iff₀ (f : ℕ → α) : M.CauchySeq f ↔ (M' α).CauchySeq f
  := by --
  simp only [MetricSpace.CauchySeq]
  rw [Metric.cauchySeq_iff']
  rw [@Metric.cauchySeq_iff' α ℕ P']
  change (∀ ε > 0, ∃ N, ∀ n ≥ N, d (f n) (f N) < ε) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, ρ (f n) (f N) < ε
  constructor
  · intro h ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h n hn
    exact ρ_le_d.trans_lt h
  · intro h ε' hε'
    let ε := min (1 / 2) (ε' / 3)
    have hε : 0 < ε := lt_min one_half_pos (div_pos hε' zero_lt_three)
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h n hn
    have hρ₁ : ρ (f n) (f N) ≤ 1 / 2 := h.le.trans (min_le_left _ _)
    refine (d_le_ρ' hρ₁).trans_lt ?_
    have : 2 * ρ (f n) (f N) < 2 * ε := mul_lt_mul_of_pos_left h zero_lt_two
    refine this.trans ?_
    refine (lt_div_iff₀' zero_lt_two).mp ?_
    dsimp only [ε]
    refine (min_le_right _ _).trans_lt ?_
    refine div_lt_div_of_pos_left hε' zero_lt_two ?_
    norm_num -- ∎

private theorem t_eq : T (α := α) = T'
  := by --
  refine TopologicalSpace.ext ?_
  ext U : 2
  rw [@Metric.isOpen_iff α P, @Metric.isOpen_iff α P']
  constructor
  · intro h x hxU
    specialize h x hxU
    obtain ⟨ε', hε', h⟩ := h
    let ε := min (1 / 2) (ε' / 3)
    have hε : 0 < ε := lt_min one_half_pos (div_pos hε' zero_lt_three)
    refine ⟨ε, hε, ?_⟩
    refine h.trans' ?_
    rintro y (hy : ρ y x < ε)
    change d y x < ε'
    have : ρ y x ≤ 1 / 2 := hy.le.trans (min_le_left _ _)
    refine (d_le_ρ' this).trans_lt ?_
    have := mul_lt_mul_of_pos_left hy zero_lt_two
    refine this.trans ?_
    refine (lt_div_iff₀' zero_lt_two).mp ?_
    dsimp only [ε]
    refine (min_le_right _ _).trans_lt ?_
    refine div_lt_div_of_pos_left hε' zero_lt_two ?_
    norm_num
  · intro h x hxU
    specialize h x hxU
    obtain ⟨ε, hε, h⟩ := h
    refine ⟨ε, hε, ?_⟩
    refine h.trans' ?_
    intro y hy
    exact ρ_le_d.trans_lt hy -- ∎

private lemma c₁ : @CompleteSpace α U → @CompleteSpace α U'
  := by --
  intro h
  rw [@Munkres.Metric.CompleteSpace_iff α M] at h
  rw [@Munkres.Metric.CompleteSpace_iff α (M' α)]
  intro f (hf : (M' α).CauchySeq f)
  rw [<-cauchy_iff₀ f] at hf
  specialize h f hf
  obtain ⟨x, h⟩ := h
  refine ⟨x, ?_⟩
  rw [Metric.tendsto_atTop] at h
  rw [@Metric.tendsto_atTop α ℕ P']
  intro ε hε
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  use N
  intro n hn
  specialize h n hn
  change ρ (f n) x < ε
  refine ρ_le_d.trans_lt ?_
  exact h -- ∎

private lemma c₂ : @CompleteSpace α U' → @CompleteSpace α U
  := by --
  intro h
  rw [@Munkres.Metric.CompleteSpace_iff α (M' α)] at h
  rw [@Munkres.Metric.CompleteSpace_iff α M]
  intro f (hf : M.CauchySeq f)
  rw [cauchy_iff₀ f] at hf
  specialize h f hf
  obtain ⟨x, h⟩ := h
  refine ⟨x, ?_⟩
  rw [Metric.tendsto_atTop]
  rw [@Metric.tendsto_atTop α ℕ P'] at h
  change ∀ ε > 0, ∃ N, ∀ n ≥ N, ρ (f n) x < ε at h
  intro ε' hε'
  let ε := min (1 / 2) (ε' / 2)
  have hε : 0 < ε := lt_min one_half_pos (half_pos hε')
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  use N
  intro n hn
  specialize h n hn
  change d (f n) x < ε'
  have hdρ := d_le_ρ' <| h.le.trans (min_le_left _ _)
  refine hdρ.trans_lt ?_
  have : 2 * ρ (f n) x < 2 * ε := mul_lt_mul_of_pos_left h zero_lt_two
  refine this.trans_le ?_
  refine (le_mul_inv_iff₀' zero_lt_two).mp ?_
  exact min_le_right _ _ -- ∎

example : @CompleteSpace α U ↔ @CompleteSpace α U' := ⟨c₁, c₂⟩
