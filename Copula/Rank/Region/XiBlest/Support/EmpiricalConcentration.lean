import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def empiricalMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω)/(n : ℝ)

/-- A two-sided Hoeffding bound, with a deliberately nonoptimal constant,
for independent observations in the unit interval. -/
theorem empiricalMean_deviation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ)
    (hb : ∀ i ω, X i ω ∈ Icc (0 : ℝ) 1) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ)=p) (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0≤ε) :
    μ.real {ω | ε ≤ |empiricalMean X n ω-p|} ≤ 2*Real.exp (-(n : ℝ)*ε^2/2) := by
  let Y : ℕ → Ω → ℝ := fun i ω => X i ω-p
  have hY : iIndepFun Y μ := hI.comp (fun _ x => x-p) (fun _ => measurable_id.sub_const p)
  have hYsub (i : ℕ) : HasSubgaussianMGF (Y i) 1 μ := by
    have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      ((hX i).sub_const p).aemeasurable
      (Filter.Eventually.of_forall fun ω => (show Y i ω ∈ Icc (-1 : ℝ) 1 by
        have h := hb i ω
        dsimp [Y]
        constructor <;> linarith [h.1,h.2,hp.1,hp.2])) (by
        change (∫ ω, X i ω-p ∂μ)=0
        rw [integral_sub (Integrable.of_mem_Icc 0 1 (hX i).aemeasurable (Filter.Eventually.of_forall (hb i)))
          (integrable_const p),hmean]
        simp)
    norm_num at hh
    exact hh
  have hneg : iIndepFun (fun i ω => -(Y i ω)) μ :=
    hY.comp (fun _ x => -x) (fun _ => measurable_id.neg)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hεn : 0 ≤ (n : ℝ)*ε := mul_nonneg hnR.le hε
  have hu := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hY
    (fun i (_ : i<n) => hYsub i) hεn
  have hl := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hneg
    (fun i (_ : i<n) => (hYsub i).neg) hεn
  simp only [NNReal.coe_one,mul_one] at hu hl
  have he : -((n : ℝ)*ε)^2/(2*(n : ℝ)) = -(n : ℝ)*ε^2/2 := by
    field_simp [hnR.ne']
  rw [he] at hu hl
  have hs : {ω | ε ≤ |empiricalMean X n ω-p|} ⊆
      {ω | (n : ℝ)*ε ≤ ∑ i ∈ Finset.range n, Y i ω} ∪
      {ω | (n : ℝ)*ε ≤ ∑ i ∈ Finset.range n, -(Y i ω)} := by
    intro ω hω
    have hsum : (∑ i ∈ Finset.range n, Y i ω) = (n : ℝ)*(empiricalMean X n ω-p) := by
      simp only [Y,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,empiricalMean]
      field_simp [hnR.ne']
    change ε ≤ |empiricalMean X n ω-p| at hω
    rcases le_abs.mp hω with h | h
    · left
      change (n : ℝ)*ε ≤ _
      rw [hsum]
      exact mul_le_mul_of_nonneg_left h hnR.le
    · right
      change (n : ℝ)*ε ≤ _
      rw [Finset.sum_neg_distrib,hsum]
      nlinarith [mul_le_mul_of_nonneg_left h hnR.le]
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by linarith))

theorem empiricalMean_finite_deviation {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → ℕ → Ω → ℝ)
    (hX : ∀ t i, Measurable (X t i)) (hI : ∀ t, iIndepFun (X t) μ)
    (hb : ∀ t i ω, X t i ω ∈ Icc (0 : ℝ) 1) (p : ι → ℝ) (hp : ∀ t, p t ∈ Icc (0 : ℝ) 1)
    (hmean : ∀ t i, (∫ ω, X t i ω ∂μ)=p t) (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0≤ε) :
    μ.real {ω | ∃ t, ε ≤ |empiricalMean (X t) n ω-p t|} ≤
      (Fintype.card ι : ℝ)*2*Real.exp (-(n : ℝ)*ε^2/2) := by
  have he : {ω | ∃ t, ε ≤ |empiricalMean (X t) n ω-p t|} =
      ⋃ t, {ω | ε ≤ |empiricalMean (X t) n ω-p t|} := by ext ω; simp
  rw [he]
  calc
    _ ≤ ∑ t, μ.real {ω | ε ≤ |empiricalMean (X t) n ω-p t|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _t : ι, 2*Real.exp (-(n : ℝ)*ε^2/2) := Finset.sum_le_sum fun t _ =>
      empiricalMean_deviation μ (X t) (hX t) (hI t) (hb t) (p t) (hp t) (hmean t) n hn ε hε
    _ = _ := by simp [mul_assoc]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
