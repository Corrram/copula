import Copula.Rank.Region.XiBlest.Support.QuadraticBandSampling

/-! # Conditional moments from independent uniform sampling -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem quadraticSample_second_uniform (b : ℝ) (hb : 0 ≤ b) :
    (volume : Measure (I × I)).map (fun p => quadraticSample b p 1) = volume := by
  have h := (quadraticBand b hb).map_eval 1
  rw [quadraticBand_toMeasure_sample,Measure.map_map (measurable_pi_apply 1)
    (continuous_quadraticSample b).measurable] at h
  exact h

noncomputable def quadraticMoment (b : ℝ) (w : I → ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  ∫ t : I, w t * unitClamp (a+b*(1-(t : ℝ))^2)^k

theorem continuous_quadraticMoment (b : ℝ) (w : I → ℝ) (hw : Continuous w) (k : ℕ) :
    Continuous (quadraticMoment b w k) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure I))
    (f := fun a : ℝ => fun t : I => w t * unitClamp (a+b*(1-(t : ℝ))^2)^k)
    (by unfold unitClamp; fun_prop) isCompact_univ
  change Continuous (fun a : ℝ => ∫ t : I, w t * unitClamp (a+b*(1-(t : ℝ))^2)^k)
  simpa only [Measure.restrict_univ] using h

theorem quadratic_kernel_moment_sample (b : ℝ) (hb : 0 ≤ b)
    (w : I → ℝ) (hw : Continuous w) (k : ℕ) :
    (∫ v : I, ∫ t : I, w t * quadraticKernel b hb v t ^ k) =
      ∫ u : I, ∫ t : I, ∫ z : I, w t * unitClamp ((z : ℝ)+b*((1-(t : ℝ))^2-(1-(u : ℝ))^2))^k := by
  let f : I → ℝ := fun v => quadraticMoment b w k (quadraticIntercept b hb v)
  have hf : Measurable f := (continuous_quadraticMoment b w hw k).measurable.comp
    (quadraticIntercept_monotone b hb).measurable
  have hs (u z : I) : f (quadraticSample b (u,z) 1) =
      ∫ t : I, w t * unitClamp ((z : ℝ)+b*((1-(t : ℝ))^2-(1-(u : ℝ))^2))^k := by
    dsimp only [f,quadraticSample,Matrix.cons_val_one,Matrix.cons_val_zero]
    rw [quadraticIntercept_quadraticMean b hb (quadraticSample_intercept_mem hb u z)]
    unfold quadraticMoment
    congr 1; funext t
    congr 3
    ring
  have hi : Integrable (fun p : I × I => f (quadraticSample b p 1)) := by
    have he : (fun p : I × I => f (quadraticSample b p 1)) =
        fun p : I × I => quadraticMoment b w k ((p.2 : ℝ)-b*(1-(p.1 : ℝ))^2) := by
      funext p
      dsimp only [f,quadraticSample,Matrix.cons_val_one,Matrix.cons_val_zero]
      rw [quadraticIntercept_quadraticMean b hb (quadraticSample_intercept_mem hb p.1 p.2)]
    rw [he]
    exact ((continuous_quadraticMoment b w hw k).comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ v : I, f v) = _
  conv_lhs => rw [← quadraticSample_second_uniform b hb]
  rw [integral_map (show Measurable (fun p : I × I => quadraticSample b p 1) by fun_prop).aemeasurable
      hf.aestronglyMeasurable]
  change (∫ p : I × I, f (quadraticSample b p 1) ∂(volume : Measure I).prod volume) = _
  rw [integral_prod _ hi]
  simp_rw [hs]
  congr 1; funext u
  apply integral_integral_swap
  exact (show Continuous (fun p : I × I => w p.2 * unitClamp ((p.1 : ℝ)+
    b*((1-(p.2 : ℝ))^2-(1-(u : ℝ))^2))^k) by
      unfold unitClamp; fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
