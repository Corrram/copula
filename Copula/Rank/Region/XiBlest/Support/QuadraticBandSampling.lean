import Copula.Rank.Region.XiBlest.Support.QuadraticMeanInverse
import Copula.Rank.Region.XiBlest.Support.BandSampling

/-! # Sampling a quadratic band from two independent uniforms -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- The second rank is the CDF transform of Z-b*(1-U)^2. -/
noncomputable def quadraticSample (b : ℝ) (p : I × I) : Fin 2 → I :=
  ![p.1, quadraticMeanUnit b ((p.2 : ℝ)-b*(1-(p.1 : ℝ))^2)]

@[fun_prop] theorem continuous_quadraticSample (b : ℝ) : Continuous (quadraticSample b) := by
  unfold quadraticSample
  fun_prop

theorem quadraticSample_intercept_mem {b : ℝ} (hb : 0 ≤ b) (u z : I) :
    (z : ℝ)-b*(1-(u : ℝ))^2 ∈ Icc (-b) (1 : ℝ) := by
  have hp : (1-(u : ℝ))^2 ≤ 1 := by nlinarith [u.property.1,u.property.2]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hp hb,z.property.1]
  · nlinarith [mul_nonneg hb (sq_nonneg (1-(u : ℝ))),z.property.2]

/-- The complete lower-orthant distribution of the sampled vector. -/
theorem quadraticSample_orthant (b : ℝ) (hb : 0 ≤ b) (u v : I) :
    (∫ p : I × I, if quadraticSample b p ≤ ![u,v] then (1 : ℝ) else 0) =
      (quadraticBand b hb).cdf ![u,v] := by
  let f : I × I → ℝ := fun p => if quadraticSample b p ≤ ![u,v] then 1 else 0
  have hi : Integrable f := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (measurable_const.ite
        (measurableSet_le (continuous_quadraticSample b).measurable measurable_const)
        measurable_const).aestronglyMeasurable
    · dsimp [f]; split_ifs <;> norm_num
  have he (t z : I) : quadraticSample b (t,z) ≤ ![u,v] ↔
      t ≤ u ∧ (z : ℝ) ≤ quadraticIntercept b hb v+b*(1-(t : ℝ))^2 := by
    simp only [quadraticSample, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    change (t ≤ u ∧ quadraticMean b ((z : ℝ)-b*(1-(t : ℝ))^2) ≤ (v : ℝ)) ↔ _
    rw [quadraticMean_le_iff b hb (quadraticSample_intercept_mem hb t z)]
    constructor <;> rintro ⟨ht,hz⟩ <;> exact ⟨ht, by linarith⟩
  change (∫ p, f p ∂(volume : Measure I).prod volume) = _
  rw [integral_prod _ hi]
  dsimp only [f]
  simp_rw [he]
  have hz (t : I) : (∫ z : I, if t ≤ u ∧ (z : ℝ) ≤ quadraticIntercept b hb v+b*(1-(t : ℝ))^2
      then (1 : ℝ) else 0) =
      if t ≤ u then unitClamp (quadraticIntercept b hb v+b*(1-(t : ℝ))^2) else 0 := by
    by_cases ht : t ≤ u
    · simp only [ht, true_and, ite_true]
      exact integral_unit_le_real _
    · simp [ht]
  simp_rw [hz]
  rw [quadraticBand_cdf]
  exact integral_indicator measurableSet_Iic

/-- The constructed copula is exactly the law of the sampled vector. -/
theorem quadraticBand_toMeasure_sample (b : ℝ) (hb : 0 ≤ b) :
    (quadraticBand b hb).toMeasure = (volume : Measure (I × I)).map (quadraticSample b) := by
  let μ : ProbabilityMeasure (Fin 2 → I) :=
    ProbabilityMeasure.map (⟨volume, inferInstance⟩ : ProbabilityMeasure (I × I)) (quadraticSample b)
  have hμ (u : Fin 2 → I) : μ.toMeasure.real (Iic u) = (quadraticBand b hb).cdf u := by
    change ((volume : Measure (I × I)).map (quadraticSample b)).real (Iic u) = _
    rw [map_measureReal_apply (continuous_quadraticSample b).measurable measurableSet_Iic]
    have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
    have hi := integral_indicator (μ := (volume : Measure (I × I)))
      (f := fun _ => (1 : ℝ)) (s := (quadraticSample b) ⁻¹' Iic u)
      ((continuous_quadraticSample b).measurable measurableSet_Iic)
    have hf : volume.real ((quadraticSample b) ⁻¹' Iic u) =
        ∫ p : I × I, if quadraticSample b p ≤ u then (1 : ℝ) else 0 := by
      simpa [Set.indicator, smul_eq_mul] using hi.symm
    rw [hf, ← he]
    exact quadraticSample_orthant b hb _ _
  let D := (quadraticBand b hb).isClassical_cdf.ofMeasure μ hμ
  have he : D = quadraticBand b hb :=
    Copula.cdf_injective ((quadraticBand b hb).isClassical_cdf.cdf_ofMeasure μ hμ)
  rw [← he]
  rfl

/-- Integrals under the band can be evaluated on two independent uniforms. -/
theorem quadraticBand_integral_sample (b : ℝ) (hb : 0 ≤ b)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(quadraticBand b hb).toMeasure) = ∫ u : I, ∫ z : I, f (quadraticSample b (u,z)) := by
  rw [quadraticBand_toMeasure_sample,
    integral_map (continuous_quadraticSample b).measurable.aemeasurable hf.measurable.aestronglyMeasurable]
  apply integral_prod
  exact (hf.comp (continuous_quadraticSample b)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The CDF at the sampled point has a simple quadratic clamped integrand. -/
theorem quadraticBand_cdf_sample (b : ℝ) (hb : 0 ≤ b) (u z : I) :
    (quadraticBand b hb).cdf (quadraticSample b (u,z)) =
      ∫ t in Iic u, unitClamp ((z : ℝ)-b*(1-(u : ℝ))^2+b*(1-(t : ℝ))^2) := by
  rw [quadraticSample, quadraticBand_cdf, quadraticIntercept_quadraticMean b hb (quadraticSample_intercept_mem hb u z)]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
