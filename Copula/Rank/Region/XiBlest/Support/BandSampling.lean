import Copula.Rank.Region.XiBlest.Support.BandMeanInverse

/-! # Sampling a diagonal band from two independent uniforms -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- The second rank is the CDF transform of b*U+Z. -/
noncomputable def bandSample (b : ℝ) (p : I × I) : Fin 2 → I :=
  ![p.1, clampedMeanUnit b (b*(p.1 : ℝ)+(p.2 : ℝ))]

@[fun_prop] theorem continuous_bandSample (b : ℝ) : Continuous (bandSample b) := by
  unfold bandSample
  fun_prop

theorem bandSample_intercept_mem {b : ℝ} (hb : 0 ≤ b) (u z : I) :
    b*(u : ℝ)+(z : ℝ) ∈ Icc (0 : ℝ) (b+1) :=
  ⟨add_nonneg (mul_nonneg hb u.property.1) z.property.1, by nlinarith [u.property.2, z.property.2]⟩

theorem integral_unit_le_real (r : ℝ) :
    (∫ z : I, if (z : ℝ) ≤ r then (1 : ℝ) else 0) = unitClamp r := by
  by_cases h0 : r < 0
  · have he (z : I) : ¬(z : ℝ) ≤ r := by linarith [z.property.1]
    simp [he, unitClamp, max_eq_left h0.le]
  by_cases h1 : 1 < r
  · have he (z : I) : (z : ℝ) ≤ r := z.property.2.trans h1.le
    simp [he, unitClamp, max_eq_right (by linarith : 0 ≤ r), min_eq_left h1.le]
  let t : I := ⟨r, by constructor <;> linarith⟩
  have he : (fun z : I => if (z : ℝ) ≤ r then (1 : ℝ) else 0) =
      (Iic t).indicator (fun _ => 1) := rfl
  rw [he, integral_indicator measurableSet_Iic]
  simp [Measure.real, unitInterval.volume_Iic, t, unitClamp,
    min_eq_right (by linarith : r ≤ 1), show 0 ≤ r by linarith]

/-- The complete lower-orthant distribution of the sampled vector. -/
theorem bandSample_orthant (b : ℝ) (hb : 0 ≤ b) (u v : I) :
    (∫ p : I × I, if bandSample b p ≤ ![u,v] then (1 : ℝ) else 0) =
      (diagonalBand b hb).cdf ![u,v] := by
  let f : I × I → ℝ := fun p => if bandSample b p ≤ ![u,v] then 1 else 0
  have hi : Integrable f := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (measurable_const.ite
        (measurableSet_le (continuous_bandSample b).measurable measurable_const)
        measurable_const).aestronglyMeasurable
    · dsimp [f]; split_ifs <;> norm_num
  have he (t z : I) : bandSample b (t,z) ≤ ![u,v] ↔
      t ≤ u ∧ (z : ℝ) ≤ bandIntercept b hb v-b*(t : ℝ) := by
    simp only [bandSample, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    change (t ≤ u ∧ clampedMean b (b*(t : ℝ)+(z : ℝ)) ≤ (v : ℝ)) ↔ _
    rw [clampedMean_le_iff b hb (bandSample_intercept_mem hb t z)]
    constructor <;> rintro ⟨ht,hz⟩ <;> exact ⟨ht, by linarith⟩
  change (∫ p, f p ∂(volume : Measure I).prod volume) = _
  rw [integral_prod _ hi]
  dsimp only [f]
  simp_rw [he]
  have hz (t : I) : (∫ z : I, if t ≤ u ∧ (z : ℝ) ≤ bandIntercept b hb v-b*(t : ℝ)
      then (1 : ℝ) else 0) =
      if t ≤ u then unitClamp (bandIntercept b hb v-b*(t : ℝ)) else 0 := by
    by_cases ht : t ≤ u
    · simp only [ht, true_and, ite_true]
      exact integral_unit_le_real _
    · simp [ht]
  simp_rw [hz]
  rw [diagonalBand_cdf]
  exact integral_indicator measurableSet_Iic

/-- The constructed copula is exactly the law of the sampled vector. -/
theorem diagonalBand_toMeasure_sample (b : ℝ) (hb : 0 ≤ b) :
    (diagonalBand b hb).toMeasure = (volume : Measure (I × I)).map (bandSample b) := by
  let μ : ProbabilityMeasure (Fin 2 → I) :=
    ProbabilityMeasure.map (⟨volume, inferInstance⟩ : ProbabilityMeasure (I × I)) (bandSample b)
  have hμ (u : Fin 2 → I) : μ.toMeasure.real (Iic u) = (diagonalBand b hb).cdf u := by
    change ((volume : Measure (I × I)).map (bandSample b)).real (Iic u) = _
    rw [map_measureReal_apply (continuous_bandSample b).measurable measurableSet_Iic]
    have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
    have hi := integral_indicator (μ := (volume : Measure (I × I)))
      (f := fun _ => (1 : ℝ)) (s := (bandSample b) ⁻¹' Iic u)
      ((continuous_bandSample b).measurable measurableSet_Iic)
    have hf : volume.real ((bandSample b) ⁻¹' Iic u) =
        ∫ p : I × I, if bandSample b p ≤ u then (1 : ℝ) else 0 := by
      simpa [Set.indicator, smul_eq_mul] using hi.symm
    rw [hf, ← he]
    exact bandSample_orthant b hb _ _
  let D := (diagonalBand b hb).isClassical_cdf.ofMeasure μ hμ
  have he : D = diagonalBand b hb :=
    Copula.cdf_injective ((diagonalBand b hb).isClassical_cdf.cdf_ofMeasure μ hμ)
  rw [← he]
  rfl

/-- Integrals under the band can be evaluated on two independent uniforms. -/
theorem diagonalBand_integral_sample (b : ℝ) (hb : 0 ≤ b)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(diagonalBand b hb).toMeasure) = ∫ u : I, ∫ z : I, f (bandSample b (u,z)) := by
  rw [diagonalBand_toMeasure_sample,
    integral_map (continuous_bandSample b).measurable.aemeasurable hf.measurable.aestronglyMeasurable]
  apply integral_prod
  exact (hf.comp (continuous_bandSample b)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The CDF at the sampled point has a simple affine clamped integrand. -/
theorem diagonalBand_cdf_sample (b : ℝ) (hb : 0 ≤ b) (u z : I) :
    (diagonalBand b hb).cdf (bandSample b (u,z)) =
      ∫ t in Iic u, unitClamp (b*(u : ℝ)+(z : ℝ)-b*(t : ℝ)) := by
  rw [bandSample, diagonalBand_cdf, bandIntercept_clampedMean b hb (bandSample_intercept_mem hb u z)]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
