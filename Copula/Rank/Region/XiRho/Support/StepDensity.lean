import Copula.Rank.Region.XiRho.Support.TwoStrip
import Copula.Dependence.Density

/-! # Exact density identification for two-strip copulas -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

noncomputable def lowerStep (a u : I) : ℝ := if u ≤ a then 1 else 0

theorem measurable_lowerStep (a : I) : Measurable (lowerStep a) := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem integrable_lowerStep (a : I) : Integrable (lowerStep a) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_lowerStep a).aestronglyMeasurable
  filter_upwards [] with u
  unfold lowerStep
  split_ifs <;> norm_num

theorem integral_lowerStep (a u : I) :
    (∫ t in Iic u, lowerStep a t) = min (u : ℝ) a := by
  change (∫ t in Iic u, (Iic a).indicator (fun _ => (1 : ℝ)) t) = _
  rw [setIntegral_indicator measurableSet_Iic, setIntegral_one_eq_measureReal]
  simp only [Iic_inter_Iic, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal (min u a).property.1]
  rfl

noncomputable def medianSign (u : I) : ℝ := if u ≤ Copula.unitHalf then 1 else -1

theorem measurable_medianSign : Measurable medianSign := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem integral_medianSign (u : I) :
    (∫ t in Iic u, medianSign t) = medianWedge u := by
  unfold medianSign
  rw [integral_median_step]
  simp only [medianWedge, min_def, max_def]
  split_ifs <;> linarith

theorem twoStrip_density (g : StripDisplacement) (d : I → ℝ)
    (hd : Measurable d) (hd1 : ∀ v, |d v| ≤ 1)
    (hprimitive : ∀ v, (∫ t in Iic v, d t) = g v) :
    (twoStrip g).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (1 + medianSign (x 0) * d (x 1))) := by
  have hm : Measurable (fun x : Fin 2 → I => medianSign (x 0) * d (x 1)) :=
    (measurable_medianSign.comp (measurable_pi_apply 0)).mul (hd.comp (measurable_pi_apply 1))
  have hb (x : Fin 2 → I) : |medianSign (x 0) * d (x 1)| ≤ 1 := by
    rw [abs_mul]
    have hs : |medianSign (x 0)| = 1 := by unfold medianSign; split_ifs <;> norm_num
    simpa only [hs, one_mul] using hd1 (x 1)
  have hi : Integrable (fun x : Fin 2 → I => medianSign (x 0) * d (x 1)) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  apply Copula.toMeasure_eq_withDensity_of_cdf_integral _ ((integrable_const _).add hi)
  · intro x
    change 0 ≤ 1 + medianSign (x 0) * d (x 1)
    linarith [(abs_le.mp (hb x)).1]
  · intro u
    have hu : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
    simp only [Pi.add_apply]
    rw [integral_add (integrable_const _) hi.integrableOn, setIntegral_one_eq_measureReal]
    change (Copula.independence 2).cdf u + _ = _
    rw [hu, Copula.integral_cube_Iic_mul, integral_medianSign, hprimitive, cdf_twoStrip]
    simp [Copula.cdf_independence, Fin.prod_univ_two]

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
