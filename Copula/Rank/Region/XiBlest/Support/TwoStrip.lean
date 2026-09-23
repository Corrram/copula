import Copula.Classical.Bivariate
import Copula.Rank.Basic
import Copula.Rank.ConditionalCDF

/-! # Copulas from a Lipschitz displacement on two median strips -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

structure StripDisplacement where
  toFun : I → ℝ
  zero : toFun 0 = 0
  one : toFun 1 = 0
  lipschitz : ∀ v w, |toFun v - toFun w| ≤ |(v : ℝ) - w|

instance : CoeFun StripDisplacement (fun _ => I → ℝ) := ⟨StripDisplacement.toFun⟩

noncomputable def medianWedge (u : I) : ℝ := min (u : ℝ) (1 - u)

theorem medianWedge_lipschitz (u v : I) :
    |medianWedge u - medianWedge v| ≤ |(u : ℝ) - v| := by
  have h := abs_min_sub_min_le_max (u : ℝ) (1 - (u : ℝ)) (v : ℝ) (1 - (v : ℝ))
  have he : 1 - (u : ℝ) - (1 - (v : ℝ)) = -((u : ℝ) - v) := by ring
  simpa only [he, abs_neg, max_self, medianWedge] using h

theorem StripDisplacement.continuous (g : StripDisplacement) : Continuous g := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa [Real.dist_eq, Subtype.dist_eq] using g.lipschitz v w

theorem StripDisplacement.abs_le (g : StripDisplacement) (v : I) : |g v| ≤ (v : ℝ) := by
  simpa [g.zero, abs_of_nonneg v.property.1] using g.lipschitz v 0

private theorem twoStrip_classical (g : StripDisplacement) :
    Copula.IsClassical (fun x : Fin 2 → I => (x 0 : ℝ) * x 1 + medianWedge (x 0) * g (x 1)) := by
  apply Copula.IsClassical.ofBivariate
    (fun u v => (u : ℝ) * v + medianWedge u * g v)
  · intro v; simp [medianWedge]
  · intro u; simp [g.zero]
  · intro v; simp [medianWedge]
  · intro u; simp [g.one]
  · intro a b c d hab hcd
    have hL := medianWedge_lipschitz b a
    have hG := g.lipschitz d c
    have hab' : (a : ℝ) ≤ b := hab
    have hcd' : (c : ℝ) ≤ d := hcd
    rw [abs_of_nonneg (sub_nonneg.mpr hab')] at hL
    rw [abs_of_nonneg (sub_nonneg.mpr hcd')] at hG
    have h := mul_le_mul hL hG (abs_nonneg _) (sub_nonneg.mpr hab')
    rw [← abs_mul] at h
    have hn := neg_abs_le ((medianWedge b - medianWedge a) * (g d - g c))
    nlinarith

noncomputable def twoStrip (g : StripDisplacement) : Copula 2 :=
  Copula.ofClassical _ (twoStrip_classical g)

@[simp] theorem cdf_twoStrip (g : StripDisplacement) (u v : I) :
    (twoStrip g).cdf ![u, v] = (u : ℝ) * v + medianWedge u * g v := by
  simp [twoStrip]

noncomputable def stripKernel (g : StripDisplacement) (v u : I) : ℝ :=
  if u ≤ Copula.unitHalf then (v : ℝ) + g v else (v : ℝ) - g v

theorem stripKernel_integrable (g : StripDisplacement) (v : I) :
    Integrable (stripKernel g v) := by
  classical
  exact Integrable.piecewise (s := Iic Copula.unitHalf) (μ := (volume : Measure I))
    measurableSet_Iic (integrable_const _) (integrable_const _)

/-- Exact integration of any two constants separated at the median. -/
theorem integral_median_step (p q : ℝ) (u : I) :
    (∫ t in Iic u, if t ≤ Copula.unitHalf then p else q) =
      min (u : ℝ) (1 / 2) * p + max 0 ((u : ℝ) - 1 / 2) * q := by
  classical
  have he : (fun t : I => if t ≤ Copula.unitHalf then p else q) =
      (Iic Copula.unitHalf).piecewise (fun _ => p) (fun _ => q) := rfl
  rw [he, integral_piecewise measurableSet_Iic (integrable_const _) (integrable_const _)]
  simp only [setIntegral_const, smul_eq_mul, Measure.real, Measure.restrict_apply measurableSet_Iic,
    compl_Iic, Measure.restrict_apply measurableSet_Ioi]
  rw [Iic_inter_Iic]
  have hI : Ioi Copula.unitHalf ∩ Iic u = Ioc Copula.unitHalf u := rfl
  rw [hI, unitInterval.volume_Iic, unitInterval.volume_Ioc]
  rw [ENNReal.toReal_ofReal (min Copula.unitHalf u).property.1]
  change min (1 / 2 : ℝ) (u : ℝ) * p +
    (ENNReal.ofReal ((u : ℝ) - 1 / 2)).toReal * q = _
  rw [ENNReal.toReal_ofReal', min_comm, max_comm]

theorem integral_stripKernel_Iic (g : StripDisplacement) (v u : I) :
    (∫ t in Iic u, stripKernel g v t) = (twoStrip g).cdf ![u, v] := by
  rw [cdf_twoStrip]
  unfold stripKernel
  rw [integral_median_step]
  unfold medianWedge
  by_cases hu : (u : ℝ) ≤ 1 / 2
  · rw [min_eq_left hu, max_eq_left (by linarith), min_eq_left (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge hu), max_eq_right (by linarith),
      min_eq_right (by linarith)]
    ring

theorem conditionalCDF_twoStrip (g : StripDisplacement) (v : I) :
    (fun u => (twoStrip g).conditionalCDF u v) =ᵐ[volume] stripKernel g v := by
  apply Copula.conditionalCDF_ae_eq_of_integral _ v (stripKernel_integrable g v)
  · intro u
    have h := abs_le.mp (g.abs_le v)
    unfold stripKernel
    split_ifs <;> linarith
  · exact integral_stripKernel_Iic g v

theorem integral_stripKernel_sq (g : StripDisplacement) (v : I) :
    (∫ u : I, stripKernel g v u ^ 2) = (v : ℝ) ^ 2 + g v ^ 2 := by
  have he : (fun u => stripKernel g v u ^ 2) =
      fun u => if u ≤ Copula.unitHalf then ((v : ℝ) + g v) ^ 2 else ((v : ℝ) - g v) ^ 2 := by
    funext u; unfold stripKernel; split_ifs <;> rfl
  have h := integral_median_step (((v : ℝ) + g v) ^ 2) (((v : ℝ) - g v) ^ 2) 1
  have hI : Iic (1 : I) = univ := by ext x; simp [unitInterval.le_one']
  rw [he]
  simp only [hI, Measure.restrict_univ] at h
  rw [h]
  norm_num
  ring

/-- Population xi of the two-strip copula; valid for any Lipschitz displacement. -/
theorem xi_twoStrip (g : StripDisplacement) :
    (twoStrip g).chatterjeeXi = 6 * (∫ v : I, g v ^ 2) := by
  have he (v : I) : (∫ u : I, (twoStrip g).conditionalCDF u v ^ 2) =
      (v : ℝ) ^ 2 + g v ^ 2 := by
    rw [← integral_stripKernel_sq]
    exact integral_congr_ae ((conditionalCDF_twoStrip g v).fun_comp (fun x : ℝ => x ^ 2))
  unfold Copula.chatterjeeXi
  simp_rw [he]
  have hi : Integrable (fun v : I => (v : ℝ) ^ 2) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  have hj : Integrable (fun v : I => g v ^ 2) :=
    Copula.integrable_continuous_unit volume ((continuous_pow 2).comp g.continuous)
  rw [integral_add hi hj, Copula.integral_unit_pow]
  norm_num
  ring

theorem beta_twoStrip (g : StripDisplacement) :
    (twoStrip g).blomqvistBeta = 2 * g Copula.unitHalf := by
  rw [Copula.blomqvistBeta, cdf_twoStrip]
  norm_num [medianWedge, Copula.unitHalf]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
