import Copula.Rank.Region.XiBeta.Mixtures
import Copula.Dependence.Conditional
import Copula.Rank.Region.XiBeta.TentIntegral

/-! # The universal cubic inequality

The proof uses the two median strips and a one-dimensional tent estimate.
All conditional integrals are with respect to the copula's regular kernel;
no density or differentiability hypothesis is imposed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBeta

/-- Displacement of the conditional distribution on the lower median strip. -/
noncomputable def medianDisplacement (C : Copula 2) (v : I) : ℝ :=
  2 * C.cdf ![Copula.unitHalf, v] - v

theorem medianDisplacement_lipschitz (C : Copula 2) (v w : I) :
    |medianDisplacement C v - medianDisplacement C w| ≤ |(v : ℝ) - w| := by
  suffices hs : ∀ v w : I, v ≤ w →
      |medianDisplacement C v - medianDisplacement C w| ≤ |(v : ℝ) - w| by
    rcases le_total v w with h | h
    · exact hs v w h
    · simpa only [abs_sub_comm] using hs w v h
  intro v w hvw
  have hm := C.monotone_cdf (show ![Copula.unitHalf, v] ≤ ![Copula.unitHalf, w] by
    intro i; fin_cases i <;> simp [hvw])
  have hl := C.cdf_sub_le_sum_abs ![Copula.unitHalf, w] ![Copula.unitHalf, v]
  have hvw' : (v : ℝ) ≤ w := hvw
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, abs_zero, zero_add, abs_of_nonneg (sub_nonneg.mpr hvw')] at hl
  rw [abs_of_nonpos (sub_nonpos.mpr hvw')]
  unfold medianDisplacement
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Jensen's inequality on each half, proved by integrating a square. -/
theorem median_strip_energy (C : Copula 2) (v : I) :
    medianDisplacement C v ^ 2 ≤
      (∫ u : I, C.conditionalCDF u v ^ 2) - (v : ℝ) ^ 2 := by
  let c := C.cdf ![Copula.unitHalf, v]
  have hL : (∫ u in Iic Copula.unitHalf, C.conditionalCDF u v) = c :=
    (C.cdf_eq_integral_conditionalCDF _ _).symm
  have hR : (∫ u in Ioi Copula.unitHalf, C.conditionalCDF u v) = (v : ℝ) - c := by
    have h := integral_add_compl (s := Iic Copula.unitHalf) measurableSet_Iic (C.integrable_conditionalCDF v)
    rw [compl_Iic, C.integral_conditionalCDF, hL] at h
    linarith
  have square (s : Set I) (k : ℝ) :
      0 ≤ (∫ u in s, C.conditionalCDF u v ^ 2) -
        2 * k * (∫ u in s, C.conditionalCDF u v) + volume.real s * k ^ 2 := by
    have hn : 0 ≤ ∫ u in s, (C.conditionalCDF u v - k) ^ 2 :=
      integral_nonneg (fun _ => sq_nonneg _)
    have he : (fun u => (C.conditionalCDF u v - k) ^ 2) =
        fun u => C.conditionalCDF u v ^ 2 - (2 * k) * C.conditionalCDF u v + k ^ 2 := by
      funext u; ring
    have hi : Integrable (fun u => C.conditionalCDF u v ^ 2) (volume.restrict s) :=
      (C.integrable_conditionalCDF_sq v).integrableOn
    have hj : Integrable (fun u => (2 * k) * C.conditionalCDF u v) (volume.restrict s) :=
      (C.integrable_conditionalCDF v).integrableOn.const_mul _
    have hadd := integral_add (hi.sub hj) (integrable_const (k ^ 2))
    simp only [Pi.sub_apply] at hadd
    rw [he, hadd,
      integral_sub hi hj, integral_const_mul, integral_const] at hn
    simpa only [Measure.restrict_apply_univ, Measure.real, smul_eq_mul] using hn
  have h₁ := square (Iic Copula.unitHalf) (2 * c)
  have h₂ := square (Ioi Copula.unitHalf) (2 * ((v : ℝ) - c))
  have hsum := integral_add_compl (s := Iic Copula.unitHalf) measurableSet_Iic (C.integrable_conditionalCDF_sq v)
  rw [compl_Iic] at hsum
  rw [hL] at h₁
  rw [hR] at h₂
  have hmL : volume.real (Iic Copula.unitHalf) = (1 / 2 : ℝ) := by
    norm_num [Measure.real, unitInterval.volume_Iic, Copula.unitHalf]
  have hmR : volume.real (Ioi Copula.unitHalf) = (1 / 2 : ℝ) := by
    norm_num [Measure.real, unitInterval.volume_Ioi, Copula.unitHalf]
  rw [hmL] at h₁
  rw [hmR] at h₂
  change (2 * c - (v : ℝ)) ^ 2 ≤ _
  nlinarith

theorem median_energy_le_xi (C : Copula 2) :
    6 * (∫ v : I, medianDisplacement C v ^ 2) ≤ C.chatterjeeXi := by
  have hi : Integrable (fun v : I => medianDisplacement C v ^ 2) :=
    Copula.integrable_continuous_unit volume (by unfold medianDisplacement; fun_prop)
  have hj : Integrable (fun v : I => (v : ℝ) ^ 2) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  have h := integral_mono hi (C.integrable_integral_conditionalCDF_sq.sub hj)
    (median_strip_energy C)
  simp only [Pi.sub_apply] at h
  rw [integral_sub C.integrable_integral_conditionalCDF_sq hj, Copula.integral_unit_pow] at h
  unfold Copula.chatterjeeXi
  norm_num at h
  linarith

/-- The beta constraint forces a tent-shaped lower bound on absolute displacement. -/
theorem medianTent_le_abs_displacement (C : Copula 2) (v : I) :
    ProbabilityTheory.Copula.RankRegion.XiBeta.medianTent |C.blomqvistBeta| v ≤ |medianDisplacement C v| := by
  have hh : medianDisplacement C Copula.unitHalf = C.blomqvistBeta / 2 := by
    unfold medianDisplacement Copula.blomqvistBeta Copula.unitHalf
    ring
  have h := abs_sub_abs_le_abs_sub (medianDisplacement C Copula.unitHalf)
    (medianDisplacement C v)
  have hl := medianDisplacement_lipschitz C Copula.unitHalf v
  rw [hh, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  change |medianDisplacement C Copula.unitHalf - medianDisplacement C v| ≤
    |(1 / 2 : ℝ) - (v : ℝ)| at hl
  rw [abs_sub_comm (1 / 2 : ℝ), hh] at hl
  unfold ProbabilityTheory.Copula.RankRegion.XiBeta.medianTent
  exact max_le (abs_nonneg _) (by linarith)

/-- Proposition 5, inequality part, for every copula including singular laws. -/
theorem beta_cubic_le_two_xi (C : Copula 2) :
    |C.blomqvistBeta| ^ 3 ≤ 2 * C.chatterjeeXi := by
  have hi : Integrable (fun v : I => ProbabilityTheory.Copula.RankRegion.XiBeta.medianTent |C.blomqvistBeta| v ^ 2) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  have hj : Integrable (fun v : I => medianDisplacement C v ^ 2) :=
    Copula.integrable_continuous_unit volume (by unfold medianDisplacement; fun_prop)
  have h := integral_mono hi hj (fun v => by
    have ht := medianTent_le_abs_displacement C v
    have hn : 0 ≤ ProbabilityTheory.Copula.RankRegion.XiBeta.medianTent |C.blomqvistBeta| v := le_max_left _ _
    nlinarith [sq_abs (medianDisplacement C v)])
  rw [ProbabilityTheory.Copula.RankRegion.XiBeta.integral_medianTent_sq (abs_nonneg _) (abs_le.mpr C.blomqvistBeta_mem_Icc)] at h
  have he := median_energy_le_xi C
  linarith

end ProbabilityTheory.Copula.RankRegion.XiBeta
