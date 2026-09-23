import Copula.Rank.Region.XiBlest.Support.QuadraticBand

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- A uniform rate at the comonotonic endpoint. -/
theorem quadraticBand_comonotonic_error (b r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) (hbr : 1 ≤ b*r^2) (u v : I) :
    |(quadraticBand b hb.le).cdf ![u,v] - min (u : ℝ) (v : ℝ)| ≤ r := by
  let a := quadraticIntercept b hb.le v
  let g : I → ℝ := fun t => unitClamp (a+b*(1-(t : ℝ))^2)
  have hi : Integrable g := quadraticKernel_integrable b hb.le v
  have hm : (∫ t, g t) = (v : ℝ) := quadraticIntercept_mean b hb.le v
  have hc : (quadraticBand b hb.le).cdf ![u,v] = ∫ t in Iic u, g t := quadraticBand_cdf b hb.le u v
  have hup : (quadraticBand b hb.le).cdf ![u,v] ≤ min (u : ℝ) (v : ℝ) := by
    exact le_min ((quadraticBand b hb.le).cdf_le_coord ![u,v] 0)
      ((quadraticBand b hb.le).cdf_le_coord ![u,v] 1)
  rw [abs_of_nonpos (sub_nonpos.mpr hup)]
  by_cases hu : a+b*(1-(u : ℝ))^2 ≤ 0
  · have ht : (∫ t in Ioc u (1 : I), g t) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      dsimp [g, unitClamp]
      have hp : (1-(t : ℝ))^2 ≤ (1-(u : ℝ))^2 := by
        nlinarith [show (u : ℝ) < t from ht.1,u.property.2,t.property.2]
      rw [max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left hp hb.le])]
      norm_num
    have he := Copula.integral_Iic_add_Ioc_unit hi (show u ≤ (1 : I) from u.property.2)
    have hs : Iic (1 : I) = univ := by ext t; simp [unitInterval.le_one']
    rw [ht, hs, Measure.restrict_univ, hm, add_zero, ← hc] at he
    rw [he]
    linarith [min_le_right (u : ℝ) (v : ℝ)]
  · by_cases hs : (u : ℝ) ≤ r
    · have hn := (quadraticBand b hb.le).cdf_nonneg ![u,v]
      linarith [min_le_left (u : ℝ) (v : ℝ)]
    · let s : I := ⟨(u : ℝ)-r, by constructor <;> linarith [u.property.2]⟩
      have hsu : s ≤ u := by change (u : ℝ)-r ≤ u; linarith
      have hg : (∫ t in Iic s, g t) = (s : ℝ) := by
        calc
          _ = ∫ _t in Iic s, (1 : ℝ) := by
            apply setIntegral_congr_fun measurableSet_Iic
            intro t ht
            have hts : (t : ℝ) ≤ (u : ℝ)-r := ht
            have hp : r^2 ≤ (1-(t : ℝ))^2-(1-(u : ℝ))^2 := by
              nlinarith [sq_nonneg ((u : ℝ)-(t : ℝ)-r),
                mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr (le_trans hts (by linarith : (u : ℝ)-r ≤ u)))]
            have hraw : 1 ≤ a+b*(1-(t : ℝ))^2 := by
              nlinarith [mul_le_mul_of_nonneg_left hp hb.le]
            dsimp [g, unitClamp]
            rw [max_eq_right (by linarith), min_eq_left hraw]
          _ = _ := by simp [Measure.real, unitInterval.volume_Iic, s.property.1]
      have ht : 0 ≤ ∫ t in Ioc s u, g t :=
        integral_nonneg (fun t => (unitClamp_mem _).1)
      have he := Copula.integral_Iic_add_Ioc_unit hi hsu
      rw [hg, ← hc] at he
      have hsval : (s : ℝ) = (u : ℝ)-r := rfl
      linarith [min_le_left (u : ℝ) (v : ℝ)]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
