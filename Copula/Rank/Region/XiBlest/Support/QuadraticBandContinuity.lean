import Copula.Rank.Region.XiBlest.Support.QuadraticMeanInverse
import Copula.Rank.Region.XiBlest.Support.CDFRankStability

/-! # Quantitative continuity of the normalized quadratic family -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem clamp_shift {x y r : ℝ} (hr : 0 ≤ r) (h : x ≤ y + r) :
    unitClamp x ≤ unitClamp y + r := by
  unfold unitClamp
  simp only [min_def, max_def]
  split_ifs <;> linarith

private theorem intercept_le_shift (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (v : I) :
    quadraticIntercept b hb v ≤ quadraticIntercept d hd v + |b-d| := by
  let c := quadraticIntercept d hd v
  let r := |b-d|
  have hc := quadraticIntercept_mem d hd v
  have ha := quadraticIntercept_mem b hb v
  have hr : 0 ≤ r := abs_nonneg _
  have hbd : d-b ≤ r := by dsimp [r]; linarith [neg_le_abs (b-d)]
  by_cases htop : 1 ≤ c+r
  · exact ha.2.trans htop
  · have hcr : c+r ∈ Icc (-b) (1 : ℝ) := ⟨by dsimp [c] at *; linarith [hc.1], le_of_not_ge htop⟩
    apply ((quadraticMean_strictMonoOn hb).le_iff_le (quadraticIntercept_mem _ _ _) hcr).mp
    rw [quadraticIntercept_mean]
    calc
      (v : ℝ) = quadraticMean d c := (quadraticIntercept_mean d hd v).symm
      _ ≤ quadraticMean b (c+r) := by
        apply integral_mono
          (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
          (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
        intro t
        apply min_le_min le_rfl
        apply max_le_max le_rfl
        have hp0 : 0 ≤ (1-(t : ℝ))^2 := sq_nonneg _
        have hp1 : (1-(t : ℝ))^2 ≤ 1 := by nlinarith [t.property.1,t.property.2]
        have hh := mul_le_mul_of_nonneg_right hbd hp0
        nlinarith [mul_nonneg hr (sub_nonneg.mpr hp1)]

theorem quadraticIntercept_abs_sub_le (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (v : I) :
    |quadraticIntercept b hb v - quadraticIntercept d hd v| ≤ |b-d| := by
  have h1 := intercept_le_shift b d hb hd v
  have h2 := intercept_le_shift d b hd hb v
  rw [abs_sub_comm d b] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem quadraticKernel_abs_sub_le (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (v u : I) :
    |quadraticKernel b hb v u - quadraticKernel d hd v u| ≤ 2*|b-d| := by
  have hi := quadraticIntercept_abs_sub_le b d hb hd v
  have hr : 0 ≤ |b-d| := abs_nonneg _
  have hp0 : 0 ≤ (1-(u : ℝ))^2 := sq_nonneg _
  have hp1 : (1-(u : ℝ))^2 ≤ 1 := by nlinarith [u.property.1,u.property.2]
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self (b-d)) hp0
  have h2 := mul_le_mul_of_nonneg_right (neg_le_abs (b-d)) hp0
  have h3 := mul_nonneg hr (sub_nonneg.mpr hp1)
  apply abs_le.mpr
  constructor
  · have hh := clamp_shift (x := quadraticIntercept d hd v+d*(1-(u : ℝ))^2)
      (y := quadraticIntercept b hb v+b*(1-(u : ℝ))^2) (r := 2*|b-d|)
      (by positivity) (by nlinarith [(abs_le.mp hi).1])
    change -(2*|b-d|) ≤ unitClamp _ - unitClamp _
    linarith
  · have hh := clamp_shift (x := quadraticIntercept b hb v+b*(1-(u : ℝ))^2)
      (y := quadraticIntercept d hd v+d*(1-(u : ℝ))^2) (r := 2*|b-d|)
      (by positivity) (by nlinarith [(abs_le.mp hi).2])
    change unitClamp _ - unitClamp _ ≤ _
    linarith

theorem quadraticBand_xi_abs_sub_le (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    |(quadraticBand b hb).chatterjeeXi - (quadraticBand d hd).chatterjeeXi| ≤ 24*|b-d| := by
  have he (r : ℝ) (hr : 0 ≤ r) (v : I) :
      (∫ u : I, (quadraticBand r hr).conditionalCDF u v ^ 2) =
        ∫ u : I, quadraticKernel r hr v u ^ 2 :=
    integral_congr_ae ((quadraticBand_conditionalCDF r hr v).fun_comp (fun z : ℝ => z^2))
  have hs (v : I) : |(∫ u : I, (quadraticBand b hb).conditionalCDF u v ^ 2) -
      (∫ u : I, (quadraticBand d hd).conditionalCDF u v ^ 2)| ≤ 4*|b-d| := by
    rw [he,he]
    apply integral_sub_abs_le_uniform volume _ _
      (Copula.integrable_continuous_unit volume (by unfold quadraticKernel unitClamp; fun_prop))
      (Copula.integrable_continuous_unit volume (by unfold quadraticKernel unitClamp; fun_prop))
    intro u
    have hh := quadraticKernel_abs_sub_le b d hb hd v u
    have h1 : quadraticKernel b hb v u ∈ Icc (0 : ℝ) 1 := unitClamp_mem _
    have h2 : quadraticKernel d hd v u ∈ Icc (0 : ℝ) 1 := unitClamp_mem _
    rw [sq_sub_sq,abs_mul]
    have hsum : |quadraticKernel b hb v u + quadraticKernel d hd v u| ≤ 2 := by
      rw [abs_of_nonneg (by linarith [h1.1,h2.1])]
      linarith [h1.2,h2.2]
    nlinarith [mul_le_mul hh hsum (abs_nonneg _) (by positivity : 0 ≤ 2*|b-d|)]
  have hh := integral_sub_abs_le_uniform volume _ _
    (quadraticBand b hb).integrable_integral_conditionalCDF_sq
    (quadraticBand d hd).integrable_integral_conditionalCDF_sq (4*|b-d|) hs
  unfold Copula.chatterjeeXi
  have hid (x y : ℝ) : (6*x-2)-(6*y-2)=6*(x-y) := by ring
  rw [hid,abs_mul]
  norm_num
  linarith

theorem continuous_quadraticBand_xi :
    Continuous (fun b : Ici (0 : ℝ) => (quadraticBand b b.property).chatterjeeXi) := by
  apply LipschitzWith.continuous (K := 24)
  apply LipschitzWith.of_dist_le_mul
  intro b d
  simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_ofNat] using
    quadraticBand_xi_abs_sub_le b d b.property d.property

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
