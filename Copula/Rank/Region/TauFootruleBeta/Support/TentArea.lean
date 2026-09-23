import Copula.Rank.Region.TauFootruleBeta.Support.TentIntegral

/-! # Exact area of a median tent -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support

private theorem integral_left_linear (a b : ℝ) :
    (∫ v in a..b, (v - a)) = (b - a) ^ 2 / 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := fun v : ℝ => (v - a) ^ 2 / 2)
    (f' := fun v => (v - a)) (fun v _ => by
      convert! (((hasDerivAt_id v).sub_const a).pow 2).div_const 2 using 1
      simp only [id_eq]
      ring)
    ((show Continuous (fun v : ℝ => (v - a)) by fun_prop).intervalIntegrable a b)
  simpa using h

private theorem integral_right_linear (a b : ℝ) :
    (∫ v in a..b, (b - v)) = (b - a) ^ 2 / 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := fun v : ℝ => -(b - v) ^ 2 / 2)
    (f' := fun v => (b - v)) (fun v _ => by
      convert! ((((hasDerivAt_id v).const_sub b).pow 2).neg).div_const 2 using 1
      simp only [id_eq]
      ring)
    ((show Continuous (fun v : ℝ => (b - v)) by fun_prop).intervalIntegrable a b)
  simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, zero_sub, neg_div, neg_neg] using h

/-- Includes the degenerate tent `r=0` and the full-width tent `r=1`. -/
theorem integral_medianTent {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (∫ v : I, medianTent r v) = r ^ 2 / 4 := by
  let a := (1 - r) / 2
  let b := (1 + r) / 2
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha : a ≤ 1 / 2 := by dsimp [a]; linarith
  have hb : 1 / 2 ≤ b := by dsimp [b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  let f := fun v : ℝ => medianTent r v
  have hf : Continuous f := continuous_medianTent r
  have h0 : (∫ v in 0..a, f v) = 0 := by
    calc
      _ = ∫ _ in 0..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le ha0] at hv
        dsimp [f, medianTent]
        rw [abs_of_nonpos (by linarith [hv.2]), max_eq_left (by dsimp [a] at hv; linarith [hv.1, hv.2])]
      _ = 0 := by simp
  have hL : (∫ v in a..(1 / 2), f v) = ((1 / 2) - a) ^ 2 / 2 := by
    rw [← integral_left_linear]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ha] at hv
    dsimp [f, medianTent]
    rw [abs_of_nonpos (by linarith [hv.2]), max_eq_right (by dsimp [a] at hv; linarith [hv.1, hv.2])]
    dsimp [a]
    ring
  have hR : (∫ v in (1 / 2)..b, f v) = (b - (1 / 2)) ^ 2 / 2 := by
    rw [← integral_right_linear]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hb] at hv
    dsimp [f, medianTent]
    rw [abs_of_nonneg (by linarith [hv.1]), max_eq_right (by dsimp [b] at hv; linarith [hv.1, hv.2])]
    dsimp [b]
    ring
  have h1 : (∫ v in b..1, f v) = 0 := by
    calc
      _ = ∫ _ in b..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hb1] at hv
        dsimp [f, medianTent]
        rw [abs_of_nonneg (by linarith [hv.1]), max_eq_left (by dsimp [b] at hv; linarith [hv.1, hv.2])]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (0 : ℝ) a)
    (hf.intervalIntegrable (μ := volume) a (1 / 2 : ℝ))
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (0 : ℝ) (1 / 2 : ℝ))
    (hf.intervalIntegrable (μ := volume) (1 / 2 : ℝ) b)
  have hsplit'' := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (0 : ℝ) b)
    (hf.intervalIntegrable (μ := volume) b (1 : ℝ))
  rw [ProbabilityTheory.Copula.integral_unitInterval (fun v => medianTent r v)]
  change (∫ v in 0..1, f v) = _
  rw [← hsplit'', ← hsplit', ← hsplit, h0, hL, hR, h1]
  dsimp [a, b]
  ring

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
