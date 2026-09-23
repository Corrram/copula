import Copula.Rank.Region.XiRho.Paper.BandCoefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Equation (5): verification of the explicit inverse boundary parameter -/

open ProbabilityTheory

namespace ProbabilityTheory.Copula.RankRegion.XiRho

noncomputable def smallXiParameter (x : ℝ) : ℝ :=
  Real.sqrt (6 * x) / (2 * Real.cos (Real.arccos (-3 * Real.sqrt (6 * x) / 5) / 3))

noncomputable def largeXiParameter (x : ℝ) : ℝ :=
  (5 + Real.sqrt (5 * (6 * x - 1))) / (10 * (1 - x))

/-- The trigonometric cubic inverse lies in (0,1] and has exactly the requested xi. -/
theorem smallXiParameter_inverse {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 3 / 10) :
    0 < smallXiParameter x ∧ smallXiParameter x ≤ 1 ∧ bandXi (smallXiParameter x) = x := by
  let a := Real.sqrt (6 * x)
  let c := Real.cos (Real.arccos (-3 * a / 5) / 3)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hasq : a ^ 2 = 6 * x := Real.sq_sqrt (by positivity)
  have halt : a < 3 / 2 := by nlinarith
  have hz : -1 < -3 * a / 5 := by linarith
  have hc : 1 / 2 < c := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.arccos (-3 * a / 5) / 3 by exact div_nonneg (Real.arccos_nonneg _) (by norm_num))
      (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos])
      (show Real.arccos (-3 * a / 5) / 3 < Real.pi / 3 by linarith [Real.arccos_lt_pi.mpr hz])
    rwa [Real.cos_pi_div_three] at h
  have hcos : 4 * c ^ 3 - 3 * c = -3 * a / 5 := by
    have h := Real.cos_three_mul (Real.arccos (-3 * a / 5) / 3)
    rw [show 3 * (Real.arccos (-3 * a / 5) / 3) = Real.arccos (-3 * a / 5) by ring,
      Real.cos_arccos hz.le (by linarith : -3 * a / 5 ≤ 1)] at h
    exact h.symm
  have hp : smallXiParameter x = a / (2 * c) := rfl
  have hbpos : 0 < smallXiParameter x := by rw [hp]; exact div_pos ha (by linarith)
  have hblt : smallXiParameter x < 3 / 2 := by
    rw [hp]
    apply (div_lt_iff₀ (by linarith : 0 < 2 * c)).mpr
    nlinarith
  have hinv : (smallXiParameter x) ^ 2 / 2 - (smallXiParameter x) ^ 3 / 5 = x := by
    rw [hp, show x = a ^ 2 / 6 by linarith]
    field_simp
    nlinarith only [hcos]
  have hb1 : smallXiParameter x ≤ 1 := by
    by_contra h
    have hgt : 1 < smallXiParameter x := lt_of_not_ge h
    have hfactor : 0 < -2 * (smallXiParameter x) ^ 2 + 3 * smallXiParameter x + 3 := by
      have hh := mul_pos hbpos (show 0 < 3 - 2 * smallXiParameter x by linarith)
      nlinarith only [hh]
    have hprod := mul_pos (sub_pos.mpr hgt) hfactor
    nlinarith only [hprod, hinv, hx1]
  refine ⟨hbpos, hb1, ?_⟩
  rw [bandXi, ite_eq_left hb1]
  exact hinv

/-- The radical quadratic inverse lies above 1 and has exactly the requested xi. -/
theorem largeXiParameter_inverse {x : ℝ} (hx : 3 / 10 < x) (hx1 : x < 1) :
    1 < largeXiParameter x ∧ bandXi (largeXiParameter x) = x := by
  let s := Real.sqrt (5 * (6 * x - 1))
  have hs : s ^ 2 = 5 * (6 * x - 1) := Real.sq_sqrt (by linarith)
  have hsn : 0 ≤ s := Real.sqrt_nonneg _
  have hslo : 2 < s := by nlinarith
  have hshi : s < 5 := by nlinarith
  have he : largeXiParameter x = 3 / (5 - s) := by
    unfold largeXiParameter
    change (5 + s) / (10 * (1 - x)) = 3 / (5 - s)
    apply (div_eq_div_iff (by linarith : 10 * (1 - x) ≠ 0) (by linarith : 5 - s ≠ 0)).mpr
    nlinarith only [hs]
  have hb : 1 < largeXiParameter x := by
    rw [he]
    apply (lt_div_iff₀ (by linarith : 0 < 5 - s)).mpr
    linarith
  refine ⟨hb, ?_⟩
  rw [bandXi, ite_eq_right (not_le.mpr hb), he]
  have hne : 5 - s ≠ 0 := by linarith
  field_simp
  nlinarith only [hs]

/-- Exactly the b_x displayed in equation (5). -/
noncomputable def boundaryParameter (x : ℝ) : ℝ :=
  if x ≤ 3 / 10 then smallXiParameter x else largeXiParameter x

theorem boundaryParameter_inverse {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    0 < boundaryParameter x ∧ bandXi (boundaryParameter x) = x := by
  unfold boundaryParameter
  split_ifs with h
  · have hh := smallXiParameter_inverse hx h
    exact ⟨hh.1, hh.2.2⟩
  · have hh := largeXiParameter_inverse (lt_of_not_ge h) hx1
    exact ⟨by linarith [hh.1], hh.2⟩

end ProbabilityTheory.Copula.RankRegion.XiRho
