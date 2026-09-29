/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantCriteria
import Copula.Archimedean.ConcordanceFamilies
import Copula.Families.Nelsen7
import Copula.Families.NelsenTable.N11
import Copula.Dependence.Singular
import Copula.Dependence.Examples

/-! # Quadrant dependence of Nelsen's families 7, 9, 10, 11, 13

* #7: NQD for all `θ ∈ [0, 1]`; PQD iff `θ = 1` (independence);
* #9, #10, #11: NQD, and not PQD (for #11 because the generator is non-strict);
* #13: PQD iff `θ ≥ 1`, NQD iff `θ ≤ 1`; for `θ < 1` (resp. `θ > 1`) the sign of dependence is
  witnessed by strict convexity (resp. concavity) of `x ↦ x^{1/θ}`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ### Family 13 -/

private theorem rpow_three_gt {p : ℝ} (hp : 1 < p) : 2 * (2 : ℝ) ^ p - 1 < (3 : ℝ) ^ p := by
  have h := (strictConvexOn_rpow hp).2 (mem_Ici.mpr zero_le_one : (1 : ℝ) ∈ Ici 0)
    (mem_Ici.mpr (by norm_num) : (3 : ℝ) ∈ Ici 0) (by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, Real.one_rpow] at h
  rw [show 1 / 2 * 1 + 1 / 2 * 3 = (2 : ℝ) by norm_num] at h
  linarith

private theorem rpow_three_lt {p : ℝ} (hp0 : 0 < p) (hp : p < 1) :
    (3 : ℝ) ^ p < 2 * (2 : ℝ) ^ p - 1 := by
  have h := (Real.strictConcaveOn_rpow hp0 hp).2 (mem_Ici.mpr zero_le_one : (1 : ℝ) ∈ Ici 0)
    (mem_Ici.mpr (by norm_num) : (3 : ℝ) ∈ Ici 0) (by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, Real.one_rpow] at h
  rw [show 1 / 2 * 1 + 1 / 2 * 3 = (2 : ℝ) by norm_num] at h
  linarith

/-- Nelsen's family 13 is not PQD for `0 < θ < 1`. -/
theorem not_isPQD_nelsen13 (θ : ℝ) (hθ : 0 < θ) (h1 : θ < 1) : ¬ (nelsen13 θ hθ).IsPQD := by
  have hp : 1 < θ⁻¹ := (one_lt_inv₀ hθ).mpr h1
  refine (nelsen13Generator θ hθ).not_isPQD_of_psi (x := 1) (y := 1) zero_le_one zero_le_one ?_
  show Real.exp (1 - (1 + (1 + 1)) ^ θ⁻¹) < Real.exp (1 - (1 + 1) ^ θ⁻¹) *
    Real.exp (1 - (1 + 1) ^ θ⁻¹)
  rw [← Real.exp_add, Real.exp_lt_exp]
  have := rpow_three_gt hp
  norm_num
  linarith

/-- Nelsen's family 13 is not NQD for `θ > 1`. -/
theorem not_isNQD_nelsen13 (θ : ℝ) (h1 : 1 < θ) : ¬ (nelsen13 θ (by linarith)).IsNQD := by
  have hθ : 0 < θ := by linarith
  have hp0 : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hp : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  refine (nelsen13Generator θ hθ).not_isNQD_of_psi (x := 1) (y := 1) zero_le_one zero_le_one ?_
  show Real.exp (1 - (1 + 1) ^ θ⁻¹) * Real.exp (1 - (1 + 1) ^ θ⁻¹) <
    Real.exp (1 - (1 + (1 + 1)) ^ θ⁻¹)
  rw [← Real.exp_add, Real.exp_lt_exp]
  have := rpow_three_lt hp0 hp
  norm_num
  linarith

/-- Nelsen's family 13 is PQD iff `θ ≥ 1`. -/
theorem isPQD_nelsen13_iff (θ : ℝ) (hθ : 0 < θ) : (nelsen13 θ hθ).IsPQD ↔ 1 ≤ θ := by
  constructor
  · intro h
    by_contra hc
    exact not_isPQD_nelsen13 θ hθ (not_le.mp hc) h
  · exact fun h => isPQD_nelsen13 θ h

/-- Nelsen's family 13 is NQD iff `θ ≤ 1`. -/
theorem isNQD_nelsen13_iff (θ : ℝ) (hθ : 0 < θ) : (nelsen13 θ hθ).IsNQD ↔ θ ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    exact not_isNQD_nelsen13 θ (not_le.mp hc) h
  · exact fun h => isNQD_nelsen13 θ hθ h

/-! ### Families 9 and 10 -/

/-- Nelsen's family 9 (Gumbel–Barnett) is not PQD. -/
theorem not_isPQD_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : ¬ (nelsen9 θ hθ h1).IsPQD := by
  refine (nelsen9Generator θ hθ h1).not_isPQD_of_psi (x := 1) (y := 1) zero_le_one zero_le_one ?_
  show Real.exp ((1 - Real.exp (1 + 1)) / θ) <
    Real.exp ((1 - Real.exp 1) / θ) * Real.exp ((1 - Real.exp 1) / θ)
  rw [← Real.exp_add, Real.exp_lt_exp, ← add_div, div_lt_div_iff_of_pos_right hθ,
    Real.exp_add]
  have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
  nlinarith

/-- Nelsen's family 10 is not PQD. -/
theorem not_isPQD_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : ¬ (nelsen10 θ hθ h1).IsPQD := by
  refine (nelsen10Generator θ hθ h1).not_isPQD_of_psi (x := 1) (y := 1) zero_le_one zero_le_one ?_
  show ((1 - -1) / (Real.exp (1 + 1) - -1)) ^ θ⁻¹ <
    ((1 - -1) / (Real.exp 1 - -1)) ^ θ⁻¹ * ((1 - -1) / (Real.exp 1 - -1)) ^ θ⁻¹
  simp only [sub_neg_eq_add]
  norm_num only
  have hp : 0 < θ⁻¹ := inv_pos.mpr hθ
  have h1 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  apply Real.rpow_lt_rpow (by positivity) _ hp
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e2, div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]

/-! ### Family 11 -/

/-- Nelsen's family 11 is NQD. -/
theorem isNQD_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) : (nelsen11 θ hθ h2).IsNQD := by
  refine (nelsen11Generator θ hθ h2).isNQD_of_psi fun x y hx hy => ?_
  show (2 - Real.exp (min (x + y) (Real.log 2))) ^ θ⁻¹ ≤
    (2 - Real.exp (min x (Real.log 2))) ^ θ⁻¹ * (2 - Real.exp (min y (Real.log 2))) ^ θ⁻¹
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have ha1 : 1 ≤ Real.exp (min x (Real.log 2)) := Real.one_le_exp (le_min hx hL)
  have hb1 : 1 ≤ Real.exp (min y (Real.log 2)) := Real.one_le_exp (le_min hy hL)
  have ha2 : Real.exp (min x (Real.log 2)) ≤ 2 := by
    calc _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (min_le_right _ _)
      _ = 2 := Real.exp_log two_pos
  have hb2 : Real.exp (min y (Real.log 2)) ≤ 2 := by
    calc _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (min_le_right _ _)
      _ = 2 := Real.exp_log two_pos
  set a := Real.exp (min x (Real.log 2))
  set b := Real.exp (min y (Real.log 2))
  have hc : min (a * b) 2 ≤ Real.exp (min (x + y) (Real.log 2)) := by
    rw [Real.exp_monotone.map_min, Real.exp_log two_pos]
    apply min_le_min _ le_rfl
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add (min_le_left _ _) (min_le_left _ _))
  have hpos : 0 ≤ (2 - a) * (2 - b) := mul_nonneg (by linarith) (by linarith)
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  apply Real.rpow_le_rpow (by
      have : Real.exp (min (x + y) (Real.log 2)) ≤ 2 := by
        calc _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (min_le_right _ _)
          _ = 2 := Real.exp_log two_pos
      linarith) _ (inv_nonneg.mpr hθ.le)
  rcases le_total (a * b) 2 with hab | hab
  · rw [min_eq_left hab] at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)]
  · rw [min_eq_right hab] at hc
    linarith

/-- Nelsen's family 11 is not PQD (its generator is non-strict). -/
theorem not_isPQD_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    ¬ (nelsen11 θ hθ h2).IsPQD := by
  refine BivariateGenerator.not_isPQD_of_not_isStrict _ fun h => ?_
  have := h (Real.log 2) (Real.log_nonneg one_le_two)
  rw [nelsen11Generator_toFun_of_le θ hθ h2 le_rfl] at this
  exact lt_irrefl _ this

/-! ### Family 7 -/

/-- Nelsen's family 7 is NQD for every `θ ∈ [0, 1]`. -/
theorem isNQD_nelsen7 (θ : I) : (nelsen7 θ).IsNQD := by
  intro u v
  rw [cdf_nelsen7]
  have h1 : (θ : ℝ) ≤ 1 := θ.property.2
  have hu := u.property
  have hv := v.property
  apply max_le (mul_nonneg hu.1 hv.1)
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2))]

/-- Nelsen's family 7 is not PQD for `θ < 1`. -/
theorem not_isPQD_nelsen7 (θ : I) (hθ : θ ≠ 1) : ¬ (nelsen7 θ).IsPQD := by
  intro h
  have hlt : (θ : ℝ) < 1 := lt_of_le_of_ne θ.property.2 (fun e => hθ (Subtype.ext e))
  let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have := h half half
  rw [cdf_nelsen7] at this
  have e : ((half : I) : ℝ) = 1 / 2 := rfl
  rw [e] at this
  have h0 : (0 : ℝ) ≤ θ := θ.property.1
  have hmax : max 0 ((θ : ℝ) * (1 / 2) * (1 / 2) + (1 - θ) * (1 / 2 + 1 / 2 - 1)) = θ / 4 := by
    rw [show (θ : ℝ) * (1 / 2) * (1 / 2) + (1 - θ) * (1 / 2 + 1 / 2 - 1) = θ / 4 by ring]
    exact max_eq_right (by linarith)
  rw [hmax] at this
  linarith

/-- Nelsen's family 7 is PQD iff `θ = 1`. -/
theorem isPQD_nelsen7_iff (θ : I) : (nelsen7 θ).IsPQD ↔ θ = 1 := by
  constructor
  · intro h
    by_contra hc
    exact not_isPQD_nelsen7 θ hc h
  · rintro rfl
    rw [nelsen7_one]
    exact isPQD_independence

end ProbabilityTheory.Copula
