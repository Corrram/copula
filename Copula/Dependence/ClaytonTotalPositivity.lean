/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.ClaytonClassification
import Copula.Dependence.TotalPositivity
import Copula.Dependence.Frechet

/-! # CDF total positivity and a singular density endpoint for Clayton copulas

This classifies `IsTP2CDF`, a property distinct from MTP2 of a density. The W endpoint also has no Lebesgue MTP2 density.
-/

open Real
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Every positive bivariate Clayton copula has a TP2 CDF. -/
theorem isTP2CDF_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).IsTP2CDF := by
  intro a b c d hab hcd
  change (clayton 2 θ hθ).cdf ![a, d] * (clayton 2 θ hθ).cdf ![b, c] ≤
    (clayton 2 θ hθ).cdf ![a, c] * (clayton 2 θ hθ).cdf ![b, d]
  by_cases ha0 : a = 0
  · subst a
    simp
  by_cases hc0 : c = 0
  · subst c
    have hzero (u : I) : (clayton 2 θ hθ).cdf ![u, 0] = 0 :=
      (clayton 2 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
    simp [hzero]
  have ha : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1
    (Ne.symm (fun h => ha0 (Subtype.ext h)))
  have hb : 0 < (b : ℝ) := lt_of_lt_of_le ha hab
  have hc : 0 < (c : ℝ) := lt_of_le_of_ne c.property.1
    (Ne.symm (fun h => hc0 (Subtype.ext h)))
  have hd : 0 < (d : ℝ) := lt_of_lt_of_le hc hcd
  let x := (a : ℝ) ^ (-θ)
  let X := (b : ℝ) ^ (-θ)
  let y := (c : ℝ) ^ (-θ)
  let Y := (d : ℝ) ^ (-θ)
  have hx : X ≤ x := Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
  have hy : Y ≤ y := Real.rpow_le_rpow_of_nonpos hc hcd (by linarith)
  have hx1 : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hb b.property.2 (by linarith)
  have hy1 : 1 ≤ Y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hd d.property.2 (by linarith)
  let A := x + y - 1
  let B := x + Y - 1
  let C := X + y - 1
  let D := X + Y - 1
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hC : 0 < C := by dsimp [C]; linarith
  have hD : 0 < D := by dsimp [D]; linarith
  have hprod : A * D ≤ B * C := by
    dsimp [A, B, C, D]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hq : -1 / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hθ.le
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hA hD) hprod hq
  rw [Real.mul_rpow hB.le hC.le, Real.mul_rpow hA.le hD.le] at hpow
  rw [cdf_clayton_two_pos θ hθ a d ha hd,
    cdf_clayton_two_pos θ hθ b c hb hc,
    cdf_clayton_two_pos θ hθ a c ha hc,
    cdf_clayton_two_pos θ hθ b d hb hd]
  exact hpow
/-- A negative Clayton copula does not have a TP2 CDF. -/
theorem not_isTP2CDF_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    ¬(claytonNegative θ hθ hn).IsTP2CDF := by
  intro h
  exact not_isPQD_clayton_negative θ hθ hn h.isPQD

/-- The negative endpoint is W and therefore has no Lebesgue MTP2 density. -/
theorem not_hasMTP2Density_clayton_negative_one :
    ¬(claytonNegative (-1) le_rfl (by norm_num)).HasMTP2Density := by
  rw [claytonNegative_neg_one, ← mardia_neg_one]
  intro h
  have hz := (mardia_density_tp2_iff (-1) (by norm_num)).mp h
  norm_num at hz

end ProbabilityTheory.Copula
