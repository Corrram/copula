/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen
import Copula.Dependence.Clayton
import Copula.Dependence.ClaytonClassification
import Copula.Dependence.ClaytonTotalPositivity
import Copula.Dependence.ClaytonDensityMeasure
import Copula.TailDependence.Nelsen12
import Copula.TailDependence.Nelsen14
import Copula.TailDependence.Quadrant
import Copula.Dependence.Nelsen12
import Copula.Dependence.BB1TotalPositivity

/-! # Dependence properties at the Nelsen 12 and 14 lower endpoints

Both families equal Clayton(1) at parameter one. These results are deliberately
restricted to that endpoint; they do not establish the full parameter rows.
-/

namespace ProbabilityTheory.Copula

theorem isCI_nelsen12_one : (nelsen12 1 le_rfl).IsCI := by
  rw [nelsen12_one]
  exact isCI_clayton_positive 1 (by norm_num)

theorem isCI_nelsen14_one : (nelsen14 1 le_rfl).IsCI := by
  rw [nelsen14_one]
  exact isCI_clayton_positive 1 (by norm_num)

theorem isTP2CDF_nelsen12_one : (nelsen12 1 le_rfl).IsTP2CDF := by
  rw [nelsen12_one]
  exact isTP2CDF_clayton_positive 1 (by norm_num)

theorem isTP2CDF_nelsen14_one : (nelsen14 1 le_rfl).IsTP2CDF := by
  rw [nelsen14_one]
  exact isTP2CDF_clayton_positive 1 (by norm_num)

theorem hasMTP2Density_nelsen12_one : (nelsen12 1 le_rfl).HasMTP2Density := by
  rw [nelsen12_one]
  exact clayton_positive_density_tp2 1 (by norm_num)

theorem hasMTP2Density_nelsen14_one : (nelsen14 1 le_rfl).HasMTP2Density := by
  rw [nelsen14_one]
  exact clayton_positive_density_tp2 1 (by norm_num)

theorem not_isCD_nelsen12_one : ¬(nelsen12 1 le_rfl).IsCD := by
  rw [nelsen12_one]
  exact not_isCD_clayton_positive 1 (by norm_num)

theorem not_isCD_nelsen14_one : ¬(nelsen14 1 le_rfl).IsCD := by
  rw [nelsen14_one]
  exact not_isCD_clayton_positive 1 (by norm_num)

/-- All Nelsen 12 members are PQD: the parameter order puts them above
the positive Clayton(1) endpoint. This is weaker than the open CI row. -/
theorem isPQD_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen12 θ hθ).IsPQD := by
  intro u v
  have hbase := (isCI_nelsen12_one.isPQD) u v
  have horder := lowerOrthantLE_nelsen12 le_rfl hθ hθ
  exact hbase.trans (horder ![u, v])

/-- Nelsen 12 has a TP2 CDF for every finite admissible parameter. -/
theorem isTP2CDF_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen12 θ hθ).IsTP2CDF := by
  simpa only [nelsen12] using isTP2CDF_bb1 1 (by norm_num) θ hθ

/-- Nelsen 14 has a TP2 CDF for every finite admissible parameter. -/
theorem isTP2CDF_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen14 θ hθ).IsTP2CDF := by
  simpa only [nelsen14] using
    isTP2CDF_bb1 θ⁻¹ (inv_pos.mpr (by linarith : 0 < θ)) θ hθ

/-- Every finite Nelsen 14 copula is positively quadrant dependent. -/
theorem isPQD_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen14 θ hθ).IsPQD := by
  intro u v
  have hθpos : 0 < θ := by linarith
  have hq : -θ⁻¹ ≤ 0 := neg_nonpos.mpr (inv_nonneg.mpr hθpos.le)
  by_cases hu0 : u = 0
  · subst u
    simp
  by_cases hv0 : v = 0
  · subst v
    simpa using (nelsen14 θ hθ).cdf_nonneg ![u, 0]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  let a : ℝ := (u : ℝ) ^ (-θ⁻¹)
  let b : ℝ := (v : ℝ) ^ (-θ⁻¹)
  let x : ℝ := a - 1
  let y : ℝ := b - 1
  have ha : 1 ≤ a := by
    dsimp [a]
    simpa using Real.rpow_le_rpow_of_nonpos hu u.property.2 hq
  have hb : 1 ≤ b := by
    dsimp [b]
    simpa using Real.rpow_le_rpow_of_nonpos hv v.property.2 hq
  have hx : 0 ≤ x := sub_nonneg.mpr ha
  have hy : 0 ≤ y := sub_nonneg.mpr hb
  have hn := Real.rpow_add_rpow_le hx hy (by norm_num : (0 : ℝ) < 1) hθ
  have hnorm : (x ^ θ + y ^ θ) ^ θ⁻¹ ≤ x + y := by
    simpa only [one_div, Real.rpow_one, div_one] using hn
  have hbase : 0 < 1 + (x ^ θ + y ^ θ) ^ θ⁻¹ := by
    have hp : 0 ≤ (x ^ θ + y ^ θ) ^ θ⁻¹ :=
      Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)) _
    linarith
  have hprod : 1 + (x ^ θ + y ^ θ) ^ θ⁻¹ ≤ a * b := by
    have hxy := mul_nonneg hx hy
    dsimp [x, y] at hnorm hxy
    nlinarith
  have hp := Real.rpow_le_rpow_of_nonpos hbase hprod
    (by linarith : -θ ≤ 0)
  have hu_id : a ^ (-θ) = (u : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_mul hu.le]
    have he : (-θ⁻¹) * (-θ) = 1 := by field_simp [hθpos.ne']
    rw [he, Real.rpow_one]
  have hv_id : b ^ (-θ) = (v : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_mul hv.le]
    have he : (-θ⁻¹) * (-θ) = 1 := by field_simp [hθpos.ne']
    rw [he, Real.rpow_one]
  have hab : (a * b) ^ (-θ) = (u : ℝ) * (v : ℝ) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ a) (by positivity : 0 ≤ b),
      hu_id, hv_id]
  rw [← hab]
  rw [nelsen14_cdf_full]
  simpa only [hu0, hv0, or_self, ite_false, x, y, a, b] using hp

/-- Nelsen 12 cannot be conditionally decreasing at any finite admissible parameter:
its lower-tail coefficient is strictly positive. -/
theorem not_isCD_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen12 θ hθ).IsCD := by
  intro h
  have hzero := isNQD_hasLowerTailDependence_zero h.isNQD
  have htail := hasLowerTailDependence_nelsen12 θ hθ
  have heq := hzero.unique htail
  have hp : 0 < ((2 : ℝ) ^ θ⁻¹)⁻¹ :=
    inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  exact (ne_of_gt hp) heq.symm

/-- Nelsen 14 cannot be conditionally decreasing at any finite admissible
parameter: its lower-tail coefficient is one half. -/
theorem not_isCD_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen14 θ hθ).IsCD := by
  intro h
  have hzero := isNQD_hasLowerTailDependence_zero h.isNQD
  have htail := hasLowerTailDependence_nelsen14 θ hθ
  have heq := hzero.unique htail
  norm_num at heq

end ProbabilityTheory.Copula
