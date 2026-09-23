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
