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

end ProbabilityTheory.Copula
