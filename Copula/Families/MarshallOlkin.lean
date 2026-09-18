/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.Basic

/-! # Marshall–Olkin and Cuadras–Augé copulas

The two-parameter Marshall–Olkin CDF is
`min(u^α,v^β) * u^(1-α) * v^(1-β)`, for `α,β ∈ [0,1]`.
This includes the singular component and all parameter endpoints.
The common-shock construction also works in every finite dimension.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem iInf_two (u : Fin 2 → I) : (⨅ i, u i) = min (u 0) (u 1) := by
  apply le_antisymm (le_min (iInf_le u 0) (iInf_le u 1))
  apply le_iInf
  intro i
  fin_cases i
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- A common shock together with independent coordinate-specific shocks. -/
noncomputable def commonShock (d : ℕ) (a : Fin d → I) : Copula d :=
  maxProduct (comonotonic d) (independence d) a

theorem isExtremeValue_commonShock (d : ℕ) (a : Fin d → I) :
    IsExtremeValue (commonShock d a) :=
  (isExtremeValue_comonotonic d).maxProduct (isExtremeValue_independence d) a

/-- The bivariate Marshall–Olkin copula. -/
noncomputable def marshallOlkin (α β : I) : Copula 2 := commonShock 2 ![α, β]

theorem cdf_marshallOlkin (α β : I) (u : Fin 2 → I) :
    (marshallOlkin α β).cdf u =
      min ((u 0 : ℝ) ^ (α : ℝ)) ((u 1 : ℝ) ^ (β : ℝ)) *
        ((u 0 : ℝ) ^ (1 - (α : ℝ)) * (u 1 : ℝ) ^ (1 - (β : ℝ))) := by
  rw [marshallOlkin, commonShock, cdf_maxProduct, cdf_comonotonic, cdf_independence]
  simp [iInf_two, Fin.prod_univ_two, unitInterval.coe_symm_eq]

theorem isExtremeValue_marshallOlkin (α β : I) : IsExtremeValue (marshallOlkin α β) :=
  isExtremeValue_commonShock _ _

/-- The Cuadras–Augé family is the equal-weight Marshall–Olkin subfamily. -/
noncomputable def cuadrasAuge (α : I) : Copula 2 := marshallOlkin α α

theorem isExtremeValue_cuadrasAuge (α : I) : IsExtremeValue (cuadrasAuge α) :=
  isExtremeValue_marshallOlkin _ _

@[simp] theorem marshallOlkin_zero_zero : marshallOlkin 0 0 = independence 2 := by
  apply ext_cdf
  intro u
  simp [cdf_marshallOlkin, cdf_independence, Fin.prod_univ_two]

@[simp] theorem marshallOlkin_one_one : marshallOlkin 1 1 = comonotonic 2 := by
  apply ext_cdf
  intro u
  simp [cdf_marshallOlkin, cdf_comonotonic, iInf_two]

end ProbabilityTheory.Copula
