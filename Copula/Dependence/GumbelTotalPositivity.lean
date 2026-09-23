/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.BB1TotalPositivity
import Copula.Families.Gumbel
import Copula.Dependence.MaxProductTotalPositivity

/-! # Gumbel CDF total positivity from log-convexity -/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The Gumbel–Hougaard CDF is TP2 for every finite θ ≥ 1.
This does not assert an MTP2 Lebesgue density. -/
theorem isTP2CDF_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).IsTP2CDF := by
  let g := gumbelGenerator θ hθ
  have hα0 : 0 ≤ θ⁻¹ := inv_nonneg.mpr (by linarith)
  have hα1 : θ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ
  have hconv : ConvexOn ℝ (Ici 0) (fun t => Real.log (g.toFun t)) := by
    apply (Real.concaveOn_rpow hα0 hα1).neg.congr
    intro t ht
    change -(t ^ θ⁻¹) = Real.log (Real.exp (-(t ^ θ⁻¹)))
    rw [Real.log_exp]
  have hpos : ∀ t, 0 ≤ t → 0 < g.toFun t := by
    intro t ht
    change 0 < Real.exp (-(t ^ θ⁻¹))
    positivity
  change g.copula.IsTP2CDF
  exact g.isTP2CDF_of_logConvex hpos hconv

/-- Every Tawn copula has a TP2 CDF, including zero and unit weights.
This does not assert an MTP2 Lebesgue density. -/
theorem isTP2CDF_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (tawn θ hθ α β).IsTP2CDF := by
  simpa only [tawn] using
    (isTP2CDF_gumbel θ hθ).maxProduct isTP2CDF_independence ![α, β]

end ProbabilityTheory.Copula
