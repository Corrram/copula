/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.TotalPositivity
import Copula.Transform.MaxProduct
import Copula.Families.MarshallOlkin
import Copula.Dependence.Examples

/-! # CDF TP2 under coordinatewise max-products -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A coordinatewise power map of the unit interval is monotone. -/
private theorem monotone_unitPower (r : I) :
    Monotone (fun u : I => unitPower u r r.property.1) := by
  intro u v huv
  exact Real.rpow_le_rpow u.property.1 huv r.property.1

/-- A max-product of TP2 copulas has a TP2 CDF. This result concerns CDFs;
it does not transfer MTP2 of Lebesgue densities. -/
theorem IsTP2CDF.maxProduct {C D : Copula 2}
    (hC : C.IsTP2CDF) (hD : D.IsTP2CDF) (a : Fin 2 → I) :
    (maxProduct C D a).IsTP2CDF := by
  let f₀ : I → I := fun u => unitPower u (a 0) (a 0).property.1
  let f₁ : I → I := fun v => unitPower v (a 1) (a 1).property.1
  let g₀ : I → I := fun u =>
    unitPower u (unitInterval.symm (a 0)) (unitInterval.symm (a 0)).property.1
  let g₁ : I → I := fun v =>
    unitPower v (unitInterval.symm (a 1)) (unitInterval.symm (a 1)).property.1
  have hf₀ : Monotone f₀ := monotone_unitPower (a 0)
  have hf₁ : Monotone f₁ := monotone_unitPower (a 1)
  have hg₀ : Monotone g₀ := monotone_unitPower (unitInterval.symm (a 0))
  have hg₁ : Monotone g₁ := monotone_unitPower (unitInterval.symm (a 1))
  have hC' : IsTP2 (fun u v : I => C.cdf ![f₀ u, f₁ v]) := by
    intro u u' v v' huu' hvv'
    exact hC (f₀ u) (f₀ u') (f₁ v) (f₁ v') (hf₀ huu') (hf₁ hvv')
  have hD' : IsTP2 (fun u v : I => D.cdf ![g₀ u, g₁ v]) := by
    intro u u' v v' huu' hvv'
    exact hD (g₀ u) (g₀ u') (g₁ v) (g₁ v') (hg₀ huu') (hg₁ hvv')
  have hmul := hC'.mul hD'
    (fun u v => C.cdf_nonneg ![f₀ u, f₁ v])
    (fun u v => D.cdf_nonneg ![g₀ u, g₁ v])
  have hCvec (u v : I) :
      (fun i : Fin 2 => unitPower (![u, v] i) (a i) (a i).property.1) =
      ![f₀ u, f₁ v] := by
    funext i
    fin_cases i <;> rfl
  have hDvec (u v : I) :
      (fun i : Fin 2 => unitPower (![u, v] i)
        (unitInterval.symm (a i)) (unitInterval.symm (a i)).property.1) =
      ![g₀ u, g₁ v] := by
    funext i
    fin_cases i <;> rfl
  intro u u' v v' huu' hvv'
  simp only [cdf_maxProduct, hCvec, hDvec]
  exact hmul u u' v v' huu' hvv'

/-- Marshall–Olkin has a TP2 CDF for all weights, including singular cases.
This differs from the separate MTP2-density classification. -/
theorem isTP2CDF_marshallOlkin (α β : I) :
    (marshallOlkin α β).IsTP2CDF := by
  simpa only [marshallOlkin, commonShock] using
    (isTP2CDF_comonotonic.maxProduct isTP2CDF_independence ![α, β])

/-- The equal-weight Cuadras–Augé subfamily has a TP2 CDF. -/
theorem isTP2CDF_cuadrasAuge (α : I) :
    (cuadrasAuge α).IsTP2CDF := by
  simpa only [cuadrasAuge] using isTP2CDF_marshallOlkin α α

end ProbabilityTheory.Copula
