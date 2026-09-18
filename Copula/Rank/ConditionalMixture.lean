/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ConditionalCDF
import Copula.Mixture

/-! # Conditional CDFs of mixtures

Uniform first marginals make the conditional mixture weights constant.
All identities are almost everywhere in the conditioning coordinate, for
each threshold separately, and include singular copulas and zero weights.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem conditionalCDF_finiteMixture {n : ℕ} (C : Fin n → Copula 2) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (v : I) :
    (fun u => (finiteMixture C w hw hsum).conditionalCDF u v) =ᵐ[volume]
      fun u => ∑ j, w j * (C j).conditionalCDF u v := by
  apply conditionalCDF_ae_eq_of_integral
  · exact integrable_finsetSum _ (fun j _ => ((C j).integrable_conditionalCDF v).const_mul _)
  · intro u
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) ((C j).conditionalCDF_nonneg u v))
  · intro u
    rw [integral_finsetSum _ (fun j _ => (((C j).integrable_conditionalCDF v).const_mul _).integrableOn)]
    simp_rw [integral_const_mul, ← cdf_eq_integral_conditionalCDF]
    exact (cdf_finiteMixture C w hw hsum _).symm

theorem conditionalCDF_mix (C D : Copula 2) (a v : I) :
    (fun u => (C.mix D a).conditionalCDF u v) =ᵐ[volume]
      fun u => (a : ℝ) * C.conditionalCDF u v + (1 - (a : ℝ)) * D.conditionalCDF u v := by
  simpa only [mix, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    conditionalCDF_finiteMixture ![C, D] ![(a : ℝ), 1 - (a : ℝ)] _ _ v

theorem conditionalCDF_independence (v : I) :
    (fun u => (independence 2).conditionalCDF u v) =ᵐ[volume] fun _ => (v : ℝ) := by
  filter_upwards [conditionalKernel_independence] with u hu
  simp [conditionalCDF, hu, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal v.property.1]

end ProbabilityTheory.Copula
