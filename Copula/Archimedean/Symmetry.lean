/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Basic
import Copula.Symmetry

/-! # Exchangeability of bivariate Archimedean copulas -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem BivariateGenerator.isExchangeable (g : BivariateGenerator) :
    g.copula.IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simpa only [BivariateGenerator.cdf_copula, Matrix.cons_val_zero, Matrix.cons_val_one]
    using g.cdf_comm u v

theorem IsArchimedean.isExchangeable {C : Copula 2} (h : C.IsArchimedean) :
    C.IsExchangeable := by
  obtain ⟨g, hg⟩ := h
  have he : C = g.copula := by
    apply ext_cdf
    intro u
    by_cases hu : ∀ i, u i ≠ 0
    · rw [hg u hu, g.hasArchimedeanGenerator u hu]
    · push Not at hu
      obtain ⟨i, hi⟩ := hu
      rw [cdf_eq_zero_of_coord_eq_zero _ _ i hi, cdf_eq_zero_of_coord_eq_zero _ _ i hi]
  rw [he]
  exact g.isExchangeable

end ProbabilityTheory.Copula
