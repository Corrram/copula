/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Basic
import Copula.Independence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # The exponential Archimedean generator and independence -/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The exponential generator `ψ(t) = exp(-t)`. -/
noncomputable def exponentialGenerator : BivariateGenerator where
  toFun t := Real.exp (-t)
  invFun u := -Real.log u
  nonneg t _ := (Real.exp_pos _).le
  antitone _ _ _ _ h := Real.exp_le_exp.mpr (neg_le_neg h)
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x _ y _ a b ha hb hab
    have h := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simpa only [smul_eq_mul, mul_neg, ← neg_add] using h
  inv_nonneg u _ := neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2)
  inv_antitone u v hu huv := by
    apply neg_le_neg
    exact Real.log_le_log (lt_of_le_of_ne u.property.1 (Ne.symm (by
      intro h; exact hu (Subtype.ext h)))) huv
  inv_one := by simp
  right_inv u hu := by
    simp only [neg_neg]
    exact Real.exp_log (lt_of_le_of_ne u.property.1 (Ne.symm (by
      intro h; exact hu (Subtype.ext h))))

@[simp] theorem exponentialGenerator_copula : exponentialGenerator.copula = independence 2 := by
  apply ext_cdf
  intro u
  rw [BivariateGenerator.cdf_copula, cdf_independence, Fin.prod_univ_two]
  by_cases h : u 0 = 0 ∨ u 1 = 0
  · rcases h with h | h <;> simp [h]
  · rw [BivariateGenerator.cdf, ite_eq_right h]
    change Real.exp (-(-Real.log (u 0) + -Real.log (u 1))) = _
    rw [neg_add, neg_neg, neg_neg, Real.exp_add,
      Real.exp_log (lt_of_le_of_ne (u 0).property.1 (Ne.symm (by
        intro hz; exact (not_or.mp h).1 (Subtype.ext hz)))),
      Real.exp_log (lt_of_le_of_ne (u 1).property.1 (Ne.symm (by
        intro hz; exact (not_or.mp h).2 (Subtype.ext hz))))]

end ProbabilityTheory.Copula
