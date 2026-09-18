/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical.Characterization

/-! # A two-variable interface to the classical construction -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Check a bivariate formula using its four boundary identities and rectangle inequality. -/
theorem IsClassical.ofBivariate (F : I → I → ℝ)
    (hz₁ : ∀ v, F 0 v = 0) (hz₂ : ∀ u, F u 0 = 0)
    (ho₁ : ∀ v, F 1 v = v) (ho₂ : ∀ u, F u 1 = u)
    (hinc : ∀ a b c e, a ≤ b → c ≤ e → 0 ≤ F b e - F a e - F b c + F a c) :
    IsClassical (fun u : Fin 2 → I => F (u 0) (u 1)) where
  normalized := ho₁ 1
  grounded u i hi := by
    fin_cases i
    · change u 0 = 0 at hi
      rw [hi, hz₁]
    · change u 1 = 0 at hi
      rw [hi, hz₂]
  marginal i t := by
    fin_cases i <;> simp [ho₁, ho₂]
  increasing a b hab := by
    rw [rectangleIncrement_two]
    simpa using hinc (a 0) (b 0) (a 1) (b 1) (hab 0) (hab 1)

end ProbabilityTheory.Copula
