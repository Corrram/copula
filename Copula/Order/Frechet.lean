/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Orthant
import Copula.Families.Frechet

/-! # Parameter ordering of Fréchet mixtures

Increasing the weight of `M` increases the copula; increasing the weight of
`W` decreases it. This corrects the second direction printed in Ansari–Rockel,
Table 5 and Appendix A.4.2.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem lowerOrthantLE_frechet {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' + b' ≤ 1)
    (haa : a ≤ a') (hbb : b' ≤ b) :
    (frechet a b ha hb hab).LowerOrthantLE (frechet a' b' ha' hb' hab') := by
  intro u
  rw [cdf_frechet, cdf_frechet]
  have hm := mul_nonneg (sub_nonneg.mpr haa)
    (sub_nonneg.mpr (cdf_le_comonotonic (independence 2) u))
  have hw := mul_nonneg (sub_nonneg.mpr hbb)
    (sub_nonneg.mpr (cdf_countermonotonic_le (independence 2) u))
  nlinarith

/-- The reverse direction in the lower-bound weight already fails at the
two parameter endpoints, as witnessed by the center of the square. -/
theorem not_lowerOrthantLE_independence_countermonotonic :
    ¬ (independence 2).LowerOrthantLE countermonotonic := by
  intro h
  have ht := h ![⟨1 / 2, by constructor <;> norm_num⟩, ⟨1 / 2, by constructor <;> norm_num⟩]
  norm_num [cdf_independence, Fin.prod_univ_two, cdf_countermonotonic] at ht

end ProbabilityTheory.Copula
