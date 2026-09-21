/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Basic

/-! # Finite patchworks with uniform marginals

Nonnegative weighted local copulas remain two-increasing after monotone
coordinate changes. The two weighted marginal identities are exactly what
is needed to obtain a copula. This is shared by finite ordinal sums,
checkerboards, check-min copulas and shuffles.
-/

open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {ι : Type*} [Fintype ι]

/-- Finite local copulas with monotone coordinates and uniform weighted marginals. -/
structure PatchworkData (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  first : ι → I → I
  second : ι → I → I
  first_mono : ∀ i, Monotone (first i)
  second_mono : ∀ i, Monotone (second i)
  first_zero : ∀ i, first i 0 = 0
  second_zero : ∀ i, second i 0 = 0
  first_one : ∀ i, first i 1 = 1
  second_one : ∀ i, second i 1 = 1
  first_margin : ∀ u, ∑ i, weight i * (first i u : ℝ) = u
  second_margin : ∀ v, ∑ i, weight i * (second i v : ℝ) = v

namespace PatchworkData

/-- Weighted CDF of the local copulas. -/
noncomputable def cdf (P : PatchworkData ι) (C : ι → Copula 2) (u v : I) : ℝ :=
  ∑ i, P.weight i * (C i).cdf ![P.first i u, P.second i v]

theorem isClassical (P : PatchworkData ι) (C : ι → Copula 2) :
    IsClassical (fun u : Fin 2 → I => P.cdf C (u 0) (u 1)) := by
  apply IsClassical.ofBivariate
  · intro v; simp [cdf, P.first_zero]
  · intro u; simp [cdf, P.second_zero]
  · intro v; simpa [cdf, P.first_one] using P.second_margin v
  · intro u; simpa [cdf, P.second_one] using P.first_margin u
  · intro a b c d hab hcd
    have h (i : ι) := (C i).rectangleIncrement_cdf_nonneg
      ![P.first i a, P.second i c] ![P.first i b, P.second i d] (by
        intro j; fin_cases j
        · exact P.first_mono i hab
        · exact P.second_mono i hcd)
    simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hs := Finset.sum_nonneg (s := Finset.univ)
      (fun i _ => mul_nonneg (P.nonneg i) (h i))
    simpa only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, cdf] using hs

/-- Assemble a finite patchwork as a probability-measure copula. -/
noncomputable def copula (P : PatchworkData ι) (C : ι → Copula 2) : Copula 2 :=
  ofClassical _ (P.isClassical C)

@[simp] theorem cdf_copula (P : PatchworkData ι) (C : ι → Copula 2) (u : Fin 2 → I) :
    (P.copula C).cdf u = P.cdf C (u 0) (u 1) :=
  congrFun (cdf_ofClassical _ _) u

/-- Pointwise order of the local copulas passes to the patchwork. -/
theorem cdf_mono (P : PatchworkData ι) (C D : ι → Copula 2)
    (h : ∀ i u, (C i).cdf u ≤ (D i).cdf u) (u v : I) :
    P.cdf C u v ≤ P.cdf D u v :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i _) (P.nonneg i)

end PatchworkData

end ProbabilityTheory.Copula
