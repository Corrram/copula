/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Theory
import Copula.Diagonal

/-! # Diagonal sections of bivariate Archimedean copulas

For `C(u, v) = ψ(φ(u) + φ(v))` the diagonal section is `δ(t) = ψ(2 φ(t))`
(Nelsen, *An Introduction to Copulas*, second edition, Section 4.1 and
Table 4.1). Since `C(t, t) < t` on `(0, 1)`, no bivariate Archimedean copula
is the upper Fréchet bound `M`.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The diagonal of the copula of a generator is its `cdf` on the diagonal. -/
theorem BivariateGenerator.diagonal_eq_cdf (g : BivariateGenerator) (t : I) :
    g.copula.diagonal t = g.cdf t t := by
  have h : g.copula.cdf ![t, t] = g.cdf (![t, t] 0) (![t, t] 1) :=
    BivariateGenerator.cdf_copula g ![t, t]
  have h0 : (![t, t] : Fin 2 → I) 0 = t := by simp
  have h1 : (![t, t] : Fin 2 → I) 1 = t := by simp
  rw [h0, h1] at h
  exact h

/-- The diagonal section formula `δ(t) = ψ(2 φ(t))` for `t > 0`. -/
theorem BivariateGenerator.diagonal_copula (g : BivariateGenerator) {t : I} (ht : t ≠ 0) :
    g.copula.diagonal t = g.toFun (2 * g.invFun t) := by
  rw [g.diagonal_eq_cdf t, BivariateGenerator.cdf, ite_or_of_not (ht) (ht) _ _, two_mul]

/-- `δ(t) < t` on the open unit interval. -/
theorem BivariateGenerator.diagonal_lt (g : BivariateGenerator) {t : I} (h0 : t ≠ 0)
    (h1 : t ≠ 1) : g.copula.diagonal t < (t : ℝ) := by
  rw [g.diagonal_eq_cdf t]
  exact g.cdf_lt_left h0 h0 h1

/-- The diagonal of a bivariate Archimedean copula lies strictly below the identity
on `(0, 1)`. -/
theorem IsArchimedean.diagonal_lt {C : Copula 2} (hC : IsArchimedean C) {t : I}
    (h0 : t ≠ 0) (h1 : t ≠ 1) : C.diagonal t < (t : ℝ) := by
  obtain ⟨g, hg⟩ := hC.exists_generator_copula
  rw [hg]
  exact g.diagonal_lt h0 h1

private noncomputable def archMid : I := ⟨1 / 2, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩

private theorem archMid_val : (archMid : ℝ) = 1 / 2 := rfl

/-- No bivariate Archimedean copula is the upper Fréchet bound. -/
theorem IsArchimedean.ne_comonotonic {C : Copula 2} (hC : IsArchimedean C) :
    C ≠ comonotonic 2 := by
  intro h
  have hd := (diagonal_eq_id_iff C).mpr h archMid
  have hh : (0 : ℝ) < (archMid : ℝ) := by rw [archMid_val]; norm_num
  have hh1 : (archMid : ℝ) < 1 := by rw [archMid_val]; norm_num
  have h0 : archMid ≠ 0 := by
    intro h'
    exact hh.ne' (congrArg (fun w : I => (w : ℝ)) h')
  have h1 : archMid ≠ 1 := by
    intro h'
    exact hh1.ne (congrArg (fun w : I => (w : ℝ)) h')
  exact (hC.diagonal_lt h0 h1).ne hd

end ProbabilityTheory.Copula
