/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.RandomVariable.Invariance
import Copula.RandomVariable.Ext
import Copula.Symmetry

/-!
# Symmetry of random vectors and of their copulas

Nelsen, *An Introduction to Copulas*, second edition, §2.7 (Theorems 2.7.1 and 2.7.2 in the
formulation for laws on `Fin 2 → ℝ`).

* A law `μ` is exchangeable if it is invariant under `swapCoord`. Then its coordinate laws agree
  and every Sklar copula of `μ` is exchangeable. Conversely, an exchangeable Sklar copula together
  with equal coordinate laws gives an exchangeable law.
* A law is radially symmetric about `(a, b)` if it is invariant under `reflectAbout a b`. With
  continuous marginals, every Sklar copula is then radially symmetric. Conversely, a radially
  symmetric Sklar copula together with marginals symmetric about `a` and `b` gives a radially
  symmetric law.

Laws are compared through their underlying measures in the converse directions.
-/

open MeasureTheory Set

namespace ProbabilityTheory.Copula

/-- Exchange the two coordinates of a real vector. -/
def swapCoord (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => x (![1, 0] i)

theorem measurable_swapCoord : Measurable swapCoord := by
  show Measurable (fun (x : Fin 2 → ℝ) (i : Fin 2) => x (![1, 0] i))
  exact Measurable.of_eval fun _ => measurable_pi_apply _

/-- Reflection of a plane vector through the point `(a, b)`. -/
abbrev reflectAbout (a b : ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  coordMap ![fun x => 2 * a - x, fun x => 2 * b - x]

theorem strictAnti_two_mul_sub (a : ℝ) : StrictAnti (fun x : ℝ => 2 * a - x) := by
  intro x y hxy
  show 2 * a - y < 2 * a - x
  linarith

/-- The coordinate laws of the swapped law are the swapped coordinate laws. -/
theorem marginal_map_swapCoord (μ : ProbabilityMeasure (Fin 2 → ℝ)) (i : Fin 2) :
    marginal (μ.map swapCoord) i = marginal μ (![1, 0] i) :=
  Measure.map_map (μ := μ.toMeasure) (measurable_pi_apply i) measurable_swapCoord

/-- Swapping the coordinates of a law transposes each of its Sklar copulas. -/
theorem isSklarCopula_map_swapCoord {μ : ProbabilityMeasure (Fin 2 → ℝ)} {C : Copula 2}
    (hC : IsSklarCopula μ C) : IsSklarCopula (μ.map swapCoord) C.transpose := by
  intro y
  have hσ : ∀ i : Fin 2, (![1, 0] : Fin 2 → Fin 2) (![1, 0] i) = i := by
    intro i
    fin_cases i <;> rfl
  have hy : ∀ i, marginalTransform (μ.map swapCoord) y i =
      marginalTransform μ (swapCoord y) (![1, 0] i) := by
    intro i
    show cdfUnit (marginal (μ.map swapCoord) i) (y i) =
      cdfUnit (marginal μ (![1, 0] i)) (y (![1, 0] (![1, 0] i)))
    rw [marginal_map_swapCoord, hσ]
  have hmt : marginalTransform (μ.map swapCoord) y =
      ![marginalTransform μ (swapCoord y) 1, marginalTransform μ (swapCoord y) 0] := by
    funext i
    rw [hy i]
    fin_cases i <;> rfl
  have he : ![marginalTransform μ (swapCoord y) 0, marginalTransform μ (swapCoord y) 1] =
      marginalTransform μ (swapCoord y) := by
    ext i
    fin_cases i <;> rfl
  have hpre : swapCoord ⁻¹' Iic y = Iic (swapCoord y) := by
    ext x
    constructor
    · intro h
      have h' : ∀ j, x (![1, 0] j) ≤ y j := h
      show ∀ i, x i ≤ y (![1, 0] i)
      intro i
      fin_cases i
      · exact h' 1
      · exact h' 0
    · intro h
      have h' : ∀ i, x i ≤ y (![1, 0] i) := h
      show ∀ j, x (![1, 0] j) ≤ y j
      intro j
      fin_cases j
      · exact h' 1
      · exact h' 0
  rw [hmt, cdf_transpose, he, hC (swapCoord y)]
  change _ = (μ.toMeasure.map swapCoord).real (Iic y)
  rw [map_measureReal_apply measurable_swapCoord measurableSet_Iic, hpre]

/-- An exchangeable random vector has identical coordinate laws. -/
theorem marginal_zero_eq_one_of_map_swapCoord_eq {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (h : μ.map swapCoord = μ) : marginal μ 0 = marginal μ 1 := by
  have h0 := marginal_map_swapCoord μ 0
  rw [h] at h0
  exact h0

/-- **Nelsen, §2.7 (exchangeable random vectors).** Every Sklar copula of an exchangeable law with
continuous marginals is exchangeable. -/
theorem isExchangeable_of_map_swapCoord_eq {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) (h : μ.map swapCoord = μ) : C.IsExchangeable := by
  have h1 := isSklarCopula_map_swapCoord hC
  rw [h] at h1
  exact h1.unique hc hC

/-- An exchangeable Sklar copula and equal coordinate laws give an exchangeable law. -/
theorem map_swapCoord_eq_of_isExchangeable {μ : ProbabilityMeasure (Fin 2 → ℝ)} {C : Copula 2}
    (hC : IsSklarCopula μ C) (hCs : C.IsExchangeable) (hm : marginal μ 0 = marginal μ 1) :
    μ.toMeasure.map swapCoord = μ.toMeasure := by
  have hCs' : C.transpose = C := hCs
  have h1 : IsSklarCopula (μ.map swapCoord) C := by
    have h := isSklarCopula_map_swapCoord hC
    rwa [hCs'] at h
  have hmarg : ∀ i, marginal (μ.map swapCoord) i = marginal μ i := by
    intro i
    rw [marginal_map_swapCoord]
    fin_cases i
    · exact hm.symm
    · exact hm
  have hmt : marginalTransform (μ.map swapCoord) = marginalTransform μ := by
    funext x i
    show cdfUnit (marginal (μ.map swapCoord) i) (x i) = cdfUnit (marginal μ i) (x i)
    rw [hmarg i]
  refine ext_real_of_Iic fun x => ?_
  have h2 := h1 x
  rw [hmt] at h2
  exact h2.symm.trans (hC x)

/-- **Nelsen, §2.7 (radially symmetric random vectors).** Every Sklar copula of a law with
continuous marginals that is radially symmetric about `(a, b)` is radially symmetric. -/
theorem isRadiallySymmetric_of_map_reflectAbout_eq {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) {a b : ℝ} (h : μ.map (reflectAbout a b) = μ) :
    C.IsRadiallySymmetric := by
  have h1 : IsSklarCopula (μ.map (reflectAbout a b)) C.survivalCopula :=
    isSklarCopula_map_strictAnti_two hc hC (strictAnti_two_mul_sub a) (strictAnti_two_mul_sub b)
  rw [h] at h1
  exact h1.unique hc hC

/-- A radially symmetric Sklar copula and coordinate laws symmetric about `a` and `b` give a law
that is radially symmetric about `(a, b)`. -/
theorem map_reflectAbout_eq_of_isRadiallySymmetric {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) (hCs : C.IsRadiallySymmetric) {a b : ℝ}
    (hm0 : (marginal μ 0).map (fun x => 2 * a - x) = marginal μ 0)
    (hm1 : (marginal μ 1).map (fun x => 2 * b - x) = marginal μ 1) :
    μ.toMeasure.map (reflectAbout a b) = μ.toMeasure := by
  have hCs' : C.survivalCopula = C := hCs
  have hα := strictAnti_two_mul_sub a
  have hβ := strictAnti_two_mul_sub b
  have h1 : IsSklarCopula (μ.map (reflectAbout a b)) C := by
    have h := isSklarCopula_map_strictAnti_two hc hC hα hβ
    rwa [hCs'] at h
  have hf : ∀ i, Measurable (![fun x : ℝ => 2 * a - x, fun x : ℝ => 2 * b - x] i) :=
    Fin.forall_fin_two.mpr ⟨hα.antitone.measurable, hβ.antitone.measurable⟩
  have hmarg : ∀ i, marginal (μ.map (reflectAbout a b)) i = marginal μ i := by
    intro i
    refine (marginal_map_coordMap μ hf i).trans ?_
    fin_cases i
    · exact hm0
    · exact hm1
  have hmt : marginalTransform (μ.map (reflectAbout a b)) = marginalTransform μ := by
    funext x i
    show cdfUnit (marginal (μ.map (reflectAbout a b)) i) (x i) = cdfUnit (marginal μ i) (x i)
    rw [hmarg i]
  refine ext_real_of_Iic fun x => ?_
  have h2 := h1 x
  rw [hmt] at h2
  exact h2.symm.trans (hC x)

end ProbabilityTheory.Copula
