/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Rank
import Copula.CDF.Continuity
import Copula.CDF.Extensionality
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Strict concordance monotonicity of Kendall's tau under full support

For bivariate copulas `C ≤ D` (pointwise, `LowerOrthantLE`) the difference of Kendall's taus
splits as (`LowerOrthantLE.kendallTau_sub_eq`)

`τ(D) - τ(C) = 4 (∫ (D - C) dD + ∫ (D - C) dC)`,

using the symmetry `∫ C dD = ∫ D dC` of the concordance integral (`integral_cdf_swap`; Nelsen
2006, Thm. 5.1.1/Cor. 5.1.2). Both integrands are nonnegative and continuous, so if one of
the two copulas has *full support* (its measure charges every nonempty open set) and
`C ≠ D`, then `τ(C) < τ(D)` (`LowerOrthantLE.kendallTau_lt_of_isOpenPosMeasure_right`,
`..._left`). No claim is made for arbitrary comparable copulas.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The difference of Kendall's taus as two concordance integrals of `D - C`. -/
theorem kendallTau_sub_eq (C D : Copula 2) :
    D.kendallTau - C.kendallTau =
      4 * ((∫ x, (D.cdf x - C.cdf x) ∂D.toMeasure) + ∫ x, (D.cdf x - C.cdf x) ∂C.toMeasure) := by
  rw [integral_sub (D.integrable_cdf _) (C.integrable_cdf _),
    integral_sub (D.integrable_cdf _) (C.integrable_cdf _), integral_cdf_swap C D]
  unfold kendallTau
  ring

private theorem integral_cdf_sub_pos {C D : Copula 2} (h : C.LowerOrthantLE D) (hne : C ≠ D)
    (μ : Measure (Fin 2 → I)) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] :
    0 < ∫ x, (D.cdf x - C.cdf x) ∂μ := by
  obtain ⟨x, hx⟩ : ∃ x, C.cdf x ≠ D.cdf x := by
    by_contra! hall
    exact hne (ext_cdf hall)
  exact (D.continuous_cdf.sub C.continuous_cdf).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun y => sub_nonneg.mpr (h y))
    (x := x) (sub_ne_zero.mpr hx.symm)

private theorem integral_cdf_sub_nonneg {C D : Copula 2} (h : C.LowerOrthantLE D)
    (μ : Measure (Fin 2 → I)) : 0 ≤ ∫ x, (D.cdf x - C.cdf x) ∂μ :=
  integral_nonneg fun y => sub_nonneg.mpr (h y)

/-- **Strict monotonicity of Kendall's tau** when the larger copula has full support. -/
theorem LowerOrthantLE.kendallTau_lt_of_isOpenPosMeasure_right {C D : Copula 2}
    (h : C.LowerOrthantLE D) (hne : C ≠ D) [D.toMeasure.IsOpenPosMeasure] :
    C.kendallTau < D.kendallTau := by
  have h1 := integral_cdf_sub_pos h hne D.toMeasure
  have h2 := integral_cdf_sub_nonneg h C.toMeasure
  have := kendallTau_sub_eq C D
  linarith

/-- **Strict monotonicity of Kendall's tau** when the smaller copula has full support. -/
theorem LowerOrthantLE.kendallTau_lt_of_isOpenPosMeasure_left {C D : Copula 2}
    (h : C.LowerOrthantLE D) (hne : C ≠ D) [C.toMeasure.IsOpenPosMeasure] :
    C.kendallTau < D.kendallTau := by
  have h1 := integral_cdf_sub_nonneg h D.toMeasure
  have h2 := integral_cdf_sub_pos h hne C.toMeasure
  have := kendallTau_sub_eq C D
  linarith

/-- Under full support of the larger copula, equal Kendall's taus force equality. -/
theorem LowerOrthantLE.kendallTau_eq_iff_of_isOpenPosMeasure_right {C D : Copula 2}
    (h : C.LowerOrthantLE D) [D.toMeasure.IsOpenPosMeasure] :
    C.kendallTau = D.kendallTau ↔ C = D := by
  refine ⟨fun he => ?_, fun he => he ▸ rfl⟩
  by_contra hne
  exact (h.kendallTau_lt_of_isOpenPosMeasure_right hne).ne he

/-- Under full support of the smaller copula, equal Kendall's taus force equality. -/
theorem LowerOrthantLE.kendallTau_eq_iff_of_isOpenPosMeasure_left {C D : Copula 2}
    (h : C.LowerOrthantLE D) [C.toMeasure.IsOpenPosMeasure] :
    C.kendallTau = D.kendallTau ↔ C = D := by
  refine ⟨fun he => ?_, fun he => he ▸ rfl⟩
  by_contra hne
  exact (h.kendallTau_lt_of_isOpenPosMeasure_left hne).ne he

end ProbabilityTheory.Copula
