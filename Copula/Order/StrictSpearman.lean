/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Rank
import Copula.Dependence.Basic
import Copula.UnitInterval

/-! # Strict concordance monotonicity of Spearman's rho

Among two comparable copulas, equality of rho forces equality of the
copulas. In particular, zero rho detects independence within either the
PQD or NQD class. No such claim is made for arbitrary copulas.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem LowerOrthantLE.spearmanRho_eq_iff {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.spearmanRho = D.spearmanRho ↔ C = D := by
  refine ⟨fun he => ?_, fun he => he ▸ rfl⟩
  rw [C.spearmanRho_eq_integral_cdf, D.spearmanRho_eq_integral_cdf] at he
  have hi : (∫ x, C.cdf x ∂(independence 2).toMeasure) =
      ∫ x, D.cdf x ∂(independence 2).toMeasure := by linarith
  have ha := (integral_eq_iff_of_ae_le (C.integrable_cdf (independence 2).toMeasure)
    (D.integrable_cdf (independence 2).toMeasure) (Filter.Eventually.of_forall h)).1 hi
  change C.cdf =ᵐ[volume] D.cdf at ha
  exact cdf_injective (Measure.eq_of_ae_eq ha C.continuous_cdf D.continuous_cdf)

theorem LowerOrthantLE.spearmanRho_lt_iff {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.spearmanRho < D.spearmanRho ↔ C ≠ D := by
  rw [lt_iff_le_and_ne, and_iff_right h.spearmanRho_le]
  exact not_congr h.spearmanRho_eq_iff

theorem LowerOrthantLE.spearmanRho_lt {C D : Copula 2} (h : C.LowerOrthantLE D)
    (hne : C ≠ D) : C.spearmanRho < D.spearmanRho := h.spearmanRho_lt_iff.mpr hne

theorem ConcordanceLE.spearmanRho_eq_iff {C D : Copula 2} (h : C.ConcordanceLE D) :
    C.spearmanRho = D.spearmanRho ↔ C = D := h.1.spearmanRho_eq_iff

theorem ConcordanceLE.spearmanRho_lt_iff {C D : Copula 2} (h : C.ConcordanceLE D) :
    C.spearmanRho < D.spearmanRho ↔ C ≠ D := h.1.spearmanRho_lt_iff

theorem isNQD_iff_lowerOrthantLE (C : Copula 2) :
    C.IsNQD ↔ C.LowerOrthantLE (independence 2) := by
  constructor
  · intro h u
    have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
    simpa only [cdf_independence, Fin.prod_univ_two, he] using h (u 0) (u 1)
  · intro h u v
    simpa [cdf_independence, Fin.prod_univ_two] using h ![u, v]

theorem IsPQD.spearmanRho_eq_zero_iff {C : Copula 2} (h : C.IsPQD) :
    C.spearmanRho = 0 ↔ C = independence 2 := by
  have ho := (isPQD_iff_lowerOrthantLE C).mp h
  simpa only [spearmanRho_independence, eq_comm] using ho.spearmanRho_eq_iff

theorem IsNQD.spearmanRho_eq_zero_iff {C : Copula 2} (h : C.IsNQD) :
    C.spearmanRho = 0 ↔ C = independence 2 := by
  have ho := (isNQD_iff_lowerOrthantLE C).mp h
  simpa only [spearmanRho_independence] using ho.spearmanRho_eq_iff

theorem IsPQD.spearmanRho_pos_iff {C : Copula 2} (h : C.IsPQD) :
    0 < C.spearmanRho ↔ C ≠ independence 2 := by
  have ho := (isPQD_iff_lowerOrthantLE C).mp h
  simpa only [spearmanRho_independence, ne_comm] using ho.spearmanRho_lt_iff

theorem IsNQD.spearmanRho_neg_iff {C : Copula 2} (h : C.IsNQD) :
    C.spearmanRho < 0 ↔ C ≠ independence 2 := by
  have ho := (isNQD_iff_lowerOrthantLE C).mp h
  simpa only [spearmanRho_independence] using ho.spearmanRho_lt_iff

theorem IsPQD.kendallTau_eq_zero_iff {C : Copula 2} (h : C.IsPQD) :
    C.kendallTau = 0 ↔ C = independence 2 := by
  refine ⟨fun hz => h.spearmanRho_eq_zero_iff.mp ?_, fun he => he ▸ kendallTau_independence⟩
  linarith [h.spearmanRho_nonneg, h.spearmanRho_le_three_mul_kendallTau]

theorem IsPQD.kendallTau_pos_iff {C : Copula 2} (h : C.IsPQD) :
    0 < C.kendallTau ↔ C ≠ independence 2 := by
  rw [lt_iff_le_and_ne, and_iff_right h.kendallTau_nonneg, ne_comm]
  exact not_congr h.kendallTau_eq_zero_iff

theorem IsNQD.spearmanRho_nonpos {C : Copula 2} (h : C.IsNQD) : C.spearmanRho ≤ 0 := by
  simpa only [spearmanRho_independence] using
    ((isNQD_iff_lowerOrthantLE C).mp h).spearmanRho_le

theorem IsNQD.three_mul_kendallTau_le_spearmanRho {C : Copula 2} (h : C.IsNQD) :
    3 * C.kendallTau ≤ C.spearmanRho := by
  have hi := integral_mono (C.integrable_cdf C.toMeasure)
    (integrable_continuous_cube C.toMeasure (show Continuous (fun x : Fin 2 → I =>
      (x 0 : ℝ) * (x 1 : ℝ)) by fun_prop))
    (fun x => by simpa only [cdf_independence, Fin.prod_univ_two] using
      (isNQD_iff_lowerOrthantLE C).mp h x)
  unfold spearmanRho kendallTau
  linarith

theorem IsNQD.kendallTau_nonpos {C : Copula 2} (h : C.IsNQD) : C.kendallTau ≤ 0 := by
  linarith [h.spearmanRho_nonpos, h.three_mul_kendallTau_le_spearmanRho]

theorem IsNQD.kendallTau_eq_zero_iff {C : Copula 2} (h : C.IsNQD) :
    C.kendallTau = 0 ↔ C = independence 2 := by
  refine ⟨fun hz => h.spearmanRho_eq_zero_iff.mp ?_, fun he => he ▸ kendallTau_independence⟩
  linarith [h.spearmanRho_nonpos, h.three_mul_kendallTau_le_spearmanRho]

theorem IsNQD.kendallTau_neg_iff {C : Copula 2} (h : C.IsNQD) :
    C.kendallTau < 0 ↔ C ≠ independence 2 := by
  rw [lt_iff_le_and_ne, and_iff_right h.kendallTau_nonpos]
  exact not_congr h.kendallTau_eq_zero_iff

end ProbabilityTheory.Copula
