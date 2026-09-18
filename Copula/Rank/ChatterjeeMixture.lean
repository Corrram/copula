/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ChatterjeeCross

/-! # Quadratic mixture identities and strict convexity of Chatterjee's xi

Mixture weights stay constant under conditioning because every first marginal
is uniform. Xi is a quadratic, strictly convex functional of the copula, and
mixing with independence scales xi by the square of the retained weight.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem chatterjeeXi_mix (C D : Copula 2) (a : I) :
    (C.mix D a).chatterjeeXi = (a : ℝ) ^ 2 * C.chatterjeeXi +
      (1 - (a : ℝ)) ^ 2 * D.chatterjeeXi +
        2 * (a : ℝ) * (1 - (a : ℝ)) * C.chatterjeeCross D := by
  have he (v : I) : (∫ u : I, (C.mix D a).conditionalCDF u v ^ 2) =
      (a : ℝ) ^ 2 * (∫ u : I, C.conditionalCDF u v ^ 2) +
      (1 - (a : ℝ)) ^ 2 * (∫ u : I, D.conditionalCDF u v ^ 2) +
      (2 * (a : ℝ) * (1 - (a : ℝ))) * (∫ u : I, C.conditionalCDF u v * D.conditionalCDF u v) := by
    calc
      _ = ∫ u : I, (a : ℝ) ^ 2 * C.conditionalCDF u v ^ 2 +
          (1 - (a : ℝ)) ^ 2 * D.conditionalCDF u v ^ 2 +
          (2 * (a : ℝ) * (1 - (a : ℝ))) * (C.conditionalCDF u v * D.conditionalCDF u v) :=
        integral_congr_ae (by
          filter_upwards [conditionalCDF_mix C D a v] with u hu
          rw [hu]
          ring)
      _ = _ := by
        have hs : Integrable (fun u : I => (a : ℝ) ^ 2 * C.conditionalCDF u v ^ 2 +
            (1 - (a : ℝ)) ^ 2 * D.conditionalCDF u v ^ 2) :=
          ((C.integrable_conditionalCDF_sq v).const_mul _).add
            ((D.integrable_conditionalCDF_sq v).const_mul _)
        rw [integral_add hs
            ((C.integrable_conditionalCDF_mul D v).const_mul (2 * (a : ℝ) * (1 - (a : ℝ)))),
          integral_add ((C.integrable_conditionalCDF_sq v).const_mul ((a : ℝ) ^ 2))
            ((D.integrable_conditionalCDF_sq v).const_mul ((1 - (a : ℝ)) ^ 2))]
        simp only [integral_const_mul]
  unfold chatterjeeXi chatterjeeCross
  simp_rw [he]
  have hs : Integrable (fun v : I => (a : ℝ) ^ 2 * (∫ u : I, C.conditionalCDF u v ^ 2) +
      (1 - (a : ℝ)) ^ 2 * (∫ u : I, D.conditionalCDF u v ^ 2)) :=
    (C.integrable_integral_conditionalCDF_sq.const_mul _).add
      (D.integrable_integral_conditionalCDF_sq.const_mul _)
  rw [integral_add hs
      ((C.integrable_integral_conditionalCDF_mul D).const_mul (2 * (a : ℝ) * (1 - (a : ℝ)))),
    integral_add (C.integrable_integral_conditionalCDF_sq.const_mul ((a : ℝ) ^ 2))
      (D.integrable_integral_conditionalCDF_sq.const_mul ((1 - (a : ℝ)) ^ 2))]
  simp only [integral_const_mul]
  ring

/-- The exact nonnegative defect in the convexity inequality. -/
theorem chatterjeeXi_mix_eq_sub_distance (C D : Copula 2) (a : I) :
    (C.mix D a).chatterjeeXi = (a : ℝ) * C.chatterjeeXi +
      (1 - (a : ℝ)) * D.chatterjeeXi -
        6 * (a : ℝ) * (1 - (a : ℝ)) * C.conditionalCDFDistanceSq D := by
  rw [chatterjeeXi_mix]
  have he := congrArg (fun x : ℝ => (a : ℝ) * (1 - (a : ℝ)) * x)
    (C.conditionalCDFDistanceSq_eq_cross D)
  nlinarith only [he]

theorem chatterjeeXi_mix_le (C D : Copula 2) (a : I) :
    (C.mix D a).chatterjeeXi ≤ (a : ℝ) * C.chatterjeeXi + (1 - (a : ℝ)) * D.chatterjeeXi := by
  rw [chatterjeeXi_mix_eq_sub_distance]
  exact sub_le_self _ (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) a.property.1) (sub_nonneg.mpr a.property.2))
    (C.conditionalCDFDistanceSq_nonneg D))

/-- Every nontrivial mixture of distinct copulas gives strict convexity. -/
theorem chatterjeeXi_mix_lt {C D : Copula 2} (hne : C ≠ D) (a : I)
    (ha0 : 0 < a) (ha1 : a < 1) :
    (C.mix D a).chatterjeeXi < (a : ℝ) * C.chatterjeeXi + (1 - (a : ℝ)) * D.chatterjeeXi := by
  rw [chatterjeeXi_mix_eq_sub_distance]
  exact sub_lt_self _ (mul_pos (mul_pos (mul_pos (by norm_num) ha0) (sub_pos.mpr ha1))
    ((C.conditionalCDFDistanceSq_pos_iff D).2 hne))

theorem chatterjeeXi_mix_eq_iff (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    (C.mix D a).chatterjeeXi = (a : ℝ) * C.chatterjeeXi + (1 - (a : ℝ)) * D.chatterjeeXi ↔
      C = D := by
  constructor
  · intro he
    by_contra hn
    exact (ne_of_lt (chatterjeeXi_mix_lt hn a ha0 ha1)) he
  · intro he
    subst D
    rw [chatterjeeXi_mix_eq_sub_distance, conditionalCDFDistanceSq_self]
    ring

/-- Mixing with independence attenuates xi quadratically in the retained copula weight. -/
theorem chatterjeeXi_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).chatterjeeXi = (a : ℝ) ^ 2 * C.chatterjeeXi := by
  simp [chatterjeeXi_mix]

theorem chatterjeeXi_independence_mix (C : Copula 2) (a : I) :
    ((independence 2).mix C a).chatterjeeXi = (1 - (a : ℝ)) ^ 2 * C.chatterjeeXi := by
  simp [chatterjeeXi_mix]

/-- Mixing with the upper Fréchet bound links xi to Spearman's footrule. -/
theorem chatterjeeXi_mix_comonotonic (C : Copula 2) (a : I) :
    (C.mix (comonotonic 2) a).chatterjeeXi = (a : ℝ) ^ 2 * C.chatterjeeXi +
      (1 - (a : ℝ)) ^ 2 + 2 * (a : ℝ) * (1 - (a : ℝ)) * C.spearmanFootrule := by
  simp [chatterjeeXi_mix]

theorem chatterjeeXi_mix_comonotonic_countermonotonic (a : I) :
    ((comonotonic 2).mix countermonotonic a).chatterjeeXi =
      (a : ℝ) ^ 2 + (1 - (a : ℝ)) ^ 2 - (a : ℝ) * (1 - (a : ℝ)) := by
  have hc : (comonotonic 2).chatterjeeCross countermonotonic = -1 / 2 := by
    rw [chatterjeeCross_comm, chatterjeeCross_comonotonic, spearmanFootrule_countermonotonic]
  rw [chatterjeeXi_mix, chatterjeeXi_comonotonic, chatterjeeXi_countermonotonic, hc]
  ring

end ProbabilityTheory.Copula
