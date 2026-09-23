/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.AMH
import Copula.Dependence.TotalPositivity

/-! # CDF-level total positivity of Ali–Mikhail–Haq copulas

This concerns TP2 of the CDF and does not assert an MTP2 Lebesgue density.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem amh_cdf_den_pos (θ : ℝ) (hθ : θ ≤ 1) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    0 < 1 - θ * (1 - (u : ℝ)) * (1 - (v : ℝ)) := by
  have huc : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
  have hvc : 0 ≤ 1 - (v : ℝ) := sub_nonneg.mpr v.property.2
  have hp : 0 ≤ (1 - (u : ℝ)) * (1 - (v : ℝ)) := mul_nonneg huc hvc
  have hple : (1 - (u : ℝ)) * (1 - (v : ℝ)) < 1 := by
    have h := mul_le_mul_of_nonneg_left
      (show 1 - (v : ℝ) ≤ 1 by linarith [v.property.1]) huc
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hθ hp
  nlinarith

/-- For θ≥0, the AMH CDF itself is TP2 on the entire closed square. -/
theorem isTP2CDF_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (hθ : 0 ≤ θ) :
    (amh θ hmin hmax).IsTP2CDF := by
  intro a b c d hab hcd
  by_cases ha : a = 0
  · simp [ha]
  by_cases hc : c = 0
  · subst c
    have hzero (u : I) : (amh θ hmin hmax).cdf ![u, 0] = 0 :=
      (amh θ hmin hmax).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
    simp [hzero]
  have hap : 0 < (a : ℝ) :=
    lt_of_le_of_ne a.property.1 (Ne.symm (by
      intro he; exact ha (Subtype.ext he)))
  have hcp : 0 < (c : ℝ) :=
    lt_of_le_of_ne c.property.1 (Ne.symm (by
      intro he; exact hc (Subtype.ext he)))
  have hbp : 0 < (b : ℝ) := lt_of_lt_of_le hap hab
  have hdp : 0 < (d : ℝ) := lt_of_lt_of_le hcp hcd
  let D (u v : I) : ℝ := 1 - θ * (1 - (u : ℝ)) * (1 - (v : ℝ))
  have hac : 0 < D a c := amh_cdf_den_pos θ hmax a c hap hcp
  have hbd : 0 < D b d := amh_cdf_den_pos θ hmax b d hbp hdp
  have had : 0 < D a d := amh_cdf_den_pos θ hmax a d hap hdp
  have hbc : 0 < D b c := amh_cdf_den_pos θ hmax b c hbp hcp
  have heq : D a d * D b c - D a c * D b d =
      θ * ((b : ℝ) - (a : ℝ)) * ((d : ℝ) - (c : ℝ)) := by
    dsimp [D]
    ring
  have hden : D a c * D b d ≤ D a d * D b c := by
    have hn := mul_nonneg (mul_nonneg hθ (sub_nonneg.mpr hab))
      (sub_nonneg.mpr hcd)
    linarith
  have hnum : 0 ≤ (a : ℝ) * (b : ℝ) * (c : ℝ) * (d : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg a.property.1 b.property.1)
      c.property.1) d.property.1
  have hratio := div_le_div_of_nonneg_left hnum (mul_pos hac hbd) hden
  change (amh θ hmin hmax).cdf ![a, d] * (amh θ hmin hmax).cdf ![b, c] ≤
    (amh θ hmin hmax).cdf ![a, c] * (amh θ hmin hmax).cdf ![b, d]
  rw [cdf_amh, cdf_amh, cdf_amh, cdf_amh]
  change ((a : ℝ) * (d : ℝ) / D a d) * ((b : ℝ) * (c : ℝ) / D b c) ≤
    ((a : ℝ) * (c : ℝ) / D a c) * ((b : ℝ) * (d : ℝ) / D b d)
  simp only [div_mul_div_comm]
  convert hratio using 1 <;> ring

/-- The AMH CDF is TP2 exactly for nonnegative parameters. -/
theorem isTP2CDF_amh_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).IsTP2CDF ↔ 0 ≤ θ := by
  constructor
  · intro h
    exact (isPQD_amh_iff θ hmin hmax).mp h.isPQD
  · exact isTP2CDF_amh θ hmin hmax

end ProbabilityTheory.Copula
