/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Symmetry
import Mathlib.Topology.ContinuousMap.Compact

/-! # Uniform CDF distance and exchangeability asymmetry

The uniform distance is the supremum of the pointwise absolute CDF difference.
`uniformMetricSpace` bundles its metric laws without imposing a global topology
instance on copulas. The bivariate exchangeability defect compares a copula
with its transpose.
-/

open scoped unitInterval
open Filter Topology

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The CDF bundled as a continuous function on the compact cube. -/
noncomputable def cdfContinuousMap (C : Copula d) : C(Fin d → I, ℝ) :=
  ⟨C.cdf, C.continuous_cdf⟩

theorem cdfContinuousMap_injective : Function.Injective (cdfContinuousMap (d := d)) := by
  intro C D h
  apply ext_cdf
  intro u
  exact congrArg (fun f : C(Fin d → I, ℝ) => f u) h

/-- Uniform (supremum) distance between two copula CDFs. -/
noncomputable def uniformCDFDistance (C D : Copula d) : ℝ :=
  dist C.cdfContinuousMap D.cdfContinuousMap

/-- The uniform metric, available as a local instance when needed. -/
@[instance_reducible] noncomputable def uniformMetricSpace (d : ℕ) : MetricSpace (Copula d) :=
  MetricSpace.induced cdfContinuousMap cdfContinuousMap_injective inferInstance

theorem uniformCDFDistance_eq_iSup (C D : Copula d) :
    C.uniformCDFDistance D = ⨆ u, |C.cdf u - D.cdf u| := by
  simp only [uniformCDFDistance, ContinuousMap.dist_eq_iSup, Real.dist_eq, cdfContinuousMap,
    ContinuousMap.coe_mk]

theorem uniformCDFDistance_nonneg (C D : Copula d) : 0 ≤ C.uniformCDFDistance D := dist_nonneg

theorem uniformCDFDistance_comm (C D : Copula d) :
    C.uniformCDFDistance D = D.uniformCDFDistance C := dist_comm _ _

@[simp] theorem uniformCDFDistance_self (C : Copula d) : C.uniformCDFDistance C = 0 := dist_self _

theorem uniformCDFDistance_eq_zero_iff (C D : Copula d) : C.uniformCDFDistance D = 0 ↔ C = D := by
  rw [uniformCDFDistance, dist_eq_zero]
  exact cdfContinuousMap_injective.eq_iff

/-- Convergence in the uniform distance is precisely uniform convergence of CDFs. -/
theorem tendsto_uniformCDFDistance_iff {α : Type*} (F : α → Copula d) (C : Copula d) (l : Filter α) :
    Tendsto (fun a => (F a).uniformCDFDistance C) l (𝓝 0) ↔
      TendstoUniformly (fun a => (F a).cdf) C.cdf l := by
  change Tendsto (fun a => dist (BoundedContinuousFunction.mkOfCompact (F a).cdfContinuousMap)
    (BoundedContinuousFunction.mkOfCompact C.cdfContinuousMap)) l (𝓝 0) ↔ _
  rw [← tendsto_iff_dist_tendsto_zero, BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  rfl

theorem uniformCDFDistance_triangle (C D E : Copula d) :
    C.uniformCDFDistance E ≤ C.uniformCDFDistance D + D.uniformCDFDistance E := dist_triangle _ _ _

theorem abs_cdf_sub_le_uniformCDFDistance (C D : Copula d) (u : Fin d → I) :
    |C.cdf u - D.cdf u| ≤ C.uniformCDFDistance D :=
  ContinuousMap.dist_apply_le_dist (f := C.cdfContinuousMap) (g := D.cdfContinuousMap) u

theorem uniformCDFDistance_le_iff (C D : Copula d) (r : ℝ) :
    C.uniformCDFDistance D ≤ r ↔ ∀ u, |C.cdf u - D.cdf u| ≤ r :=
  ContinuousMap.dist_le_iff_of_nonempty

theorem uniformCDFDistance_le_one (C D : Copula d) : C.uniformCDFDistance D ≤ 1 := by
  apply (C.uniformCDFDistance_le_iff D 1).2
  intro u
  exact abs_le.mpr ⟨by linarith [C.cdf_nonneg u, D.cdf_le_one u],
    by linarith [D.cdf_nonneg u, C.cdf_le_one u]⟩

/-- The diameter of bivariate copulas in the uniform metric is at most one half. -/
theorem uniformCDFDistance_le_half (C D : Copula 2) : C.uniformCDFDistance D ≤ 1 / 2 := by
  have hb (C D : Copula 2) (x : Fin 2 → I) : C.cdf x - D.cdf x ≤ 1 / 2 := by
    have h0 := C.cdf_le_coord x 0
    have h1 := C.cdf_le_coord x 1
    have hn := D.cdf_nonneg x
    have hl := D.sum_sub_dim_add_one_le_cdf x
    simp only [Fin.sum_univ_two, Nat.cast_ofNat] at hl
    linarith
  apply (C.uniformCDFDistance_le_iff D _).2
  intro x
  exact abs_le.mpr ⟨by linarith [hb D C x], hb C D x⟩

/-- The two Fréchet extremes attain the bivariate diameter. -/
@[simp] theorem uniformCDFDistance_comonotonic_countermonotonic :
    (comonotonic 2).uniformCDFDistance countermonotonic = 1 / 2 := by
  apply le_antisymm (uniformCDFDistance_le_half _ _)
  have h := (comonotonic 2).abs_cdf_sub_le_uniformCDFDistance countermonotonic ![unitHalf, unitHalf]
  rw [cdf_comonotonic_two, cdf_countermonotonic] at h
  norm_num [unitHalf] at h
  exact h

theorem uniformCDFDistance_mix_le (C D E F : Copula d) (a : I) :
    (C.mix D a).uniformCDFDistance (E.mix F a) ≤
      (a : ℝ) * C.uniformCDFDistance E + (1 - (a : ℝ)) * D.uniformCDFDistance F := by
  apply (uniformCDFDistance_le_iff _ _ _).2
  intro u
  rw [cdf_mix, cdf_mix]
  have he : (a : ℝ) * C.cdf u + (1 - (a : ℝ)) * D.cdf u -
      ((a : ℝ) * E.cdf u + (1 - (a : ℝ)) * F.cdf u) =
      (a : ℝ) * (C.cdf u - E.cdf u) + (1 - (a : ℝ)) * (D.cdf u - F.cdf u) := by ring
  rw [he]
  calc
    _ ≤ |(a : ℝ) * (C.cdf u - E.cdf u)| + |(1 - (a : ℝ)) * (D.cdf u - F.cdf u)| := abs_add_le _ _
    _ = (a : ℝ) * |C.cdf u - E.cdf u| + (1 - (a : ℝ)) * |D.cdf u - F.cdf u| := by
      rw [abs_mul, abs_mul, abs_of_nonneg a.property.1, abs_of_nonneg (sub_nonneg.mpr a.property.2)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (C.abs_cdf_sub_le_uniformCDFDistance E u) a.property.1)
      (mul_le_mul_of_nonneg_left (D.abs_cdf_sub_le_uniformCDFDistance F u) (sub_nonneg.mpr a.property.2))

theorem uniformCDFDistance_transpose (C D : Copula 2) :
    C.transpose.uniformCDFDistance D.transpose = C.uniformCDFDistance D := by
  have h (C D : Copula 2) : C.transpose.uniformCDFDistance D.transpose ≤ C.uniformCDFDistance D := by
    apply (uniformCDFDistance_le_iff _ _ _).2
    intro x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    conv_lhs => rw [hx, cdf_transpose, cdf_transpose]
    exact C.abs_cdf_sub_le_uniformCDFDistance D _
  exact le_antisymm (h C D) (by simpa only [transpose_transpose] using h C.transpose D.transpose)

/-- The unnormalized uniform exchangeability defect `sup |C(u,v)-C(v,u)|`. -/
noncomputable def exchangeabilityDefect (C : Copula 2) : ℝ := C.uniformCDFDistance C.transpose

theorem exchangeabilityDefect_nonneg (C : Copula 2) : 0 ≤ C.exchangeabilityDefect :=
  C.uniformCDFDistance_nonneg _

theorem exchangeabilityDefect_eq_zero_iff (C : Copula 2) :
    C.exchangeabilityDefect = 0 ↔ C.IsExchangeable := by
  rw [exchangeabilityDefect, uniformCDFDistance_eq_zero_iff]
  exact eq_comm

@[simp] theorem exchangeabilityDefect_transpose (C : Copula 2) :
    C.transpose.exchangeabilityDefect = C.exchangeabilityDefect := by
  simp only [exchangeabilityDefect, transpose_transpose, uniformCDFDistance_comm]

theorem exchangeabilityDefect_mix_le (C D : Copula 2) (a : I) :
    (C.mix D a).exchangeabilityDefect ≤ (a : ℝ) * C.exchangeabilityDefect +
      (1 - (a : ℝ)) * D.exchangeabilityDefect := by
  simpa only [exchangeabilityDefect, transpose_mix] using
    uniformCDFDistance_mix_le C D C.transpose D.transpose a

@[simp] theorem exchangeabilityDefect_independence : (independence 2).exchangeabilityDefect = 0 :=
  (exchangeabilityDefect_eq_zero_iff _).2 isExchangeable_independence

@[simp] theorem exchangeabilityDefect_comonotonic : (comonotonic 2).exchangeabilityDefect = 0 :=
  (exchangeabilityDefect_eq_zero_iff _).2 isExchangeable_comonotonic

@[simp] theorem exchangeabilityDefect_countermonotonic : countermonotonic.exchangeabilityDefect = 0 :=
  (exchangeabilityDefect_eq_zero_iff _).2 isExchangeable_countermonotonic

/-- The universal one-third bound for the unnormalized exchangeability defect. -/
theorem exchangeabilityDefect_le_third (C : Copula 2) : C.exchangeabilityDefect ≤ 1 / 3 := by
  have hb (u v : I) (huv : u ≤ v) : |C.cdf ![u, v] - C.cdf ![v, u]| ≤ 1 / 3 := by
    have hC := C.cdf_le_coord ![u, v] 0
    have hD := C.cdf_le_coord ![v, u] 1
    have hnC := C.cdf_nonneg ![u, v]
    have hnD := C.cdf_nonneg ![v, u]
    have hlC := C.sum_sub_dim_add_one_le_cdf ![u, v]
    have hlD := C.sum_sub_dim_add_one_le_cdf ![v, u]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_ofNat] at hC hD hlC hlD
    have h₁ : |C.cdf ![u, v] - C.cdf ![v, u]| ≤ (u : ℝ) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have h₂ : |C.cdf ![u, v] - C.cdf ![v, u]| ≤ 1 - (v : ℝ) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hmC : C.cdf ![u, u] ≤ C.cdf ![u, v] := C.monotone_cdf (by
      intro i; fin_cases i; exact le_rfl; exact huv)
    have hmD : C.cdf ![u, u] ≤ C.cdf ![v, u] := C.monotone_cdf (by
      intro i; fin_cases i; exact huv; exact le_rfl)
    have ha := C.cdf_sub_le_sum_abs ![u, v] ![u, u]
    have hb := C.cdf_sub_le_sum_abs ![v, u] ![u, u]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
      abs_zero, zero_add, add_zero, abs_of_nonneg (sub_nonneg.mpr (show (u : ℝ) ≤ v from huv))] at ha hb
    have h₃ : |C.cdf ![u, v] - C.cdf ![v, u]| ≤ (v : ℝ) - u :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  apply (uniformCDFDistance_le_iff _ _ _).2
  intro x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx, cdf_transpose]
  rcases le_total (x 0) (x 1) with h | h
  · exact hb _ _ h
  · simpa only [abs_sub_comm] using hb _ _ h

end ProbabilityTheory.Copula
