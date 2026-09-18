/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Clayton.CDF
import Copula.Independence
import Copula.Comonotonic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # The independence and comonotonic limits of Clayton copulas

The statements apply to any filter of positive parameters. At zero, differentiating
the logarithm of the CDF base gives the product limit. At infinity, a power-mean
bound squeezes the CDF to its smallest coordinate.
-/

open MeasureTheory Set Filter Real
open scoped unitInterval Topology BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

private theorem clayton_formula_tendsto_zero (u : Fin d → I)
    (hu : ∀ i, 0 < (u i : ℝ)) :
    Tendsto (fun θ : ℝ => (1 + ∑ i, ((u i : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹))
      (𝓝[>] 0) (𝓝 (∏ i, (u i : ℝ))) := by
  let B : ℝ → ℝ := fun θ => 1 + ∑ i, ((u i : ℝ) ^ (-θ) - 1)
  have hB0 : B 0 = 1 := by simp [B]
  have hderiv : HasDerivAt B (∑ i, -log (u i : ℝ)) 0 := by
    have hh (i : Fin d) : HasDerivAt (fun θ : ℝ => (u i : ℝ) ^ (-θ) - 1)
        (-log (u i : ℝ)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).neg.const_rpow (hu i)).sub_const 1)
    exact (HasDerivAt.fun_sum (fun i _ => hh i)).const_add 1
  have hl : HasDerivAt (fun θ => log (B θ)) (∑ i, -log (u i : ℝ)) 0 := by
    simpa [hB0] using hderiv.log (by rw [hB0]; exact one_ne_zero)
  have hs : Tendsto (fun θ : ℝ => θ⁻¹ * log (B θ)) (𝓝[>] 0)
      (𝓝 (∑ i, -log (u i : ℝ))) := by
    simpa [hB0] using hl.tendsto_slope_zero_right
  have hp : exp (-(∑ i, -log (u i : ℝ))) = ∏ i, (u i : ℝ) := by
    rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
    exact Finset.prod_congr rfl (fun i _ => Real.exp_log (hu i))
  rw [← hp]
  apply (hs.neg.rexp).congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hBpos : 0 < B θ := by
    have hn : 0 ≤ ∑ i, ((u i : ℝ) ^ (-θ) - 1) := Finset.sum_nonneg (fun i _ =>
      sub_nonneg.mpr (one_le_rpow_of_pos_of_le_one_of_nonpos (hu i) (u i).property.2
        (neg_nonpos.mpr (le_of_lt hθ))))
    dsimp [B]
    linarith
  rw [Real.rpow_def_of_pos hBpos]
  congr 1
  ring

/-- Positive Clayton parameters approaching zero give the independence CDF. -/
theorem tendsto_clayton_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 < θ a) (hlim : Tendsto θ l (𝓝 0)) (u : Fin d → I) :
    Tendsto (fun a => (clayton d (θ a) (hθ a)).cdf u) l
      (𝓝 ((independence d).cdf u)) := by
  by_cases hu : ∀ i, 0 < (u i : ℝ)
  · have ht : Tendsto θ l (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hθ⟩
    simpa only [cdf_clayton_of_pos _ _ _ hu, cdf_independence, Function.comp_def] using
      (clayton_formula_tendsto_zero u hu).comp ht
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    have hz : u i = 0 := Subtype.ext (le_antisymm hi (u i).property.1)
    simpa only [cdf_eq_zero_of_coord_eq_zero _ u i hz] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))

/-- A quantitative lower bound that becomes the minimum-coordinate CDF at infinity. -/
theorem clayton_min_lower_bound [NeZero d] (θ : ℝ) (hθ : 0 < θ)
    (u : Fin d → I) (hu : ∀ i, 0 < (u i : ℝ)) :
    (d : ℝ) ^ (-θ⁻¹) * ((⨅ i, u i : I) : ℝ) ≤ (clayton d θ hθ).cdf u := by
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := u)
  have hm (i : Fin d) : (u j : ℝ) ≤ (u i : ℝ) := by
    exact_mod_cast (hj.trans_le (iInf_le u i))
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  let B : ℝ := 1 + ∑ i, ((u i : ℝ) ^ (-θ) - 1)
  have hB : 0 < B := by
    have hh : 0 ≤ ∑ i, ((u i : ℝ) ^ (-θ) - 1) := Finset.sum_nonneg (fun i _ =>
      sub_nonneg.mpr (one_le_rpow_of_pos_of_le_one_of_nonpos (hu i) (u i).property.2
        (neg_nonpos.mpr hθ.le)))
    dsimp [B]
    linarith
  have hbound : B ≤ (d : ℝ) * (u j : ℝ) ^ (-θ) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin d) _ =>
      rpow_le_rpow_of_nonpos (hu j) (hm i) (neg_nonpos.mpr hθ.le))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    dsimp [B]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    linarith
  have hh := rpow_le_rpow_of_nonpos hB hbound (neg_nonpos.mpr (inv_pos.mpr hθ).le)
  rw [mul_rpow (zero_le_one.trans hd) (rpow_nonneg (hu j).le _), ← rpow_mul (hu j).le,
    show -θ * -θ⁻¹ = 1 by field_simp, rpow_one] at hh
  rw [cdf_clayton_of_pos θ hθ u hu, ← hj]
  exact hh

/-- Positive Clayton parameters tending to infinity give the comonotonic CDF. -/
theorem tendsto_clayton_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 < θ a) (hlim : Tendsto θ l atTop) (u : Fin d → I) :
    Tendsto (fun a => (clayton d (θ a) (hθ a)).cdf u) l
      (𝓝 ((comonotonic d).cdf u)) := by
  by_cases hd : d = 0
  · subst d
    simp only [cdf_dim_zero]
    exact tendsto_const_nhds
  let : NeZero d := ⟨hd⟩
  by_cases hu : ∀ i, 0 < (u i : ℝ)
  · have hi : Tendsto (fun a => -(θ a)⁻¹) l (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_inv_atTop_zero.comp hlim).neg
    have hp : Tendsto (fun a => (d : ℝ) ^ (-(θ a)⁻¹)) l (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.rpow hi (Or.inl (by exact_mod_cast hd)) :
        Tendsto (fun a => (d : ℝ) ^ (-(θ a)⁻¹)) l (𝓝 ((d : ℝ) ^ (0 : ℝ))))
    rw [cdf_comonotonic]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using hp.mul_const (((⨅ i, u i : I) : ℝ))) tendsto_const_nhds
    · exact fun a => clayton_min_lower_bound (θ a) (hθ a) u hu
    · intro a
      obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := u)
      rw [← hi]
      exact (clayton d (θ a) (hθ a)).cdf_le_coord u i
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    have hz : u i = 0 := Subtype.ext (le_antisymm hi (u i).property.1)
    simpa only [cdf_eq_zero_of_coord_eq_zero _ u i hz] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))

end ProbabilityTheory.Copula
