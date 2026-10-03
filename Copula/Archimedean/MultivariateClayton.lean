/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Multivariate
import Copula.Families.Clayton.Negative
import Copula.Rank.Integration

/-!
# Negative-parameter Clayton copulas in dimension `d`

The Clayton formula
`C_θ(u) = max(0, u₁^{-θ} + ⋯ + u_d^{-θ} - d + 1)^{-1/θ}`
is a `d`-copula for `-1/(d-1) ≤ θ < 0` (Nelsen 2006, §4.6; McNeil–Nešlehová 2009, §4, where the
bound `θ ≥ -1/(d-1)` is shown to be sharp): its inverse generator `ψ(t) = max(0, 1 - t)^{-1/θ}` is
`d`-monotone exactly when `-1/θ ≥ d - 1` (`isMultiplyMonotone_truncated_rpow`).

* `claytonNegativeMultivariate d θ` is the resulting `d`-copula, with the closed-form CDF
  `cdf_claytonNegativeMultivariate`; in dimension two it is the bivariate negative Clayton copula
  (`claytonNegativeMultivariate_two`).
* Conversely the bound is sharp (`not_cdf_eq_claytonFormula`): for `θ < -1/(d-1)` no `d`-copula
  has this CDF. The proof is elementary: a copula vanishing on `{∑ uᵢ^β ≤ d - 1}` is carried by
  `{∑ Uᵢ^β ≥ d - 1}`, hence `d/(1+β) = E ∑ Uᵢ^β ≥ d - 1`, i.e. `(d - 1) β ≤ 1`
  (`mul_le_one_of_cdf_eq_zero`). With `β = 1` this also re-proves that `W_d` is not a copula for
  `d ≥ 3`.
-/

open Set Filter Topology MeasureTheory Asymptotics
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-! ### Truncated powers -/

private theorem rpow_eq_mul_rpow_sub_one {m α : ℝ} (hm : 0 ≤ m) (hα : 1 < α) :
    m ^ α = m * m ^ (α - 1) := by
  rcases hm.lt_or_eq with hm | rfl
  · rw [Real.rpow_sub_one hm.ne']
    field_simp
  · rw [Real.zero_rpow (by linarith), zero_mul]

/-- The truncated power `z ↦ max(0, z)^α` is differentiable for `α > 1`. -/
theorem hasDerivAt_max_zero_rpow {α : ℝ} (hα : 1 < α) (y : ℝ) :
    HasDerivAt (fun z : ℝ => (max 0 z) ^ α) (α * (max 0 y) ^ (α - 1)) y := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hev : (fun z : ℝ => (max 0 z) ^ α) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      rw [max_eq_left hz.le, Real.zero_rpow (by linarith)]
    rw [max_eq_left hy.le, Real.zero_rpow (by linarith), mul_zero]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
  · rw [max_self, Real.zero_rpow (by linarith), mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have h1 : (fun h : ℝ => max 0 h) =O[𝓝 0] fun h => h :=
      IsBigO.of_bound 1 (Eventually.of_forall fun h => by
        rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        exact max_le (abs_nonneg _) (le_abs_self _))
    have h2 : (fun h : ℝ => (max 0 h) ^ (α - 1)) =o[𝓝 0] fun _ => (1 : ℝ) := by
      rw [isLittleO_one_iff]
      have hc : ContinuousAt (fun h : ℝ => (max 0 h) ^ (α - 1)) 0 :=
        (continuous_const.max continuous_id).continuousAt.rpow_const (Or.inr (by linarith))
      have := hc.tendsto
      simpa [Real.zero_rpow (by linarith : α - 1 ≠ 0)] using this
    refine (h1.mul_isLittleO h2).congr' (Eventually.of_forall fun h => ?_)
      (Eventually.of_forall fun h => mul_one h)
    simp only [zero_add, max_self, Real.zero_rpow (by linarith : α ≠ 0), sub_zero, smul_zero]
    exact (rpow_eq_mul_rpow_sub_one (le_max_left 0 h) hα).symm
  · have hev : (fun z : ℝ => (max 0 z) ^ α) =ᶠ[𝓝 y] fun z => z ^ α := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      rw [max_eq_right (le_of_lt hz)]
    rw [max_eq_right hy.le]
    exact (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).congr_of_eventuallyEq hev

private theorem hasDerivAt_truncated_rpow {α : ℝ} (hα : 1 < α) (c t : ℝ) :
    HasDerivAt (fun s : ℝ => c * (max 0 (1 - s)) ^ α)
      (c * (α * (max 0 (1 - t)) ^ (α - 1) * (-1))) t :=
  ((hasDerivAt_max_zero_rpow hα (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)).const_mul c

/-- **`c · max(0, 1 - t)^α` is `n`-monotone whenever `α ≥ n - 1`** (`c ≥ 0`, `α ≥ 0`). -/
theorem isMultiplyMonotone_truncated_rpow : ∀ (n : ℕ) {c α : ℝ}, 0 ≤ c → 0 ≤ α →
    (n : ℝ) - 1 ≤ α → IsMultiplyMonotone n (fun t => c * (max 0 (1 - t)) ^ α)
  | 0, c, α, hc, _, _ => fun _ _ => mul_nonneg hc (Real.rpow_nonneg (le_max_left _ _) _)
  | 1, c, α, hc, hα, _ => ⟨fun _ _ => mul_nonneg hc (Real.rpow_nonneg (le_max_left _ _) _),
      fun _ _ _ _ hxy => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_left _ _)
        (max_le_max le_rfl (by linarith)) hα) hc⟩
  | 2, c, α, hc, hα, hn => by
    have hα1 : 1 ≤ α := by norm_num at hn; linarith
    refine ⟨fun _ _ => mul_nonneg hc (Real.rpow_nonneg (le_max_left _ _) _),
      fun _ _ _ _ hxy => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_left _ _)
        (max_le_max le_rfl (by linarith)) hα) hc, ?_⟩
    have hconv : ConvexOn ℝ (Ici 0) (fun t : ℝ => (max 0 (1 - t)) ^ α) :=
      (truncatedLinearGenerator.innerPower α hα1).convex
    simpa [smul_eq_mul] using (hconv.subset Ioi_subset_Ici_self (convex_Ioi 0)).smul hc
  | n + 3, c, α, hc, hα, hn => by
    have hα1 : 1 < α := by push_cast at hn; linarith
    refine ⟨fun _ _ => mul_nonneg hc (Real.rpow_nonneg (le_max_left _ _) _),
      fun t _ => (hasDerivAt_truncated_rpow hα1 c t).differentiableAt.differentiableWithinAt,
      ?_⟩
    refine IsMultiplyMonotone.congr (n := n + 2)
      (isMultiplyMonotone_truncated_rpow (n + 2) (c := c * α) (α := α - 1)
        (mul_nonneg hc hα) (by linarith) (by push_cast at hn ⊢; linarith)) fun t _ => ?_
    simp only [(hasDerivAt_truncated_rpow hα1 c t).deriv]
    ring

/-! ### The negative Clayton family in dimension `d` -/

private theorem one_le_neg_inv {d : ℕ} {θ : ℝ} (hd : 2 ≤ d) (hθ : -1 / ((d : ℝ) - 1) ≤ θ)
    (hn : θ < 0) : (d : ℝ) - 1 ≤ (-θ)⁻¹ := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h : -θ ≤ 1 / ((d : ℝ) - 1) := by
    rw [neg_div] at hθ
    linarith
  rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
  rw [le_div_iff₀ (by linarith)] at h
  linarith

/-- The `d`-monotone generator `max(0, 1 - t)^{-1/θ}` of the Clayton family for
`-1/(d-1) ≤ θ < 0`. -/
noncomputable def claytonNegativeGenerator (d : ℕ) (θ : ℝ) (hd : 2 ≤ d)
    (hθ : -1 / ((d : ℝ) - 1) ≤ θ) (hn : θ < 0) : MultivariateGenerator d where
  toBivariateGenerator := truncatedLinearGenerator.innerPower (-θ)⁻¹ (by
    have := one_le_neg_inv hd hθ hn
    have : (1 : ℝ) ≤ (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith)
  continuousOn := by
    apply Continuous.continuousOn
    exact (continuous_const.max (continuous_const.sub continuous_id)).rpow_const
      (fun _ => Or.inr (inv_nonneg.mpr (by linarith)))
  multiplyMonotone := by
    refine (isMultiplyMonotone_truncated_rpow d (c := 1) (α := (-θ)⁻¹) zero_le_one
      (inv_nonneg.mpr (by linarith)) (one_le_neg_inv hd hθ hn)).congr fun t _ => ?_
    simp [BivariateGenerator.innerPower, truncatedLinearGenerator]

/-- **The `d`-dimensional Clayton copula with parameter `-1/(d-1) ≤ θ < 0`.** -/
noncomputable def claytonNegativeMultivariate (d : ℕ) (θ : ℝ) (hd : 2 ≤ d)
    (hθ : -1 / ((d : ℝ) - 1) ≤ θ) (hn : θ < 0) : Copula d :=
  (claytonNegativeGenerator d θ hd hθ hn).copula

/-- The Clayton CDF formula `max(0, ∑ uᵢ^{-θ} - d + 1)^{-1/θ}` (and `0` on the lower faces). -/
noncomputable def claytonFormula (d : ℕ) (θ : ℝ) (u : Fin d → I) : ℝ := by
  classical
  exact if ∃ i, u i = 0 then 0 else (max 0 (∑ i, (u i : ℝ) ^ (-θ) - d + 1)) ^ (-θ)⁻¹

/-- **Closed form of the negative Clayton CDF.** -/
theorem cdf_claytonNegativeMultivariate (d : ℕ) (θ : ℝ) (hd : 2 ≤ d)
    (hθ : -1 / ((d : ℝ) - 1) ≤ θ) (hn : θ < 0) :
    (claytonNegativeMultivariate d θ hd hθ hn).cdf = claytonFormula d θ := by
  funext u
  rw [claytonNegativeMultivariate, MultivariateGenerator.cdf_copula, claytonFormula]
  by_cases h : ∃ i, u i = 0
  · rw [MultivariateGenerator.cdf_of_exists_zero _ h]
    simp only [h, ↓reduceIte]
  · have h' : ∀ i, u i ≠ 0 := fun i hi => h ⟨i, hi⟩
    rw [MultivariateGenerator.cdf_of_forall_ne_zero _ h']
    simp only [h, ↓reduceIte]
    simp only [claytonNegativeGenerator, BivariateGenerator.innerPower, truncatedLinearGenerator,
      coe_unitPower, inv_inv]
    congr 2
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring

/-- In dimension two this is the bivariate negative Clayton copula. -/
theorem claytonNegativeMultivariate_two (θ : ℝ) (hθ : -1 / (((2 : ℕ) : ℝ) - 1) ≤ θ)
    (hθ' : -1 ≤ θ) (hn : θ < 0) :
    claytonNegativeMultivariate 2 θ le_rfl hθ hn = claytonNegative θ hθ' hn :=
  MultivariateGenerator.copula_two _

theorem isArchimedean_claytonNegativeMultivariate (d : ℕ) (θ : ℝ) (hd : 2 ≤ d)
    (hθ : -1 / ((d : ℝ) - 1) ≤ θ) (hn : θ < 0) :
    IsArchimedean (claytonNegativeMultivariate d θ hd hθ hn) :=
  MultivariateGenerator.isArchimedean_copula _

/-! ### Sharpness of the parameter bound -/

/-- Dyadic upper approximation of a point of the unit interval. -/
private noncomputable def dyadicUp (n : ℕ) (k : ℕ) : I :=
  Set.projIcc 0 1 zero_le_one ((k : ℝ) / 2 ^ n)

/-- **A copula vanishing on `{∑ uᵢ^β ≤ d - 1}` forces `(d - 1) β ≤ 1`.** Such a copula is
carried by `{∑ Uᵢ^β ≥ d - 1}` while `E ∑ Uᵢ^β = d/(1 + β)`. -/
theorem mul_le_one_of_cdf_eq_zero {d : ℕ} (C : Copula d) {β : ℝ} (hβ : 0 < β)
    (h0 : ∀ u : Fin d → I, ∑ i, (u i : ℝ) ^ β ≤ (d : ℝ) - 1 → C.cdf u = 0) :
    ((d : ℝ) - 1) * β ≤ 1 := by
  classical
  set F : (Fin d → I) → ℝ := fun x => ∑ i, (x i : ℝ) ^ β with hF
  have hFc : Continuous F := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_subtype_val.comp (continuous_apply i)).rpow_const
      (fun _ => Or.inr hβ.le)
  -- the set `{F < d - 1}` is `C`-null
  have hnull : C.toMeasure {x | F x < (d : ℝ) - 1} = 0 := by
    let w : ℕ × (Fin d → ℕ) → Fin d → I := fun p i => dyadicUp p.1 (p.2 i)
    have hcover : {x | F x < (d : ℝ) - 1} ⊆
        ⋃ p : ℕ × (Fin d → ℕ), {x | F (w p) ≤ (d : ℝ) - 1 ∧ x ≤ w p} := by
      intro x hx
      -- dyadic approximations from above converge to `x`
      let k : ℕ → Fin d → ℕ := fun n i => ⌈(x i : ℝ) * 2 ^ n⌉₊
      have hk : ∀ n i, (x i : ℝ) ≤ (k n i : ℝ) / 2 ^ n ∧
          (k n i : ℝ) / 2 ^ n ≤ (x i : ℝ) + 1 / 2 ^ n := by
        intro n i
        have hp : (0 : ℝ) < 2 ^ n := by positivity
        constructor
        · rw [le_div_iff₀ hp]
          exact Nat.le_ceil _
        · rw [div_le_iff₀ hp, add_mul, one_div_mul_cancel hp.ne']
          have := Nat.ceil_lt_add_one (show 0 ≤ (x i : ℝ) * 2 ^ n by
            have := (x i).property.1; positivity)
          linarith
      have hlim : Tendsto (fun n => F (w (n, k n))) atTop (𝓝 (F x)) := by
        have hw : ∀ i, Tendsto (fun n => ((w (n, k n) i : I) : ℝ)) atTop (𝓝 (x i : ℝ)) := by
          intro i
          have hup : Tendsto (fun n : ℕ => (x i : ℝ) + 1 / 2 ^ n) atTop (𝓝 (x i : ℝ)) := by
            have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
              simp only [one_div]
              exact tendsto_inv_atTop_zero.comp
                (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
            simpa using tendsto_const_nhds.add this
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          · intro n
            simp only [w, dyadicUp, Set.coe_projIcc]
            exact le_max_of_le_right (le_min (x i).property.2 (hk n i).1)
          · intro n
            simp only [w, dyadicUp, Set.coe_projIcc]
            exact max_le (by have := (x i).property.1; positivity)
              ((min_le_right _ _).trans (hk n i).2)
        exact (hFc.tendsto x).comp (tendsto_pi_nhds.mpr fun i =>
          tendsto_subtype_rng.mpr (hw i))
      obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hx)).exists
      refine Set.mem_iUnion.mpr ⟨(n, k n), hn.le, fun i => ?_⟩
      show (x i : ℝ) ≤ ((w (n, k n) i : I) : ℝ)
      simp only [w, dyadicUp, Set.coe_projIcc]
      exact le_max_of_le_right (le_min (x i).property.2 (hk n i).1)
    apply measure_mono_null hcover
    apply measure_iUnion_null
    intro p
    by_cases hp : F (w p) ≤ (d : ℝ) - 1
    · have hset : {x | F (w p) ≤ (d : ℝ) - 1 ∧ x ≤ w p} = Iic (w p) := by
        ext x; simp [hp]
      rw [hset]
      have := h0 (w p) hp
      rw [cdf, measureReal_def, ENNReal.toReal_eq_zero_iff] at this
      exact this.resolve_right (measure_ne_top _ _)
    · have hset : {x | F (w p) ≤ (d : ℝ) - 1 ∧ x ≤ w p} = ∅ := by
        ext x; simp [hp]
      rw [hset, measure_empty]
  -- integrate
  have hae : ∀ᵐ x ∂C.toMeasure, (d : ℝ) - 1 ≤ F x := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => not_le.mp hx) hnull
  have hint : (∫ x, F x ∂C.toMeasure) = (d : ℝ) / (β + 1) := by
    simp only [hF]
    rw [integral_finsetSum (f := fun i (x : Fin d → I) => (x i : ℝ) ^ β) _
      (fun i _ => integrable_continuous_cube C.toMeasure
        (show Continuous (fun x : Fin d → I => (x i : ℝ) ^ β) from
          (continuous_subtype_val.comp (continuous_apply i)).rpow_const
            (fun _ => Or.inr hβ.le)))]
    have he : ∀ i : Fin d, (∫ x, (x i : ℝ) ^ β ∂C.toMeasure) = 1 / (β + 1) := by
      intro i
      rw [C.integral_eval i (fun u : I => (u : ℝ) ^ β) (by fun_prop),
        integral_unitInterval (fun t => t ^ β), integral_rpow (Or.inl (by linarith))]
      simp [Real.zero_rpow (by linarith : β + 1 ≠ 0)]
    simp_rw [he]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hle : (d : ℝ) - 1 ≤ ∫ x, F x ∂C.toMeasure := by
    have := integral_mono_ae (integrable_const ((d : ℝ) - 1))
      (integrable_continuous_cube C.toMeasure hFc) hae
    simpa using this
  rw [hint, le_div_iff₀ (by linarith)] at hle
  nlinarith

/-- **Sharpness of the Clayton parameter bound**: for `θ < -1/(d-1)` the Clayton formula is not
the CDF of any `d`-copula (McNeil–Nešlehová 2009; Nelsen 2006, §4.6). -/
theorem not_cdf_eq_claytonFormula {d : ℕ} (hd : 2 ≤ d) {θ : ℝ}
    (hθ : θ < -1 / ((d : ℝ) - 1)) (C : Copula d) : C.cdf ≠ claytonFormula d θ := by
  intro hC
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hθneg : θ < 0 := lt_of_lt_of_le hθ (div_nonpos_of_nonpos_of_nonneg (by norm_num)
    (by linarith))
  have hb := mul_le_one_of_cdf_eq_zero C (β := -θ) (by linarith) (fun u hu => by
    rw [hC, claytonFormula]
    split_ifs with h
    · rfl
    · rw [max_eq_left (by linarith), Real.zero_rpow (inv_ne_zero (by linarith))])
  have : -1 / ((d : ℝ) - 1) ≤ θ := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- **The Clayton formula with `θ < 0` is a `d`-copula iff `θ ≥ -1/(d-1)`.** -/
theorem exists_cdf_eq_claytonFormula_iff {d : ℕ} (hd : 2 ≤ d) {θ : ℝ} (hn : θ < 0) :
    (∃ C : Copula d, C.cdf = claytonFormula d θ) ↔ -1 / ((d : ℝ) - 1) ≤ θ := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra h
    exact not_cdf_eq_claytonFormula hd (not_le.mp h) C hC
  · intro hθ
    exact ⟨_, cdf_claytonNegativeMultivariate d θ hd hθ hn⟩

end ProbabilityTheory.Copula
