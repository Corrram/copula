/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Clayton
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The Clayton CDF

The gamma Laplace transform identifies the joint tails of the exponential/gamma
ratios. Inverting the marginal CDFs then gives the usual Archimedean formula.
-/

open MeasureTheory Set Filter Real
open scoped unitInterval ENNReal BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

private theorem expMeasure_Ici {t : ℝ} (ht : 0 ≤ t) :
    expMeasure 1 (Ici t) = ENNReal.ofReal (exp (-t)) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let : NullSingletonClass (expMeasure 1) := by unfold expMeasure gammaMeasure; infer_instance
  rw [← measure_congr Ioi_ae_eq_Ici, ← compl_Iic,
    prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq zero_lt_one, if_pos ht, one_mul,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by
      have : exp (-t) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      linarith)]
  congr 1
  ring

/-- Joint lower tails of any selected negative exponential/gamma ratios. -/
theorem claytonLaw_lowerTail (θ : ℝ) (hθ : 0 < θ) (s : Finset (Fin d))
    (t : Fin d → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    (claytonLaw d θ hθ).toMeasure {x | ∀ i ∈ s, x i ≤ -t i} =
      ENNReal.ofReal ((1 + ∑ i ∈ s, t i) ^ (-θ⁻¹)) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure (gammaMeasure θ⁻¹ 1) :=
    isProbabilityMeasure_gammaMeasure (inv_pos.mpr hθ) zero_lt_one
  have hm : Measurable (fun p : (Fin d → ℝ) × ℝ => fun i => -(p.1 i / p.2)) := by fun_prop
  have hs : MeasurableSet {x : Fin d → ℝ | ∀ i ∈ s, x i ≤ -t i} := by measurability
  change ((Measure.pi fun _ : Fin d => expMeasure 1).prod (gammaMeasure θ⁻¹ 1)).map
      (fun p i => -(p.1 i / p.2)) {x | ∀ i ∈ s, x i ≤ -t i} = _
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm)]
  rw [← lintegral_exp_neg_gammaMeasure (inv_pos.mpr hθ) (Finset.sum_nonneg ht)]
  apply lintegral_congr_ae
  filter_upwards [ae_pos_gammaMeasure θ⁻¹ 1] with g hg
  have he : {x : Fin d → ℝ | ∀ i ∈ s, -(x i / g) ≤ -t i} =
      Set.pi univ (fun i => if i ∈ s then Ici (t i * g) else univ) := by
    ext x
    simp only [mem_ofPred_eq, neg_le_neg_iff, le_div_iff₀ hg, mem_pi, mem_univ,
      forall_const]
    constructor
    · intro hx i
      split_ifs with hi
      · exact hx i hi
      · trivial
    · intro hx i hi
      simpa [hi] using hx i
  change (Measure.pi fun _ : Fin d => expMeasure 1)
      {x | ∀ i ∈ s, -(x i / g) ≤ -t i} = _
  rw [he, Measure.pi_pi]
  have hp (i : Fin d) : expMeasure 1 (if i ∈ s then Ici (t i * g) else univ) =
      if i ∈ s then ENNReal.ofReal (exp (-(t i * g))) else 1 := by
    split_ifs with hi
    · exact expMeasure_Ici (mul_nonneg (ht i hi) hg.le)
    · exact measure_univ
  simp_rw [hp]
  rw [Finset.prod_ite_mem_eq, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (exp_pos _).le),
    ← Real.exp_sum, ← Finset.sum_neg_distrib, ← Finset.sum_mul]

/-- The marginal CDF of the negative ratio at a nonpositive argument. -/
theorem cdf_claytonLaw_marginal (θ : ℝ) (hθ : 0 < θ) (i : Fin d)
    {t : ℝ} (ht : 0 ≤ t) :
    ProbabilityTheory.cdf (marginal (claytonLaw d θ hθ) i) (-t) =
      (1 + t) ^ (-θ⁻¹) := by
  rw [ProbabilityTheory.cdf_eq_real, marginal,
    map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic, Measure.real]
  have he : (fun x : Fin d → ℝ => x i) ⁻¹' Iic (-t) =
      {x | ∀ j ∈ ({i} : Finset (Fin d)), x j ≤ -(fun _ => t) j} := by ext x; simp
  rw [he, claytonLaw_lowerTail θ hθ {i} (fun _ => t) (by simpa), Finset.sum_singleton,
    ENNReal.toReal_ofReal (by positivity)]

/-- Joint CDF of the negative exponential/gamma ratios. -/
theorem claytonLaw_real_Iic (θ : ℝ) (hθ : 0 < θ) (t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    (claytonLaw d θ hθ).toMeasure.real (Iic (fun i => -t i)) =
      (1 + ∑ i, t i) ^ (-θ⁻¹) := by
  have he : Iic (fun i => -t i) = {x : Fin d → ℝ | ∀ i ∈ Finset.univ, x i ≤ -t i} := by
    ext x; simp [Pi.le_def]
  rw [Measure.real, he, claytonLaw_lowerTail θ hθ Finset.univ t (fun i _ => ht i),
    ENNReal.toReal_ofReal (by positivity)]

/-- The explicit Clayton CDF when every coordinate is positive. -/
theorem cdf_clayton_of_pos (θ : ℝ) (hθ : 0 < θ) (u : Fin d → I)
    (hu : ∀ i, 0 < (u i : ℝ)) :
    (clayton d θ hθ).cdf u =
      (1 + ∑ i, ((u i : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹) := by
  let t : Fin d → ℝ := fun i => (u i : ℝ) ^ (-θ) - 1
  have ht (i : Fin d) : 0 ≤ t i := by
    exact sub_nonneg.mpr (Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (hu i) (u i).property.2 (neg_nonpos.mpr hθ.le))
  have hinv (i : Fin d) : (1 + t i) ^ (-θ⁻¹) = (u i : ℝ) := by
    dsimp [t]
    rw [show 1 + ((u i : ℝ) ^ (-θ) - 1) = (u i : ℝ) ^ (-θ) by ring,
      ← Real.rpow_mul (hu i).le]
    simp [hθ.ne']
  have he : marginalTransform (claytonLaw d θ hθ) (fun i => -t i) = u := by
    funext i
    apply Subtype.ext
    change ProbabilityTheory.cdf (marginal (claytonLaw d θ hθ) i) (-t i) = (u i : ℝ)
    rw [cdf_claytonLaw_marginal θ hθ i (ht i), hinv]
  calc
    _ = (clayton d θ hθ).cdf (marginalTransform (claytonLaw d θ hθ) (fun i => -t i)) :=
      congrArg (clayton d θ hθ).cdf he.symm
    _ = (claytonLaw d θ hθ).toMeasure.real (Iic (fun i => -t i)) :=
      isSklarCopula_clayton d θ hθ _
    _ = _ := claytonLaw_real_Iic θ hθ t ht

/-- The familiar sum-minus-dimension form of the positive-coordinate Clayton CDF. -/
theorem cdf_clayton (θ : ℝ) (hθ : 0 < θ) (u : Fin d → I)
    (hu : ∀ i, 0 < (u i : ℝ)) :
    (clayton d θ hθ).cdf u =
      (∑ i, (u i : ℝ) ^ (-θ) - (d : ℝ) + 1) ^ (-1 / θ) := by
  rw [cdf_clayton_of_pos θ hθ u hu, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1 <;> ring

/-- The Clayton CDF vanishes on every lower face of the cube. -/
theorem cdf_clayton_of_zero (θ : ℝ) (hθ : 0 < θ) (u : Fin d → I)
    (i : Fin d) (hi : u i = 0) : (clayton d θ hθ).cdf u = 0 :=
  (clayton d θ hθ).cdf_eq_zero_of_coord_eq_zero u i hi

end ProbabilityTheory.Copula
