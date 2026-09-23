/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Clayton.CDF
import Copula.Families.Clayton.Negative
import Copula.Dependence.Basic
import Copula.Dependence.ConditionalMonotonicity
import Copula.Archimedean.Clayton
import Mathlib.Analysis.Convex.Deriv

/-! # Quadrant dependence and conditional increasingness for the Clayton family -/


open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The bivariate Clayton CDF for positive parameters at positive coordinates. -/
theorem cdf_clayton_two_pos (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    (Copula.clayton 2 θ hθ).cdf ![u, v] =
      ((u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1) ^ (-1 / θ) := by
  have h : ∀ i : Fin 2, 0 < (![u, v] i : ℝ) := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  convert Copula.cdf_clayton θ hθ ![u, v] h using 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ring

/-- Positive Clayton parameters are positively quadrant dependent. -/
theorem isPQD_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    (Copula.clayton 2 θ hθ).IsPQD := by
  intro u v
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · simp only [hv0, Set.Icc.coe_zero, mul_zero]
    exact (Copula.clayton 2 θ hθ).cdf_nonneg ![u, 0]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  let x := (u : ℝ) ^ (-θ)
  let y := (v : ℝ) ^ (-θ)
  have hx : 1 ≤ x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hu u.property.2 (neg_nonpos.mpr hθ.le)
  have hy : 1 ≤ y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hv v.property.2 (neg_nonpos.mpr hθ.le)
  have hxy : x + y - 1 ≤ x * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hb : 0 < x + y - 1 := by linarith
  have hpow (w : I) (hw : 0 < (w : ℝ)) :
      ((w : ℝ) ^ (-θ)) ^ (-1 / θ) = (w : ℝ) := by
    rw [← Real.rpow_mul hw.le]
    have he : (-θ) * (-1 / θ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hmult : (x * y) ^ (-1 / θ) = (u : ℝ) * (v : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _),
      hpow u hu, hpow v hv]
  have hr : -1 / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hθ.le
  have hle := Real.rpow_le_rpow_of_nonpos hb hxy hr
  rw [hmult] at hle
  rw [cdf_clayton_two_pos θ hθ u v hu hv]
  exact hle

/-- Every admissible negative bivariate Clayton copula is negatively quadrant dependent. -/
theorem isNQD_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).IsNQD := by
  intro u v
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · subst v
    simp only [Set.Icc.coe_zero, mul_zero]
    rw [(claytonNegative θ hθ hn).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  let x := (u : ℝ) ^ (-θ)
  let y := (v : ℝ) ^ (-θ)
  have hp : 0 < -θ := by linarith
  have hx0 : 0 ≤ x := Real.rpow_nonneg hu.le _
  have hy0 : 0 ≤ y := Real.rpow_nonneg hv.le _
  have hx1 : x ≤ 1 := Real.rpow_le_one hu.le u.property.2 (by linarith)
  have hy1 : y ≤ 1 := Real.rpow_le_one hv.le v.property.2 (by linarith)
  have hxy : x + y - 1 ≤ x * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]
  have hbase : max 0 (x + y - 1) ≤ x * y := max_le (mul_nonneg hx0 hy0) hxy
  have hpow (w : I) (hw : 0 < (w : ℝ)) :
      ((w : ℝ) ^ (-θ)) ^ (-θ)⁻¹ = (w : ℝ) := by
    rw [← Real.rpow_mul hw.le]
    rw [mul_inv_cancel₀ (ne_of_gt hp), Real.rpow_one]
  have hmult : (x * y) ^ (-θ)⁻¹ = (u : ℝ) * (v : ℝ) := by
    rw [Real.mul_rpow hx0 hy0, hpow u hu, hpow v hv]
  have hr : 0 ≤ (-θ)⁻¹ := inv_nonneg.mpr hp.le
  have hle := Real.rpow_le_rpow (by positivity : 0 ≤ max 0 (x + y - 1)) hbase hr
  rw [hmult] at hle
  rw [cdf_claytonNegative θ hθ hn ![u, v] (by
    intro i
    fin_cases i
    · simpa using hu0
    · simpa using hv0)]
  exact hle

open Real

/-- A positive Clayton CDF section, written in a form differentiable at every positive first coordinate. -/
private noncomputable def csec (θ k u : ℝ) : ℝ := u * (1 + k * u ^ θ) ^ (-1 / θ)

private theorem csec_deriv (θ k u : ℝ) (hθ : 0 < θ) (hk : 0 ≤ k) (hu : 0 < u) :
    HasDerivAt (csec θ k) ((1 + k * u ^ θ) ^ (-1 / θ - 1)) u := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ θ) (θ * u ^ (θ - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hbase : HasDerivAt (fun t : ℝ => 1 + k * t ^ θ)
      (k * θ * u ^ (θ - 1)) u := by
    convert (hasDerivAt_const u (1 : ℝ)).add ((hasDerivAt_const u k).mul hpow) using 1; ring
  have hb : 0 < 1 + k * u ^ θ := by positivity
  have hrpow : HasDerivAt (fun t : ℝ => (1 + k * t ^ θ) ^ (-1 / θ))
      ((k * θ * u ^ (θ - 1)) * (-1 / θ) * (1 + k * u ^ θ) ^ (-1 / θ - 1)) u := by
    convert hbase.rpow_const (Or.inl hb.ne') using 1
  have hm := (hasDerivAt_id u).mul hrpow
  convert hm using 1
  · ext t
    simp [csec]
  · rw [Real.rpow_sub_one hb.ne']
    simp only [id_eq]
    rw [Real.rpow_sub_one hu.ne']
    field_simp [hu.ne', hb.ne']
    ring
private theorem csec_antitone_deriv (θ k : ℝ) (hθ : 0 < θ) (hk : 0 ≤ k) :
    AntitoneOn (deriv (csec θ k)) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  rw [(csec_deriv θ k x hθ hk hx.1).deriv,
    (csec_deriv θ k y hθ hk hy.1).deriv]
  have hp : x ^ θ ≤ y ^ θ := Real.rpow_le_rpow hx.1.le hxy hθ.le
  have hb : 1 + k * x ^ θ ≤ 1 + k * y ^ θ := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hp)]
  have hbx : 0 < 1 + k * x ^ θ := by
    have hxpow : 0 ≤ x ^ θ := Real.rpow_nonneg hx.1.le _
    nlinarith [mul_nonneg hk hxpow]
  have he : -1 / θ - 1 ≤ 0 := by
    have hh : -1 / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hθ.le
    linarith
  exact Real.rpow_le_rpow_of_nonpos hbx hb he

private theorem csec_concave (θ k : ℝ) (hθ : 0 < θ) (hk : 0 ≤ k) :
    ConcaveOn ℝ (Set.Icc 0 1) (csec θ k) := by
  have hc : ContinuousOn (csec θ k) (Set.Icc 0 1) := by
    intro x hx
    have hp : ContinuousAt (fun t : ℝ => t ^ θ) x :=
      Real.continuousAt_rpow_const x θ (Or.inr hθ.le)
    have hbx : 0 < 1 + k * x ^ θ := by
      have hxpow : 0 ≤ x ^ θ := Real.rpow_nonneg hx.1 _
      nlinarith [mul_nonneg hk hxpow]
    have hb : ContinuousAt (fun t : ℝ => 1 + k * t ^ θ) x := by
      fun_prop
    have hr : ContinuousAt (fun t : ℝ => (1 + k * t ^ θ) ^ (-1 / θ)) x := by
      have hroot : ContinuousAt (fun z : ℝ => z ^ (-1 / θ)) (1 + k * x ^ θ) :=
        Real.continuousAt_rpow_const _ _ (Or.inl hbx.ne')
      exact show ContinuousAt ((fun z : ℝ => z ^ (-1 / θ)) ∘ (fun t : ℝ => 1 + k * t ^ θ)) x from @ContinuousAt.comp ℝ ℝ ℝ _ _ _ (fun t : ℝ => 1 + k * t ^ θ) x (fun z : ℝ => z ^ (-1 / θ)) hroot hb
    exact (continuousAt_id.mul hr).continuousWithinAt
  have hd : DifferentiableOn ℝ (csec θ k) (Set.Ioo 0 1) := by
    intro x hx
    exact (csec_deriv θ k x hθ hk hx.1).differentiableAt.differentiableWithinAt
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1) hc
  · simpa only [interior_Icc] using hd
  · simpa only [interior_Icc] using csec_antitone_deriv θ k hθ hk
private theorem csec_eq_alt (θ k u : ℝ) (hθ : 0 < θ) (hk : 0 ≤ k) (hu : 0 < u) :
    csec θ k u = (u ^ (-θ) + k) ^ (-1 / θ) := by
  have hq : 0 < u ^ θ := Real.rpow_pos_of_pos hu _
  have hp : 0 < u ^ (-θ) := Real.rpow_pos_of_pos hu _
  have hb : 0 ≤ u ^ (-θ) + k := by linarith
  have hmul : u ^ θ * (u ^ (-θ) + k) = 1 + k * u ^ θ := by
    have hc : u ^ θ * u ^ (-θ) = 1 := by
      rw [← Real.rpow_add hu]
      simp
    nlinarith
  have he : (u ^ θ) ^ (-1 / θ) = u⁻¹ := by
    rw [← Real.rpow_mul hu.le]
    have hprod : θ * (-1 / θ) = -1 := by field_simp
    rw [hprod, Real.rpow_neg_one]
  unfold csec
  rw [← hmul, Real.mul_rpow hq.le hb, he]
  field_simp [hu.ne']

private theorem clayton_cdf_eq_csec (θ : ℝ) (hθ : 0 < θ) (v : I)
    (hv0 : v ≠ 0) (u : I) :
    (clayton 2 θ hθ).cdf ![u, v] = csec θ ((v : ℝ) ^ (-θ) - 1) u := by
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  have hk : 0 ≤ (v : ℝ) ^ (-θ) - 1 := sub_nonneg.mpr
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv v.property.2 (by linarith))
  by_cases hu0 : u = 0
  · subst u
    simp [csec]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  rw [cdf_clayton_two_pos θ hθ u v hu hv]
  rw [csec_eq_alt θ _ _ hθ hk hu]
  congr 1
  ring

private theorem csec_chord (θ k : ℝ) (hθ : 0 < θ) (hk : 0 ≤ k)
    (a b c : I) (hab : a ≤ b) (hbc : b ≤ c) :
    ((b : ℝ) - (a : ℝ)) * csec θ k c +
      ((c : ℝ) - (b : ℝ)) * csec θ k a ≤
        ((c : ℝ) - (a : ℝ)) * csec θ k b := by
  by_cases hab_eq : a = b
  · subst b
    simp
  by_cases hbc_eq : b = c
  · subst c
    simp
  have hab' : (a : ℝ) < b := by exact_mod_cast (lt_of_le_of_ne hab hab_eq)
  have hbc' : (b : ℝ) < c := by exact_mod_cast (lt_of_le_of_ne hbc hbc_eq)
  have hf := (csec_concave θ k hθ hk).neg.secant_mono_aux1
    a.property c.property hab' hbc'
  simp only [Pi.neg_apply] at hf
  nlinarith
/-- Every positive bivariate Clayton copula is stochastically increasing in the first coordinate. -/
theorem isSI_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).IsSI := by
  intro a b c v hab hbc
  by_cases hv0 : v = 0
  · subst v
    have hzero (u : I) : (clayton 2 θ hθ).cdf ![u, 0] = 0 :=
      (clayton 2 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
    simp [hzero]
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  have hk : 0 ≤ (v : ℝ) ^ (-θ) - 1 := sub_nonneg.mpr
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv v.property.2 (by linarith))
  rw [clayton_cdf_eq_csec θ hθ v hv0 a,
    clayton_cdf_eq_csec θ hθ v hv0 b,
    clayton_cdf_eq_csec θ hθ v hv0 c]
  exact csec_chord θ _ hθ hk a b c hab hbc

/-- Every positive bivariate Clayton copula is conditionally increasing in both directions. -/
theorem isCI_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).IsCI :=
  (isArchimedean_clayton 2 θ hθ).isCI_iff.mpr (isSI_clayton_positive θ hθ)
end ProbabilityTheory.Copula
