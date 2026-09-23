/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Clayton
import Mathlib.Analysis.Convex.Piecewise

/-! # Conditional decreasingness for negative Clayton copulas

The proof extends convexity of each positive CDF section across the truncation
point where that section vanishes. Archimedean symmetry supplies the other
direction.
-/

open Real Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private noncomputable def nsec (p k u : ℝ) : ℝ :=
  u * (1 - k * u ^ (-p)) ^ (1 / p)

private theorem nsec_deriv (p k u : ℝ) (hp : 0 < p)
    (hu : 0 < u) (hb : 0 < 1 - k * u ^ (-p)) :
    HasDerivAt (nsec p k) ((1 - k * u ^ (-p)) ^ (1 / p - 1)) u := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ (-p)) ((-p) * u ^ (-p - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hbase : HasDerivAt (fun t : ℝ => 1 - k * t ^ (-p))
      (-k * (-p) * u ^ (-p - 1)) u := by
    convert (hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_const u k).mul hpow) using 1; ring
  have hrpow : HasDerivAt (fun t : ℝ => (1 - k * t ^ (-p)) ^ (1 / p))
      ((-k * (-p) * u ^ (-p - 1)) * (1 / p) *
        (1 - k * u ^ (-p)) ^ (1 / p - 1)) u := by
    convert hbase.rpow_const (Or.inl hb.ne') using 1
  have hm := (hasDerivAt_id u).mul hrpow
  convert hm using 1
  · ext t
    simp [nsec]
  · rw [Real.rpow_sub_one hb.ne']
    simp only [id_eq]
    rw [Real.rpow_sub_one hu.ne']
    field_simp [hp.ne', hu.ne', hb.ne']
    ring
private theorem nep_pow (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    (k ^ (1 / p)) ^ p = k := by
  rw [← Real.rpow_mul hk.le]
  rw [div_mul_cancel₀ 1 hp.ne', Real.rpow_one]

private theorem nsec_base_pos (p k u : ℝ) (hp : 0 < p) (hk : 0 < k)
    (hu : k ^ (1 / p) < u) : 0 < 1 - k * u ^ (-p) := by
  have he : k = (k ^ (1 / p)) ^ p := (nep_pow p k hp hk).symm
  have he0 : 0 < k ^ (1 / p) := Real.rpow_pos_of_pos hk _
  have hpow : (k ^ (1 / p)) ^ p < u ^ p :=
    Real.rpow_lt_rpow he0.le hu hp
  have hu0 : 0 < u := he0.trans hu
  have huinv : 0 < u ^ (-p) := Real.rpow_pos_of_pos hu0 _
  have hid : u ^ p * u ^ (-p) = 1 := by
    rw [← Real.rpow_add hu0]
    simp
  rw [he] at *
  nlinarith [mul_lt_mul_of_pos_right hpow huinv]

private theorem nsec_deriv_monotone (p k : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hk : 0 < k) :
    MonotoneOn (deriv (nsec p k)) (Set.Ioi (k ^ (1 / p))) := by
  intro x hx y hy hxy
  have he0 : 0 < k ^ (1 / p) := Real.rpow_pos_of_pos hk _
  have hx0 : 0 < x := he0.trans hx
  have hy0 : 0 < y := he0.trans hy
  have hbx := nsec_base_pos p k x hp hk hx
  have hby := nsec_base_pos p k y hp hk hy
  rw [(nsec_deriv p k x hp hx0 hbx).deriv,
    (nsec_deriv p k y hp hy0 hby).deriv]
  have hr : y ^ (-p) ≤ x ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hb : 1 - k * x ^ (-p) ≤ 1 - k * y ^ (-p) := by
    nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hr)]
  have hq : 0 ≤ 1 / p - 1 := by
    have h : 1 ≤ 1 / p := (le_div_iff₀ hp).mpr (by linarith)
    linarith
  exact Real.rpow_le_rpow hbx.le hb hq

private theorem nsec_convex (p k : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hk : 0 < k) :
    ConvexOn ℝ (Set.Ici (k ^ (1 / p))) (nsec p k) := by
  have he0 : 0 < k ^ (1 / p) := Real.rpow_pos_of_pos hk _
  have hc : ContinuousOn (nsec p k) (Set.Ici (k ^ (1 / p))) := by
    intro x hx
    have hx0 : 0 < x := he0.trans_le hx
    have hpow : ContinuousAt (fun t : ℝ => t ^ (-p)) x :=
      Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')
    have hbase : ContinuousAt (fun t : ℝ => 1 - k * t ^ (-p)) x := by
      fun_prop
    have hq : 0 ≤ 1 / p := by positivity
    have hroot : ContinuousAt (fun z : ℝ => z ^ (1 / p)) (1 - k * x ^ (-p)) :=
      Real.continuousAt_rpow_const _ _ (Or.inr hq)
    have hr : ContinuousAt (fun t : ℝ => (1 - k * t ^ (-p)) ^ (1 / p)) x := by
      exact show ContinuousAt ((fun z : ℝ => z ^ (1 / p)) ∘
        (fun t : ℝ => 1 - k * t ^ (-p))) x from
        @ContinuousAt.comp ℝ ℝ ℝ _ _ _ (fun t : ℝ => 1 - k * t ^ (-p)) x
          (fun z : ℝ => z ^ (1 / p)) hroot hbase
    exact (continuousAt_id.mul hr).continuousWithinAt
  have hd : DifferentiableOn ℝ (nsec p k) (Set.Ioi (k ^ (1 / p))) := by
    intro x hx
    have hx0 : 0 < x := he0.trans hx
    exact (nsec_deriv p k x hp hx0 (nsec_base_pos p k x hp hk hx)).differentiableAt.differentiableWithinAt
  apply MonotoneOn.convexOn_of_deriv (convex_Ici _) hc
  · simpa only [interior_Ici] using hd
  · simpa only [interior_Ici] using nsec_deriv_monotone p k hp hp1 hk
private theorem nsec_boundary (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    nsec p k (k ^ (1 / p)) = 0 := by
  have he0 : 0 < k ^ (1 / p) := Real.rpow_pos_of_pos hk _
  have hi : (k ^ (1 / p)) ^ p * (k ^ (1 / p)) ^ (-p) = 1 := by
    rw [← Real.rpow_add he0]
    simp
  have hb : 1 - k * (k ^ (1 / p)) ^ (-p) = 0 := by
    nlinarith [nep_pow p k hp hk, hi]
  unfold nsec
  rw [hb]
  exact mul_eq_zero.mpr (Or.inr (Real.zero_rpow (by positivity)))

private theorem nsec_base_nonneg (p k u : ℝ) (hp : 0 < p) (hk : 0 < k)
    (hu : k ^ (1 / p) ≤ u) : 0 ≤ 1 - k * u ^ (-p) := by
  rcases eq_or_lt_of_le hu with he | he
  · subst u
    have hi : (k ^ (1 / p)) ^ p * (k ^ (1 / p)) ^ (-p) = 1 := by
      rw [← Real.rpow_add (Real.rpow_pos_of_pos hk _)]
      simp
    nlinarith [nep_pow p k hp hk, hi]
  · exact (nsec_base_pos p k u hp hk he).le

private theorem nsec_monotone (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    MonotoneOn (nsec p k) (Set.Ici (k ^ (1 / p))) := by
  intro x hx y hy hxy
  have he0 : 0 < k ^ (1 / p) := Real.rpow_pos_of_pos hk _
  have hx0 : 0 < x := he0.trans_le hx
  have hr : y ^ (-p) ≤ x ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hb : 1 - k * x ^ (-p) ≤ 1 - k * y ^ (-p) := by
    nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hr)]
  have hbx := nsec_base_nonneg p k x hp hk hx
  have hby := nsec_base_nonneg p k y hp hk hy
  have hq : 0 ≤ 1 / p := by positivity
  have hpow : (1 - k * x ^ (-p)) ^ (1 / p) ≤
      (1 - k * y ^ (-p)) ^ (1 / p) := Real.rpow_le_rpow hbx hb hq
  unfold nsec
  exact mul_le_mul hxy hpow (Real.rpow_nonneg hbx _) (le_of_lt (he0.trans_le hy))
private theorem nsec_piecewise_convex (p k : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) (hk : 0 < k) :
    ConvexOn ℝ Set.univ
      ((Set.Iic (k ^ (1 / p))).piecewise (fun _ : ℝ => 0) (nsec p k)) := by
  apply convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    (convexOn_const 0 (convex_Iic _)) (nsec_convex p k hp hp1 hk)
  · intro x hx y hy hxy
    exact le_refl _
  · exact nsec_monotone p k hp hk
  · exact (nsec_boundary p k hp hk).symm
private theorem nsec_eq_active (p k u : ℝ) (hp : 0 < p) (hk : 0 < k)
    (hu : k ^ (1 / p) < u) :
    nsec p k u = (u ^ p - k) ^ (1 / p) := by
  have he0 : 0 < k ^ (1 / p) := Real.rpow_pos_of_pos hk _
  have hu0 : 0 < u := he0.trans hu
  have hb := nsec_base_pos p k u hp hk hu
  have hi : u ^ p * u ^ (-p) = 1 := by
    rw [← Real.rpow_add hu0]
    simp
  have hmul : u ^ p * (1 - k * u ^ (-p)) = u ^ p - k := by
    nlinarith
  have hq : (u ^ p) ^ (1 / p) = u := by
    rw [← Real.rpow_mul hu0.le]
    have hprod : p * (1 / p) = 1 := by field_simp
    rw [hprod, Real.rpow_one]
  rw [← hmul, Real.mul_rpow (Real.rpow_nonneg hu0.le _) hb.le, hq]
  rfl
private theorem nsec_piecewise_eq (p k u : ℝ) (hp : 0 < p) (hk : 0 < k)
    (hu0 : 0 ≤ u) :
    (Set.Iic (k ^ (1 / p))).piecewise (fun _ : ℝ => 0) (nsec p k) u =
      (max 0 (u ^ p - k)) ^ (1 / p) := by
  by_cases h : u ≤ k ^ (1 / p)
  · rw [Set.piecewise_eq_of_mem (Set.Iic (k ^ (1 / p))) (fun _ : ℝ => 0) (nsec p k) h]
    have hpow : u ^ p ≤ k := by
      calc
        u ^ p ≤ (k ^ (1 / p)) ^ p := Real.rpow_le_rpow hu0 h hp.le
        _ = k := nep_pow p k hp hk
    have hbase : u ^ p - k ≤ 0 := sub_nonpos.mpr hpow
    rw [max_eq_left hbase, Real.zero_rpow (by positivity)]
  · have hu : k ^ (1 / p) < u := lt_of_not_ge h
    rw [Set.piecewise_eq_of_notMem (Set.Iic (k ^ (1 / p)))
      (fun _ : ℝ => 0) (nsec p k) (by simpa using h)]
    have hpow : k < u ^ p := by
      calc
        k = (k ^ (1 / p)) ^ p := (nep_pow p k hp hk).symm
        _ < u ^ p := Real.rpow_lt_rpow (Real.rpow_nonneg hk.le _) hu hp
    rw [max_eq_right (sub_nonneg.mpr hpow.le)]
    exact nsec_eq_active p k u hp hk hu
private theorem clayton_negative_section (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0)
    (v : I) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (u : I) :
    (claytonNegative θ hθ hn).cdf ![u, v] =
      (Set.Iic ((1 - (v : ℝ) ^ (-θ)) ^ (1 / (-θ)))).piecewise
        (fun _ : ℝ => 0) (nsec (-θ) (1 - (v : ℝ) ^ (-θ))) u := by
  have hp : 0 < -θ := by linarith
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  have hvlt : (v : ℝ) < 1 := lt_of_le_of_ne v.property.2
    (fun h => hv1 (Subtype.ext h))
  have hk : 0 < 1 - (v : ℝ) ^ (-θ) := by
    have hpow : (v : ℝ) ^ (-θ) < 1 := by
      convert Real.rpow_lt_rpow hv.le hvlt hp using 1; simp
    linarith
  rw [nsec_piecewise_eq (-θ) (1 - (v : ℝ) ^ (-θ)) u hp hk u.property.1]
  by_cases hu0 : u = 0
  · subst u
    rw [(claytonNegative θ hθ hn).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl]
    have hpow : (0 : ℝ) ^ (-θ) = 0 := Real.zero_rpow hp.ne'
    rw [Set.Icc.coe_zero, hpow]
    have hm : max 0 (0 - (1 - (v : ℝ) ^ (-θ))) = 0 :=
      max_eq_left (by linarith)
    rw [hm, Real.zero_rpow (by positivity)]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  rw [cdf_claytonNegative θ hθ hn ![u, v] (by
    intro i
    fin_cases i
    · simpa using hu0
    · simpa using hv0)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_div]
  congr 1
  ring_nf
/-- Every admissible negative bivariate Clayton copula is stochastically decreasing in the first coordinate. -/
theorem isSD_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).IsSD := by
  intro a b c v hab hbc
  by_cases hv0 : v = 0
  · subst v
    have hzero (u : I) : (claytonNegative θ hθ hn).cdf ![u, 0] = 0 :=
      (claytonNegative θ hθ hn).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
    simp [hzero]
  by_cases hv1 : v = 1
  · subst v
    simp only [cdf_two_one_right]
    nlinarith
  have hp : 0 < -θ := by linarith
  have hp1 : -θ ≤ 1 := by linarith
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  have hvlt : (v : ℝ) < 1 := lt_of_le_of_ne v.property.2
    (fun h => hv1 (Subtype.ext h))
  have hk : 0 < 1 - (v : ℝ) ^ (-θ) := by
    have hpow : (v : ℝ) ^ (-θ) < 1 := by
      convert Real.rpow_lt_rpow hv.le hvlt hp using 1; simp
    linarith
  rw [clayton_negative_section θ hθ hn v hv0 hv1 a,
    clayton_negative_section θ hθ hn v hv0 hv1 b,
    clayton_negative_section θ hθ hn v hv0 hv1 c]
  by_cases hab_eq : a = b
  · subst b
    simp
  by_cases hbc_eq : b = c
  · subst c
    simp
  have hab' : (a : ℝ) < b := by exact_mod_cast (lt_of_le_of_ne hab hab_eq)
  have hbc' : (b : ℝ) < c := by exact_mod_cast (lt_of_le_of_ne hbc hbc_eq)
  have hf := (nsec_piecewise_convex (-θ) (1 - (v : ℝ) ^ (-θ)) hp hp1 hk).secant_mono_aux1
    (Set.mem_univ _) (Set.mem_univ _) hab' hbc'
  nlinarith

/-- Every admissible negative bivariate Clayton copula is conditionally decreasing in both directions. -/
theorem isCD_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).IsCD :=
  (isArchimedean_claytonNegative θ hθ hn).isCD_iff.mpr
    (isSD_clayton_negative θ hθ hn)
end ProbabilityTheory.Copula
