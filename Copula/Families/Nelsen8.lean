/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Truncated
import Copula.Order.Orthant

/-! # The Nelsen 8 bivariate copula

A rational non-strict Archimedean generator is valid for θ ≥ 1. The printed
CDF holds on the entire closed square, and θ = 1 gives the lower Fréchet bound.
-/

open Set
open scoped unitInterval
namespace ProbabilityTheory.Copula

private theorem n8_jensen (θ x y a b : ℝ) (hθ : 1 ≤ θ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    (1 - (a*x+b*y)) / (1+(θ-1)*(a*x+b*y)) ≤
      a*((1-x)/(1+(θ-1)*x)) + b*((1-y)/(1+(θ-1)*y)) := by
  let k := θ - 1
  have hk : 0 ≤ k := by dsimp [k]; linarith
  have hdx : 0 < 1+k*x := by positivity
  have hdy : 0 < 1+k*y := by positivity
  have hdz : 0 < 1+k*(a*x+b*y) := by positivity
  have hid : a*((1-x)/(1+k*x)) + b*((1-y)/(1+k*y)) -
      (1-(a*x+b*y))/(1+k*(a*x+b*y)) =
      θ*k*a*b*(x-y)^2 / ((1+k*x)*(1+k*y)*(1+k*(a*x+b*y))) := by
    have hb' : b = 1-a := by linarith
    subst b
    have hθk : θ = k + 1 := by dsimp [k]; ring
    rw [hθk]
    field_simp [ne_of_gt hdx, ne_of_gt hdy, ne_of_gt hdz]
    ring
  have hrhs : 0 ≤ θ*k*a*b*(x-y)^2 /
      ((1+k*x)*(1+k*y)*(1+k*(a*x+b*y))) := by positivity
  dsimp [k] at hid ⊢
  linarith


private theorem n8_ratio_antitone (θ x y : ℝ) (hθ : 1 ≤ θ)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1-y)/(1+(θ-1)*y) ≤ (1-x)/(1+(θ-1)*x) := by
  have hk : 0 ≤ θ-1 := by linarith
  have hdx : 0 < 1+(θ-1)*x := by positivity
  have hy : 0 ≤ y := le_trans hx hxy
  have hdy : 0 < 1+(θ-1)*y := by positivity
  apply (div_le_div_iff₀ hdy hdx).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : 0 ≤ θ)]

noncomputable def nelsen8Generator (θ : ℝ) (hθ : 1 ≤ θ) : BivariateGenerator where
  toFun t := max 0 ((1-t)/(1+(θ-1)*t))
  invFun u := (1-(u:ℝ))/(1+(θ-1)*(u:ℝ))
  nonneg _ _ := le_max_left _ _
  antitone := by
    intro x hx y hy hxy
    exact max_le_max le_rfl (n8_ratio_antitone θ x y hθ hx hxy)
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    apply max_le
    · positivity
    · have hr := n8_jensen θ x y a b hθ hx hy ha hb hab
      have hx' := le_max_right 0 ((1-x)/(1+(θ-1)*x))
      have hy' := le_max_right 0 ((1-y)/(1+(θ-1)*y))
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'),
        mul_nonneg hb (sub_nonneg.mpr hy')]
  inv_nonneg u _ := by
    have hk : 0 ≤ θ-1 := by linarith
    have hd : 0 < 1+(θ-1)*(u:ℝ) := by nlinarith [mul_nonneg hk u.property.1]
    exact div_nonneg (sub_nonneg.mpr u.property.2) hd.le
  inv_antitone u v _ huv := by
    exact n8_ratio_antitone θ (u:ℝ) (v:ℝ) hθ u.property.1 huv
  inv_one := by norm_num
  right_inv u _ := by
    have hk : 0 ≤ θ-1 := by linarith
    have hdu : 0 < 1+(θ-1)*(u:ℝ) := by nlinarith [mul_nonneg hk u.property.1]
    let d : ℝ := 1+(θ-1)*(u:ℝ)
    have hd : d ≠ 0 := ne_of_gt hdu
    have hphi : 0 ≤ (1-(u:ℝ))/(1+(θ-1)*(u:ℝ)) :=
      div_nonneg (sub_nonneg.mpr u.property.2) hdu.le
    have hdp : 0 < 1+(θ-1)*((1-(u:ℝ))/(1+(θ-1)*(u:ℝ))) := by positivity
    change max 0 ((1-((1-(u:ℝ))/(1+(θ-1)*(u:ℝ)))) /
      (1+(θ-1)*((1-(u:ℝ))/(1+(θ-1)*(u:ℝ))))) = (u:ℝ)
    have heq : (1-((1-(u:ℝ))/(1+(θ-1)*(u:ℝ)))) /
      (1+(θ-1)*((1-(u:ℝ))/(1+(θ-1)*(u:ℝ)))) = (u:ℝ) := by
      have hnum : 1-((1-(u:ℝ))/(1+(θ-1)*(u:ℝ))) = θ*(u:ℝ)/(1+(θ-1)*(u:ℝ)) := by
        change 1-(1-(u:ℝ))/d = θ*(u:ℝ)/d
        field_simp [hd]
        dsimp [d]
        ring
      have hden : 1+(θ-1)*((1-(u:ℝ))/(1+(θ-1)*(u:ℝ))) = θ/(1+(θ-1)*(u:ℝ)) := by
        change 1+(θ-1)*((1-(u:ℝ))/d) = θ/d
        field_simp [hd]
        dsimp [d]
        ring
      rw [hnum, hden]
      apply (div_eq_iff (div_ne_zero (by linarith : θ ≠ 0) hdu.ne')).mpr
      ring
    rw [heq, max_eq_right u.property.1]

/-- Nelsen 8 as a valid bivariate Archimedean copula for θ ≥ 1. -/
noncomputable def nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 :=
  (nelsen8Generator θ hθ).copula

theorem isArchimedean_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    IsArchimedean (nelsen8 θ hθ) :=
  (nelsen8Generator θ hθ).isArchimedean

private theorem n8_rational_identity (θ u v : ℝ) (hθ : 1 ≤ θ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    (1 - ((1-u)/(1+(θ-1)*u) + (1-v)/(1+(θ-1)*v))) /
      (1+(θ-1)*((1-u)/(1+(θ-1)*u) + (1-v)/(1+(θ-1)*v))) =
    (θ^2*u*v - (1-u)*(1-v)) /
      (θ^2-(θ-1)^2*(1-u)*(1-v)) := by
  let k := θ-1
  let du := 1+k*u
  let dv := 1+k*v
  let p := (1-u)/du
  let q := (1-v)/dv
  let n := θ^2*u*v - (1-u)*(1-v)
  let d := θ^2-k^2*(1-u)*(1-v)
  have hk : 0 ≤ k := by dsimp [k]; linarith
  have hdu : 0 < du := by dsimp [du]; positivity
  have hdv : 0 < dv := by dsimp [dv]; positivity
  have hp : 0 ≤ p := div_nonneg (by linarith) hdu.le
  have hq : 0 ≤ q := div_nonneg (by linarith) hdv.le
  have hdl : 0 < 1+k*(p+q) := by positivity
  have hn : 1-(p+q) = n/(du*dv) := by
    dsimp [p,q,n]
    field_simp [ne_of_gt hdu, ne_of_gt hdv]
    dsimp [du,dv,k]
    ring
  have hd : 1+k*(p+q) = d/(du*dv) := by
    dsimp [p,q,d]
    field_simp [ne_of_gt hdu, ne_of_gt hdv]
    dsimp [du,dv,k]
    ring
  have hD : d ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hd
    exact (ne_of_gt hdl) hd
  change (1-(p+q))/(1+k*(p+q)) = n/d
  rw [hn, hd]
  field_simp [hD, ne_of_gt hdu, ne_of_gt hdv]

private theorem n8_source_den_pos (θ u v : ℝ) (hθ : 1 ≤ θ)
    (hu : 0 ≤ u) (_hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < θ^2 - (θ-1)^2*(1-u)*(1-v) := by
  have hk : 0 ≤ θ-1 := by linarith
  have huv : (1-u)*(1-v) ≤ 1 := by
    have h : 0 ≤ u*(1-v) := mul_nonneg hu (by linarith)
    nlinarith
  have hmul : (θ-1)^2*((1-u)*(1-v)) ≤ (θ-1)^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left huv (sq_nonneg (θ-1))
  nlinarith [sq_nonneg (θ-1)]

/-- The printed Nelsen 8 CDF on the full closed unit square. -/
theorem nelsen8_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen8 θ hθ).cdf ![u,v] =
      max 0 ((θ^2*(u:ℝ)*(v:ℝ) - (1-(u:ℝ))*(1-(v:ℝ))) /
        (θ^2-(θ-1)^2*(1-(u:ℝ))*(1-(v:ℝ)))) := by
  have hd := n8_source_den_pos θ (u:ℝ) (v:ℝ) hθ
    u.property.1 u.property.2 v.property.1 v.property.2
  rw [nelsen8, BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
  by_cases hu : u = 0
  · subst u
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, true_or, ↓reduceIte]
    have hn : θ^2*(0:ℝ)*(v:ℝ) - (1-(0:ℝ))*(1-(v:ℝ)) ≤ 0 := by
      nlinarith [v.property.2]
    have hq : (θ^2*(↑(0:I):ℝ)*(v:ℝ) - (1-(↑(0:I):ℝ))*(1-(v:ℝ))) /
        (θ^2-(θ-1)^2*(1-(↑(0:I):ℝ))*(1-(v:ℝ))) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by simpa using hn) hd.le
    simpa using (max_eq_left hq).symm
  by_cases hv : v = 0
  · subst v
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu, or_true, ↓reduceIte]
    have hn : θ^2*(u:ℝ)*(0:ℝ) - (1-(u:ℝ))*(1-(0:ℝ)) ≤ 0 := by
      nlinarith [u.property.2]
    have hq : (θ^2*(u:ℝ)*(↑(0:I):ℝ) - (1-(u:ℝ))*(1-(↑(0:I):ℝ))) /
        (θ^2-(θ-1)^2*(1-(u:ℝ))*(1-(↑(0:I):ℝ))) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by simpa using hn) hd.le
    simpa using (max_eq_left hq).symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ↓reduceIte]
  change max 0 ((1-((1-(u:ℝ))/(1+(θ-1)*(u:ℝ)) +
      (1-(v:ℝ))/(1+(θ-1)*(v:ℝ)))) /
    (1+(θ-1)*((1-(u:ℝ))/(1+(θ-1)*(u:ℝ)) +
      (1-(v:ℝ))/(1+(θ-1)*(v:ℝ))))) = _
  rw [n8_rational_identity θ (u:ℝ) (v:ℝ) hθ
    u.property.1 u.property.2 v.property.1 v.property.2]

/-- Nelsen 8 starts at the lower Fréchet copula. -/
@[simp] theorem nelsen8_one : nelsen8 1 le_rfl = countermonotonic := by
  apply ext_cdf
  intro z
  have hz : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [hz, nelsen8_cdf_full, cdf_countermonotonic]
  norm_num
  congr 1; ring

/-- Nelsen 8 increases in lower-orthant order with its parameter. -/
theorem lowerOrthantLE_nelsen8 {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η)
    (hθη : θ ≤ η) : (nelsen8 θ hθ).LowerOrthantLE (nelsen8 η hη) := by
  intro z
  have hz : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [hz, nelsen8_cdf_full, nelsen8_cdf_full]
  apply max_le_max le_rfl
  let u : ℝ := z 0
  let v : ℝ := z 1
  let p : ℝ := u * v
  let a : ℝ := (1-u)*(1-v)
  have hu : 0 ≤ u := (z 0).property.1
  have hu1 : u ≤ 1 := (z 0).property.2
  have hv : 0 ≤ v := (z 1).property.1
  have hv1 : v ≤ 1 := (z 1).property.2
  have hp : 0 ≤ p := mul_nonneg hu hv
  have ha : 0 ≤ a := mul_nonneg (by linarith) (by linarith)
  have ha1 : a ≤ 1 := by
    have h := mul_nonneg hu (by linarith : 0 ≤ 1-v)
    dsimp [a]
    nlinarith
  have hDθ : 0 < θ^2-(θ-1)^2*a := by
    simpa only [a, mul_assoc] using n8_source_den_pos θ u v hθ hu hu1 hv hv1
  have hDη : 0 < η^2-(η-1)^2*a := by
    simpa only [a, mul_assoc] using n8_source_den_pos η u v hη hu hu1 hv hv1
  simp only [mul_assoc]
  change (θ^2*p-a)/(θ^2-(θ-1)^2*a) ≤
    (η^2*p-a)/(η^2-(η-1)^2*a)
  apply (div_le_div_iff₀ hDθ hDη).mpr
  have hA : 0 ≤ 2*θ*η-θ-η := by
    have h1 := mul_nonneg (by linarith : 0 ≤ θ) (by linarith : 0 ≤ η-1)
    have h2 := mul_nonneg (by linarith : 0 ≤ η) (by linarith : 0 ≤ θ-1)
    nlinarith
  have hB : 0 ≤ θ+η-a*(θ+η-2) := by
    have h := mul_nonneg (sub_nonneg.mpr ha1)
      (by linarith : 0 ≤ θ+η-2)
    nlinarith
  have hbr : 0 ≤ p*(2*θ*η-θ-η) + θ+η-a*(θ+η-2) := by
    nlinarith [mul_nonneg hp hA, hB]
  have hfact : (η^2*p-a)*(θ^2-(θ-1)^2*a) -
      (θ^2*p-a)*(η^2-(η-1)^2*a) =
      a*(η-θ)*(p*(2*θ*η-θ-η) + θ+η-a*(θ+η-2)) := by ring
  nlinarith [mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hθη)) hbr]

end ProbabilityTheory.Copula
