/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical.Bivariate
import Copula.Symmetry
import Copula.Rank.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # The Plackett family

Plackett's family of copulas (R. L. Plackett, *A class of bivariate distributions*,
J. Amer. Statist. Assoc. 60 (1965); Nelsen 2006, §3.3.1, (3.3.3)): for `θ > 0`, `θ ≠ 1`,

`C_θ(u,v) = ([1 + (θ-1)(u+v)] - √([1 + (θ-1)(u+v)]² - 4uvθ(θ-1))) / (2(θ-1))`,

and `C_1 = Π`. Main results:

* a derivative criterion for two-increasingness (`rectangle_nonneg_of_hasDerivAt`): if every
  vertical section `v ↦ F(u,v)` has derivative `g(u,v)` on `(0,1)` and `g(·,v)` is
  nondecreasing, then all rectangle increments of `F` are nonnegative;
* the discriminant `[1 + (θ-1)(u+v)]² - 4uvθ(θ-1)` is positive on the closed unit square
  (`plackettDisc_pos`), the partial derivative
  `∂C_θ/∂v = (1 - (1 + (θ-1)(u+v) - 2θu)/√disc) / 2` is nondecreasing in `u` (its
  `u`-derivative is the Plackett density `θ(1 + (θ-1)(u+v-2uv)) / disc^{3/2} > 0`,
  `hasDerivAt_plackettDeriv_left`, `plackettDensity_pos`), hence
  `C_θ` is a copula for every `θ > 0` (`plackett`);
* `C_1 = Π` (`plackett_one`), and the defining *constant cross-product ratio* property
  `C(1 - u - v + C) = θ (u - C)(v - C)` (`plackett_cross_ratio`), i.e.
  `P(U ≤ u, V ≤ v) P(U > u, V > v) = θ P(U ≤ u, V > v) P(U > u, V ≤ v)`;
* exchangeability and radial symmetry (`isExchangeable_plackett`, `isRadiallySymmetric_plackett`);
* Blomqvist's `β(C_θ) = (√θ - 1)/(√θ + 1)` (`blomqvistBeta_plackett`).

The concordance ordering in `θ` and the limits `M`, `W` are in `Copula.Families.Plackett.Order`,
Spearman's rho in `Copula.Families.Plackett.Spearman`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ## A derivative criterion for two-increasingness -/

/-- If each vertical section `v ↦ F(u,v)` (for `u ∈ [0,1]`) is continuous on `[0,1]` with
derivative `g(u,v)` on `(0,1)`, and each `u ↦ g(u,v)` is nondecreasing on `[0,1]`, then `F` has
nonnegative rectangle increments on the unit square. -/
theorem rectangle_nonneg_of_hasDerivAt {F g : ℝ → ℝ → ℝ}
    (hcont : ∀ u ∈ Icc (0 : ℝ) 1, ContinuousOn (F u) (Icc 0 1))
    (hder : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt (F u) (g u v) v)
    (hmono : ∀ v ∈ Ioo (0 : ℝ) 1, MonotoneOn (fun u => g u v) (Icc 0 1))
    {a b c e : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hc : 0 ≤ c) (hce : c ≤ e)
    (he : e ≤ 1) : 0 ≤ F b e - F a e - F b c + F a c := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have hsub : Icc c e ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hc he
  have hmon : MonotoneOn (fun v => F b v - F a v) (Icc c e) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c e)
    · exact ((hcont b hbI).sub (hcont a haI)).mono hsub
    · intro v hv
      rw [interior_Icc] at hv
      have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨hc.trans_lt hv.1, hv.2.trans_le he⟩
      exact ((hder b hbI v hv').sub (hder a haI v hv')).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨hc.trans_lt hv.1, hv.2.trans_le he⟩
      have hd : HasDerivAt (fun v => F b v - F a v) (g b v - g a v) v :=
        (hder b hbI v hv').sub (hder a haI v hv')
      rw [hd.deriv]
      exact sub_nonneg.mpr (hmono v hv' haI hbI hab)
  have h := hmon ⟨le_rfl, hce⟩ ⟨hce, le_rfl⟩ hce
  simp only at h
  linarith

/-! ## The Plackett formula -/

/-- The linear term `1 + (θ - 1)(u + v)` of the Plackett formula. -/
def plackettLinear (θ u v : ℝ) : ℝ := 1 + (θ - 1) * (u + v)

/-- The discriminant `[1 + (θ-1)(u+v)]² - 4uvθ(θ-1)` of the Plackett formula. -/
def plackettDisc (θ u v : ℝ) : ℝ := plackettLinear θ u v ^ 2 - 4 * θ * (θ - 1) * u * v

/-- The Plackett CDF formula (Nelsen (3.3.3)); `Π` for `θ = 1`. -/
noncomputable def plackettCDF (θ u v : ℝ) : ℝ :=
  if θ = 1 then u * v else (plackettLinear θ u v - √(plackettDisc θ u v)) / (2 * (θ - 1))

theorem plackettLinear_comm (θ u v : ℝ) : plackettLinear θ u v = plackettLinear θ v u := by
  unfold plackettLinear; ring

theorem plackettDisc_comm (θ u v : ℝ) : plackettDisc θ u v = plackettDisc θ v u := by
  unfold plackettDisc; rw [plackettLinear_comm]; ring

theorem plackettCDF_comm (θ u v : ℝ) : plackettCDF θ u v = plackettCDF θ v u := by
  unfold plackettCDF; rw [plackettLinear_comm, plackettDisc_comm, mul_comm u v]

theorem plackettDisc_eq (θ u v : ℝ) : plackettDisc θ u v =
    1 + 2 * (θ - 1) * (u + v - 2 * u * v) + (θ - 1) ^ 2 * (u - v) ^ 2 := by
  unfold plackettDisc plackettLinear; ring

/-- The Plackett discriminant is positive on the closed unit square. -/
theorem plackettDisc_pos {θ u v : ℝ} (hθ : 0 < θ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : 0 < plackettDisc θ u v := by
  rw [plackettDisc_eq]
  have h1 := mul_nonneg hu0 (sub_nonneg.mpr hv1)
  have h2 := mul_nonneg hv0 (sub_nonneg.mpr hu1)
  have hw : 0 ≤ u + v - 2 * u * v := by nlinarith
  have hw1 : 2 * (u + v - 2 * u * v) ≤ 1 + (u - v) ^ 2 := by nlinarith [sq_nonneg (1 - u - v)]
  have hd1 : (u - v) ^ 2 ≤ 1 := by nlinarith
  rcases le_or_gt 1 θ with h | h
  · nlinarith [sq_nonneg ((θ - 1) * (u - v)), mul_nonneg (sub_nonneg.mpr h) hw]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h.le) (sub_nonneg.mpr hw1),
      mul_nonneg (mul_nonneg hθ.le (sub_nonneg.mpr h.le)) (sub_nonneg.mpr hd1), mul_pos hθ hθ]

theorem plackettDisc_zero_left (θ v : ℝ) :
    plackettDisc θ 0 v = (1 + (θ - 1) * v) ^ 2 := by
  unfold plackettDisc plackettLinear; ring

theorem plackettDisc_one_left (θ v : ℝ) :
    plackettDisc θ 1 v = (θ - (θ - 1) * v) ^ 2 := by
  unfold plackettDisc plackettLinear; ring

theorem plackettCDF_zero_left {θ : ℝ} (hθ : 0 < θ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    plackettCDF θ 0 v = 0 := by
  unfold plackettCDF
  split_ifs with h
  · simp
  · rw [plackettDisc_zero_left, Real.sqrt_sq (by nlinarith)]
    unfold plackettLinear; simp

theorem plackettCDF_one_left {θ : ℝ} (hθ : 0 < θ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    plackettCDF θ 1 v = v := by
  unfold plackettCDF
  split_ifs with h
  · simp
  · rw [plackettDisc_one_left, Real.sqrt_sq (by nlinarith)]
    unfold plackettLinear
    have : θ - 1 ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring

/-- The quadratic equation `(θ - 1) C² - [1 + (θ-1)(u+v)] C + θuv = 0` satisfied by the
Plackett formula on the unit square. -/
theorem plackettCDF_quadratic {θ u v : ℝ} (hθ : 0 < θ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (θ - 1) * plackettCDF θ u v ^ 2 - plackettLinear θ u v * plackettCDF θ u v
      + θ * u * v = 0 := by
  unfold plackettCDF
  split_ifs with h
  · subst h; unfold plackettLinear; ring
  · have hD := plackettDisc_pos hθ hu0 hu1 hv0 hv1
    have hs := Real.sq_sqrt hD.le
    have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr h
    have hdef : plackettDisc θ u v = plackettLinear θ u v ^ 2 - 4 * θ * (θ - 1) * u * v := rfl
    field_simp
    linear_combination hs + hdef

/-! ## Derivatives -/

/-- The partial derivative `∂C_θ/∂v = (1 - (1 + (θ-1)(u+v) - 2θu)/√disc) / 2` of the Plackett
formula (`θ ≠ 1`). -/
noncomputable def plackettDeriv (θ u v : ℝ) : ℝ :=
  (1 - (plackettLinear θ u v - 2 * θ * u) / √(plackettDisc θ u v)) / 2

theorem hasDerivAt_plackettLinear_right (θ u v : ℝ) :
    HasDerivAt (fun y => plackettLinear θ u y) (θ - 1) v := by
  unfold plackettLinear
  have := (((hasDerivAt_id v).const_add u).const_mul (θ - 1)).const_add 1
  simpa using this

theorem hasDerivAt_plackettDisc_right (θ u v : ℝ) :
    HasDerivAt (fun y => plackettDisc θ u y)
      (2 * plackettLinear θ u v * (θ - 1) - 4 * θ * (θ - 1) * u) v := by
  unfold plackettDisc
  have h : HasDerivAt (fun y => plackettLinear θ u y ^ 2 - 4 * θ * (θ - 1) * u * y)
      ((2 : ℕ) * plackettLinear θ u v ^ (2 - 1) * (θ - 1) - 4 * θ * (θ - 1) * u * 1) v :=
    ((hasDerivAt_plackettLinear_right θ u v).pow 2).sub
      ((hasDerivAt_id' v).const_mul (4 * θ * (θ - 1) * u))
  convert h using 1
  push_cast; ring

theorem hasDerivAt_plackettLinear_left (θ u v : ℝ) :
    HasDerivAt (fun x => plackettLinear θ x v) (θ - 1) u := by
  have h : (fun x => plackettLinear θ x v) = fun x => plackettLinear θ v x :=
    funext fun x => plackettLinear_comm θ x v
  rw [h]; exact hasDerivAt_plackettLinear_right θ v u

theorem hasDerivAt_plackettDisc_left (θ u v : ℝ) :
    HasDerivAt (fun x => plackettDisc θ x v)
      (2 * plackettLinear θ u v * (θ - 1) - 4 * θ * (θ - 1) * v) u := by
  have h : (fun x => plackettDisc θ x v) = fun x => plackettDisc θ v x :=
    funext fun x => plackettDisc_comm θ x v
  rw [h, plackettLinear_comm]; exact hasDerivAt_plackettDisc_right θ v u

theorem plackettCDF_eq_of_ne {θ : ℝ} (hθ : θ ≠ 1) (u v : ℝ) :
    plackettCDF θ u v = (plackettLinear θ u v - √(plackettDisc θ u v)) / (2 * (θ - 1)) := by
  simp [plackettCDF, hθ]

theorem continuous_plackettCDF (θ : ℝ) :
    Continuous (fun p : ℝ × ℝ => plackettCDF θ p.1 p.2) := by
  by_cases hθ : θ = 1
  · simp only [plackettCDF, hθ, ite_true]; fun_prop
  · simp only [plackettCDF_eq_of_ne hθ, plackettLinear, plackettDisc]; fun_prop

theorem hasDerivAt_plackettCDF_right {θ u v : ℝ} (hθ : θ ≠ 1) (hD : 0 < plackettDisc θ u v) :
    HasDerivAt (fun y => plackettCDF θ u y) (plackettDeriv θ u v) v := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have hs := (hasDerivAt_plackettDisc_right θ u v).sqrt hD.ne'
  have := ((hasDerivAt_plackettLinear_right θ u v).sub hs).div_const (2 * (θ - 1))
  have hfun : (fun y => plackettCDF θ u y) =
      fun y => (plackettLinear θ u y - √(plackettDisc θ u y)) / (2 * (θ - 1)) :=
    funext fun y => plackettCDF_eq_of_ne hθ u y
  rw [hfun]
  convert this using 1
  unfold plackettDeriv
  have hr : 0 < √(plackettDisc θ u v) := Real.sqrt_pos.mpr hD
  field_simp
  ring

/-- The `u`-derivative of `(1 + (θ-1)(u+v) - 2θu)/√disc`: it equals
`-2θ(1 + (θ-1)(u+v-2uv)) / disc^{3/2}`, minus twice the Plackett density. -/
theorem hasDerivAt_plackettRatio_left {θ u v : ℝ} (hD : 0 < plackettDisc θ u v) :
    HasDerivAt (fun x => (plackettLinear θ x v - 2 * θ * x) / √(plackettDisc θ x v))
      (-2 * θ * (1 + (θ - 1) * (u + v - 2 * u * v)) /
        (√(plackettDisc θ u v) * plackettDisc θ u v)) u := by
  have hs := (hasDerivAt_plackettDisc_left θ u v).sqrt hD.ne'
  have hr : 0 < √(plackettDisc θ u v) := Real.sqrt_pos.mpr hD
  have ha : HasDerivAt (fun x => plackettLinear θ x v - 2 * θ * x) (θ - 1 - 2 * θ * 1) u :=
    (hasDerivAt_plackettLinear_left θ u v).sub ((hasDerivAt_id' u).const_mul (2 * θ))
  have h := ha.div hs hr.ne'
  convert h using 1
  · simp only [mul_one]
    have hr2 : √(plackettDisc θ u v) ^ 2 = plackettDisc θ u v := Real.sq_sqrt hD.le
    have key : (θ - 1 - 2 * θ) * plackettDisc θ u v - (plackettLinear θ u v - 2 * θ * u) *
        ((2 * plackettLinear θ u v * (θ - 1) - 4 * θ * (θ - 1) * v)) / 2 =
        -2 * θ * (1 + (θ - 1) * (u + v - 2 * u * v)) := by
      unfold plackettDisc plackettLinear; ring
    rw [← key]
    generalize √(plackettDisc θ u v) = r at hr hr2 ⊢
    rw [← hr2]
    field_simp

/-- The Plackett density `c_θ(u,v) = θ(1 + (θ-1)(u+v-2uv)) / disc^{3/2}`. -/
noncomputable def plackettDensity (θ u v : ℝ) : ℝ :=
  θ * (1 + (θ - 1) * (u + v - 2 * u * v)) / (√(plackettDisc θ u v) * plackettDisc θ u v)

/-- The density is the mixed partial derivative: `∂/∂u (∂C_θ/∂v) = c_θ`. -/
theorem hasDerivAt_plackettDeriv_left {θ u v : ℝ} (hD : 0 < plackettDisc θ u v) :
    HasDerivAt (fun x => plackettDeriv θ x v) (plackettDensity θ u v) u := by
  have h := ((hasDerivAt_plackettRatio_left hD).const_sub 1).div_const 2
  unfold plackettDeriv plackettDensity
  convert h using 1
  ring

/-- The Plackett density is positive on the closed unit square. -/
theorem plackettDensity_pos {θ u v : ℝ} (hθ : 0 < θ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : 0 < plackettDensity θ u v := by
  have hD := plackettDisc_pos hθ hu0 hu1 hv0 hv1
  have h1 := mul_nonneg hu0 (sub_nonneg.mpr hv1)
  have h2 := mul_nonneg hv0 (sub_nonneg.mpr hu1)
  have h3 := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1)
  have h4 := mul_nonneg hu0 hv0
  have hpos : 0 < 1 + (θ - 1) * (u + v - 2 * u * v) := by
    rcases le_or_gt 1 θ with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg h1 h2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h.le) (add_nonneg h3 h4)]
  unfold plackettDensity
  have := Real.sqrt_pos.mpr hD
  positivity

/-- The Plackett partial derivative `∂C_θ/∂v` is nondecreasing in `u`. -/
theorem plackettDeriv_monotoneOn {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    MonotoneOn (fun u => plackettDeriv θ u v) (Icc 0 1) := by
  have hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun x => (plackettLinear θ x v - 2 * θ * x) / √(plackettDisc θ x v))
      (-2 * θ * (1 + (θ - 1) * (x + v - 2 * x * v)) /
        (√(plackettDisc θ x v) * plackettDisc θ x v)) x :=
    fun x hx => hasDerivAt_plackettRatio_left (plackettDisc_pos hθ hx.1 hx.2 hv0 hv1)
  have hk : AntitoneOn (fun x => (plackettLinear θ x v - 2 * θ * x) / √(plackettDisc θ x v))
      (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Ioo_subset_Icc_self hx
      rw [(hd x hx').deriv]
      have hD := plackettDisc_pos hθ hx'.1 hx'.2 hv0 hv1
      have h1 := mul_nonneg hx'.1 (sub_nonneg.mpr hv1)
      have h2 := mul_nonneg hv0 (sub_nonneg.mpr hx'.2)
      have h3 := mul_nonneg (sub_nonneg.mpr hx'.2) (sub_nonneg.mpr hv1)
      have h4 := mul_nonneg hx'.1 hv0
      have hpos : 0 ≤ 1 + (θ - 1) * (x + v - 2 * x * v) := by
        rcases le_or_gt 1 θ with h | h
        · nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg h1 h2)]
        · nlinarith [mul_nonneg (sub_nonneg.mpr h.le) (add_nonneg h3 h4)]
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · positivity
  intro a ha b hb hab
  have := hk ha hb hab
  simp only [plackettDeriv]
  linarith

/-! ## The Plackett copula -/

/-- The Plackett formula satisfies the classical copula conditions for every `θ > 0`. -/
theorem isClassical_plackettCDF (θ : ℝ) (hθ : 0 < θ) :
    IsClassical (fun u : Fin 2 → I => plackettCDF θ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate (fun u v : I => plackettCDF θ u v)
    (fun v => plackettCDF_zero_left hθ v.2.1 v.2.2)
    (fun u => by rw [plackettCDF_comm]; exact plackettCDF_zero_left hθ u.2.1 u.2.2)
    (fun v => plackettCDF_one_left hθ v.2.1 v.2.2)
    (fun u => by rw [plackettCDF_comm]; exact plackettCDF_one_left hθ u.2.1 u.2.2)
  intro a b c e hab hce
  have hab' : (a : ℝ) ≤ b := hab
  have hce' : (c : ℝ) ≤ e := hce
  by_cases h1 : θ = 1
  · simp only [plackettCDF, h1, ite_true]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hce')]
  · exact rectangle_nonneg_of_hasDerivAt (F := plackettCDF θ) (g := plackettDeriv θ)
      (fun u _ => ((continuous_plackettCDF θ).comp
        (continuous_const.prodMk continuous_id)).continuousOn)
      (fun u hu v hv => hasDerivAt_plackettCDF_right h1
        (plackettDisc_pos hθ hu.1 hu.2 hv.1.le hv.2.le))
      (fun v hv => plackettDeriv_monotoneOn hθ hv.1.le hv.2.le)
      a.2.1 hab' b.2.2 c.2.1 hce' e.2.2

/-- The Plackett copula `C_θ`, `θ > 0` (Nelsen 2006, (3.3.3)). -/
noncomputable def plackett (θ : ℝ) (hθ : 0 < θ) : Copula 2 :=
  ofClassical _ (isClassical_plackettCDF θ hθ)

@[simp] theorem cdf_plackett (θ : ℝ) (hθ : 0 < θ) (u : Fin 2 → I) :
    (plackett θ hθ).cdf u = plackettCDF θ (u 0) (u 1) := congrFun (cdf_ofClassical _ _) u

theorem cdf_plackett_two (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (plackett θ hθ).cdf ![u, v] = plackettCDF θ u v := by simp

/-- `C_1 = Π`. -/
@[simp] theorem plackett_one : plackett 1 one_pos = independence 2 := by
  apply ext_cdf; intro u
  simp [plackettCDF, cdf_independence, Fin.prod_univ_two]

/-- The constant cross-product ratio property defining the Plackett family:
`C(1 - u - v + C) = θ (u - C)(v - C)` with `C = C_θ(u,v)`. In terms of `(U,V) ~ C_θ`:
`P(U ≤ u, V ≤ v) P(U > u, V > v) = θ P(U ≤ u, V > v) P(U > u, V ≤ v)`. -/
theorem plackett_cross_ratio (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (plackett θ hθ).cdf ![u, v] * (1 - u - v + (plackett θ hθ).cdf ![u, v]) =
      θ * (u - (plackett θ hθ).cdf ![u, v]) * (v - (plackett θ hθ).cdf ![u, v]) := by
  rw [cdf_plackett_two]
  have h := plackettCDF_quadratic hθ u.2.1 u.2.2 v.2.1 v.2.2
  unfold plackettLinear at h
  linear_combination -h

theorem isExchangeable_plackett (θ : ℝ) (hθ : 0 < θ) : (plackett θ hθ).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp only [cdf_plackett_two]
  exact plackettCDF_comm θ u v

theorem plackettCDF_reflect (θ u v : ℝ) :
    plackettCDF θ u v = u + v - 1 + plackettCDF θ (1 - u) (1 - v) := by
  unfold plackettCDF
  split_ifs with h
  · ring
  · have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr h
    have hD : plackettDisc θ (1 - u) (1 - v) = plackettDisc θ u v := by
      rw [plackettDisc_eq, plackettDisc_eq]; ring
    rw [hD]
    unfold plackettLinear
    field_simp
    ring

theorem isRadiallySymmetric_plackett (θ : ℝ) (hθ : 0 < θ) :
    (plackett θ hθ).IsRadiallySymmetric := by
  rw [isRadiallySymmetric_iff]
  intro u v
  simp only [cdf_plackett_two, unitInterval.coe_symm_eq]
  exact plackettCDF_reflect θ u v

/-- Blomqvist's beta of the Plackett copula: `β(C_θ) = (√θ - 1)/(√θ + 1)`. -/
theorem blomqvistBeta_plackett (θ : ℝ) (hθ : 0 < θ) :
    (plackett θ hθ).blomqvistBeta = (√θ - 1) / (√θ + 1) := by
  rw [blomqvistBeta, cdf_plackett_two]
  have hu : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
  rw [hu]
  have hs : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hss : √θ ^ 2 = θ := Real.sq_sqrt hθ.le
  unfold plackettCDF
  split_ifs with h
  · subst h; simp; norm_num
  · have hD : plackettDisc θ (1 / 2) (1 / 2) = θ := by
      unfold plackettDisc plackettLinear; ring
    have hL : plackettLinear θ (1 / 2) (1 / 2) = θ := by unfold plackettLinear; ring
    rw [hD, hL]
    have hs1 : √θ - 1 ≠ 0 := by
      intro h0
      apply h
      rw [← hss, show √θ = 1 by linarith]; norm_num
    have hθ1 : θ - 1 = (√θ - 1) * (√θ + 1) := by linear_combination -hss
    rw [hθ1]
    generalize √θ = r at hs hss hs1 ⊢
    subst hss
    field_simp
    ring

end ProbabilityTheory.Copula
