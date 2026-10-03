/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.RafterySpearman
import Copula.Rank.KendallConditionalProduct
import Copula.Rank.ConditionalDerivative

/-! # Kendall's tau of the Raftery family

For the Raftery copula `C_θ` (`0 ≤ θ < 1`, exponent `p = 1/(1-θ)`, see
`Copula.Families.Raftery`) Kendall's tau is

`τ(C_θ) = 2θ / (3 - θ)`  (`kendallTau_raftery`; Nelsen 2006, exercises of Ch. 5),

equivalently `τ = 2(p-1)/(2p+1)`.

Proof. By `kendallTau_conditional_product` and exchangeability, `τ = 1 - 4 ∬ ∂₁C ∂₂C`. The
conditional distribution functions agree almost everywhere with the classical partial
derivatives (`conditionalCDF_eq_deriv`), which are explicit on both sides of the diagonal
(`Raftery.condDeriv`; the two branches meet continuously on the diagonal). Below the diagonal
(`t ≤ x`) the product of the partial derivatives is
`∂₂C · ∂₁C = c(x) t^p/(2p-1) + p c(x) (x^p - x^{1-p}) t^{2p-1}/(2p-1)²` with
`c(x) = p x^{p-1} + (p-1) x^{-p}`, whose integral over `t ∈ [0,x]` is elementary
(`integral_partialProduct`); above the diagonal the same integral appears after Fubini. Hence
`∬ ∂₁C ∂₂C = 2 ∫₀¹ L = 3/(4(2p+1))`.

References: A. E. Raftery, *A continuous multivariate exponential distribution*, Comm. Statist.
A 13 (1984); R. B. Nelsen, *An Introduction to Copulas* (2006), exercises of Ch. 5 (Raftery family).
-/

open MeasureTheory Set Filter Function
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

namespace RafteryKendall

variable {p : ℝ}

/-- `∂C/∂v` at `(t, x)` below the diagonal (`t ≤ x`). -/
noncomputable def vDeriv (p t x : ℝ) : ℝ :=
  t ^ p * (p * x ^ (p - 1) + (p - 1) * x ^ (-p)) / (2 * p - 1)

/-- `∂C/∂u` at `(t, x)` below the diagonal (`t ≤ x`). -/
noncomputable def uDeriv (p t x : ℝ) : ℝ :=
  1 + p * t ^ (p - 1) * (x ^ p - x ^ (1 - p)) / (2 * p - 1)

/-- The product of the two partial derivatives below the diagonal. -/
noncomputable def partialProduct (p t x : ℝ) : ℝ := vDeriv p t x * uDeriv p t x

theorem condDeriv_eq (u v : ℝ) :
    Raftery.condDeriv p u v = if u ≤ v then vDeriv p u v else uDeriv p v u := rfl

theorem vDeriv_zero_left (hp : 1 ≤ p) (x : ℝ) : vDeriv p 0 x = 0 := by
  simp [vDeriv, Real.zero_rpow (show p ≠ 0 by linarith)]

/-- The integrand `∂₁C ∂₂C` split along the diagonal. -/
theorem integrand_eq (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) :
    Raftery.condDeriv p v u * Raftery.condDeriv p u v =
      (if u ≤ v then partialProduct p u v else 0) +
        (if v < u then partialProduct p v u else 0) := by
  rw [condDeriv_eq, condDeriv_eq]
  rcases lt_trichotomy u v with h | h | h
  · simp only [show ¬ v ≤ u from not_le.2 h, show u ≤ v from h.le,
      show ¬ v < u from not_lt.2 h.le, ↓reduceIte, add_zero, partialProduct]
    ring
  · subst h
    simp only [le_refl, lt_irrefl, ↓reduceIte, add_zero, partialProduct]
    rcases eq_or_lt_of_le hu with h0 | h0
    · subst h0
      rw [vDeriv_zero_left hp]
      ring
    · rw [show vDeriv p u u = uDeriv p u u from Raftery.branch_eq hp h0]
  · simp only [show v ≤ u from h.le, show ¬ u ≤ v from not_le.2 h, h, ↓reduceIte, zero_add,
      partialProduct]

theorem rpow_mul_rpow_sub_one (hp : 1 ≤ p) {t : ℝ} (ht : 0 ≤ t) :
    t ^ p * t ^ (p - 1) = t ^ (2 * p - 1) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    rw [Real.zero_rpow (by linarith), zero_mul, Real.zero_rpow (by linarith)]
  · rw [← Real.rpow_add h]
    ring_nf

theorem derivative_identity {a b c D : ℝ} (hq : 2 * p - 1 ≠ 0) (hr : p + 1 ≠ 0) :
    a * c / (2 * p - 1) * (1 + p * b * D / (2 * p - 1)) =
      c * ((p + 1) * a) / ((2 * p - 1) * (p + 1)) +
        c * D * (2 * p * (a * b)) / (2 * (2 * p - 1) ^ 2) := by
  field_simp

/-- An antiderivative of `t ↦ ∂₂C(t,x) ∂₁C(t,x)`. -/
noncomputable def primitive (p x t : ℝ) : ℝ :=
  (p * x ^ (p - 1) + (p - 1) * x ^ (-p)) * t ^ (p + 1) / ((2 * p - 1) * (p + 1)) +
    (p * x ^ (p - 1) + (p - 1) * x ^ (-p)) * (x ^ p - x ^ (1 - p)) * t ^ (2 * p) /
      (2 * (2 * p - 1) ^ 2)

theorem hasDerivAt_primitive (hp : 1 ≤ p) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (primitive p x) (partialProduct p t x) t := by
  have h1 := Real.hasDerivAt_rpow_const (x := t) (p := p + 1) (Or.inr (by linarith))
  have h2 := Real.hasDerivAt_rpow_const (x := t) (p := 2 * p) (Or.inr (by linarith))
  have h := ((h1.const_mul (p * x ^ (p - 1) + (p - 1) * x ^ (-p))).div_const
    ((2 * p - 1) * (p + 1))).add
    ((h2.const_mul ((p * x ^ (p - 1) + (p - 1) * x ^ (-p)) * (x ^ p - x ^ (1 - p)))).div_const
      (2 * (2 * p - 1) ^ 2))
  have hq : (2 * p - 1) ≠ 0 := by linarith
  have hr : (p + 1) ≠ 0 := by linarith
  convert h using 1
  · funext y
    simp only [primitive, Pi.add_apply]
  unfold partialProduct vDeriv uDeriv
  rw [show p + 1 - 1 = p by ring, ← rpow_mul_rpow_sub_one hp ht]
  generalize t ^ p = a
  generalize t ^ (p - 1) = b
  generalize x ^ (p - 1) = e₁
  generalize x ^ (-p) = e₂
  generalize x ^ p = e₃
  generalize x ^ (1 - p) = e₄
  exact derivative_identity hq hr

/-- The closed form of `∫₀ˣ ∂₂C(t,x) ∂₁C(t,x) dt`. -/
noncomputable def lowerIntegral (p x : ℝ) : ℝ :=
  (p * x ^ (2 * p) + (p - 1) * x) / ((2 * p - 1) * (p + 1)) +
    (p * x ^ (4 * p - 1) - x ^ (2 * p) - (p - 1) * x) / (2 * (2 * p - 1) ^ 2)

theorem primitive_eq (hp : 1 ≤ p) {x : ℝ} (hx : 0 ≤ x) :
    primitive p x x - primitive p x 0 = lowerIntegral p x := by
  have h0 : primitive p x 0 = 0 := by
    simp [primitive, Real.zero_rpow (show p + 1 ≠ 0 by linarith),
      Real.zero_rpow (show 2 * p ≠ 0 by linarith)]
  rw [h0, sub_zero]
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst hx0
    simp [primitive, lowerIntegral, Real.zero_rpow (show p + 1 ≠ 0 by linarith),
      Real.zero_rpow (show 2 * p ≠ 0 by linarith),
      Real.zero_rpow (show 4 * p - 1 ≠ 0 by linarith)]
  have e1 : x ^ (p - 1) * x ^ (p + 1) = x ^ (2 * p) := by rw [← Real.rpow_add hx0]; ring_nf
  have e2 : x ^ (-p) * x ^ (p + 1) = x := by
    rw [← Real.rpow_add hx0, show -p + (p + 1) = 1 by ring, Real.rpow_one]
  have e3 : x ^ (p - 1) * x ^ p * x ^ (2 * p) = x ^ (4 * p - 1) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have e4 : x ^ (p - 1) * x ^ (1 - p) * x ^ (2 * p) = x ^ (2 * p) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have e5 : x ^ (-p) * x ^ p * x ^ (2 * p) = x ^ (2 * p) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have e6 : x ^ (-p) * x ^ (1 - p) * x ^ (2 * p) = x := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, show -p + (1 - p) + 2 * p = 1 by ring,
      Real.rpow_one]
  have hexp : primitive p x x =
      (p * (x ^ (p - 1) * x ^ (p + 1)) + (p - 1) * (x ^ (-p) * x ^ (p + 1))) /
          ((2 * p - 1) * (p + 1)) +
        (p * (x ^ (p - 1) * x ^ p * x ^ (2 * p)) - p * (x ^ (p - 1) * x ^ (1 - p) * x ^ (2 * p)) +
            (p - 1) * (x ^ (-p) * x ^ p * x ^ (2 * p)) -
            (p - 1) * (x ^ (-p) * x ^ (1 - p) * x ^ (2 * p))) / (2 * (2 * p - 1) ^ 2) := by
    unfold primitive
    ring
  rw [hexp, e1, e2, e3, e4, e5, e6, lowerIntegral]
  ring

theorem continuous_partialProduct (hp : 1 ≤ p) (x : ℝ) :
    Continuous (fun t => partialProduct p t x) := by
  have h1 : Continuous (fun t : ℝ => t ^ p) := Real.continuous_rpow_const (by linarith)
  have h2 : Continuous (fun t : ℝ => t ^ (p - 1)) := Real.continuous_rpow_const (by linarith)
  unfold partialProduct vDeriv uDeriv
  exact ((h1.mul continuous_const).div_const _).mul
    (continuous_const.add (((continuous_const.mul h2).mul continuous_const).div_const _))

/-- `∫₀ˣ ∂₂C(t,x) ∂₁C(t,x) dt = L(x)`. -/
theorem integral_partialProduct (hp : 1 ≤ p) (x : I) :
    (∫ t in Iic x, partialProduct p (t : ℝ) x) = lowerIntegral p x := by
  rw [integral_unit_Iic (fun t => partialProduct p t x),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_primitive hp x (by
        rw [uIcc_of_le x.2.1] at ht; exact ht.1))
      ((continuous_partialProduct hp x).intervalIntegrable _ _),
    primitive_eq hp x.2.1]

theorem continuous_lowerIntegral (hp : 1 ≤ p) : Continuous (lowerIntegral p) := by
  unfold lowerIntegral
  have h1 : Continuous (fun x : ℝ => x ^ (2 * p)) := Real.continuous_rpow_const (by linarith)
  have h2 : Continuous (fun x : ℝ => x ^ (4 * p - 1)) := Real.continuous_rpow_const (by linarith)
  exact (((continuous_const.mul h1).add (continuous_const.mul continuous_id)).div_const _).add
    ((((continuous_const.mul h2).sub h1).sub (continuous_const.mul continuous_id)).div_const _)

/-- `∫₀¹ L = 3/(8(2p+1))`. -/
theorem integral_lowerIntegral (hp : 1 ≤ p) :
    (∫ x : I, lowerIntegral p x) = 3 / (8 * (2 * p + 1)) := by
  rw [integral_unitInterval (lowerIntegral p)]
  have hq : (2 * p - 1) ≠ 0 := by linarith
  have hr : (p + 1) ≠ 0 := by linarith
  have hs : (2 * p + 1) ≠ 0 := by linarith
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => (p * (x ^ (2 * p + 1) / (2 * p + 1)) + (p - 1) * (x ^ 2 / 2)) /
          ((2 * p - 1) * (p + 1)) +
        (x ^ (4 * p) / 4 - x ^ (2 * p + 1) / (2 * p + 1) - (p - 1) * (x ^ 2 / 2)) /
          (2 * (2 * p - 1) ^ 2)) (lowerIntegral p x) x := by
    intro x _
    have ha := Real.hasDerivAt_rpow_const (x := x) (p := 2 * p + 1) (Or.inr (by linarith))
    have hb := Real.hasDerivAt_rpow_const (x := x) (p := 4 * p) (Or.inr (by linarith))
    have hc := hasDerivAt_pow 2 x
    have h := ((((ha.div_const (2 * p + 1)).const_mul p).add
      ((hc.div_const 2).const_mul (p - 1))).div_const ((2 * p - 1) * (p + 1))).add
      ((((hb.div_const 4).sub (ha.div_const (2 * p + 1))).sub
        ((hc.div_const 2).const_mul (p - 1))).div_const (2 * (2 * p - 1) ^ 2))
    convert h using 1
    rw [lowerIntegral, show 2 * p + 1 - 1 = 2 * p by ring]
    field_simp
    ring
  have hLc := continuous_lowerIntegral hp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hLc.intervalIntegrable _ _)]
  simp only [Real.one_rpow, Real.zero_rpow (show 2 * p + 1 ≠ 0 by linarith),
    Real.zero_rpow (show 4 * p ≠ 0 by linarith), zero_div, mul_zero, add_zero, sub_zero, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have e1 : (p * (1 / (2 * p + 1)) + (p - 1) * (1 / 2)) =
      (2 * p ^ 2 + p - 1) / (2 * (2 * p + 1)) := by
    field_simp; ring
  have e2 : (1 / 4 - 1 / (2 * p + 1) - (p - 1) * (1 / 2)) =
      -(4 * p ^ 2 - 4 * p + 1) / (4 * (2 * p + 1)) := by
    field_simp; ring
  have f1 : 2 * p ^ 2 + p - 1 = (2 * p - 1) * (p + 1) := by ring
  have f2 : 4 * p ^ 2 - 4 * p + 1 = (2 * p - 1) ^ 2 := by ring
  rw [e1, e2, f1, f2]
  field_simp
  ring

/-- Bounds `0 ≤ ∂₂C, ∂₁C ≤ 1` below the diagonal. -/
theorem abs_partialProduct_le (hp : 1 ≤ p) {t x : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) (hx0 : 0 < x)
    (hx1 : x ≤ 1) : |partialProduct p t x| ≤ 1 := by
  have hq : 0 < 2 * p - 1 := by linarith
  have hc : 0 ≤ p * x ^ (p - 1) + (p - 1) * x ^ (-p) := by
    have := Real.rpow_nonneg hx0.le (p - 1)
    have := Real.rpow_nonneg hx0.le (-p)
    have : 0 ≤ p - 1 := by linarith
    positivity
  have htp : t ^ p ≤ x ^ p := Real.rpow_le_rpow ht htx (by linarith)
  have htp1 : t ^ (p - 1) ≤ x ^ (p - 1) := Real.rpow_le_rpow ht htx (by linarith)
  have hx2 : x ^ (2 * p - 1) ≤ 1 := Real.rpow_le_one hx0.le hx1 (by linarith)
  have hx2' : 0 ≤ x ^ (2 * p - 1) := Real.rpow_nonneg hx0.le _
  have f1 : x ^ p * x ^ (p - 1) = x ^ (2 * p - 1) := rpow_mul_rpow_sub_one hp hx0.le
  have f2 : x ^ p * x ^ (-p) = 1 := by rw [← Real.rpow_add hx0]; simp
  have f3 : x ^ (p - 1) * x ^ (1 - p) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hD : x ^ p ≤ x ^ (1 - p) := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have hv0 : 0 ≤ vDeriv p t x := div_nonneg (mul_nonneg (Real.rpow_nonneg ht p) hc) hq.le
  have hv1 : vDeriv p t x ≤ 1 := by
    rw [vDeriv, div_le_one hq]
    calc t ^ p * (p * x ^ (p - 1) + (p - 1) * x ^ (-p))
        ≤ x ^ p * (p * x ^ (p - 1) + (p - 1) * x ^ (-p)) := mul_le_mul_of_nonneg_right htp hc
      _ = p * x ^ (2 * p - 1) + (p - 1) := by linear_combination p * f1 + (p - 1) * f2
      _ ≤ 2 * p - 1 := by nlinarith
  have htp1' : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht _
  have hu1 : uDeriv p t x ≤ 1 := by
    rw [uDeriv]
    have : p * t ^ (p - 1) * (x ^ p - x ^ (1 - p)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) htp1') (by linarith)
    have := div_nonpos_of_nonpos_of_nonneg this hq.le
    linarith
  have hu0 : 0 ≤ uDeriv p t x := by
    rw [uDeriv]
    have hb : p * t ^ (p - 1) * (x ^ (1 - p) - x ^ p) ≤ 2 * p - 1 := by
      calc p * t ^ (p - 1) * (x ^ (1 - p) - x ^ p)
          ≤ p * x ^ (p - 1) * (x ^ (1 - p) - x ^ p) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htp1 (by linarith))
              (by linarith)
        _ = p * (1 - x ^ (2 * p - 1)) := by
            rw [mul_assoc, mul_sub, f3, mul_comm (x ^ (p - 1)) (x ^ p), f1]
        _ ≤ 2 * p - 1 := by nlinarith
    have : p * t ^ (p - 1) * (x ^ p - x ^ (1 - p)) / (2 * p - 1) ≥ -1 := by
      rw [ge_iff_le, le_div_iff₀ hq]
      linarith
    linarith
  rw [partialProduct, abs_of_nonneg (mul_nonneg hv0 hu0)]
  calc vDeriv p t x * uDeriv p t x ≤ 1 * 1 := mul_le_mul hv1 hu1 hu0 zero_le_one
    _ = 1 := one_mul 1

/-- The part of the integrand below the diagonal, as a function of `(v, u)`. -/
noncomputable def lower (p : ℝ) (v u : I) : ℝ :=
  if (u : ℝ) ≤ v then partialProduct p u v else 0

/-- The part of the integrand above the diagonal, as a function of `(v, u)`. -/
noncomputable def upper (p : ℝ) (v u : I) : ℝ :=
  if (v : ℝ) < u then partialProduct p v u else 0

theorem measurable_upper (p : ℝ) : Measurable (uncurry (upper p)) := by
  unfold uncurry upper partialProduct vDeriv uDeriv
  refine Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) ?_ measurable_const
  fun_prop

theorem integrable_upper (hp : 1 ≤ p) :
    Integrable (uncurry (upper p)) ((volume : Measure I).prod volume) := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_upper p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  simp only [uncurry, upper]
  split_ifs with h
  · exact abs_partialProduct_le hp q.1.2.1 h.le (q.1.2.1.trans_lt h) q.2.2.2
  · simp

theorem integrable_upper_section (hp : 1 ≤ p) (v : I) : Integrable (fun u => upper p v u) :=
  (integrable_const (1 : ℝ)).mono'
    ((measurable_upper p).comp measurable_prodMk_left).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      simp only [upper]
      split_ifs with h
      · exact abs_partialProduct_le hp v.2.1 h.le (v.2.1.trans_lt h) u.2.2
      · simp)

theorem integral_lower (hp : 1 ≤ p) (v : I) : (∫ u : I, lower p v u) = lowerIntegral p v := by
  have he : (fun u : I => lower p v u) =
      (Iic v).indicator (fun u : I => partialProduct p (u : ℝ) v) := by
    funext u
    unfold lower
    by_cases h : u ≤ v
    · rw [indicator_of_mem (show u ∈ Iic v from h), ite_eq_left (show (u : ℝ) ≤ v from h)]
    · rw [indicator_of_notMem (show u ∉ Iic v from h), ite_eq_right (show ¬ (u : ℝ) ≤ v from h)]
  rw [he, integral_indicator measurableSet_Iic, integral_partialProduct hp]

theorem integrable_lower_section (hp : 1 ≤ p) (v : I) : Integrable (fun u => lower p v u) := by
  have he : (fun u : I => lower p v u) =
      (Iic v).indicator (fun u : I => partialProduct p (u : ℝ) v) := by
    funext u
    unfold lower
    by_cases h : u ≤ v
    · rw [indicator_of_mem (show u ∈ Iic v from h), ite_eq_left (show (u : ℝ) ≤ v from h)]
    · rw [indicator_of_notMem (show u ∉ Iic v from h), ite_eq_right (show ¬ (u : ℝ) ≤ v from h)]
  rw [he]
  exact (((continuous_partialProduct hp v).comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).indicator measurableSet_Iic

theorem integral_upper (hp : 1 ≤ p) (u : I) : (∫ v : I, upper p v u) = lowerIntegral p u := by
  have he : (fun v : I => upper p v u) =
      (Iio u).indicator (fun v : I => partialProduct p (v : ℝ) u) := by
    funext v
    unfold upper
    by_cases h : v < u
    · rw [indicator_of_mem (show v ∈ Iio u from h), ite_eq_left (show (v : ℝ) < u from h)]
    · rw [indicator_of_notMem (show v ∉ Iio u from h), ite_eq_right (show ¬ (v : ℝ) < u from h)]
  rw [he, integral_indicator measurableSet_Iio, setIntegral_congr_set Iio_ae_eq_Iic,
    integral_partialProduct hp]

private theorem ae_coe_mem_Ioo : ∀ᵐ v : I, (v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)).mem_iff]
      with x hx
    exact hx.2
  exact unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae h

theorem measurable_condDeriv (p : ℝ) :
    Measurable (fun q : I × I => Raftery.condDeriv p (q.1 : ℝ) (q.2 : ℝ)) := by
  unfold Raftery.condDeriv
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) ?_ ?_ <;> fun_prop

end RafteryKendall

/-- The conditional distribution function of the Raftery copula is the partial derivative
`∂₁C_θ(u, v) = Raftery.condDeriv p v u` (`p = 1/(1-θ)`) for almost every `u`. -/
theorem conditionalCDF_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (v : I) :
    ∀ᵐ u : I, (raftery θ h0 h1).conditionalCDF u v = Raftery.condDeriv (1 / (1 - θ)) v u := by
  have hp := one_le_raftery_exponent h0 h1
  filter_upwards [conditionalCDF_eq_deriv (raftery θ h0 h1) v, RafteryKendall.ae_coe_mem_Ioo]
    with u hu hI
  rw [hu]
  apply HasDerivAt.deriv
  have he : cdfSection (raftery θ h0 h1) v =ᶠ[𝓝 (u : ℝ)]
      fun y => Raftery.core (1 / (1 - θ)) v y := by
    filter_upwards [Ioo_mem_nhds hI.1 hI.2] with y hy
    rw [cdfSection, cdf_raftery_two, rafteryCDF, Raftery.core_comm,
      projIcc_of_mem zero_le_one ⟨hy.1.le, hy.2.le⟩]
  exact (Raftery.hasDerivAt_core hp v.2.1 hI.1).congr_of_eventuallyEq he

/-- **Kendall's tau of the Raftery copula**: `τ(C_θ) = 2θ/(3 - θ)` (Nelsen 2006). -/
theorem kendallTau_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    (raftery θ h0 h1).kendallTau = 2 * θ / (3 - θ) := by
  have hp := one_le_raftery_exponent h0 h1
  set p := 1 / (1 - θ) with hpdef
  set C := raftery θ h0 h1 with hC
  have hCt : C.transpose = C := isExchangeable_raftery h0 h1
  have hA : ∀ v : I, ∀ᵐ u : I, C.conditionalCDF u v = Raftery.condDeriv p v u :=
    conditionalCDF_raftery h0 h1
  have hf : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v = Raftery.condDeriv p v u :=
    Filter.Eventually.of_forall hA
  have hr : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF v u = Raftery.condDeriv p u v := by
    have hm : MeasurableSet {q : I × I |
        C.conditionalCDF q.2 q.1 = Raftery.condDeriv p (q.1 : ℝ) (q.2 : ℝ)} :=
      measurableSet_eq_fun C.measurable_conditionalCDF (RafteryKendall.measurable_condDeriv p)
    exact (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u = Raftery.condDeriv p u v) hm).mp
        (Filter.Eventually.of_forall hA)
  have hcross :
      (∫ u : I, ∫ v : I, C.conditionalCDF u v * C.conditionalCDF v u) =
        ∫ v : I, ∫ u : I, (RafteryKendall.lower p v u + RafteryKendall.upper p v u) := by
    have hi : Integrable (fun q : I × I =>
        C.conditionalCDF q.1 q.2 * C.conditionalCDF q.2 q.1) := by
      simpa only [hCt] using crossConditional_integrable C
    rw [integral_integral_swap hi]
    apply integral_congr_ae
    filter_upwards [hf, hr] with v hv hv'
    apply integral_congr_ae
    filter_upwards [hv, hv'] with u hu hu'
    rw [hu, hu', RafteryKendall.integrand_eq hp u.2.1]
    rfl
  have hinner : ∀ v : I,
      (∫ u : I, (RafteryKendall.lower p v u + RafteryKendall.upper p v u)) =
        RafteryKendall.lowerIntegral p v + ∫ u : I, RafteryKendall.upper p v u := by
    intro v
    rw [integral_add (RafteryKendall.integrable_lower_section hp v)
      (RafteryKendall.integrable_upper_section hp v), RafteryKendall.integral_lower hp]
  have hLi : Integrable (fun v : I => RafteryKendall.lowerIntegral p v) :=
    ((RafteryKendall.continuous_lowerIntegral hp).comp continuous_subtype_val
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUi : Integrable (fun v : I => ∫ u : I, RafteryKendall.upper p v u) :=
    (RafteryKendall.integrable_upper hp).integral_prod_left
  change C.kendallTau = _
  rw [kendallTau_conditional_product, hCt, hcross]
  simp_rw [hinner]
  rw [integral_add hLi hUi, integral_integral_swap (RafteryKendall.integrable_upper hp)]
  simp_rw [RafteryKendall.integral_upper hp]
  rw [RafteryKendall.integral_lowerIntegral hp, hpdef]
  have h1' : (1 - θ) ≠ 0 := by linarith
  have h3 : (3 - θ) ≠ 0 := by linarith
  have h4 : 2 * (1 / (1 - θ)) + 1 = (3 - θ) / (1 - θ) := by
    field_simp
    ring
  rw [h4]
  field_simp
  ring

end ProbabilityTheory.Copula
