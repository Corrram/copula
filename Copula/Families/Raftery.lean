/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Basic
import Copula.Dependence.Basic
import Copula.TailDependence.Derivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The Raftery family

Raftery's family (A. E. Raftery, *A continuous multivariate exponential distribution*,
Comm. Statist. A 13 (1984); it appears in the exercises of Nelsen 2006, Ch. 2 and 5): for
`θ ∈ [0,1)`,

`C_θ(u,v) = M(u,v) + (1-θ)/(1+θ) · (uv)^{1/(1-θ)} · (1 - max(u,v)^{-(1+θ)/(1-θ)})`,

and `C_θ → M` as `θ → 1`. With `p = 1/(1-θ) ≥ 1` and `(1-θ)/(1+θ) = 1/(2p-1)` this reads, for
`u ≤ v`, `C(u,v) = u + u^p (v^p - v^{1-p})/(2p-1)` (and symmetrically).

Main results:
* `C_θ` is a copula for every `θ ∈ [0,1)` (`raftery`): its vertical sections are
  differentiable on `(0,1)`, including across the diagonal where the two branches of the
  partial derivative `∂C/∂v` meet continuously, and `∂C/∂v` is nondecreasing in `u`
  (`rectangle_nonneg_of_hasDerivAt`); in particular `C_θ` has no singular component;
* Nelsen's closed form (`raftery_cdf_eq`), `C_0 = Π` (`raftery_zero`), exchangeability, and
  the uniform convergence `|C_θ - M| ≤ (1-θ)/(1+θ)` (`tendsto_rafteryCDF_one`);
* `C_θ` is PQD (Bernoulli's inequality);
* the diagonal `δ(t) = (2θ t + (1-θ) t^{2/(1-θ)})/(1+θ)`, Blomqvist's beta, and the tail
  coefficients `λ_L = 2θ/(1+θ)`, `λ_U = 0`.
-/

open Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace Raftery

/-- The Raftery CDF in the exponent `p = 1/(1-θ) ≥ 1`. -/
noncomputable def core (p u v : ℝ) : ℝ :=
  if u ≤ v then u + u ^ p * (v ^ p - v ^ (1 - p)) / (2 * p - 1)
  else v + v ^ p * (u ^ p - u ^ (1 - p)) / (2 * p - 1)

/-- The partial derivative `∂C/∂v` in the exponent `p`. -/
noncomputable def condDeriv (p u v : ℝ) : ℝ :=
  if u ≤ v then u ^ p * (p * v ^ (p - 1) + (p - 1) * v ^ (-p)) / (2 * p - 1)
  else 1 + p * v ^ (p - 1) * (u ^ p - u ^ (1 - p)) / (2 * p - 1)

variable {p : ℝ}

theorem core_comm (u v : ℝ) : core p u v = core p v u := by
  unfold core
  rcases lt_trichotomy u v with h | h | h
  · rw [ite_eq_left h.le, ite_eq_right (not_le.mpr h)]
  · subst h; rfl
  · rw [ite_eq_right (not_le.mpr h), ite_eq_left h.le]

theorem core_zero_left (hp : 1 ≤ p) {v : ℝ} (hv : 0 ≤ v) : core p 0 v = 0 := by
  unfold core
  rw [ite_eq_left hv, Real.zero_rpow (by linarith)]
  ring

theorem core_one_left {v : ℝ} (hv : v ≤ 1) : core p 1 v = v := by
  unfold core
  split_ifs with h
  · have : v = 1 := le_antisymm hv h
    subst this; simp
  · simp

/-- The key identity at the diagonal: for `x > 0`,
`x^p (p x^{p-1} + (p-1) x^{-p})/(2p-1) = 1 + p x^{p-1} (x^p - x^{1-p})/(2p-1)`. -/
theorem branch_eq (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) :
    x ^ p * (p * x ^ (p - 1) + (p - 1) * x ^ (-p)) / (2 * p - 1) =
      1 + p * x ^ (p - 1) * (x ^ p - x ^ (1 - p)) / (2 * p - 1) := by
  have h1 : x ^ p * x ^ (p - 1) = x ^ (2 * p - 1) := by
    rw [← Real.rpow_add hx]; ring_nf
  have h2 : x ^ p * x ^ (-p) = 1 := by
    rw [← Real.rpow_add hx]; simp
  have h3 : x ^ (p - 1) * x ^ (1 - p) = 1 := by
    rw [← Real.rpow_add hx]; simp
  have hq : (2 * p - 1) ≠ 0 := by linarith
  have key : x ^ p * (p * x ^ (p - 1) + (p - 1) * x ^ (-p)) =
      (2 * p - 1) + p * x ^ (p - 1) * (x ^ p - x ^ (1 - p)) := by
    linear_combination (p - 1) * h2 + p * h3
  rw [key, add_div, div_self hq]

/-- The first branch, valid for `v ≥ u`. -/
theorem hasDerivAt_branch₁ (u : ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun y => u + u ^ p * (y ^ p - y ^ (1 - p)) / (2 * p - 1))
      (u ^ p * (p * w ^ (p - 1) + (p - 1) * w ^ (-p)) / (2 * p - 1)) w := by
  have h1 := Real.hasDerivAt_rpow_const (p := p) (Or.inl hw.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := 1 - p) (Or.inl hw.ne')
  have h := ((h1.sub h2).const_mul (u ^ p)).div_const (2 * p - 1) |>.const_add u
  convert h using 1
  rw [show 1 - p - 1 = -p by ring]
  ring

/-- The second branch, valid for `v ≤ u`. -/
theorem hasDerivAt_branch₂ (u : ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun y => y + y ^ p * (u ^ p - u ^ (1 - p)) / (2 * p - 1))
      (1 + p * w ^ (p - 1) * (u ^ p - u ^ (1 - p)) / (2 * p - 1)) w := by
  have h1 := Real.hasDerivAt_rpow_const (p := p) (Or.inl hw.ne')
  have h := (hasDerivAt_id' w).add ((h1.mul_const (u ^ p - u ^ (1 - p))).div_const (2 * p - 1))
  convert h using 1

theorem hasDerivAt_core (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    HasDerivAt (fun y => core p u y) (condDeriv p u v) v := by
  rcases lt_trichotomy u v with h | h | h
  · -- `u < v`: the first branch near `v`
    have he : (fun y => core p u y) =ᶠ[𝓝 v]
        fun y => u + u ^ p * (y ^ p - y ^ (1 - p)) / (2 * p - 1) := by
      filter_upwards [lt_mem_nhds h] with y hy
      simp [core, hy.le]
    rw [show condDeriv p u v = u ^ p * (p * v ^ (p - 1) + (p - 1) * v ^ (-p)) / (2 * p - 1) by
      simp [condDeriv, h.le]]
    exact (hasDerivAt_branch₁ u hv).congr_of_eventuallyEq he
  · -- `u = v`: both one-sided derivatives agree
    subst h
    have hd : condDeriv p u u = 1 + p * u ^ (p - 1) * (u ^ p - u ^ (1 - p)) / (2 * p - 1) := by
      simp only [condDeriv, le_refl, ↓reduceIte]
      exact branch_eq hp hv
    rw [hd]
    have hl : HasDerivWithinAt (fun y => core p u y)
        (1 + p * u ^ (p - 1) * (u ^ p - u ^ (1 - p)) / (2 * p - 1)) (Iic u) u := by
      apply (hasDerivAt_branch₂ u hv).hasDerivWithinAt.congr
      · intro y hy
        simp only [core]
        split_ifs with h'
        · have : y = u := le_antisymm hy h'
          subst this; ring
        · rfl
      · simp only [core, le_refl, ↓reduceIte]
    have hr : HasDerivWithinAt (fun y => core p u y)
        (1 + p * u ^ (p - 1) * (u ^ p - u ^ (1 - p)) / (2 * p - 1)) (Ici u) u := by
      rw [← branch_eq hp hv]
      apply (hasDerivAt_branch₁ u hv).hasDerivWithinAt.congr
      · intro y hy
        simp [core, show u ≤ y from hy]
      · simp [core]
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · -- `v < u`: the second branch near `v`
    have he : (fun y => core p u y) =ᶠ[𝓝 v]
        fun y => y + y ^ p * (u ^ p - u ^ (1 - p)) / (2 * p - 1) := by
      filter_upwards [gt_mem_nhds h] with y hy
      simp [core, not_le.mpr hy]
    rw [show condDeriv p u v = 1 + p * v ^ (p - 1) * (u ^ p - u ^ (1 - p)) / (2 * p - 1) by
      simp [condDeriv, not_le.mpr h]]
    exact (hasDerivAt_branch₂ u hv).congr_of_eventuallyEq he

theorem continuousOn_core (hp : 1 ≤ p) {u : ℝ} (hu : 0 ≤ u) :
    ContinuousOn (fun y => core p u y) (Icc 0 1) := by
  rcases eq_or_lt_of_le hu with h | h
  · subst h
    exact continuousOn_const.congr (fun y hy => core_zero_left hp hy.1)
  · apply Continuous.continuousOn
    unfold core
    apply continuous_if_le continuous_const continuous_id
    · apply ContinuousOn.add continuousOn_const
      apply ContinuousOn.div_const
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.sub
      · exact fun y _ => (Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).continuousWithinAt
      · intro y hy
        exact (Real.continuousAt_rpow_const _ _ (Or.inl (by
          simp only [mem_ofPred_eq, id] at hy; linarith))).continuousWithinAt
    · exact (continuous_id.add ((Real.continuous_rpow_const (by linarith)).mul
        continuous_const |>.div_const _)).continuousOn
    · intro y hy
      simp only [id] at hy
      subst hy
      ring

theorem condDeriv_monotoneOn (hp : 1 ≤ p) {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    MonotoneOn (fun u => condDeriv p u v) (Icc 0 1) := by
  have hq : 0 < 2 * p - 1 := by linarith
  have hc : 0 ≤ p * v ^ (p - 1) + (p - 1) * v ^ (-p) := by
    have := Real.rpow_nonneg hv0.le (p - 1)
    have := Real.rpow_nonneg hv0.le (-p)
    positivity
  -- first branch, monotone on `[0, ∞)`
  have hB1 : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      a ^ p * (p * v ^ (p - 1) + (p - 1) * v ^ (-p)) / (2 * p - 1) ≤
        b ^ p * (p * v ^ (p - 1) + (p - 1) * v ^ (-p)) / (2 * p - 1) := by
    intro a b ha hab
    apply div_le_div_of_nonneg_right _ hq.le
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hab (by linarith)) hc
  -- second branch, monotone on `(0, ∞)`
  have hB2 : ∀ a b : ℝ, 0 < a → a ≤ b →
      1 + p * v ^ (p - 1) * (a ^ p - a ^ (1 - p)) / (2 * p - 1) ≤
        1 + p * v ^ (p - 1) * (b ^ p - b ^ (1 - p)) / (2 * p - 1) := by
    intro a b ha hab
    have h1 := Real.rpow_le_rpow ha.le hab (by linarith : (0 : ℝ) ≤ p)
    have h2 := Real.rpow_le_rpow_of_nonpos ha hab (by linarith : 1 - p ≤ 0)
    have hpv : 0 ≤ p * v ^ (p - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hv0.le _)
    have := mul_le_mul_of_nonneg_left (by linarith : a ^ p - a ^ (1 - p) ≤ b ^ p - b ^ (1 - p)) hpv
    have := div_le_div_of_nonneg_right this hq.le
    linarith
  intro a ha b hb hab
  simp only [condDeriv]
  by_cases hbv : b ≤ v
  · rw [ite_eq_left (hab.trans hbv), ite_eq_left hbv]
    exact hB1 a b ha.1 hab
  · rw [ite_eq_right hbv]
    by_cases hav : a ≤ v
    · rw [ite_eq_left hav]
      calc _ ≤ v ^ p * (p * v ^ (p - 1) + (p - 1) * v ^ (-p)) / (2 * p - 1) := hB1 a v ha.1 hav
        _ = 1 + p * v ^ (p - 1) * (v ^ p - v ^ (1 - p)) / (2 * p - 1) := branch_eq hp hv0
        _ ≤ _ := hB2 v b hv0 (le_of_lt (not_le.mp hbv))
    · rw [ite_eq_right hav]
      exact hB2 a b (hv0.trans (not_le.mp hav)) hab

theorem rectangle_nonneg (hp : 1 ≤ p) {a b c e : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hce : c ≤ e) (he : e ≤ 1) :
    0 ≤ core p b e - core p a e - core p b c + core p a c :=
  rectangle_nonneg_of_hasDerivAt (F := core p) (g := condDeriv p)
    (fun _ hu => continuousOn_core hp hu.1)
    (fun _ hu _ hv => hasDerivAt_core hp hu.1 hv.1)
    (fun _ hv => condDeriv_monotoneOn hp hv.1 hv.2) ha hab hb hc hce he

/-- Positive quadrant dependence of the core formula. -/
theorem mul_le_core (hp : 1 ≤ p) {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : u * v ≤ core p u v := by
  have hq : 0 < 2 * p - 1 := by linarith
  -- reduce to `u ≤ v`
  wlog huv : u ≤ v generalizing u v
  · rw [mul_comm, core_comm]
    exact this hv0 hv1 hu0 hu1 (le_of_lt (not_le.mp huv))
  rw [core, ite_eq_left huv]
  rcases eq_or_lt_of_le hu0 with h0 | h0
  · subst h0; rw [Real.zero_rpow (by linarith)]; simp
  have hv : 0 < v := h0.trans_le huv
  -- `u^p ≤ u v^{p-1}`
  have hup : u ^ p ≤ u * v ^ (p - 1) := by
    calc u ^ p = u * u ^ (p - 1) := by
          rw [← Real.rpow_one_add' h0.le (by linarith)]; ring_nf
      _ ≤ u * v ^ (p - 1) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0.le huv (by linarith)) h0.le
  have hdiff : 0 ≤ v ^ (1 - p) - v ^ p :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_ge hv hv1 (by linarith))
  have h1 : v ^ (p - 1) * (v ^ (1 - p) - v ^ p) = 1 - v ^ (2 * p - 1) := by
    rw [mul_sub, ← Real.rpow_add hv, ← Real.rpow_add hv]; ring_nf; simp
  -- Bernoulli: `1 - v^{2p-1} ≤ (2p-1)(1-v)`
  have hbern : 1 + (2 * p - 1) * (v - 1) ≤ (1 + (v - 1)) ^ (2 * p - 1) :=
    one_add_mul_self_le_rpow_one_add (by linarith) (by linarith)
  rw [show 1 + (v - 1) = v by ring] at hbern
  have key : u ^ p * (v ^ (1 - p) - v ^ p) ≤ u * ((2 * p - 1) * (1 - v)) := by
    calc u ^ p * (v ^ (1 - p) - v ^ p) ≤ u * v ^ (p - 1) * (v ^ (1 - p) - v ^ p) :=
          mul_le_mul_of_nonneg_right hup hdiff
      _ = u * (1 - v ^ (2 * p - 1)) := by rw [mul_assoc, h1]
      _ ≤ u * ((2 * p - 1) * (1 - v)) := mul_le_mul_of_nonneg_left (by linarith) h0.le
  have : u ^ p * (v ^ p - v ^ (1 - p)) / (2 * p - 1) ≥ -(u * (1 - v)) := by
    rw [ge_iff_le, le_div_iff₀ hq]
    nlinarith
  linarith

/-- The diagonal of the core formula. -/
theorem core_diag (hp : 1 ≤ p) {t : ℝ} (ht : 0 ≤ t) :
    core p t t = ((2 * p - 2) * t + t ^ (2 * p)) / (2 * p - 1) := by
  have hq : (2 * p - 1) ≠ 0 := by linarith
  rw [core, ite_eq_left le_rfl]
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    rw [Real.zero_rpow (show p ≠ 0 by linarith), Real.zero_rpow (show 2 * p ≠ 0 by linarith)]
    simp
  · have h1 : t ^ p * t ^ p = t ^ (2 * p) := by rw [← Real.rpow_add h]; ring_nf
    have h2 : t ^ p * t ^ (1 - p) = t := by rw [← Real.rpow_add h]; simp
    rw [eq_div_iff hq, add_mul, div_mul_cancel₀ _ hq]
    linear_combination h1 - h2

end Raftery

/-- The Raftery CDF formula `C_θ` for `θ ∈ [0,1)`, in the exponent `p = 1/(1-θ)`. -/
noncomputable def rafteryCDF (θ u v : ℝ) : ℝ := Raftery.core (1 / (1 - θ)) u v

theorem one_le_raftery_exponent {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 1 ≤ 1 / (1 - θ) := by
  rw [le_div_iff₀ (by linarith)]; linarith

theorem raftery_exponent_sub {θ : ℝ} (h1 : θ < 1) :
    2 * (1 / (1 - θ)) - 1 = (1 + θ) / (1 - θ) := by
  have : (1 - θ) ≠ 0 := by linarith
  field_simp
  ring

theorem raftery_scale {θ : ℝ} (h1 : θ < 1) :
    1 / (2 * (1 / (1 - θ)) - 1) = (1 - θ) / (1 + θ) := by
  rw [raftery_exponent_sub h1, one_div_div]

theorem isClassical_rafteryCDF {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    IsClassical (fun u : Fin 2 → I => rafteryCDF θ (u 0) (u 1)) := by
  have hp := one_le_raftery_exponent h0 h1
  apply IsClassical.ofBivariate (fun u v : I => rafteryCDF θ u v)
    (fun v => Raftery.core_zero_left hp v.2.1)
    (fun u => by
      change Raftery.core _ _ _ = 0
      rw [Raftery.core_comm]; exact Raftery.core_zero_left hp u.2.1)
    (fun v => Raftery.core_one_left v.2.2)
    (fun u => by
      change Raftery.core _ _ _ = _
      rw [Raftery.core_comm]; exact Raftery.core_one_left u.2.2)
  intro a b c e hab hce
  exact Raftery.rectangle_nonneg hp a.2.1 hab b.2.2 c.2.1 hce e.2.2

/-- The Raftery copula `C_θ`, `0 ≤ θ < 1` (Raftery 1984; Nelsen 2006). -/
noncomputable def raftery (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) : Copula 2 :=
  ofClassical _ (isClassical_rafteryCDF h0 h1)

@[simp] theorem cdf_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (u : Fin 2 → I) :
    (raftery θ h0 h1).cdf u = rafteryCDF θ (u 0) (u 1) := congrFun (cdf_ofClassical _ _) u

theorem cdf_raftery_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (u v : I) :
    (raftery θ h0 h1).cdf ![u, v] = rafteryCDF θ u v := by simp

/-- Nelsen's form of the Raftery CDF: for `u, v > 0`,
`C_θ(u,v) = min(u,v) + (1-θ)/(1+θ) (uv)^{1/(1-θ)} (1 - max(u,v)^{-(1+θ)/(1-θ)})`. -/
theorem raftery_cdf_eq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (u v : I) (hu : 0 < (u : ℝ))
    (hv : 0 < (v : ℝ)) :
    (raftery θ h0 h1).cdf ![u, v] = min (u : ℝ) v + (1 - θ) / (1 + θ) *
      ((u : ℝ) * v) ^ (1 / (1 - θ)) * (1 - (max (u : ℝ) v) ^ (-((1 + θ) / (1 - θ)))) := by
  have hp := one_le_raftery_exponent h0 h1
  rw [cdf_raftery_two, rafteryCDF]
  set p := 1 / (1 - θ) with hpdef
  have hθ1 : (1 - θ) ≠ 0 := by linarith
  have hk : (1 - θ) / (1 + θ) = 1 / (2 * p - 1) := by
    rw [hpdef, raftery_scale h1]
  have he : -((1 + θ) / (1 - θ)) = (1 - p) - p := by rw [hpdef]; field_simp; ring
  rw [hk, he]
  -- both cases reduce to the same computation
  have key : ∀ x y : ℝ, 0 < y →
      x + x ^ p * (y ^ p - y ^ (1 - p)) / (2 * p - 1) =
        x + 1 / (2 * p - 1) * (x ^ p * y ^ p) * (1 - y ^ (1 - p - p)) := by
    intro x y hy
    have h : y ^ p * y ^ (1 - p - p) = y ^ (1 - p) := by rw [← Real.rpow_add hy]; ring_nf
    rw [← h]; ring
  rw [Real.mul_rpow u.2.1 v.2.1]
  unfold Raftery.core
  split_ifs with huv
  · rw [min_eq_left huv, max_eq_right huv]; exact key _ _ hv
  · have hvu : (v : ℝ) ≤ u := le_of_lt (not_le.mp huv)
    rw [min_eq_right hvu, max_eq_left hvu, mul_comm ((u : ℝ) ^ p)]; exact key _ _ hu

/-- `C_0 = Π`. -/
@[simp] theorem raftery_zero : raftery 0 le_rfl one_pos = independence 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_raftery_two, cdf_independence, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, rafteryCDF, Raftery.core]
  norm_num
  split_ifs <;> ring

theorem isExchangeable_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    (raftery θ h0 h1).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp only [cdf_raftery_two, rafteryCDF]
  exact Raftery.core_comm _ _

/-- Raftery copulas are positively quadrant dependent. -/
theorem isPQD_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : (raftery θ h0 h1).IsPQD := by
  intro u v
  rw [cdf_raftery_two]
  exact Raftery.mul_le_core (one_le_raftery_exponent h0 h1) u.2.1 u.2.2 v.2.1 v.2.2

namespace Raftery

variable {p : ℝ}

/-- The distance to the upper Fréchet–Hoeffding bound: `0 ≤ min(u,v) - C ≤ 1/(2p-1)`. -/
theorem min_sub_core_le (hp : 1 ≤ p) {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : 0 ≤ min u v - core p u v ∧ min u v - core p u v ≤ 1 / (2 * p - 1) := by
  have hq : 0 < 2 * p - 1 := by linarith
  wlog huv : u ≤ v generalizing u v
  · rw [min_comm, core_comm]
    exact this hv0 hv1 hu0 hu1 (le_of_lt (not_le.mp huv))
  rw [core, ite_eq_left huv, min_eq_left huv]
  rcases eq_or_lt_of_le hv0 with h | hv
  · have : u = 0 := le_antisymm (h ▸ huv) hu0
    subst this; rw [Real.zero_rpow (by linarith)]; simp; linarith
  have hdiff : 0 ≤ v ^ (1 - p) - v ^ p :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_ge hv hv1 (by linarith))
  have hup : u ^ p ≤ v ^ p := Real.rpow_le_rpow hu0 huv (by linarith)
  have hvv : v ^ p * v ^ (1 - p) = v := by rw [← Real.rpow_add hv]; simp
  have hb : u ^ p * (v ^ (1 - p) - v ^ p) ≤ 1 := by
    have h1 : u ^ p * (v ^ (1 - p) - v ^ p) ≤ u ^ p * v ^ (1 - p) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.rpow_nonneg hv.le p])
        (Real.rpow_nonneg hu0 p)
    have h2 : u ^ p * v ^ (1 - p) ≤ v ^ p * v ^ (1 - p) :=
      mul_le_mul_of_nonneg_right hup (Real.rpow_nonneg hv.le _)
    linarith
  have hn : 0 ≤ u ^ p * (v ^ (1 - p) - v ^ p) := mul_nonneg (Real.rpow_nonneg hu0 p) hdiff
  constructor
  · have : u ^ p * (v ^ p - v ^ (1 - p)) / (2 * p - 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) hq.le
    linarith
  · rw [show u - (u + u ^ p * (v ^ p - v ^ (1 - p)) / (2 * p - 1)) =
      u ^ p * (v ^ (1 - p) - v ^ p) / (2 * p - 1) by ring]
    exact div_le_div_of_nonneg_right hb hq.le

end Raftery

/-- Uniform distance to `M`: `0 ≤ min(u,v) - C_θ(u,v) ≤ (1-θ)/(1+θ)`. -/
theorem min_sub_rafteryCDF_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (u v : I) :
    0 ≤ min (u : ℝ) v - rafteryCDF θ u v ∧
      min (u : ℝ) v - rafteryCDF θ u v ≤ (1 - θ) / (1 + θ) := by
  rw [← raftery_scale h1]
  exact Raftery.min_sub_core_le (one_le_raftery_exponent h0 h1) u.2.1 u.2.2 v.2.1 v.2.2

/-- `C_θ → M` as `θ → 1⁻` (Nelsen 2006). -/
theorem tendsto_rafteryCDF_one (u v : I) :
    Tendsto (fun θ => rafteryCDF θ u v) (𝓝[<] 1) (𝓝 ((comonotonic 2).cdf ![u, v])) := by
  rw [cdf_comonotonic_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hk : Tendsto (fun θ : ℝ => (1 - θ) / (1 + θ)) (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun θ : ℝ => (1 - θ) / (1 + θ)) 1 :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    have h := hc.tendsto
    norm_num at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun θ : ℝ => min (u : ℝ) v - (1 - θ) / (1 + θ)) (𝓝[<] 1)
      (𝓝 (min (u : ℝ) v)) := by
    simpa using hk.const_sub (min (u : ℝ) v)
  have hev : ∀ᶠ θ in 𝓝[<] (1 : ℝ), 0 < θ ∧ θ < 1 :=
    ((lt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [hev] with θ hθ
    linarith [(min_sub_rafteryCDF_le hθ.1.le hθ.2 u v).2]
  · filter_upwards [hev] with θ hθ
    linarith [(min_sub_rafteryCDF_le hθ.1.le hθ.2 u v).1]

/-- The diagonal section `δ(t) = (2θ t + (1-θ) t^{2/(1-θ)})/(1+θ)`. -/
theorem raftery_diagonal {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (t : I) :
    (raftery θ h0 h1).diagonal t =
      (2 * θ * t + (1 - θ) * (t : ℝ) ^ (2 / (1 - θ))) / (1 + θ) := by
  have hp := one_le_raftery_exponent h0 h1
  rw [diagonal, cdf_raftery_two, rafteryCDF, Raftery.core_diag hp t.2.1,
    raftery_exponent_sub h1]
  have h1' : (1 - θ) ≠ 0 := by linarith
  have h2 : (1 + θ) ≠ 0 := by linarith
  have he : 2 * (1 / (1 - θ)) = 2 / (1 - θ) := by ring
  have h3 : 2 * (1 / (1 - θ)) - 2 = 2 * θ / (1 - θ) := by field_simp; ring
  rw [h3, he, div_div_eq_mul_div]
  field_simp

/-- Blomqvist's beta of the Raftery copula:
`β = (3θ - 1)/(1+θ) + 4(1-θ)/(1+θ) · (1/2)^{2/(1-θ)}`. -/
theorem blomqvistBeta_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    (raftery θ h0 h1).blomqvistBeta =
      (3 * θ - 1) / (1 + θ) + 4 * (1 - θ) / (1 + θ) * (1 / 2 : ℝ) ^ (2 / (1 - θ)) := by
  have h := raftery_diagonal h0 h1 unitHalf
  rw [diagonal] at h
  rw [blomqvistBeta, h]
  have hu : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
  rw [hu]
  have h2 : (1 + θ) ≠ 0 := by linarith
  field_simp
  ring

theorem hasDerivAt_raftery_diagonal {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (2 * θ * t + (1 - θ) * t ^ (2 / (1 - θ))) / (1 + θ))
      ((2 * θ + (1 - θ) * ((2 / (1 - θ)) * x ^ (2 / (1 - θ) - 1))) / (1 + θ)) x := by
  have hp : 1 ≤ 2 / (1 - θ) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h := Real.hasDerivAt_rpow_const (x := x) (Or.inr hp)
  have := ((((hasDerivAt_id' x).const_mul (2 * θ)).add (h.const_mul (1 - θ)))).div_const (1 + θ)
  convert this using 1
  ring

/-- The lower tail dependence coefficient of the Raftery copula is `2θ/(1+θ)`. -/
theorem hasLowerTailDependence_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    (raftery θ h0 h1).HasLowerTailDependence (2 * θ / (1 + θ)) := by
  apply hasLowerTailDependence_of_hasDerivWithinAt
    (f := fun t : ℝ => (2 * θ * t + (1 - θ) * t ^ (2 / (1 - θ))) / (1 + θ))
    (fun t => (raftery_diagonal h0 h1 t).symm)
  have h := (hasDerivAt_raftery_diagonal h0 h1 0).hasDerivWithinAt (s := Icc 0 1)
  convert h using 1
  have hp : 2 / (1 - θ) - 1 ≠ 0 := by
    have : 2 ≤ 2 / (1 - θ) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith
  rw [Real.zero_rpow hp]
  ring

/-- The upper tail dependence coefficient of the Raftery copula is `0`. -/
theorem hasUpperTailDependence_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    (raftery θ h0 h1).HasUpperTailDependence 0 := by
  have h := hasUpperTailDependence_of_hasDerivWithinAt (C := raftery θ h0 h1)
    (f := fun t : ℝ => (2 * θ * t + (1 - θ) * t ^ (2 / (1 - θ))) / (1 + θ))
    (fun t => (raftery_diagonal h0 h1 t).symm)
    ((hasDerivAt_raftery_diagonal h0 h1 1).hasDerivWithinAt (s := Icc 0 1))
  convert h using 1
  have h1' : (1 - θ) ≠ 0 := by linarith
  have h2 : (1 + θ) ≠ 0 := by linarith
  rw [Real.one_rpow]
  field_simp
  ring

end ProbabilityTheory.Copula
