/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.Pickands
import Copula.Dependence.Basic
import Copula.Rectangle

/-! # Every bivariate extreme-value copula is a Pickands copula

For a bivariate copula `C` define `A_C(t) = -log C(e^{-(1-t)}, e^{-t})` (`pickandsOf C`). If `C` is
max-stable (`IsExtremeValue`), then `A_C` is a Pickands dependence function and `C = C_{A_C}`
(`IsExtremeValue.eq_pickandsCopula`). Hence the bivariate extreme-value copulas are exactly the
Pickands copulas (`isExtremeValue_iff_exists_pickands`), every such copula is PQD, and the
pointwise order of extreme-value copulas is the reversed order of their Pickands functions.

Proof of convexity of `A_C` (no spectral measure is needed). Put
`ℓ(x,y) = -log C(e^{-x}, e^{-y})` on `[0,∞)²`. Max-stability makes `ℓ` positively homogeneous, so
`C(e^{-εx}, e^{-εy}) = exp(-ε ℓ(x,y))`; 2-increasingness of `C` at scale `ε` and `ε → 0` give
submodularity of `ℓ` (`evTail_submodular`). Applied to the rectangle with corners `(1-c, c)` and
`λ(1-c, λc)` this is a three-point convexity inequality for `A_C` around every `c ∈ (0,1)` with
arbitrarily close points (`pickandsOf_local`), and a continuous function with this local property
is convex (`convexOn_Icc_of_local`, an argmax argument).

References: J. Pickands, *Multivariate extreme value distributions* (1981); G. Gudendorf and
J. Segers, *Extreme-value copulas* (2010) (Pickands representation); H. Joe,
*Dependence Modeling with Copulas* (2014).
-/

open Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A continuous function on `[a,b]` which satisfies, around every interior point and at every
scale, some three-point convexity inequality, is convex on `[a,b]`. -/
theorem convexOn_Icc_of_local {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hloc : ∀ c ∈ Ioo a b, ∀ ε > 0, ∃ p q, c - ε < p ∧ p < c ∧ c < q ∧ q < c + ε ∧
      (q - p) * f c ≤ (q - c) * f p + (c - p) * f q) :
    ConvexOn ℝ (Icc a b) f := by
  apply convexOn_of_slope_mono_adjacent (convex_Icc a b)
  intro x y z hx hz hxy hyz
  rw [div_le_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 hyz)]
  by_contra hcon
  push Not at hcon
  have hxz : x < z := hxy.trans hyz
  have hne : z - x ≠ 0 := (sub_pos.2 hxz).ne'
  set L : ℝ → ℝ := fun c => (f x * (z - c) + f z * (c - x)) / (z - x) with hL
  set φ : ℝ → ℝ := fun c => f c - L c with hφ
  have hsub : Icc x z ⊆ Icc a b := Icc_subset_Icc hx.1 hz.2
  have hLc : Continuous L := by
    rw [hL]
    fun_prop
  have hφc : ContinuousOn φ (Icc x z) := (hf.mono hsub).sub hLc.continuousOn
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hxz.le) hφc
  have hmax' : ∀ w ∈ Icc x z, φ w ≤ φ m := fun w hw => isMaxOn_iff.1 hmax w hw
  have hφx : φ x = 0 := by
    simp only [hφ, hL]
    rw [sub_eq_zero, eq_div_iff hne]
    ring
  have hφz : φ z = 0 := by
    simp only [hφ, hL]
    rw [sub_eq_zero, eq_div_iff hne]
    ring
  have hφy : 0 < φ y := by
    have he : φ y = ((f y - f x) * (z - y) - (f z - f y) * (y - x)) / (z - x) := by
      simp only [hφ, hL]
      rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
      ring
    rw [he]
    exact div_pos (by linarith) (sub_pos.2 hxz)
  have hM : 0 < φ m := hφy.trans_le (hmax' y ⟨hxy.le, hyz.le⟩)
  set K := Icc x z ∩ φ ⁻¹' {φ m} with hK
  have hKc : IsClosed K := hφc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKne : K.Nonempty := ⟨m, hm, rfl⟩
  have hKb : BddBelow K := ⟨x, fun c hc => hc.1.1⟩
  have hcK : sInf K ∈ K := hKc.csInf_mem hKne hKb
  set c := sInf K with hc
  have hφcM : φ c = φ m := hcK.2
  have hcx : x < c := by
    refine lt_of_le_of_ne hcK.1.1 (fun h => ?_)
    rw [← h, hφx] at hφcM
    linarith
  have hcz : c < z := by
    refine lt_of_le_of_ne hcK.1.2 (fun h => ?_)
    rw [h, hφz] at hφcM
    linarith
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hineq⟩ := hloc c ⟨hx.1.trans_lt hcx, hcz.trans_le hz.2⟩
    (min (c - x) (z - c)) (lt_min (sub_pos.2 hcx) (sub_pos.2 hcz))
  have hpx : x < p := by linarith [min_le_left (c - x) (z - c)]
  have hqz : q < z := by linarith [min_le_right (c - x) (z - c)]
  have hpI : p ∈ Icc x z := ⟨hpx.le, by linarith⟩
  have hqI : q ∈ Icc x z := ⟨by linarith, hqz.le⟩
  have hφp : φ p < φ m := by
    rcases lt_or_eq_of_le (hmax' p hpI) with h | h
    · exact h
    · have : c ≤ p := csInf_le hKb ⟨hpI, h⟩
      linarith
  have hφq : φ q ≤ φ m := hmax' q hqI
  have hLlin : (q - p) * L c = (q - c) * L p + (c - p) * L q := by
    simp only [hL]
    ring
  have hφineq : (q - p) * φ c ≤ (q - c) * φ p + (c - p) * φ q := by
    simp only [hφ]
    linarith
  have h1 := mul_lt_mul_of_pos_left hφp (sub_pos.2 hq1)
  have h2 := mul_le_mul_of_nonneg_left hφq (sub_nonneg.2 hp2.le)
  rw [hφcM] at hφineq
  linarith

/-- The (negative log of the) copula on the exponential scale:
`ℓ_C(x,y) = -log C(e^{-x}, e^{-y})` for `x, y ≥ 0`. -/
noncomputable def evTail (C : Copula 2) (x y : ℝ) : ℝ :=
  -Real.log (C.cdf ![expNegUnit x, expNegUnit y])

/-- The Pickands function of a bivariate copula: `A_C(t) = -log C(e^{-(1-t)}, e^{-t})`. -/
noncomputable def pickandsOf (C : Copula 2) (t : ℝ) : ℝ := evTail C (1 - t) t

private theorem coe_pos_of_ne' {u : I} (hu : u ≠ 0) : (0 : ℝ) < u :=
  lt_of_le_of_ne u.2.1 (fun h => hu (Subtype.ext h.symm))

theorem continuous_expNegUnit : Continuous expNegUnit :=
  Continuous.subtype_mk (by fun_prop) _

theorem expNegUnit_zero : expNegUnit 0 = 1 := by
  apply Subtype.ext
  simp

theorem expNegUnit_neg_log {u : I} (hu : u ≠ 0) : expNegUnit (-Real.log u) = u := by
  apply Subtype.ext
  rw [coe_expNegUnit, max_eq_left (neg_nonneg.2 (Real.log_nonpos u.2.1 u.2.2)), neg_neg,
    Real.exp_log (coe_pos_of_ne' hu)]

private theorem rect_nonneg (C : Copula 2) {a b c e : I} (hab : a ≤ b) (hce : c ≤ e) :
    0 ≤ C.cdf ![b, e] - C.cdf ![a, e] - C.cdf ![b, c] + C.cdf ![a, c] := by
  have hle : (![a, c] : Fin 2 → I) ≤ ![b, e] := by
    intro i
    fin_cases i
    · exact hab
    · exact hce
  have h := C.rectangleIncrement_cdf_nonneg ![a, c] ![b, e] hle
  rw [rectangleIncrement_two] at h
  simpa using h

namespace IsExtremeValue

variable {C : Copula 2}

/-- Extreme-value copulas are positive on `(0,1]²`. -/
theorem cdf_pos (hC : C.IsExtremeValue) {u v : I} (hu : u ≠ 0) (hv : v ≠ 0) :
    0 < C.cdf ![u, v] := by
  have hm : min u v ≠ 0 := by
    rcases min_choice u v with h | h <;> rw [h] <;> assumption
  have hd := hC.hasPowerDiagonal (min u v)
  have hpos : 0 < C.diagonal (min u v) := by
    rw [hd]
    exact Real.rpow_pos_of_pos (coe_pos_of_ne' hm) _
  refine hpos.trans_le (C.monotone_cdf ?_)
  intro i
  fin_cases i
  · exact min_le_left u v
  · exact min_le_right u v

theorem evTail_exp (hC : C.IsExtremeValue) (x y : ℝ) :
    Real.exp (-evTail C x y) = C.cdf ![expNegUnit x, expNegUnit y] := by
  rw [evTail, neg_neg, Real.exp_log (hC.cdf_pos (expNegUnit_ne_zero x) (expNegUnit_ne_zero y))]

/-- Positive homogeneity of `ℓ_C`, from max-stability. -/
theorem evTail_smul (hC : C.IsExtremeValue) {s : ℝ} (hs : 0 < s) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : evTail C (s * x) (s * y) = s * evTail C x y := by
  have h := hC ![expNegUnit x, expNegUnit y] s hs
  have he : (fun i => unitPower (![expNegUnit x, expNegUnit y] i) s hs.le) =
      ![expNegUnit (s * x), expNegUnit (s * y)] := by
    funext i
    fin_cases i
    · apply Subtype.ext
      show Real.exp (-max x 0) ^ s = Real.exp (-max (s * x) 0)
      rw [max_eq_left hx, max_eq_left (mul_nonneg hs.le hx), ← Real.exp_mul]
      congr 1
      ring
    · apply Subtype.ext
      show Real.exp (-max y 0) ^ s = Real.exp (-max (s * y) 0)
      rw [max_eq_left hy, max_eq_left (mul_nonneg hs.le hy), ← Real.exp_mul]
      congr 1
      ring
  rw [he] at h
  rw [evTail, evTail, h, Real.log_rpow (hC.cdf_pos (expNegUnit_ne_zero x)
    (expNegUnit_ne_zero y))]
  ring

theorem evTail_zero_right (C : Copula 2) {x : ℝ} (hx : 0 ≤ x) : evTail C x 0 = x := by
  rw [evTail, expNegUnit_zero, cdf_two_one_right, coe_expNegUnit, max_eq_left hx,
    Real.log_exp, neg_neg]

theorem evTail_zero_left (C : Copula 2) {y : ℝ} (hy : 0 ≤ y) : evTail C 0 y = y := by
  rw [evTail, expNegUnit_zero, cdf_two_one_left, coe_expNegUnit, max_eq_left hy,
    Real.log_exp, neg_neg]

/-- The Fréchet upper bound: `max x y ≤ ℓ_C(x,y)`. -/
theorem max_le_evTail (hC : C.IsExtremeValue) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max x y ≤ evTail C x y := by
  have hle := C.cdf_le_comonotonic ![expNegUnit x, expNegUnit y]
  rw [cdf_comonotonic_two] at hle
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coe_expNegUnit, max_eq_left hx,
    max_eq_left hy] at hle
  have hmin : min (Real.exp (-x)) (Real.exp (-y)) = Real.exp (-max x y) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_right (Real.exp_le_exp.2 (neg_le_neg h))]
    · rw [max_eq_left h, min_eq_left (Real.exp_le_exp.2 (neg_le_neg h))]
  rw [hmin, ← hC.evTail_exp] at hle
  linarith [Real.exp_le_exp.1 hle]

private theorem le_of_forall_exp_rect {a b c d : ℝ}
    (h : ∀ ε > 0, 0 ≤ Real.exp (-(ε * a)) - Real.exp (-(ε * b)) - Real.exp (-(ε * c)) +
      Real.exp (-(ε * d))) : a + d ≤ b + c := by
  by_contra hcon
  push Not at hcon
  set η := a + d - b - c with hη
  have hηp : 0 < η := by linarith
  set ε := min (η / (2 * (a ^ 2 + d ^ 2 + 1))) (1 / (|a| + |d| + 1)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεa : |-(ε * a)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_pos hε0]
    calc ε * |a| ≤ 1 / (|a| + |d| + 1) * (|a| + |d| + 1) :=
          mul_le_mul (min_le_right _ _) (by linarith [abs_nonneg d]) (abs_nonneg a) (by positivity)
      _ = 1 := div_mul_cancel₀ 1 (by positivity)
  have hεd : |-(ε * d)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_pos hε0]
    calc ε * |d| ≤ 1 / (|a| + |d| + 1) * (|a| + |d| + 1) :=
          mul_le_mul (min_le_right _ _) (by linarith [abs_nonneg a]) (abs_nonneg d) (by positivity)
      _ = 1 := div_mul_cancel₀ 1 (by positivity)
  have ea := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hεa)).2
  have ed := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hεd)).2
  have eb := Real.add_one_le_exp (-(ε * b))
  have ec := Real.add_one_le_exp (-(ε * c))
  have hmain := h ε hε0
  -- `η ≤ ε (a² + d²)`
  have h1 : ε * η ≤ ε * (ε * (a ^ 2 + d ^ 2)) := by
    rw [hη]
    nlinarith
  have h2 : η ≤ ε * (a ^ 2 + d ^ 2) := le_of_mul_le_mul_left h1 hε0
  have h3 : ε * (a ^ 2 + d ^ 2) < η := by
    have hq : 0 < 2 * (a ^ 2 + d ^ 2 + 1) := by positivity
    calc ε * (a ^ 2 + d ^ 2) ≤ η / (2 * (a ^ 2 + d ^ 2 + 1)) * (a ^ 2 + d ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ < η := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hq]
          nlinarith [mul_pos hηp (show (0 : ℝ) < a ^ 2 + d ^ 2 + 2 by positivity)]
  linarith

/-- Submodularity of `ℓ_C` on `[0,∞)²`. -/
theorem evTail_submodular (hC : C.IsExtremeValue) {x x' y y' : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x')
    (hy : 0 ≤ y) (hyy : y ≤ y') :
    evTail C x y + evTail C x' y' ≤ evTail C x y' + evTail C x' y := by
  apply le_of_forall_exp_rect
  intro ε hε
  have hx' : 0 ≤ x' := hx.trans hxx
  have hy' : 0 ≤ y' := hy.trans hyy
  rw [← hC.evTail_smul hε hx hy, ← hC.evTail_smul hε hx' hy, ← hC.evTail_smul hε hx hy',
    ← hC.evTail_smul hε hx' hy', hC.evTail_exp, hC.evTail_exp, hC.evTail_exp, hC.evTail_exp]
  have hmono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : expNegUnit t ≤ expNegUnit s := by
    change Real.exp (-max t 0) ≤ Real.exp (-max s 0)
    rw [max_eq_left hs, max_eq_left (hs.trans hst)]
    exact Real.exp_le_exp.2 (neg_le_neg hst)
  have h1 : expNegUnit (ε * x') ≤ expNegUnit (ε * x) :=
    hmono (mul_nonneg hε.le hx) (mul_le_mul_of_nonneg_left hxx hε.le)
  have h2 : expNegUnit (ε * y') ≤ expNegUnit (ε * y) :=
    hmono (mul_nonneg hε.le hy) (mul_le_mul_of_nonneg_left hyy hε.le)
  have := rect_nonneg C h1 h2
  linarith

theorem continuous_pickandsOf (hC : C.IsExtremeValue) : Continuous (pickandsOf C) := by
  have hc : Continuous fun t : ℝ => C.cdf ![expNegUnit (1 - t), expNegUnit t] := by
    apply C.continuous_cdf.comp
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_expNegUnit.comp (by fun_prop)
    · exact continuous_expNegUnit
  exact (hc.log fun t => (hC.cdf_pos (expNegUnit_ne_zero _) (expNegUnit_ne_zero _)).ne').neg

theorem pickandsOf_zero (C : Copula 2) : pickandsOf C 0 = 1 := by
  rw [pickandsOf, sub_zero, evTail_zero_right C zero_le_one]

theorem pickandsOf_one (C : Copula 2) : pickandsOf C 1 = 1 := by
  rw [pickandsOf, sub_self, evTail_zero_left C zero_le_one]

/-- Scaling `ℓ_C` along a ray in terms of `A_C`. -/
theorem evTail_eq_mul_pickandsOf (hC : C.IsExtremeValue) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    evTail C x y = (x + y) * pickandsOf C (y / (x + y)) := by
  rcases eq_or_lt_of_le (add_nonneg hx hy) with h | h
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0 hy0
    rw [evTail_zero_left C le_rfl]
    ring
  · rw [pickandsOf, ← hC.evTail_smul h (by
        rw [sub_nonneg]; exact (pickands_ratio_mem hx hy).2) (pickands_ratio_mem hx hy).1]
    congr 1
    · rw [mul_sub, mul_div_cancel₀ _ h.ne', mul_one]
      ring
    · exact (mul_div_cancel₀ _ h.ne').symm

/-- The local three-point convexity inequality of `A_C` around `c ∈ (0,1)`. -/
theorem pickandsOf_local (hC : C.IsExtremeValue) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ p q, c - ε < p ∧ p < c ∧ c < q ∧ q < c + ε ∧
      (q - p) * pickandsOf C c ≤ (q - c) * pickandsOf C p + (c - p) * pickandsOf C q := by
  obtain ⟨hc0, hc1⟩ := hc
  have h1c : 0 < 1 - c := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos hε
  obtain ⟨D1, hD1⟩ : ∃ D : ℝ, D = 1 - c + (1 + δ) * c := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ D : ℝ, D = (1 + δ) * (1 - c) + c := ⟨_, rfl⟩
  have hD1p : 1 ≤ D1 := by rw [hD1]; nlinarith [mul_pos hδ0 hc0]
  have hD2p : 1 ≤ D2 := by rw [hD2]; nlinarith [mul_pos hδ0 h1c]
  have hD10 : D1 ≠ 0 := by positivity
  have hD20 : D2 ≠ 0 := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = c * (1 - c) * δ / (D1 * D2) := ⟨_, rfl⟩
  have hk0 : 0 < k := by
    rw [hk]
    exact div_pos (mul_pos (mul_pos hc0 h1c) hδ0) (mul_pos (by linarith) (by linarith))
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 + δ) * c / D1 := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = c / D2 := ⟨_, rfl⟩
  have hqc : q - c = D2 * k := by
    rw [hq, hk]
    field_simp
    rw [hD1]
    ring
  have hcp : c - p = D1 * k := by
    rw [hp, hk]
    field_simp
    rw [hD2]
    ring
  have hcc : c * (1 - c) ≤ 1 := by nlinarith
  have hcδ : c * (1 - c) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hcc hδ0.le
  have hb1 : D2 * k ≤ δ := by
    rw [hk, show D2 * (c * (1 - c) * δ / (D1 * D2)) = c * (1 - c) * δ / D1 by
      field_simp, div_le_iff₀ (by linarith)]
    nlinarith
  have hb2 : D1 * k ≤ δ := by
    rw [hk, show D1 * (c * (1 - c) * δ / (D1 * D2)) = c * (1 - c) * δ / D2 by
      field_simp, div_le_iff₀ (by linarith)]
    nlinarith
  have hD1k : 0 < D1 * k := mul_pos (by linarith) hk0
  have hD2k : 0 < D2 * k := mul_pos (by linarith) hk0
  refine ⟨p, q, by linarith, by linarith, by linarith, by linarith, ?_⟩
  -- the submodularity inequality on the rectangle `[1-c, λ(1-c)] × [c, λc]`, `λ = 1 + δ`
  have hlam1 : (1 : ℝ) ≤ 1 + δ := by linarith
  have hsub := hC.evTail_submodular h1c.le (le_mul_of_one_le_left h1c.le hlam1) hc0.le
    (le_mul_of_one_le_left hc0.le hlam1)
  have e1 : evTail C (1 - c) c = pickandsOf C c := rfl
  have e2 : evTail C ((1 + δ) * (1 - c)) ((1 + δ) * c) = (1 + δ) * pickandsOf C c :=
    hC.evTail_smul (by linarith) h1c.le hc0.le
  have e3 : evTail C (1 - c) ((1 + δ) * c) = D1 * pickandsOf C q := by
    rw [hC.evTail_eq_mul_pickandsOf h1c.le (mul_pos (by linarith) hc0).le, hq, hD1]
  have e4 : evTail C ((1 + δ) * (1 - c)) c = D2 * pickandsOf C p := by
    rw [hC.evTail_eq_mul_pickandsOf (mul_pos (by linarith) h1c).le hc0.le, hp, hD2]
  rw [e1, e2, e3, e4] at hsub
  have hsum : D1 + D2 = 2 + δ := by rw [hD1, hD2]; ring
  have hmul := mul_le_mul_of_nonneg_left hsub hk0.le
  have hk2 : k * pickandsOf C c * (D1 + D2) = k * pickandsOf C c * (2 + δ) := by rw [hsum]
  rw [show q - p = D2 * k + D1 * k by linarith, hqc, hcp]
  linarith

/-- The Pickands function of a bivariate extreme-value copula is a Pickands dependence
function. -/
theorem isPickandsFunction_pickandsOf (hC : C.IsExtremeValue) :
    IsPickandsFunction (pickandsOf C) := by
  have hconv : ConvexOn ℝ (Icc 0 1) (pickandsOf C) :=
    convexOn_Icc_of_local hC.continuous_pickandsOf.continuousOn
      (fun c hc ε hε => hC.pickandsOf_local hc hε)
  refine ⟨hconv, fun t ht => ?_, fun t ht => ?_⟩
  · have h := hconv.2 (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
      (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (sub_nonneg.2 ht.2) ht.1
      (sub_add_cancel 1 t)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, pickandsOf_zero, pickandsOf_one] at h
    linarith
  · rw [pickandsOf, max_comm]
    exact hC.max_le_evTail (sub_nonneg.2 ht.2) ht.1

/-- **Pickands representation.** Every bivariate extreme-value copula is the Pickands copula of
its Pickands function `A_C(t) = -log C(e^{-(1-t)}, e^{-t})`. -/
theorem eq_pickandsCopula (hC : C.IsExtremeValue) :
    C = pickandsCopula (pickandsOf C) hC.isPickandsFunction_pickandsOf := by
  apply ext_cdf_two
  intro u v
  rw [cdf_pickandsCopula_two, pickandsCDF]
  split_ifs with h
  · rcases h with h | h
    · simp [h]
    · simpa [h] using C.cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  · push Not at h
    have hx : 0 ≤ -Real.log u := neg_nonneg.2 (Real.log_nonpos u.2.1 u.2.2)
    have hy : 0 ≤ -Real.log v := neg_nonneg.2 (Real.log_nonpos v.2.1 v.2.2)
    rw [pickandsTail, ← hC.evTail_eq_mul_pickandsOf hx hy, hC.evTail_exp,
      expNegUnit_neg_log h.1, expNegUnit_neg_log h.2]

end IsExtremeValue

/-- On `[0,1]`, the Pickands function of `C_A` is `A`. -/
theorem pickandsOf_pickandsCopula {A : ℝ → ℝ} (hA : IsPickandsFunction A) :
    EqOn (pickandsOf (pickandsCopula A hA)) A (Icc 0 1) := by
  intro t ht
  rw [pickandsOf, evTail, cdf_pickandsCopula_expNegUnit hA ht, Real.log_exp, neg_neg]

/-- The bivariate extreme-value copulas are exactly the Pickands copulas. -/
theorem isExtremeValue_iff_exists_pickands (C : Copula 2) :
    C.IsExtremeValue ↔ ∃ (A : ℝ → ℝ) (hA : IsPickandsFunction A), C = pickandsCopula A hA := by
  constructor
  · intro hC
    exact ⟨_, _, hC.eq_pickandsCopula⟩
  · rintro ⟨A, hA, rfl⟩
    exact isExtremeValue_pickandsCopula hA

/-- Every bivariate extreme-value copula is positively quadrant dependent. -/
theorem IsExtremeValue.isPQD {C : Copula 2} (hC : C.IsExtremeValue) : C.IsPQD := by
  rw [hC.eq_pickandsCopula]
  exact isPQD_pickandsCopula _

/-- For extreme-value copulas, `C ≤ D` pointwise iff `A_D ≤ A_C` on `[0,1]`. -/
theorem IsExtremeValue.lowerOrthantLE_iff {C D : Copula 2} (hC : C.IsExtremeValue)
    (hD : D.IsExtremeValue) :
    C.LowerOrthantLE D ↔ ∀ t ∈ Icc (0 : ℝ) 1, pickandsOf D t ≤ pickandsOf C t := by
  conv_lhs => rw [hC.eq_pickandsCopula, hD.eq_pickandsCopula]
  exact pickandsCopula_lowerOrthantLE_iff _ _

/-- Two extreme-value copulas coincide iff their Pickands functions agree on `[0,1]`. -/
theorem IsExtremeValue.eq_iff {C D : Copula 2} (hC : C.IsExtremeValue)
    (hD : D.IsExtremeValue) : C = D ↔ EqOn (pickandsOf C) (pickandsOf D) (Icc 0 1) := by
  conv_lhs => rw [hC.eq_pickandsCopula, hD.eq_pickandsCopula]
  exact pickandsCopula_eq_iff _ _

end ProbabilityTheory.Copula
