/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.LevelCurves
import Copula.Archimedean.Clayton
import Copula.Archimedean.Exponential
import Copula.Order.Rank
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Concordance ordering of Archimedean copulas via generators

Nelsen, *An Introduction to Copulas*, second edition, Theorem 4.4.2: for Archimedean copulas
`C₁`, `C₂` with generators `φ₁`, `φ₂`, `C₁ ≺ C₂` (pointwise `C₁ ≤ C₂`) iff `f = φ₁ ∘ φ₂^[-1]` is
subadditive. We prove this for a strict second generator (`ψ₂ > 0`, so `f = φ₁ ∘ ψ₂` is
defined on all of `[0, ∞)`), with the first generator arbitrary (strict or not):

* `BivariateGenerator.lowerOrthantLE_iff_subadditive`: Theorem 4.4.2;
* `subadditive_of_concaveOn` and `BivariateGenerator.lowerOrthantLE_of_concaveOn`: Nelsen's
  Corollary 4.4.3 (a concave `f` with `f(0) ≥ 0` is subadditive);
* `BivariateGenerator.isPQD_iff` (Nelsen, Section 4.4 / Exercise 4.19-type statement): a strict
  Archimedean copula is positively quadrant dependent iff `ψ(x) ψ(y) ≤ ψ(x + y)`
  (`−log ψ` subadditive); `BivariateGenerator.not_isPQD_of_not_isStrict`: non-strict
  Archimedean copulas are never PQD;
* `BivariateGenerator.isNQD_iff`: an Archimedean copula is negatively quadrant dependent iff
  `φ(uv) ≤ φ(u) + φ(v)` on `(0, 1]`;
* `lowerOrthantLE_clayton`: Clayton's family is increasing in `θ > 0` in the concordance order
  (`f(s) = (1 + s)^{θ₁/θ₂} − 1` is concave for `θ₁ ≤ θ₂`). (For Gumbel's family the ordering is
  `lowerOrthantLE_gumbel` in `Copula.Dependence.Gumbel`.)
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Nelsen, Corollary 4.4.3: a concave function on `[0, ∞)` with `f(0) ≥ 0` is subadditive. -/
theorem subadditive_of_concaveOn {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f) (h0 : 0 ≤ f 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : f (x + y) ≤ f x + f y := by
  rcases (add_nonneg hx hy).lt_or_eq with hs | hs
  · have key : ∀ z, 0 ≤ z → z ≤ x + y → z / (x + y) * f (x + y) ≤ f z := by
      intro z hz0 hzs
      have ha : 0 ≤ z / (x + y) := div_nonneg hz0 hs.le
      have hb : 0 ≤ 1 - z / (x + y) := by
        rw [sub_nonneg, div_le_one hs]; exact hzs
      have h := hf.2 (mem_Ici.mpr hs.le) (mem_Ici.mpr le_rfl : (0 : ℝ) ∈ Ici 0) ha hb
        (by ring)
      simp only [smul_eq_mul, mul_zero, add_zero] at h
      rw [div_mul_cancel₀ _ hs.ne'] at h
      nlinarith [mul_nonneg hb h0]
    have h1 := key x hx (by linarith)
    have h2 := key y hy (by linarith)
    have : x / (x + y) * f (x + y) + y / (x + y) * f (x + y) = f (x + y) := by
      rw [← add_mul, ← add_div, div_self hs.ne', one_mul]
    linarith
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0; subst hy0
    simpa using h0

namespace BivariateGenerator

/-- The real extension of the generator at a value of an inverse generator. -/
private theorem invFunReal_toFun_eq (g₁ g₂ : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) :
    g₁.invFunReal (g₂.toFun s) = g₁.invFun (g₂.toI hs) := by
  rw [invFunReal, projIcc_of_mem _ ⟨g₂.nonneg s hs, g₂.toFun_le_one hs⟩]
  rfl

/-- Nelsen, Theorem 4.4.2 (strict second generator): `C₁ ≤ C₂` pointwise iff
`f = φ₁ ∘ ψ₂` is subadditive on `[0, ∞)`. -/
theorem lowerOrthantLE_iff_subadditive (g₁ g₂ : BivariateGenerator) (h₂ : g₂.IsStrict) :
    g₁.copula.LowerOrthantLE g₂.copula ↔
      ∀ x y, 0 ≤ x → 0 ≤ y → g₁.invFunReal (g₂.toFun (x + y)) ≤
        g₁.invFunReal (g₂.toFun x) + g₁.invFunReal (g₂.toFun y) := by
  constructor
  · intro hle x y hx hy
    have hxy : 0 ≤ x + y := add_nonneg hx hy
    set u := g₂.toI hx
    set v := g₂.toI hy
    have hu : u ≠ 0 := g₂.toI_ne_zero hx (h₂ x hx)
    have hv : v ≠ 0 := g₂.toI_ne_zero hy (h₂ y hy)
    have hc := hle ![u, v]
    simp only [cdf_copula, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    rw [cdf, ite_or_of_not hu hv, cdf, ite_or_of_not hu hv, g₂.invFun_toI hx (h₂ x hx),
      g₂.invFun_toI hy (h₂ y hy)] at hc
    rw [invFunReal_toFun_eq g₁ g₂ hxy, invFunReal_toFun_eq g₁ g₂ hx, invFunReal_toFun_eq g₁ g₂ hy]
    set w := g₂.toI hxy
    have hw : w ≠ 0 := g₂.toI_ne_zero hxy (h₂ _ hxy)
    have hs0 : 0 ≤ g₁.invFun u + g₁.invFun v :=
      add_nonneg (g₁.inv_nonneg u hu) (g₁.inv_nonneg v hv)
    by_contra hlt
    push Not at hlt
    have hwpos : 0 < g₁.toFun (g₁.invFun w) := by
      rw [g₁.right_inv w hw]; exact coe_pos hw
    have h := g₁.toFun_lt_of_lt hs0 hlt hwpos
    rw [g₁.right_inv w hw] at h
    change (w : ℝ) < _ at h
    have : (w : ℝ) = g₂.toFun (x + y) := rfl
    linarith
  · intro hsub z
    rw [cdf_copula, cdf_copula]
    by_cases hz : z 0 = 0 ∨ z 1 = 0
    · simp only [cdf, hz, ite_true, le_refl]
    rw [cdf, ite_eq_right hz, cdf, ite_eq_right hz]
    push Not at hz
    set a := g₂.invFun (z 0)
    set b := g₂.invFun (z 1)
    have ha : 0 ≤ a := g₂.inv_nonneg _ hz.1
    have hb : 0 ≤ b := g₂.inv_nonneg _ hz.2
    have hfa : g₁.invFunReal (g₂.toFun a) = g₁.invFun (z 0) := by
      rw [g₂.right_inv _ hz.1, invFunReal_coe]
    have hfb : g₁.invFunReal (g₂.toFun b) = g₁.invFun (z 1) := by
      rw [g₂.right_inv _ hz.2, invFunReal_coe]
    have hs := hsub a b ha hb
    rw [hfa, hfb, invFunReal_toFun_eq g₁ g₂ (add_nonneg ha hb)] at hs
    set w := g₂.toI (add_nonneg ha hb)
    have hw : w ≠ 0 := g₂.toI_ne_zero _ (h₂ _ (add_nonneg ha hb))
    have h := g₁.antitone_nonneg (g₁.inv_nonneg w hw)
      (add_nonneg (g₁.inv_nonneg _ hz.1) (g₁.inv_nonneg _ hz.2)) hs
    rw [g₁.right_inv w hw] at h
    exact h

/-- Nelsen, Corollary 4.4.3: if `f = φ₁ ∘ ψ₂` is concave on `[0, ∞)` (and `ψ₂` is strict),
then `C₁ ≤ C₂`. -/
theorem lowerOrthantLE_of_concaveOn (g₁ g₂ : BivariateGenerator) (h₂ : g₂.IsStrict)
    (hf : ConcaveOn ℝ (Ici 0) (fun s => g₁.invFunReal (g₂.toFun s))) :
    g₁.copula.LowerOrthantLE g₂.copula := by
  rw [lowerOrthantLE_iff_subadditive g₁ g₂ h₂]
  intro x y hx hy
  have h0 : 0 ≤ g₁.invFunReal (g₂.toFun 0) := by
    rw [g₂.toFun_zero, show (1 : ℝ) = ((1 : I) : ℝ) from rfl, invFunReal_coe, g₁.inv_one]
  exact subadditive_of_concaveOn hf h0 hx hy

/-- A strict Archimedean copula is PQD iff `ψ(x) ψ(y) ≤ ψ(x + y)` for all `x, y ≥ 0`
(equivalently, `−log ψ` is subadditive; Nelsen, Section 4.4). -/
theorem isPQD_iff (g : BivariateGenerator) (hg : g.IsStrict) :
    g.copula.IsPQD ↔ ∀ x y, 0 ≤ x → 0 ≤ y → g.toFun x * g.toFun y ≤ g.toFun (x + y) := by
  rw [isPQD_iff_lowerOrthantLE, ← exponentialGenerator_copula,
    lowerOrthantLE_iff_subadditive _ _ hg]
  have hφ : ∀ s, 0 ≤ s → exponentialGenerator.invFunReal (g.toFun s) = -Real.log (g.toFun s) := by
    intro s hs
    rw [invFunReal_toFun_eq exponentialGenerator g hs]
    rfl
  constructor
  · intro h x y hx hy
    have h1 := h x y hx hy
    rw [hφ _ (add_nonneg hx hy), hφ _ hx, hφ _ hy] at h1
    have hpx := hg x hx
    have hpy := hg y hy
    have hpxy := hg _ (add_nonneg hx hy)
    rw [← Real.log_le_log_iff (mul_pos hpx hpy) hpxy, Real.log_mul hpx.ne' hpy.ne']
    linarith
  · intro h x y hx hy
    have h1 := h x y hx hy
    rw [hφ _ (add_nonneg hx hy), hφ _ hx, hφ _ hy]
    have hpx := hg x hx
    have hpy := hg y hy
    have h2 := Real.log_le_log (mul_pos hpx hpy) h1
    rw [Real.log_mul hpx.ne' hpy.ne'] at h2
    linarith

/-- A non-strict Archimedean copula is never PQD: its diagonal vanishes near zero. -/
theorem not_isPQD_of_not_isStrict (g : BivariateGenerator) (hg : ¬ g.IsStrict) :
    ¬ g.copula.IsPQD := by
  intro hpqd
  obtain ⟨t₀, ht₀, hz⟩ := g.exists_diagonal_eq_zero hg
  have h := hpqd t₀ t₀
  have hdiag : g.copula.cdf ![t₀, t₀] = 0 := by
    rw [cdf_copula]
    exact hz t₀ le_rfl
  rw [hdiag] at h
  have hp := coe_pos ht₀
  nlinarith

/-- An Archimedean copula is NQD iff `φ(uv) ≤ φ(u) + φ(v)` for all `u, v ∈ (0, 1]`
(Nelsen, Section 4.4, with `C₂ = Π` in Theorem 4.4.2). -/
theorem isNQD_iff (g : BivariateGenerator) :
    g.copula.IsNQD ↔ ∀ u v : ℝ, 0 < u → u ≤ 1 → 0 < v → v ≤ 1 →
      g.invFunReal (u * v) ≤ g.invFunReal u + g.invFunReal v := by
  have hstrict : exponentialGenerator.IsStrict := fun s _ => Real.exp_pos _
  have hNQD : g.copula.IsNQD ↔ g.copula.LowerOrthantLE (independence 2) := by
    constructor
    · intro h z
      have hz : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
      rw [hz, cdf_independence, Fin.prod_univ_two]
      exact h (z 0) (z 1)
    · intro h u v
      have := h ![u, v]
      rwa [cdf_independence, Fin.prod_univ_two] at this
  rw [hNQD, ← exponentialGenerator_copula, lowerOrthantLE_iff_subadditive _ _ hstrict]
  change (∀ x y, 0 ≤ x → 0 ≤ y → g.invFunReal (Real.exp (-(x + y))) ≤
      g.invFunReal (Real.exp (-x)) + g.invFunReal (Real.exp (-y))) ↔ _
  constructor
  · intro h u v hu0 hu1 hv0 hv1
    have hx : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu0.le hu1)
    have hy : 0 ≤ -Real.log v := neg_nonneg.mpr (Real.log_nonpos hv0.le hv1)
    have h1 := h _ _ hx hy
    rw [neg_add, neg_neg, neg_neg, Real.exp_add, Real.exp_log hu0, Real.exp_log hv0] at h1
    exact h1
  · intro h x y hx hy
    have h1 := h (Real.exp (-x)) (Real.exp (-y)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))
    rw [← Real.exp_add, ← neg_add] at h1
    exact h1

end BivariateGenerator

/-- Clayton's family is increasing in `θ > 0` in the lower-orthant (concordance) order:
`f(s) = φ_θ(ψ_η(s)) = (1 + s)^{θ/η} − 1` is concave for `θ ≤ η` (Nelsen, Example 4.19-type). -/
theorem lowerOrthantLE_clayton {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hθη : θ ≤ η) :
    (clayton 2 θ hθ).LowerOrthantLE (clayton 2 η hη) := by
  rw [← claytonGenerator_copula θ hθ, ← claytonGenerator_copula η hη]
  have hstrict : (claytonGenerator η hη).IsStrict := fun s hs =>
    Real.rpow_pos_of_pos (by linarith) _
  apply BivariateGenerator.lowerOrthantLE_of_concaveOn _ _ hstrict
  set p := θ / η with hp
  have hp0 : 0 ≤ p := div_nonneg hθ.le hη.le
  have hp1 : p ≤ 1 := (div_le_one hη).mpr hθη
  have hf : ∀ s, 0 ≤ s → (claytonGenerator θ hθ).invFunReal ((claytonGenerator η hη).toFun s) =
      (1 + s) ^ p - 1 := by
    intro s hs
    rw [BivariateGenerator.invFunReal, projIcc_of_mem _ ⟨(claytonGenerator η hη).nonneg s hs,
      (claytonGenerator η hη).toFun_le_one hs⟩]
    change ((1 + s) ^ (-η⁻¹)) ^ (-θ) - 1 = _
    rw [← Real.rpow_mul (by linarith), show -η⁻¹ * -θ = p by rw [hp]; field_simp]
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hxy : 0 ≤ a • x + b • y := by simp only [smul_eq_mul]; positivity
  simp only [smul_eq_mul] at hxy ⊢
  rw [hf x hx0, hf y hy0, hf _ hxy]
  have hc := (Real.concaveOn_rpow hp0 hp1).2 (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ 1 + x))
    (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ 1 + y)) ha hb hab
  simp only [smul_eq_mul] at hc
  have he : a * (1 + x) + b * (1 + y) = 1 + (a * x + b * y) := by linear_combination hab
  rw [he] at hc
  nlinarith

end ProbabilityTheory.Copula
