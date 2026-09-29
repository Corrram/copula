/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Concordance
import Copula.Archimedean.Power
import Copula.TailDependence.Quadrant
import Copula.Reflection.Bivariate

/-! # Criteria for quadrant dependence of Archimedean copulas

For a bivariate Archimedean generator `g` with inverse generator `ψ = g.toFun` (Nelsen,
*An Introduction to Copulas*, second edition, Section 4.4 with `C₂ = Π`), we prove two-sided
criteria that do not need strictness of `ψ`:

* `isPQD_of_psi` / `not_isPQD_of_psi`: `C` is PQD as soon as `ψ(x) ψ(y) ≤ ψ(x + y)` for all
  `x, y ≥ 0`, and it is not PQD as soon as `ψ(x + y) < ψ(x) ψ(y)` for one pair;
* `isNQD_of_psi` / `not_isNQD_of_psi`: the reverse inequalities give NQD and non-NQD;
* `isPQD_of_phi` / `not_isPQD_of_phi`: the same statements in terms of the generator `φ`,
  `φ(u) + φ(v) ≤ φ(u v)`;
* `not_isNQD_of_hasLowerTailDependence`, `not_isNQD_of_hasUpperTailDependence`: a nonzero tail
  coefficient excludes NQD;
* `isNQD_reflect_iff`, `isPQD_reflect_iff`: reflecting the second coordinate swaps PQD and NQD.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

variable (g : BivariateGenerator)

private theorem cdf_eq_of_ne (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    g.copula.cdf ![u, v] = g.toFun (g.invFun u + g.invFun v) := by
  rw [cdf_copula]
  show g.cdf u v = _
  simp [cdf, hu, hv]

/-- On `(0, 1]` the real extension `invFunReal` agrees with `invFun`. -/
theorem invFunReal_of_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    g.invFunReal x = g.invFun ⟨x, hx0.le, hx1⟩ := by
  rw [invFunReal, projIcc_of_mem _ ⟨hx0.le, hx1⟩]

/-- `ψ (φ x) = x` on `(0, 1]`, for the real extension `invFunReal`. -/
theorem toFun_invFunReal {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    g.toFun (g.invFunReal x) = x := by
  have h := g.right_inv ⟨x, hx0.le, hx1⟩ (by
    intro h; have := congrArg (fun v : I => (v : ℝ)) h; simp at this; linarith)
  rw [show x = ((⟨x, hx0.le, hx1⟩ : I) : ℝ) from rfl, invFunReal_coe]
  exact h

/-- Sufficient criterion for PQD: `ψ(x) ψ(y) ≤ ψ(x + y)` for all `x, y ≥ 0`. -/
theorem isPQD_of_psi (h : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g.toFun x * g.toFun y ≤ g.toFun (x + y)) :
    g.copula.IsPQD := by
  intro u v
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  rw [cdf_eq_of_ne g u v hu hv]
  have := h (g.invFun u) (g.invFun v) (g.inv_nonneg u hu) (g.inv_nonneg v hv)
  rwa [g.right_inv u hu, g.right_inv v hv] at this

/-- Sufficient criterion for NQD: `ψ(x + y) ≤ ψ(x) ψ(y)` for all `x, y ≥ 0`. -/
theorem isNQD_of_psi (h : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g.toFun (x + y) ≤ g.toFun x * g.toFun y) :
    g.copula.IsNQD := by
  intro u v
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  rw [cdf_eq_of_ne g u v hu hv]
  have := h (g.invFun u) (g.invFun v) (g.inv_nonneg u hu) (g.inv_nonneg v hv)
  rwa [g.right_inv u hu, g.right_inv v hv] at this

/-- A pair `x, y ≥ 0` with `ψ(x + y) < ψ(x) ψ(y)` shows that `C` is not PQD. -/
theorem not_isPQD_of_psi {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : g.toFun (x + y) < g.toFun x * g.toFun y) : ¬ g.copula.IsPQD := by
  intro hP
  have h0 : 0 ≤ g.toFun (x + y) := g.nonneg _ (add_nonneg hx hy)
  have hxy : 0 < g.toFun x * g.toFun y := lt_of_le_of_lt h0 h
  have hx0 : 0 < g.toFun x := by
    by_contra hc
    have : g.toFun x = 0 := le_antisymm (not_lt.mp hc) (g.nonneg _ hx)
    rw [this, zero_mul] at hxy; exact lt_irrefl _ hxy
  have hy0 : 0 < g.toFun y := by
    by_contra hc
    have : g.toFun y = 0 := le_antisymm (not_lt.mp hc) (g.nonneg _ hy)
    rw [this, mul_zero] at hxy; exact lt_irrefl _ hxy
  have := hP (g.toI hx) (g.toI hy)
  rw [cdf_eq_of_ne g _ _ (g.toI_ne_zero hx hx0) (g.toI_ne_zero hy hy0), g.invFun_toI hx hx0,
    g.invFun_toI hy hy0] at this
  simp only [coe_toI] at this
  linarith

/-- A pair `x, y ≥ 0` with `ψ(x) ψ(y) < ψ(x + y)` shows that `C` is not NQD. -/
theorem not_isNQD_of_psi {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : g.toFun x * g.toFun y < g.toFun (x + y)) : ¬ g.copula.IsNQD := by
  intro hN
  have hxy : 0 < g.toFun (x + y) :=
    lt_of_le_of_lt (mul_nonneg (g.nonneg _ hx) (g.nonneg _ hy)) h
  have hx0 : 0 < g.toFun x :=
    lt_of_lt_of_le hxy (g.antitone_nonneg hx (add_nonneg hx hy) (by linarith))
  have hy0 : 0 < g.toFun y :=
    lt_of_lt_of_le hxy (g.antitone_nonneg hy (add_nonneg hx hy) (by linarith))
  have := hN (g.toI hx) (g.toI hy)
  rw [cdf_eq_of_ne g _ _ (g.toI_ne_zero hx hx0) (g.toI_ne_zero hy hy0), g.invFun_toI hx hx0,
    g.invFun_toI hy hy0] at this
  simp only [coe_toI] at this
  linarith

/-- PQD is equivalent to `ψ(x) ψ(y) ≤ ψ(x + y)` for all `x, y ≥ 0`. -/
theorem isPQD_iff_psi :
    g.copula.IsPQD ↔ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g.toFun x * g.toFun y ≤ g.toFun (x + y) := by
  refine ⟨fun h x y hx hy => ?_, isPQD_of_psi g⟩
  by_contra hc
  exact not_isPQD_of_psi g hx hy (not_le.mp hc) h

/-- NQD is equivalent to `ψ(x + y) ≤ ψ(x) ψ(y)` for all `x, y ≥ 0`. -/
theorem isNQD_iff_psi :
    g.copula.IsNQD ↔ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g.toFun (x + y) ≤ g.toFun x * g.toFun y := by
  refine ⟨fun h x y hx hy => ?_, isNQD_of_psi g⟩
  by_contra hc
  exact not_isNQD_of_psi g hx hy (not_le.mp hc) h

/-- Inner powers `ψ ^ q` (`q ≥ 1`) preserve NQD. -/
theorem isNQD_innerPower (q : ℝ) (hq : 1 ≤ q) (h : g.copula.IsNQD) :
    (g.innerPower q hq).copula.IsNQD := by
  rw [isNQD_iff_psi] at h ⊢
  intro x y hx hy
  show g.toFun (x + y) ^ q ≤ g.toFun x ^ q * g.toFun y ^ q
  rw [← Real.mul_rpow (g.nonneg _ hx) (g.nonneg _ hy)]
  exact Real.rpow_le_rpow (g.nonneg _ (add_nonneg hx hy)) (h x y hx hy) (by linarith)

/-- Inner powers `ψ ^ q` (`q ≥ 1`) preserve PQD. -/
theorem isPQD_innerPower (q : ℝ) (hq : 1 ≤ q) (h : g.copula.IsPQD) :
    (g.innerPower q hq).copula.IsPQD := by
  rw [isPQD_iff_psi] at h ⊢
  intro x y hx hy
  show g.toFun x ^ q * g.toFun y ^ q ≤ g.toFun (x + y) ^ q
  rw [← Real.mul_rpow (g.nonneg _ hx) (g.nonneg _ hy)]
  exact Real.rpow_le_rpow (mul_nonneg (g.nonneg _ hx) (g.nonneg _ hy)) (h x y hx hy)
    (by linarith)

/-- Sufficient criterion for PQD in terms of the generator: `φ(u) + φ(v) ≤ φ(u v)`. -/
theorem isPQD_of_phi (h : ∀ u v : ℝ, 0 < u → u ≤ 1 → 0 < v → v ≤ 1 →
    g.invFunReal u + g.invFunReal v ≤ g.invFunReal (u * v)) : g.copula.IsPQD := by
  intro u v
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  rw [cdf_eq_of_ne g u v hu hv]
  have hu0 := coe_pos hu
  have hv0 := coe_pos hv
  have hle := h u v hu0 u.property.2 hv0 v.property.2
  rw [invFunReal_coe, invFunReal_coe] at hle
  have hn : 0 ≤ g.invFunReal ((u : ℝ) * v) := by
    rw [← g.toFun_invFunReal (mul_pos hu0 hv0) (by nlinarith [u.property.2, v.property.2])] at *
    exact le_trans (add_nonneg (g.inv_nonneg u hu) (g.inv_nonneg v hv)) hle
  have := g.antitone_nonneg (add_nonneg (g.inv_nonneg u hu) (g.inv_nonneg v hv)) hn hle
  rwa [g.toFun_invFunReal (mul_pos hu0 hv0) (by nlinarith [u.property.2, v.property.2])] at this

/-- If `φ(u v) < φ(u) + φ(v)` for some `u, v ∈ (0, 1]`, then `C` is not PQD. -/
theorem not_isPQD_of_phi {u v : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hv0 : 0 < v) (hv1 : v ≤ 1)
    (h : g.invFunReal (u * v) < g.invFunReal u + g.invFunReal v) : ¬ g.copula.IsPQD := by
  intro hP
  have hP' := hP ⟨u, hu0.le, hu1⟩ ⟨v, hv0.le, hv1⟩
  have hu' : (⟨u, hu0.le, hu1⟩ : I) ≠ 0 := by
    intro hh; have := congrArg (fun v : I => (v : ℝ)) hh; simp at this; linarith
  have hv' : (⟨v, hv0.le, hv1⟩ : I) ≠ 0 := by
    intro hh; have := congrArg (fun v : I => (v : ℝ)) hh; simp at this; linarith
  rw [cdf_eq_of_ne g _ _ hu' hv'] at hP'
  have e1 : g.invFun ⟨u, hu0.le, hu1⟩ = g.invFunReal u := (invFunReal_coe g ⟨u, hu0.le, hu1⟩).symm
  have e2 : g.invFun ⟨v, hv0.le, hv1⟩ = g.invFunReal v := (invFunReal_coe g ⟨v, hv0.le, hv1⟩).symm
  rw [e1, e2] at hP'
  have hw1 : u * v ≤ 1 := by nlinarith
  have hn : 0 ≤ g.invFunReal (u * v) := by
    have := g.inv_nonneg ⟨u * v, (mul_pos hu0 hv0).le, hw1⟩ (by
      intro hh; have := congrArg (fun v : I => (v : ℝ)) hh; simp at this
      rcases this with h | h <;> linarith)
    rwa [← invFunReal_coe g ⟨u * v, (mul_pos hu0 hv0).le, hw1⟩] at this
  have hsum : 0 ≤ g.invFunReal u + g.invFunReal v := le_trans hn h.le
  have hw := g.toFun_invFunReal (mul_pos hu0 hv0) hw1
  have key : g.toFun (g.invFunReal u + g.invFunReal v) < u * v := by
    by_cases hz : g.toFun (g.invFunReal u + g.invFunReal v) = 0
    · rw [hz]; exact mul_pos hu0 hv0
    · have := g.toFun_lt_of_lt hn h (lt_of_le_of_ne (g.nonneg _ hsum) (Ne.symm hz))
      rwa [hw] at this
  linarith

end BivariateGenerator

/-- A nonzero lower tail coefficient excludes NQD. -/
theorem not_isNQD_of_hasLowerTailDependence {C : Copula 2} {l : ℝ}
    (h : C.HasLowerTailDependence l) (hl : l ≠ 0) : ¬ C.IsNQD :=
  fun hN => hl (h.unique (isNQD_hasLowerTailDependence_zero hN))

/-- A nonzero upper tail coefficient excludes NQD. -/
theorem not_isNQD_of_hasUpperTailDependence {C : Copula 2} {l : ℝ}
    (h : C.HasUpperTailDependence l) (hl : l ≠ 0) : ¬ C.IsNQD :=
  fun hN => hl (h.unique (isNQD_hasUpperTailDependence_zero hN))

/-- Reflecting the second coordinate turns PQD into NQD. -/
theorem isNQD_reflect_of_isPQD {C : Copula 2} (h : C.IsPQD) : (C.reflect {1}).IsNQD := by
  intro u v
  rw [cdf_reflect_second]
  have := h u (unitInterval.symm v)
  simp only [unitInterval.coe_symm_eq] at this
  nlinarith

/-- Reflecting the second coordinate turns NQD into PQD. -/
theorem isPQD_reflect_of_isNQD {C : Copula 2} (h : C.IsNQD) : (C.reflect {1}).IsPQD := by
  intro u v
  rw [cdf_reflect_second]
  have := h u (unitInterval.symm v)
  simp only [unitInterval.coe_symm_eq] at this
  nlinarith

/-- If `C` is not NQD, its second-coordinate reflection is not PQD. -/
theorem not_isPQD_reflect_of_not_isNQD {C : Copula 2} (h : ¬ C.IsNQD) : ¬ (C.reflect {1}).IsPQD := by
  intro hP
  apply h
  intro u v
  have := hP u (unitInterval.symm v)
  rw [cdf_reflect_second] at this
  simp only [unitInterval.symm_symm, unitInterval.coe_symm_eq] at this
  nlinarith

/-- If `C` is not PQD, its second-coordinate reflection is not NQD. -/
theorem not_isNQD_reflect_of_not_isPQD {C : Copula 2} (h : ¬ C.IsPQD) : ¬ (C.reflect {1}).IsNQD := by
  intro hN
  apply h
  intro u v
  have := hN u (unitInterval.symm v)
  rw [cdf_reflect_second] at this
  simp only [unitInterval.symm_symm, unitInterval.coe_symm_eq] at this
  nlinarith

end ProbabilityTheory.Copula
