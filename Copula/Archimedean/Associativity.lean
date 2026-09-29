/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Theory

/-! # Algebraic properties of bivariate Archimedean copulas

Nelsen, *An Introduction to Copulas*, second edition, Theorem 4.1.5: a bivariate
Archimedean copula `C(u, v) = ψ(φ(u) + φ(v))` is

1. symmetric, `C(u, v) = C(v, u)` (`BivariateGenerator.op_comm`);
2. associative, `C(C(u, v), w) = C(u, C(v, w))` (`BivariateGenerator.op_assoc`);
3. unchanged when the generator `φ` is replaced by `c φ` for a constant `c > 0`
   (`BivariateGenerator.scale`, `BivariateGenerator.scale_copula`).

To state associativity, `BivariateGenerator.op` regards the copula as a binary
operation on the unit interval. Associativity holds for strict and non-strict
generators alike: the zero set is handled by the key identity
`C(u, ψ(s)) = ψ(φ(u) + s)` (`BivariateGenerator.cdf_toI`), which is also valid when
`ψ(s) = 0`. The operation has neutral element `1` and absorbing element `0`, so
`(I, op)` is a commutative ordered monoid (Nelsen, Section 4.1, the discussion
before Theorem 4.1.6).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- The Archimedean formula is bounded by its second argument. -/
theorem cdf_le_right (g : BivariateGenerator) (u v : I) : g.cdf u v ≤ v := by
  have h : g.cdf u v ≤ g.cdf 1 v := g.cdf_mono_left v (show u ≤ 1 from u.property.2)
  rwa [g.cdf_one_left] at h

/-- The Archimedean formula is bounded by its first argument. -/
theorem cdf_le_left (g : BivariateGenerator) (u v : I) : g.cdf u v ≤ u := by
  rw [g.cdf_comm]
  exact g.cdf_le_right v u

/-- The bivariate Archimedean copula as a binary operation on the unit interval. -/
noncomputable def op (g : BivariateGenerator) (u v : I) : I :=
  ⟨g.cdf u v, g.cdf_nonneg u v, (g.cdf_le_right u v).trans v.property.2⟩

@[simp] theorem coe_op (g : BivariateGenerator) (u v : I) : (g.op u v : ℝ) = g.cdf u v := rfl

/-- The operation is the copula CDF at the pair `(u, v)`. -/
theorem coe_op_eq_cdf_copula (g : BivariateGenerator) (u v : I) :
    (g.op u v : ℝ) = g.copula.cdf ![u, v] := by
  rw [coe_op, cdf_copula]
  rfl

/-- Nelsen, Theorem 4.1.5 (1): Archimedean copulas are symmetric. -/
theorem op_comm (g : BivariateGenerator) (u v : I) : g.op u v = g.op v u :=
  Subtype.ext (g.cdf_comm u v)

@[simp] theorem op_one_left (g : BivariateGenerator) (v : I) : g.op 1 v = v :=
  Subtype.ext (g.cdf_one_left v)

@[simp] theorem op_one_right (g : BivariateGenerator) (u : I) : g.op u 1 = u :=
  Subtype.ext (g.cdf_one_right u)

@[simp] theorem op_zero_left (g : BivariateGenerator) (v : I) : g.op 0 v = 0 :=
  Subtype.ext (g.cdf_zero_left v)

@[simp] theorem op_zero_right (g : BivariateGenerator) (u : I) : g.op u 0 = 0 :=
  Subtype.ext (g.cdf_zero_right u)

/-- The operation is monotone in each argument. -/
theorem op_mono_left (g : BivariateGenerator) (v : I) : Monotone (fun u => g.op u v) :=
  fun _ _ h => g.cdf_mono_left v h

theorem op_mono_right (g : BivariateGenerator) (u : I) : Monotone (fun v => g.op u v) := by
  intro a b h
  change g.cdf u a ≤ g.cdf u b
  rw [g.cdf_comm u a, g.cdf_comm u b]
  exact g.cdf_mono_left u h

/-- The key identity `C(u, ψ(s)) = ψ(φ(u) + s)` for `u > 0` and `s ≥ 0`, including the case
`ψ(s) = 0` of a non-strict generator. -/
theorem cdf_toI (g : BivariateGenerator) {u : I} (hu : u ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    g.cdf u (g.toI hs) = g.toFun (g.invFun u + s) := by
  rcases (g.nonneg s hs).lt_or_eq with hpos | hzero
  · rw [cdf, ite_or_of_not hu (g.toI_ne_zero hs hpos), g.invFun_toI hs hpos]
  · have h0 : g.toI hs = 0 := Subtype.ext hzero.symm
    rw [h0, cdf_zero_right]
    have hle := g.antitone_nonneg hs (add_nonneg (g.inv_nonneg u hu) hs)
      (le_add_of_nonneg_left (g.inv_nonneg u hu))
    exact le_antisymm (g.nonneg _ (add_nonneg (g.inv_nonneg u hu) hs)) (hle.trans hzero.symm.le)

/-- For positive arguments the operation is `ψ(φ(u) + φ(v))`, as a point of `I`. -/
theorem op_eq_toI (g : BivariateGenerator) {u v : I} (hu : u ≠ 0) (hv : v ≠ 0) :
    g.op u v = g.toI (add_nonneg (g.inv_nonneg u hu) (g.inv_nonneg v hv)) :=
  Subtype.ext (by rw [coe_op, coe_toI, cdf, ite_or_of_not hu hv])

/-- Nelsen, Theorem 4.1.5 (2), at the level of the CDF formula:
`C(C(u, v), w) = ψ(φ(u) + φ(v) + φ(w))` for positive arguments. -/
theorem cdf_op_left (g : BivariateGenerator) {u v w : I} (hu : u ≠ 0) (hv : v ≠ 0)
    (hw : w ≠ 0) :
    g.cdf (g.op u v) w = g.toFun (g.invFun u + g.invFun v + g.invFun w) := by
  rw [g.op_eq_toI hu hv, g.cdf_comm, g.cdf_toI hw, add_comm]

/-- Nelsen, Theorem 4.1.5 (2): Archimedean copulas are associative. -/
theorem op_assoc (g : BivariateGenerator) (u v w : I) :
    g.op (g.op u v) w = g.op u (g.op v w) := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  by_cases hw : w = 0
  · simp [hw]
  apply Subtype.ext
  rw [coe_op, coe_op, g.cdf_op_left hu hv hw, g.op_eq_toI hv hw, g.cdf_toI hu, add_assoc]

/-- Scaling Nelsen's generator: the generator `c φ` with inverse generator `t ↦ ψ(t / c)`. -/
noncomputable def scale (g : BivariateGenerator) (c : ℝ) (hc : 0 < c) : BivariateGenerator where
  toFun t := g.toFun (t / c)
  invFun u := c * g.invFun u
  nonneg t ht := g.nonneg _ (div_nonneg ht hc.le)
  antitone x hx y hy hxy := g.antitone (mem_Ici.mpr (div_nonneg hx hc.le))
    (mem_Ici.mpr (div_nonneg hy hc.le)) (div_le_div_of_nonneg_right hxy hc.le)
  convex := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := g.convex.2 (mem_Ici.mpr (div_nonneg (mem_Ici.mp hx) hc.le))
      (mem_Ici.mpr (div_nonneg (mem_Ici.mp hy) hc.le)) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have he : (a * x + b * y) / c = a * (x / c) + b * (y / c) := by ring
    rw [he]
    exact h
  inv_nonneg u hu := mul_nonneg hc.le (g.inv_nonneg u hu)
  inv_antitone u v hu huv := mul_le_mul_of_nonneg_left (g.inv_antitone u v hu huv) hc.le
  inv_one := by simp [g.inv_one]
  right_inv u hu := by
    rw [mul_div_cancel_left₀ _ hc.ne', g.right_inv u hu]

@[simp] theorem scale_toFun (g : BivariateGenerator) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (g.scale c hc).toFun t = g.toFun (t / c) := rfl

@[simp] theorem scale_invFun (g : BivariateGenerator) (c : ℝ) (hc : 0 < c) (u : I) :
    (g.scale c hc).invFun u = c * g.invFun u := rfl

theorem scale_cdf (g : BivariateGenerator) (c : ℝ) (hc : 0 < c) (u v : I) :
    (g.scale c hc).cdf u v = g.cdf u v := by
  unfold cdf
  split_ifs
  · rfl
  · simp only [scale_toFun, scale_invFun]
    rw [← mul_add, mul_div_cancel_left₀ _ hc.ne']

/-- Nelsen, Theorem 4.1.5 (3): for `c > 0`, the generator `c φ` generates the same copula. -/
@[simp] theorem scale_copula (g : BivariateGenerator) (c : ℝ) (hc : 0 < c) :
    (g.scale c hc).copula = g.copula := by
  apply ext_cdf
  intro u
  rw [cdf_copula, cdf_copula, scale_cdf]

end BivariateGenerator

/-- Nelsen, Theorem 4.1.5 (2) for a bivariate copula with an identified generator:
`C(C(u, v), w) = C(u, C(v, w))`, written with CDF values. -/
theorem IsArchimedean.cdf_assoc {C : Copula 2} (hC : IsArchimedean C) (u v w : I) :
    ∃ (x y : I), (x : ℝ) = C.cdf ![u, v] ∧ (y : ℝ) = C.cdf ![v, w] ∧
      C.cdf ![x, w] = C.cdf ![u, y] := by
  obtain ⟨g, rfl⟩ := hC.exists_generator_copula
  refine ⟨g.op u v, g.op v w, g.coe_op_eq_cdf_copula u v, g.coe_op_eq_cdf_copula v w, ?_⟩
  rw [← g.coe_op_eq_cdf_copula, ← g.coe_op_eq_cdf_copula, g.op_assoc]

end ProbabilityTheory.Copula
