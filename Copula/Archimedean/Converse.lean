/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Theory
import Copula.Rectangle

/-! # Nelsen's Theorem 4.1.4: an Archimedean formula is a copula iff the generator is convex

Nelsen, *An Introduction to Copulas*, second edition, Theorem 4.1.4: for a continuous strictly
decreasing generator `φ : [0, 1] → [0, ∞]` with `φ(1) = 0` and pseudo-inverse `ψ = φ^[-1]`,
the function `C(u, v) = ψ(φ(u) + φ(v))` is a copula **if and only if** `φ` is convex.
The library's `BivariateGenerator` builds convexity (of `ψ` on `[0, ∞)`) into the structure
and proves the "if" direction (`BivariateGenerator.copula`). This file proves the converse.

* `ArchimedeanPregenerator`: the data of Theorem 4.1.4 *without* convexity, in the library's
  inverse-generator convention: `ψ ≥ 0` antitone on `[0, ∞)` and strictly decreasing where it is
  positive (Nelsen's strictly decreasing `φ` with pseudo-inverse `ψ`), and `φ` a right inverse of
  `ψ` on `(0, 1]` with `φ(1) = 0`.
* `ArchimedeanPregenerator.convexOn_of_copula`: if some copula has CDF `ψ(φ(u) + φ(v))`, then `ψ`
  is convex on `[0, ∞)` (the "only if" of Theorem 4.1.4).
* `ArchimedeanPregenerator.exists_copula_iff`: Theorem 4.1.4 as an equivalence.
* `ArchimedeanPregenerator.toGenerator`: the `BivariateGenerator` of a convex pregenerator.

The proof follows Nelsen: the rectangle inequality on `[u₂, u₁] × [v, 1]` (Lemma 4.1.3) says
`ψ(b) + ψ(a + c) ≤ ψ(a) + ψ(b + c)` for `0 ≤ a ≤ b`, `c ≥ 0` (increments of `ψ` over intervals of a
fixed length are nondecreasing, `ArchimedeanPregenerator.increment_le`). Nelsen then uses
midpoint convexity and continuity; we instead use that an antitone function with nondecreasing
increments is convex (`convexOn_of_antitoneOn_of_increment_le`): equal-step increments give
the convexity inequality at rational weights, and monotonicity extends it to all weights, so no
continuity argument is needed.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

section IncrementConvexity

variable {f : ℝ → ℝ}

/-- Equal-step increments: if increments of `f` over intervals of a fixed length are
nondecreasing, then `n (f(x + m d) - f(x)) ≤ m (f(x + n d) - f(x))` for `m ≤ n`. -/
theorem increment_average_le
    (hw : ∀ a b c, 0 ≤ a → a ≤ b → 0 ≤ c → f b + f (a + c) ≤ f a + f (b + c))
    {x d : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) {m n : ℕ} (hmn : m ≤ n) :
    (n : ℝ) * (f (x + m * d) - f x) ≤ m * (f (x + n * d) - f x) := by
  set g : ℕ → ℝ := fun k => f (x + k * d) with hg
  set D : ℕ → ℝ := fun k => g (k + 1) - g k with hD
  have hsucc : ∀ k : ℕ, x + ((k + 1 : ℕ) : ℝ) * d = x + k * d + d := by
    intro k; push_cast; ring
  have hDmono : ∀ j k : ℕ, j ≤ k → D j ≤ D k := by
    intro j k hjk
    have hj : 0 ≤ x + j * d := by positivity
    have hjk' : x + j * d ≤ x + k * d := by
      have : (j : ℝ) ≤ k := Nat.cast_le.mpr hjk
      nlinarith
    have h := hw _ _ d hj hjk' hd
    simp only [hD, hg, hsucc]
    linarith
  have hg0 : g 0 = f x := by simp [hg]
  have L1 : ∀ p : ℕ, g (p + 1) - g 0 ≤ (p + 1) * D p := by
    intro p
    induction p with
    | zero => simp [hD]
    | succ p ih =>
      have := hDmono p (p + 1) (Nat.le_succ p)
      have he : g (p + 1 + 1) - g 0 = (g (p + 1) - g 0) + D (p + 1) := by simp only [hD]; ring
      rw [he]
      push_cast
      nlinarith
  have L2 : ∀ p k : ℕ, k * D p ≤ g (p + 1 + k) - g (p + 1) := by
    intro p k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hDmono p (p + 1 + k) (by omega)
      have he : g (p + 1 + (k + 1)) - g (p + 1) = (g (p + 1 + k) - g (p + 1)) + D (p + 1 + k) := by
        simp only [hD]
        rw [show p + 1 + (k + 1) = p + 1 + k + 1 by omega]
        ring
      rw [he]
      push_cast
      nlinarith
  change (n : ℝ) * (g m - f x) ≤ m * (g n - f x)
  rw [← hg0]
  rcases Nat.eq_zero_or_eq_succ_pred m with hm | hm
  · simp [hm]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    set p := m.pred
    rw [hm]
    have h1 := L1 p
    have h2 := L2 p k
    push_cast
    nlinarith

/-- The convexity inequality along a segment `x ≤ y`, from nondecreasing increments and
antitonicity. -/
theorem le_of_antitoneOn_of_increment_le (hanti : AntitoneOn f (Ici 0))
    (hw : ∀ a b c, 0 ≤ a → a ≤ b → 0 ≤ c → f b + f (a + c) ≤ f a + f (b + c))
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    f (x + b * (y - x)) ≤ f x + b * (f y - f x) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hΔ : 0 ≤ f x - f y := sub_nonneg.mpr (hanti hx hy hxy)
  by_contra hlt
  push Not at hlt
  set ε := f (x + b * (y - x)) - f x - b * (f y - f x) with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((f x - f y) / ε)
  have hnpos : (0 : ℝ) < n := (div_nonneg hΔ hεpos.le).trans_lt hn
  set m := ⌊b * n⌋₊ with hm
  have hbn : 0 ≤ b * n := by positivity
  have hm1 : (m : ℝ) ≤ b * n := Nat.floor_le hbn
  have hm2 : b * n < m + 1 := Nat.lt_floor_add_one _
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := hm1.trans (by nlinarith)
    exact_mod_cast this
  set d := (y - x) / n with hd
  have hd0 : 0 ≤ d := div_nonneg (sub_nonneg.mpr hxy) hnpos.le
  have hnd : (n : ℝ) * d = y - x := by rw [hd]; field_simp
  have hmd : (m : ℝ) * d ≤ b * (y - x) := by
    rw [← hnd]
    nlinarith
  have hmd0 : 0 ≤ (m : ℝ) * d := by positivity
  have hz : f (x + b * (y - x)) ≤ f (x + m * d) :=
    hanti (show x + m * d ∈ Ici 0 from mem_Ici.mpr (by positivity))
      (show x + b * (y - x) ∈ Ici 0 from mem_Ici.mpr (by nlinarith)) (by linarith)
  have hA := increment_average_le hw hx hd0 hmn
  rw [hnd, show x + (y - x) = y by ring] at hA
  -- n (f z - f x) ≤ m (f y - f x) ≤ (b n - 1)(f y - f x)
  have hB : (m : ℝ) * (f y - f x) ≤ (b * n - 1) * (f y - f x) := by nlinarith
  have hC : (n : ℝ) * ε ≤ f x - f y := by
    have : (n : ℝ) * (f (x + b * (y - x)) - f x) ≤ (b * n - 1) * (f y - f x) := by
      nlinarith
    rw [hε]
    nlinarith
  have := (div_lt_iff₀ hεpos).mp hn
  linarith

/-- An antitone function on `[0, ∞)` whose increments over intervals of a fixed length are
nondecreasing (`f(b) + f(a + c) ≤ f(a) + f(b + c)` for `0 ≤ a ≤ b`, `0 ≤ c`) is convex. -/
theorem convexOn_of_antitoneOn_of_increment_le (hanti : AntitoneOn f (Ici 0))
    (hw : ∀ a b c, 0 ≤ a → a ≤ b → 0 ≤ c → f b + f (a + c) ≤ f a + f (b + c)) :
    ConvexOn ℝ (Ici 0) f := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  rcases le_total x y with hxy | hyx
  · have h := le_of_antitoneOn_of_increment_le hanti hw hx0 hxy hb (by linarith)
    have e1 : a * x + b * y = x + b * (y - x) := by rw [show a = 1 - b by linarith]; ring
    have e2 : a * f x + b * f y = f x + b * (f y - f x) := by rw [show a = 1 - b by linarith]; ring
    rw [e1, e2]
    exact h
  · have h := le_of_antitoneOn_of_increment_le hanti hw hy0 hyx ha (by linarith)
    have e1 : a * x + b * y = y + a * (x - y) := by rw [show b = 1 - a by linarith]; ring
    have e2 : a * f x + b * f y = f y + a * (f x - f y) := by rw [show b = 1 - a by linarith]; ring
    rw [e1, e2]
    exact h

end IncrementConvexity

/-- The data of Nelsen's Theorem 4.1.4 without convexity, in the inverse-generator convention:
`ψ = toFun` is nonnegative and antitone on `[0, ∞)` and strictly decreasing where positive, and
`φ = invFun` is a right inverse of `ψ` on `(0, 1]` with `φ(1) = 0`. -/
structure ArchimedeanPregenerator where
  /-- Decreasing inverse generator (Nelsen's pseudo-inverse `φ^[-1]`). -/
  toFun : ℝ → ℝ
  /-- Generator on positive unit-interval arguments; its value at zero is unused. -/
  invFun : I → ℝ
  nonneg : ∀ t, 0 ≤ t → 0 ≤ toFun t
  antitone : AntitoneOn toFun (Ici 0)
  strictAnti : ∀ a b, 0 ≤ a → a < b → 0 < toFun b → toFun b < toFun a
  inv_nonneg : ∀ u, u ≠ 0 → 0 ≤ invFun u
  inv_one : invFun 1 = 0
  right_inv : ∀ u, u ≠ 0 → toFun (invFun u) = (u : ℝ)

namespace ArchimedeanPregenerator

variable (p : ArchimedeanPregenerator)

/-- The Archimedean formula of a pregenerator, with grounded boundary values. -/
noncomputable def cdf (u v : I) : ℝ :=
  if u = 0 ∨ v = 0 then 0 else p.toFun (p.invFun u + p.invFun v)

theorem toFun_zero : p.toFun 0 = 1 := by
  have h1 : (1 : I) ≠ 0 := one_ne_zero
  have h := p.right_inv 1 h1
  rwa [p.inv_one, Set.Icc.coe_one] at h

theorem toFun_le_one {s : ℝ} (hs : 0 ≤ s) : p.toFun s ≤ 1 :=
  (p.antitone (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs).trans p.toFun_zero.le

/-- The value `ψ(s)` as a point of `I`. -/
noncomputable def toI {s : ℝ} (hs : 0 ≤ s) : I := ⟨p.toFun s, p.nonneg s hs, p.toFun_le_one hs⟩

theorem toI_ne_zero {s : ℝ} (hs : 0 ≤ s) (hpos : 0 < p.toFun s) : p.toI hs ≠ 0 := by
  intro h
  have h' : p.toFun s = 0 := congrArg (fun v : I => (v : ℝ)) h
  exact hpos.ne' h'

/-- `φ(ψ(s)) = s` where `ψ(s) > 0`. -/
theorem invFun_toI {s : ℝ} (hs : 0 ≤ s) (hpos : 0 < p.toFun s) : p.invFun (p.toI hs) = s := by
  have hne := p.toI_ne_zero hs hpos
  have hr : p.toFun (p.invFun (p.toI hs)) = p.toFun s := p.right_inv _ hne
  have hnn := p.inv_nonneg _ hne
  rcases lt_trichotomy (p.invFun (p.toI hs)) s with hlt | heq | hgt
  · have := p.strictAnti _ _ hnn hlt hpos
    rw [hr] at this
    exact absurd this (lt_irrefl _)
  · exact heq
  · have := p.strictAnti _ _ hs hgt (by rw [hr]; exact hpos)
    rw [hr] at this
    exact absurd this (lt_irrefl _)

/-- The generator is antitone on `(0, 1]` (a consequence of the axioms). -/
theorem inv_antitone (u v : I) (hu : u ≠ 0) (huv : u ≤ v) : p.invFun v ≤ p.invFun u := by
  have hv : v ≠ 0 := fun h => hu (le_antisymm (h ▸ huv) unitInterval.nonneg')
  by_contra hlt
  push Not at hlt
  rcases huv.lt_or_eq with h | h
  · have h1 := p.antitone (mem_Ici.mpr (p.inv_nonneg u hu)) (mem_Ici.mpr (p.inv_nonneg v hv))
      hlt.le
    rw [p.right_inv u hu, p.right_inv v hv] at h1
    exact absurd h (not_lt.mpr h1)
  · rw [h] at hlt
    exact lt_irrefl _ hlt

/-- The Wright-convexity inequality `ψ(b) + ψ(a + c) ≤ ψ(a) + ψ(b + c)` (`0 ≤ a ≤ b`, `c ≥ 0`)
follows from the rectangle inequality on the rectangles `[ψ(b), ψ(a)] × [ψ(c), 1]`. -/
theorem increment_le
    (hinc : ∀ u₁ u₂ v : I, u₂ ≤ u₁ → 0 ≤ u₁ - u₂ - p.cdf u₁ v + p.cdf u₂ v)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) :
    p.toFun b + p.toFun (a + c) ≤ p.toFun a + p.toFun (b + c) := by
  have hb : 0 ≤ b := ha.trans hab
  have hanti : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → p.toFun t ≤ p.toFun s :=
    fun hs hst => p.antitone (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hst)) hst
  rcases (p.nonneg b hb).lt_or_eq with hbpos | hbzero
  · rcases (p.nonneg c hc).lt_or_eq with hcpos | hczero
    · have hapos : 0 < p.toFun a := hbpos.trans_le (hanti ha hab)
      have h := hinc (p.toI ha) (p.toI hb) (p.toI hc) (show p.toFun b ≤ p.toFun a from hanti ha hab)
      have hA := p.toI_ne_zero ha hapos
      have hB := p.toI_ne_zero hb hbpos
      have hC := p.toI_ne_zero hc hcpos
      simp only [cdf, hA, hB, hC, or_self, ite_false, p.invFun_toI ha hapos,
        p.invFun_toI hb hbpos, p.invFun_toI hc hcpos] at h
      change 0 ≤ p.toFun a - p.toFun b - _ + _ at h
      linarith
    · have h1 : p.toFun (a + c) ≤ 0 := (hanti hc (le_add_of_nonneg_left ha)).trans hczero.symm.le
      have h2 := p.nonneg (b + c) (add_nonneg hb hc)
      have h3 := hanti ha hab
      linarith
  · have h1 : p.toFun (b + c) = 0 :=
      le_antisymm ((hanti hb (le_add_of_nonneg_right hc)).trans hbzero.symm.le)
        (p.nonneg _ (add_nonneg hb hc))
    have h2 := hanti ha (le_add_of_nonneg_right hc : a ≤ a + c)
    rw [h1, ← hbzero]
    linarith

/-- The "only if" of Nelsen's Theorem 4.1.4, from the rectangle inequality on the rectangles
`[u₂, u₁] × [v, 1]` (Nelsen's Lemma 4.1.3 condition): the inverse generator is convex. -/
theorem convexOn_of_rectangle
    (hinc : ∀ u₁ u₂ v : I, u₂ ≤ u₁ → 0 ≤ u₁ - u₂ - p.cdf u₁ v + p.cdf u₂ v) :
    ConvexOn ℝ (Ici 0) p.toFun :=
  convexOn_of_antitoneOn_of_increment_le p.antitone
    (fun _ _ _ ha hab hc => p.increment_le hinc ha hab hc)

/-- Nelsen, Theorem 4.1.4 ("only if"): if some bivariate copula has the CDF `ψ(φ(u) + φ(v))`,
then the inverse generator `ψ` is convex on `[0, ∞)`. -/
theorem convexOn_of_copula {C : Copula 2} (hC : ∀ u v : I, C.cdf ![u, v] = p.cdf u v) :
    ConvexOn ℝ (Ici 0) p.toFun := by
  apply p.convexOn_of_rectangle
  intro u₁ u₂ v h
  have hab : (![u₂, v] : Fin 2 → I) ≤ ![u₁, 1] := by
    intro i
    fin_cases i
    · exact h
    · exact v.property.2
  have hr := C.rectangleIncrement_cdf_nonneg _ _ hab
  rw [rectangleIncrement_two] at hr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hr
  rw [hC, hC, hC, hC] at hr
  have e1 : ∀ u : I, p.cdf u 1 = u := by
    intro u
    by_cases hu : u = 0
    · simp [cdf, hu]
    · simp [cdf, hu, p.inv_one, p.right_inv u hu]
  rw [e1, e1] at hr
  linarith

/-- The `BivariateGenerator` of a pregenerator with convex inverse generator. -/
noncomputable def toGenerator (hconv : ConvexOn ℝ (Ici 0) p.toFun) : BivariateGenerator where
  toFun := p.toFun
  invFun := p.invFun
  nonneg := p.nonneg
  antitone := p.antitone
  convex := hconv
  inv_nonneg := p.inv_nonneg
  inv_antitone := p.inv_antitone
  inv_one := p.inv_one
  right_inv := p.right_inv

@[simp] theorem toGenerator_cdf (hconv : ConvexOn ℝ (Ici 0) p.toFun) (u v : I) :
    (p.toGenerator hconv).cdf u v = p.cdf u v := rfl

/-- Nelsen, Theorem 4.1.4: `ψ(φ(u) + φ(v))` is the CDF of a bivariate copula iff the inverse
generator `ψ` is convex on `[0, ∞)`. -/
theorem exists_copula_iff :
    (∃ C : Copula 2, ∀ u v : I, C.cdf ![u, v] = p.cdf u v) ↔ ConvexOn ℝ (Ici 0) p.toFun := by
  refine ⟨fun ⟨_, hC⟩ => p.convexOn_of_copula hC, fun hconv => ?_⟩
  refine ⟨(p.toGenerator hconv).copula, fun u v => ?_⟩
  rw [BivariateGenerator.cdf_copula]
  rfl

end ArchimedeanPregenerator

/-- Every bivariate generator is a pregenerator (forgetting convexity). -/
noncomputable def BivariateGenerator.toPregenerator (g : BivariateGenerator) :
    ArchimedeanPregenerator where
  toFun := g.toFun
  invFun := g.invFun
  nonneg := g.nonneg
  antitone := g.antitone
  strictAnti _ _ ha hab hb := g.toFun_lt_of_lt ha hab hb
  inv_nonneg := g.inv_nonneg
  inv_one := g.inv_one
  right_inv := g.right_inv

end ProbabilityTheory.Copula
