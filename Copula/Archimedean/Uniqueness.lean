/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Associativity

/-! # Uniqueness of Archimedean generators up to a positive factor

Nelsen, *An Introduction to Copulas*, second edition, Theorem 4.1.5 (3) shows that the
generators `φ` and `c φ` (`c > 0`) produce the same Archimedean copula. Conversely, the
generator of a bivariate Archimedean copula is unique up to such a factor (Genest and
MacKay, 1986; Nelsen, Section 4.1, the remark after Theorem 4.1.5):

* `BivariateGenerator.copula_eq_iff`: `C_{φ₁} = C_{φ₂}` iff `φ₂ = c φ₁` on `(0, 1]` for some
  `c > 0`;
* `BivariateGenerator.toFun_mul_eq_of_invFun_eq_mul`: in that case the inverse generators
  satisfy `ψ₂(c s) = ψ₁(s)` for all `s ≥ 0`, including the zero set of a non-strict generator;
* `HasArchimedeanGenerator.invFun_eq_mul`: two generators identified for the same bivariate
  copula differ by a positive factor.

The proof of the converse follows Genest–MacKay: `h = φ₂ ∘ ψ₁` satisfies Cauchy's equation
`h(x + y) = h(x) + h(y)` wherever `ψ₁(x + y) > 0` (because `φ₂(C(u, v)) = φ₂(u) + φ₂(v)` when
`C(u, v) > 0`), and it is monotone, so it is linear (`additive_monotone_ratio_le`, a
self-contained version of the monotone Cauchy equation on a down-closed subset of `[0, ∞)`).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- Monotone solutions of Cauchy's equation on a down-closed subset `P` of `[0, ∞)` are linear:
for `s, t ∈ P` with `s, t > 0` one has `h(t) s ≤ h(s) t` (hence `h(s)/s = h(t)/t` by symmetry). -/
theorem additive_monotone_ratio_le {P : ℝ → Prop} {h : ℝ → ℝ}
    (hdown : ∀ s t, P t → 0 ≤ s → s ≤ t → P s)
    (hadd : ∀ x y, 0 ≤ x → 0 ≤ y → P (x + y) → h (x + y) = h x + h y)
    (hmono : ∀ s t, P t → 0 ≤ s → s ≤ t → h s ≤ h t)
    {s t : ℝ} (hs : P s) (ht : P t) (hs0 : 0 < s) (ht0 : 0 < t) :
    h t * s ≤ h s * t := by
  have hP0 : P 0 := hdown 0 t ht le_rfl ht0.le
  have hh0 : h 0 = 0 := by
    have h00 := hadd 0 0 le_rfl le_rfl (by simpa using hP0)
    simp only [add_zero] at h00
    linarith
  have hht : 0 ≤ h t := hh0 ▸ hmono 0 t ht le_rfl ht0.le
  -- multiples
  have hmul : ∀ (k : ℕ) (x : ℝ), 0 ≤ x → P (k * x) → h (k * x) = k * h x := by
    intro k
    induction k with
    | zero => intro x _ _; simp [hh0]
    | succ k ih =>
      intro x hx hP
      have he : ((k + 1 : ℕ) : ℝ) * x = k * x + x := by push_cast; ring
      have hkx : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg k) hx
      rw [he] at hP ⊢
      rw [hadd _ _ hkx hx hP, ih x hx (hdown _ _ hP hkx (le_add_of_nonneg_right hx))]
      push_cast
      ring
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (h t * t / (h t * s - h s * t))
  have hd : 0 < h t * s - h s * t := by linarith
  have hn0 : (0 : ℝ) ≤ n := (div_nonneg (mul_nonneg hht ht0.le) hd.le).trans hn.le
  have hnpos : (0 : ℝ) < n := by
    rcases hn0.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      rw [← h'] at hn
      exact absurd hn (not_lt.mpr (div_nonneg (mul_nonneg hht ht0.le) hd.le))
  set x := t / n with hx
  have hx0 : 0 ≤ x := div_nonneg ht0.le hnpos.le
  have hnx : (n : ℝ) * x = t := by rw [hx]; field_simp
  have hhx : h t = n * h x := by
    have := hmul n x hx0 (by rw [hnx]; exact ht)
    rwa [hnx] at this
  set m := ⌊(n : ℝ) * s / t⌋₊ with hm
  have hm1 : (m : ℝ) ≤ n * s / t := Nat.floor_le (by positivity)
  have hm2 : (n : ℝ) * s / t < m + 1 := Nat.lt_floor_add_one _
  have hmx : (m : ℝ) * x ≤ s := by
    rw [hx]
    rw [le_div_iff₀ ht0] at hm1
    rw [mul_div_assoc', div_le_iff₀ hnpos]
    linarith
  have hmx0 : 0 ≤ (m : ℝ) * x := mul_nonneg (Nat.cast_nonneg m) hx0
  have hPm : P (m * x) := hdown _ _ hs hmx0 hmx
  have hle : (m : ℝ) * h x ≤ h s := by
    rw [← hmul m x hx0 hPm]
    exact hmono _ _ hs hmx0 hmx
  have hm2' : (n : ℝ) * s < (m + 1) * t := by rwa [div_lt_iff₀ ht0] at hm2
  -- n (h t s) ≤ h t (m + 1) t = n (m h x) t + h t t ≤ n h s t + h t t
  have key : (n : ℝ) * (h t * s) ≤ n * (h s * t) + h t * t := by
    calc (n : ℝ) * (h t * s) = h t * (n * s) := by ring
      _ ≤ h t * ((m + 1) * t) := mul_le_mul_of_nonneg_left hm2'.le hht
      _ = n * ((m * h x) * t) + h t * t := by rw [hhx]; ring
      _ ≤ n * (h s * t) + h t * t := by
        gcongr
  have : h t * t / (h t * s - h s * t) * (h t * s - h s * t) < n * (h t * s - h s * t) :=
    mul_lt_mul_of_pos_right hn hd
  rw [div_mul_cancel₀ _ hd.ne'] at this
  nlinarith

/-- If `φ₂ = c φ₁` on `(0, 1]`, then `ψ₂(c s) = ψ₁(s)` for every `s ≥ 0`. -/
theorem toFun_mul_eq_of_invFun_eq_mul (g₁ g₂ : BivariateGenerator) {c : ℝ} (hc : 0 < c)
    (h : ∀ u : I, u ≠ 0 → g₂.invFun u = c * g₁.invFun u) {s : ℝ} (hs : 0 ≤ s) :
    g₂.toFun (c * s) = g₁.toFun s := by
  have hcs : 0 ≤ c * s := mul_nonneg hc.le hs
  rcases (g₁.nonneg s hs).lt_or_eq with h1 | h1
  · -- `ψ₁(s) = w > 0`, so `φ₁(w) = s` and `φ₂(w) = c s`
    have hw := g₁.invFun_toI hs h1
    have h2 := g₂.right_inv (g₁.toI hs) (g₁.toI_ne_zero hs h1)
    rw [h _ (g₁.toI_ne_zero hs h1), hw, coe_toI] at h2
    exact h2
  · rcases (g₂.nonneg (c * s) hcs).lt_or_eq with h2 | h2
    · exfalso
      have hw := g₂.invFun_toI hcs h2
      have hne := g₂.toI_ne_zero hcs h2
      rw [h _ hne] at hw
      have hw' : g₁.invFun (g₂.toI hcs) = s := by
        have := congrArg (· / c) hw
        simpa [mul_div_cancel_left₀ _ hc.ne'] using this
      have hr := g₁.right_inv _ hne
      rw [hw', coe_toI] at hr
      rw [hr] at h1
      exact h2.ne' h1.symm
    · rw [← h1, ← h2]

/-- Nelsen, Theorem 4.1.5 (3) in pointwise form: generators proportional on `(0, 1]` give the
same Archimedean copula. -/
theorem copula_eq_of_invFun_eq_mul (g₁ g₂ : BivariateGenerator) {c : ℝ} (hc : 0 < c)
    (h : ∀ u : I, u ≠ 0 → g₂.invFun u = c * g₁.invFun u) : g₁.copula = g₂.copula := by
  apply ext_cdf
  intro x
  rw [cdf_copula, cdf_copula]
  unfold cdf
  split_ifs with hx
  · rfl
  · push Not at hx
    rw [h _ hx.1, h _ hx.2, ← mul_add, toFun_mul_eq_of_invFun_eq_mul g₁ g₂ hc h
      (add_nonneg (g₁.inv_nonneg _ hx.1) (g₁.inv_nonneg _ hx.2))]

private theorem coe_pos' {u : I} (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

/-- The point `ψ(s)` of `I`, written through the projection onto `[0, 1]`. -/
private theorem projIcc_toFun (g : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) :
    projIcc 0 1 zero_le_one (g.toFun s) = g.toI hs :=
  projIcc_of_mem _ ⟨g.nonneg s hs, g.toFun_le_one hs⟩

/-- Genest–MacKay: the generator of a bivariate Archimedean copula is unique up to a positive
factor. If `C_{φ₁} = C_{φ₂}` then `φ₂ = c φ₁` on `(0, 1]` for some `c > 0`. -/
theorem exists_invFun_eq_mul_of_copula_eq (g₁ g₂ : BivariateGenerator)
    (hC : g₁.copula = g₂.copula) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : I, u ≠ 0 → g₂.invFun u = c * g₁.invFun u := by
  have hcdf : ∀ u v : I, g₁.cdf u v = g₂.cdf u v := by
    intro u v
    have := congrArg (fun C : Copula 2 => C.cdf ![u, v]) hC
    simpa using this
  -- `h = φ₂ ∘ ψ₁` on the positivity region `P` of `ψ₁`
  let P : ℝ → Prop := fun s => 0 ≤ s ∧ 0 < g₁.toFun s
  let hfun : ℝ → ℝ := fun s => g₂.invFun (projIcc 0 1 zero_le_one (g₁.toFun s))
  have hdown : ∀ s t, P t → 0 ≤ s → s ≤ t → P s := fun s t ht hs hst =>
    ⟨hs, ht.2.trans_le (g₁.antitone_nonneg hs ht.1 hst)⟩
  have hmono : ∀ s t, P t → 0 ≤ s → s ≤ t → hfun s ≤ hfun t := by
    intro s t ht hs hst
    simp only [hfun, projIcc_toFun g₁ hs, projIcc_toFun g₁ ht.1]
    exact g₂.inv_antitone _ _ (g₁.toI_ne_zero ht.1 ht.2)
      (show (g₁.toI ht.1 : ℝ) ≤ g₁.toI hs from g₁.antitone_nonneg hs ht.1 hst)
  have hadd : ∀ x y, 0 ≤ x → 0 ≤ y → P (x + y) → hfun (x + y) = hfun x + hfun y := by
    intro x y hx hy hxy
    have hxp : 0 < g₁.toFun x :=
      hxy.2.trans_le (g₁.antitone_nonneg hx hxy.1 (le_add_of_nonneg_right hy))
    have hyp : 0 < g₁.toFun y :=
      hxy.2.trans_le (g₁.antitone_nonneg hy hxy.1 (le_add_of_nonneg_left hx))
    have ha := g₁.toI_ne_zero hx hxp
    have hb := g₁.toI_ne_zero hy hyp
    have hval : g₁.cdf (g₁.toI hx) (g₁.toI hy) = g₁.toFun (x + y) := by
      rw [cdf, ite_or_of_not ha hb, g₁.invFun_toI hx hxp, g₁.invFun_toI hy hyp]
    have hpos : 0 < g₂.cdf (g₁.toI hx) (g₁.toI hy) := by rw [← hcdf, hval]; exact hxy.2
    obtain ⟨w, hw, hw2⟩ := g₂.invFun_cdf ha hb hpos
    have hw' : w = g₁.toI hxy.1 := Subtype.ext (by rw [hw, ← hcdf, hval, coe_toI])
    simp only [hfun, projIcc_toFun g₁ hx, projIcc_toFun g₁ hy, projIcc_toFun g₁ hxy.1]
    rw [← hw', hw2]
  -- evaluation of `h` along `φ₁`
  have heval : ∀ u : I, u ≠ 0 → hfun (g₁.invFun u) = g₂.invFun u := by
    intro u hu
    simp only [hfun, projIcc_toFun g₁ (g₁.inv_nonneg u hu)]
    congr 1
    exact Subtype.ext (by rw [coe_toI, g₁.right_inv u hu])
  have hPinv : ∀ u : I, u ≠ 0 → P (g₁.invFun u) := fun u hu =>
    ⟨g₁.inv_nonneg u hu, by rw [g₁.right_inv u hu]; exact coe_pos' hu⟩
  let u₀ : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hu₀ : u₀ ≠ 0 := fun h => by
    have := congrArg (fun v : I => (v : ℝ)) h
    norm_num [u₀] at this
  have hu₀1 : u₀ ≠ 1 := fun h => by
    have := congrArg (fun v : I => (v : ℝ)) h
    norm_num [u₀] at this
  have ht₀ := g₁.invFun_pos hu₀ hu₀1
  have ht₀' := g₂.invFun_pos hu₀ hu₀1
  refine ⟨g₂.invFun u₀ / g₁.invFun u₀, div_pos ht₀' ht₀, ?_⟩
  intro u hu
  rcases (g₁.inv_nonneg u hu).lt_or_eq with hs | hs
  · have h1 := additive_monotone_ratio_le hdown hadd hmono (hPinv u hu) (hPinv u₀ hu₀) hs ht₀
    have h2 := additive_monotone_ratio_le hdown hadd hmono (hPinv u₀ hu₀) (hPinv u hu) ht₀ hs
    rw [heval u hu, heval u₀ hu₀] at h1 h2
    rw [div_mul_eq_mul_div, eq_div_iff ht₀.ne']
    linarith
  · have h1 : (u : ℝ) = 1 := by rw [← g₁.right_inv u hu, ← hs, g₁.toFun_zero]
    have hu1 : u = 1 := Subtype.ext h1
    rw [hu1, g₁.inv_one, g₂.inv_one, mul_zero]

/-- Genest–MacKay uniqueness theorem (Nelsen, Section 4.1): two bivariate generators give the
same Archimedean copula iff `φ₂ = c φ₁` on `(0, 1]` for some constant `c > 0`. -/
theorem copula_eq_iff (g₁ g₂ : BivariateGenerator) :
    g₁.copula = g₂.copula ↔ ∃ c : ℝ, 0 < c ∧ ∀ u : I, u ≠ 0 → g₂.invFun u = c * g₁.invFun u :=
  ⟨exists_invFun_eq_mul_of_copula_eq g₁ g₂, fun ⟨_, hc, h⟩ => copula_eq_of_invFun_eq_mul g₁ g₂ hc h⟩

/-- Uniqueness in terms of inverse generators: `C_{ψ₁} = C_{ψ₂}` iff `ψ₂(s) = ψ₁(s / c)` for all
`s ≥ 0` and some `c > 0`. -/
theorem copula_eq_iff_toFun (g₁ g₂ : BivariateGenerator) :
    g₁.copula = g₂.copula ↔ ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → g₂.toFun (c * s) = g₁.toFun s := by
  constructor
  · intro hC
    obtain ⟨c, hc, h⟩ := exists_invFun_eq_mul_of_copula_eq g₁ g₂ hC
    exact ⟨c, hc, fun s hs => toFun_mul_eq_of_invFun_eq_mul g₁ g₂ hc h hs⟩
  · rintro ⟨c, hc, h⟩
    apply copula_eq_of_invFun_eq_mul g₁ g₂ hc
    intro u hu
    have hs := mul_nonneg hc.le (g₁.inv_nonneg u hu)
    have hr : g₂.toFun (c * g₁.invFun u) = u := by rw [h _ (g₁.inv_nonneg u hu), g₁.right_inv u hu]
    have hpos : 0 < g₂.toFun (c * g₁.invFun u) := by
      rw [hr]; exact coe_pos' hu
    have hw := g₂.invFun_toI hs hpos
    have he : g₂.toI hs = u := Subtype.ext (by rw [coe_toI, hr])
    rw [he] at hw
    exact hw

/-- Two generators give the same copula iff one is a positive rescaling of the other
(`BivariateGenerator.scale`) on `(0, 1]`. -/
theorem copula_eq_iff_scale (g₁ g₂ : BivariateGenerator) :
    g₁.copula = g₂.copula ↔
      ∃ (c : ℝ) (hc : 0 < c), ∀ u : I, u ≠ 0 → g₂.invFun u = (g₁.scale c hc).invFun u := by
  rw [copula_eq_iff]
  simp only [scale_invFun]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h⟩⟩

end BivariateGenerator

/-- Two generators identified for the same bivariate copula differ by a positive factor. -/
theorem HasArchimedeanGenerator.invFun_eq_mul {C : Copula 2} {g₁ g₂ : BivariateGenerator}
    (h₁ : HasArchimedeanGenerator C g₁) (h₂ : HasArchimedeanGenerator C g₂) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : I, u ≠ 0 → g₂.invFun u = c * g₁.invFun u :=
  BivariateGenerator.exists_invFun_eq_mul_of_copula_eq g₁ g₂ (h₁.eq_copula.symm.trans h₂.eq_copula)

end ProbabilityTheory.Copula
