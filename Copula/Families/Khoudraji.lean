/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Gumbel
import Copula.Families.MarshallOlkin
import Copula.Dependence.Basic
import Copula.Order.Orthant
import Copula.Symmetry
import Copula.Rank.MarshallOlkinXi

/-! # Khoudraji's asymmetrization

Khoudraji's device (A. Khoudraji, *Contributions à l'étude des copules et à la modélisation
des valeurs extrêmes bivariées*, PhD thesis, Laval 1995; Genest, Ghoudi and Rivest 1998;
E. Liebscher, *Construction of asymmetric multivariate copulas*, J. Multivariate Anal. 99
(2008)) turns a copula `C` and weights `a, b ∈ [0,1]` into

`K_{a,b}(u,v) = u^{1-a} v^{1-b} C(u^a, v^b)`.

It is the special case `D = Π` of Liebscher's product construction
`C(u^a, v^b) D(u^{1-a}, v^{1-b})` (`Copula.Transform.MaxProduct`), which realizes it as the law
of the coordinatewise maximum of a transformed sample of `C` and an independent transformed
sample of `Π`. Results:

* the CDF formula (`cdf_khoudraji`), endpoint weights `K_{1,1} = C`, `K_{0,0} = Π`, and
  `K_{a,b}(Π) = Π`;
* Marshall–Olkin copulas are the Khoudraji asymmetrizations of `M`, and Tawn's asymmetric
  logistic copulas those of Gumbel's (`khoudraji_comonotonic`, `tawn_eq_khoudraji`);
* the construction preserves max-stability, the pointwise order, PQD and NQD, and commutes
  with transposition up to swapping the weights (`transpose_khoudraji`);
* it does break exchangeability: `K_{a,b}(M)` is exchangeable if and only if `a = b` or
  `ab = 0` (`isExchangeable_khoudraji_comonotonic_iff`), detected by the directional
  Chatterjee's xi of the Marshall–Olkin copula.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Khoudraji's asymmetrization `u^{1-a} v^{1-b} C(u^a, v^b)` of a bivariate copula. -/
noncomputable def khoudraji (C : Copula 2) (a b : I) : Copula 2 :=
  maxProduct C (independence 2) ![a, b]

/-- The CDF of Khoudraji's asymmetrization: `K(u,v) = C(u^a, v^b) u^{1-a} v^{1-b}`
(with `0^0 = 1`). -/
theorem cdf_khoudraji (C : Copula 2) (a b u v : I) :
    (khoudraji C a b).cdf ![u, v] =
      C.cdf ![unitPower u a a.2.1, unitPower v b b.2.1] *
        ((u : ℝ) ^ (1 - (a : ℝ)) * (v : ℝ) ^ (1 - (b : ℝ))) := by
  rw [khoudraji, cdf_maxProduct, cdf_independence, Fin.prod_univ_two]
  have hw : (fun i => unitPower (![u, v] i) (![a, b] i) (![a, b] i).property.1) =
      ![unitPower u a a.2.1, unitPower v b b.2.1] := by
    ext i; fin_cases i <;> rfl
  rw [hw]
  simp [unitInterval.coe_symm_eq]

private theorem fin_two_const (a : I) : (![a, a] : Fin 2 → I) = fun _ => a := by
  ext i; fin_cases i <;> rfl

@[simp] theorem khoudraji_one_one (C : Copula 2) : khoudraji C 1 1 = C := by
  rw [khoudraji, fin_two_const, maxProduct_one]

@[simp] theorem khoudraji_zero_zero (C : Copula 2) : khoudraji C 0 0 = independence 2 := by
  rw [khoudraji, fin_two_const, maxProduct_zero]

/-- `x^a x^{1-a} = x` on the unit interval (with `0^0 = 1`). -/
theorem unit_rpow_mul_rpow_one_sub (x a : I) :
    (x : ℝ) ^ (a : ℝ) * (x : ℝ) ^ (1 - (a : ℝ)) = x := by
  rcases eq_or_lt_of_le x.2.1 with h | h
  · rw [← h]
    rcases eq_or_lt_of_le a.2.1 with ha | ha
    · rw [← ha]; simp
    · rw [Real.zero_rpow ha.ne']; simp
  · rw [← Real.rpow_add h]; simp

@[simp] theorem khoudraji_independence (a b : I) :
    khoudraji (independence 2) a b = independence 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_khoudraji, cdf_independence, cdf_independence, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coe_unitPower]
  calc (u : ℝ) ^ (a : ℝ) * (v : ℝ) ^ (b : ℝ) * ((u : ℝ) ^ (1 - (a : ℝ)) * (v : ℝ) ^ (1 - (b : ℝ)))
      = ((u : ℝ) ^ (a : ℝ) * (u : ℝ) ^ (1 - (a : ℝ))) *
          ((v : ℝ) ^ (b : ℝ) * (v : ℝ) ^ (1 - (b : ℝ))) := by ring
    _ = u * v := by rw [unit_rpow_mul_rpow_one_sub, unit_rpow_mul_rpow_one_sub]

/-- A zero first weight gives independence: `K_{0,b}(C) = Π`. -/
@[simp] theorem khoudraji_zero_left (C : Copula 2) (b : I) :
    khoudraji C 0 b = independence 2 := by
  apply ext_cdf_two
  intro u v
  have h0 : ∀ (w : I) (h), unitPower w ((0 : I) : ℝ) h = 1 := fun w h => by ext; simp
  rw [cdf_khoudraji, cdf_independence, Fin.prod_univ_two, h0, cdf_two_one_left]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coe_unitPower, Set.Icc.coe_zero,
    sub_zero, Real.rpow_one]
  calc (v : ℝ) ^ (b : ℝ) * ((u : ℝ) * (v : ℝ) ^ (1 - (b : ℝ)))
      = u * ((v : ℝ) ^ (b : ℝ) * (v : ℝ) ^ (1 - (b : ℝ))) := by ring
    _ = u * v := by rw [unit_rpow_mul_rpow_one_sub]

/-- A zero second weight gives independence: `K_{a,0}(C) = Π`. -/
@[simp] theorem khoudraji_zero_right (C : Copula 2) (a : I) :
    khoudraji C a 0 = independence 2 := by
  apply ext_cdf_two
  intro u v
  have h0 : ∀ (w : I) (h), unitPower w ((0 : I) : ℝ) h = 1 := fun w h => by ext; simp
  rw [cdf_khoudraji, cdf_independence, Fin.prod_univ_two, h0, cdf_two_one_right]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coe_unitPower, Set.Icc.coe_zero,
    sub_zero, Real.rpow_one]
  calc (u : ℝ) ^ (a : ℝ) * ((u : ℝ) ^ (1 - (a : ℝ)) * (v : ℝ))
      = ((u : ℝ) ^ (a : ℝ) * (u : ℝ) ^ (1 - (a : ℝ))) * v := by ring
    _ = u * v := by rw [unit_rpow_mul_rpow_one_sub]

/-- Marshall–Olkin copulas are the Khoudraji asymmetrizations of `M`. -/
theorem khoudraji_comonotonic (a b : I) :
    khoudraji (comonotonic 2) a b = marshallOlkin a b := rfl

/-- Tawn's asymmetric logistic copulas are the Khoudraji asymmetrizations of Gumbel's. -/
theorem tawn_eq_khoudraji (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    tawn θ hθ α β = khoudraji (gumbel θ hθ) α β := rfl

/-- Khoudraji's construction preserves max-stability (extreme-value copulas). -/
theorem IsExtremeValue.khoudraji {C : Copula 2} (hC : IsExtremeValue C) (a b : I) :
    IsExtremeValue (khoudraji C a b) :=
  hC.maxProduct (isExtremeValue_independence 2) _

/-- `K_{a,b}(C)ᵀ = K_{b,a}(Cᵀ)`. -/
theorem transpose_khoudraji (C : Copula 2) (a b : I) :
    (khoudraji C a b).transpose = khoudraji C.transpose b a := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_khoudraji, cdf_khoudraji, cdf_transpose]
  ring

/-- Khoudraji's construction is monotone for the pointwise order. -/
theorem LowerOrthantLE.khoudraji {C D : Copula 2} (h : C.LowerOrthantLE D) (a b : I) :
    (khoudraji C a b).LowerOrthantLE (khoudraji D a b) := by
  intro w
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hw, cdf_khoudraji, cdf_khoudraji]
  exact mul_le_mul_of_nonneg_right (h _)
    (mul_nonneg (Real.rpow_nonneg (w 0).2.1 _) (Real.rpow_nonneg (w 1).2.1 _))

/-- Khoudraji's construction preserves positive quadrant dependence. -/
theorem IsPQD.khoudraji {C : Copula 2} (hC : C.IsPQD) (a b : I) : (khoudraji C a b).IsPQD := by
  intro u v
  have h := LowerOrthantLE.khoudraji (C := independence 2) (D := C)
    (fun w => by
      have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
      rw [hw, cdf_independence, Fin.prod_univ_two]
      exact hC (w 0) (w 1)) a b ![u, v]
  rw [khoudraji_independence, cdf_independence, Fin.prod_univ_two] at h
  exact h

/-- Khoudraji's construction preserves negative quadrant dependence. -/
theorem IsNQD.khoudraji {C : Copula 2} (hC : C.IsNQD) (a b : I) : (khoudraji C a b).IsNQD := by
  intro u v
  have h := LowerOrthantLE.khoudraji (C := C) (D := independence 2)
    (fun w => by
      have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
      rw [hw, cdf_independence, Fin.prod_univ_two]
      exact hC (w 0) (w 1)) a b ![u, v]
  rw [khoudraji_independence, cdf_independence, Fin.prod_univ_two] at h
  exact h

/-- Khoudraji's construction preserves exchangeability when the weights are equal. -/
theorem IsExchangeable.khoudraji {C : Copula 2} (hC : C.IsExchangeable) (a : I) :
    (khoudraji C a a).IsExchangeable := by
  unfold IsExchangeable at *
  rw [transpose_khoudraji, hC]

/-- The Khoudraji asymmetrization of `M` (the Marshall–Olkin copula) is exchangeable if and
only if `a = b` or one weight vanishes (in which case it is `Π`). -/
theorem isExchangeable_khoudraji_comonotonic_iff (a b : I) :
    (khoudraji (comonotonic 2) a b).IsExchangeable ↔ a = b ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    have ht : (khoudraji (comonotonic 2) a b).transpose = khoudraji (comonotonic 2) b a := by
      rw [transpose_khoudraji, isExchangeable_comonotonic]
    unfold IsExchangeable at h
    rw [h] at ht
    have hx := congrArg chatterjeeXi ht
    rw [khoudraji_comonotonic, khoudraji_comonotonic, marshallOlkin_chatterjeeXi,
      marshallOlkin_chatterjeeXi] at hx
    by_contra hne
    push Not at hne
    obtain ⟨hab, ha0, hb0⟩ := hne
    have ha : 0 < (a : ℝ) := lt_of_le_of_ne a.2.1 (fun h => ha0 (Subtype.ext h.symm))
    have hb : 0 < (b : ℝ) := lt_of_le_of_ne b.2.1 (fun h => hb0 (Subtype.ext h.symm))
    have hab' : (a : ℝ) ≠ b := fun h => hab (Subtype.ext h)
    have ha1 := a.2.2
    have hb1 := b.2.2
    have hD1 : 0 < 3 * (a : ℝ) + b - 2 * a * b := by nlinarith
    have hD2 : 0 < 3 * (b : ℝ) + a - 2 * b * a := by nlinarith
    rw [div_eq_div_iff hD1.ne' hD2.ne'] at hx
    have hfac : (a : ℝ) * b * ((a - b) * (a + b - 2 * a * b)) = 0 := by linear_combination hx / 2
    have h2 : ((a : ℝ) - b) * (a + b - 2 * a * b) = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h (mul_pos ha hb).ne'
      · exact h
    rcases mul_eq_zero.mp h2 with h | h
    · exact hab' (sub_eq_zero.mp h)
    have p1 := mul_nonneg ha.le (sub_nonneg.mpr hb1)
    have p2 := mul_nonneg hb.le (sub_nonneg.mpr ha1)
    have e1 : (a : ℝ) * (1 - b) = 0 := by nlinarith
    have e2 : (b : ℝ) * (1 - a) = 0 := by nlinarith
    have hb' : (1 : ℝ) - b = 0 := (mul_eq_zero.mp e1).resolve_left ha.ne'
    have ha' : (1 : ℝ) - a = 0 := (mul_eq_zero.mp e2).resolve_left hb.ne'
    exact hab' (by linarith)
  · rintro (h | h | h)
    · subst h; exact isExchangeable_comonotonic.khoudraji a
    · subst h; rw [khoudraji_zero_left]; exact isExchangeable_independence
    · subst h; rw [khoudraji_zero_right]; exact isExchangeable_independence

end ProbabilityTheory.Copula
