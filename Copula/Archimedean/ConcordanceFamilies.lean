/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Concordance
import Copula.Families.NelsenTable.N9
import Copula.Families.NelsenTable.N10
import Copula.Families.NelsenTable.N13
import Copula.Families.NelsenTable.N19
import Copula.Families.NelsenTable.N20

/-! # Quadrant dependence of families of Nelsen's Table 4.1 via generators

Applications of the generator criteria of `Copula.Archimedean.Concordance` (Nelsen,
*An Introduction to Copulas*, second edition, Theorem 4.4.2 with `Π` as one of the copulas):
a strict Archimedean copula is PQD iff `ψ(x) ψ(y) ≤ ψ(x + y)`, and an Archimedean copula is NQD
iff `φ(uv) ≤ φ(u) + φ(v)` on `(0, 1]`.

* family 4.2.9 (`0 < θ ≤ 1`) is NQD (`isNQD_nelsen9`): `1 + θ(A + B) ≤ (1 + θA)(1 + θB)`;
* family 4.2.10 (`0 < θ ≤ 1`) is NQD (`isNQD_nelsen10`): `2ab − 1 ≤ (2a − 1)(2b − 1)` for
  `a, b ≥ 1`;
* family 4.2.13 is PQD for `θ ≥ 1` (`isPQD_nelsen13`) and NQD for `0 < θ ≤ 1`
  (`isNQD_nelsen13`), by concavity resp. convexity of `t ↦ t^p` on `[1, ∞)`
  (`one_add_add_rpow_add_one_le`, `one_add_rpow_add_one_le_of_one_le`);
* families 4.2.19 and 4.2.20 (`θ > 0`) are PQD (`isPQD_nelsen19`, `isPQD_nelsen20`), from
  `log(e^a + e^b − 1) ≤ a + b` for `a, b ≥ 0`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- `(1 + a + b)^p + 1 ≤ (1 + a)^p + (1 + b)^p` for `0 ≤ p ≤ 1` and `a, b ≥ 0`. -/
theorem one_add_add_rpow_add_one_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : (1 + (a + b)) ^ p + 1 ≤ (1 + a) ^ p + (1 + b) ^ p := by
  have hconc : ConcaveOn ℝ (Ici 0) (fun s : ℝ => (1 + s) ^ p - 1) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy c d hc hd hcd
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have h := (Real.concaveOn_rpow hp0 hp1).2 (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ 1 + x))
      (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ 1 + y)) hc hd hcd
    simp only [smul_eq_mul] at h ⊢
    have he : c * (1 + x) + d * (1 + y) = 1 + (c * x + d * y) := by linear_combination hcd
    rw [he] at h
    nlinarith
  have h := subadditive_of_concaveOn hconc (by simp) ha hb
  linarith

/-- `(1 + a)^p + (1 + b)^p ≤ (1 + a + b)^p + 1` for `p ≥ 1` and `a, b ≥ 0`. -/
theorem one_add_rpow_add_one_le_of_one_le {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : (1 + a) ^ p + (1 + b) ^ p ≤ (1 + (a + b)) ^ p + 1 := by
  have hconc : ConcaveOn ℝ (Ici 0) (fun s : ℝ => -((1 + s) ^ p - 1)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy c d hc hd hcd
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have h := (convexOn_rpow hp).2 (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ 1 + x))
      (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ 1 + y)) hc hd hcd
    simp only [smul_eq_mul] at h ⊢
    have he : c * (1 + x) + d * (1 + y) = 1 + (c * x + d * y) := by linear_combination hcd
    rw [he] at h
    nlinarith
  have h := subadditive_of_concaveOn hconc (by simp) ha hb
  linarith

private theorem invFunReal_of_pos (g : BivariateGenerator) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    g.invFunReal x = g.invFun ⟨x, hx0.le, hx1⟩ := by
  rw [BivariateGenerator.invFunReal, projIcc_of_mem _ ⟨hx0.le, hx1⟩]

private theorem log_nonneg_neg {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) : 0 ≤ -Real.log u :=
  neg_nonneg.mpr (Real.log_nonpos hu0.le hu1)

/-- Nelsen's family 9 is negatively quadrant dependent. -/
theorem isNQD_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : (nelsen9 θ hθ h1).IsNQD := by
  rw [nelsen9, BivariateGenerator.isNQD_iff]
  intro u v hu0 hu1 hv0 hv1
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have huv1 : u * v ≤ 1 := by nlinarith
  rw [invFunReal_of_pos _ huv0 huv1, invFunReal_of_pos _ hu0 hu1, invFunReal_of_pos _ hv0 hv1]
  change Real.log (1 - θ * Real.log (u * v)) ≤
    Real.log (1 - θ * Real.log u) + Real.log (1 - θ * Real.log v)
  have hA := log_nonneg_neg hu0 hu1
  have hB := log_nonneg_neg hv0 hv1
  have hpa : 0 < 1 - θ * Real.log u := by nlinarith
  have hpb : 0 < 1 - θ * Real.log v := by nlinarith
  rw [← Real.log_mul hpa.ne' hpb.ne', Real.log_mul hu0.ne' hv0.ne']
  apply Real.log_le_log (by nlinarith)
  nlinarith [mul_nonneg (mul_nonneg hθ.le hA) (mul_nonneg hθ.le hB)]

/-- Nelsen's family 10 is negatively quadrant dependent. -/
theorem isNQD_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : (nelsen10 θ hθ h1).IsNQD := by
  rw [nelsen10, BivariateGenerator.isNQD_iff]
  intro u v hu0 hu1 hv0 hv1
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have huv1 : u * v ≤ 1 := by nlinarith
  rw [invFunReal_of_pos _ huv0 huv1, invFunReal_of_pos _ hu0 hu1, invFunReal_of_pos _ hv0 hv1]
  simp only [nelsen10Generator, BivariateGenerator.innerPower, amhGenerator, coe_unitPower,
    inv_inv]
  rw [Real.mul_rpow hu0.le hv0.le]
  set a := u ^ θ with ha
  set b := v ^ θ with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hu0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hv0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one hu0.le hu1 hθ.le
  have hb1 : b ≤ 1 := Real.rpow_le_one hv0.le hv1 hθ.le
  have hA : 1 ≤ 2 / a - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ ha0]; linarith
  have hB : 1 ≤ 2 / b - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hb0]; linarith
  have e1 : -1 + (1 - -1) / (a * b) = 2 / (a * b) - 1 := by ring
  have e2 : -1 + (1 - -1) / a = 2 / a - 1 := by ring
  have e3 : -1 + (1 - -1) / b = 2 / b - 1 := by ring
  rw [e1, e2, e3, ← Real.log_mul (by linarith) (by linarith)]
  apply Real.log_le_log
  · have : 2 ≤ 2 / (a * b) := by
      rw [le_div_iff₀ (mul_pos ha0 hb0)]; nlinarith
    linarith
  · have hia : 1 ≤ 1 / a := by rw [le_div_iff₀ ha0]; linarith
    have hib : 1 ≤ 1 / b := by rw [le_div_iff₀ hb0]; linarith
    have e4 : 2 / (a * b) = 2 * (1 / a) * (1 / b) := by field_simp
    have e5 : 2 / a = 2 * (1 / a) := by ring
    have e6 : 2 / b = 2 * (1 / b) := by ring
    rw [e4, e5, e6]
    nlinarith [mul_nonneg (sub_nonneg.mpr hia) (sub_nonneg.mpr hib)]

/-- Nelsen's family 13 is positively quadrant dependent for `θ ≥ 1`. -/
theorem isPQD_nelsen13 (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen13 θ (by linarith)).IsPQD := by
  have hstrict : (nelsen13Generator θ (by linarith)).IsStrict := fun _ _ => Real.exp_pos _
  rw [nelsen13, BivariateGenerator.isPQD_iff _ hstrict]
  intro x y hx hy
  change Real.exp (1 - (1 + x) ^ θ⁻¹) * Real.exp (1 - (1 + y) ^ θ⁻¹) ≤
    Real.exp (1 - (1 + (x + y)) ^ θ⁻¹)
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := one_add_add_rpow_add_one_le (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ θ))
    (inv_le_one_of_one_le₀ hθ) hx hy
  linarith

/-- Nelsen's family 13 is negatively quadrant dependent for `0 < θ ≤ 1`. -/
theorem isNQD_nelsen13 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : (nelsen13 θ hθ).IsNQD := by
  rw [nelsen13, BivariateGenerator.isNQD_iff]
  intro u v hu0 hu1 hv0 hv1
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have huv1 : u * v ≤ 1 := by nlinarith
  rw [invFunReal_of_pos _ huv0 huv1, invFunReal_of_pos _ hu0 hu1, invFunReal_of_pos _ hv0 hv1]
  change (1 - Real.log (u * v)) ^ θ - 1 ≤ ((1 - Real.log u) ^ θ - 1) + ((1 - Real.log v) ^ θ - 1)
  rw [Real.log_mul hu0.ne' hv0.ne']
  have h := one_add_add_rpow_add_one_le hθ.le h1 (log_nonneg_neg hu0 hu1) (log_nonneg_neg hv0 hv1)
  have e1 : 1 - (Real.log u + Real.log v) = 1 + (-Real.log u + -Real.log v) := by ring
  have e2 : 1 - Real.log u = 1 + -Real.log u := by ring
  have e3 : 1 - Real.log v = 1 + -Real.log v := by ring
  rw [e1, e2, e3]
  linarith

/-- `log(e^a + e^b − 1) ≤ a + b` for `a, b ≥ 0`. -/
private theorem log_exp_add_exp_sub_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (Real.exp a + Real.exp b - 1) ≤ a + b := by
  have hea := Real.one_le_exp ha
  have heb := Real.one_le_exp hb
  rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr hea) (sub_nonneg.mpr heb)]

/-- Nelsen's family 19 is positively quadrant dependent. -/
theorem isPQD_nelsen19 (θ : ℝ) (hθ : 0 < θ) : (nelsen19 θ hθ).IsPQD := by
  have hL : ∀ s, 0 ≤ s → θ ≤ Real.log (s + Real.exp θ) := fun s hs => le_log_add_exp hs θ
  have hstrict : (nelsen19Generator θ hθ).IsStrict := fun s hs =>
    div_pos hθ (hθ.trans_le (hL s hs))
  rw [nelsen19, BivariateGenerator.isPQD_iff _ hstrict]
  intro x y hx hy
  change θ / Real.log (x + Real.exp θ) * (θ / Real.log (y + Real.exp θ)) ≤
    θ / Real.log (x + y + Real.exp θ)
  set a := Real.log (x + Real.exp θ) - θ with ha
  set b := Real.log (y + Real.exp θ) - θ with hb
  have ha0 : 0 ≤ a := by linarith [hL x hx]
  have hb0 : 0 ≤ b := by linarith [hL y hy]
  have hxa : x + Real.exp θ = Real.exp θ * Real.exp a := by
    rw [← Real.exp_add, ha, add_sub_cancel, Real.exp_log (by positivity)]
  have hyb : y + Real.exp θ = Real.exp θ * Real.exp b := by
    rw [← Real.exp_add, hb, add_sub_cancel, Real.exp_log (by positivity)]
  have hxy : Real.log (x + y + Real.exp θ) ≤ θ + (a + b) := by
    have he : x + y + Real.exp θ = Real.exp θ * (Real.exp a + Real.exp b - 1) := by
      linear_combination hxa + hyb
    have hpos : 0 < Real.exp a + Real.exp b - 1 := by
      linarith [Real.one_le_exp ha0, Real.one_le_exp hb0]
    rw [he, Real.log_mul (Real.exp_pos θ).ne' hpos.ne', Real.log_exp]
    linarith [log_exp_add_exp_sub_one_le ha0 hb0]
  have hLx : Real.log (x + Real.exp θ) = θ + a := by rw [ha]; ring
  have hLy : Real.log (y + Real.exp θ) = θ + b := by rw [hb]; ring
  have hLxy : θ ≤ Real.log (x + y + Real.exp θ) := hL _ (add_nonneg hx hy)
  rw [hLx, hLy, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith [mul_nonneg ha0 hb0]

/-- Nelsen's family 20 is positively quadrant dependent. -/
theorem isPQD_nelsen20 (θ : ℝ) (hθ : 0 < θ) : (nelsen20 θ hθ).IsPQD := by
  have hL : ∀ s, 0 ≤ s → 1 ≤ Real.log (s + Real.exp 1) := fun s hs => le_log_add_exp hs 1
  have hstrict : (nelsen20Generator θ hθ).IsStrict := fun s hs =>
    Real.rpow_pos_of_pos (zero_lt_one.trans_le (hL s hs)) _
  rw [nelsen20, BivariateGenerator.isPQD_iff _ hstrict]
  intro x y hx hy
  change Real.log (x + Real.exp 1) ^ (-θ⁻¹) * Real.log (y + Real.exp 1) ^ (-θ⁻¹) ≤
    Real.log (x + y + Real.exp 1) ^ (-θ⁻¹)
  set a := Real.log (x + Real.exp 1) - 1 with ha
  set b := Real.log (y + Real.exp 1) - 1 with hb
  have ha0 : 0 ≤ a := by linarith [hL x hx]
  have hb0 : 0 ≤ b := by linarith [hL y hy]
  have hxa : x + Real.exp 1 = Real.exp 1 * Real.exp a := by
    rw [← Real.exp_add, ha, add_sub_cancel, Real.exp_log (by positivity)]
  have hyb : y + Real.exp 1 = Real.exp 1 * Real.exp b := by
    rw [← Real.exp_add, hb, add_sub_cancel, Real.exp_log (by positivity)]
  have hxy : Real.log (x + y + Real.exp 1) ≤ 1 + (a + b) := by
    have he : x + y + Real.exp 1 = Real.exp 1 * (Real.exp a + Real.exp b - 1) := by
      linear_combination hxa + hyb
    have hpos : 0 < Real.exp a + Real.exp b - 1 := by
      linarith [Real.one_le_exp ha0, Real.one_le_exp hb0]
    rw [he, Real.log_mul (Real.exp_pos 1).ne' hpos.ne', Real.log_exp]
    linarith [log_exp_add_exp_sub_one_le ha0 hb0]
  have hLx : Real.log (x + Real.exp 1) = 1 + a := by rw [ha]; ring
  have hLy : Real.log (y + Real.exp 1) = 1 + b := by rw [hb]; ring
  have hLxy : 1 ≤ Real.log (x + y + Real.exp 1) := hL _ (add_nonneg hx hy)
  rw [hLx, hLy, ← Real.mul_rpow (by linarith) (by linarith)]
  apply Real.rpow_le_rpow_of_nonpos (by linarith) _ (neg_nonpos.mpr (inv_nonneg.mpr hθ.le))
  nlinarith [mul_nonneg ha0 hb0]

end ProbabilityTheory.Copula
