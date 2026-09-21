/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Bernstein.Basis
import Copula.OrdinalSum.Basic

/-! # Bernstein copulas

The tensor Bernstein polynomial of a copula is again a copula for arbitrary
positive degrees in the two coordinates. Copula validity is proved from
the polynomial formula, using monotonicity of Bernstein combinations of
ordered coefficients; no admissibility proof is required from the caller.
-/

open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

open Bernstein

private theorem bernstein_grid_mono (n : ℕ) :
    Monotone (_root_.bernstein.z (n := n)) := by
  intro i j hij
  change (i : ℝ) / n ≤ (j : ℝ) / n
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg _)

/-- Tensor Bernstein polynomial of the sampled copula CDF. -/
noncomputable def bernsteinCDF (C : Copula 2) (m n : ℕ) (u v : I) : ℝ :=
  blend m (fun i => blend n
    (fun j => C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j]) v) u

/-- The classical copula conditions hold for every pair of positive degrees. -/
theorem isClassical_bernsteinCDF (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsClassical (fun u : Fin 2 → I => C.bernsteinCDF m n (u 0) (u 1)) := by
  apply IsClassical.ofBivariate
  · intro v
    simp [bernsteinCDF, blend_const]
  · intro u
    simp [bernsteinCDF, blend_const]
  · intro v
    simp only [bernsteinCDF, blend_one, _root_.bernstein.z_last (Nat.ne_of_gt hm),
      cdf_two_one_left]
    exact blend_id n hn v
  · intro u
    simp only [bernsteinCDF, blend_one, _root_.bernstein.z_last (Nat.ne_of_gt hn),
      cdf_two_one_right]
    exact blend_id m hm u
  · intro a b c d hab hcd
    let g : Fin (m + 1) → ℝ := fun i =>
      blend n (fun j => C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j]) d -
      blend n (fun j => C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j]) c
    have hg : Monotone g := by
      intro i j hij
      let f : Fin (n + 1) → ℝ := fun k =>
        C.cdf ![_root_.bernstein.z j, _root_.bernstein.z k] -
        C.cdf ![_root_.bernstein.z i, _root_.bernstein.z k]
      have hf : Monotone f := by
        intro k l hkl
        have h := C.rectangleIncrement_cdf_nonneg
          ![_root_.bernstein.z i, _root_.bernstein.z k]
          ![_root_.bernstein.z j, _root_.bernstein.z l] (by
            intro r; fin_cases r
            · exact bernstein_grid_mono m hij
            · exact bernstein_grid_mono n hkl)
        simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
        dsimp [f]
        linarith
      have h := blend_mono n f hf hcd
      dsimp [f] at h
      rw [blend_sub, blend_sub] at h
      dsimp [g]
      linarith
    have h := blend_mono m g hg hab
    dsimp [g] at h
    rw [blend_sub, blend_sub] at h
    dsimp [bernsteinCDF]
    linarith

/-- The Bernstein copula with positive coordinate degrees `m` and `n`. -/
noncomputable def bernstein (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : Copula 2 :=
  ofClassical _ (C.isClassical_bernsteinCDF m n hm hn)

@[simp] theorem cdf_bernstein (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (u : Fin 2 → I) :
    (C.bernstein m n hm hn).cdf u = C.bernsteinCDF m n (u 0) (u 1) :=
  congrFun (cdf_ofClassical _ _) u

/-- The usual tensor-product Bernstein formula, with indices including both endpoints. -/
theorem bernsteinCDF_eq_sum (C : Copula 2) (m n : ℕ) (u v : I) :
    C.bernsteinCDF m n u v = ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
      C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j] *
        _root_.bernstein m i u * _root_.bernstein n j v := by
  simp only [bernsteinCDF, blend, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- Bernstein smoothing fixes independence at every pair of positive degrees. -/
@[simp] theorem bernstein_independence (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (independence 2).bernstein m n hm hn = independence 2 := by
  apply ext_cdf
  intro u
  rw [cdf_bernstein]
  simp only [bernsteinCDF, cdf_independence, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h (i : Fin (m + 1)) : blend n
      (fun j => (_root_.bernstein.z i : ℝ) * (_root_.bernstein.z j : ℝ)) (u 1) =
        (_root_.bernstein.z i : ℝ) * (u 1 : ℝ) := by
    simp only [blend, mul_assoc, ← Finset.mul_sum]
    rw [← blend, blend_id n hn]
  simp_rw [h]
  simp only [blend]
  simp_rw [mul_right_comm (_ : ℝ) (u 1 : ℝ)]
  rw [← Finset.sum_mul, ← blend, blend_id m hm]

/-- The degree `(1,1)` Bernstein approximation of every copula is independence. -/
@[simp] theorem bernstein_one_one (C : Copula 2) :
    C.bernstein 1 1 (by decide) (by decide) = independence 2 := by
  apply ext_cdf
  intro u
  simp [bernsteinCDF, blend, Fin.sum_univ_two, _root_.bernstein.z,
    _root_.bernstein_apply, cdf_independence, Fin.prod_univ_two, mul_comm]

end ProbabilityTheory.Copula
