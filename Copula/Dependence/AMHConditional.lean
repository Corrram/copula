/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.AMH
import Copula.Dependence.ConditionalMonotonicity

/-! # Exact conditional monotonicity of Ali–Mikhail–Haq copulas -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem amh_den_pos (θ : ℝ) (hθ : θ ≤ 1) (u v : I)
    (hv : 0 < (v : ℝ)) :
    0 < 1 - θ * (1 - (u : ℝ)) * (1 - (v : ℝ)) := by
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hu1 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
  have hv1 : 0 ≤ 1 - (v : ℝ) := sub_nonneg.mpr v.property.2
  have hp : 0 ≤ (1 - (u : ℝ)) * (1 - (v : ℝ)) := mul_nonneg hu1 hv1
  have hple : (1 - (u : ℝ)) * (1 - (v : ℝ)) < 1 := by
    have h := mul_le_mul_of_nonneg_right (show 1 - (u : ℝ) ≤ 1 by linarith) hv1
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hθ hp
  nlinarith

private theorem fractional_chord (A B q x y z : ℝ)
    (hx : A + B * x ≠ 0) (hy : A + B * y ≠ 0)
    (hz : A + B * z ≠ 0) :
    (z - x) * (q * y / (A + B * y)) -
      (y - x) * (q * z / (A + B * z)) -
      (z - y) * (q * x / (A + B * x)) =
      q * A * B * (y - x) * (z - y) * (z - x) /
        ((A + B * x) * (A + B * y) * (A + B * z)) := by
  let Dx : ℝ := A + B * x
  let Dy : ℝ := A + B * y
  let Dz : ℝ := A + B * z
  have hDx : Dx ≠ 0 := hx
  have hDy : Dy ≠ 0 := hy
  have hDz : Dz ≠ 0 := hz
  change (z - x) * (q * y / Dy) - (y - x) * (q * z / Dz) -
    (z - y) * (q * x / Dx) =
    q * A * B * (y - x) * (z - y) * (z - x) / (Dx * Dy * Dz)
  field_simp [hDx, hDy, hDz]
  dsimp [Dx, Dy, Dz]
  ring

private theorem amh_chord (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1)
    (a b c v : I) (hv : 0 < (v : ℝ)) :
    ((c : ℝ) - (a : ℝ)) * (amh θ hmin hmax).cdf ![b, v] -
      ((b : ℝ) - (a : ℝ)) * (amh θ hmin hmax).cdf ![c, v] -
      ((c : ℝ) - (b : ℝ)) * (amh θ hmin hmax).cdf ![a, v] =
    ((v : ℝ) * (1 - θ * (1 - (v : ℝ))) * (θ * (1 - (v : ℝ))) *
      ((b : ℝ) - (a : ℝ)) * ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ))) /
      ((1 - θ * (1 - (a : ℝ)) * (1 - (v : ℝ))) *
        (1 - θ * (1 - (b : ℝ)) * (1 - (v : ℝ))) *
        (1 - θ * (1 - (c : ℝ)) * (1 - (v : ℝ)))) := by
  let A : ℝ := 1 - θ * (1 - (v : ℝ))
  let B : ℝ := θ * (1 - (v : ℝ))
  have hden (x : I) :
      1 - θ * (1 - (x : ℝ)) * (1 - (v : ℝ)) = A + B * (x : ℝ) := by
    dsimp [A, B]
    ring
  have hda : A + B * (a : ℝ) ≠ 0 := by
    rw [← hden a]
    exact (amh_den_pos θ hmax a v hv).ne'
  have hdb : A + B * (b : ℝ) ≠ 0 := by
    rw [← hden b]
    exact (amh_den_pos θ hmax b v hv).ne'
  have hdc : A + B * (c : ℝ) ≠ 0 := by
    rw [← hden c]
    exact (amh_den_pos θ hmax c v hv).ne'
  rw [cdf_amh, cdf_amh, cdf_amh]
  rw [hden a, hden b, hden c]
  convert fractional_chord A B (v : ℝ) (a : ℝ) (b : ℝ) (c : ℝ)
    hda hdb hdc using 1; dsimp [A, B]; ring

/-- AMH is directionally conditionally increasing for every nonnegative parameter. -/
theorem isSI_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (hθ : 0 ≤ θ) :
    (amh θ hmin hmax).IsSI := by
  intro a b c v hab hbc
  by_cases hv : v = 0
  · subst v
    simp [cdf_amh]
  have hvp : 0 < (v : ℝ) :=
    lt_of_le_of_ne v.property.1 (Ne.symm (by
      intro he; exact hv (Subtype.ext he)))
  have hA : 0 < 1 - θ * (1 - (v : ℝ)) := by
    simpa using amh_den_pos θ hmax 0 v hvp
  have hnum : 0 ≤ (v : ℝ) * (1 - θ * (1 - (v : ℝ))) *
      (θ * (1 - (v : ℝ))) * ((b : ℝ) - (a : ℝ)) *
      ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hvp.le hA.le)
            (mul_nonneg hθ (sub_nonneg.mpr v.property.2)))
          (sub_nonneg.mpr hab))
        (sub_nonneg.mpr hbc))
      (sub_nonneg.mpr (hab.trans hbc))
  have hden : 0 < (1 - θ * (1 - (a : ℝ)) * (1 - (v : ℝ))) *
      (1 - θ * (1 - (b : ℝ)) * (1 - (v : ℝ))) *
      (1 - θ * (1 - (c : ℝ)) * (1 - (v : ℝ))) := by
    exact mul_pos (mul_pos (amh_den_pos θ hmax a v hvp)
      (amh_den_pos θ hmax b v hvp)) (amh_den_pos θ hmax c v hvp)
  have hch := amh_chord θ hmin hmax a b c v hvp
  have hr : 0 ≤
      ((c : ℝ) - (a : ℝ)) * (amh θ hmin hmax).cdf ![b, v] -
      ((b : ℝ) - (a : ℝ)) * (amh θ hmin hmax).cdf ![c, v] -
      ((c : ℝ) - (b : ℝ)) * (amh θ hmin hmax).cdf ![a, v] := by
    rw [hch]
    exact div_nonneg hnum hden.le
  linarith

/-- AMH is directionally conditionally decreasing for every nonpositive parameter. -/
theorem isSD_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (hθ : θ ≤ 0) :
    (amh θ hmin hmax).IsSD := by
  intro a b c v hab hbc
  by_cases hv : v = 0
  · subst v
    simp [cdf_amh]
  have hvp : 0 < (v : ℝ) :=
    lt_of_le_of_ne v.property.1 (Ne.symm (by
      intro he; exact hv (Subtype.ext he)))
  have hA : 0 < 1 - θ * (1 - (v : ℝ)) := by
    simpa using amh_den_pos θ hmax 0 v hvp
  have hnum : (v : ℝ) * (1 - θ * (1 - (v : ℝ))) *
      (θ * (1 - (v : ℝ))) * ((b : ℝ) - (a : ℝ)) *
      ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ)) ≤ 0 := by
    have hB : θ * (1 - (v : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hθ (sub_nonneg.mpr v.property.2)
    have hstart : (v : ℝ) * (1 - θ * (1 - (v : ℝ))) *
        (θ * (1 - (v : ℝ))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hvp.le hA.le) hB
    have h4 := mul_nonpos_of_nonpos_of_nonneg hstart (sub_nonneg.mpr hab)
    have h5 := mul_nonpos_of_nonpos_of_nonneg h4 (sub_nonneg.mpr hbc)
    exact mul_nonpos_of_nonpos_of_nonneg h5 (sub_nonneg.mpr (hab.trans hbc))
  have hden : 0 < (1 - θ * (1 - (a : ℝ)) * (1 - (v : ℝ))) *
      (1 - θ * (1 - (b : ℝ)) * (1 - (v : ℝ))) *
      (1 - θ * (1 - (c : ℝ)) * (1 - (v : ℝ))) := by
    exact mul_pos (mul_pos (amh_den_pos θ hmax a v hvp)
      (amh_den_pos θ hmax b v hvp)) (amh_den_pos θ hmax c v hvp)
  have hch := amh_chord θ hmin hmax a b c v hvp
  have hr :
      ((c : ℝ) - (a : ℝ)) * (amh θ hmin hmax).cdf ![b, v] -
      ((b : ℝ) - (a : ℝ)) * (amh θ hmin hmax).cdf ![c, v] -
      ((c : ℝ) - (b : ℝ)) * (amh θ hmin hmax).cdf ![a, v] ≤ 0 := by
    rw [hch]
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
  linarith

/-- AMH is conditionally increasing exactly for θ≥0. -/
theorem isCI_amh_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).IsCI ↔ 0 ≤ θ := by
  constructor
  · intro h
    exact (isPQD_amh_iff θ hmin hmax).mp h.isPQD
  · intro h
    exact (isArchimedean_amh θ hmin hmax).isCI_iff.mpr
      (isSI_amh θ hmin hmax h)

/-- AMH is conditionally decreasing exactly for θ≤0. -/
theorem isCD_amh_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).IsCD ↔ θ ≤ 0 := by
  constructor
  · intro h
    exact (isNQD_amh_iff θ hmin hmax).mp h.isNQD
  · intro h
    exact (isArchimedean_amh θ hmin hmax).isCD_iff.mpr
      (isSD_amh θ hmin hmax h)

end ProbabilityTheory.Copula
