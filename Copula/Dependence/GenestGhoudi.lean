/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.ConditionalMonotonicity
import Copula.Dependence.DensityTotalPositivity
import Copula.Families.Nelsen
import Copula.TailDependence.GenestGhoudi
import Copula.TailDependence.Quadrant

open scoped unitInterval

/-! # Exact Genest–Ghoudi dependence exclusions and CD range -/

namespace ProbabilityTheory.Copula

private theorem genestGhoudi_zero_diagonal_witness (θ : ℝ) (hθ : 1 ≤ θ) :
    ∃ t : I, 0 < (t : ℝ) ∧ (genestGhoudi θ hθ).cdf ![t,t] = 0 := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  have hθpos : 0 < θ := by linarith
  have hinv : 0 < θ⁻¹ := inv_pos.mpr hθpos
  have ha : 1 < a := Real.one_lt_rpow (by norm_num) hinv
  let q : ℝ := a⁻¹
  have hqpos : 0 < q := inv_pos.mpr (by linarith)
  have hqlt : q < 1 := inv_lt_one_of_one_lt₀ ha
  let t : ℝ := (1-q) ^ θ
  have htpos : 0 < t := Real.rpow_pos_of_pos (by dsimp [q]; linarith) _
  have ht1 : t ≤ 1 :=
    Real.rpow_le_one (by dsimp [q]; linarith) (by dsimp [q]; linarith) hθpos.le
  let ti : I := ⟨t, htpos.le, ht1⟩
  refine ⟨ti, htpos, ?_⟩
  have hpow : (t : ℝ) ^ θ⁻¹ = 1-q := by
    dsimp [t]
    exact Real.rpow_rpow_inv (by dsimp [q]; linarith) hθpos.ne'
  have hinner : 1 - a * (1 - (ti : ℝ) ^ θ⁻¹) = 0 := by
    change 1 - a * (1 - t ^ θ⁻¹) = 0
    rw [hpow]
    have hcancel : a * q = 1 := mul_inv_cancel₀ (ne_of_gt (by linarith : 0 < a))
    linarith
  rw [genestGhoudi_cdf_full]
  have hti : ti ≠ 0 := by
    intro hz
    have hz' := congrArg (fun x : I => (x : ℝ)) hz
    change t = 0 at hz'
    linarith
  simp only [hti, or_self, ↓reduceIte]
  have hnorm : (((1 - (ti : ℝ) ^ θ⁻¹) ^ θ +
      (1 - (ti : ℝ) ^ θ⁻¹) ^ θ) ^ θ⁻¹) =
      a * (1 - (ti : ℝ) ^ θ⁻¹) := by
    have hb : 0 ≤ 1 - (ti : ℝ) ^ θ⁻¹ := by
      have hle : (ti : ℝ) ^ θ⁻¹ ≤ 1 :=
        Real.rpow_le_one htpos.le ht1 hinv.le
      linarith
    rw [← two_mul, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hb _),
      Real.rpow_rpow_inv hb hθpos.ne']
  rw [hnorm]
  rw [hinner]
  simp [Real.zero_rpow hθpos.ne']

/-- Every Genest–Ghoudi copula fails positive quadrant dependence. -/
theorem not_isPQD_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(genestGhoudi θ hθ).IsPQD := by
  obtain ⟨t, ht, hz⟩ := genestGhoudi_zero_diagonal_witness θ hθ
  intro h
  have hh := h t t
  rw [hz] at hh
  nlinarith [mul_pos ht ht]


/-- No Genest–Ghoudi copula is conditionally increasing. -/
theorem not_isCI_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(genestGhoudi θ hθ).IsCI :=
  fun h => not_isPQD_genestGhoudi θ hθ h.isPQD

/-- No Genest–Ghoudi CDF is TP2. -/
theorem not_isTP2CDF_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(genestGhoudi θ hθ).IsTP2CDF :=
  fun h => not_isPQD_genestGhoudi θ hθ h.isPQD

/-- No Genest–Ghoudi copula has an MTP2 Lebesgue density. -/
theorem not_hasMTP2Density_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(genestGhoudi θ hθ).HasMTP2Density :=
  fun h => not_isPQD_genestGhoudi θ hθ (hasMTP2Density_isPQD _ h)

/-- Positive upper-tail dependence excludes CD for θ>1. -/
theorem not_isCD_genestGhoudi (θ : ℝ) (hθ : 1 < θ) :
    ¬(genestGhoudi θ (le_of_lt hθ)).IsCD := by
  intro h
  have hzero := isNQD_hasUpperTailDependence_zero h.isNQD
  have htail := hasUpperTailDependence_genestGhoudi θ (le_of_lt hθ)
  have heq := hzero.unique htail
  have hθ0 : 0 < θ := by linarith
  have hi : 0 < θ⁻¹ := inv_pos.mpr hθ0
  have hcancel : θ * θ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθ0)
  have hinv : θ⁻¹ < 1 := by
    have hm := mul_lt_mul_of_pos_right hθ hi
    nlinarith
  have hp := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hinv
  linarith

/-- The countermonotonic endpoint is CD. -/
theorem isCD_genestGhoudi_one : (genestGhoudi 1 le_rfl).IsCD := by
  simpa only [genestGhoudi_one] using isCD_countermonotonic

/-- Genest–Ghoudi is CD exactly at θ=1. -/
theorem isCD_genestGhoudi_iff (θ : ℝ) (hθ : 1 ≤ θ) :
    (genestGhoudi θ hθ).IsCD ↔ θ = 1 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hθ with heq | hlt
    · exact heq.symm
    · exact False.elim (not_isCD_genestGhoudi θ hlt h)
  · intro heq
    subst θ
    simpa using isCD_genestGhoudi_one

end ProbabilityTheory.Copula
