/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Integration
import Copula.Mixture

/-! # Quadrant, tail and stochastic positive dependence

LTD, RTI and SI refer to coordinate `1` given coordinate `0`.
The division-free tail inequalities include the boundary points. SI uses
the equivalent CDF concavity characterization, written with chord lengths.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

@[simp] theorem cdf_two_zero_left (C : Copula 2) (v : I) : C.cdf ![0, v] = 0 :=
  C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl

@[simp] theorem cdf_two_one_left (C : Copula 2) (v : I) : C.cdf ![1, v] = (v : ℝ) := by
  have he : ![(1 : I), v] = Function.update (fun _ : Fin 2 => (1 : I)) 1 v := by
    ext i; fin_cases i <;> simp
  rw [he, C.cdf_update_one]

@[simp] theorem cdf_two_one_right (C : Copula 2) (u : I) : C.cdf ![u, 1] = (u : ℝ) := by
  have he : ![u, (1 : I)] = Function.update (fun _ : Fin 2 => (1 : I)) 0 u := by
    ext i; fin_cases i <;> simp
  rw [he, C.cdf_update_one]

/-- Positive quadrant dependence. -/
def IsPQD (C : Copula 2) : Prop := ∀ u v : I, (u : ℝ) * (v : ℝ) ≤ C.cdf ![u, v]

/-- Negative quadrant dependence. -/
def IsNQD (C : Copula 2) : Prop := ∀ u v : I, C.cdf ![u, v] ≤ (u : ℝ) * (v : ℝ)

/-- Left-tail decreasing: `P(V ≤ v | U ≤ u)` decreases in `u > 0`. -/
def IsLTD (C : Copula 2) : Prop :=
  ∀ a b v : I, a ≤ b → (a : ℝ) * C.cdf ![b, v] ≤ (b : ℝ) * C.cdf ![a, v]

/-- Right-tail increasing: `P(V > v | U > u)` increases in `u < 1`.
Equivalently, the upper-tail conditional CDF decreases. -/
def IsRTI (C : Copula 2) : Prop :=
  ∀ a b v : I, a ≤ b →
    (1 - (a : ℝ)) * ((v : ℝ) - C.cdf ![b, v]) ≤
      (1 - (b : ℝ)) * ((v : ℝ) - C.cdf ![a, v])

/-- Stochastic increasingness via concavity of every first-coordinate CDF section.
The chord inequality avoids division by zero, including coincident endpoints. -/
def IsSI (C : Copula 2) : Prop :=
  ∀ a b c v : I, a ≤ b → b ≤ c →
    ((b : ℝ) - (a : ℝ)) * C.cdf ![c, v] +
      ((c : ℝ) - (b : ℝ)) * C.cdf ![a, v] ≤
        ((c : ℝ) - (a : ℝ)) * C.cdf ![b, v]

theorem IsLTD.isPQD {C : Copula 2} (h : C.IsLTD) : C.IsPQD := by
  intro u v
  simpa using h u 1 v u.property.2

theorem IsRTI.isPQD {C : Copula 2} (h : C.IsRTI) : C.IsPQD := by
  intro u v
  have ht := h 0 u v u.property.1
  simp at ht
  linarith

theorem IsSI.isLTD {C : Copula 2} (h : C.IsSI) : C.IsLTD := by
  intro a b v hab
  simpa using h 0 a b v a.property.1 hab

theorem IsSI.isRTI {C : Copula 2} (h : C.IsSI) : C.IsRTI := by
  intro a b v hab
  have ht := h a b 1 v hab b.property.2
  simp only [cdf_two_one_left] at ht
  change ((b : ℝ) - (a : ℝ)) * (v : ℝ) + (1 - (b : ℝ)) * C.cdf ![a, v] ≤
    (1 - (a : ℝ)) * C.cdf ![b, v] at ht
  nlinarith

theorem IsSI.isPQD {C : Copula 2} (h : C.IsSI) : C.IsPQD := h.isLTD.isPQD

theorem isLTD_iff_ratio_antitone (C : Copula 2) : C.IsLTD ↔
    ∀ v : I, AntitoneOn (fun u : I => C.cdf ![u, v] / (u : ℝ)) (Set.Ioi 0) := by
  constructor
  · intro h v a ha b hb hab
    exact (div_le_div_iff₀ (show 0 < (b : ℝ) from hb)
      (show 0 < (a : ℝ) from ha)).mpr (by nlinarith [h a b v hab])
  · intro h a b v hab
    by_cases ha : a = 0
    · simp [ha]
    · have ha' : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha)
      have hb' : 0 < b := ha'.trans_le hab
      have ht := (div_le_div_iff₀ (show 0 < (b : ℝ) from hb')
        (show 0 < (a : ℝ) from ha')).mp (h v ha' hb' hab)
      nlinarith

theorem isRTI_iff_ratio_antitone (C : Copula 2) : C.IsRTI ↔
    ∀ v : I, AntitoneOn (fun u : I => ((v : ℝ) - C.cdf ![u, v]) / (1 - (u : ℝ)))
      (Set.Iio 1) := by
  constructor
  · intro h v a ha b hb hab
    exact (div_le_div_iff₀ (sub_pos.mpr (show (b : ℝ) < 1 from hb))
      (sub_pos.mpr (show (a : ℝ) < 1 from ha))).mpr (by nlinarith [h a b v hab])
  · intro h a b v hab
    by_cases hb : b = 1
    · simp [hb]
    · have hb' : b < 1 := lt_of_le_of_ne b.property.2 hb
      have ha' : a < 1 := hab.trans_lt hb'
      have ht := (div_le_div_iff₀ (sub_pos.mpr (show (b : ℝ) < 1 from hb'))
        (sub_pos.mpr (show (a : ℝ) < 1 from ha'))).mp (h v ha' hb' hab)
      nlinarith

theorem IsPQD.mix {C D : Copula 2} (hC : C.IsPQD) (hD : D.IsPQD) (w : I) :
    (mix C D w).IsPQD := by
  intro u v
  rw [cdf_mix]
  nlinarith [mul_nonneg w.property.1 (sub_nonneg.mpr (hC u v)),
    mul_nonneg (sub_nonneg.mpr w.property.2) (sub_nonneg.mpr (hD u v))]

/-- The usual survival-probability formulation of RTI. -/
theorem isRTI_iff_survivalRatio_monotone (C : Copula 2) : C.IsRTI ↔
    ∀ v : I, MonotoneOn
      (fun u : I => (1 - (u : ℝ) - (v : ℝ) + C.cdf ![u, v]) / (1 - (u : ℝ))) (Set.Iio 1) := by
  constructor
  · intro h v a ha b hb hab
    apply (div_le_div_iff₀ (sub_pos.mpr (show (a : ℝ) < 1 from ha))
      (sub_pos.mpr (show (b : ℝ) < 1 from hb))).mpr
    nlinarith [h a b v hab]
  · intro h a b v hab
    by_cases hb : b = 1
    · simp [hb]
    · have hb' : b < 1 := lt_of_le_of_ne b.property.2 hb
      have ha' : a < 1 := hab.trans_lt hb'
      have ht := (div_le_div_iff₀ (sub_pos.mpr (show (a : ℝ) < 1 from ha'))
        (sub_pos.mpr (show (b : ℝ) < 1 from hb'))).mp (h v ha' hb' hab)
      nlinarith

theorem IsLTD.mix {C D : Copula 2} (hC : C.IsLTD) (hD : D.IsLTD) (w : I) :
    (mix C D w).IsLTD := by
  intro a b v hab
  simp only [cdf_mix]
  nlinarith [mul_nonneg w.property.1 (sub_nonneg.mpr (hC a b v hab)),
    mul_nonneg (sub_nonneg.mpr w.property.2) (sub_nonneg.mpr (hD a b v hab))]

theorem IsRTI.mix {C D : Copula 2} (hC : C.IsRTI) (hD : D.IsRTI) (w : I) :
    (mix C D w).IsRTI := by
  intro a b v hab
  simp only [cdf_mix]
  nlinarith [mul_nonneg w.property.1 (sub_nonneg.mpr (hC a b v hab)),
    mul_nonneg (sub_nonneg.mpr w.property.2) (sub_nonneg.mpr (hD a b v hab))]

theorem IsSI.mix {C D : Copula 2} (hC : C.IsSI) (hD : D.IsSI) (w : I) :
    (mix C D w).IsSI := by
  intro a b c v hab hbc
  simp only [cdf_mix]
  nlinarith [mul_nonneg w.property.1 (sub_nonneg.mpr (hC a b c v hab hbc)),
    mul_nonneg (sub_nonneg.mpr w.property.2) (sub_nonneg.mpr (hD a b c v hab hbc))]

end ProbabilityTheory.Copula
