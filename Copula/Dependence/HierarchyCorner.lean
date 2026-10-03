/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Transpose
import Copula.Dependence.Singular
import Copula.Order.Survival
import Copula.Symmetry

/-!
# Corner set monotonicity: LCSD and RCSI

Harris (1970) introduced the corner set monotonicity notions (Nelsen, *An Introduction to
Copulas*, 2nd ed., §5.2.3):

* `(X, Y)` is *left corner set decreasing* (LCSD) if
  `P(X ≤ x, Y ≤ y | X ≤ x', Y ≤ y')` is nonincreasing in `x'` and `y'`;
* `(X, Y)` is *right corner set increasing* (RCSI) if
  `P(X > x, Y > y | X > x', Y > y')` is nondecreasing in `x'` and `y'`.

For copulas we state both conditions division-free, cross-multiplying the conditional
probabilities (`IsLCSD`, `IsRCSI`); boundary cases with vanishing conditioning probabilities
are then automatically included. We prove

* LCSD is equivalent to total positivity of the copula CDF (`isLCSD_iff_isTP2CDF`,
  Nelsen §5.2.3);
* RCSI is equivalent to total positivity of the joint survival function
  `(u, v) ↦ 1 - u - v + C(u, v)` (`isRCSI_iff_isTP2_survival`, Nelsen §5.2.3), and to
  LCSD of the survival copula (`isRCSI_iff_survivalCopula_isLCSD`);
* both notions are symmetric in the coordinates;
* LCSD implies LTD in both directions, RCSI implies RTI in both directions
  (Nelsen §5.2.3), hence both imply PQD;
* `M` and `Π` are LCSD and RCSI, while `W` is neither.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Left corner set decreasing, in cross-multiplied form:
`P(U ≤ u, V ≤ v | U ≤ a, V ≤ b)` is nonincreasing in `(a, b)`. -/
def IsLCSD (C : Copula 2) : Prop :=
  ∀ u v a b a' b' : I, a ≤ a' → b ≤ b' →
    C.cdf ![min u a', min v b'] * C.cdf ![a, b] ≤ C.cdf ![min u a, min v b] * C.cdf ![a', b']

/-- Right corner set increasing, in cross-multiplied form:
`P(U > u, V > v | U > a, V > b)` is nondecreasing in `(a, b)`. -/
def IsRCSI (C : Copula 2) : Prop :=
  ∀ u v a b a' b' : I, a ≤ a' → b ≤ b' →
    C.survival ![max u a, max v b] * C.survival ![a', b'] ≤
      C.survival ![max u a', max v b'] * C.survival ![a, b]

/-! ## A two-step argument for TP2 functions -/

/-- One coordinate step of the corner-set inequality for a nonnegative TP2 function that is
monotone in its first argument. -/
private theorem tp2_corner_step {F : I → I → ℝ} (htp : IsTP2 F) (hn : ∀ a b, 0 ≤ F a b)
    (hm : ∀ b, Monotone (fun a => F a b)) (x : I) {a a' y b : I} (haa : a ≤ a')
    (hyb : y ≤ b) : F (min x a') y * F a b ≤ F (min x a) y * F a' b := by
  rcases le_total x a with hxa | hax
  · rw [min_eq_left hxa, min_eq_left (hxa.trans haa)]
    exact mul_le_mul_of_nonneg_left (hm b haa) (hn _ _)
  · rw [min_eq_right hax]
    rcases le_total x a' with hxa' | hax'
    · rw [min_eq_left hxa']
      have h1 := htp a x y b hax hyb
      have h2 := mul_le_mul_of_nonneg_left (hm b hxa') (hn a y)
      linarith [mul_comm (F x y) (F a b)]
    · rw [min_eq_right hax']
      have h1 := htp a a' y b haa hyb
      linarith [mul_comm (F a' y) (F a b)]

/-- The corner-set inequality for a nonnegative TP2 function that is monotone in each
argument. -/
private theorem tp2_corner {F : I → I → ℝ} (htp : IsTP2 F) (hn : ∀ a b, 0 ≤ F a b)
    (hm₁ : ∀ b, Monotone (fun a => F a b)) (hm₂ : ∀ a, Monotone (F a))
    (u v a b a' b' : I) (haa : a ≤ a') (hbb : b ≤ b') :
    F (min u a') (min v b') * F a b ≤ F (min u a) (min v b) * F a' b' := by
  have s1 := tp2_corner_step htp hn hm₁ u haa (min_le_right v b)
  have s2 := tp2_corner_step (F := fun s t => F t s) htp.swap (fun _ _ => hn _ _) hm₂ v hbb
    (min_le_right u a')
  rcases (hn a' b).eq_or_lt with h0 | hpos
  · have hab : F a b = 0 := le_antisymm (h0 ▸ hm₁ b haa) (hn a b)
    rw [hab, mul_zero]
    exact mul_nonneg (hn _ _) (hn _ _)
  · refine le_of_mul_le_mul_right ?_ hpos
    calc F (min u a') (min v b') * F a b * F a' b
        = F (min u a') (min v b') * F a' b * F a b := by ring
      _ ≤ F (min u a') (min v b) * F a' b' * F a b :=
        mul_le_mul_of_nonneg_right s2 (hn a b)
      _ = F (min u a') (min v b) * F a b * F a' b' := by ring
      _ ≤ F (min u a) (min v b) * F a' b * F a' b' :=
        mul_le_mul_of_nonneg_right s1 (hn a' b')
      _ = F (min u a) (min v b) * F a' b' * F a' b := by ring

/-! ## LCSD -/

/-- LCSD is equivalent to total positivity of the copula CDF (Nelsen, §5.2.3). -/
theorem isLCSD_iff_isTP2CDF (C : Copula 2) : C.IsLCSD ↔ C.IsTP2CDF := by
  constructor
  · intro h a b c d hab hcd
    have := h a d b c b d le_rfl hcd
    simpa only [min_eq_left hab, min_self, min_eq_right hcd] using this
  · intro h u v a b a' b' haa hbb
    refine tp2_corner (F := fun s t => C.cdf ![s, t]) h (fun _ _ => C.cdf_nonneg _)
      (fun t s s' hss => C.monotone_cdf ?_) (fun s t t' htt => C.monotone_cdf ?_)
      u v a b a' b' haa hbb
    · intro i; fin_cases i
      · exact hss
      · exact le_rfl
    · intro i; fin_cases i
      · exact le_rfl
      · exact htt

theorem IsLCSD.isTP2CDF {C : Copula 2} (h : C.IsLCSD) : C.IsTP2CDF :=
  (isLCSD_iff_isTP2CDF C).mp h

theorem IsTP2CDF.isLCSD {C : Copula 2} (h : C.IsTP2CDF) : C.IsLCSD :=
  (isLCSD_iff_isTP2CDF C).mpr h

/-- LCSD is symmetric in the two coordinates. -/
theorem IsLCSD.transpose {C : Copula 2} (h : C.IsLCSD) : C.transpose.IsLCSD :=
  (h.isTP2CDF.reindex_swap).isLCSD

/-- LCSD implies left tail decreasingness of `V` given `U` (Nelsen, §5.2.3). -/
theorem IsLCSD.isLTD {C : Copula 2} (h : C.IsLCSD) : C.IsLTD := h.isTP2CDF.isLTD

/-- LCSD implies left tail decreasingness of `U` given `V` (Nelsen, §5.2.3). -/
theorem IsLCSD.isLTD_transpose {C : Copula 2} (h : C.IsLCSD) : C.transpose.IsLTD :=
  h.isTP2CDF.isLTD_swap

theorem IsLCSD.isPQD {C : Copula 2} (h : C.IsLCSD) : C.IsPQD := h.isLTD.isPQD

/-! ## RCSI -/

/-- The bivariate joint survival function as a CDF value of the survival copula. -/
theorem survival_two_eq_survivalCopula (C : Copula 2) (x y : I) :
    C.survival ![x, y] =
      C.survivalCopula.cdf ![unitInterval.symm x, unitInterval.symm y] := by
  rw [survival_two, cdf_survivalCopula, unitInterval.symm_symm, unitInterval.symm_symm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  ring

private theorem antitone_symm : Antitone (unitInterval.symm) :=
  fun _ _ h => unitInterval.symm_le_symm.mpr h

private theorem symm_max (x y : I) :
    unitInterval.symm (max x y) = min (unitInterval.symm x) (unitInterval.symm y) :=
  antitone_symm.map_max

/-- RCSI of a copula is LCSD of its survival copula. -/
theorem isRCSI_iff_survivalCopula_isLCSD (C : Copula 2) :
    C.IsRCSI ↔ C.survivalCopula.IsLCSD := by
  simp only [IsRCSI, IsLCSD, survival_two_eq_survivalCopula, symm_max]
  constructor
  · intro h u v a b a' b' haa hbb
    have := h (unitInterval.symm u) (unitInterval.symm v) (unitInterval.symm a')
      (unitInterval.symm b') (unitInterval.symm a) (unitInterval.symm b)
      (unitInterval.symm_le_symm.mpr haa) (unitInterval.symm_le_symm.mpr hbb)
    simpa only [unitInterval.symm_symm] using this
  · intro h u v a b a' b' haa hbb
    exact h _ _ _ _ _ _ (unitInterval.symm_le_symm.mpr haa) (unitInterval.symm_le_symm.mpr hbb)

/-- RCSI is equivalent to total positivity of the joint survival function
(Nelsen, §5.2.3). -/
theorem isRCSI_iff_isTP2_survival (C : Copula 2) :
    C.IsRCSI ↔ IsTP2 (fun u v : I => C.survival ![u, v]) := by
  rw [isRCSI_iff_survivalCopula_isLCSD, isLCSD_iff_isTP2CDF]
  simp only [IsTP2CDF, IsTP2, survival_two_eq_survivalCopula]
  constructor
  · intro h a b c d hab hcd
    have := h _ _ _ _ (unitInterval.symm_le_symm.mpr hab) (unitInterval.symm_le_symm.mpr hcd)
    linarith [mul_comm (C.survivalCopula.cdf ![unitInterval.symm a, unitInterval.symm d])
      (C.survivalCopula.cdf ![unitInterval.symm b, unitInterval.symm c])]
  · intro h a b c d hab hcd
    have := h _ _ _ _ (unitInterval.symm_le_symm.mpr hab) (unitInterval.symm_le_symm.mpr hcd)
    simp only [unitInterval.symm_symm] at this
    linarith [mul_comm (C.survivalCopula.cdf ![a, d]) (C.survivalCopula.cdf ![b, c])]

/-- The joint survival function of the transposed copula. -/
theorem survival_transpose_two (C : Copula 2) (x y : I) :
    C.transpose.survival ![x, y] = C.survival ![y, x] := by
  simp only [survival_two, Matrix.cons_val_zero, Matrix.cons_val_one, transpose,
    cdf_reindex_swap]
  ring

/-- RCSI is symmetric in the two coordinates. -/
theorem IsRCSI.transpose {C : Copula 2} (h : C.IsRCSI) : C.transpose.IsRCSI := by
  intro u v a b a' b' haa hbb
  simp only [survival_transpose_two]
  exact h v u b a b' a' hbb haa

/-- RCSI implies right tail increasingness of `V` given `U` (Nelsen, §5.2.3). -/
theorem IsRCSI.isRTI {C : Copula 2} (h : C.IsRCSI) : C.IsRTI := by
  intro a b v hab
  have := h 0 v a 0 b 0 hab le_rfl
  simp only [max_eq_right (unitInterval.nonneg' (t := a)), max_eq_right (unitInterval.nonneg' (t := b)),
    max_eq_left (unitInterval.nonneg' (t := v)),
    survival_two, Matrix.cons_val_zero, Matrix.cons_val_one, Set.Icc.coe_zero,
    C.cdf_eq_zero_of_coord_eq_zero ![a, 0] 1 rfl,
    C.cdf_eq_zero_of_coord_eq_zero ![b, 0] 1 rfl] at this
  nlinarith

/-- RCSI implies right tail increasingness of `U` given `V` (Nelsen, §5.2.3). -/
theorem IsRCSI.isRTI_transpose {C : Copula 2} (h : C.IsRCSI) : C.transpose.IsRTI :=
  h.transpose.isRTI

theorem IsRCSI.isPQD {C : Copula 2} (h : C.IsRCSI) : C.IsPQD := h.isRTI.isPQD

/-! ## Benchmarks -/

theorem isLCSD_independence : (independence 2).IsLCSD := isTP2CDF_independence.isLCSD

theorem isLCSD_comonotonic : (comonotonic 2).IsLCSD := isTP2CDF_comonotonic.isLCSD

theorem isRCSI_independence : (independence 2).IsRCSI := by
  rw [isRCSI_iff_survivalCopula_isLCSD, isRadiallySymmetric_independence]
  exact isLCSD_independence

theorem isRCSI_comonotonic : (comonotonic 2).IsRCSI := by
  rw [isRCSI_iff_survivalCopula_isLCSD, isRadiallySymmetric_comonotonic]
  exact isLCSD_comonotonic

theorem not_isLCSD_countermonotonic : ¬ countermonotonic.IsLCSD :=
  fun h => not_isPQD_countermonotonic h.isPQD

theorem not_isRCSI_countermonotonic : ¬ countermonotonic.IsRCSI :=
  fun h => not_isPQD_countermonotonic h.isPQD

end ProbabilityTheory.Copula
