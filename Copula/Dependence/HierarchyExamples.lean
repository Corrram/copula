/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.ProductPerturbation
import Copula.Dependence.ConditionalMonotonicity

/-!
# Strictness of the positive dependence hierarchy

Product perturbations `C(u,v) = uv + φ(u) ψ(v)` of independence
(`Copula.Families.ProductPerturbation`) with piecewise linear profiles separate the levels of
the positive dependence hierarchy of Nelsen, *An Introduction to Copulas*, 2nd ed., §5.2.
Writing `D = C - Π = φ ⊗ ψ` with `ψ ≥ 0`:

* LTD holds iff `φ(u)/u` is nonincreasing, RTI iff `φ(u)/(1-u)` is nondecreasing, SI iff `φ` is
  concave, and PQD iff `φ ≥ 0` (sufficient directions proved here);
* the tent `τ(t) = min(t, 1-t)`, the bumps `max(0, min(t - 1/2, 1 - t))` and
  `max(0, min(t, 1/2 - t))` and the two-peak profile
  `max(min(t, (1-t)/3), min(t/3, 1-t))` give:

| copula | PQD | LTD | RTI | SI | SI of transpose |
| --- | --- | --- | --- | --- | --- |
| `rightBumpCopula` | yes | no | yes | no | |
| `leftBumpCopula` | yes | yes | no | no | |
| `twoPeakCopula` | yes | yes | yes | no | |
| `tentTwoPeakCopula` | yes | yes | yes | yes | no |

Hence PQD ⇏ LTD, PQD ⇏ RTI, RTI ⇏ LTD, LTD ⇏ RTI, LTD ∧ RTI ⇏ SI (the hypothesis of the
Capéraà–Genest inequality is strictly weaker than SI), and SI(V|U) ⇏ SI(U|V).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace HierarchyExamples

/-! ## Profile conditions -/

/-- Profile condition for LTD: `φ(u)/u` is nonincreasing (cross-multiplied). -/
def LTDProfile (f : I → ℝ) : Prop := ∀ a b : I, a ≤ b → (a : ℝ) * f b ≤ (b : ℝ) * f a

/-- Profile condition for RTI: `φ(u)/(1-u)` is nondecreasing (cross-multiplied). -/
def RTIProfile (f : I → ℝ) : Prop :=
  ∀ a b : I, a ≤ b → (1 - (b : ℝ)) * f a ≤ (1 - (a : ℝ)) * f b

/-- Profile condition for SI: concavity in chord form. -/
def ChordConcave (f : I → ℝ) : Prop :=
  ∀ a b c : I, a ≤ b → b ≤ c →
    ((b : ℝ) - a) * f c + ((c : ℝ) - b) * f a ≤ ((c : ℝ) - a) * f b

theorem LTDProfile.min {f g : I → ℝ} (hf : LTDProfile f) (hg : LTDProfile g) :
    LTDProfile (fun t => min (f t) (g t)) := by
  intro a b hab
  have ha : (0 : ℝ) ≤ a := a.2.1
  have hb : (0 : ℝ) ≤ b := b.2.1
  rw [mul_min_of_nonneg _ _ ha, mul_min_of_nonneg _ _ hb]
  exact min_le_min (hf a b hab) (hg a b hab)

theorem LTDProfile.max {f g : I → ℝ} (hf : LTDProfile f) (hg : LTDProfile g) :
    LTDProfile (fun t => max (f t) (g t)) := by
  intro a b hab
  have ha : (0 : ℝ) ≤ a := a.2.1
  have hb : (0 : ℝ) ≤ b := b.2.1
  rw [mul_max_of_nonneg _ _ ha, mul_max_of_nonneg _ _ hb]
  exact max_le_max (hf a b hab) (hg a b hab)

theorem ltdProfile_affine {f : I → ℝ} (m k : ℝ) (hk : 0 ≤ k) (hf : ∀ t, f t = m * t + k) :
    LTDProfile f := by
  intro a b hab
  rw [hf, hf]
  have : (a : ℝ) ≤ b := hab
  nlinarith

theorem RTIProfile.min {f g : I → ℝ} (hf : RTIProfile f) (hg : RTIProfile g) :
    RTIProfile (fun t => min (f t) (g t)) := by
  intro a b hab
  have ha : (0 : ℝ) ≤ 1 - a := sub_nonneg.mpr a.2.2
  have hb : (0 : ℝ) ≤ 1 - b := sub_nonneg.mpr b.2.2
  rw [mul_min_of_nonneg _ _ ha, mul_min_of_nonneg _ _ hb]
  exact min_le_min (hf a b hab) (hg a b hab)

theorem RTIProfile.max {f g : I → ℝ} (hf : RTIProfile f) (hg : RTIProfile g) :
    RTIProfile (fun t => max (f t) (g t)) := by
  intro a b hab
  have ha : (0 : ℝ) ≤ 1 - a := sub_nonneg.mpr a.2.2
  have hb : (0 : ℝ) ≤ 1 - b := sub_nonneg.mpr b.2.2
  rw [mul_max_of_nonneg _ _ ha, mul_max_of_nonneg _ _ hb]
  exact max_le_max (hf a b hab) (hg a b hab)

theorem rtiProfile_affine {f : I → ℝ} (m k : ℝ) (hk : 0 ≤ m + k) (hf : ∀ t, f t = m * t + k) :
    RTIProfile f := by
  intro a b hab
  rw [hf, hf]
  have : (a : ℝ) ≤ b := hab
  nlinarith

theorem ChordConcave.min {f g : I → ℝ} (hf : ChordConcave f) (hg : ChordConcave g) :
    ChordConcave (fun t => min (f t) (g t)) := by
  intro a b c hab hbc
  have h₁ : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr hab
  have h₂ : (0 : ℝ) ≤ (c : ℝ) - b := sub_nonneg.mpr hbc
  have h₃ : (0 : ℝ) ≤ (c : ℝ) - a := by linarith
  rw [mul_min_of_nonneg _ _ h₃]
  apply le_min
  · nlinarith [hf a b c hab hbc, mul_le_mul_of_nonneg_left (min_le_left (f c) (g c)) h₁,
      mul_le_mul_of_nonneg_left (min_le_left (f a) (g a)) h₂]
  · nlinarith [hg a b c hab hbc, mul_le_mul_of_nonneg_left (min_le_right (f c) (g c)) h₁,
      mul_le_mul_of_nonneg_left (min_le_right (f a) (g a)) h₂]

theorem chordConcave_affine {f : I → ℝ} (m k : ℝ) (hf : ∀ t, f t = m * t + k) :
    ChordConcave f := by
  intro a b c _ _
  rw [hf, hf, hf]
  apply le_of_eq
  ring

/-! ## Dependence properties of product perturbations -/

variable {φ ψ : BoundaryProfile} {h : φ.lip * ψ.lip ≤ 1}

theorem productPerturbation_isPQD (hφ : ∀ t, 0 ≤ φ t) (hψ : ∀ t, 0 ≤ ψ t) :
    (productPerturbation φ ψ h).IsPQD := by
  intro u v
  rw [cdf_productPerturbation]
  nlinarith [mul_nonneg (hφ u) (hψ v)]

theorem productPerturbation_isLTD (hψ : ∀ t, 0 ≤ ψ t) (hφ : LTDProfile φ) :
    (productPerturbation φ ψ h).IsLTD := by
  intro a b v hab
  rw [cdf_productPerturbation, cdf_productPerturbation]
  nlinarith [mul_le_mul_of_nonneg_right (hφ a b hab) (hψ v)]

theorem productPerturbation_isRTI (hψ : ∀ t, 0 ≤ ψ t) (hφ : RTIProfile φ) :
    (productPerturbation φ ψ h).IsRTI := by
  intro a b v hab
  rw [cdf_productPerturbation, cdf_productPerturbation]
  nlinarith [mul_le_mul_of_nonneg_right (hφ a b hab) (hψ v)]

theorem productPerturbation_isSI (hψ : ∀ t, 0 ≤ ψ t) (hφ : ChordConcave φ) :
    (productPerturbation φ ψ h).IsSI := by
  intro a b c v hab hbc
  rw [cdf_productPerturbation, cdf_productPerturbation, cdf_productPerturbation]
  nlinarith [mul_le_mul_of_nonneg_right (hφ a b c hab hbc) (hψ v)]

/-- The transpose of `Π + φ ⊗ ψ` is `Π + ψ ⊗ φ`. -/
theorem productPerturbation_transpose (h' : ψ.lip * φ.lip ≤ 1) :
    (productPerturbation φ ψ h).transpose = productPerturbation ψ φ h' := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_productPerturbation, cdf_productPerturbation]
  ring

/-! ## Piecewise linear profiles -/

private theorem piece_lip {A B s t : ℝ} (m : ℝ) (hm : |m| ≤ 1) (hAB : A - B = m * (s - t)) :
    |A - B| ≤ |s - t| := by
  rw [hAB, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hm

/-- The tent profile `min(t, 1 - t)`. -/
noncomputable def tent : BoundaryProfile where
  toFun t := min (t : ℝ) (1 - t)
  lip := 1
  lip_nonneg := zero_le_one
  zero := by simp
  one := by simp
  lipschitz s t := by
    rw [one_mul]
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (piece_lip 1 (by norm_num) (by ring))
      (piece_lip (-1) (by norm_num) (by ring)))

/-- A bump supported on `[1/2, 1]`: `max(0, min(t - 1/2, 1 - t))`. -/
noncomputable def rightBump : BoundaryProfile where
  toFun t := max 0 (min ((t : ℝ) - 1 / 2) (1 - t))
  lip := 1
  lip_nonneg := zero_le_one
  zero := by norm_num
  one := by norm_num
  lipschitz s t := by
    rw [one_mul]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (piece_lip 1 (by norm_num) (by ring))
      (piece_lip (-1) (by norm_num) (by ring)))

/-- A bump supported on `[0, 1/2]`: `max(0, min(t, 1/2 - t))`. -/
noncomputable def leftBump : BoundaryProfile where
  toFun t := max 0 (min (t : ℝ) (1 / 2 - t))
  lip := 1
  lip_nonneg := zero_le_one
  zero := by norm_num
  one := by norm_num
  lipschitz s t := by
    rw [one_mul]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (piece_lip 1 (by norm_num) (by ring))
      (piece_lip (-1) (by norm_num) (by ring)))

/-- A non-concave profile with two peaks: `max(min(t, (1-t)/3), min(t/3, 1-t))`. -/
noncomputable def twoPeak : BoundaryProfile where
  toFun t := max (min (t : ℝ) ((1 - t) / 3)) (min ((t : ℝ) / 3) (1 - t))
  lip := 1
  lip_nonneg := zero_le_one
  zero := by norm_num
  one := by norm_num
  lipschitz s t := by
    rw [one_mul]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (piece_lip 1 (by norm_num) (by ring))
        (piece_lip (-1 / 3) (by norm_num [abs_div]) (by ring)))
    · exact (abs_min_sub_min_le_max _ _ _ _).trans
        (max_le (piece_lip (1 / 3) (by norm_num [abs_div]) (by ring))
          (piece_lip (-1) (by norm_num) (by ring)))

private theorem lip_mul : (1 : ℝ) * 1 ≤ 1 := by norm_num

@[simp] theorem tent_apply (t : I) : tent t = min (t : ℝ) (1 - t) := rfl

@[simp] theorem rightBump_apply (t : I) : rightBump t = max 0 (min ((t : ℝ) - 1 / 2) (1 - t)) :=
  rfl

@[simp] theorem leftBump_apply (t : I) : leftBump t = max 0 (min (t : ℝ) (1 / 2 - t)) := rfl

@[simp] theorem twoPeak_apply (t : I) :
    twoPeak t = max (min (t : ℝ) ((1 - t) / 3)) (min ((t : ℝ) / 3) (1 - t)) := rfl

theorem tent_nonneg (t : I) : 0 ≤ tent t :=
  le_min t.2.1 (sub_nonneg.mpr t.2.2)

theorem rightBump_nonneg (t : I) : 0 ≤ rightBump t := le_max_left _ _

theorem leftBump_nonneg (t : I) : 0 ≤ leftBump t := le_max_left _ _

theorem twoPeak_nonneg (t : I) : 0 ≤ twoPeak t :=
  le_max_of_le_left (le_min t.2.1 (by linarith [t.2.2]))

theorem tent_ltd : LTDProfile tent :=
  (ltdProfile_affine (f := fun t : I => (t : ℝ)) 1 0 le_rfl fun t => by ring).min
    (ltdProfile_affine (f := fun t : I => 1 - (t : ℝ)) (-1) 1 zero_le_one fun t => by ring)

theorem tent_rti : RTIProfile tent :=
  (rtiProfile_affine (f := fun t : I => (t : ℝ)) 1 0 (by norm_num) fun t => by ring).min
    (rtiProfile_affine (f := fun t : I => 1 - (t : ℝ)) (-1) 1 (by norm_num) fun t => by ring)

theorem tent_concave : ChordConcave tent :=
  (chordConcave_affine (f := fun t : I => (t : ℝ)) 1 0 fun t => by ring).min
    (chordConcave_affine (f := fun t : I => 1 - (t : ℝ)) (-1) 1 fun t => by ring)

theorem rightBump_rti : RTIProfile rightBump :=
  (rtiProfile_affine (f := fun _ : I => (0 : ℝ)) 0 0 (by norm_num) fun t => by ring).max
    ((rtiProfile_affine (f := fun t : I => (t : ℝ) - 1 / 2) 1 (-1 / 2) (by norm_num)
      fun t => by ring).min
      (rtiProfile_affine (f := fun t : I => 1 - (t : ℝ)) (-1) 1 (by norm_num) fun t => by ring))

theorem leftBump_ltd : LTDProfile leftBump :=
  (ltdProfile_affine (f := fun _ : I => (0 : ℝ)) 0 0 le_rfl fun t => by ring).max
    ((ltdProfile_affine (f := fun t : I => (t : ℝ)) 1 0 le_rfl fun t => by ring).min
      (ltdProfile_affine (f := fun t : I => 1 / 2 - (t : ℝ)) (-1) (1 / 2) (by norm_num)
        fun t => by ring))

theorem twoPeak_ltd : LTDProfile twoPeak :=
  ((ltdProfile_affine (f := fun t : I => (t : ℝ)) 1 0 le_rfl fun t => by ring).min
    (ltdProfile_affine (f := fun t : I => (1 - (t : ℝ)) / 3) (-1 / 3) (1 / 3) (by norm_num)
      fun t => by ring)).max
  ((ltdProfile_affine (f := fun t : I => (t : ℝ) / 3) (1 / 3) 0 le_rfl fun t => by ring).min
    (ltdProfile_affine (f := fun t : I => 1 - (t : ℝ)) (-1) 1 zero_le_one fun t => by ring))

theorem twoPeak_rti : RTIProfile twoPeak :=
  ((rtiProfile_affine (f := fun t : I => (t : ℝ)) 1 0 (by norm_num) fun t => by ring).min
    (rtiProfile_affine (f := fun t : I => (1 - (t : ℝ)) / 3) (-1 / 3) (1 / 3) (by norm_num)
      fun t => by ring)).max
  ((rtiProfile_affine (f := fun t : I => (t : ℝ) / 3) (1 / 3) 0 (by norm_num) fun t => by ring).min
    (rtiProfile_affine (f := fun t : I => 1 - (t : ℝ)) (-1) 1 (by norm_num) fun t => by ring))

/-! ## The four copulas -/

/-- `Π + rightBump ⊗ tent`: RTI and PQD but not LTD. -/
noncomputable def rightBumpCopula : Copula 2 := productPerturbation rightBump tent lip_mul

/-- `Π + leftBump ⊗ tent`: LTD and PQD but not RTI. -/
noncomputable def leftBumpCopula : Copula 2 := productPerturbation leftBump tent lip_mul

/-- `Π + twoPeak ⊗ tent`: LTD and RTI but not SI. -/
noncomputable def twoPeakCopula : Copula 2 := productPerturbation twoPeak tent lip_mul

/-- `Π + tent ⊗ twoPeak`: SI, but its transpose is not SI. -/
noncomputable def tentTwoPeakCopula : Copula 2 := productPerturbation tent twoPeak lip_mul

private noncomputable def pt (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : I := ⟨x, h0, h1⟩

@[simp] private theorem coe_pt (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : ((pt x h0 h1 : I) : ℝ) = x :=
  rfl

theorem isRTI_rightBumpCopula : rightBumpCopula.IsRTI :=
  productPerturbation_isRTI tent_nonneg rightBump_rti

theorem isPQD_rightBumpCopula : rightBumpCopula.IsPQD :=
  isRTI_rightBumpCopula.isPQD

theorem not_isLTD_rightBumpCopula : ¬ rightBumpCopula.IsLTD := by
  intro h
  have := h (pt (1 / 2) (by norm_num) (by norm_num)) (pt (3 / 4) (by norm_num) (by norm_num))
    (pt (1 / 2) (by norm_num) (by norm_num)) (Subtype.mk_le_mk.mpr (by norm_num))
  simp only [show ∀ u v : I, rightBumpCopula.cdf ![u, v] = (u : ℝ) * v + rightBump u * tent v from
    fun u v => cdf_productPerturbation _ _ _ u v, rightBump_apply, tent_apply, coe_pt] at this
  change (1 / 2 : ℝ) * (3 / 4 * (1 / 2) + max 0 (min (3 / 4 - 1 / 2) (1 - 3 / 4)) *
      min (1 / 2) (1 - 1 / 2)) ≤
    3 / 4 * (1 / 2 * (1 / 2) + max 0 (min (1 / 2 - 1 / 2) (1 - 1 / 2)) *
      min (1 / 2) (1 - 1 / 2)) at this
  norm_num at this

theorem not_isSI_rightBumpCopula : ¬ rightBumpCopula.IsSI :=
  fun h => not_isLTD_rightBumpCopula h.isLTD

theorem isLTD_leftBumpCopula : leftBumpCopula.IsLTD :=
  productPerturbation_isLTD tent_nonneg leftBump_ltd

theorem isPQD_leftBumpCopula : leftBumpCopula.IsPQD :=
  isLTD_leftBumpCopula.isPQD

theorem not_isRTI_leftBumpCopula : ¬ leftBumpCopula.IsRTI := by
  intro h
  have := h (pt (1 / 4) (by norm_num) (by norm_num)) (pt (1 / 2) (by norm_num) (by norm_num))
    (pt (1 / 2) (by norm_num) (by norm_num)) (Subtype.mk_le_mk.mpr (by norm_num))
  simp only [show ∀ u v : I, leftBumpCopula.cdf ![u, v] = (u : ℝ) * v + leftBump u * tent v from
    fun u v => cdf_productPerturbation _ _ _ u v, leftBump_apply, tent_apply, coe_pt] at this
  change (1 - 1 / 4 : ℝ) * (1 / 2 - (1 / 2 * (1 / 2) + max 0 (min (1 / 2) (1 / 2 - 1 / 2)) *
      min (1 / 2) (1 - 1 / 2))) ≤
    (1 - 1 / 2) * (1 / 2 - (1 / 4 * (1 / 2) + max 0 (min (1 / 4) (1 / 2 - 1 / 4)) *
      min (1 / 2) (1 - 1 / 2))) at this
  norm_num at this

theorem not_isSI_leftBumpCopula : ¬ leftBumpCopula.IsSI :=
  fun h => not_isRTI_leftBumpCopula h.isRTI

theorem isLTD_twoPeakCopula : twoPeakCopula.IsLTD :=
  productPerturbation_isLTD tent_nonneg twoPeak_ltd

theorem isRTI_twoPeakCopula : twoPeakCopula.IsRTI :=
  productPerturbation_isRTI tent_nonneg twoPeak_rti

/-- LTD and RTI together do not imply SI. -/
theorem not_isSI_twoPeakCopula : ¬ twoPeakCopula.IsSI := by
  intro h
  have := h (pt (1 / 4) (by norm_num) (by norm_num)) (pt (1 / 2) (by norm_num) (by norm_num))
    (pt (3 / 4) (by norm_num) (by norm_num)) (pt (1 / 2) (by norm_num) (by norm_num))
    (Subtype.mk_le_mk.mpr (by norm_num)) (Subtype.mk_le_mk.mpr (by norm_num))
  simp only [show ∀ u v : I, twoPeakCopula.cdf ![u, v] = (u : ℝ) * v + twoPeak u * tent v from
    fun u v => cdf_productPerturbation _ _ _ u v, twoPeak_apply, tent_apply, coe_pt] at this
  change ((1 / 2 : ℝ) - 1 / 4) * (3 / 4 * (1 / 2) +
      max (min (3 / 4) ((1 - 3 / 4) / 3)) (min (3 / 4 / 3) (1 - 3 / 4)) *
        min (1 / 2) (1 - 1 / 2)) +
    (3 / 4 - 1 / 2) * (1 / 4 * (1 / 2) +
      max (min (1 / 4) ((1 - 1 / 4) / 3)) (min (1 / 4 / 3) (1 - 1 / 4)) *
        min (1 / 2) (1 - 1 / 2)) ≤
    (3 / 4 - 1 / 4) * (1 / 2 * (1 / 2) +
      max (min (1 / 2) ((1 - 1 / 2) / 3)) (min (1 / 2 / 3) (1 - 1 / 2)) *
        min (1 / 2) (1 - 1 / 2)) at this
  norm_num at this

theorem isSI_tentTwoPeakCopula : tentTwoPeakCopula.IsSI :=
  productPerturbation_isSI twoPeak_nonneg tent_concave

theorem transpose_tentTwoPeakCopula : tentTwoPeakCopula.transpose = twoPeakCopula :=
  productPerturbation_transpose lip_mul

/-- Stochastic increasingness of `V` in `U` does not imply that of `U` in `V`. -/
theorem not_isSI_transpose_tentTwoPeakCopula : ¬ tentTwoPeakCopula.transpose.IsSI := by
  rw [transpose_tentTwoPeakCopula]
  exact not_isSI_twoPeakCopula

theorem not_isCI_tentTwoPeakCopula : ¬ tentTwoPeakCopula.IsCI :=
  fun h => not_isSI_transpose_tentTwoPeakCopula h.2

end HierarchyExamples

end ProbabilityTheory.Copula
