/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Diagonal
import Copula.Symmetry
import Copula.Order.Orthant

/-! # Lower and upper tail dependence

Both limits are parametrized by a tail probability `t → 0+`. Thus the upper
threshold is `1-t`. Existence is an explicit predicate, never assumed.
See Nelsen, second edition, §5.4.
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- Lower tail conditional probability at a positive tail width. -/
noncomputable def lowerTailRatio (C : Copula 2) (t : I) : ℝ := C.diagonal t / (t : ℝ)

/-- Upper tail conditional probability at threshold `1-t`. -/
noncomputable def upperTailRatio (C : Copula 2) (t : I) : ℝ := C.survivalCopula.lowerTailRatio t

/-- Existence and value of the lower tail-dependence limit. -/
def HasLowerTailDependence (C : Copula 2) (l : ℝ) : Prop :=
  Tendsto C.lowerTailRatio (𝓝[>] (0 : I)) (𝓝 l)

/-- Existence and value of the upper tail-dependence limit. -/
def HasUpperTailDependence (C : Copula 2) (l : ℝ) : Prop :=
  Tendsto C.upperTailRatio (𝓝[>] (0 : I)) (𝓝 l)

theorem tailFilter_neBot : NeBot (𝓝[>] (0 : I)) :=
  nhdsGT_neBot_of_exists_gt ⟨1, by norm_num⟩

theorem lowerTailRatio_mem_Icc (C : Copula 2) (t : I) : C.lowerTailRatio t ∈ Icc 0 1 :=
  ⟨div_nonneg (C.diagonal_nonneg t) t.property.1,
    div_le_one_of_le₀ (C.diagonal_le t) t.property.1⟩

theorem upperTailRatio_mem_Icc (C : Copula 2) (t : I) : C.upperTailRatio t ∈ Icc 0 1 :=
  C.survivalCopula.lowerTailRatio_mem_Icc t

theorem upperTailRatio_eq (C : Copula 2) (t : I) :
    C.upperTailRatio t = (2 * (t : ℝ) - 1 + C.diagonal (unitInterval.symm t)) / (t : ℝ) := by
  simp only [upperTailRatio, lowerTailRatio, diagonal, cdf_survivalCopula, two_mul]

theorem upperTailRatio_eq_survival (C : Copula 2) (t : I) :
    C.upperTailRatio t = C.survival ![unitInterval.symm t, unitInterval.symm t] / (t : ℝ) := by
  rw [C.upperTailRatio_eq, C.survival_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq, diagonal]
  ring

private theorem tendsto_symm_zero_one :
    Tendsto unitInterval.symm (𝓝[>] (0 : I)) (𝓝[<] (1 : I)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · simpa using (unitInterval.continuous_symm.tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
    simpa using unitInterval.strictAnti_symm ht

private theorem tendsto_symm_one_zero :
    Tendsto unitInterval.symm (𝓝[<] (1 : I)) (𝓝[>] (0 : I)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · simpa using (unitInterval.continuous_symm.tendsto (1 : I)).mono_left nhdsWithin_le_nhds
  · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[<] (1 : I), t < 1)] with t ht
    simpa using unitInterval.strictAnti_symm ht

/-- Equivalence with the usual formula parametrized by a threshold tending to one. -/
theorem hasUpperTailDependence_iff_tendsto_one (C : Copula 2) (l : ℝ) :
    C.HasUpperTailDependence l ↔
      Tendsto (fun t : I => (1 - 2 * (t : ℝ) + C.diagonal t) / (1 - (t : ℝ)))
        (𝓝[<] (1 : I)) (𝓝 l) := by
  have he (t : I) : C.upperTailRatio (unitInterval.symm t) =
      (1 - 2 * (t : ℝ) + C.diagonal t) / (1 - (t : ℝ)) := by
    rw [C.upperTailRatio_eq, unitInterval.symm_symm, unitInterval.coe_symm_eq]
    ring
  constructor
  · intro h
    simpa only [Function.comp_def, he] using h.comp tendsto_symm_one_zero
  · intro h
    have hh := h.comp tendsto_symm_zero_one
    change Tendsto C.upperTailRatio (𝓝[>] (0 : I)) (𝓝 l)
    simpa only [Function.comp_def, ← he, unitInterval.symm_symm] using hh

theorem HasLowerTailDependence.mem_Icc {C : Copula 2} {l : ℝ} (h : C.HasLowerTailDependence l) :
    l ∈ Icc 0 1 := by
  have := tailFilter_neBot
  exact isClosed_Icc.mem_of_tendsto h (Eventually.of_forall C.lowerTailRatio_mem_Icc)

theorem HasUpperTailDependence.mem_Icc {C : Copula 2} {l : ℝ} (h : C.HasUpperTailDependence l) :
    l ∈ Icc 0 1 := HasLowerTailDependence.mem_Icc (C := C.survivalCopula) h

theorem HasLowerTailDependence.unique {C : Copula 2} {a b : ℝ}
    (ha : C.HasLowerTailDependence a) (hb : C.HasLowerTailDependence b) : a = b := by
  have := tailFilter_neBot
  exact tendsto_nhds_unique ha hb

theorem HasUpperTailDependence.unique {C : Copula 2} {a b : ℝ}
    (ha : C.HasUpperTailDependence a) (hb : C.HasUpperTailDependence b) : a = b :=
  HasLowerTailDependence.unique (C := C.survivalCopula) ha hb

theorem hasUpperTailDependence_iff_survivalCopula (C : Copula 2) (l : ℝ) :
    C.HasUpperTailDependence l ↔ C.survivalCopula.HasLowerTailDependence l := Iff.rfl

theorem hasLowerTailDependence_iff_survivalCopula (C : Copula 2) (l : ℝ) :
    C.HasLowerTailDependence l ↔ C.survivalCopula.HasUpperTailDependence l := by
  rw [hasUpperTailDependence_iff_survivalCopula, survivalCopula_survivalCopula]

theorem hasLowerTailDependence_transpose_iff (C : Copula 2) (l : ℝ) :
    C.transpose.HasLowerTailDependence l ↔ C.HasLowerTailDependence l := by
  have he : C.transpose.lowerTailRatio = C.lowerTailRatio := by
    funext t
    simp [lowerTailRatio, diagonal]
  simp only [HasLowerTailDependence, he]

theorem hasUpperTailDependence_transpose_iff (C : Copula 2) (l : ℝ) :
    C.transpose.HasUpperTailDependence l ↔ C.HasUpperTailDependence l := by
  rw [hasUpperTailDependence_iff_survivalCopula, ← transpose_survivalCopula,
    hasLowerTailDependence_transpose_iff, hasUpperTailDependence_iff_survivalCopula]

theorem IsRadiallySymmetric.hasUpperTailDependence_iff {C : Copula 2} (h : C.IsRadiallySymmetric)
    (l : ℝ) : C.HasUpperTailDependence l ↔ C.HasLowerTailDependence l := by
  rw [hasUpperTailDependence_iff_survivalCopula, h]

theorem LowerOrthantLE.lowerTailDependence_le {C D : Copula 2} (h : C.LowerOrthantLE D)
    {a b : ℝ} (ha : C.HasLowerTailDependence a) (hb : D.HasLowerTailDependence b) : a ≤ b := by
  have := tailFilter_neBot
  apply le_of_tendsto_of_tendsto ha hb
  exact Eventually.of_forall fun t => div_le_div_of_nonneg_right (h ![t, t]) t.property.1

theorem LowerOrthantLE.upperTailDependence_le {C D : Copula 2} (h : C.LowerOrthantLE D)
    {a b : ℝ} (ha : C.HasUpperTailDependence a) (hb : D.HasUpperTailDependence b) : a ≤ b := by
  have hr : C.survivalCopula.LowerOrthantLE D.survivalCopula :=
    (upperOrthantLE_iff_reflect C D).1 ((upperOrthantLE_iff_lowerOrthantLE C D).2 h)
  exact hr.lowerTailDependence_le ha hb

theorem HasLowerTailDependence.mix {C D : Copula 2} {a b : ℝ}
    (hC : C.HasLowerTailDependence a) (hD : D.HasLowerTailDependence b) (w : I) :
    (C.mix D w).HasLowerTailDependence ((w : ℝ) * a + (1 - (w : ℝ)) * b) := by
  have he : (C.mix D w).lowerTailRatio = fun t =>
      (w : ℝ) * C.lowerTailRatio t + (1 - (w : ℝ)) * D.lowerTailRatio t := by
    funext t
    simp only [lowerTailRatio, diagonal, cdf_mix]
    ring
  unfold HasLowerTailDependence
  rw [he]
  exact (hC.const_mul _).add (hD.const_mul _)

theorem HasUpperTailDependence.mix {C D : Copula 2} {a b : ℝ}
    (hC : C.HasUpperTailDependence a) (hD : D.HasUpperTailDependence b) (w : I) :
    (C.mix D w).HasUpperTailDependence ((w : ℝ) * a + (1 - (w : ℝ)) * b) := by
  rw [hasUpperTailDependence_iff_survivalCopula, survivalCopula_mix]
  exact HasLowerTailDependence.mix hC hD w

end ProbabilityTheory.Copula
