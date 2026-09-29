/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Sklar
import Copula.Reflection.Bivariate
import Mathlib.MeasureTheory.Measure.Interval

/-!
# Invariance of the copula under monotone transformations

Nelsen, *An Introduction to Copulas*, second edition, Theorems 2.4.3 and 2.4.4.

Let `μ` be a law on `Fin d → ℝ` with continuous marginal CDFs and let each coordinate be
transformed by a strictly monotone function `f i`. If `s` is the set of coordinates with
strictly decreasing `f i`, then the transformed law again has continuous marginal CDFs and its
copula is the copula of `μ` reflected in the coordinates of `s`
(`ofContinuousMarginals_map_coordMap`).

For `d = 2` this gives the classical statements: two increasing transformations leave the
copula unchanged, one decreasing transformation reflects the corresponding coordinate, and two
decreasing transformations produce the survival copula.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Apply the function `f i` to the `i`-th coordinate of a real vector. -/
def coordMap (f : Fin d → ℝ → ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => f i (x i)

@[simp]
theorem coordMap_apply (f : Fin d → ℝ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    coordMap f x i = f i (x i) := rfl

/-- Coordinatewise application of measurable maps is measurable. -/
theorem measurable_coordMap {f : Fin d → ℝ → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (coordMap f) :=
  Measurable.of_eval fun i => (hf i).comp (measurable_pi_apply i)

/-- Strictly monotone functions, of either direction, are measurable. -/
theorem measurable_fn_of_strict {s : Finset (Fin d)} {f : Fin d → ℝ → ℝ}
    (hinc : ∀ i, i ∉ s → StrictMono (f i)) (hdec : ∀ i, i ∈ s → StrictAnti (f i)) (i : Fin d) :
    Measurable (f i) := by
  by_cases hi : i ∈ s
  · exact (hdec i hi).antitone.measurable
  · exact (hinc i hi).monotone.measurable

/-- A real probability measure with continuous CDF has no atoms. -/
theorem measure_singleton_eq_zero_of_continuous_cdf (m : Measure ℝ) [IsProbabilityMeasure m]
    (hc : Continuous (ProbabilityTheory.cdf m)) (x : ℝ) : m {x} = 0 := by
  have h := (ProbabilityTheory.cdf m).measure_singleton x
  have hl : Function.leftLim (ProbabilityTheory.cdf m) x = ProbabilityTheory.cdf m x :=
    hc.continuousWithinAt.leftLim_eq
  rw [ProbabilityTheory.measure_cdf, hl, sub_self, ENNReal.ofReal_zero] at h
  exact h

/-- For an atomless probability measure, `m [x, ∞) = 1 - m (-∞, x]`. -/
theorem real_Ici_eq_one_sub (m : Measure ℝ) [IsProbabilityMeasure m] {x : ℝ} (h : m {x} = 0) :
    m.real (Ici x) = 1 - m.real (Iic x) := by
  rw [← measureReal_congr (Ioi_ae_eq_Ici' h), ← compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ]

/-- The marginals of a coordinatewise transformed law are the transformed marginals. -/
theorem marginal_map_coordMap (μ : ProbabilityMeasure (Fin d → ℝ)) {f : Fin d → ℝ → ℝ}
    (hf : ∀ i, Measurable (f i)) (i : Fin d) :
    marginal (μ.map (coordMap f)) i = (marginal μ i).map (f i) := by
  have h1 := Measure.map_map (μ := μ.toMeasure) (measurable_pi_apply i) (measurable_coordMap hf)
  have h2 := Measure.map_map (μ := μ.toMeasure) (hf i) (measurable_pi_apply i)
  exact h1.trans h2.symm

theorem cdf_marginal_map_coordMap_of_strictMono (μ : ProbabilityMeasure (Fin d → ℝ))
    {f : Fin d → ℝ → ℝ} (hf : ∀ i, Measurable (f i)) {i : Fin d} (hi : StrictMono (f i))
    (x : ℝ) : ProbabilityTheory.cdf (marginal (μ.map (coordMap f)) i) (f i x) =
      ProbabilityTheory.cdf (marginal μ i) x := by
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, marginal_map_coordMap μ hf i,
    map_measureReal_apply (hf i) measurableSet_Iic]
  have he : f i ⁻¹' Iic (f i x) = Iic x := by
    ext y
    simp only [mem_preimage, mem_Iic]
    exact hi.le_iff_le
  rw [he]

theorem cdf_marginal_map_coordMap_of_strictAnti (μ : ProbabilityMeasure (Fin d → ℝ))
    {f : Fin d → ℝ → ℝ} (hf : ∀ i, Measurable (f i)) {i : Fin d} (hi : StrictAnti (f i))
    (hc : Continuous (ProbabilityTheory.cdf (marginal μ i))) (x : ℝ) :
    ProbabilityTheory.cdf (marginal (μ.map (coordMap f)) i) (f i x) =
      1 - ProbabilityTheory.cdf (marginal μ i) x := by
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, marginal_map_coordMap μ hf i,
    map_measureReal_apply (hf i) measurableSet_Iic]
  have he : f i ⁻¹' Iic (f i x) = Ici x := by
    ext y
    simp only [mem_preimage, mem_Iic]
    exact hi.le_iff_ge
  rw [he]
  exact real_Ici_eq_one_sub _ (measure_singleton_eq_zero_of_continuous_cdf _ hc x)

/-- Transforming every coordinate by a strictly monotone function keeps the marginal CDFs
continuous, because an injective map sends an atomless law to an atomless law. -/
theorem continuous_cdf_marginal_map_coordMap (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : Fin d → ℝ → ℝ}
    {s : Finset (Fin d)} (hinc : ∀ i, i ∉ s → StrictMono (f i))
    (hdec : ∀ i, i ∈ s → StrictAnti (f i)) (i : Fin d) :
    Continuous (ProbabilityTheory.cdf (marginal (μ.map (coordMap f)) i)) := by
  have hf := measurable_fn_of_strict hinc hdec
  have hinj : Function.Injective (f i) := by
    by_cases hi : i ∈ s
    · exact (hdec i hi).injective
    · exact (hinc i hi).injective
  have hsing : ∀ x, marginal μ i {x} = 0 :=
    measure_singleton_eq_zero_of_continuous_cdf _ (hc i)
  have : NullSingletonClass (marginal (μ.map (coordMap f)) i) := by
    refine ⟨fun y => ?_⟩
    rw [marginal_map_coordMap μ hf i, Measure.map_apply (hf i) (measurableSet_singleton y)]
    by_cases hy : ∃ x, f i x = y
    · obtain ⟨x, hx⟩ := hy
      refine measure_mono_null (fun z hz => ?_) (hsing x)
      have hz' : f i z = y := hz
      exact Set.mem_singleton_iff.mpr (hinj (hz'.trans hx.symm))
    · have hsub : f i ⁻¹' {y} ⊆ (∅ : Set ℝ) := fun z hz => (hy ⟨z, hz⟩).elim
      exact measure_mono_null hsub measure_empty
  exact continuous_cdf_of_atomless _

/-- The coordinatewise transform of the marginal CDFs of the image law is the reflection of
the transform of the original law. -/
theorem marginalTransform_coordMap (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : Fin d → ℝ → ℝ}
    {s : Finset (Fin d)} (hinc : ∀ i, i ∉ s → StrictMono (f i))
    (hdec : ∀ i, i ∈ s → StrictAnti (f i)) (x : Fin d → ℝ) :
    marginalTransform (μ.map (coordMap f)) (coordMap f x) =
      reflectPoint s (marginalTransform μ x) := by
  have hf := measurable_fn_of_strict hinc hdec
  funext i
  apply Subtype.ext
  by_cases hi : i ∈ s
  · have h := cdf_marginal_map_coordMap_of_strictAnti μ hf (hdec i hi) (hc i) (x i)
    simp only [reflectPoint, hi, ↓reduceIte, unitInterval.coe_symm_eq]
    exact h
  · have h := cdf_marginal_map_coordMap_of_strictMono μ hf (hinc i hi) (x i)
    simp only [reflectPoint, hi, ↓reduceIte]
    exact h

/-- **Nelsen, Theorems 2.4.3 and 2.4.4 (any dimension).** Applying strictly increasing maps to
the coordinates outside `s` and strictly decreasing maps to the coordinates in `s` replaces the
copula by its reflection in the coordinates of `s`. -/
theorem ofContinuousMarginals_map_coordMap (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : Fin d → ℝ → ℝ}
    {s : Finset (Fin d)} (hinc : ∀ i, i ∉ s → StrictMono (f i))
    (hdec : ∀ i, i ∈ s → StrictAnti (f i)) :
    ofContinuousMarginals (μ.map (coordMap f))
        (continuous_cdf_marginal_map_coordMap μ hc hinc hdec) =
      (ofContinuousMarginals μ hc).reflect s := by
  have hf := measurable_fn_of_strict hinc hdec
  apply ext
  have h1 := Measure.map_map (μ := μ.toMeasure)
    (measurable_marginalTransform (μ.map (coordMap f))) (measurable_coordMap hf)
  have h2 := Measure.map_map (μ := μ.toMeasure) (measurable_reflectPoint s)
    (measurable_marginalTransform μ)
  have h3 : marginalTransform (μ.map (coordMap f)) ∘ coordMap f =
      reflectPoint s ∘ marginalTransform μ :=
    funext (marginalTransform_coordMap μ hc hinc hdec)
  show (μ.toMeasure.map (coordMap f)).map (marginalTransform (μ.map (coordMap f))) =
    (μ.toMeasure.map (marginalTransform μ)).map (reflectPoint s)
  rw [h1, h2, h3]

/-- Any Sklar copula of `μ` reflected in `s` is a Sklar copula of the transformed law. -/
theorem isSklarCopula_map_coordMap {μ : ProbabilityMeasure (Fin d → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : Fin d → ℝ → ℝ}
    {s : Finset (Fin d)} (hinc : ∀ i, i ∉ s → StrictMono (f i))
    (hdec : ∀ i, i ∈ s → StrictAnti (f i)) {C : Copula d} (hC : IsSklarCopula μ C) :
    IsSklarCopula (μ.map (coordMap f)) (C.reflect s) := by
  have hCe : C = ofContinuousMarginals μ hc :=
    hC.unique hc (isSklarCopula_ofContinuousMarginals μ hc)
  subst hCe
  rw [← ofContinuousMarginals_map_coordMap μ hc hinc hdec]
  exact isSklarCopula_ofContinuousMarginals _ _

/-- The Sklar copula of the transformed law is the reflected copula of the original law. -/
theorem eq_reflect_of_isSklarCopula_map_coordMap {μ : ProbabilityMeasure (Fin d → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : Fin d → ℝ → ℝ}
    {s : Finset (Fin d)} (hinc : ∀ i, i ∉ s → StrictMono (f i))
    (hdec : ∀ i, i ∈ s → StrictAnti (f i)) {C D : Copula d} (hC : IsSklarCopula μ C)
    (hD : IsSklarCopula (μ.map (coordMap f)) D) : D = C.reflect s :=
  hD.unique (continuous_cdf_marginal_map_coordMap μ hc hinc hdec)
    (isSklarCopula_map_coordMap hc hinc hdec hC)

/-! ### The bivariate statements -/

/-- **Nelsen, Theorem 2.4.3.** Strictly increasing transformations of both coordinates leave the
Sklar copula unchanged. -/
theorem isSklarCopula_map_strictMono_two {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) {α β : ℝ → ℝ} (hα : StrictMono α) (hβ : StrictMono β) :
    IsSklarCopula (μ.map (coordMap ![α, β])) C := by
  have hinc : ∀ i, i ∉ (∅ : Finset (Fin 2)) → StrictMono (![α, β] i) := by
    refine Fin.forall_fin_two.mpr ⟨fun _ => ?_, fun _ => ?_⟩
    · exact hα
    · exact hβ
  have hdec : ∀ i, i ∈ (∅ : Finset (Fin 2)) → StrictAnti (![α, β] i) :=
    fun i hi => by simp at hi
  have h := isSklarCopula_map_coordMap hc hinc hdec hC
  rwa [reflect_empty] at h

/-- **Nelsen, Theorem 2.4.4 (first case).** A strictly increasing map of the first coordinate
and a strictly decreasing map of the second coordinate reflect the second copula coordinate. -/
theorem isSklarCopula_map_strictMono_strictAnti {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) {α β : ℝ → ℝ} (hα : StrictMono α) (hβ : StrictAnti β) :
    IsSklarCopula (μ.map (coordMap ![α, β])) (C.reflect {1}) := by
  have hinc : ∀ i, i ∉ ({1} : Finset (Fin 2)) → StrictMono (![α, β] i) := by
    refine Fin.forall_fin_two.mpr ⟨fun _ => ?_, fun h => ?_⟩
    · exact hα
    · exact absurd (Finset.mem_singleton_self (1 : Fin 2)) h
  have hdec : ∀ i, i ∈ ({1} : Finset (Fin 2)) → StrictAnti (![α, β] i) := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hβ
  exact isSklarCopula_map_coordMap hc hinc hdec hC

/-- **Nelsen, Theorem 2.4.4 (second case).** A strictly decreasing map of the first coordinate
and a strictly increasing map of the second coordinate reflect the first copula coordinate. -/
theorem isSklarCopula_map_strictAnti_strictMono {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) {α β : ℝ → ℝ} (hα : StrictAnti α) (hβ : StrictMono β) :
    IsSklarCopula (μ.map (coordMap ![α, β])) (C.reflect {0}) := by
  have hinc : ∀ i, i ∉ ({0} : Finset (Fin 2)) → StrictMono (![α, β] i) := by
    refine Fin.forall_fin_two.mpr ⟨fun h => ?_, fun _ => ?_⟩
    · exact absurd (Finset.mem_singleton_self (0 : Fin 2)) h
    · exact hβ
  have hdec : ∀ i, i ∈ ({0} : Finset (Fin 2)) → StrictAnti (![α, β] i) := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hα
  exact isSklarCopula_map_coordMap hc hinc hdec hC

/-- **Nelsen, Theorem 2.4.4 (survival case).** Strictly decreasing transformations of both
coordinates turn the Sklar copula into the survival copula. -/
theorem isSklarCopula_map_strictAnti_two {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) {α β : ℝ → ℝ} (hα : StrictAnti α) (hβ : StrictAnti β) :
    IsSklarCopula (μ.map (coordMap ![α, β])) C.survivalCopula := by
  have hinc : ∀ i, i ∉ (Finset.univ : Finset (Fin 2)) → StrictMono (![α, β] i) :=
    fun i hi => absurd (Finset.mem_univ i) hi
  have hdec : ∀ i, i ∈ (Finset.univ : Finset (Fin 2)) → StrictAnti (![α, β] i) := by
    refine Fin.forall_fin_two.mpr ⟨fun _ => ?_, fun _ => ?_⟩
    · exact hα
    · exact hβ
  exact isSklarCopula_map_coordMap hc hinc hdec hC

end ProbabilityTheory.Copula
