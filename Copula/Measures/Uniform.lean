/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Topology.UniformDistance
import Copula.Measures.CDFDistanceSymmetry

/-! # The uniform distance to independence

Schweizer and Wolff (1981) proposed normalized `L¹`, `L²` and `L∞` distances between a copula
`C` and the independence copula `Π` (Nelsen, *An Introduction to Copulas*, 2nd ed., §5.3.1).
The `L¹` version is `schweizerWolff` (`σ`), the square of the `L²` version is Hoeffding's
`hoeffdingPhiSq` (`Φ²`), and this file adds the uniform version

`κ(C) = 4 sup |C(u,v) - uv|`.

We prove: the supremum is attained, `κ` takes values in `[0,1]`, vanishes exactly under
independence, is invariant under transposition and reflections, is `4`-Lipschitz for the uniform
distance of copulas, and dominates `|β|` (Blomqvist's beta) and `σ / 3`. Iterated-integral forms
of `σ` and `Φ²` are also recorded. The equality case `κ = 1 ↔ |β| = 1` is in
`Copula.Measures.Bounds`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Schweizer–Wolff's uniform (`L∞`) distance to independence, `κ(C) = 4 sup |C - Π|`. -/
noncomputable def schweizerWolffKappa (C : Copula 2) : ℝ :=
  4 * C.uniformCDFDistance (independence 2)

theorem abs_cdfDeviation_le_schweizerWolffKappa (C : Copula 2) (x : Fin 2 → I) :
    4 * |C.cdfDeviation x| ≤ C.schweizerWolffKappa := by
  have h := C.abs_cdf_sub_le_uniformCDFDistance (independence 2) x
  have hx : (independence 2).cdf x = (x 0 : ℝ) * x 1 := by
    simp [cdf_independence, Fin.prod_univ_two]
  rw [hx] at h
  unfold schweizerWolffKappa cdfDeviation
  linarith

theorem abs_cdf_sub_mul_le_schweizerWolffKappa (C : Copula 2) (u v : I) :
    4 * |C.cdf ![u, v] - (u : ℝ) * v| ≤ C.schweizerWolffKappa :=
  C.abs_cdfDeviation_le_schweizerWolffKappa ![u, v]

theorem schweizerWolffKappa_le_iff (C : Copula 2) (q : ℝ) :
    C.schweizerWolffKappa ≤ q ↔ ∀ u v : I, 4 * |C.cdf ![u, v] - (u : ℝ) * v| ≤ q := by
  constructor
  · intro h u v
    exact (C.abs_cdf_sub_mul_le_schweizerWolffKappa u v).trans h
  · intro h
    have hr : C.uniformCDFDistance (independence 2) ≤ q / 4 := by
      apply (C.uniformCDFDistance_le_iff _ _).2
      intro x
      have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
      have hx' := h (x 0) (x 1)
      rw [← hx] at hx'
      rw [cdf_independence_two]
      linarith
    unfold schweizerWolffKappa
    linarith

theorem schweizerWolffKappa_nonneg (C : Copula 2) : 0 ≤ C.schweizerWolffKappa := by
  unfold schweizerWolffKappa
  linarith [C.uniformCDFDistance_nonneg (independence 2)]

/-- The supremum defining `κ` is attained. -/
theorem exists_schweizerWolffKappa_eq (C : Copula 2) :
    ∃ u v : I, 4 * |C.cdf ![u, v] - (u : ℝ) * v| = C.schweizerWolffKappa := by
  have hc : Continuous (fun p : I × I => 4 * |C.cdf ![p.1, p.2] - (p.1 : ℝ) * p.2|) := by
    have h1 : Continuous (fun p : I × I => C.cdf ![p.1, p.2]) :=
      C.continuous_cdf.comp (by fun_prop)
    have h2 : Continuous (fun p : I × I => (p.1 : ℝ) * p.2) := by fun_prop
    exact continuous_const.mul ((h1.sub h2).abs)
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.continuousOn
  have hmax : ∀ q : I × I, 4 * |C.cdf ![q.1, q.2] - (q.1 : ℝ) * q.2| ≤
      4 * |C.cdf ![p.1, p.2] - (p.1 : ℝ) * p.2| := fun q => hp (mem_univ q)
  have hle : C.schweizerWolffKappa ≤ 4 * |C.cdf ![p.1, p.2] - (p.1 : ℝ) * p.2| :=
    (C.schweizerWolffKappa_le_iff _).2 (fun u v => hmax (u, v))
  exact ⟨p.1, p.2, le_antisymm (C.abs_cdf_sub_mul_le_schweizerWolffKappa _ _) hle⟩

theorem schweizerWolffKappa_le_one (C : Copula 2) : C.schweizerWolffKappa ≤ 1 := by
  apply (C.schweizerWolffKappa_le_iff 1).2
  intro u v
  have hM := C.cdf_le_comonotonic ![u, v]
  have hW := C.cdf_countermonotonic_le ![u, v]
  rw [cdf_comonotonic_two] at hM
  rw [cdf_countermonotonic] at hW
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hM hW
  have hu0 := u.property.1
  have hu1 := u.property.2
  have hv0 := v.property.1
  have hv1 := v.property.2
  have hlow : -(1 / 4 : ℝ) ≤ C.cdf ![u, v] - (u : ℝ) * v := by
    have h1 : -(1 / 4 : ℝ) ≤ max 0 ((u : ℝ) + v - 1) - (u : ℝ) * v := by
      by_cases h : (u : ℝ) + v ≤ 1
      · have := le_max_left (0 : ℝ) ((u : ℝ) + v - 1)
        nlinarith [sq_nonneg ((u : ℝ) - v), sq_nonneg ((u : ℝ) + v - 1)]
      · have := le_max_right (0 : ℝ) ((u : ℝ) + v - 1)
        nlinarith [sq_nonneg ((u : ℝ) - v), sq_nonneg ((u : ℝ) + v - 1)]
    linarith
  have hup : C.cdf ![u, v] - (u : ℝ) * v ≤ 1 / 4 := by
    rcases le_total (u : ℝ) v with h | h
    · have : C.cdf ![u, v] ≤ u := hM.trans (min_le_left _ _)
      nlinarith [sq_nonneg ((u : ℝ) - 1 / 2), sq_nonneg ((v : ℝ) - 1 / 2)]
    · have : C.cdf ![u, v] ≤ v := hM.trans (min_le_right _ _)
      nlinarith [sq_nonneg ((u : ℝ) - 1 / 2), sq_nonneg ((v : ℝ) - 1 / 2)]
  have habs : |C.cdf ![u, v] - (u : ℝ) * v| ≤ 1 / 4 := abs_le.mpr ⟨hlow, hup⟩
  linarith

theorem schweizerWolffKappa_mem_Icc (C : Copula 2) : C.schweizerWolffKappa ∈ Icc (0 : ℝ) 1 :=
  ⟨C.schweizerWolffKappa_nonneg, C.schweizerWolffKappa_le_one⟩

theorem schweizerWolffKappa_eq_zero_iff (C : Copula 2) :
    C.schweizerWolffKappa = 0 ↔ C = independence 2 := by
  unfold schweizerWolffKappa
  rw [mul_eq_zero, or_iff_right (by norm_num : (4 : ℝ) ≠ 0), uniformCDFDistance_eq_zero_iff]

@[simp] theorem schweizerWolffKappa_independence : (independence 2).schweizerWolffKappa = 0 :=
  (schweizerWolffKappa_eq_zero_iff _).2 rfl

theorem schweizerWolffKappa_pos_iff (C : Copula 2) :
    0 < C.schweizerWolffKappa ↔ C ≠ independence 2 := by
  constructor
  · intro h hC
    rw [hC, schweizerWolffKappa_independence] at h
    exact lt_irrefl _ h
  · intro h
    rcases lt_or_eq_of_le C.schweizerWolffKappa_nonneg with h' | h'
    · exact h'
    · exact absurd ((C.schweizerWolffKappa_eq_zero_iff).1 h'.symm) h

/-- Two copulas with the same absolute deviation from independence at every point have the
same `κ`. -/
theorem schweizerWolffKappa_le_of_abs_eq (C D : Copula 2)
    (h : ∀ u v : I, ∃ u' v' : I, |C.cdf ![u, v] - (u : ℝ) * v| =
      |D.cdf ![u', v'] - (u' : ℝ) * v'|) :
    C.schweizerWolffKappa ≤ D.schweizerWolffKappa := by
  apply (C.schweizerWolffKappa_le_iff _).2
  intro u v
  obtain ⟨u', v', he⟩ := h u v
  rw [he]
  exact D.abs_cdf_sub_mul_le_schweizerWolffKappa u' v'

@[simp] theorem schweizerWolffKappa_transpose (C : Copula 2) :
    C.transpose.schweizerWolffKappa = C.schweizerWolffKappa := by
  have h (C : Copula 2) : C.transpose.schweizerWolffKappa ≤ C.schweizerWolffKappa := by
    apply schweizerWolffKappa_le_of_abs_eq
    intro u v
    exact ⟨v, u, by rw [cdf_transpose, mul_comm]⟩
  exact le_antisymm (h C) (by simpa only [transpose_transpose] using h C.transpose)

@[simp] theorem schweizerWolffKappa_reflect_second (C : Copula 2) :
    (C.reflect {1}).schweizerWolffKappa = C.schweizerWolffKappa := by
  have h (C : Copula 2) : (C.reflect {1}).schweizerWolffKappa ≤ C.schweizerWolffKappa := by
    apply schweizerWolffKappa_le_of_abs_eq
    intro u v
    refine ⟨u, unitInterval.symm v, ?_⟩
    rw [cdf_reflect_second, unitInterval.coe_symm_eq, ← abs_neg]
    congr 1
    ring
  exact le_antisymm (h C) (by simpa only [reflect_reflect] using h (C.reflect {1}))

@[simp] theorem schweizerWolffKappa_reflect_first (C : Copula 2) :
    (C.reflect {0}).schweizerWolffKappa = C.schweizerWolffKappa := by
  rw [← schweizerWolffKappa_transpose, transpose_reflect_first, schweizerWolffKappa_reflect_second,
    schweizerWolffKappa_transpose]

/-- `κ` is 4-Lipschitz for the uniform distance of copulas. -/
theorem abs_schweizerWolffKappa_sub_le (C D : Copula 2) :
    |C.schweizerWolffKappa - D.schweizerWolffKappa| ≤ 4 * C.uniformCDFDistance D := by
  unfold schweizerWolffKappa
  have h1 := C.uniformCDFDistance_triangle D (independence 2)
  have h2 := D.uniformCDFDistance_triangle C (independence 2)
  rw [uniformCDFDistance_comm D C] at h2
  rw [abs_le]
  constructor <;> linarith

/-- `κ` is continuous along mixtures. -/
theorem continuous_schweizerWolffKappa_mix (C D : Copula 2) :
    Continuous (fun a : I => (C.mix D a).schweizerWolffKappa) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨ε / 8, by positivity, fun b hb => ?_⟩
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_schweizerWolffKappa_sub_le _ _) ?_
  have hd : (C.mix D b).uniformCDFDistance (C.mix D a) ≤ |(b : ℝ) - a| := by
    apply (uniformCDFDistance_le_iff _ _ _).2
    intro x
    rw [cdf_mix, cdf_mix]
    have he : (b : ℝ) * C.cdf x + (1 - b) * D.cdf x - ((a : ℝ) * C.cdf x + (1 - a) * D.cdf x) =
        ((b : ℝ) - a) * (C.cdf x - D.cdf x) := by ring
    rw [he, abs_mul]
    have : |C.cdf x - D.cdf x| ≤ 1 := abs_le.mpr ⟨by linarith [C.cdf_nonneg x, D.cdf_le_one x],
      by linarith [D.cdf_nonneg x, C.cdf_le_one x]⟩
    nlinarith [abs_nonneg ((b : ℝ) - a)]
  rw [Subtype.dist_eq, Real.dist_eq] at hb
  nlinarith

theorem abs_blomqvistBeta_le_schweizerWolffKappa (C : Copula 2) :
    |C.blomqvistBeta| ≤ C.schweizerWolffKappa := by
  have h := C.abs_cdf_sub_mul_le_schweizerWolffKappa unitHalf unitHalf
  have hh : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
  rw [hh] at h
  unfold blomqvistBeta
  rw [show 4 * C.cdf ![unitHalf, unitHalf] - 1 = 4 * (C.cdf ![unitHalf, unitHalf] - 1 / 2 * (1 / 2))
    by ring, abs_mul]
  norm_num at h ⊢
  linarith

/-- The `L¹` distance as an iterated integral with the second coordinate outside. -/
theorem schweizerWolff_eq_iterated (C : Copula 2) :
    C.schweizerWolff = 12 * ∫ v : I, ∫ u : I, |C.cdf ![u, v] - (u : ℝ) * v| := by
  rw [schweizerWolff_eq_integral_abs_cdfDeviation,
    integral_independence_two (fun x => |C.cdfDeviation x|) C.continuous_cdfDeviation.abs]
  congr 1
  have hi : Integrable (fun p : I × I => |C.cdfDeviation ![p.1, p.2]|)
      ((volume : Measure I).prod volume) :=
    ((C.continuous_cdfDeviation.comp (by fun_prop)).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_integral_swap hi

/-- Hoeffding's `Φ²` as an iterated integral with the second coordinate outside. -/
theorem hoeffdingPhiSq_eq_iterated (C : Copula 2) :
    C.hoeffdingPhiSq = 90 * ∫ v : I, ∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) ^ 2 := by
  rw [hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR, blumKieferRosenblattR,
    integral_independence_two (fun x => C.cdfDeviation x ^ 2) (C.continuous_cdfDeviation.pow 2)]
  congr 1
  have hi : Integrable (fun p : I × I => C.cdfDeviation ![p.1, p.2] ^ 2)
      ((volume : Measure I).prod volume) :=
    ((C.continuous_cdfDeviation.comp (by fun_prop)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_integral_swap hi

/-- The `L¹` distance is dominated by the uniform one: `σ ≤ 3 κ`. -/
theorem schweizerWolff_le_three_mul_schweizerWolffKappa (C : Copula 2) :
    C.schweizerWolff ≤ 3 * C.schweizerWolffKappa := by
  have h : (∫ x, |C.cdfDeviation x| ∂(independence 2).toMeasure) ≤
      ∫ _x, C.schweizerWolffKappa / 4 ∂(independence 2).toMeasure :=
    integral_mono (C.integrable_abs_cdfDeviation _) (integrable_const _) fun x => by
      have := C.abs_cdfDeviation_le_schweizerWolffKappa x
      simp only
      linarith
  rw [integral_const, probReal_univ, one_smul] at h
  rw [schweizerWolff_eq_integral_abs_cdfDeviation]
  linarith

/-- Hoeffding's `Φ²` is dominated by the uniform distance: `Φ² ≤ 90/16 κ²`. -/
theorem hoeffdingPhiSq_le_schweizerWolffKappa_sq (C : Copula 2) :
    C.hoeffdingPhiSq ≤ 45 / 8 * C.schweizerWolffKappa ^ 2 := by
  have h : (∫ x, C.cdfDeviation x ^ 2 ∂(independence 2).toMeasure) ≤
      ∫ _x, (C.schweizerWolffKappa / 4) ^ 2 ∂(independence 2).toMeasure :=
    integral_mono (C.integrable_cdfDeviation_sq _) (integrable_const _) fun x => by
      have h1 := C.abs_cdfDeviation_le_schweizerWolffKappa x
      have h2 := abs_nonneg (C.cdfDeviation x)
      simp only
      rw [← sq_abs]
      nlinarith
  rw [integral_const, probReal_univ, one_smul] at h
  rw [hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR, blumKieferRosenblattR]
  nlinarith

end ProbabilityTheory.Copula
