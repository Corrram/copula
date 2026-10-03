/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Concordance.Continuity
import Copula.Order.StrictSpearman
import Copula.Rank.Symmetry
import Copula.Rank.Benchmarks
import Copula.Rank.ChatterjeeExamples
import Copula.Measures.SchweizerWolff
import Copula.Measures.CDFDistanceBenchmarks
import Copula.Support

/-!
# Scarsini's axioms for measures of concordance

Following Scarsini (1984) and Nelsen, *An Introduction to Copulas*, 2nd ed., Definition 5.1.7,
a numerical measure `κ` of association, expressed through the copula of a continuous pair
`(X, Y)`, is a *measure of concordance* if

1. it is defined for every copula (automatic for a function `Copula 2 → ℝ`);
2. `-1 ≤ κ(C) ≤ 1`, `κ(M) = 1` and `κ(W) = -1`;
3. `κ(Cᵀ) = κ(C)` (symmetry, `κ_{Y,X} = κ_{X,Y}`);
4. `κ(Π) = 0` (independence);
5. reflecting either coordinate changes the sign: `κ_{-X,Y} = κ_{X,-Y} = -κ_{X,Y}`;
6. coherence: `C ≤ D` pointwise implies `κ(C) ≤ κ(D)`;
7. continuity: if `Cₙ → C` pointwise then `κ(Cₙ) → κ(C)`.

Pointwise convergence of copulas is equivalent to uniform convergence
(`tendstoUniformly_cdf_iff`); `IsMeasureOfConcordance.tendsto_of_tendstoUniformly` restates
property 7 in uniform form.

We prove that Spearman's rho, Kendall's tau, Blomqvist's beta and Gini's gamma are measures
of concordance (Nelsen, §5.1), derive the standard consequences
(Nelsen, §5.1: perfect positive/negative dependence gives `±1`; invariance under the
survival transformation; vanishing for copulas invariant under one reflection; signs under
quadrant dependence), and show that Chatterjee's xi, the Schweizer–Wolff sigma, Hoeffding's
`Φ²` and Spearman's footrule are *not* measures of concordance: the first three take the value
`1` at both Fréchet bounds, which contradicts the reflection axiom, and the footrule takes the
value `-1/2` at `W`.
-/

open MeasureTheory Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- Scarsini's axioms for a measure of concordance (Nelsen, Definition 5.1.7). Property 1
(definedness for every pair of continuous random variables) is built into the type. -/
structure IsMeasureOfConcordance (κ : Copula 2 → ℝ) : Prop where
  /-- Property 2: values in `[-1, 1]`. -/
  mem_Icc : ∀ C, κ C ∈ Icc (-1 : ℝ) 1
  /-- Property 2: `κ(M) = 1`. -/
  comonotonic : κ (comonotonic 2) = 1
  /-- Property 2: `κ(W) = -1`. -/
  countermonotonic : κ countermonotonic = -1
  /-- Property 3: symmetry in the two coordinates. -/
  transpose : ∀ C, κ C.transpose = κ C
  /-- Property 4: independence has concordance zero. -/
  independence : κ (independence 2) = 0
  /-- Property 5: reflecting the first coordinate changes the sign. -/
  reflect_first : ∀ C, κ (C.reflect {0}) = -κ C
  /-- Property 5: reflecting the second coordinate changes the sign. -/
  reflect_second : ∀ C, κ (C.reflect {1}) = -κ C
  /-- Property 6: coherence with the pointwise (concordance) order. -/
  mono : ∀ C D, C.LowerOrthantLE D → κ C ≤ κ D
  /-- Property 7: continuity under pointwise convergence of copulas. -/
  tendsto : ∀ (C : ℕ → Copula 2) (D : Copula 2),
    (∀ u, Tendsto (fun n => (C n).cdf u) atTop (𝓝 (D.cdf u))) →
      Tendsto (fun n => κ (C n)) atTop (𝓝 (κ D))

namespace IsMeasureOfConcordance

variable {κ : Copula 2 → ℝ}

/-- Property 7 in the equivalent form of uniform convergence of the CDFs. -/
theorem tendsto_of_tendstoUniformly (h : IsMeasureOfConcordance κ) (C : ℕ → Copula 2)
    (D : Copula 2) (hC : TendstoUniformly (fun n => (C n).cdf) D.cdf atTop) :
    Tendsto (fun n => κ (C n)) atTop (𝓝 (κ D)) :=
  h.tendsto C D ((tendstoUniformly_cdf_iff C D).mp hC)

/-- Measures of concordance are invariant under the survival transformation `C ↦ Ĉ`
(reflection of both coordinates, `κ_{-X,-Y} = κ_{X,Y}`). -/
theorem survivalCopula (h : IsMeasureOfConcordance κ) (C : Copula 2) :
    κ C.survivalCopula = κ C := by
  rw [← reflect_first_second, h.reflect_second, h.reflect_first, neg_neg]

/-- A copula invariant under reflection of the first coordinate has concordance zero. -/
theorem eq_zero_of_reflect_first_eq (h : IsMeasureOfConcordance κ) {C : Copula 2}
    (hC : C.reflect {0} = C) : κ C = 0 := by
  have := h.reflect_first C
  rw [hC] at this
  linarith

/-- A copula invariant under reflection of the second coordinate has concordance zero. -/
theorem eq_zero_of_reflect_second_eq (h : IsMeasureOfConcordance κ) {C : Copula 2}
    (hC : C.reflect {1} = C) : κ C = 0 := by
  have := h.reflect_second C
  rw [hC] at this
  linarith

/-- Nelsen, §5.1: if `Y` is almost surely an increasing function of `X`
(the copula is `M`), the concordance is `1`. -/
theorem eq_one_of_ae_eq (h : IsMeasureOfConcordance κ) {C : Copula 2}
    (hC : ∀ᵐ x ∂C.toMeasure, x 0 = x 1) : κ C = 1 := by
  rw [(eq_comonotonic_iff_ae_eval_eq C).mpr hC, h.comonotonic]

/-- Nelsen, §5.1: if `Y` is almost surely a decreasing function of `X`
(the copula is `W`), the concordance is `-1`. -/
theorem eq_neg_one_of_ae_eq_symm (h : IsMeasureOfConcordance κ) {C : Copula 2}
    (hC : ∀ᵐ x ∂C.toMeasure, x 1 = unitInterval.symm (x 0)) : κ C = -1 := by
  rw [(eq_countermonotonic_iff_ae_eval_eq_symm C).mpr hC, h.countermonotonic]

/-- Positive quadrant dependence forces a nonnegative concordance. -/
theorem nonneg_of_isPQD (h : IsMeasureOfConcordance κ) {C : Copula 2} (hC : C.IsPQD) :
    0 ≤ κ C := by
  simpa [h.independence] using h.mono _ _ ((isPQD_iff_lowerOrthantLE C).mp hC)

/-- Negative quadrant dependence forces a nonpositive concordance. -/
theorem nonpos_of_isNQD (h : IsMeasureOfConcordance κ) {C : Copula 2} (hC : C.IsNQD) :
    κ C ≤ 0 := by
  simpa [h.independence] using h.mono _ _ ((isNQD_iff_lowerOrthantLE C).mp hC)

/-- A measure of concordance is nondecreasing along the concordance order. -/
theorem mono_concordanceLE (h : IsMeasureOfConcordance κ) {C D : Copula 2}
    (hCD : C.ConcordanceLE D) : κ C ≤ κ D :=
  h.mono C D hCD.1

/-- Convex combinations of measures of concordance are measures of concordance. -/
theorem convexComb {κ' : Copula 2 → ℝ} (h : IsMeasureOfConcordance κ)
    (h' : IsMeasureOfConcordance κ') {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    IsMeasureOfConcordance (fun C => a * κ C + (1 - a) * κ' C) where
  mem_Icc C := by
    obtain ⟨h₁, h₂⟩ := h.mem_Icc C
    obtain ⟨h₁', h₂'⟩ := h'.mem_Icc C
    constructor <;> nlinarith
  comonotonic := by rw [h.comonotonic, h'.comonotonic]; ring
  countermonotonic := by rw [h.countermonotonic, h'.countermonotonic]; ring
  transpose C := by rw [h.transpose, h'.transpose]
  independence := by rw [h.independence, h'.independence]; ring
  reflect_first C := by rw [h.reflect_first, h'.reflect_first]; ring
  reflect_second C := by rw [h.reflect_second, h'.reflect_second]; ring
  mono C D hCD := by
    have := h.mono C D hCD
    have := h'.mono C D hCD
    nlinarith
  tendsto C D hC := ((h.tendsto C D hC).const_mul a).add ((h'.tendsto C D hC).const_mul (1 - a))

/-- A functional taking the same value at both Fréchet bounds violates the axioms. -/
theorem comonotonic_ne_countermonotonic (h : IsMeasureOfConcordance κ) :
    κ (Copula.comonotonic 2) ≠ κ Copula.countermonotonic := by
  rw [h.comonotonic, h.countermonotonic]
  norm_num

end IsMeasureOfConcordance

/-! ## The four classical measures of concordance -/

/-- Spearman's rho is a measure of concordance. -/
theorem isMeasureOfConcordance_spearmanRho : IsMeasureOfConcordance spearmanRho where
  mem_Icc := spearmanRho_mem_Icc
  comonotonic := spearmanRho_comonotonic
  countermonotonic := spearmanRho_countermonotonic
  transpose := spearmanRho_transpose
  independence := spearmanRho_independence
  reflect_first := spearmanRho_reflect_first
  reflect_second := spearmanRho_reflect_second
  mono _ _ h := h.spearmanRho_le
  tendsto C D h := tendsto_spearmanRho_of_tendsto C D h

/-- Kendall's tau is a measure of concordance. -/
theorem isMeasureOfConcordance_kendallTau : IsMeasureOfConcordance kendallTau where
  mem_Icc := kendallTau_mem_Icc
  comonotonic := kendallTau_comonotonic
  countermonotonic := kendallTau_countermonotonic
  transpose := kendallTau_transpose
  independence := kendallTau_independence
  reflect_first := kendallTau_reflect_first
  reflect_second := kendallTau_reflect_second
  mono _ _ h := h.kendallTau_le
  tendsto C D h := tendsto_kendallTau_of_tendsto C D h

/-- Blomqvist's beta is a measure of concordance. -/
theorem isMeasureOfConcordance_blomqvistBeta : IsMeasureOfConcordance blomqvistBeta where
  mem_Icc := blomqvistBeta_mem_Icc
  comonotonic := blomqvistBeta_comonotonic
  countermonotonic := blomqvistBeta_countermonotonic
  transpose := blomqvistBeta_transpose
  independence := blomqvistBeta_independence
  reflect_first := blomqvistBeta_reflect_first
  reflect_second := blomqvistBeta_reflect_second
  mono _ _ h := h.blomqvistBeta_le
  tendsto C D h := tendsto_blomqvistBeta_of_tendsto C D h

/-- Gini's gamma is a measure of concordance. -/
theorem isMeasureOfConcordance_giniGamma : IsMeasureOfConcordance giniGamma where
  mem_Icc := giniGamma_mem_Icc
  comonotonic := giniGamma_comonotonic
  countermonotonic := giniGamma_countermonotonic
  transpose := giniGamma_transpose
  independence := giniGamma_independence
  reflect_first := giniGamma_reflect_first
  reflect_second := giniGamma_reflect_second
  mono _ _ h := h.giniGamma_le
  tendsto C D h := tendsto_giniGamma_of_tendsto C D h

/-! ## Coefficients that are not measures of concordance -/

/-- Chatterjee's xi violates the reflection axiom: reflecting `M` gives `W`, but
`ξ(W) = ξ(M) = 1`. -/
theorem chatterjeeXi_reflect_second_comonotonic :
    ((comonotonic 2).reflect {1}).chatterjeeXi ≠ -(comonotonic 2).chatterjeeXi := by
  rw [reflect_comonotonic_eq_countermonotonic]
  norm_num

/-- Chatterjee's xi is not a measure of concordance. -/
theorem not_isMeasureOfConcordance_chatterjeeXi :
    ¬ IsMeasureOfConcordance chatterjeeXi := fun h =>
  chatterjeeXi_reflect_second_comonotonic (h.reflect_second _)

/-- The Schweizer–Wolff sigma violates the reflection axiom. -/
theorem schweizerWolff_reflect_second_comonotonic :
    ((comonotonic 2).reflect {1}).schweizerWolff ≠ -(comonotonic 2).schweizerWolff := by
  rw [reflect_comonotonic_eq_countermonotonic]
  norm_num

/-- The Schweizer–Wolff sigma is not a measure of concordance. -/
theorem not_isMeasureOfConcordance_schweizerWolff :
    ¬ IsMeasureOfConcordance schweizerWolff := fun h =>
  schweizerWolff_reflect_second_comonotonic (h.reflect_second _)

/-- Hoeffding's `Φ²` violates the reflection axiom. -/
theorem hoeffdingPhiSq_reflect_second_comonotonic :
    ((comonotonic 2).reflect {1}).hoeffdingPhiSq ≠ -(comonotonic 2).hoeffdingPhiSq := by
  rw [reflect_comonotonic_eq_countermonotonic]
  norm_num

/-- Hoeffding's `Φ²` is not a measure of concordance. -/
theorem not_isMeasureOfConcordance_hoeffdingPhiSq :
    ¬ IsMeasureOfConcordance hoeffdingPhiSq := fun h =>
  hoeffdingPhiSq_reflect_second_comonotonic (h.reflect_second _)

/-- Spearman's footrule takes the value `-1/2` at `W`, so it is not a measure of concordance
(it also violates the reflection axiom at `M`). -/
theorem not_isMeasureOfConcordance_spearmanFootrule :
    ¬ IsMeasureOfConcordance spearmanFootrule := fun h => by
  have := h.countermonotonic
  norm_num at this

end ProbabilityTheory.Copula
