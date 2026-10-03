/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Topology.Uniform
import Copula.Order.Rank
import Copula.Rank.Spearman

/-!
# Continuity of rank coefficients under convergence of copulas

If a family of bivariate copulas converges pointwise to a copula `D`, then Spearman's
rho, Kendall's tau, Blomqvist's beta, Gini's gamma and Spearman's footrule converge to the
corresponding coefficients of `D`. This is the continuity axiom in Scarsini's definition
of a measure of concordance (Nelsen, *An Introduction to Copulas*, 2nd ed., Definition 5.1.7,
property 7).

Pointwise convergence of copula CDFs is uniform (`tendstoUniformly_cdf_of_tendsto`). The
linear coefficients follow from dominated convergence. For Kendall's tau the integrand and
the integrating measure both move; we split
`∫ Cₙ dCₙ = ∫ (Cₙ - D) dCₙ + ∫ Cₙ dD`, using the symmetry of the concordance integral
(`integral_cdf_swap`), and control the first term by the uniform distance.
-/

open MeasureTheory Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

variable {ι : Type*} {l : Filter ι}

/-- Integrals of copula CDFs against a fixed finite measure converge under pointwise
convergence of the copulas. -/
theorem tendsto_integral_cdf_of_tendsto {d : ℕ} [l.IsCountablyGenerated] (C : ι → Copula d)
    (D : Copula d) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u)))
    (μ : Measure (Fin d → I)) [IsFiniteMeasure μ] :
    Tendsto (fun n => ∫ x, (C n).cdf x ∂μ) l (𝓝 (∫ x, D.cdf x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall fun n => (C n).continuous_cdf.aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => ?_)
    (integrable_const 1) (Eventually.of_forall h)
  rw [Real.norm_eq_abs, abs_of_nonneg ((C n).cdf_nonneg x)]
  exact (C n).cdf_le_one x

/-- Integrals of a function of a CDF section over the unit interval converge. -/
private theorem tendsto_integral_section [l.IsCountablyGenerated] (C : ι → Copula 2)
    (D : Copula 2) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u)))
    (p : I → Fin 2 → I) (hp : Continuous p) :
    Tendsto (fun n => ∫ t : I, (C n).cdf (p t)) l (𝓝 (∫ t : I, D.cdf (p t))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall fun n => ((C n).continuous_cdf.comp hp).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun t => ?_)
    (integrable_const 1) (Eventually.of_forall fun t => h (p t))
  rw [Real.norm_eq_abs, abs_of_nonneg ((C n).cdf_nonneg _)]
  exact (C n).cdf_le_one _

/-- Spearman's rho is continuous under pointwise convergence of copulas. -/
theorem tendsto_spearmanRho_of_tendsto [l.IsCountablyGenerated] (C : ι → Copula 2)
    (D : Copula 2) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u))) :
    Tendsto (fun n => (C n).spearmanRho) l (𝓝 D.spearmanRho) := by
  simp_rw [spearmanRho_eq_integral_cdf]
  exact ((tendsto_integral_cdf_of_tendsto C D h _).const_mul 12).sub_const 3

/-- Blomqvist's beta is continuous under pointwise convergence of copulas. -/
theorem tendsto_blomqvistBeta_of_tendsto (C : ι → Copula 2)
    (D : Copula 2) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u))) :
    Tendsto (fun n => (C n).blomqvistBeta) l (𝓝 D.blomqvistBeta) :=
  ((h ![unitHalf, unitHalf]).const_mul 4).sub_const 1

/-- Spearman's footrule is continuous under pointwise convergence of copulas. -/
theorem tendsto_spearmanFootrule_of_tendsto [l.IsCountablyGenerated] (C : ι → Copula 2)
    (D : Copula 2) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u))) :
    Tendsto (fun n => (C n).spearmanFootrule) l (𝓝 D.spearmanFootrule) :=
  ((tendsto_integral_section C D h (fun t => ![t, t]) (by fun_prop)).const_mul 6).sub_const 2

/-- Gini's gamma is continuous under pointwise convergence of copulas. -/
theorem tendsto_giniGamma_of_tendsto [l.IsCountablyGenerated] (C : ι → Copula 2)
    (D : Copula 2) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u))) :
    Tendsto (fun n => (C n).giniGamma) l (𝓝 D.giniGamma) :=
  (((tendsto_integral_section C D h (fun t => ![t, t]) (by fun_prop)).add
    (tendsto_integral_section C D h (fun t => ![t, unitInterval.symm t])
      (by fun_prop))).const_mul 4).sub_const 2

/-- Under uniform convergence of the CDFs, the integral of `Cₙ - D` against `Cₙ` vanishes. -/
private theorem tendsto_integral_cdf_sub_self (C : ι → Copula 2) (D : Copula 2)
    (h : TendstoUniformly (fun n => (C n).cdf) D.cdf l) :
    Tendsto (fun n => ∫ x, ((C n).cdf x - D.cdf x) ∂(C n).toMeasure) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero]
  have hb : ∀ x, ‖(C n).cdf x - D.cdf x‖ ≤ ε / 2 := fun x => by
    have := hn x
    rw [Real.dist_eq, abs_sub_comm] at this
    exact (Real.norm_eq_abs _).le.trans this.le
  have hle := norm_integral_le_of_norm_le_const (μ := (C n).toMeasure)
    (Eventually.of_forall hb)
  rw [probReal_univ, mul_one] at hle
  rw [← Real.norm_eq_abs]
  linarith

/-- Kendall's tau is continuous under pointwise convergence of copulas. -/
theorem tendsto_kendallTau_of_tendsto [l.IsCountablyGenerated] (C : ι → Copula 2)
    (D : Copula 2) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u))) :
    Tendsto (fun n => (C n).kendallTau) l (𝓝 D.kendallTau) := by
  have hsplit (n : ι) : (∫ x, (C n).cdf x ∂(C n).toMeasure) =
      (∫ x, ((C n).cdf x - D.cdf x) ∂(C n).toMeasure) + ∫ x, (C n).cdf x ∂D.toMeasure := by
    rw [integral_sub ((C n).integrable_cdf _) (D.integrable_cdf _),
      integral_cdf_swap (C n) D]
    ring
  have hlim : Tendsto (fun n => ∫ x, (C n).cdf x ∂(C n).toMeasure) l
      (𝓝 (∫ x, D.cdf x ∂D.toMeasure)) := by
    simp_rw [hsplit]
    simpa using (tendsto_integral_cdf_sub_self C D
      (tendstoUniformly_cdf_of_tendsto C D h)).add
      (tendsto_integral_cdf_of_tendsto C D h D.toMeasure)
  exact (hlim.const_mul 4).sub_const 1

end ProbabilityTheory.Copula
