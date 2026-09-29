/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.RandomVariable.Ext
import Copula.Independence
import Copula.Sklar

/-!
# Independence and the independence copula

Nelsen, *An Introduction to Copulas*, second edition, Theorem 2.4.2.

The coordinates of a random vector with law `μ` are independent exactly when `μ` is the product
of its coordinate laws, `μ = Measure.pi (marginal μ)`. This holds if and only if the
independence copula `Copula.independence d` is a Sklar copula of `μ`. With continuous marginals
the Sklar copula is unique, so independence is equivalent to the Sklar copula being `Π`.
-/

open MeasureTheory Set

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The lower-orthant probability of a product measure is the product of the marginal CDF values. -/
theorem measureReal_Iic_pi (ν : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (x : Fin d → ℝ) : (Measure.pi ν).real (Iic x) = ∏ i, (ν i).real (Iic (x i)) := by
  have h : Iic x = Set.pi univ (fun i => Iic (x i)) := by
    ext y
    simp [mem_Iic, Pi.le_def]
  simp only [Measure.real, h, Measure.pi_pi, ENNReal.toReal_prod]

/-- A law that is the product of its marginals has the independence copula as a Sklar copula. -/
theorem isSklarCopula_independence_of_eq_pi (μ : ProbabilityMeasure (Fin d → ℝ))
    (hμ : μ.toMeasure = Measure.pi (fun i => marginal μ i)) :
    IsSklarCopula μ (independence d) := by
  intro x
  rw [cdf_independence, hμ, measureReal_Iic_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact ProbabilityTheory.cdf_eq_real (marginal μ i) (x i)

/-- If the independence copula is a Sklar copula of a law, the law is the product of its
marginals. -/
theorem eq_pi_marginal_of_isSklarCopula_independence (μ : ProbabilityMeasure (Fin d → ℝ))
    (h : IsSklarCopula μ (independence d)) :
    μ.toMeasure = Measure.pi (fun i => marginal μ i) := by
  apply ext_real_of_Iic
  intro x
  rw [measureReal_Iic_pi, ← h x, cdf_independence]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact ProbabilityTheory.cdf_eq_real (marginal μ i) (x i)

/-- **Nelsen, Theorem 2.4.2.** A law has the independence copula as a Sklar copula if and only if
it is the product of its marginals. -/
theorem isSklarCopula_independence_iff (μ : ProbabilityMeasure (Fin d → ℝ)) :
    IsSklarCopula μ (independence d) ↔ μ.toMeasure = Measure.pi (fun i => marginal μ i) :=
  ⟨eq_pi_marginal_of_isSklarCopula_independence μ, isSklarCopula_independence_of_eq_pi μ⟩

/-- With continuous marginals, the Sklar copula of a law is the independence copula if and only if
the law is the product of its marginals. -/
theorem ofContinuousMarginals_eq_independence_iff (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ofContinuousMarginals μ hc = independence d ↔
      μ.toMeasure = Measure.pi (fun i => marginal μ i) := by
  constructor
  · intro h
    apply eq_pi_marginal_of_isSklarCopula_independence
    rw [← h]
    exact isSklarCopula_ofContinuousMarginals μ hc
  · intro h
    exact (isSklarCopula_ofContinuousMarginals μ hc).unique hc
      (isSklarCopula_independence_of_eq_pi μ h)

end ProbabilityTheory.Copula
