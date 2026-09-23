import Copula

open ProbabilityTheory MeasureTheory
open scoped unitInterval

-- Public imports, full-domain statements and the independence/singular endpoints.
example (θ : I) : (Copula.nelsen7 θ).chatterjeeXi = 1 - (θ : ℝ) :=
  Copula.chatterjeeXi_nelsen7 θ
example : (Copula.nelsen7 0).chatterjeeXi = 1 := by
  rw [Copula.chatterjeeXi_nelsen7]; norm_num
example : (Copula.nelsen7 1).chatterjeeXi = 0 := by
  rw [Copula.chatterjeeXi_nelsen7]; norm_num
example (θ η : I) : (Copula.nelsen7 θ).SchurBothLE (Copula.nelsen7 η) ↔ η ≤ θ :=
  Copula.schurBothLE_nelsen7_iff
example : (Copula.mardia 0 (by norm_num)).IsCI ∧ (Copula.mardia 0 (by norm_num)).IsCD := by
  constructor
  · rw [Copula.mardia_ci_iff]; exact Or.inl rfl
  · rw [Copula.mardia_cd_iff]; exact Or.inl rfl
example : ¬(Copula.frechet 1 0 (by norm_num) (by norm_num) (by norm_num)).HasMTP2Density := by
  rw [Copula.frechet_density_tp2_iff]; norm_num
example : (Copula.frechet 0 (1/4) (by norm_num) (by norm_num) (by norm_num)).chatterjeeXi +
    (Copula.frechet 0 (1/4) (by norm_num) (by norm_num) (by norm_num)).spearmanFootrule = -(1/16 : ℝ) := by
  rw [Copula.frechet_xi_add_footrule_eq_iff]; exact ⟨rfl, rfl⟩


example (α β : I) : (Copula.marshallOlkin α β).spearmanRho =
    3 * (α : ℝ) * (β : ℝ) /
      (2 * (α : ℝ) + 2 * (β : ℝ) - (α : ℝ) * (β : ℝ)) :=
  Copula.marshallOlkin_spearmanRho α β
example (α : I) : (Copula.marshallOlkin α 0).spearmanRho = 0 := by
  rw [Copula.marshallOlkin_spearmanRho]
  norm_num
example (α β : I) : (Copula.marshallOlkin α β).chatterjeeXi =
    2 * (α : ℝ) ^ 2 * (β : ℝ) /
      (3 * (α : ℝ) + (β : ℝ) - 2 * (α : ℝ) * (β : ℝ)) :=
  Copula.marshallOlkin_chatterjeeXi α β
example (β : I) : (Copula.marshallOlkin 0 β).chatterjeeXi = 0 := by
  rw [Copula.marshallOlkin_chatterjeeXi]
  norm_num
#print axioms ProbabilityTheory.Copula.hasLowerTailDependence_clayton_positive
#print axioms ProbabilityTheory.Copula.hasUpperTailDependence_clayton_positive
#print axioms ProbabilityTheory.Copula.hasLowerTailDependence_clayton_negative
#print axioms ProbabilityTheory.Copula.hasUpperTailDependence_clayton_negative
#print axioms ProbabilityTheory.Copula.not_isCI_clayton_negative
#print axioms ProbabilityTheory.Copula.not_isCD_clayton_positive
#print axioms ProbabilityTheory.Copula.isCD_clayton_negative
#print axioms ProbabilityTheory.Copula.isCI_clayton_positive
#print axioms ProbabilityTheory.Copula.marshallOlkin_chatterjeeXi
#print axioms ProbabilityTheory.Copula.marshallOlkin_spearmanRho
#print axioms ProbabilityTheory.Copula.frechet_density_tp2_iff
#print axioms ProbabilityTheory.Copula.mardia_ci_iff
#print axioms ProbabilityTheory.Copula.chatterjeeXi_nelsen7
#print axioms ProbabilityTheory.Copula.schurBothLE_nelsen7_iff
#print axioms ProbabilityTheory.Copula.frechet_xi_add_footrule_eq_iff

#print axioms ProbabilityTheory.Copula.isTP2CDF_clayton_positive
#print axioms ProbabilityTheory.Copula.not_isTP2CDF_clayton_negative
#print axioms ProbabilityTheory.Copula.not_isNQD_clayton_positive
#print axioms ProbabilityTheory.Copula.not_isPQD_clayton_negative
