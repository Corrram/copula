import Copula.Rank.Region.XiBlest.Support.PartitionCellLaw

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

/-- The patchwork is a weighted sum of affine images of the actual local copula laws. -/
noncomputable def patchworkLaw (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) : Measure (Fin 2 → I) :=
  ∑ i, ∑ j, ENNReal.ofReal (A.mass i j) • partitionCellLaw P Q i j (C i j)

instance (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) (j : Fin n) :
    IsFiniteMeasure (ENNReal.ofReal (A.mass i j) • partitionCellLaw P Q i j (C i j)) := by
  constructor
  simp

instance (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) : IsFiniteMeasure (patchworkLaw A C) := by
  unfold patchworkLaw
  infer_instance

instance (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) : IsProbabilityMeasure (patchworkLaw A C) := by
  constructor
  simp only [patchworkLaw,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  have hj (i : Fin m) : (∑ j, ENNReal.ofReal (A.mass i j)) = ENNReal.ofReal (P.width i) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => A.nonneg i j),A.row_sum]
  simp_rw [hj]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (P.width_pos i).le),P.sum_width]
  norm_num

theorem patchworkLaw_Iic (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (u : Fin 2 → I) :
    patchworkLaw A C (Iic u) = ENNReal.ofReal ((A.patchwork C).cdf u) := by
  simp only [patchworkLaw,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    partitionCellLaw_Iic,CellMass.cdf_patchwork]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (A.nonneg i j) ((C i j).cdf_nonneg _)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (A.nonneg i j) ((C i j).cdf_nonneg _))]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_mul (A.nonneg i j)]

theorem toMeasure_patchworkLaw (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).toMeasure = patchworkLaw A C := by
  let E := A.patchwork C
  have hF (u : Fin 2 → I) : (patchworkLaw A C).real (Iic u)=E.cdf u := by
    rw [Measure.real,patchworkLaw_Iic,ENNReal.toReal_ofReal (E.cdf_nonneg u)]
  let D := E.isClassical_cdf.ofMeasure ⟨patchworkLaw A C,inferInstance⟩ hF
  have he : D=E := Copula.cdf_injective (E.isClassical_cdf.cdf_ofMeasure ⟨patchworkLaw A C,inferInstance⟩ hF)
  rw [show A.patchwork C=E from rfl,← he]
  rfl

theorem integral_patchwork (A : CellMass P Q) (C : Fin m → Fin n → Copula 2)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(A.patchwork C).toMeasure) =
      ∑ i, ∑ j, A.mass i j * ∫ x, f (partitionCellMap P Q i j x) ∂(C i j).toMeasure := by
  rw [toMeasure_patchworkLaw,patchworkLaw,integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_smul_measure,ENNReal.toReal_ofReal (A.nonneg i j),smul_eq_mul,
        integral_partitionCellLaw P Q i j (C i j) hf]
    · intro j _
      exact Copula.integrable_continuous_cube _ hf
  · intro i _
    exact Copula.integrable_continuous_cube _ hf

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
