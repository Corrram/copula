import Copula.Rank.Region.XiBlest.Support.RowEnergyConvergence

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ}

theorem copulaRowMean_mono (P : IntervalPartition m) (C : Copula 2) (i : Fin m) :
    Monotone (copulaRowMean P C i) := by
  intro v w hvw
  rw [copulaRowMean_integral,copulaRowMean_integral]
  apply integral_mono (conditionalCDF_embed_integrable P C i v) (conditionalCDF_embed_integrable P C i w)
  intro u
  exact measureReal_mono (Iic_subset_Iic.mpr hvw)

theorem copulaRowMean_total (P : IntervalPartition m) (C : Copula 2) (v : I) :
    (∑ i, P.width i*copulaRowMean P C i v) = v := by
  have he (i : Fin m) : P.width i*copulaRowMean P C i v =
      C.cdf ![P.point i.succ,v]-C.cdf ![P.point i.castSucc,v] := by
    unfold copulaRowMean
    field_simp [(P.width_pos i).ne']
  simp_rw [he]
  rw [IntervalPartition.sum_differences (fun k => C.cdf ![P.point k,v])]
  simp only [P.one,P.zero,Copula.cdf_two_one_left,Copula.cdf_two_zero_left,sub_zero]

theorem checkerboardRow_interpolation_error (P : IntervalPartition m) (Q : IntervalPartition n)
    (C : Copula 2) (i : Fin m) (j : Fin n) (v : I) :
    |checkerboardRow (C.cellMass P Q) i (partitionEmbed Q j v)-copulaRowMean P C i (partitionEmbed Q j v)| ≤
      copulaRowMean P C i (Q.point j.succ)-copulaRowMean P C i (Q.point j.castSucc) := by
  rw [checkerboardRow_embed,checkerboardRow_grid,checkerboardRow_grid]
  have h0 := copulaRowMean_mono P C i (partitionEmbed_lower Q j v)
  have h1 := copulaRowMean_mono P C i (partitionEmbed_upper Q j v)
  have hp := mul_nonneg v.property.1 (sub_nonneg.mpr (h0.trans h1))
  have hq := mul_nonneg (sub_nonneg.mpr v.property.2) (sub_nonneg.mpr (h0.trans h1))
  rw [abs_le]
  constructor <;> nlinarith

theorem checkerboard_energy_interpolation_error_embed (P : IntervalPartition m) (Q : IntervalPartition n)
    (C : Copula 2) (j : Fin n) (v : I) :
    |conditionalEnergy (C.cellMass P Q).checkerboard (partitionEmbed Q j v)-rowMeanEnergy P C (partitionEmbed Q j v)| ≤
      2*Q.width j := by
  let w := partitionEmbed Q j v
  have hd (i : Fin m) : |checkerboardRow (C.cellMass P Q) i w^2-copulaRowMean P C i w^2| ≤
      2*(copulaRowMean P C i (Q.point j.succ)-copulaRowMean P C i (Q.point j.castSucc)) := by
    have h := checkerboardRow_interpolation_error P Q C i j v
    have h1 := sq_sub_le_of_mem_unit (checkerboardRow_mem (C.cellMass P Q) i w) (copulaRowMean_mem P C i w) h
    have h2 := sq_sub_le_of_mem_unit
      (δ := copulaRowMean P C i (Q.point j.succ)-copulaRowMean P C i (Q.point j.castSucc)) (copulaRowMean_mem P C i w) (checkerboardRow_mem (C.cellMass P Q) i w)
      (by rw [abs_sub_comm]; exact h)
    rw [abs_le]
    constructor <;> linarith
  unfold conditionalEnergy rowMeanEnergy
  rw [checkerboard_conditional_energy,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |P.width i*checkerboardRow (C.cellMass P Q) i w^2-P.width i*copulaRowMean P C i w^2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, P.width i*|checkerboardRow (C.cellMass P Q) i w^2-copulaRowMean P C i w^2| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub,abs_mul,abs_of_pos (P.width_pos i)]
    _ ≤ ∑ i, P.width i*(2*(copulaRowMean P C i (Q.point j.succ)-copulaRowMean P C i (Q.point j.castSucc))) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hd i) (P.width_pos i).le
    _ = 2*Q.width j := by
      simp only [mul_sub,Finset.sum_sub_distrib]
      simp_rw [show ∀ a b : ℝ, a*(2*b)=2*(a*b) by intro a b; ring]
      rw [← Finset.mul_sum,← Finset.mul_sum,copulaRowMean_total,copulaRowMean_total]
      unfold IntervalPartition.width
      ring

theorem partitionEmbed_exists (P : IntervalPartition m) (v : I) :
    ∃ (i : Fin m) (u : I), partitionEmbed P i u=v := by
  obtain ⟨i,hi⟩ := P.exists_cell v
  refine ⟨i,P.coord i v,?_⟩
  apply Subtype.ext
  change (P.point i.castSucc : ℝ)+P.width i*(P.coord i v : ℝ)=(v : ℝ)
  rw [P.coe_coord_of_mem i v hi.1 hi.2]
  field_simp [(P.width_pos i).ne']
  ring

theorem checkerboard_energy_interpolation_error (P : IntervalPartition m) (C : Copula 2) (n : ℕ) (v : I) :
    |conditionalEnergy (C.cellMass P (IntervalPartition.uniform (n+1) (by omega))).checkerboard v-rowMeanEnergy P C v| ≤
      2/((n : ℝ)+1) := by
  let Q := IntervalPartition.uniform (n+1) (by omega)
  obtain ⟨j,u,hu⟩ := partitionEmbed_exists Q v
  have h := checkerboard_energy_interpolation_error_embed P Q C j u
  rw [hu] at h
  simpa only [Q,IntervalPartition.width_uniform,Nat.cast_add,Nat.cast_one,mul_one_div] using h

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
