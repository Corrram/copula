import Copula.Rank.Region.XiBlest.Support.CheckerboardEnergy

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem checkerboardRow_mem (A : CellMass P Q) (i : Fin m) (v : I) :
    checkerboardRow A i v ∈ Icc (0 : ℝ) 1 := by
  have hw := (P.width_pos i).le
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (div_nonneg (A.nonneg i j) hw) (Q.coord j v).property.1)
  · calc
      _ ≤ ∑ j, A.mass i j / P.width i * 1 := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (Q.coord j v).property.2 (div_nonneg (A.nonneg i j) hw))
      _ = 1 := by simp only [mul_one,← Finset.sum_div,A.row_sum,div_self (P.width_pos i).ne']

theorem copulaRowMean_sub_le (C D : Copula 2) (P : IntervalPartition m)
    (ε : ℝ) (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε) (i : Fin m) (v : I) :
    |copulaRowMean P C i v-copulaRowMean P D i v| ≤ 2*ε/P.width i := by
  have h1 := abs_le.mp (h (P.point i.succ) v)
  have h0 := abs_le.mp (h (P.point i.castSucc) v)
  unfold copulaRowMean
  rw [← sub_div,abs_div,abs_of_pos (P.width_pos i)]
  apply (div_le_div_iff_of_pos_right (P.width_pos i)).mpr
  rw [abs_le]
  constructor <;> linarith [h1.1,h1.2,h0.1,h0.2]

theorem checkerboardRow_sub_le_embed (C D : Copula 2) (P : IntervalPartition m) (Q : IntervalPartition n)
    (ε : ℝ) (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε)
    (i : Fin m) (j : Fin n) (v : I) :
    |checkerboardRow (C.cellMass P Q) i (partitionEmbed Q j v)-
      checkerboardRow (D.cellMass P Q) i (partitionEmbed Q j v)| ≤ 2*ε/P.width i := by
  simp only [checkerboardRow_embed,checkerboardRow_grid]
  have h0 := copulaRowMean_sub_le C D P ε h i (Q.point j.castSucc)
  have h1 := copulaRowMean_sub_le C D P ε h i (Q.point j.succ)
  have he (a b c d : ℝ) : (1-(v : ℝ))*a+(v : ℝ)*b-((1-(v : ℝ))*c+(v : ℝ)*d) =
      (1-(v : ℝ))*(a-c)+(v : ℝ)*(b-d) := by ring
  rw [he]
  calc
    _ ≤ |(1-(v : ℝ))*(_-_)|+|(v : ℝ)*(_-_)| := abs_add_le _ _
    _ = (1-(v : ℝ))*|_-_|+(v : ℝ)*|_-_| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr v.property.2),abs_of_nonneg v.property.1]
    _ ≤ (1-(v : ℝ))*(2*ε/P.width i)+(v : ℝ)*(2*ε/P.width i) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr v.property.2))
        (mul_le_mul_of_nonneg_left h1 v.property.1)
    _ = _ := by ring

theorem sq_sub_le_of_mem_unit {a b δ : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (_hb : b ∈ Icc (0 : ℝ) 1)
    (hδ : |a-b| ≤ δ) : a^2 ≤ b^2+2*δ := by
  have hn : 0 ≤ δ := (abs_nonneg _).trans hδ
  have h := (abs_le.mp hδ).2
  by_cases hab : a ≤ b
  · nlinarith [ha.1,_hb.1]
  · have hab' : 0 ≤ a-b := sub_nonneg.mpr (le_of_not_ge hab)
    have hh := mul_le_mul_of_nonneg_left (show a+b ≤ 2 by linarith [ha.2,_hb.2]) hab'
    nlinarith

theorem checkerboard_energy_stability_embed (C D : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (ε : ℝ) (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε)
    (j : Fin n) (v : I) :
    conditionalEnergy (C.cellMass P Q).checkerboard (partitionEmbed Q j v) ≤
      conditionalEnergy (D.cellMass P Q).checkerboard (partitionEmbed Q j v)+4*(m : ℝ)*ε := by
  unfold conditionalEnergy
  rw [checkerboard_conditional_energy,checkerboard_conditional_energy]
  calc
    _ ≤ ∑ i, (P.width i*checkerboardRow (D.cellMass P Q) i (partitionEmbed Q j v)^2+4*ε) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := mul_le_mul_of_nonneg_left
        (sq_sub_le_of_mem_unit (checkerboardRow_mem (C.cellMass P Q) i _) (checkerboardRow_mem (D.cellMass P Q) i _)
          (checkerboardRow_sub_le_embed C D P Q ε h i j v)) (P.width_pos i).le
      have he : P.width i*(checkerboardRow (D.cellMass P Q) i (partitionEmbed Q j v)^2+2*(2*ε/P.width i)) =
          P.width i*checkerboardRow (D.cellMass P Q) i (partitionEmbed Q j v)^2+4*ε := by
        field_simp [(P.width_pos i).ne']
        ring
      rwa [he] at hh
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem checkerboard_xi_stability_le (C D : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (ε : ℝ) (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε) :
    (C.cellMass P Q).checkerboard.chatterjeeXi ≤ (D.cellMass P Q).checkerboard.chatterjeeXi+24*(m : ℝ)*ε := by
  let C' := (C.cellMass P Q).checkerboard
  let D' := (D.cellMass P Q).checkerboard
  have he : (∫ v : I, conditionalEnergy C' v) ≤ (∫ v : I, conditionalEnergy D' v)+4*(m : ℝ)*ε := by
    rw [integral_partition Q _ (conditionalEnergy_measurable C')
      (fun j => conditionalEnergy_integrable_comp C' (partitionEmbed_continuous Q j).measurable),
      integral_partition Q _ (conditionalEnergy_measurable D')
      (fun j => conditionalEnergy_integrable_comp D' (partitionEmbed_continuous Q j).measurable)]
    calc
      _ ≤ ∑ j, Q.width j*((∫ v : I, conditionalEnergy D' (partitionEmbed Q j v))+4*(m : ℝ)*ε) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (Q.width_pos j).le
        have hh := integral_mono
          (conditionalEnergy_integrable_comp C' (partitionEmbed_continuous Q j).measurable)
          ((conditionalEnergy_integrable_comp D' (partitionEmbed_continuous Q j).measurable).add (integrable_const (4*(m : ℝ)*ε)))
          (checkerboard_energy_stability_embed C D P Q ε h j)
        simp only [Pi.add_apply] at hh
        rw [integral_add (conditionalEnergy_integrable_comp D' (partitionEmbed_continuous Q j).measurable)
          (integrable_const (4*(m : ℝ)*ε))] at hh
        simpa using hh
      _ = _ := by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,Q.sum_width,one_mul]
  change 6*(∫ v : I, conditionalEnergy C' v)-2 ≤ 6*(∫ v : I, conditionalEnergy D' v)-2+24*(m : ℝ)*ε
  linarith

/-- Stability on arbitrary partitions; the constant depends only on the number of predictor bins. -/
theorem checkerboard_xi_stability (C D : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (ε : ℝ) (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε) :
    |(C.cellMass P Q).checkerboard.chatterjeeXi-(D.cellMass P Q).checkerboard.chatterjeeXi| ≤ 24*(m : ℝ)*ε := by
  have hCD := checkerboard_xi_stability_le C D P Q ε h
  have hDC := checkerboard_xi_stability_le D C P Q ε (fun u v => by rw [abs_sub_comm]; exact h u v)
  rw [abs_le]
  constructor <;> linarith

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
