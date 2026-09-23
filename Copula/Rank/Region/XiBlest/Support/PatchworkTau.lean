import Copula.Rank.Region.XiBlest.Support.PatchworkLaw
import Copula.Rank.Region.XiBlest.Support.PartitionCoordEmbed
import Copula.Rank.Benchmarks

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def orderHalf {n : ℕ} (r i : Fin n) : ℝ :=
  if r < i then 1 else if r=i then 1/2 else 0

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem patchwork_cell_cdf_integral (C : Fin m → Fin n → Copula 2) (i r : Fin m) (j s : Fin n) :
    (∫ x, (C r s).cdf ![P.coord r (partitionEmbed P i (x 0)),Q.coord s (partitionEmbed Q j (x 1))]
      ∂(C i j).toMeasure) = orderHalf r i * orderHalf s j +
        if r=i ∧ s=j then (C i j).kendallTau/4 else 0 := by
  have he (x : Fin 2 → I) : ![x 0,x 1]=x := by ext a; fin_cases a <;> rfl
  rcases lt_trichotomy r i with hri | rfl | hir <;> rcases lt_trichotomy s j with hsj | rfl | hjs
  all_goals try have hri0 := ne_of_lt hri
  all_goals try have hsj0 := ne_of_lt hsj
  all_goals try have hir0 := ne_of_gt hir
  all_goals try have hir1 := not_lt_of_gt hir
  all_goals try have hjs0 := ne_of_gt hjs
  all_goals try have hjs1 := not_lt_of_gt hjs
  all_goals simp_all [partition_coord_embed,orderHalf,Copula.integral_coe_eval,not_lt_of_ge]
  rw [Copula.kendallTau]
  ring

theorem patchwork_tau_formula (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).kendallTau =
      4*(∑ i, ∑ j, ∑ r, ∑ s, A.mass i j*A.mass r s*orderHalf r i*orderHalf s j)-1 +
        ∑ i, ∑ j, A.mass i j^2*(C i j).kendallTau := by
  rw [Copula.kendallTau,integral_patchwork A C (A.patchwork C).continuous_cdf]
  have hcell (i : Fin m) (j : Fin n) :
      (∫ x, (A.patchwork C).cdf (partitionCellMap P Q i j x) ∂(C i j).toMeasure) =
      (∑ r, ∑ s, A.mass r s*orderHalf r i*orderHalf s j) + A.mass i j*(C i j).kendallTau/4 := by
    simp only [CellMass.cdf_patchwork,partitionCellMap,Matrix.cons_val_zero,Matrix.cons_val_one]
    have hcont (r : Fin m) (s : Fin n) : Continuous (fun x : Fin 2 → I =>
        (C r s).cdf ![P.coord r (partitionEmbed P i (x 0)),Q.coord s (partitionEmbed Q j (x 1))]) := by
      apply (C r s).continuous_cdf.comp
      apply continuous_pi
      intro b
      fin_cases b
      all_goals dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
      all_goals unfold IntervalPartition.coord partitionEmbed; fun_prop
    simp (disch := intro a ha; exact Copula.integrable_continuous_cube _ (by fun_prop)) only [integral_finsetSum]
    simp_rw [integral_const_mul,patchwork_cell_cdf_integral,mul_add]
    simp only [Finset.sum_add_distrib,mul_ite,mul_zero,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [mul_assoc]
    ring
  have hb : (∑ i, ∑ j, A.mass i j * (∑ r, ∑ s, A.mass r s*orderHalf r i*orderHalf s j)) =
      ∑ i, ∑ j, ∑ r, ∑ s, A.mass i j*A.mass r s*orderHalf r i*orderHalf s j := by
    simp only [Finset.mul_sum,mul_assoc]
  have hc : (∑ i, ∑ j, A.mass i j * (A.mass i j*(C i j).kendallTau/4)) =
      (∑ i, ∑ j, A.mass i j^2*(C i j).kendallTau)/4 := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hcell,mul_add,Finset.sum_add_distrib]
  rw [hb,hc]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
