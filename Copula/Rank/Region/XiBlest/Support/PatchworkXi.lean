import Copula.Rank.Region.XiBlest.Support.PatchworkRow
import Copula.Rank.Region.XiBlest.Support.ConditionalEnergy

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

noncomputable def patchworkRowEnergy (A : CellMass P Q) (C : Fin m → Fin n → Copula 2)
    (i : Fin m) (v : I) : ℝ := ∫ u : I, patchworkRow A C i v u^2

theorem patchworkRowEnergy_measurable (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) :
    Measurable (patchworkRowEnergy A C i) :=
  (patchworkRow_joint_measurable A C i).pow_const 2 |>.stronglyMeasurable.integral_prod_right'.measurable

theorem patchworkRowEnergy_mem (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) (v : I) :
    patchworkRowEnergy A C i v ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun u => sq_nonneg _)
  · calc
      _ ≤ ∫ _u : I, (1 : ℝ) := integral_mono (patchworkRow_sq_integrable A C i v) (integrable_const _) (fun u => by
        have h := patchworkRow_mem A C i v u
        nlinarith [h.1,h.2])
      _ = 1 := by simp

theorem patchworkRowEnergy_integrable_comp (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m)
    {f : I → I} (hf : Measurable f) : Integrable (fun v => patchworkRowEnergy A C i (f v)) := by
  refine (integrable_const (1 : ℝ)).mono' ((patchworkRowEnergy_measurable A C i).comp hf).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs,abs_of_nonneg (patchworkRowEnergy_mem A C i (f v)).1]
    exact (patchworkRowEnergy_mem A C i (f v)).2

theorem patchworkRowEnergy_integral (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) :
    (∫ v : I, patchworkRowEnergy A C i v) =
      ∑ j, Q.width j * ((cellPrefix A i j / P.width i)^2+
        (cellPrefix A i j / P.width i)*(A.mass i j / P.width i)+
        (A.mass i j / P.width i)^2*((C i j).chatterjeeXi+2)/6) := by
  rw [integral_partition Q _ (patchworkRowEnergy_measurable A C i)
    (fun j => patchworkRowEnergy_integrable_comp A C i (partitionEmbed_continuous Q j).measurable)]
  apply Finset.sum_congr rfl
  intro j _
  unfold patchworkRowEnergy
  simp_rw [patchworkRow_embed]
  rw [normalizedCDF_affine_energy]

theorem patchwork_xi_formula (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).chatterjeeXi =
      6*(∑ i, P.width i * ∑ j, Q.width j * ((cellPrefix A i j / P.width i)^2+
        (cellPrefix A i j / P.width i)*(A.mass i j / P.width i)+
        (A.mass i j / P.width i)^2*((C i j).chatterjeeXi+2)/6))-2 := by
  have he (v : I) : (∫ u : I, (A.patchwork C).conditionalCDF u v^2) =
      ∑ i, P.width i * patchworkRowEnergy A C i v := by
    have hae : (fun u => (A.patchwork C).conditionalCDF u v^2) =ᵐ[volume]
        fun u => patchworkKernel A C v u^2 := by
      filter_upwards [patchwork_conditionalCDF A C v] with u hu
      rw [hu]
    rw [integral_congr_ae hae]
    exact integral_partitionSum_sq P (fun i => patchworkRow A C i v)
      (fun i => patchworkRow_measurable A C i v) (fun i => patchworkRow_sq_integrable A C i v)
  rw [Copula.chatterjeeXi]
  simp_rw [he]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul,patchworkRowEnergy_integral]
  · intro i _
    exact (patchworkRowEnergy_integrable_comp A C i measurable_id).const_mul _


theorem patchwork_xi_correction (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).chatterjeeXi = A.checkerboard.chatterjeeXi +
      ∑ i, ∑ j, Q.width j / P.width i * A.mass i j^2 * (C i j).chatterjeeXi := by
  have he (i : Fin m) (j : Fin n) :
      P.width i * (Q.width j * ((cellPrefix A i j / P.width i)^2+
        (cellPrefix A i j / P.width i)*(A.mass i j / P.width i)+
        (A.mass i j / P.width i)^2*((C i j).chatterjeeXi+2)/6)) =
      P.width i * (Q.width j * ((cellPrefix A i j / P.width i)^2+
        (cellPrefix A i j / P.width i)*(A.mass i j / P.width i)+
        (A.mass i j / P.width i)^2*2/6)) +
        (Q.width j / P.width i * A.mass i j^2 * (C i j).chatterjeeXi)/6 := by
    field_simp [(P.width_pos i).ne']
    ring
  rw [patchwork_xi_formula,CellMass.checkerboard,patchwork_xi_formula]
  simp only [Copula.chatterjeeXi_independence,zero_add,Finset.mul_sum]
  simp_rw [he]
  simp only [mul_add,Finset.sum_add_distrib]
  simp_rw [show ∀ x : ℝ, 6*(x/6)=x by intro x; ring]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
