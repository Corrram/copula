import Copula.Rank.Region.XiBlest.Support.CheckerboardRows
import Copula.Rank.Region.XiBlest.Support.PatchworkXi
import Copula.Rank.ConditionalMixture

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem patchworkRow_independence (A : CellMass P Q) (i : Fin m) (v : I) :
    patchworkRow A (fun _ _ => Copula.independence 2) i v =ᵐ[volume]
      fun _ => checkerboardRow A i v := by
  have h (j : Fin n) : (fun u => normalizedCDF (Copula.independence 2) u (Q.coord j v)) =ᵐ[volume]
      fun _ => (Q.coord j v : ℝ) :=
    (normalizedCDF_ae _ _).trans (Copula.conditionalCDF_independence _)
  filter_upwards [ae_all_iff.mpr h] with u hu
  unfold patchworkRow checkerboardRow
  simp only [hu]

theorem checkerboard_conditional_energy (A : CellMass P Q) (v : I) :
    (∫ u : I, A.checkerboard.conditionalCDF u v^2) = ∑ i, P.width i * checkerboardRow A i v^2 := by
  have hae : (fun u => A.checkerboard.conditionalCDF u v^2) =ᵐ[volume]
      fun u => patchworkKernel A (fun _ _ => Copula.independence 2) v u^2 :=
    (patchwork_conditionalCDF A (fun _ _ => Copula.independence 2) v).fun_comp (fun x : ℝ => x^2)
  rw [integral_congr_ae hae]
  rw [show (∫ u : I, patchworkKernel A (fun _ _ => Copula.independence 2) v u^2) =
      ∑ i, P.width i * ∫ u : I, patchworkRow A (fun _ _ => Copula.independence 2) i v u^2 from
    integral_partitionSum_sq P _ (fun i => patchworkRow_measurable A _ i v)
      (fun i => patchworkRow_sq_integrable A _ i v)]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun u => patchworkRow A (fun _ _ => Copula.independence 2) i v u^2) =ᵐ[volume]
      fun _ => checkerboardRow A i v^2 :=
    (patchworkRow_independence A i v).fun_comp (fun x : ℝ => x^2)
  rw [integral_congr_ae he]
  simp

noncomputable def conditionalEnergy (C : Copula 2) (v : I) : ℝ := ∫ u : I, C.conditionalCDF u v^2

theorem conditionalEnergy_measurable (C : Copula 2) : Measurable (conditionalEnergy C) :=
  C.measurable_conditionalCDF.pow_const 2 |>.stronglyMeasurable.integral_prod_right'.measurable

theorem conditionalEnergy_mem (C : Copula 2) (v : I) : conditionalEnergy C v ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun _ => sq_nonneg _
  · calc
      _ ≤ ∫ _u : I, (1 : ℝ) := integral_mono (C.integrable_conditionalCDF_sq v) (integrable_const _) (fun u => by
        nlinarith [C.conditionalCDF_nonneg u v,C.conditionalCDF_le_one u v])
      _ = 1 := by simp

theorem conditionalEnergy_integrable_comp (C : Copula 2) {f : I → I} (hf : Measurable f) :
    Integrable (fun v => conditionalEnergy C (f v)) := by
  refine (integrable_const (1 : ℝ)).mono' ((conditionalEnergy_measurable C).comp hf).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs,abs_of_nonneg (conditionalEnergy_mem C (f v)).1]
    exact (conditionalEnergy_mem C (f v)).2

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
