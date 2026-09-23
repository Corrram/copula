import Copula.Rank.Region.XiBlest.Support.EmpiricalCopulaCDF
import Copula.Rank.Region.XiBlest.Support.FiniteRanks
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Independent observations with uniform marginal laws have no coordinate ties,
simultaneously over every pair in the infinite sample. -/
theorem copulaSample_ae_injective {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Copula 2) (X : ℕ → Ω → (Fin 2 → I))
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i)=C.toMeasure) :
    ∀ᵐ ω ∂μ, ∀ d : Fin 2, Function.Injective (fun i => X i ω d) := by
  have hm (i : ℕ) (d : Fin 2) : Measurable (fun ω => X i ω d) := (measurable_pi_apply d).comp (hX i)
  have hd (i : ℕ) (d : Fin 2) : μ.map (fun ω => X i ω d)=(volume : Measure I) := by
    change μ.map ((fun z : Fin 2 → I => z d) ∘ X i) = _
    rw [← Measure.map_map (measurable_pi_apply d) (hX i),hlaw,Copula.map_eval]
  have hp (d : Fin 2) (i j : ℕ) (hij : i≠j) : ∀ᵐ ω ∂μ, X i ω d ≠ X j ω d := by
    have hh := (hI.comp (fun _ x => x d) (fun _ => measurable_pi_apply d)).indepFun hij
    have hmap := hh.map_prod_eq_prod_map_map (hm i d).aemeasurable (hm j d).aemeasurable
    rw [hd,hd] at hmap
    have hae : ∀ᵐ p : I × I ∂(volume : Measure I).prod volume, p.1 ≠ p.2 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
      exact Filter.Eventually.of_forall fun u => by
        filter_upwards [Measure.ae_ne (volume : Measure I) u] with v hv
        exact Ne.symm hv
    rw [← hmap] at hae
    exact (ae_map_iff ((hm i d).prodMk (hm j d)).aemeasurable
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).mp hae
  have hall (d : Fin 2) (i j : ℕ) : ∀ᵐ ω ∂μ, X i ω d=X j ω d → i=j := by
    by_cases h : i=j
    · exact Filter.Eventually.of_forall fun _ _ => h
    · filter_upwards [hp d i j h] with ω hω
      exact fun he => False.elim (hω he)
  exact ae_all_iff.mpr fun d => ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hall d i j

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
