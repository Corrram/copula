import Copula.Rank.Region.XiBlest.Support.SampleNoTies
import Copula.Rank.Region.XiBlest.Support.RankCopulaCDF
import Copula.Rank.Region.XiBlest.Support.EmpiricalCDFRate

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Rank-based empirical copula. Its value on tied samples is immaterial under
continuous marginal laws and is fixed to independence. -/
noncomputable def sampleRankCopula {Ω : Type*} (X : ℕ → Ω → (Fin 2 → I)) (n : ℕ) (ω : Ω) : Copula 2 := by
  classical
  let x : Fin (n+1) → (Fin 2 → I) := fun i => X i.val ω
  exact if h : Function.Injective (fun i => x i 0) ∧ Function.Injective (fun i => x i 1) then
    rankCopula (n+1) (by omega) (finiteRanks _ h.1) (finiteRanks _ h.2)
  else Copula.independence 2

/-- Almost-sure uniform CDF rate for the actual rank-based empirical copula. -/
theorem sampleRankCopula_ae_rate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Copula 2) (X : ℕ → Ω → (Fin 2 → I))
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i)=C.toMeasure) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ u v : I,
      |(sampleRankCopula X n ω).cdf ![u,v]-C.cdf ![u,v]| ≤ 3*empiricalCDFRadius n+8/((n : ℝ)+1) := by
  filter_upwards [copulaSample_ae_injective μ C X hX hI hlaw,empiricalCopulaCDF_ae_rate μ C X hX hI hlaw] with ω hω hrate
  filter_upwards [hrate] with n hn
  intro u v
  have hi (d : Fin 2) : Function.Injective (fun i : Fin (n+1) => X i.val ω d) :=
    (hω d).comp Fin.val_injective
  rw [sampleRankCopula,dite_eq_left ⟨hi 0,hi 1⟩]
  have hh := rankCopula_cdf_error (n+1) (by omega) (finiteRanks _ (hi 0)) (finiteRanks _ (hi 1))
    (fun i : Fin (n+1) => X i.val ω)
    (fun k l => (finiteRanks_le_iff _ (hi 0) k l).symm) (fun k l => (finiteRanks_le_iff _ (hi 1) k l).symm)
    C (empiricalCDFRadius n+2/((n : ℝ)+1)) (by have h := empiricalCDFRadius_nonneg n; positivity)
    (fun s t => by rw [finiteSampleCDF_eq_empirical]; exact hn s t) u v
  simp only [Nat.cast_add,Nat.cast_one] at hh
  convert hh using 1
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
