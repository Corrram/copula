import Copula.Rank.Region.XiBlest.Support.EmpiricalCopulaCDF
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators ENNReal

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def empiricalCDFRadius (n : ℕ) : ℝ :=
  Real.sqrt (8*Real.log ((n : ℝ)+2)/((n : ℝ)+1))

theorem empiricalCDFRadius_nonneg (n : ℕ) : 0 ≤ empiricalCDFRadius n := Real.sqrt_nonneg _

theorem empiricalCDFRadius_exp (n : ℕ) :
    ((n : ℝ)+2)^2*2*Real.exp (-((n : ℝ)+1)*empiricalCDFRadius n^2/2) = 2/((n : ℝ)+2)^2 := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hn2 : 0 < (n : ℝ)+2 := by positivity
  have hl : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hs : empiricalCDFRadius n^2=8*Real.log ((n : ℝ)+2)/((n : ℝ)+1) :=
    Real.sq_sqrt (by positivity)
  rw [hs]
  have he : -((n : ℝ)+1)*(8*Real.log ((n : ℝ)+2)/((n : ℝ)+1))/2 = -(4*Real.log ((n : ℝ)+2)) := by
    field_simp
    ring
  rw [he,Real.exp_neg,show (4 : ℝ)*Real.log ((n : ℝ)+2)=(4 : ℕ)*Real.log ((n : ℝ)+2) from rfl,
    Real.exp_nat_mul,Real.exp_log hn2]
  field_simp

theorem empiricalCDFRadius_summable : Summable (fun n : ℕ => 2/((n : ℝ)+2)^2) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by omega)
  have hh := (summable_nat_add_iff 2).mpr h
  simpa only [Nat.cast_add,Nat.cast_ofNat,mul_one_div] using hh.mul_left 2

/-- Uniform empirical CDF control almost surely, obtained from a growing finite
grid, Hoeffding's inequality and Borel-Cantelli. No empirical convergence is assumed. -/
theorem empiricalCopulaCDF_ae_rate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Copula 2) (X : ℕ → Ω → (Fin 2 → I))
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i)=C.toMeasure) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ u v : I,
      |empiricalCopulaCDF X (n+1) ω ![u,v]-C.cdf ![u,v]| ≤ empiricalCDFRadius n+2/((n : ℝ)+1) := by
  let P (n : ℕ) := IntervalPartition.uniform (n+1) (by omega)
  let bad (n : ℕ) : Set Ω := {ω | ∃ t : Fin (n+2) × Fin (n+2), empiricalCDFRadius n ≤
    |empiricalCopulaCDF X (n+1) ω ![(P n).point t.1,(P n).point t.2]-C.cdf ![(P n).point t.1,(P n).point t.2]|}
  have hbound (n : ℕ) : μ.real (bad n) ≤ 2/((n : ℝ)+2)^2 := by
    have h := empiricalCopulaCDF_grid_deviation μ C X hX hI hlaw
      (fun t : Fin (n+2) × Fin (n+2) => ![(P n).point t.1,(P n).point t.2])
      (n+1) (by omega) (empiricalCDFRadius n) (empiricalCDFRadius_nonneg n)
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at h
    rw [← sq] at h
    exact h.trans_eq (empiricalCDFRadius_exp n)
  have hs : (∑' n, μ (bad n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top empiricalCDFRadius_summable.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro n
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (bad n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  filter_upwards [ae_eventually_notMem hs] with ω hω
  filter_upwards [hω] with n hn
  intro u v
  have hg (i j : Fin (n+2)) :
      |empiricalCopulaCDF X (n+1) ω ![(P n).point i,(P n).point j]-C.cdf ![(P n).point i,(P n).point j]| ≤
        empiricalCDFRadius n := by
    have hh : ¬ empiricalCDFRadius n ≤
        |empiricalCopulaCDF X (n+1) ω ![(P n).point i,(P n).point j]-C.cdf ![(P n).point i,(P n).point j]| := by
      intro hh
      exact hn ⟨(i,j),hh⟩
    exact (lt_of_not_ge hh).le
  have h := cdf_grid_error_bound C (empiricalCopulaCDF X (n+1) ω) (empiricalCopulaCDF_mono X (n+1) ω)
    (P n) (P n) (empiricalCDFRadius n) (1/((n : ℝ)+1)) (1/((n : ℝ)+1))
    (fun i => by simp [P,IntervalPartition.width_uniform]) (fun i => by simp [P,IntervalPartition.width_uniform]) hg u v
  convert h using 1
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
