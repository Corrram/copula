import Copula.Rank.Region.XiBlest.Support.PermutationShuffle
import Copula.Rank.Region.XiBlest.Support.SampleRankCopula
import Copula.Rank.Region.XiBlest.Support.EmpiricalRateAsymptotics
import Mathlib.Probability.HasLawExists

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem uniform_stripCut_coord (n : ℕ) (i : Fin (n+1)) (u : I) :
    stripCut (1/((n : ℝ)+1)) ((i : ℝ)/(n+1)) u =
      (1/((n : ℝ)+1))*((IntervalPartition.uniform (n+1) (by omega)).coord i u : ℝ) := by
  rw [stripCut_eq_min_sub (by positivity)]
  have h := (IntervalPartition.uniform (n+1) (by omega)).width_mul_coord i u
  rw [IntervalPartition.width_uniform] at h
  have hp0 : ((IntervalPartition.uniform (n+1) (by omega)).point i.castSucc : ℝ)=(i : ℝ)/((n : ℝ)+1) := by
    change (i.val : ℝ)/((n+1 : ℕ) : ℝ)=_
    norm_num only [Nat.cast_add,Nat.cast_one]
  have hp1 : ((IntervalPartition.uniform (n+1) (by omega)).point i.succ : ℝ)=((i : ℝ)+1)/((n : ℝ)+1) := by
    change ((i.val+1 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)=_
    norm_num only [Nat.cast_add,Nat.cast_one]
  rw [hp0,hp1] at h
  norm_num only [Nat.cast_add,Nat.cast_one] at h
  rw [← add_div]
  exact h.symm

theorem permutationShuffle_eq_rankCheckMin (n : ℕ) (rx ry : Equiv.Perm (Fin (n+1))) :
    PermutationShuffle.copula n (rx.symm.trans ry)=(rankCellMass (n+1) (by omega) rx ry).checkMin := by
  apply Copula.ext_cdf
  intro u
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  rw [hu,PermutationShuffle.copula,PositiveShuffle.cdf,CellMass.cdf_checkMin]
  simp only [PermutationShuffle.shuffle,PermutationShuffle.strip,Matrix.cons_val_zero,Matrix.cons_val_one,
    rankCellMass,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [uniform_stripCut_coord,← mul_min_of_nonneg _ _ (show 0≤1/((n : ℝ)+1) by positivity),
    Equiv.trans_apply,Nat.cast_add,Nat.cast_one]

theorem rankCheckMin_cdf_error (n : ℕ) (rx ry : Equiv.Perm (Fin (n+1))) (u v : I) :
    |(rankCellMass (n+1) (by omega) rx ry).checkMin.cdf ![u,v]-(rankCopula (n+1) (by omega) rx ry).cdf ![u,v]| ≤
      2/((n : ℝ)+1) := by
  let P := IntervalPartition.uniform (n+1) (by omega)
  let A := rankCellMass (n+1) (by omega) rx ry
  have hg (i j : Fin (n+2)) : A.checkMin.cdf ![P.point i,P.point j]=A.checkerboard.cdf ![P.point i,P.point j] := by
    unfold CellMass.checkMin CellMass.checkerboard
    rw [CellMass.cdf_patchwork_point,CellMass.cdf_patchwork_point]
  have h := cdf_grid_error_bound A.checkerboard A.checkMin.cdf A.checkMin.monotone_cdf P P 0
    (1/((n : ℝ)+1)) (1/((n : ℝ)+1))
    (fun i => by simp [P,IntervalPartition.width_uniform,Nat.cast_add,Nat.cast_one])
    (fun i => by simp [P,IntervalPartition.width_uniform,Nat.cast_add,Nat.cast_one])
    (fun i j => by rw [hg]; simp) u v
  change |A.checkMin.cdf ![u,v]-A.checkerboard.cdf ![u,v]| ≤ _
  convert h using 1
  ring

/-- A quantitative uniform approximation by actual equal-width permutation shuffles. -/
theorem exists_permutationShuffle_approximation (C : Copula 2) :
    ∃ π : (n : ℕ) → Equiv.Perm (Fin (n+1)), ∀ᶠ n in atTop, ∀ u v : I,
      |(PermutationShuffle.copula n (π n)).cdf ![u,v]-C.cdf ![u,v]| ≤
        3*empiricalCDFRadius n+10/((n : ℝ)+1) := by
  obtain ⟨Ω,mΩ,μ,X,hX,hLaw,hI,hμ⟩ := exists_iid ℕ C.toMeasure
  let := mΩ
  let := hμ
  have hL (i : ℕ) : μ.map (X i)=C.toMeasure := (hLaw i).map_eq
  have hae := (sampleRankCopula_ae_rate μ C X hX hI hL).and (copulaSample_ae_injective μ C X hX hI hL)
  obtain ⟨ω,hω,hi⟩ := hae.exists
  let rx (n : ℕ) : Equiv.Perm (Fin (n+1)) := finiteRanks (fun i => X i.val ω 0) ((hi 0).comp Fin.val_injective)
  let ry (n : ℕ) : Equiv.Perm (Fin (n+1)) := finiteRanks (fun i => X i.val ω 1) ((hi 1).comp Fin.val_injective)
  refine ⟨fun n => (rx n).symm.trans (ry n),?_⟩
  filter_upwards [hω] with n hn
  intro u v
  have hs : sampleRankCopula X n ω=rankCopula (n+1) (by omega) (rx n) (ry n) := by
    rw [sampleRankCopula,dite_eq_left ⟨(hi 0).comp Fin.val_injective,(hi 1).comp Fin.val_injective⟩]
  have hrate := hn u v
  rw [hs] at hrate
  rw [permutationShuffle_eq_rankCheckMin]
  have htri := abs_sub_le ((rankCellMass (n+1) (by omega) (rx n) (ry n)).checkMin.cdf ![u,v])
    ((rankCopula (n+1) (by omega) (rx n) (ry n)).cdf ![u,v]) (C.cdf ![u,v])
  have he := rankCheckMin_cdf_error n (rx n) (ry n) u v
  calc
    _ ≤ 2/((n : ℝ)+1)+(3*empiricalCDFRadius n+8/((n : ℝ)+1)) := htri.trans (add_le_add he hrate)
    _ = _ := by ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
