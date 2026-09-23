import Copula.Rank.Region.XiBlest.Support.RankCopula
import Copula.Rank.Region.XiBlest.Support.EmpiricalCopulaCDF

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def finiteSampleCDF {n : ℕ} (x : Fin n → (Fin 2 → I)) (t : Fin 2 → I) : ℝ :=
  (1/(n : ℝ))*∑ k, lowerCubeIndicator t (x k)

theorem finiteSampleCDF_eq_empirical {Ω : Type*} (X : ℕ → Ω → (Fin 2 → I)) (n : ℕ) (ω : Ω) (t : Fin 2 → I) :
    finiteSampleCDF (fun k : Fin n => X k.val ω) t=empiricalCopulaCDF X n ω t := by
  unfold finiteSampleCDF empiricalCopulaCDF empiricalMean
  rw [Fin.sum_univ_eq_sum_range (fun k => lowerCubeIndicator t (X k ω)) n]
  ring

theorem lowerCubeIndicator_two (x : Fin 2 → I) (u v : I) :
    lowerCubeIndicator ![u,v] x = if x 0 ≤ u ∧ x 1 ≤ v then 1 else 0 := by
  have he : x ∈ Iic ![u,v] ↔ x 0 ≤ u ∧ x 1 ≤ v := by
    change (∀ i, x i ≤ ![u,v] i) ↔ _
    simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [lowerCubeIndicator,Set.indicator,he]

/-- Exact link between rank-grid CDF values and empirical order-statistic thresholds. -/
theorem rankCopula_cdf_grid (n : ℕ) (hn : 0<n) (rx ry : Equiv.Perm (Fin n))
    (x : Fin n → (Fin 2 → I)) (i j : Fin (n+1)) (u v : I)
    (hx : ∀ k, x k 0 ≤ u ↔ (rx k).val < i.val)
    (hy : ∀ k, x k 1 ≤ v ↔ (ry k).val < j.val) :
    (rankCopula n hn rx ry).cdf ![(IntervalPartition.uniform n hn).point i,(IntervalPartition.uniform n hn).point j] =
      finiteSampleCDF x ![u,v] := by
  rw [rankCopula_cdf]
  unfold finiteSampleCDF
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [IntervalPartition.coord_point,lowerCubeIndicator_two,hx,hy]
  by_cases h1 : (rx k).val < i.val <;> by_cases h2 : (ry k).val < j.val <;> simp [h1,h2]

/-- Rank transformation preserves uniform CDF approximation, up to the fine-grid mesh. -/
theorem rankCopula_cdf_error (n : ℕ) (hn : 0<n) (rx ry : Equiv.Perm (Fin n))
    (x : Fin n → (Fin 2 → I))
    (hx : ∀ k l, x k 0 ≤ x l 0 ↔ rx k ≤ rx l)
    (hy : ∀ k l, x k 1 ≤ x l 1 ↔ ry k ≤ ry l)
    (C : Copula 2) (δ : ℝ) (hδ : 0≤δ)
    (hCDF : ∀ u v, |finiteSampleCDF x ![u,v]-C.cdf ![u,v]| ≤ δ) (u v : I) :
    |(rankCopula n hn rx ry).cdf ![u,v]-C.cdf ![u,v]| ≤ 3*δ+2/(n : ℝ) := by
  let P := IntervalPartition.uniform n hn
  have hg (i j : Fin (n+1)) :
      |(rankCopula n hn rx ry).cdf ![P.point i,P.point j]-C.cdf ![P.point i,P.point j]| ≤ 3*δ := by
    by_cases hi : i.val=0
    · have hi' : i=0 := Fin.ext hi
      simp only [hi',P.zero,Copula.cdf_two_zero_left,sub_self,abs_zero]
      positivity
    by_cases hj : j.val=0
    · have hj' : j=0 := Fin.ext hj
      simp only [hj',P.zero,Copula.cdf_two_zero_right,sub_self,abs_zero]
      positivity
    let a : Fin n := ⟨i.val-1,by omega⟩
    let b : Fin n := ⟨j.val-1,by omega⟩
    let s := x (rx.symm a) 0
    let t := x (ry.symm b) 1
    have hs (k : Fin n) : x k 0 ≤ s ↔ (rx k).val < i.val := by
      rw [hx]
      simp only [Equiv.apply_symm_apply]
      change (rx k).val ≤ i.val-1 ↔ (rx k).val < i.val
      omega
    have ht (k : Fin n) : x k 1 ≤ t ↔ (ry k).val < j.val := by
      rw [hy]
      simp only [Equiv.apply_symm_apply]
      change (ry k).val ≤ j.val-1 ↔ (ry k).val < j.val
      omega
    have hx1 := rankCopula_cdf_grid n hn rx ry x i (Fin.last n) s 1 hs
      (fun k => iff_of_true (x k 1).property.2 (ry k).is_lt)
    have hy1 := rankCopula_cdf_grid n hn rx ry x (Fin.last n) j 1 t
      (fun k => iff_of_true (x k 0).property.2 (rx k).is_lt) ht
    simp only [IntervalPartition.one,Copula.cdf_two_one_right] at hx1
    simp only [IntervalPartition.one,Copula.cdf_two_one_left] at hy1
    have hxs : |(P.point i : ℝ)-(s : ℝ)| ≤ δ := by
      have hh := hCDF s 1
      rw [← hx1,Copula.cdf_two_one_right] at hh
      exact hh
    have hyt : |(P.point j : ℝ)-(t : ℝ)| ≤ δ := by
      have hh := hCDF 1 t
      rw [← hy1,Copula.cdf_two_one_left] at hh
      exact hh
    have he := rankCopula_cdf_grid n hn rx ry x i j s t hs ht
    have hc := C.abs_cdf_sub_le_sum_abs ![s,t] ![P.point i,P.point j]
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hc
    rw [abs_sub_comm (s : ℝ),abs_sub_comm (t : ℝ)] at hc
    rw [he]
    have hh := abs_add_le (finiteSampleCDF x ![s,t]-C.cdf ![s,t])
      (C.cdf ![s,t]-C.cdf ![P.point i,P.point j])
    rw [sub_add_sub_cancel] at hh
    linarith [hCDF s t]
  have h := cdf_grid_error_bound C (rankCopula n hn rx ry).cdf (rankCopula n hn rx ry).monotone_cdf
    P P (3*δ) (1/(n : ℝ)) (1/(n : ℝ))
    (fun i => by simp [P,IntervalPartition.width_uniform]) (fun i => by simp [P,IntervalPartition.width_uniform]) hg u v
  convert h using 1
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
