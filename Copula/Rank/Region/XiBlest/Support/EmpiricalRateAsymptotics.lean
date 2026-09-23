import Copula.Rank.Region.XiBlest.Support.EmpiricalCDFRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem empiricalCDFRadius_scaled_bound (n : ℕ) :
    ((n : ℝ)+2)^(1/3 : ℝ)*empiricalCDFRadius n ≤
      Real.sqrt (16*Real.log ((n : ℝ)+2)/((n : ℝ)+2)^(1/3 : ℝ)) := by
  let b : ℝ := (n : ℝ)+2
  let r : ℝ := b^(1/3 : ℝ)
  have hb : 0<b := by dsimp [b]; positivity
  have hr : 0<r := Real.rpow_pos_of_pos hb _
  have hn : 0<(n : ℝ)+1 := by positivity
  have hl : 0≤Real.log b := Real.log_nonneg (by dsimp [b]; have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hc : r^3=b := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast hb.le]
    norm_num
  have hs : empiricalCDFRadius n^2=8*Real.log b/((n : ℝ)+1) := Real.sq_sqrt (by positivity)
  have he : (r*empiricalCDFRadius n)^2*r*((n : ℝ)+1)=8*Real.log b*b := by
    rw [mul_pow,hs]
    field_simp
    nlinarith [hc]
  have hbN : b ≤ 2*((n : ℝ)+1) := by dsimp [b]; have h := Nat.cast_nonneg (α := ℝ) n; linarith
  have hle : (r*empiricalCDFRadius n)^2*r ≤ 16*Real.log b := by
    apply le_of_mul_le_mul_right (a := (n : ℝ)+1) _ hn
    nlinarith [mul_le_mul_of_nonneg_left hbN (show 0≤8*Real.log b by positivity)]
  have hsle : (r*empiricalCDFRadius n)^2 ≤ 16*Real.log b/r := (le_div_iff₀ hr).mpr hle
  have hrad : 0 ≤ 16*Real.log b/r := by positivity
  have hsq := Real.sq_sqrt hrad
  have hnon := Real.sqrt_nonneg (16*Real.log b/r)
  change r*empiricalCDFRadius n ≤ Real.sqrt (16*Real.log b/r)
  nlinarith

theorem empiricalCDFRadius_scaled_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ)+2)^(1/3 : ℝ)*empiricalCDFRadius n) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop := tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hl := ((isLittleO_log_rpow_atTop (show 0 < (1/3 : ℝ) by norm_num)).tendsto_div_nhds_zero).comp hb
  have hs := (hl.const_mul 16).sqrt
  apply squeeze_zero (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (empiricalCDFRadius_nonneg n))
    empiricalCDFRadius_scaled_bound
  simpa only [Function.comp_def,mul_zero,Real.sqrt_zero,mul_div_assoc] using hs

theorem empiricalMesh_scaled_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ)+2)^(1/3 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have he := ((tendsto_rpow_neg_atTop (show 0 < (2/3 : ℝ) by norm_num)).comp hb).const_mul 2
  apply squeeze_zero (fun n : ℕ => by positivity)
    (fun n : ℕ => (show ((n : ℝ)+2)^(1/3 : ℝ)/((n : ℝ)+1) ≤ 2*((n : ℝ)+2)^(-(2/3 : ℝ)) from ?_))
    (by simpa only [Function.comp_def,mul_zero] using he)
  have hbpos : 0<(n : ℝ)+2 := by positivity
  have hr : 0≤((n : ℝ)+2)^(1/3 : ℝ) := Real.rpow_nonneg hbpos.le _
  have hn : 0<(n : ℝ)+1 := by positivity
  rw [show -(2/3 : ℝ)=(1/3 : ℝ)-1 by norm_num,Real.rpow_sub hbpos,Real.rpow_one]
  rw [div_le_iff₀ hn]
  have ht : ((n : ℝ)+2)^(1/3 : ℝ)*((n : ℝ)+2) ≤ 2*((n : ℝ)+2)^(1/3 : ℝ)*((n : ℝ)+1) := by
    nlinarith [mul_nonneg hr (Nat.cast_nonneg (α := ℝ) n)]
  apply (mul_le_mul_iff_of_pos_right hbpos).mp
  convert ht using 1
  field_simp

theorem empiricalRankRate_scaled_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ)+2)^(1/3 : ℝ)*(3*empiricalCDFRadius n+8/((n : ℝ)+1))) atTop (𝓝 0) := by
  have h := (empiricalCDFRadius_scaled_tendsto.const_mul 3).add (empiricalMesh_scaled_tendsto.const_mul 8)
  convert h using 1
  · funext n
    ring
  · norm_num

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
