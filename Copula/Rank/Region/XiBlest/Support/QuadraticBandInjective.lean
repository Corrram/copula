import Copula.Rank.Region.XiBlest.Support.QuadraticMeanInverse

/-! # Identifiability of the normalized quadratic slope -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem clamp_eq_interior {x y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (he : unitClamp x=y) : x=y := by
  unfold unitClamp at he
  rcases le_total x 0 with h | h
  · rw [max_eq_left h,min_eq_right zero_le_one] at he
    linarith [hy.1]
  · rw [max_eq_right h] at he
    rcases le_total x 1 with h1 | h1
    · rwa [min_eq_right h1] at he
    · rw [min_eq_left h1] at he
      linarith [hy.2]

/-- A clamped affine function with an interior unclipped value identifies its slope. -/
private theorem clamp_affine_slope {a b c d : ℝ} (hb : 0 ≤ b) (ha : a ∈ Ioo (-b) 1)
    (he : ∀ w : I, unitClamp (a+b*(w : ℝ))=unitClamp (c+d*(w : ℝ))) : b=d := by
  let w : ℝ := (1-a)/(b+1)
  let z : ℝ := (a+b)/(b+1)
  have hden : 0 < b+1 := by linarith
  have hw0 : 0 < w := div_pos (by linarith [ha.2]) hden
  have hw1 : w < 1 := (div_lt_one hden).mpr (by linarith [ha.1])
  have hz0 : 0 < z := div_pos (by linarith [ha.1]) hden
  have hz1 : z < 1 := (div_lt_one hden).mpr (by linarith [ha.2])
  have hwz : a+b*w=z := by dsimp [w,z]; field_simp; ring
  have hcl : unitClamp z=z := by unfold unitClamp; rw [max_eq_right hz0.le,min_eq_right hz1.le]
  have h0 := he ⟨w,hw0.le,hw1.le⟩
  dsimp only at h0
  rw [hwz,hcl] at h0
  have hraw0 : c+d*w=z := clamp_eq_interior ⟨hz0,hz1⟩ h0.symm
  let e : ℝ := min ((1-w)/2) ((1-z)/(2*(b+1)))
  have he0 : 0 < e := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hew : e ≤ (1-w)/2 := min_le_left _ _
  have hez : e ≤ (1-z)/(2*(b+1)) := min_le_right _ _
  have hem : e*(2*(b+1)) ≤ 1-z := (le_div_iff₀ (by positivity)).mp hez
  have hw1mem : w+e ∈ Icc (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
  have hz1mem : z+b*e ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · nlinarith [mul_nonneg hb he0.le]
    · nlinarith
  have h1 := he ⟨w+e,hw1mem⟩
  dsimp only at h1
  have hwz1 : a+b*(w+e)=z+b*e := by linarith
  rw [hwz1] at h1
  have hcl1 : unitClamp (z+b*e)=z+b*e := by
    unfold unitClamp; rw [max_eq_right hz1mem.1.le,min_eq_right hz1mem.2.le]
  rw [hcl1] at h1
  have hraw1 := clamp_eq_interior hz1mem h1.symm
  nlinarith

private theorem quadraticIntercept_interior (b : ℝ) (hb : 0 ≤ b) (v : I)
    (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) : quadraticIntercept b hb v ∈ Ioo (-b) 1 := by
  have hm := quadraticIntercept_mem b hb v
  have hlow : quadraticMean b (-b) < quadraticMean b (quadraticIntercept b hb v) := by
    rw [quadraticMean_zero b hb,quadraticIntercept_mean]
    exact hv.1
  have hhigh : quadraticMean b (quadraticIntercept b hb v) < quadraticMean b 1 := by
    rw [quadraticMean_top b hb,quadraticIntercept_mean]
    exact hv.2
  exact ⟨((quadraticMean_strictMonoOn hb).lt_iff_lt ⟨le_rfl,by linarith⟩ hm).mp hlow,
    ((quadraticMean_strictMonoOn hb).lt_iff_lt hm ⟨by linarith,le_rfl⟩).mp hhigh⟩

theorem quadraticBand_injective (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (he : quadraticBand b hb=quadraticBand d hd) : b=d := by
  let v : I := ⟨1/2,by constructor <;> norm_num⟩
  have hk : (fun u : I => quadraticKernel b hb v u) =ᵐ[volume] fun u => quadraticKernel d hd v u := by
    filter_upwards [quadraticBand_conditionalCDF b hb v,quadraticBand_conditionalCDF d hd v] with u hu hv
    rw [he] at hu
    exact hu.symm.trans hv
  have hfun := Measure.eq_of_ae_eq hk
    (show Continuous (quadraticKernel b hb v) by unfold quadraticKernel unitClamp; fun_prop)
    (show Continuous (quadraticKernel d hd v) by unfold quadraticKernel unitClamp; fun_prop)
  apply clamp_affine_slope hb (quadraticIntercept_interior b hb v (by dsimp [v]; constructor <;> norm_num))
  intro w
  let u : I := ⟨1-Real.sqrt (w : ℝ),by
    have h0 := Real.sqrt_nonneg (w : ℝ)
    have h1 := Real.sqrt_le_one.mpr w.property.2
    constructor <;> linarith⟩
  have hp : (1-(u : ℝ))^2=(w : ℝ) := by
    dsimp only [u]
    rw [show 1-(1-Real.sqrt (w : ℝ))=Real.sqrt (w : ℝ) by ring,Real.sq_sqrt w.property.1]
  have hh := congrFun hfun u
  simpa only [quadraticKernel,hp] using hh

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
