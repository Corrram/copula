import Copula.Rank.Region.XiBlest.Paper.ExtremalFamily
import Copula.Rank.Region.XiBlest.Paper.ClosedRegion
import Copula.Rank.Region.XiBlest.Support.QuadraticBandContinuity
import Copula.Rank.Region.XiBlest.Support.QuadraticBandEndpoint

/-! # Exhaustion of all xi levels by the constructed Blest family -/

open MeasureTheory ProbabilityTheory Set Filter ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem extremal_coefficients_monotone {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hbd : b ≤ d) :
    (extremalCopula b hb).chatterjeeXi ≤ (extremalCopula d hd).chatterjeeXi ∧
      blestNu (extremalCopula b hb) ≤ blestNu (extremalCopula d hd) := by
  rcases eq_or_lt_of_le hbd with rfl | hbd
  · exact ⟨le_rfl,le_rfl⟩
  have h1 := extremal_support (extremalCopula d hd) b hb
  have h2 := extremal_support (extremalCopula b hb) d hd
  have hn : blestNu (extremalCopula b hb) ≤ blestNu (extremalCopula d hd) := by nlinarith
  exact ⟨by nlinarith [mul_nonneg hb (sub_nonneg.mpr hn)],hn⟩

theorem extremal_xi_continuous :
    Continuous (fun b : Ici (0 : ℝ) => (extremalCopula b b.property).chatterjeeXi) :=
  continuous_quadraticBand_xi

noncomputable def extremalSequence (n : ℕ) : Copula 2 :=
  extremalCopula (((n : ℝ)+1)^2) (by positivity)

theorem extremalSequence_cdf (u v : I) :
    Tendsto (fun n => (extremalSequence n).cdf ![u,v]) atTop
      (𝓝 ((Copula.comonotonic 2).cdf ![u,v])) := by
  have hbound (n : ℕ) : |(extremalSequence n).cdf ![u,v] - min (u : ℝ) (v : ℝ)| ≤
      1/((n : ℝ)+1) := by
    apply quadraticBand_comonotonic_error (((n : ℝ)+1)^2) (1/((n : ℝ)+1)) (by positivity)
      (by positivity) _ u v
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
    rfl
  rw [Copula.cdf_comonotonic_two]
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  intro n
  simpa only [Real.dist_eq,Matrix.cons_val_zero,Matrix.cons_val_one] using hbound n

theorem extremalSequence_xi :
    Tendsto (fun n => (extremalSequence n).chatterjeeXi) atTop (𝓝 1) := by
  have hm : Monotone (fun n => (extremalSequence n).chatterjeeXi) := by
    intro n m hnm
    apply (extremal_coefficients_monotone (by positivity) (by positivity) _).1
    have h : (n : ℝ) ≤ m := by exact_mod_cast hnm
    nlinarith [show 0 ≤ (n : ℝ) by positivity,show 0 ≤ (m : ℝ) by positivity]
  have hb : BddAbove (range (fun n => (extremalSequence n).chatterjeeXi)) :=
    ⟨1,by rintro _ ⟨n,rfl⟩; exact (extremalSequence n).chatterjeeXi_le_one⟩
  have ht := tendsto_atTop_ciSup hm hb
  have hl := xi_le_limit_of_cdf extremalSequence (Copula.comonotonic 2) _ extremalSequence_cdf ht
  rw [Copula.chatterjeeXi_comonotonic] at hl
  have hu := le_of_tendsto ht (Eventually.of_forall fun n => (extremalSequence n).chatterjeeXi_le_one)
  rwa [le_antisymm hu hl] at ht

theorem extremalSequence_blest :
    Tendsto (fun n => blestNu (extremalSequence n)) atTop (𝓝 1) := by
  simpa only [blest_comonotonic] using
    blest_tendsto_of_cdf extremalSequence (Copula.comonotonic 2) extremalSequence_cdf

/-- Every nontrivial xi below one has an actual member of the extremal family. -/
theorem extremal_parameter_exists (x : ℝ) (hx : x ∈ Ioo 0 1) :
    ∃ b : ℝ, ∃ hb : 0 < b, (extremalCopula b hb.le).chatterjeeXi = x := by
  obtain ⟨n,hn⟩ := (extremalSequence_xi.eventually_const_lt hx.2).exists
  let d : ℝ := ((n : ℝ)+1)^2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let f : I → ℝ := fun u => (extremalCopula (d*(u : ℝ)) (mul_nonneg hd u.property.1)).chatterjeeXi
  have hf : Continuous f := by
    have hg : Continuous (fun u : I => (⟨d*(u : ℝ),mul_nonneg hd u.property.1⟩ : Ici (0 : ℝ))) :=
      (continuous_const.mul continuous_subtype_val).subtype_mk _
    simpa only [Function.comp_def] using extremal_xi_continuous.comp hg
  have hc (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (he : r=s) :
      (extremalCopula r hr).chatterjeeXi=(extremalCopula s hs).chatterjeeXi := by
    subst s; rfl
  have hz : f 0=0 := by
    have h := hc (d*0) 0 (by simp) (by norm_num) (mul_zero d)
    rw [extremal_zero,Copula.chatterjeeXi_independence] at h
    exact h
  have ht : f 1=(extremalSequence n).chatterjeeXi := hc (d*1) d (by simpa using hd) hd (mul_one d)
  obtain ⟨u,hu⟩ := exists_unitInterval_eq (z := x) hf (by rw [hz]; exact hx.1.le)
    (by rw [ht]; exact hn.le)
  have hp : 0 < d*(u : ℝ) := by
    by_contra h
    have hzero : d*(u : ℝ)=0 := le_antisymm (le_of_not_gt h) (mul_nonneg hd u.property.1)
    have he0 (r : ℝ) (hr : 0 ≤ r) (he : r=0) : (extremalCopula r hr).chatterjeeXi=0 := by
      subst r
      rw [extremal_zero,Copula.chatterjeeXi_independence]
    have hh : f u=0 := he0 _ _ hzero
    linarith [hx.1]
  exact ⟨d*(u : ℝ),hp,hu⟩

end ProbabilityTheory.Copula.RankRegion.XiBlest
