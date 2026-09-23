import Copula.Rank.Region.XiBlest.Support.QuadraticBandMoments
import Copula.Rank.Region.XiBlest.Support.ClampNoiseMoments
import Copula.Rank.Region.XiBlest.Support.SquaredUniformMoments

/-! # Polynomial coefficient integrals for slopes between zero and one -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def noiseMoment (k : ℕ) (d : ℝ) : ℝ := ∫ z : I, unitClamp ((z : ℝ)+d)^k

@[fun_prop] theorem continuous_noiseMoment (k : ℕ) : Continuous (noiseMoment k) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure I))
    (f := fun d : ℝ => fun z : I => unitClamp ((z : ℝ)+d)^k)
    (by unfold unitClamp; fun_prop) isCompact_univ
  change Continuous (fun d : ℝ => ∫ z : I, unitClamp ((z : ℝ)+d)^k)
  simpa only [Measure.restrict_univ] using h

theorem quadratic_kernel_moment_pair (b : ℝ) (hb : 0 ≤ b) (w : I → ℝ) (hw : Continuous w) (k : ℕ) :
    (∫ v : I, ∫ t : I, w t * quadraticKernel b hb v t ^ k) =
      ∫ p : I × I, w p.2 * noiseMoment k (b*squareDelta p) := by
  rw [quadratic_kernel_moment_sample b hb w hw k]
  have hi : Integrable (fun p : I × I => w p.2 * noiseMoment k (b*squareDelta p)) :=
    (by fun_prop : Continuous (fun p : I × I => w p.2 * noiseMoment k (b*squareDelta p))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change _ = ∫ p : I × I, w p.2 * noiseMoment k (b*squareDelta p) ∂(volume : Measure I).prod volume
  rw [integral_prod _ hi]
  simp only [noiseMoment,squareDelta,squarePotential,integral_const_mul]

theorem quadraticBand_xi_noise (b : ℝ) (hb : 0 ≤ b) :
    (quadraticBand b hb).chatterjeeXi = 6*(∫ p : I × I, noiseMoment 2 (b*squareDelta p))-2 := by
  have he (v : I) : (∫ u : I, (quadraticBand b hb).conditionalCDF u v ^ 2) =
      ∫ u : I, quadraticKernel b hb v u ^ 2 :=
    integral_congr_ae ((quadraticBand_conditionalCDF b hb v).fun_comp (fun z : ℝ => z^2))
  have hm := quadratic_kernel_moment_pair b hb (fun _ => 1) continuous_const 2
  simp only [one_mul] at hm
  unfold Copula.chatterjeeXi
  simp_rw [he]
  rw [hm]

private theorem scaled_delta_bound (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (p : I × I) :
    |b*squareDelta p| ≤ 1 := by
  rw [abs_mul,abs_of_nonneg hb.1]
  exact (mul_le_mul_of_nonneg_left (squareDelta_abs_le p) hb.1).trans (by simpa using hb.2)

theorem integral_noise_square (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ p : I × I, noiseMoment 2 (b*squareDelta p)) = 1/3+4*b^2/45-4*b^3/105 := by
  rw [integral_pair_symmetrize _ (by fun_prop)]
  have he (p : I × I) : (noiseMoment 2 (b*squareDelta p)+noiseMoment 2 (b*squareDelta p.swap))/2 =
      1/3+(b^2/2)*squareDelta p^2-(b^3/3)*|squareDelta p|^3 := by
    have hs : squareDelta p.swap = -squareDelta p := by unfold squareDelta; simp
    rw [hs]
    have h := clamp_noise_square_pair (b*squareDelta p) (scaled_delta_bound b hb p)
    have hn : (∫ z : I, unitClamp ((z : ℝ)-b*squareDelta p)^2)=noiseMoment 2 (b * -squareDelta p) := by
      unfold noiseMoment; congr 1; funext z; congr 2; ring
    rw [hn] at h
    change (noiseMoment 2 (b*squareDelta p)+noiseMoment 2 (b * -squareDelta p))/2 = _ at h
    rw [h,abs_mul,abs_of_nonneg hb.1]
    ring
  simp_rw [he]
  have hs : Integrable (fun p : I × I => squareDelta p^2) :=
    (by fun_prop : Continuous (fun p : I × I => squareDelta p^2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun p : I × I => |squareDelta p|^3) :=
    (by fun_prop : Continuous (fun p : I × I => |squareDelta p|^3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ha : Integrable (fun p : I × I => 1/3+(b^2/2)*squareDelta p^2) :=
    (integrable_const (1/3 : ℝ)).add (hs.const_mul _)
  rw [integral_sub ha (hc.const_mul _),integral_add (integrable_const _) (hs.const_mul _),
    integral_const_mul,integral_const_mul,integral_squareDelta_sq,integral_squareDelta_cube]
  simp
  ring

theorem quadraticBand_xi_polynomial (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (quadraticBand b hb.1).chatterjeeXi=8*b^2*(7-3*b)/105 := by
  rw [quadraticBand_xi_noise,integral_noise_square b hb]
  ring

theorem integral_noise_weighted (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ p : I × I, squarePotential p.2 * noiseMoment 1 (b*squareDelta p)) =
      1/6+4*b/45-b^2/35 := by
  rw [integral_pair_symmetrize _ (by fun_prop)]
  have he (p : I × I) :
      (squarePotential p.2 * noiseMoment 1 (b*squareDelta p)+
        squarePotential p.swap.2 * noiseMoment 1 (b*squareDelta p.swap))/2 =
      (squarePotential p.1+squarePotential p.2)/4+(b/2)*squareDelta p^2-
        (b^2/4)*|squareDelta p|^3 := by
    have hs : squareDelta p.swap = -squareDelta p := by unfold squareDelta; simp
    have h1 := clamp_noise_moment (b*squareDelta p) (scaled_delta_bound b hb p)
    have h2 := clamp_noise_moment (b*squareDelta p.swap) (scaled_delta_bound b hb p.swap)
    have hn (d : ℝ) : noiseMoment 1 d = ∫ z : I, unitClamp ((z : ℝ)+d) := by simp [noiseMoment]
    rw [hn,hn,h1,h2,hs]
    simp only [Prod.snd_swap,mul_neg,abs_neg,abs_mul,abs_of_nonneg hb.1]
    have hc : |squareDelta p|^3 = squareDelta p^2*|squareDelta p| := by rw [pow_succ,sq_abs]
    rw [hc]
    unfold squareDelta
    ring
  simp_rw [he]
  have hs : Integrable (fun p : I × I => squareDelta p^2) :=
    (by fun_prop : Continuous (fun p : I × I => squareDelta p^2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun p : I × I => |squareDelta p|^3) :=
    (by fun_prop : Continuous (fun p : I × I => |squareDelta p|^3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp : Integrable (fun p : I × I => (squarePotential p.1+squarePotential p.2)/4) :=
    (by fun_prop : Continuous (fun p : I × I => (squarePotential p.1+squarePotential p.2)/4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hval : (∫ p : I × I, (squarePotential p.1+squarePotential p.2)/4)=1/6 := by
    change (∫ p : I × I, (squarePotential p.1+squarePotential p.2)/4 ∂(volume : Measure I).prod volume)=_
    rw [integral_prod _ hp]
    have hx (u : I) : (∫ v : I, (squarePotential u+squarePotential v)/4) = (squarePotential u+1/3)/4 := by
      rw [integral_div,integral_add (integrable_const _) (Copula.integrable_continuous_unit volume continuous_squarePotential),integral_squarePotential]
      simp
    simp_rw [hx]
    rw [integral_div,integral_add (Copula.integrable_continuous_unit volume continuous_squarePotential) (integrable_const _),integral_squarePotential]
    norm_num
  have ha : Integrable (fun p : I × I => (squarePotential p.1+squarePotential p.2)/4+(b/2)*squareDelta p^2) :=
    hp.add (hs.const_mul _)
  rw [integral_sub ha (hc.const_mul _),integral_add hp (hs.const_mul _),
    integral_const_mul,integral_const_mul,hval,integral_squareDelta_sq,integral_squareDelta_cube]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
