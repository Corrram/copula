import Copula.Rank.Region.XiBlest.Support.ClampNoiseTails

/-! # Exact tail corrections to both coefficient polynomials -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def xiTail (b t : ℝ) : ℝ := (max 0 (b*t-1))^2*(2*b*t+1)
noncomputable def nuTail (b t : ℝ) : ℝ := 3*t*(max 0 (b*t-1))^2

@[fun_prop] theorem continuous_xiTail (b : ℝ) : Continuous (xiTail b) := by unfold xiTail; fun_prop
@[fun_prop] theorem continuous_nuTail (b : ℝ) : Continuous (nuTail b) := by unfold nuTail; fun_prop

private theorem integrable_pair {f : I × I → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem integral_delta_polynomial (a b c : ℝ) :
    (∫ p : I × I,a+b*squareDelta p^2+c*|squareDelta p|^3)=a+b*(8/45)+c*(4/35) := by
  have hs : Integrable (fun p : I × I => squareDelta p^2) := integrable_pair (by fun_prop)
  have hc : Integrable (fun p : I × I => |squareDelta p|^3) := integrable_pair (by fun_prop)
  have ha : Integrable (fun p : I × I => a+b*squareDelta p^2) := (integrable_const a).add (hs.const_mul b)
  rw [integral_add ha (hc.const_mul c),integral_add (integrable_const a) (hs.const_mul b),
    integral_const_mul,integral_const_mul,integral_squareDelta_sq,integral_squareDelta_cube]
  simp

private theorem integral_potential_pair : (∫ p : I × I,(squarePotential p.1+squarePotential p.2)/4)=1/6 := by
  have hi : Integrable (fun p : I × I => (squarePotential p.1+squarePotential p.2)/4) := integrable_pair (by fun_prop)
  change (∫ p : I × I,(squarePotential p.1+squarePotential p.2)/4 ∂(volume : Measure I).prod volume)=_
  rw [integral_prod _ hi]
  have he (u : I) : (∫ v : I,(squarePotential u+squarePotential v)/4)=(squarePotential u+1/3)/4 := by
    rw [integral_div,integral_add (integrable_const _) (Copula.integrable_continuous_unit volume continuous_squarePotential),integral_squarePotential]
    simp
  simp_rw [he]
  rw [integral_div,integral_add (Copula.integrable_continuous_unit volume continuous_squarePotential) (integrable_const _),integral_squarePotential]
  norm_num

theorem integral_noise_square_tail (b : ℝ) (hb : 0 ≤ b) :
    (∫ p : I × I,noiseMoment 2 (b*squareDelta p)) =
      1/3+4*b^2/45-4*b^3/105+(∫ p : I × I,xiTail b |squareDelta p|)/6 := by
  rw [integral_pair_symmetrize _ (by fun_prop)]
  have he (p : I × I) : (noiseMoment 2 (b*squareDelta p)+noiseMoment 2 (b*squareDelta p.swap))/2 =
      (1/3+(b^2/2)*squareDelta p^2+(-b^3/3)*|squareDelta p|^3)+xiTail b |squareDelta p|/6 := by
    have hs : b*squareDelta p.swap=-(b*squareDelta p) := by unfold squareDelta; simp; ring
    rw [hs,noise_square_full,abs_mul,abs_of_nonneg hb]
    unfold xiTail
    ring
  simp_rw [he]
  rw [integral_add (integrable_pair (by fun_prop)) (integrable_pair (by fun_prop)),
    integral_div,integral_delta_polynomial]
  ring

theorem integral_noise_weighted_tail (b : ℝ) (hb : 0 ≤ b) :
    (∫ p : I × I,squarePotential p.2*noiseMoment 1 (b*squareDelta p)) =
      1/6+4*b/45-b^2/35+(∫ p : I × I,nuTail b |squareDelta p|)/12 := by
  rw [integral_pair_symmetrize _ (by fun_prop)]
  have he (p : I × I) :
      (squarePotential p.2*noiseMoment 1 (b*squareDelta p)+squarePotential p.swap.2*noiseMoment 1 (b*squareDelta p.swap))/2 =
      (squarePotential p.1+squarePotential p.2)/4+
        (0+(b/2)*squareDelta p^2+(-b^2/4)*|squareDelta p|^3)+nuTail b |squareDelta p|/12 := by
    have h := noise_weighted_full b (squarePotential p.2) (squarePotential p.1) hb
    change (squarePotential p.2*noiseMoment 1 (b*(squarePotential p.2-squarePotential p.1))+
      squarePotential p.1*noiseMoment 1 (b*(squarePotential p.1-squarePotential p.2)))/2=_
    rw [h]
    unfold squareDelta nuTail
    ring
  simp_rw [he]
  rw [integral_add (integrable_pair (by fun_prop)) (integrable_pair (by fun_prop)),
    integral_add (integrable_pair (by fun_prop)) (integrable_pair (by fun_prop)),
    integral_potential_pair,integral_delta_polynomial,integral_div]
  ring

theorem quadraticBand_xi_tail (b : ℝ) (hb : 0 ≤ b) :
    (quadraticBand b hb).chatterjeeXi=8*b^2*(7-3*b)/105+∫ p : I × I,xiTail b |squareDelta p| := by
  rw [quadraticBand_xi_noise,integral_noise_square_tail b hb]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
