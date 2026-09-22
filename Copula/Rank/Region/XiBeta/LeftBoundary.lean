import Copula.Rank.Region.XiBeta.SharpBound
import Copula.Rank.Region.XiBeta.TwoStrip

/-! # The attaining left boundary in Proposition 3(i) -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBeta

/-- The signed median tent from equations (4)-(6). The sign at zero is immaterial. -/
noncomputable def tentDisplacement (b : ℝ) (hb : b ∈ Icc (-1) 1) : StripDisplacement where
  toFun v := if 0 ≤ b then medianTent b v else -medianTent (-b) v
  zero := by
    dsimp
    split_ifs <;> norm_num [medianTent] <;> linarith [hb.1, hb.2]
  one := by
    dsimp
    split_ifs <;> norm_num [medianTent] <;> linarith [hb.1, hb.2]
  lipschitz v w := by
    split_ifs
    · exact medianTent_lipschitz b v w
    · have h := medianTent_lipschitz (-b) v w
      simpa only [neg_sub_neg, abs_sub_comm] using h

noncomputable def leftBoundary (b : ℝ) (hb : b ∈ Icc (-1) 1) : Copula 2 :=
  twoStrip (tentDisplacement b hb)

theorem leftBoundary_cdf (b : ℝ) (hb : b ∈ Icc (-1) 1) (u v : I) :
    (leftBoundary b hb).cdf ![u, v] =
      (u : ℝ) * v + min (u : ℝ) (1 - u) *
        (if 0 ≤ b then medianTent b v else -medianTent (-b) v) :=
  cdf_twoStrip _ _ _

theorem leftBoundary_beta (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).blomqvistBeta = b := by
  rw [leftBoundary, beta_twoStrip]
  change 2 * (if 0 ≤ b then medianTent b (1 / 2) else -medianTent (-b) (1 / 2)) = b
  split_ifs with h
  · rw [medianTent, sub_self, abs_zero, sub_zero, max_eq_right (by linarith)]
    ring
  · rw [medianTent, sub_self, abs_zero, sub_zero, max_eq_right (by linarith)]
    ring

theorem leftBoundary_xi (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).chatterjeeXi = |b| ^ 3 / 2 := by
  rw [leftBoundary, xi_twoStrip]
  have he : (fun v : I => (tentDisplacement b hb) v ^ 2) =
      fun v : I => medianTent |b| v ^ 2 := by
    funext v
    change (if 0 ≤ b then medianTent b v else -medianTent (-b) v) ^ 2 = _
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), neg_sq]
  rw [he, integral_medianTent_sq (abs_nonneg _) (abs_le.mpr hb)]
  ring

/-- The cubic lower boundary is attained for every allowed beta. -/
theorem left_boundary_attained (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧ C.chatterjeeXi = |b| ^ 3 / 2 :=
  ⟨leftBoundary b hb, leftBoundary_beta b hb, leftBoundary_xi b hb⟩

/-- Proposition 5, equality case. Strict convexity rules out a second minimizer. -/
theorem xi_eq_lower_iff (C : Copula 2) (b : ℝ) (hb : b ∈ Icc (-1) 1)
    (hbeta : C.blomqvistBeta = b) :
    C.chatterjeeXi = |b| ^ 3 / 2 ↔ C = leftBoundary b hb := by
  constructor
  · intro hxi
    by_contra hne
    have hs := Copula.chatterjeeXi_mix_lt hne Copula.unitHalf
      (by change (0 : ℝ) < 1 / 2; norm_num) (by change (1 / 2 : ℝ) < 1; norm_num)
    have hm := beta_mixture_fixed C (leftBoundary b hb) hbeta (leftBoundary_beta b hb)
      Copula.unitHalf
    have hl := beta_cubic_le_two_xi (C.mix (leftBoundary b hb) Copula.unitHalf)
    rw [hm] at hl
    rw [hxi, leftBoundary_xi] at hs
    change (C.mix (leftBoundary b hb) Copula.unitHalf).chatterjeeXi <
      (1 / 2 : ℝ) * (|b| ^ 3 / 2) + (1 - 1 / 2) * (|b| ^ 3 / 2) at hs
    linarith
  · rintro rfl
    exact leftBoundary_xi b hb

end ProbabilityTheory.Copula.RankRegion.XiBeta
