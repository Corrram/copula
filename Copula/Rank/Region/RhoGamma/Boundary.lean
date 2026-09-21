/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.GluedMoments
import Copula.Rank.Region.RhoFootrule.UpperCoverage
import Copula.Rank.Extrema

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

/-- The explicit gamma coordinate in the source's boundary parametrization. -/
noncomputable def gammaValue (s c m : ℝ) : ℝ :=
  1 - 2 * (centralLength s c) ^ 2 - (cornerLength s c) ^ 2 * m

/-- The explicit rho coordinate in the source's boundary parametrization. -/
noncomputable def rhoValue (s c q : ℝ) : ℝ :=
  1 - 2 * (centralLength s c) ^ 3 - 3 / 2 * (cornerLength s c) ^ 3 * q

inductive UpperParameter
  | lowerEndpoint
  | upperEndpoint
  | halfShift (s : ℝ) (hs : 1 ≤ s)
  | right (S : RhoFootrule.RightData)
  | left (S : RhoFootrule.LeftData)

namespace UpperParameter

open RhoFootrule.UpperSpline

noncomputable def gamma : UpperParameter → ℝ
  | .lowerEndpoint => -1
  | .upperEndpoint => 1
  | .halfShift s _ => gammaValue s (3 / 8 - s / 2) (1 / 2)
  | .right S => gammaValue (period S.N S.v S.w) (offset S.N S.v S.w)
      (S.w + S.N * S.v + S.N * (S.N + 1) * S.v ^ 2)
  | .left S => gammaValue (period S.N S.v S.w) (offset S.N S.v S.w + S.v * S.w)
      (S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2)

noncomputable def rho : UpperParameter → ℝ
  | .lowerEndpoint => -1
  | .upperEndpoint => 1
  | .halfShift s _ => rhoValue s (3 / 8 - s / 2) (1 / 4)
  | .right S => rhoValue (period S.N S.v S.w) (offset S.N S.v S.w)
      ((S.w + S.N * S.v) ^ 2 + 2 * S.N * (S.N + 1) * (S.w + S.N * S.v) * S.v ^ 2 +
        2 / 3 * S.N * (S.N + 1) * S.v ^ 3)
  | .left S => rhoValue (period S.N S.v S.w) (offset S.N S.v S.w + S.v * S.w)
      ((S.w + (S.N + 1) * S.v) ^ 2 - 2 * S.N * (S.N + 1) * (S.w + (S.N + 1) * S.v) * S.v ^ 2 +
        2 / 3 * S.N * (S.N + 1) * S.v ^ 3)

noncomputable def copula : UpperParameter → Copula 2
  | .lowerEndpoint => countermonotonic
  | .upperEndpoint => comonotonic 2
  | .halfShift s hs => (AuxiliaryCertificate.halfShift s hs).copula
  | .right S => (AuxiliaryCertificate.ofRight S).copula
  | .left S => (AuxiliaryCertificate.ofLeft S).copula

theorem gamma_coefficient (p : UpperParameter) : p.copula.giniGamma = p.gamma := by
  cases p with
  | lowerEndpoint => exact giniGamma_countermonotonic
  | upperEndpoint => exact giniGamma_comonotonic
  | halfShift s hs =>
    change (AuxiliaryCertificate.halfShift s hs).copula.giniGamma = _
    rw [AuxiliaryCertificate.gamma]
    change 1 - 2 * (centralLength s (3 / 8 - s / 2)) ^ 2 -
      (cornerLength s (3 / 8 - s / 2)) ^ 2 * (1 - RhoFootrule.halfTurn.spearmanFootrule) / 3 = _
    rw [RhoFootrule.halfTurn_footrule]
    dsimp [gamma, gammaValue]
    ring
  | right S =>
    change (AuxiliaryCertificate.ofRight S).copula.giniGamma = _
    rw [AuxiliaryCertificate.gamma]
    change 1 - 2 * (centralLength (period S.N S.v S.w) (offset S.N S.v S.w)) ^ 2 -
      (cornerLength (period S.N S.v S.w) (offset S.N S.v S.w)) ^ 2 *
        (1 - S.copula.spearmanFootrule) / 3 = _
    rw [S.footrule]
    dsimp [gamma, gammaValue]
    ring
  | left S =>
    change (AuxiliaryCertificate.ofLeft S).copula.giniGamma = _
    rw [AuxiliaryCertificate.gamma]
    change 1 - 2 * (centralLength (period S.N S.v S.w) (offset S.N S.v S.w + S.v * S.w)) ^ 2 -
      (cornerLength (period S.N S.v S.w) (offset S.N S.v S.w + S.v * S.w)) ^ 2 *
        (1 - S.copula.spearmanFootrule) / 3 = _
    rw [S.footrule]
    dsimp [gamma, gammaValue]
    ring

theorem rho_coefficient (p : UpperParameter) : p.copula.spearmanRho = p.rho := by
  cases p with
  | lowerEndpoint => exact spearmanRho_countermonotonic
  | upperEndpoint => exact spearmanRho_comonotonic
  | halfShift s hs =>
    change (AuxiliaryCertificate.halfShift s hs).copula.spearmanRho = _
    rw [AuxiliaryCertificate.rho]
    change 1 - 2 * (centralLength s (3 / 8 - s / 2)) ^ 3 -
      (cornerLength s (3 / 8 - s / 2)) ^ 3 * (1 - RhoFootrule.halfTurn.spearmanRho) / 4 = _
    rw [RhoFootrule.halfTurn_rho]
    dsimp [rho, rhoValue]
    ring
  | right S =>
    change (AuxiliaryCertificate.ofRight S).copula.spearmanRho = _
    rw [AuxiliaryCertificate.rho]
    change 1 - 2 * (centralLength (period S.N S.v S.w) (offset S.N S.v S.w)) ^ 3 -
      (cornerLength (period S.N S.v S.w) (offset S.N S.v S.w)) ^ 3 *
        (1 - S.copula.spearmanRho) / 4 = _
    rw [S.rho]
    dsimp [rho, rhoValue]
    ring
  | left S =>
    change (AuxiliaryCertificate.ofLeft S).copula.spearmanRho = _
    rw [AuxiliaryCertificate.rho]
    change 1 - 2 * (centralLength (period S.N S.v S.w) (offset S.N S.v S.w + S.v * S.w)) ^ 3 -
      (cornerLength (period S.N S.v S.w) (offset S.N S.v S.w + S.v * S.w)) ^ 3 *
        (1 - S.copula.spearmanRho) / 4 = _
    rw [S.rho]
    dsimp [rho, rhoValue]
    ring

theorem maximizes (p : UpperParameter) (C : Copula 2) (h : C.giniGamma = p.gamma) :
    C.spearmanRho ≤ p.rho := by
  rw [← p.rho_coefficient]
  have hh : C.giniGamma = p.copula.giniGamma := h.trans p.gamma_coefficient.symm
  cases p with
  | lowerEndpoint =>
    have hC : C = countermonotonic := C.giniGamma_eq_neg_one_iff.mp h
    rw [hC]
    exact le_rfl
  | upperEndpoint => simpa only [copula, spearmanRho_comonotonic] using C.spearmanRho_mem_Icc.2
  | halfShift s hs => exact (AuxiliaryCertificate.halfShift s hs).maximizes_rho C hh
  | right S => exact (AuxiliaryCertificate.ofRight S).maximizes_rho C hh
  | left S => exact (AuxiliaryCertificate.ofLeft S).maximizes_rho C hh

end UpperParameter
end ProbabilityTheory.Copula.RankRegion.RhoGamma
