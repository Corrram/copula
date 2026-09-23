import Copula.Rank.Region.TauFootruleBeta.Paper.Definitions
import Copula.Rank.Region.TauFootruleBeta.Support.Mixture

/-! # Filling the vertical fibres in the proof of Theorem 1.1

The endpoints must be supplied with both the prescribed footrule and beta.
No assertion that pairwise bounds imply joint attainability is assumed here.
-/

open ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

theorem concordance_mixture (C D E F : Copula 2) (a b : I) :
    (C.mix D a).concordanceQ (E.mix F b) =
      (a : ℝ) * (b : ℝ) * C.concordanceQ E +
      (a : ℝ) * (1 - (b : ℝ)) * C.concordanceQ F +
      (1 - (a : ℝ)) * (b : ℝ) * D.concordanceQ E +
      (1 - (a : ℝ)) * (1 - (b : ℝ)) * D.concordanceQ F := by
  rw [Copula.concordanceQ_mix_left]
  simp_rw [Copula.concordanceQ_mix_right]
  ring

theorem tau_mixture_continuous (C D : Copula 2) :
    Continuous (fun a : I => (C.mix D a).kendallTau) :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.continuous_tau_mix C D

/-- The intermediate-value step of the constructive joint-region proof. -/
theorem fixed_footrule_beta_intermediate (C D : Copula 2) {p b t : ℝ}
    (hpC : C.spearmanFootrule = p) (hpD : D.spearmanFootrule = p)
    (hbC : C.blomqvistBeta = b) (hbD : D.blomqvistBeta = b)
    (htC : C.kendallTau ≤ t) (htD : t ≤ D.kendallTau) :
    ∃ E : Copula 2,
      E.spearmanFootrule = p ∧ E.blomqvistBeta = b ∧ E.kendallTau = t := by
  obtain ⟨a, ha⟩ := ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.exists_unitInterval_eq
    (tau_mixture_continuous D C) (by simpa using htC) (by simpa using htD)
  refine ⟨D.mix C a, ?_, ?_, ha⟩
  · rw [Copula.spearmanFootrule_mix, hpD, hpC]
    ring
  · rw [Copula.blomqvistBeta_mix, hbD, hbC]
    ring

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
