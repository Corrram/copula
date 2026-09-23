import Copula.Rank.Region.TauFootruleBeta.Support.CenteredOrdinal

/-! # Equation (9): source-facing names for the shared centered ordinal sum -/

open ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

noncomputable def centralMargin (α : I) : I :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralMargin α

noncomputable def centralSplit (α : I) : I :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralSplit α

theorem central_weight (α : I) :
    (1 - (centralMargin α : ℝ)) * centralSplit α = (α : ℝ) :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.central_weight α

noncomputable def centeredOrdinal (C : Copula 2) (α : I) : Copula 2 :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal C α

theorem centeredOrdinal_zero (C : Copula 2) : centeredOrdinal C 0 = Copula.comonotonic 2 :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_zero C

theorem centeredOrdinal_one (C : Copula 2) : centeredOrdinal C 1 = C :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_one C

noncomputable def centralEmbed (α u : I) : I :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralEmbed α u

theorem coe_centralEmbed (α u : I) :
    (centralEmbed α u : ℝ) = (1 - (α : ℝ)) / 2 + (α : ℝ) * u :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.coe_centralEmbed α u

theorem centeredOrdinal_cdf (C : Copula 2) (α u v : I) :
    (centeredOrdinal C α).cdf ![centralEmbed α u, centralEmbed α v] =
      (1 - (α : ℝ)) / 2 + (α : ℝ) * C.cdf ![u, v] :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_cdf C α u v

theorem centeredOrdinal_tau (C : Copula 2) (α : I) :
    (centeredOrdinal C α).kendallTau = (α : ℝ) ^ 2 * C.kendallTau + 1 - (α : ℝ) ^ 2 :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_tau C α

theorem centeredOrdinal_footrule (C : Copula 2) (α : I) :
    (centeredOrdinal C α).spearmanFootrule =
      (α : ℝ) ^ 2 * C.spearmanFootrule + 1 - (α : ℝ) ^ 2 :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_footrule C α

theorem centeredOrdinal_beta (C : Copula 2) (α : I) :
    (centeredOrdinal C α).blomqvistBeta = (α : ℝ) * C.blomqvistBeta + 1 - (α : ℝ) :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_beta C α

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
