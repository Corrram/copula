import Copula.Rank.Region.XiBlest.Support.CopulaWeakCompactness
import Copula.Rank.Region.XiBlest.Support.XiLowerSemicontinuity
import Copula.Rank.Region.XiBlest.Support.XiAffineRegion

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Lower semicontinuity of xi plus filling toward xi=1 makes the actual region closed. -/
theorem isClosed_xiCoefficientRegion (r : Copula 2 → ℝ)
    (hcont : ∀ (C : ℕ → Copula 2) (D : Copula 2),
      (∀ u v : I, Tendsto (fun n => (C n).cdf ![u,v]) atTop (𝓝 (D.cdf ![u,v]))) →
      Tendsto (fun n => r (C n)) atTop (𝓝 (r D)))
    (hup : ∀ (C : Copula 2) (x : ℝ), C.chatterjeeXi ≤ x → x ≤ 1 →
      ∃ D : Copula 2, D.chatterjeeXi=x ∧ r D=r C) :
    IsClosed (xiCoefficientRegion r) := by
  apply IsSeqClosed.isClosed
  intro p z hp hz
  choose C hxi hr using hp
  have hxl : Tendsto (fun n => (C n).chatterjeeXi) atTop (𝓝 z.1) := by
    simpa only [hxi,Function.comp_def] using ((continuous_fst.tendsto z).comp hz)
  have hrl : Tendsto (fun n => r (C n)) atTop (𝓝 z.2) := by
    simpa only [hr,Function.comp_def] using ((continuous_snd.tendsto z).comp hz)
  obtain ⟨D,φ,hφ,_,hcdf⟩ := exists_copula_subsequence C
  have hlow : D.chatterjeeXi ≤ z.1 := xi_le_limit_of_cdf _ D z.1 hcdf (hxl.comp hφ.tendsto_atTop)
  have hhigh : z.1 ≤ 1 := le_of_tendsto hxl (Eventually.of_forall fun n => (C n).chatterjeeXi_mem_Icc.2)
  have hval : r D=z.2 := tendsto_nhds_unique (hcont _ D hcdf) (hrl.comp hφ.tendsto_atTop)
  obtain ⟨E,hE,hEr⟩ := hup D z.1 hlow hhigh
  exact ⟨E,hE,hEr.trans hval⟩

/-- A closed xi region with a bounded second coefficient is compact. -/
theorem isCompact_xiCoefficientRegion (r : Copula 2 → ℝ)
    (hc : IsClosed (xiCoefficientRegion r)) (a b : ℝ) (hr : ∀ C, r C ∈ Icc a b) :
    IsCompact (xiCoefficientRegion r) := by
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
  rintro ⟨x,y⟩ ⟨C,rfl,rfl⟩
  exact ⟨C.chatterjeeXi_mem_Icc,hr C⟩

/-- Every nonempty vertical slice attains both coefficient extrema. -/
theorem xi_slice_extrema (r : Copula 2 → ℝ) (hc : IsCompact (xiCoefficientRegion r))
    (C : Copula 2) : ∃ L U : Copula 2,
      L.chatterjeeXi=C.chatterjeeXi ∧ U.chatterjeeXi=C.chatterjeeXi ∧
      ∀ D : Copula 2, D.chatterjeeXi=C.chatterjeeXi → r L ≤ r D ∧ r D ≤ r U := by
  let S := xiCoefficientRegion r ∩ {p : ℝ × ℝ | p.1=C.chatterjeeXi}
  have hs : IsCompact S := hc.inter_right (isClosed_eq continuous_fst continuous_const)
  have hn : S.Nonempty := ⟨(C.chatterjeeXi,r C),⟨C,rfl,rfl⟩,rfl⟩
  obtain ⟨l,⟨⟨L,hL,hLr⟩,hl⟩,hmin⟩ := hs.exists_isMinOn hn continuous_snd.continuousOn
  obtain ⟨u,⟨⟨U,hU,hUr⟩,hu⟩,hmax⟩ := hs.exists_isMaxOn hn continuous_snd.continuousOn
  refine ⟨L,U,hL.trans hl,hU.trans hu,fun D hD => ?_⟩
  have hd : (D.chatterjeeXi,r D) ∈ S := ⟨⟨D,rfl,rfl⟩,hD⟩
  exact ⟨hLr ▸ hmin hd,hUr ▸ hmax hd⟩

/-- Every nonempty horizontal slice attains its least xi. -/
theorem coefficient_slice_minimum (r : Copula 2 → ℝ) (hc : IsCompact (xiCoefficientRegion r))
    (C : Copula 2) : ∃ L : Copula 2, r L=r C ∧
      ∀ D : Copula 2, r D=r C → L.chatterjeeXi ≤ D.chatterjeeXi := by
  let S := xiCoefficientRegion r ∩ {p : ℝ × ℝ | p.2=r C}
  have hs : IsCompact S := hc.inter_right (isClosed_eq continuous_snd continuous_const)
  have hn : S.Nonempty := ⟨(C.chatterjeeXi,r C),⟨C,rfl,rfl⟩,rfl⟩
  obtain ⟨l,⟨⟨L,hL,hLr⟩,hl⟩,hmin⟩ := hs.exists_isMinOn hn continuous_fst.continuousOn
  refine ⟨L,hLr.trans hl,fun D hD => ?_⟩
  have hd : (D.chatterjeeXi,r D) ∈ S := ⟨⟨D,rfl,rfl⟩,hD⟩
  exact hL ▸ hmin hd

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
