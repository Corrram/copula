import Copula.Rank.Region.XiRho.Paper.BoundaryInverse
import Copula.Rank.Region.XiRho.Paper.RegionGeometry
import Copula.Rank.Region.XiRho.Paper.StochasticBounds
import Copula.Rank.Region.XiRho.Support.XiReflection

/-! # Theorem 1: the full explicit xi--rho region and unique interior boundary copulas -/

open ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiRho.Support

namespace ProbabilityTheory.Copula.RankRegion.XiRho

/-- Exactly M_x in equation (5), with the displayed trigonometric/radical inverse. -/
noncomputable def upperRhoAtXi (x : ℝ) : ℝ :=
  if x = 0 then 0 else if x = 1 then 1 else bandRho (boundaryParameter x)

noncomputable def boundaryCopula (x : ℝ) (hx : 0 < x) (hx1 : x < 1) : Copula 2 :=
  sourceBand (boundaryParameter x) (boundaryParameter_inverse hx hx1).1

/-- The original source family attains every interior positive boundary point. -/
theorem boundaryCopula_coefficients {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (boundaryCopula x hx hx1).chatterjeeXi = x ∧
      (boundaryCopula x hx hx1).spearmanRho = upperRhoAtXi x := by
  unfold boundaryCopula
  rw [sourceBand_xi, sourceBand_rho]
  exact ⟨(boundaryParameter_inverse hx hx1).2,
    by simp [upperRhoAtXi, ne_of_gt hx, ne_of_lt hx1]⟩

private theorem interior_rho_bound (C : Copula 2) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hC : C.chatterjeeXi = x) : C.spearmanRho ≤ upperRhoAtXi x := by
  have hb := boundaryParameter_inverse hx hx1
  have h := explicit_band_support C (boundaryParameter x) hb.1.le
  rw [hC, hb.2] at h
  have he : upperRhoAtXi x = bandRho (boundaryParameter x) := by
    simp [upperRhoAtXi, ne_of_gt hx, ne_of_lt hx1]
  rw [he]
  nlinarith only [h, hb.1]

/-- Theorem 1: the sharp two-sided bound for every bivariate copula. -/
theorem sharp_absolute_rho_bound (C : Copula 2) :
    |C.spearmanRho| ≤ upperRhoAtXi C.chatterjeeXi := by
  by_cases h0 : C.chatterjeeXi = 0
  · rw [(xi_zero_slice C).mp h0 |>.2, h0]
    norm_num [upperRhoAtXi]
  by_cases h1 : C.chatterjeeXi = 1
  · rw [h1]
    norm_num [upperRhoAtXi]
    exact abs_le.mpr C.spearmanRho_mem_Icc
  have hx : 0 < C.chatterjeeXi := lt_of_le_of_ne C.chatterjeeXi_nonneg (Ne.symm h0)
  have hx1 : C.chatterjeeXi < 1 := lt_of_le_of_ne C.chatterjeeXi_le_one h1
  apply abs_le.mpr
  refine ⟨?_, interior_rho_bound C hx hx1 rfl⟩
  have h := interior_rho_bound (C.reflect {1}) hx hx1 (xi_reflect_second C)
  rw [Copula.spearmanRho_reflect_second] at h
  linarith

private theorem interior_bound_positive {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : 0 < upperRhoAtXi x := by
  have hs := normalizedBand_isSI (boundaryParameter x) (boundaryParameter_inverse hx hx1).1.le
  have hh := si_xi_le_rho _ hs
  rw [(normalizedBand_coefficients _ _).1, (normalizedBand_coefficients _ _).2,
    (boundaryParameter_inverse hx hx1).2] at hh
  simp only [upperRhoAtXi, ite_eq_right (ne_of_gt hx), ite_eq_right (ne_of_lt hx1)]
  linarith

/-- Equations (4)--(5): necessary and sufficient conditions for the full exact region. -/
theorem exact_region (x y : ℝ) :
    (∃ C : Copula 2, C.chatterjeeXi = x ∧ C.spearmanRho = y) ↔
      x ∈ Icc (0 : ℝ) 1 ∧ |y| ≤ upperRhoAtXi x := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.chatterjeeXi_mem_Icc, sharp_absolute_rho_bound C⟩
  · rintro ⟨hx, hy⟩
    by_cases h0 : x = 0
    · subst x
      have he : y = 0 := abs_eq_zero.mp (le_antisymm (by simpa [upperRhoAtXi] using hy) (abs_nonneg y))
      subst y
      exact ⟨Copula.independence 2, by simp, by simp⟩
    by_cases h1 : x = 1
    · subst x
      apply (xi_one_slice y).mpr
      simpa [upperRhoAtXi] using abs_le.mp hy
    have hx0 : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
    have hx1 : x < 1 := lt_of_le_of_ne hx.2 h1
    let D := boundaryCopula x hx0 hx1
    have hd := boundaryCopula_coefficients hx0 hx1
    have hp : (x, upperRhoAtXi x) ∈ attainableRegion := ⟨D, hd⟩
    have hn : (x, -upperRhoAtXi x) ∈ attainableRegion :=
      ⟨D.reflect {1}, by rw [xi_reflect_second]; exact hd.1,
        by rw [Copula.spearmanRho_reflect_second, hd.2]⟩
    have hm := interior_bound_positive hx0 hx1
    let a := (y + upperRhoAtXi x) / (2 * upperRhoAtXi x)
    have ha : 0 ≤ a := div_nonneg (by linarith [(abs_le.mp hy).1]) (by positivity)
    have ha1 : a ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 2 * upperRhoAtXi x)).mpr
      linarith [(abs_le.mp hy).2]
    have h := attainable_region_convex hp hn ha (by linarith : 0 ≤ 1 - a)
      (show a + (1 - a) = 1 by ring)
    change ∃ C : Copula 2, C.chatterjeeXi = a * x + (1 - a) * x ∧
      C.spearmanRho = a * upperRhoAtXi x + (1 - a) * (-upperRhoAtXi x) at h
    obtain ⟨C, hc, hr⟩ := h
    refine ⟨C, ?_, ?_⟩
    · nlinarith only [hc]
    · rw [hr]
      dsimp [a]
      field_simp
      ring

/-- The positive boundary identifies the actual copula uniquely at every interior xi. -/
theorem upper_boundary_unique (C : Copula 2) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hC : C.chatterjeeXi = x) :
    C.spearmanRho = upperRhoAtXi x ↔ C = boundaryCopula x hx hx1 := by
  have hb := boundaryParameter_inverse hx hx1
  have hxi : C.chatterjeeXi = (normalizedBand (boundaryParameter x) hb.1.le).chatterjeeXi := by
    rw [(normalizedBand_coefficients _ _).1, hb.2, hC]
  have h := normalizedBand_maximal_rho_eq_iff C (boundaryParameter x) hb.1 hxi
  rw [(normalizedBand_coefficients _ _).2] at h
  have hval : upperRhoAtXi x = bandRho (boundaryParameter x) := by
    simp [upperRhoAtXi, ne_of_gt hx, ne_of_lt hx1]
  rw [hval]
  simpa only [boundaryCopula, sourceBand_eq_normalizedBand] using h

/-- The reflected source copula is the unique negative-boundary optimizer. -/
theorem lower_boundary_unique (C : Copula 2) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hC : C.chatterjeeXi = x) :
    C.spearmanRho = -upperRhoAtXi x ↔ C = (boundaryCopula x hx hx1).reflect {1} := by
  have h := upper_boundary_unique (C.reflect {1}) hx hx1 (by rw [xi_reflect_second, hC])
  rw [Copula.spearmanRho_reflect_second] at h
  constructor
  · intro he
    have hc := h.mp (by linarith)
    simpa only [Copula.reflect_reflect] using congrArg (fun D : Copula 2 => D.reflect {1}) hc
  · intro he
    rw [he, Copula.spearmanRho_reflect_second, (boundaryCopula_coefficients hx hx1).2]

end ProbabilityTheory.Copula.RankRegion.XiRho
