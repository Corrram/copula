import Copula.Rank.Region.XiRho.Support.Mixture
import Mathlib.Analysis.Convex.Basic

/-! # Convexity of xi regions with an affine second coefficient

An ordinary mixture can fall below the desired xi coordinate. If every
coefficient value has a witness with xi=1, a second mixture fills that gap
while preserving the coefficient. No compactness or closure is assumed.
-/

open ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

def xiCoefficientRegion (φ : Copula 2 → ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ C : Copula 2, C.chatterjeeXi = p.1 ∧ φ C = p.2}

variable (φ : Copula 2 → ℝ)
  (hφ : ∀ C D : Copula 2, ∀ a : I, φ (C.mix D a) = (a : ℝ) * φ C + (1 - a) * φ D)

include hφ

/-- Every intermediate xi value is attained at the same coefficient value. -/
theorem xi_intermediate_at_coefficient (C D : Copula 2) (he : φ C = φ D)
    (x : ℝ) (hC : C.chatterjeeXi ≤ x) (hD : x ≤ D.chatterjeeXi) :
    ∃ E : Copula 2, E.chatterjeeXi = x ∧ φ E = φ C := by
  obtain ⟨a, ha⟩ := exists_unitInterval_eq (continuous_xi_mix D C)
    (by simpa using hC) (by simpa using hD)
  refine ⟨D.mix C a, ha, ?_⟩
  rw [hφ, ← he]
  ring

variable (htop : ∀ C : Copula 2, ∃ D : Copula 2, D.chatterjeeXi = 1 ∧ φ D = φ C)

include htop

/-- At any attained coefficient value, all xi values up to one are attained. -/
theorem xi_upward_at_coefficient (C : Copula 2) (x : ℝ)
    (hx : C.chatterjeeXi ≤ x) (hx1 : x ≤ 1) :
    ∃ D : Copula 2, D.chatterjeeXi = x ∧ φ D = φ C := by
  obtain ⟨D, hD, he⟩ := htop C
  exact xi_intermediate_at_coefficient φ hφ C D he.symm x hx (hD ▸ hx1)

/-- Convexity follows from actual copula witnesses, not from assuming xi is affine. -/
theorem convex_xiCoefficientRegion : Convex ℝ (xiCoefficientRegion φ) := by
  rintro p ⟨C, hC, hCφ⟩ q ⟨D, hD, hDφ⟩ a b ha hb hab
  change ∃ E : Copula 2, E.chatterjeeXi = a * p.1 + b * q.1 ∧ φ E = a * p.2 + b * q.2
  let t : I := ⟨a, ha, by linarith⟩
  have ht : 1 - a = b := by linarith
  have hx : (C.mix D t).chatterjeeXi ≤ a * p.1 + b * q.1 := by
    simpa only [t, ht, hC, hD] using C.chatterjeeXi_mix_le D t
  have hx1 : a * p.1 + b * q.1 ≤ 1 := by
    have h₀ := mul_nonneg ha (sub_nonneg.mpr C.chatterjeeXi_mem_Icc.2)
    have h₁ := mul_nonneg hb (sub_nonneg.mpr D.chatterjeeXi_mem_Icc.2)
    rw [hC] at h₀
    rw [hD] at h₁
    nlinarith
  obtain ⟨E, hE, hEφ⟩ := xi_upward_at_coefficient φ hφ htop (C.mix D t) _ hx hx1
  refine ⟨E, hE, ?_⟩
  simpa only [hφ, t, ht, hCφ, hDφ] using hEφ

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
