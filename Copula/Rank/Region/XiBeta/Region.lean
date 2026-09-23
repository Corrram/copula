import Copula.Rank.Region.XiBeta.RightBoundary

/-! # The exact attainable region (Theorem 1)

Both endpoints are constructed explicitly. Fixed-beta mixtures attain
every intermediate xi, so the existential conclusion has no supplied
boundary hypotheses.
-/

open ProbabilityTheory Set

namespace ProbabilityTheory.Copula.RankRegion.XiBeta

/-- The set equality in Theorem 1, stated as membership equivalence. -/
theorem exact_xi_beta_region (x b : ℝ) :
    (∃ C : Copula 2, C.chatterjeeXi = x ∧ C.blomqvistBeta = b) ↔
      x ∈ Icc 0 1 ∧ b ∈ Icc (-1) 1 ∧ |b| ^ 3 ≤ 2 * x := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.chatterjeeXi_mem_Icc, C.blomqvistBeta_mem_Icc, beta_cubic_le_two_xi C⟩
  · rintro ⟨hx, hb, hbound⟩
    obtain ⟨C, hC, hxi⟩ := fixed_beta_intermediate (x := x)
      (leftBoundary b hb) (rightBoundary b hb)
      (leftBoundary_beta b hb) (rightBoundary_beta b hb)
      (by rw [leftBoundary_xi]; linarith) (by rw [rightBoundary_xi]; exact hx.2)
    exact ⟨C, hxi, hC⟩

end ProbabilityTheory.Copula.RankRegion.XiBeta
