import Copula.Rank.Region

/-! Exact membership, nonmembership, boundary junctions and transitive axiom reports. -/

open ProbabilityTheory
open ProbabilityTheory.Copula
open ProbabilityTheory.Copula.RankRegion

-- The three vertices of the tau–footrule triangle, with the footrule normalization.
example : (-1 / 2, -1) ∈ attainable .footrule .tau := by
  rw [attainable_footrule_tau_iff]; norm_num

example : (-1 / 2, 0) ∈ attainable .footrule .tau := by
  rw [attainable_footrule_tau_iff]; norm_num

example : (1, 1) ∈ attainable .footrule .tau := by
  rw [attainable_footrule_tau_iff]; norm_num

-- An interior fibre is filled even though tau is not affine under mixtures.
example : (0, 0) ∈ attainable .footrule .tau := by
  rw [attainable_footrule_tau_iff]; norm_num

example : (1 / 2, 0) ∈ attainable .gamma .tau := by
  rw [attainable_gamma_tau_iff]; norm_num

example : (-1 / 2, 0) ∈ attainable .gamma .tau := by
  rw [attainable_gamma_tau_iff]; norm_num

-- The kink in the upper footrule–gamma boundary.
example : (1 / 4, 1 / 2) ∈ attainable .footrule .gamma := by
  rw [attainable_footrule_gamma_iff]; norm_num

example : (-1 / 2, 0) ∉ attainable .footrule .gamma := by
  rw [attainable_footrule_gamma_iff]; norm_num

-- Cubic and quadratic beta boundaries, including singular endpoint fibres.
example : (0, 13 / 16) ∈ attainable .beta .rho := by
  rw [attainable_beta_rho_iff]; norm_num

example : (0, -(13 / 16)) ∈ attainable .beta .rho := by
  rw [attainable_beta_rho_iff]; norm_num

example : (1, 0) ∈ attainable .beta .tau := by
  rw [attainable_beta_tau_iff]; norm_num

example : (1, 1 / 4) ∈ attainable .beta .footrule := by
  rw [attainable_beta_footrule_iff]; norm_num

example : (-1, -1 / 2) ∈ attainable .beta .gamma := by
  rw [attainable_beta_gamma_iff]; norm_num

example : (-1, 0) ∉ attainable .beta .rho := by
  rw [attainable_beta_rho_iff]; norm_num

-- The exact xi–beta boundary and an excluded point.
example : ∃ C : Copula 2, C.chatterjeeXi = 1 / 2 ∧ C.blomqvistBeta = 1 := by
  rw [attainable_xi_beta_iff]
  norm_num

example : ¬ ∃ C : Copula 2, C.chatterjeeXi = 1 / 4 ∧ C.blomqvistBeta = 1 := by
  rw [attainable_xi_beta_iff]
  norm_num

-- The xi–rho zero fibre is a singleton.
example : ∃ C : Copula 2, C.chatterjeeXi = 0 ∧ C.spearmanRho = 0 := by
  rw [attainable_xi_rho_iff]
  norm_num [XiRho.upperRhoAtXi]

example : ¬ ∃ C : Copula 2, C.chatterjeeXi = 0 ∧ C.spearmanRho = 1 / 2 := by
  rw [attainable_xi_rho_iff]
  norm_num [XiRho.upperRhoAtXi]

-- Coordinate order is explicit and reversible.
example : (13 / 16, 0) ∈ attainable .rho .beta := by
  rw [mem_attainable_swap, attainable_beta_rho_iff]; norm_num

example : (RhoFootrule.contactCopula 1).spearmanFootrule = 1 / 4 ∧
    (RhoFootrule.contactCopula 1).spearmanRho = 5 / 8 := by
  convert RhoFootrule.contactCopula_coefficients 1 using 1 <;> norm_num

example : (RhoTau.junctionCopula 1).kendallTau = 0 ∧
    (RhoTau.junctionCopula 1).spearmanRho = -1 / 2 := by
  convert RhoTau.junctionCopula_coefficients 1 using 1 <;> norm_num

-- A non-junction point on a Schreyer–Paulin–Trutschnig prototype arc.
example : (RhoTau.arcCopula 1 unitHalf).kendallTau = -1 / 4 ∧
    (RhoTau.arcCopula 1 unitHalf).spearmanRho = -101 / 144 := by
  convert RhoTau.arcCopula_coefficients 1 unitHalf using 1 <;>
    norm_num [RhoTau.arcTau, RhoTau.arcRho, unitHalf]

#print axioms RhoTau.arcCopula_coefficients
#print axioms attainable_footrule_tau_iff
#print axioms attainable_gamma_tau_iff
#print axioms attainable_footrule_gamma_iff
#print axioms attainable_beta_rho_iff
#print axioms attainable_beta_tau_iff
#print axioms attainable_beta_footrule_iff
#print axioms attainable_beta_gamma_iff
#print axioms attainable_xi_beta_iff
#print axioms attainable_xi_rho_iff
#print axioms RhoFootrule.contactCopula_maximizes_rho
#print axioms RhoGamma.supporting_maximum
#print axioms RhoGamma.halfShift_optimal

-- Non-contact points on both halves of the new sharp upper boundary.
example : (5 / 32, 33 / 64) ∈ attainable .footrule .rho := by
  rw [mem_attainable_iff]
  let a := RhoFootrule.UpperParameter.right (RhoFootrule.rightFamily 1 (by decide) unitHalf)
  refine ⟨a.copula, ?_, ?_⟩
  · change a.copula.spearmanFootrule = _
    rw [a.coefficients.1]
    norm_num [a, RhoFootrule.UpperParameter.footrule, RhoFootrule.rightFamily, unitHalf]
  · change a.copula.spearmanRho = _
    rw [a.coefficients.2]
    norm_num [a, RhoFootrule.UpperParameter.rho, RhoFootrule.rightFamily, unitHalf]

example : (-13 / 32, -21 / 64) ∈ attainable .footrule .rho := by
  rw [mem_attainable_iff]
  let a := RhoFootrule.UpperParameter.left (RhoFootrule.leftFamily 1 (by decide) unitHalf)
  refine ⟨a.copula, ?_, ?_⟩
  · change a.copula.spearmanFootrule = _
    rw [a.coefficients.1]
    norm_num [a, RhoFootrule.UpperParameter.footrule, RhoFootrule.leftFamily, unitHalf]
  · change a.copula.spearmanRho = _
    rw [a.coefficients.2]
    norm_num [a, RhoFootrule.UpperParameter.rho, RhoFootrule.leftFamily, unitHalf]

-- The sharp upper arc excludes a point below the old quadratic envelope.
example : (5 / 32, 17 / 32) ∉ attainable .footrule .rho := by
  rw [mem_attainable_iff]
  rintro ⟨C, hp, hr⟩
  change C.spearmanFootrule = _ at hp
  change C.spearmanRho = _ at hr
  let a := RhoFootrule.UpperParameter.right (RhoFootrule.rightFamily 1 (by decide) unitHalf)
  have ha : a.footrule = 5 / 32 := by
    norm_num [a, RhoFootrule.UpperParameter.footrule, RhoFootrule.rightFamily, unitHalf]
  have h := a.maximizes C (hp.trans ha.symm)
  rw [hr] at h
  norm_num [a, RhoFootrule.UpperParameter.rho, RhoFootrule.rightFamily, unitHalf] at h

-- The singular minimum-footrule fibre is completely filled.
example : (-1 / 2, -3 / 4) ∈ attainable .footrule .rho := by
  rw [attainable_footrule_rho_iff]
  refine ⟨by norm_num, by norm_num [RhoFootrule.lowerBoundary], ?_⟩
  refine ⟨.left (RhoFootrule.leftFamily 1 (by decide) 0), ?_, ?_⟩ <;>
    norm_num [RhoFootrule.UpperParameter.footrule, RhoFootrule.UpperParameter.rho,
      RhoFootrule.leftFamily]

example : (1, 0) ∉ attainable .footrule .rho := by
  rw [attainable_footrule_rho_iff]
  norm_num [RhoFootrule.lowerBoundary]

#print axioms attainable_footrule_rho_iff
#print axioms RhoFootrule.RightData.supporting_bound
#print axioms RhoFootrule.LeftData.supporting_bound

-- A rational non-junction point on the sharp rho–gamma boundary.
private noncomputable def gammaTestParameter : RhoGamma.UpperParameter :=
  .halfShift (11 / 8) (by norm_num)

private theorem gammaTest_coordinates :
    gammaTestParameter.gamma = 23 / 81 ∧ gammaTestParameter.rho = 455 / 729 := by
  have hs : Real.sqrt (81 / 64 : ℝ) = 9 / 8 := by
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 81 / 64)
    have hn := Real.sqrt_nonneg (81 / 64 : ℝ)
    nlinarith
  norm_num [gammaTestParameter, RhoGamma.UpperParameter.gamma, RhoGamma.UpperParameter.rho,
    RhoGamma.gammaValue, RhoGamma.rhoValue, RhoGamma.centralLength,
    RhoGamma.cornerLength, RhoGamma.splitRatio, hs]

example : (23 / 81, 455 / 729) ∈ attainable .gamma .rho := by
  rw [mem_attainable_iff]
  exact ⟨gammaTestParameter.copula,
    gammaTestParameter.gamma_coefficient.trans gammaTest_coordinates.1,
    gammaTestParameter.rho_coefficient.trans gammaTest_coordinates.2⟩

example : (-(23 / 81), -(455 / 729)) ∈ attainable .gamma .rho := by
  rw [mem_attainable_iff]
  refine ⟨gammaTestParameter.copula.reflect {1}, ?_, ?_⟩
  · change (gammaTestParameter.copula.reflect {1}).giniGamma = _
    rw [giniGamma_reflect_second, gammaTestParameter.gamma_coefficient,
      gammaTest_coordinates.1]
  · change (gammaTestParameter.copula.reflect {1}).spearmanRho = _
    rw [spearmanRho_reflect_second, gammaTestParameter.rho_coefficient,
      gammaTest_coordinates.2]

example : (23 / 81, 5 / 8) ∉ attainable .gamma .rho := by
  rw [mem_attainable_iff]
  rintro ⟨C, hg, hr⟩
  change C.giniGamma = _ at hg
  change C.spearmanRho = _ at hr
  have h := gammaTestParameter.maximizes C (hg.trans gammaTest_coordinates.1.symm)
  rw [hr, gammaTest_coordinates.2] at h
  norm_num at h

#print axioms attainable_gamma_rho_iff
#print axioms RhoGamma.AuxiliaryCertificate.supporting_bound


-- The exact SPT region: an interior point, both endpoint fibres, and an exclusion.
example : (1 / 4, 0) ∈ attainable .rho .tau := by
  rw [attainable_rho_tau_iff]
  refine ⟨by norm_num, ⟨.arc 0 0, ?_, ?_⟩, ⟨.arc 0 0, ?_, ?_⟩⟩ <;>
    norm_num [RhoTau.LowerParameter.tau, RhoTau.LowerParameter.rho,
      RhoTau.arcTau, RhoTau.arcRho]

example : (-1, -1) ∈ attainable .rho .tau := by
  rw [attainable_rho_tau_iff]
  refine ⟨by norm_num, ⟨.endpoint, rfl, le_rfl⟩, ⟨.arc 0 1, ?_, ?_⟩⟩ <;>
    norm_num [RhoTau.LowerParameter.tau, RhoTau.LowerParameter.rho,
      RhoTau.arcTau, RhoTau.arcRho]

example : (1, 1) ∈ attainable .rho .tau := by
  rw [attainable_rho_tau_iff]
  refine ⟨by norm_num, ⟨.arc 0 1, ?_, ?_⟩, ⟨.endpoint, rfl, ?_⟩⟩ <;>
    norm_num [RhoTau.LowerParameter.tau, RhoTau.LowerParameter.rho,
      RhoTau.arcTau, RhoTau.arcRho]

example : (3 / 4, 0) ∉ attainable .rho .tau := by
  rw [attainable_rho_tau_iff]
  rintro ⟨_, _, b, hbt, hbr⟩
  let a : RhoTau.LowerParameter := .arc 0 0
  have ha : a.tau = 0 ∧ a.rho = -1 / 2 := by
    norm_num [a, RhoTau.LowerParameter.tau, RhoTau.LowerParameter.rho,
      RhoTau.arcTau, RhoTau.arcRho]
  have hb := (b.tau_eq_iff a).mp (by rw [hbt, ha.1, neg_zero])
  rw [ha.2] at hb
  linarith

-- The finite extremal reduction and limiting argument introduce no extra axioms.
#print axioms RhoTau.finite_sharp_bound
#print axioms RhoTau.boundaryMap_le_rho
#print axioms attainable_rho_tau_iff

-- A point outside a curved SPT arc, away from all junctions.
example : (-3 / 4, -1 / 4) ∉ attainable .rho .tau := by
  rw [attainable_rho_tau_iff]
  rintro ⟨_, ⟨a, hat, har⟩, _⟩
  let b : RhoTau.LowerParameter := .arc 1 unitHalf
  have hb : b.tau = -1 / 4 ∧ b.rho = -101 / 144 := by
    norm_num [b, RhoTau.LowerParameter.tau, RhoTau.LowerParameter.rho,
      RhoTau.arcTau, RhoTau.arcRho, unitHalf]
  have ha := (a.tau_eq_iff b).mp (hat.trans hb.1.symm)
  rw [hb.2] at ha
  linarith
