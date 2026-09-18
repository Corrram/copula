import Copula
import Mathlib.Tactic.NormNum

/-! Public API examples, including the empty dimension and dependent coordinates. -/

noncomputable section

open ProbabilityTheory MeasureTheory
open scoped unitInterval

namespace CopulaTest

def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

def threeQuarters : I := ⟨3 / 4, by norm_num, by norm_num⟩

-- The empty product is one, so groundedness must not be stated in dimension zero.
example : (Copula.independence 0).cdf (fun _ => 0) = 1 := by simp

example : (Copula.comonotonic 0).cdf (fun _ => 0) = 1 := by simp

-- Two concrete copulas have different CDFs at the same point.
example : (Copula.independence 2).cdf (fun _ => half) = 1 / 4 := by
  norm_num [Copula.cdf_independence, Fin.prod_univ_two, half]

example : (Copula.comonotonic 2).cdf (fun _ => half) = 1 / 2 := by
  simp [half]

-- The uniform marginal is available for every copula.
example (C : Copula 2) : C.cdf (Function.update (fun _ => 1) 0 half) = 1 / 2 := by
  simp [half]

example (C : Copula 2) : C.cdf ![0, half] = 0 :=
  C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl

-- Reindexing can repeat a coordinate as well as select one.
example (C : Copula 1) : Copula 3 := C.reindex (fun _ => 0)

example (C : Copula 2) (ρ : Fin 2 ≃ Fin 2) : (C.reindex ρ).reindex ρ.symm = C := by
  simp

-- The measure accessor participates in mathlib's probability API.
example (C : Copula 2) : C.toMeasure Set.univ = 1 := measure_univ

-- The lower bound is nontrivial even without any dependence assumptions.
example (C : Copula 2) : 1 / 2 ≤ C.cdf (fun _ => threeQuarters) := by
  have h := C.frechet_lower_le_cdf (fun _ => threeQuarters)
  norm_num [Fin.sum_univ_two, threeQuarters] at h
  exact h

-- The comonotonic copula attains the universal upper bound in every dimension.
example {d : ℕ} (C : Copula d) (u : Fin d → I) : C.cdf u ≤ (Copula.comonotonic d).cdf u := by
  simpa only [Copula.cdf_comonotonic] using C.cdf_le_frechet_upper u

example (C : Copula 0) : 1 ≤ C.cdf (fun _ => 0) := by
  convert C.frechet_lower_le_cdf (fun _ => 0) using 1
  norm_num

example (C : Copula 2) :
    |C.cdf (fun _ => threeQuarters) - C.cdf (fun _ => half)| ≤ 1 / 2 := by
  have h := C.abs_cdf_sub_le_sum_abs (fun _ => threeQuarters) (fun _ => half)
  norm_num [Fin.sum_univ_two, threeQuarters, half] at h
  exact h

-- The default Pi metric is the maximum metric, so its Lipschitz constant is d.
example (C : Copula 2) : LipschitzWith 2 C.cdf := C.lipschitzWith_cdf

example (C : Copula 0) : LipschitzWith 0 C.cdf := by
  simpa only [Nat.cast_zero] using C.lipschitzWith_cdf

example (C : Copula 2) (ρ : Fin 3 → Fin 2) : Continuous (C.reindex ρ).cdf :=
  (C.reindex ρ).continuous_cdf

-- CDF extensionality handles both the empty product and a single coordinate.
example (C D : Copula 0) : C = D := by
  apply Copula.ext_cdf
  intro u
  simp

example : Copula.independence 1 = Copula.comonotonic 1 := by
  apply Copula.ext_cdf
  intro u
  have hu : u = fun _ => u 0 := funext fun i => congrArg u (Subsingleton.elim i 0)
  rw [hu]
  simp

-- Reflections preserve the law after applying the same transformation twice.
example (C : Copula 3) : (C.reflect {0, 2}).reflect {0, 2} = C := by simp

example : (Copula.comonotonic 2).reflect {1} = Copula.countermonotonic :=
  Copula.reflect_comonotonic_eq_countermonotonic

example : Copula.countermonotonic.cdf (fun _ => half) = 0 := by
  norm_num [Copula.cdf_countermonotonic, half]

example : Copula.countermonotonic.cdf (fun _ => threeQuarters) = 1 / 2 := by
  norm_num [Copula.cdf_countermonotonic, threeQuarters]

example (C : Copula 1) : C = Copula.independence 1 := Subsingleton.elim _ _

example (C : Copula 0) :
    Copula.rectangleIncrement C.cdf (fun _ => 0) (fun _ => 1) = 1 := by
  rw [C.rectangleIncrement_cdf _ _ (by intro i; exact Fin.elim0 i)]
  have he : Set.pi Set.univ (fun _ : Fin 0 => Set.Ioc (0 : I) 1) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x i _
    exact Fin.elim0 i
  rw [he, probReal_univ]

example (C : Copula 2) (a b : Fin 2 → I) (hab : a ≤ b) :
    0 ≤ C.cdf b - C.cdf ![a 0, b 1] - C.cdf ![b 0, a 1] + C.cdf a := by
  rw [← Copula.rectangleIncrement_two]
  exact C.rectangleIncrement_cdf_nonneg a b hab

example (C : Copula 3) : Copula.IsClassical C.cdf := C.isClassical_cdf

-- The continuous-marginal theorem asserts both existence and full uniqueness.
example (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (Copula.marginal μ i))) :
    ∃! C : Copula 2, Copula.IsSklarCopula μ C :=
  Copula.existsUnique_sklarCopula_of_continuous μ hc

-- A correlation matrix yields an actual copula with uniform marginals.
example (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosSemidef) (hd : ∀ i, R i i = 1) :
    (Copula.gaussian R hR hd).cdf (Function.update (fun _ => 1) 0 half) = 1 / 2 := by
  simp [half]

-- General Sklar existence includes purely atomic laws.
example (a : Fin 2 → ℝ) :
    ∃ C : Copula 2, Copula.IsSklarCopula ⟨Measure.dirac a, inferInstance⟩ C :=
  Copula.exists_sklarCopula _

example : (Copula.clayton 2 1 (by norm_num)).cdf (fun _ => 1) = 1 := by simp

-- The low-dimensional entry point remains available.
example (F : (Fin 1 → I) → ℝ) (hF : Copula.IsClassical F) : ∃! C : Copula 1, C.cdf = F :=
  hF.existsUnique_dim_one

-- Classical functions can now be turned into bundled copulas in every dimension.
example (F : (Fin 3 → I) → ℝ) (hF : Copula.IsClassical F) :
    (Copula.ofClassical F hF).cdf = F := by simp

example (C : Copula 0) : Copula.ofClassical C.cdf C.isClassical_cdf = C := by simp

example (C : Copula 2) : Copula.ofClassical C.cdf C.isClassical_cdf = C := by simp

-- Identity and singular all-ones correlation matrices recover the expected laws.
example : Copula.gaussian (1 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.PosSemidef.one (by simp) =
    Copula.independence 2 := by simp

example : (Copula.gaussian (Matrix.of (fun (_ _ : Fin 2) => (1 : ℝ)))
    (Copula.posSemidef_allOnes 2) (fun _ => rfl)).cdf (fun _ => half) = 1 / 2 := by
  simp [half]

-- The gamma-frailty construction agrees with a concrete textbook Clayton value.
example : (Copula.clayton 2 1 (by norm_num)).cdf (fun _ => half) = 1 / 3 := by
  rw [Copula.cdf_clayton 1 (by norm_num) _ (by intro i; norm_num [half])]
  norm_num [Fin.sum_univ_two, half, Real.rpow_neg_one]

example (θ : ℝ) (hθ : 0 < θ) : (Copula.clayton 0 θ hθ).cdf (fun _ => 0) = 1 := by simp

example (θ : ℝ) (hθ : 0 < θ) : (Copula.clayton 2 θ hθ).cdf ![0, half] = 0 :=
  Copula.cdf_clayton_of_zero θ hθ _ 0 rfl

-- Parameter-limit statements apply directly to arbitrary positive sequences.
example (θ : ℕ → ℝ) (hθ : ∀ n, 0 < θ n)
    (ht : Filter.Tendsto θ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (Copula.clayton 2 (θ n) (hθ n)).cdf (fun _ => half))
      Filter.atTop (nhds (1 / 4)) := by
  have he : (Copula.independence 2).cdf (fun _ => half) = 1 / 4 := by
    norm_num [Copula.cdf_independence, Fin.prod_univ_two, half]
  simpa only [he] using Copula.tendsto_clayton_zero θ hθ ht (fun _ : Fin 2 => half)

example (θ : ℕ → ℝ) (hθ : ∀ n, 0 < θ n) (ht : Filter.Tendsto θ Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => (Copula.clayton 2 (θ n) (hθ n)).cdf (fun _ => half))
      Filter.atTop (nhds (1 / 2)) := by
  simpa [Copula.cdf_comonotonic, half] using
    Copula.tendsto_clayton_atTop θ hθ ht (fun _ : Fin 2 => half)

-- Generator-based families are actual probability measures with uniform marginals.
example (θ : ℝ) (hθ : 1 ≤ θ) : Copula.IsArchimedean (Copula.gumbel θ hθ) :=
  Copula.isArchimedean_gumbel θ hθ

example (θ : ℝ) (hθ : 0 < θ) : Copula.IsArchimedean (Copula.clayton 5 θ hθ) :=
  Copula.isArchimedean_clayton 5 θ hθ

example : Copula.gumbel 1 le_rfl = Copula.independence 2 := by simp

example : Copula.joe 1 le_rfl = Copula.independence 2 := by simp

example (θ : ℝ) (hθ : 0 < θ) : Copula.bb1 θ hθ 1 le_rfl = Copula.clayton 2 θ hθ := by simp

example (θ : ℝ) (hθ : 1 ≤ θ) : Copula.bb6 θ hθ 1 le_rfl = Copula.joe θ hθ := by simp

example (θ : ℝ) (hθ : 0 < θ) : (Copula.frank θ hθ).cdf ![0, half] = 0 :=
  Copula.cdf_eq_zero_of_coord_eq_zero _ _ 0 rfl

example (θ : ℝ) (hθ : 0 < θ) :
    (Copula.frank θ hθ).cdf (Function.update (fun _ => 1) 0 half) = 1 / 2 := by simp [half]

example (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I) (t : ℝ) (ht : 0 < t) :
    (Copula.gumbel θ hθ).cdf (fun i => Copula.unitPower (u i) t ht.le) =
      ((Copula.gumbel θ hθ).cdf u) ^ t := Copula.isExtremeValue_gumbel θ hθ u t ht

example (θ : ℝ) (hθ : 1 ≤ θ) (a b : I) : Copula.IsExtremeValue (Copula.tawn θ hθ a b) :=
  Copula.isExtremeValue_tawn θ hθ a b

example (a : Fin 4 → I) : Copula.IsExtremeValue (Copula.commonShock 4 a) :=
  Copula.isExtremeValue_commonShock 4 a

example : (Copula.commonShock 0 (fun i => Fin.elim0 i)).cdf (fun i => Fin.elim0 i) = 1 := by simp

example : Copula.marshallOlkin 0 0 = Copula.independence 2 := by simp

example : Copula.marshallOlkin 1 1 = Copula.comonotonic 2 := by simp

example : (Copula.marshallOlkin 1 0).cdf (fun _ => half) = 1 / 4 := by
  norm_num [Copula.cdf_marshallOlkin, half]

example (C D : Copula 3) : Copula.maxProduct C D (fun _ => 0) = D := by simp

example (C D : Copula 3) : Copula.maxProduct C D (fun _ => 1) = C := by simp

-- Both signs of the FGM parameter are supported.
example : (Copula.fgm 1 (by norm_num)).cdf (fun _ => half) = 5 / 16 := by
  norm_num [Copula.cdf_fgm, Copula.fgmCDF, half]

example : (Copula.fgm (-1) (by norm_num)).cdf (fun _ => half) = 3 / 16 := by
  norm_num [Copula.cdf_fgm, Copula.fgmCDF, half]

example : Copula.mardia (-1) (by norm_num) = Copula.countermonotonic := by simp

example : Copula.mardia 0 (by norm_num) = Copula.independence 2 := by simp

example : Copula.mardia 1 (by norm_num) = Copula.comonotonic 2 := by simp

example (C D : Copula 2) (a : I) (u : Fin 2 → I) :
    (Copula.mix C D a).cdf u = (a : ℝ) * C.cdf u + (1 - (a : ℝ)) * D.cdf u := by simp

-- Student degrees of freedom need not be integral, or large enough for moments.
example (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.PosSemidef) (hd : ∀ i, R i i = 1) :
    (Copula.studentT R hR hd (1 / 2) (by norm_num)).cdf
      (Function.update (fun _ => 1) 0 half) = 1 / 2 := by simp [half]

example (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosSemidef) (hd : ∀ i, R i i = 1) :
    Copula.studentT R hR hd 1 zero_lt_one = Copula.cauchy R hR hd := by simp

example (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosSemidef) (hd : ∀ i, R i i = 1) :
    Copula.varianceGamma R hR hd 1 zero_lt_one = Copula.laplace R hR hd := by simp

example (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosSemidef) (hd : ∀ i, R i i = 1)
    (ν : ℝ) (hν : 0 < ν) :
    Copula.IsSklarCopula (Copula.studentTLaw R ν hν) (Copula.studentT R hR hd ν hν) :=
  Copula.isSklarCopula_studentT R hR hd ν hν

-- Singular dispersion matrices are accepted by the elliptical mixture construction.
example : (Copula.slash (Matrix.of (fun (_ _ : Fin 2) => (1 : ℝ)))
    (Copula.posSemidef_allOnes 2) (fun _ => rfl) 1 zero_lt_one).cdf (fun _ => 1) = 1 := by simp

example (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosSemidef) (hd : ∀ i, R i i = 1) :
    (Copula.normalLognormal R hR hd 0).cdf (Function.update (fun _ => 1) 0 half) = 1 / 2 := by
  simp [half]

-- All six population coefficients have proved sharp range bounds.
example (C : Copula 2) : C.spearmanRho ∈ Set.Icc (-1) 1 := C.spearmanRho_mem_Icc

example (C : Copula 2) : C.kendallTau ∈ Set.Icc (-1) 1 := C.kendallTau_mem_Icc

example (C : Copula 2) : C.spearmanFootrule ∈ Set.Icc (-1 / 2) 1 := C.spearmanFootrule_mem_Icc

example (C : Copula 2) : C.giniGamma ∈ Set.Icc (-1) 1 := C.giniGamma_mem_Icc

example (C : Copula 2) : C.blomqvistBeta ∈ Set.Icc (-1) 1 := C.blomqvistBeta_mem_Icc

example (C : Copula 2) : C.chatterjeeXi ∈ Set.Icc 0 1 := C.chatterjeeXi_mem_Icc

-- Each triple is (independence, comonotonicity, countermonotonicity).
example : ((Copula.independence 2).spearmanRho, (Copula.comonotonic 2).spearmanRho,
    Copula.countermonotonic.spearmanRho) = (0, 1, -1) := by simp

example : ((Copula.independence 2).kendallTau, (Copula.comonotonic 2).kendallTau,
    Copula.countermonotonic.kendallTau) = (0, 1, -1) := by simp

example : ((Copula.independence 2).spearmanFootrule, (Copula.comonotonic 2).spearmanFootrule,
    Copula.countermonotonic.spearmanFootrule) = (0, 1, -1 / 2) := by simp

example : ((Copula.independence 2).giniGamma, (Copula.comonotonic 2).giniGamma,
    Copula.countermonotonic.giniGamma) = (0, 1, -1) := by simp

example : ((Copula.independence 2).blomqvistBeta, (Copula.comonotonic 2).blomqvistBeta,
    Copula.countermonotonic.blomqvistBeta) = (0, 1, -1) := by simp

example : ((Copula.independence 2).chatterjeeXi, (Copula.comonotonic 2).chatterjeeXi,
    Copula.countermonotonic.chatterjeeXi) = (0, 1, 1) := by simp

example (C : Copula 2) :
    C.spearmanRho = 12 * (∫ x, C.cdf x ∂(Copula.independence 2).toMeasure) - 3 :=
  C.spearmanRho_eq_integral_cdf

example (C D : Copula 2) (h : ∀ u, C.cdf u ≤ D.cdf u) : C.spearmanRho ≤ D.spearmanRho :=
  Copula.spearmanRho_mono h

example (C D : Copula 2) (a : I) : (Copula.mix C D a).spearmanRho =
    (a : ℝ) * C.spearmanRho + (1 - (a : ℝ)) * D.spearmanRho := Copula.spearmanRho_mix C D a

example (C D : Copula 2) (a : I) : (Copula.mix C D a).spearmanFootrule =
    (a : ℝ) * C.spearmanFootrule + (1 - (a : ℝ)) * D.spearmanFootrule :=
  Copula.spearmanFootrule_mix C D a

example (C D : Copula 2) (a : I) : (Copula.mix C D a).giniGamma =
    (a : ℝ) * C.giniGamma + (1 - (a : ℝ)) * D.giniGamma := Copula.giniGamma_mix C D a

example (C D : Copula 2) (a : I) : (Copula.mix C D a).blomqvistBeta =
    (a : ℝ) * C.blomqvistBeta + (1 - (a : ℝ)) * D.blomqvistBeta := Copula.blomqvistBeta_mix C D a

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).spearmanRho = θ / 3 :=
  Copula.spearmanRho_fgm θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).spearmanFootrule = θ / 5 :=
  Copula.spearmanFootrule_fgm θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).giniGamma = 4 * θ / 15 :=
  Copula.giniGamma_fgm θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).blomqvistBeta = θ / 4 :=
  Copula.blomqvistBeta_fgm θ hθ

-- The direction is the second coordinate given the first; densities are unnecessary.
example (C : Copula 2) {f : I → I} (hf : Measurable f)
    (h : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)) : C.chatterjeeXi = 1 :=
  C.chatterjeeXi_eq_one_of_function hf h

example (C : Copula 2) (t : I) : (∫ u : I, C.conditionalCDF u t) = (t : ℝ) :=
  C.integral_conditionalCDF t

example (C : Copula 2) :
    C.chatterjeeXi = 6 * (∫ t : I, ∫ u : I, (C.conditionalCDF u t - (t : ℝ)) ^ 2) :=
  C.chatterjeeXi_eq_integral_centered_sq

example (C : Copula 2) : (C.reindex ![1, 0]).chatterjeeXi ∈ Set.Icc 0 1 :=
  (C.reindex ![1, 0]).chatterjeeXi_mem_Icc

-- Positive dependence is directional for SI and the two tail properties.
example (C : Copula 2) (h : C.IsSI) : C.IsLTD ∧ C.IsRTI ∧ C.IsPQD :=
  ⟨h.isLTD, h.isRTI, h.isPQD⟩

example (C : Copula 2) (h : C.IsLTD) : C.IsPQD := h.isPQD

example (C : Copula 2) (h : C.IsRTI) : C.IsPQD := h.isPQD

example (C : Copula 2) (h : C.IsTP2CDF) : C.IsLTD ∧ (C.reindex ![1, 0]).IsLTD :=
  ⟨h.isLTD, h.isLTD_swap⟩

example (C : Copula 2) (h : C.HasTP2Kernel) : C.IsSI := h.isSI

example (C : Copula 2) (h : C.IsLTD) (v : I) :
    AntitoneOn (fun u : I => C.cdf ![u, v] / (u : ℝ)) (Set.Ioi 0) :=
  (Copula.isLTD_iff_ratio_antitone C).mp h v

example (C : Copula 2) (h : C.IsRTI) (v : I) :
    MonotoneOn (fun u : I => (1 - (u : ℝ) - (v : ℝ) + C.cdf ![u, v]) / (1 - (u : ℝ)))
      (Set.Iio 1) := (Copula.isRTI_iff_survivalRatio_monotone C).mp h v

example (C D : Copula 2) (hC : C.IsSI) (hD : D.IsSI) (a : I) :
    (Copula.mix C D a).IsSI := hC.mix hD a

example (C D : Copula 2) (hC : C.IsLTD) (hD : D.IsLTD) (a : I) :
    (Copula.mix C D a).IsLTD := hC.mix hD a

example (C D : Copula 2) (hC : C.IsRTI) (hD : D.IsRTI) (a : I) :
    (Copula.mix C D a).IsRTI := hC.mix hD a

example (C D : Copula 2) (hC : C.IsPQD) (hD : D.IsPQD) (a : I) :
    (Copula.mix C D a).IsPQD := hC.mix hD a

example (C : Copula 2) : (C.reindex ![1, 0]).IsPQD ↔ C.IsPQD :=
  Copula.isPQD_reindex_swap_iff C

example (C : Copula 2) : (C.reindex ![1, 0]).IsTP2CDF ↔ C.IsTP2CDF :=
  Copula.isTP2CDF_reindex_swap_iff C

example (C : Copula 2) (h : C.IsPQD) :
    0 ≤ C.spearmanRho ∧ 0 ≤ C.kendallTau ∧ 0 ≤ C.spearmanFootrule ∧
      0 ≤ C.giniGamma ∧ 0 ≤ C.blomqvistBeta :=
  ⟨h.spearmanRho_nonneg, h.kendallTau_nonneg, h.spearmanFootrule_nonneg,
    h.giniGamma_nonneg, h.blomqvistBeta_nonneg⟩

example (C : Copula 2) (h : C.IsPQD) : C.spearmanRho ≤ 3 * C.kendallTau :=
  h.spearmanRho_le_three_mul_kendallTau

example : (Copula.independence 0).HasMTP2Density := Copula.hasMTP2Density_independence 0

example : (Copula.independence 4).HasMTP2Density := Copula.hasMTP2Density_independence 4

example : (Copula.comonotonic 2).HasTP2Kernel ∧ ¬ (Copula.comonotonic 2).HasMTP2Density :=
  ⟨Copula.hasTP2Kernel_comonotonic, Copula.not_hasMTP2Density_comonotonic⟩

example : ¬ Copula.countermonotonic.IsPQD := Copula.not_isPQD_countermonotonic

example : ¬ Copula.countermonotonic.IsSI := Copula.not_isSI_countermonotonic

example : ¬ Copula.countermonotonic.HasTP2Kernel := Copula.not_hasTP2Kernel_countermonotonic

example (C : Copula 2) : C.IsPQD ∧ C.IsNQD ↔ C = Copula.independence 2 :=
  Copula.isPQD_and_isNQD_iff C

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).IsSI ↔ 0 ≤ θ :=
  Copula.isSI_fgm_iff θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).IsLTD ↔ 0 ≤ θ :=
  Copula.isLTD_fgm_iff θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).IsRTI ↔ 0 ≤ θ :=
  Copula.isRTI_fgm_iff θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).IsTP2CDF ↔ 0 ≤ θ :=
  Copula.isTP2CDF_fgm_iff θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) (hpos : 0 ≤ θ) : (Copula.fgm θ hθ).HasMTP2Density :=
  Copula.hasMTP2Density_fgm θ hθ hpos

example : ¬ (Copula.fgm (-1 / 2) (by norm_num)).IsPQD := by
  rw [Copula.isPQD_fgm_iff]
  norm_num

example (θ : ℝ) : IsMTP2 (Copula.fgmDensity θ) ↔ 0 ≤ θ :=
  Copula.isMTP2_fgmDensity_iff θ

example (d : ℕ) (f : Fin d → I → ℝ) : IsMTP2 (fun x : Fin d → I => ∏ i, f i (x i)) :=
  isMTP2_prod f

example (C : Copula 2) (u v : I) : C.cdf ![u, v] = ∫ t in Set.Iic u, C.conditionalCDF t v :=
  C.cdf_eq_integral_conditionalCDF u v

example {d : ℕ} (C D : Copula d) (h : C.SupermodularLE D) : C.ConcordanceLE D :=
  h.concordanceLE

example (C D : Copula 2) : C.UpperOrthantLE D ↔ C.LowerOrthantLE D :=
  Copula.upperOrthantLE_iff_lowerOrthantLE C D

example (C D : Copula 2) : C.ConcordanceLE D ↔ C.LowerOrthantLE D :=
  Copula.concordanceLE_iff_lowerOrthantLE C D

example {d : ℕ} (C D : Copula d) (h : C.LowerOrthantLE D) (k : D.LowerOrthantLE C) :
    C = D := h.antisymm k

example {d : ℕ} (C D : Copula d) (h : C.UpperOrthantLE D) (k : D.UpperOrthantLE C) :
    C = D := h.antisymm k

example (C D : Copula 2) (h : C.LowerOrthantLE D) : C.kendallTau ≤ D.kendallTau :=
  h.kendallTau_le

example (C D : Copula 2) (h : C.LowerOrthantLE D) : C.spearmanRho ≤ D.spearmanRho :=
  h.spearmanRho_le

example (C : Copula 2) : Copula.countermonotonic.ConcordanceLE C :=
  Copula.concordanceLE_countermonotonic C

example (C : Copula 2) : C.ConcordanceLE (Copula.comonotonic 2) :=
  Copula.concordanceLE_comonotonic C

example (C : Copula 2) : C.IsPQD ↔ (Copula.independence 2).LowerOrthantLE C :=
  Copula.isPQD_iff_lowerOrthantLE C

example (C : Copula 2) (u : Fin 2 → I) :
    C.survival u = 1 - (u 0 : ℝ) - (u 1 : ℝ) + C.cdf u := C.survival_two u

example {d : ℕ} (C D : Copula d) :
    C.UpperOrthantLE D ↔
      (C.reflect Finset.univ).LowerOrthantLE (D.reflect Finset.univ) :=
  Copula.upperOrthantLE_iff_reflect C D

example {d : ℕ} (C D : Copula d) (h : C.LowerOrthantLE D) {a b : I} (hab : a ≤ b) :
    (D.mix C a).LowerOrthantLE (D.mix C b) := h.mix_weight hab

example {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (Copula.fgm θ hθ).ConcordanceLE (Copula.fgm η hη) ↔ θ ≤ η :=
  Copula.concordanceLE_fgm_iff hθ hη

example (C D : Copula 2) (h : C.SchurLE D) : C.chatterjeeXi ≤ D.chatterjeeXi :=
  h.chatterjeeXi_le

example (C : Copula 2) : (Copula.independence 2).SchurLE C := Copula.schurLE_independence C

example (C : Copula 2) : C.SchurLE (Copula.independence 2) ↔ C = Copula.independence 2 :=
  Copula.schurLE_independence_iff C

example : (Copula.comonotonic 2).SchurLE Copula.countermonotonic :=
  Copula.schurLE_countermonotonic _

example : Copula.countermonotonic.SchurLE (Copula.comonotonic 2) :=
  Copula.schurLE_comonotonic _

example : ¬ Copula.countermonotonic.SchurLE (Copula.independence 2) :=
  Copula.not_schurLE_countermonotonic_independence

example : ¬ (Copula.comonotonic 2).LowerOrthantLE Copula.countermonotonic :=
  Copula.not_lowerOrthantLE_comonotonic_countermonotonic

example : (Copula.independence 0).ConcordanceLE (Copula.independence 0) :=
  Copula.ConcordanceLE.refl _

example (C : Copula 2) : C.diagonal 0 = 0 ∧ C.diagonal 1 = 1 := by simp

example (C : Copula 2) {s t : I} (h : s ≤ t) :
    C.diagonal t - C.diagonal s ∈ Set.Icc 0 (2 * ((t : ℝ) - (s : ℝ))) :=
  C.diagonal_sub_mem_Icc h

example (C : Copula 2) : (∀ t : I, C.diagonal t = (t : ℝ)) ↔ C = Copula.comonotonic 2 :=
  C.diagonal_eq_id_iff

example (C : Copula 2) (t : I) : C.toMeasure.real {x | max (x 0) (x 1) ≤ t} = C.diagonal t :=
  C.measureReal_max_le t

example (C : Copula 2) (t : I) :
    C.toMeasure.real {x | min (x 0) (x 1) ≤ t} = 2 * (t : ℝ) - C.diagonal t :=
  C.measureReal_min_le t

example (C : Copula 2) (u v : I) :
    (C.reflect {0}).cdf ![u, v] = (v : ℝ) - C.cdf ![unitInterval.symm u, v] :=
  C.cdf_reflect_first u v

example (C : Copula 2) (u v : I) :
    (C.reflect {1}).cdf ![u, v] = (u : ℝ) - C.cdf ![u, unitInterval.symm v] :=
  C.cdf_reflect_second u v

example (C : Copula 2) : (C.mix C.transpose Copula.unitHalf).IsExchangeable :=
  C.isExchangeable_symmetrize

example (C : Copula 2) : (C.mix C.survivalCopula Copula.unitHalf).IsRadiallySymmetric :=
  C.isRadiallySymmetric_symmetrize

example (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).IsExchangeable ∧ (Copula.fgm θ hθ).IsRadiallySymmetric :=
  ⟨Copula.isExchangeable_fgm θ hθ, Copula.isRadiallySymmetric_fgm θ hθ⟩

example (C : Copula 2) : C.transpose.kendallTau = C.kendallTau := by simp

example (C : Copula 2) : C.transpose.giniGamma = C.giniGamma := by simp

example (C : Copula 2) : (C.reflect {0}).spearmanRho = -C.spearmanRho :=
  C.spearmanRho_reflect_first

example (C : Copula 2) : (C.reflect {1}).kendallTau = -C.kendallTau :=
  C.kendallTau_reflect_second

example (C : Copula 2) : (C.reflect {0}).giniGamma = -C.giniGamma :=
  C.giniGamma_reflect_first

example (C : Copula 2) : C.survivalCopula.spearmanFootrule = C.spearmanFootrule := by simp

example (C : Copula 2) : C.survivalCopula.kendallTau = C.kendallTau := by simp

example (C : Copula 2) {l : ℝ} (h : C.HasLowerTailDependence l) : l ∈ Set.Icc 0 1 := h.mem_Icc

example (C : Copula 2) {l : ℝ} (h : C.HasUpperTailDependence l) : l ∈ Set.Icc 0 1 := h.mem_Icc

example (C : Copula 2) (l : ℝ) :
    C.HasUpperTailDependence l ↔ C.survivalCopula.HasLowerTailDependence l :=
  C.hasUpperTailDependence_iff_survivalCopula l

example (C : Copula 2) (l : ℝ) : C.transpose.HasLowerTailDependence l ↔ C.HasLowerTailDependence l :=
  C.hasLowerTailDependence_transpose_iff l

example : (Copula.independence 2).HasLowerTailDependence 0 := Copula.hasLowerTailDependence_independence

example : (Copula.comonotonic 2).HasUpperTailDependence 1 := Copula.hasUpperTailDependence_comonotonic

example : Copula.countermonotonic.HasLowerTailDependence 0 := Copula.hasLowerTailDependence_countermonotonic

example : ¬ (Copula.independence 2).HasLowerTailDependence 1 := by
  intro h
  have he := h.unique Copula.hasLowerTailDependence_independence
  norm_num at he

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).HasUpperTailDependence 0 :=
  Copula.hasUpperTailDependence_fgm θ hθ

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).HasLowerTailDependence a :=
  Copula.hasLowerTailDependence_frechet a b ha hb hab

example (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).HasUpperTailDependence (θ ^ 2 * (1 + θ) / 2) :=
  Copula.hasUpperTailDependence_mardia θ hθ

example (w : I) : ((Copula.comonotonic 2).mix (Copula.independence 2) w).HasLowerTailDependence w := by
  simpa using Copula.hasLowerTailDependence_comonotonic.mix Copula.hasLowerTailDependence_independence w

example (C D : Copula 2) (h : C.LowerOrthantLE D) {a b : ℝ}
    (ha : C.HasUpperTailDependence a) (hb : D.HasUpperTailDependence b) : a ≤ b :=
  h.upperTailDependence_le ha hb

-- Ansari–Rockel family coverage and convention checks.
example (C D : Copula 2) (hC : C.IsArchimedean) (hD : D.IsArchimedean) :
    C.SchurBothLE D ↔ C.SchurLE D := Copula.schurBothLE_iff_of_archimedean hC hD

example (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.nelsen2 θ hθ).IsArchimedean :=
  Copula.isArchimedean_nelsen2 θ hθ

example (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.genestGhoudi θ hθ).IsExchangeable :=
  (Copula.isArchimedean_genestGhoudi θ hθ).isExchangeable

example (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (Copula.nelsen12 θ hθ).cdf u =
      (1 + (((u 0 : ℝ)⁻¹ - 1) ^ θ + ((u 1 : ℝ)⁻¹ - 1) ^ θ) ^ θ⁻¹)⁻¹ :=
  Copula.cdf_nelsen12 θ hθ u hu

example (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.nelsen14 θ hθ).IsArchimedean :=
  Copula.isArchimedean_nelsen14 θ hθ

example : Copula.nelsen2 1 le_rfl = Copula.countermonotonic := Copula.nelsen2_one
example : Copula.genestGhoudi 1 le_rfl = Copula.countermonotonic := Copula.genestGhoudi_one
example : Copula.nelsen12 1 le_rfl = Copula.clayton 2 1 (by norm_num) := Copula.nelsen12_one
example : Copula.nelsen14 1 le_rfl = Copula.clayton 2 1 (by norm_num) := Copula.nelsen14_one

example : Copula.claytonNegative (-1) le_rfl (by norm_num) = Copula.countermonotonic :=
  Copula.claytonNegative_neg_one

example (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (Copula.claytonNegative θ hθ hn).IsArchimedean :=
  Copula.isArchimedean_claytonNegative θ hθ hn

example (C : Copula 2) (h : C.IsArchimedean) : C.IsCI ↔ C.IsSI := h.isCI_iff
example (C : Copula 2) : (C.reflect {1}).IsSI ↔ C.IsSD := C.isSI_reflect_second_iff
example : (Copula.independence 2).IsCI ∧ (Copula.independence 2).IsCD :=
  ⟨Copula.isCI_independence, Copula.isCD_independence⟩

example : Copula.countermonotonic.IsCD := Copula.isCD_countermonotonic
example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).IsCD ↔ θ ≤ 0 :=
  Copula.isCD_fgm_iff θ hθ

example (θ : I) : (Copula.nelsen7 θ).IsCD := Copula.isCD_nelsen7 θ
example (θ u v : I) : (Copula.nelsen7 θ).cdf ![u, v] =
    max 0 ((θ : ℝ) * (u : ℝ) * (v : ℝ) + (1 - (θ : ℝ)) * ((u : ℝ) + (v : ℝ) - 1)) :=
  Copula.cdf_nelsen7 θ u v

example : Copula.nelsen7 0 = Copula.countermonotonic := Copula.nelsen7_zero
example : Copula.nelsen7 1 = Copula.independence 2 := Copula.nelsen7_one
example {θ η : I} (h : θ ≤ η) : (Copula.nelsen7 θ).LowerOrthantLE (Copula.nelsen7 η) :=
  Copula.lowerOrthantLE_nelsen7 h

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).kendallTau = 2 * θ / 9 :=
  Copula.kendallTau_fgm θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.fgm θ hθ).chatterjeeXi = θ ^ 2 / 15 :=
  Copula.chatterjeeXi_fgm θ hθ

example (θ : ℝ) (hθ : |θ| ≤ 1) (v : I) :
    (fun u => (Copula.fgm θ hθ).conditionalCDF u v) =ᵐ[MeasureTheory.volume]
      fun u => Copula.fgmConditionalCDF θ u v := Copula.conditionalCDF_fgm θ hθ v

example {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (Copula.fgm θ hθ).SchurLE (Copula.fgm η hη) ↔ |θ| ≤ |η| := Copula.schurLE_fgm_iff hθ hη

example {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (Copula.fgm θ hθ).SchurBothLE (Copula.fgm η hη) ↔ |θ| ≤ |η| :=
  Copula.schurBothLE_fgm_iff hθ hη

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).spearmanRho = a - b :=
  Copula.spearmanRho_frechet a b ha hb hab

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.mardia θ hθ).spearmanRho = θ ^ 3 :=
  Copula.spearmanRho_mardia θ hθ

example {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' + b' ≤ 1) (haa : a ≤ a') (hbb : b' ≤ b) :
    (Copula.frechet a b ha hb hab).LowerOrthantLE (Copula.frechet a' b' ha' hb' hab') :=
  Copula.lowerOrthantLE_frechet ha hb hab ha' hb' hab' haa hbb

example : ¬ (Copula.independence 2).LowerOrthantLE Copula.countermonotonic :=
  Copula.not_lowerOrthantLE_independence_countermonotonic

example (C : Copula 2) (f : ℝ → ℝ) (l : ℝ)
    (hf : ∀ t : I, f t = C.diagonal t) (hd : HasDerivWithinAt f l (Set.Icc 0 1) 0) :
    C.HasLowerTailDependence l := Copula.hasLowerTailDependence_of_hasDerivWithinAt hf hd

example (C : Copula 2) (f : ℝ → ℝ) (l : ℝ)
    (hf : ∀ t : I, f t = C.diagonal t) (hd : HasDerivWithinAt f l (Set.Icc 0 1) 1) :
    C.HasUpperTailDependence (2 - l) := Copula.hasUpperTailDependence_of_hasDerivWithinAt hf hd

example (C : Copula 2) (κ : ℝ) (h : C.HasPowerDiagonal κ) : κ ∈ Set.Icc 1 2 := h.mem_Icc

example (C : Copula 2) (h : C.IsExtremeValue) (t : I) :
    C.diagonal t = (t : ℝ) ^ C.extremalCoefficient := h.hasPowerDiagonal t

example (C : Copula 2) (h : C.IsExtremeValue) : C.extremalCoefficient ∈ Set.Icc 1 2 :=
  h.extremalCoefficient_mem_Icc

example (C : Copula 2) (h : C.IsExtremeValue) :
    C.HasUpperTailDependence (2 - C.extremalCoefficient) := h.hasUpperTailDependence

example (C : Copula 2) (h : C.IsExtremeValue) (hne : C ≠ Copula.comonotonic 2) :
    C.HasLowerTailDependence 0 := h.hasLowerTailDependence_zero hne

example (C : Copula 2) (h : C.IsExtremeValue) :
    C.HasUpperTailDependence 1 ↔ C = Copula.comonotonic 2 := h.hasUpperTailDependence_one_iff

example (C D : Copula 2) (h : C.LowerOrthantLE D) (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    D.extremalCoefficient ≤ C.extremalCoefficient := h.extremalCoefficient_antitone hC hD

example (α β : I) : (Copula.marshallOlkin α β).HasUpperTailDependence (min (α : ℝ) (β : ℝ)) :=
  Copula.hasUpperTailDependence_marshallOlkin α β

example (α β : I) :
    (Copula.marshallOlkin α β).HasLowerTailDependence (if α = 1 ∧ β = 1 then 1 else 0) :=
  Copula.hasLowerTailDependence_marshallOlkin α β

example : (Copula.marshallOlkin 1 1).HasLowerTailDependence 1 := by
  simpa using Copula.hasLowerTailDependence_marshallOlkin 1 1

example (β : I) : (Copula.marshallOlkin 0 β).HasUpperTailDependence 0 := by
  simpa only [show ((0 : I) : ℝ) = 0 from rfl, min_eq_left β.property.1] using
    Copula.hasUpperTailDependence_marshallOlkin 0 β

example (α : I) : (Copula.cuadrasAuge α).HasUpperTailDependence (α : ℝ) :=
  Copula.hasUpperTailDependence_cuadrasAuge α

example : (Copula.cuadrasAuge 1).HasLowerTailDependence 1 := by
  simpa using Copula.hasLowerTailDependence_cuadrasAuge 1

example (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.gumbel θ hθ).HasLowerTailDependence 0 :=
  Copula.hasLowerTailDependence_gumbel θ hθ

example (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.gumbel θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  Copula.hasUpperTailDependence_gumbel θ hθ

example (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (Copula.tawn θ hθ α β).HasUpperTailDependence
      ((α : ℝ) + (β : ℝ) - ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) :=
  Copula.hasUpperTailDependence_tawn θ hθ α β

example (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) : (Copula.tawn θ hθ α β).HasLowerTailDependence 0 :=
  Copula.hasLowerTailDependence_tawn θ hθ α β

example (α β : I) : (Copula.tawn 1 le_rfl α β).HasUpperTailDependence 0 := by
  simpa using Copula.hasUpperTailDependence_tawn 1 le_rfl α β

example (C : Copula 2) (h : C.IsExtremeValue) :
    C.spearmanFootrule = 6 / (C.extremalCoefficient + 1) - 2 := h.spearmanFootrule

example (C : Copula 2) (h : C.IsExtremeValue) :
    C.blomqvistBeta = (2 : ℝ) ^ (2 - C.extremalCoefficient) - 1 := h.blomqvistBeta

example (α β : I) :
    (Copula.marshallOlkin α β).spearmanFootrule = 6 / (3 - min (α : ℝ) (β : ℝ)) - 2 :=
  Copula.spearmanFootrule_marshallOlkin α β

example (α : I) : (Copula.cuadrasAuge α).blomqvistBeta = (2 : ℝ) ^ (α : ℝ) - 1 :=
  Copula.blomqvistBeta_cuadrasAuge α

example (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.gumbel θ hθ).spearmanFootrule = 6 / ((2 : ℝ) ^ θ⁻¹ + 1) - 2 :=
  Copula.spearmanFootrule_gumbel θ hθ

example (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (Copula.tawn θ hθ α β).blomqvistBeta =
      (2 : ℝ) ^ ((α : ℝ) + (β : ℝ) - ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) - 1 :=
  Copula.blomqvistBeta_tawn θ hθ α β

example (C : Copula 2) : C.chatterjeeXi = 0 ↔ C = Copula.independence 2 :=
  C.chatterjeeXi_eq_zero_iff

example (C : Copula 2) : 0 < C.chatterjeeXi ↔ C ≠ Copula.independence 2 := C.chatterjeeXi_pos_iff

example (C D : Copula 2) : C.conditionalCDFDistanceSq D = 0 ↔ C = D :=
  C.conditionalCDFDistanceSq_eq_zero_iff D

example (C D : Copula 2)
    (h : ∀ᵐ v : I, (fun u => C.conditionalCDF u v) =ᵐ[MeasureTheory.volume]
      fun u => D.conditionalCDF u v) : C = D := Copula.ext_conditionalCDF_ae h

example (C D : Copula 2) (a v : I) :
    (fun u => (C.mix D a).conditionalCDF u v) =ᵐ[MeasureTheory.volume]
      fun u => (a : ℝ) * C.conditionalCDF u v + (1 - (a : ℝ)) * D.conditionalCDF u v :=
  Copula.conditionalCDF_mix C D a v

example {n : ℕ} (C : Fin n → Copula 2) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (v : I) :
    (fun u => (Copula.finiteMixture C w hw hsum).conditionalCDF u v) =ᵐ[MeasureTheory.volume]
      fun u => ∑ j, w j * (C j).conditionalCDF u v :=
  Copula.conditionalCDF_finiteMixture C w hw hsum v

example (C D : Copula 2) (a : I) :
    (C.mix D a).chatterjeeXi ≤ (a : ℝ) * C.chatterjeeXi + (1 - (a : ℝ)) * D.chatterjeeXi :=
  Copula.chatterjeeXi_mix_le C D a

example (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    (C.mix D a).chatterjeeXi = (a : ℝ) * C.chatterjeeXi + (1 - (a : ℝ)) * D.chatterjeeXi ↔
      C = D := Copula.chatterjeeXi_mix_eq_iff C D a ha0 ha1

example (C : Copula 2) (a : I) :
    (C.mix (Copula.independence 2) a).chatterjeeXi = (a : ℝ) ^ 2 * C.chatterjeeXi :=
  Copula.chatterjeeXi_mix_independence C a

example (C : Copula 2) : C.chatterjeeCross (Copula.comonotonic 2) = C.spearmanFootrule :=
  C.chatterjeeCross_comonotonic

example : ((Copula.comonotonic 2).mix Copula.countermonotonic Copula.unitHalf).chatterjeeXi =
    1 / 4 := by
  rw [Copula.chatterjeeXi_mix_comonotonic_countermonotonic]
  norm_num [Copula.unitHalf]

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).chatterjeeXi = (a - b) ^ 2 + a * b :=
  Copula.chatterjeeXi_frechet a b ha hb hab

example : (Copula.frechet (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)).chatterjeeXi =
    3 / 16 := by rw [Copula.chatterjeeXi_frechet]; norm_num

example (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).chatterjeeXi = θ ^ 4 * (1 + 3 * θ ^ 2) / 4 :=
  Copula.chatterjeeXi_mardia θ hθ

example : (Copula.mardia (1 / 2) (by norm_num)).chatterjeeXi = 7 / 256 := by
  rw [Copula.chatterjeeXi_mardia]
  norm_num

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.mardia θ hθ).chatterjeeXi = 0 ↔ θ = 0 :=
  Copula.chatterjeeXi_mardia_eq_zero_iff θ hθ

example (C D E : Copula 2) (hC : C.SchurLE E) (hD : D.SchurLE E) (a : I) :
    (C.mix D a).SchurLE E := hC.mix hD a

example (C : Copula 2) (a : I) : (C.mix (Copula.independence 2) a).SchurLE C :=
  Copula.schurLE_mix_independence C a

example (C : Copula 2) (a b : I) (hab : a ≤ b) :
    (C.mix (Copula.independence 2) a).SchurLE (C.mix (Copula.independence 2) b) :=
  Copula.schurLE_mix_independence_mono C hab

example (C D : Copula 2) : C.concordanceQ D = D.concordanceQ C := C.concordanceQ_comm D

example (C D : Copula 2) : C.concordanceQ D ∈ Set.Icc (-1) 1 := C.concordanceQ_mem_Icc D

example (C : Copula 2) : C.concordanceQ (Copula.independence 2) = C.spearmanRho / 3 :=
  C.concordanceQ_independence

example (C : Copula 2) :
    C.giniGamma = C.concordanceQ (Copula.comonotonic 2) + C.concordanceQ Copula.countermonotonic :=
  C.giniGamma_eq_concordanceQ

example (C D E : Copula 2) (h : C.LowerOrthantLE D) : E.concordanceQ C ≤ E.concordanceQ D :=
  h.concordanceQ_le_right E

example (C D : Copula 2) (i : Fin 2) :
    ∀ᵐ p ∂C.toMeasure.prod D.toMeasure, p.1 i ≠ p.2 i := C.ae_prod_eval_ne D i

example (C D : Copula 2) : C.concordanceQ D =
    (C.toMeasure.prod D.toMeasure).real Copula.concordantPairs -
      (C.toMeasure.prod D.toMeasure).real Copula.discordantPairs :=
  C.concordanceQ_eq_concordant_sub_discordant D

example (C : Copula 2) : C.kendallTau =
    (C.toMeasure.prod C.toMeasure).real Copula.concordantPairs -
      (C.toMeasure.prod C.toMeasure).real Copula.discordantPairs :=
  C.kendallTau_eq_concordant_sub_discordant

example (C : Copula 2) : C.kendallTau = 1 ↔
    ∀ᵐ p ∂C.toMeasure.prod C.toMeasure, p ∈ Copula.concordantPairs :=
  C.kendallTau_eq_one_iff_ae_concordant

example (C : Copula 2) : C.kendallTau = -1 ↔
    ∀ᵐ p ∂C.toMeasure.prod C.toMeasure, p ∈ Copula.discordantPairs :=
  C.kendallTau_eq_neg_one_iff_ae_discordant

example : ((Copula.independence 2).toMeasure.prod (Copula.independence 2).toMeasure).real
    Copula.concordantPairs = 1 / 2 := by rw [Copula.measureReal_concordantPairs]; norm_num

example : ((Copula.comonotonic 2).toMeasure.prod (Copula.comonotonic 2).toMeasure).real
    Copula.concordantPairs = 1 := by rw [Copula.measureReal_concordantPairs]; norm_num

example : (Copula.countermonotonic.toMeasure.prod Copula.countermonotonic.toMeasure).real
    Copula.discordantPairs = 1 := by rw [Copula.measureReal_discordantPairs]; norm_num

example : ((Copula.comonotonic 2).toMeasure.prod Copula.countermonotonic.toMeasure).real
    Copula.concordantPairs = 1 / 2 := by rw [Copula.measureReal_concordantPairs]; norm_num

example {n : ℕ} (C : Fin n → Copula 2) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    (Copula.finiteMixture C w hw hs).kendallTau = ∑ i, ∑ j, w i * w j * (C i).concordanceQ (C j) :=
  Copula.kendallTau_finiteMixture C w hw hs

example (C : Copula 2) (a : I) : (C.mix (Copula.independence 2) a).kendallTau =
    (a : ℝ) ^ 2 * C.kendallTau + 2 / 3 * (a : ℝ) * (1 - (a : ℝ)) * C.spearmanRho :=
  Copula.kendallTau_mix_independence C a

example : ((Copula.comonotonic 2).mix (Copula.independence 2) half).kendallTau = 5 / 12 := by
  rw [Copula.kendallTau_mix_independence]
  norm_num [half]

example (a : I) : ((Copula.comonotonic 2).mix Copula.countermonotonic a).kendallTau =
    2 * (a : ℝ) - 1 := Copula.kendallTau_mix_comonotonic_countermonotonic a

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).kendallTau = (a - b) * (a + b + 2) / 3 :=
  Copula.kendallTau_frechet a b ha hb hab

example : let C := Copula.frechet (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    C.spearmanRho = -1 / 4 ∧ C.kendallTau = -11 / 48 ∧ C.spearmanFootrule = 0 ∧
      C.giniGamma = -1 / 4 ∧ C.blomqvistBeta = -1 / 4 ∧ C.chatterjeeXi = 3 / 16 := by
  dsimp
  rw [Copula.spearmanRho_frechet, Copula.kendallTau_frechet, Copula.spearmanFootrule_frechet,
    Copula.giniGamma_frechet, Copula.blomqvistBeta_frechet, Copula.chatterjeeXi_frechet]
  norm_num

example : let C := Copula.mardia (-1 / 2) (by norm_num)
    C.spearmanRho = -1 / 8 ∧ C.kendallTau = -3 / 32 ∧ C.spearmanFootrule = -1 / 32 ∧
      C.giniGamma = -1 / 8 ∧ C.blomqvistBeta = -1 / 8 ∧ C.chatterjeeXi = 7 / 256 := by
  dsimp
  rw [Copula.spearmanRho_mardia, Copula.kendallTau_mardia, Copula.spearmanFootrule_mardia,
    Copula.giniGamma_mardia, Copula.blomqvistBeta_mardia, Copula.chatterjeeXi_mardia]
  norm_num

-- Zero Kendall tau does not characterize independence.
example : let C := Copula.frechet (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    C.kendallTau = 0 ∧ C ≠ Copula.independence 2 := by
  dsimp
  constructor
  · rw [Copula.kendallTau_frechet]
    norm_num
  · rw [← Copula.chatterjeeXi_eq_zero_iff, Copula.chatterjeeXi_frechet]
    norm_num

example (θ : ℝ) (hθ : |θ| ≤ 1) : (Copula.mardia θ hθ).kendallTau = 0 ↔ θ = 0 :=
  Copula.kendallTau_mardia_eq_zero_iff θ hθ

end CopulaTest
