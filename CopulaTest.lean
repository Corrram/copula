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

end CopulaTest
