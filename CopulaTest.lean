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

end CopulaTest
