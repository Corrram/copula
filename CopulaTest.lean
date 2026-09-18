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

end CopulaTest
