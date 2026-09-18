import Copula
import Mathlib.Tactic.NormNum

/-! Public API examples, including the empty dimension and dependent coordinates. -/

open ProbabilityTheory MeasureTheory
open scoped unitInterval

namespace CopulaTest

def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

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
  simpa [half] using C.cdf_update_one 0 half

example (C : Copula 2) : C.cdf ![0, half] = 0 :=
  C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl

-- Reindexing can repeat a coordinate as well as select one.
example (C : Copula 1) : Copula 3 := C.reindex (fun _ => 0)

example (C : Copula 2) (ρ : Fin 2 ≃ Fin 2) : (C.reindex ρ).reindex ρ.symm = C := by
  simp

-- The measure accessor participates in mathlib's probability API.
example (C : Copula 2) : C.toMeasure Set.univ = 1 := measure_univ

end CopulaTest
