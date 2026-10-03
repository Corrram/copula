/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.MarkovProduct.Laws
import Copula.Rank.ConditionalMixture
import Copula.Rank.ChatterjeeExamples

/-! # Algebra of the Markov product: mixtures, idempotents and inverses

Further properties of the Darsow–Nguyen–Olsen Markov product `A * B = A.markovProduct B`
(W. F. Darsow, B. Nguyen and E. T. Olsen, *Copulas and Markov processes*, Illinois J. Math. 36
(1992); W. F. Darsow and E. T. Olsen, *Characterization of idempotent 2-copulas*, Note Mat. 30
(2010); Durante and Sempi 2016, §5.2; Nelsen 2006, §6.3):

* the product is bilinear with respect to convex combinations (`markovProduct_mix`,
  `mix_markovProduct`);
* products within the Fréchet–Mardia-type families: `(aM + (1-a)Π) * (bM + (1-b)Π) =
  abM + (1-ab)Π` and `(aM + (1-a)W) * (bM + (1-b)W) = (ab + (1-a)(1-b))M + (a(1-b)+(1-a)b)W`;
* idempotent copulas (`IsIdempotent`, `C * C = C`): `M` and `Π` are idempotent, `W` is not,
  idempotents are closed under transposition, `aM + (1-a)Π` is idempotent iff `a ∈ {0,1}`, and
  `C * Cᵀ` is idempotent whenever `C` is left invertible;
* inverses: `C` has a left inverse (`A * C = M` for some `A`) iff `Cᵀ * C = M` iff `ξ(C) = 1`
  (via the data-processing inequality); it has a right inverse iff `ξ(Cᵀ) = 1`; a copula with
  both a left and a right inverse has `Cᵀ` as its unique two-sided inverse.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ## Bilinearity -/

theorem integrable_conditionalCDF_mul_conditionalCDF (C D : Copula 2) (u v : I) :
    Integrable (fun s => C.conditionalCDF s u * D.conditionalCDF s v) := by
  refine (D.integrable_conditionalCDF v).mono'
    ((C.measurable_conditionalCDF_left u).mul
      (D.measurable_conditionalCDF_left v)).aestronglyMeasurable ?_
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (C.conditionalCDF_nonneg s u),
    abs_of_nonneg (D.conditionalCDF_nonneg s v)]
  exact mul_le_of_le_one_left (D.conditionalCDF_nonneg s v) (C.conditionalCDF_le_one s u)

/-- Right distributivity: `A * (aB + (1-a)C) = a (A * B) + (1-a) (A * C)`. -/
theorem markovProduct_mix (A B C : Copula 2) (a : I) :
    A.markovProduct (B.mix C a) = (A.markovProduct B).mix (A.markovProduct C) a := by
  apply ext_cdf_two
  intro u v
  rw [cdf_mix, cdf_markovProduct_eq_integral, cdf_markovProduct_eq_integral,
    cdf_markovProduct_eq_integral]
  have h : (fun s => A.transpose.conditionalCDF s u * (B.mix C a).conditionalCDF s v) =ᵐ[volume]
      fun s => (a : ℝ) * (A.transpose.conditionalCDF s u * B.conditionalCDF s v) +
        (1 - (a : ℝ)) * (A.transpose.conditionalCDF s u * C.conditionalCDF s v) := by
    filter_upwards [conditionalCDF_mix B C a v] with s hs
    rw [hs]; ring
  rw [integral_congr_ae h, integral_add, integral_const_mul, integral_const_mul]
  · exact (integrable_conditionalCDF_mul_conditionalCDF _ _ u v).const_mul _
  · exact (integrable_conditionalCDF_mul_conditionalCDF _ _ u v).const_mul _

/-- Left distributivity: `(aA + (1-a)B) * C = a (A * C) + (1-a) (B * C)`. -/
theorem mix_markovProduct (A B C : Copula 2) (a : I) :
    (A.mix B a).markovProduct C = (A.markovProduct C).mix (B.markovProduct C) a := by
  have h := markovProduct_mix C.transpose A.transpose B.transpose a
  rw [← transpose_mix, ← transpose_markovProduct, ← transpose_markovProduct,
    ← transpose_markovProduct, ← transpose_mix] at h
  simpa using congrArg transpose h

/-- Iterated mixtures of two copulas. -/
theorem mix_mix_right (C D : Copula 2) (a b : I) :
    (C.mix D b).mix D a = C.mix D (a * b) := by
  apply ext_cdf; intro u
  simp only [cdf_mix, Set.Icc.coe_mul]
  ring

/-- `(aM + (1-a)Π) * (bM + (1-b)Π) = abM + (1-ab)Π`. -/
theorem markovProduct_mix_comonotonic_independence (a b : I) :
    ((comonotonic 2).mix (independence 2) a).markovProduct
        ((comonotonic 2).mix (independence 2) b) =
      (comonotonic 2).mix (independence 2) (a * b) := by
  rw [mix_markovProduct, comonotonic_markovProduct, independence_markovProduct, mix_mix_right]

/-- `(aM + (1-a)W) * (bM + (1-b)W) = (ab + (1-a)(1-b)) M + (a(1-b) + (1-a)b) W`. -/
theorem cdf_markovProduct_mix_comonotonic_countermonotonic (a b : I) (u : Fin 2 → I) :
    (((comonotonic 2).mix countermonotonic a).markovProduct
        ((comonotonic 2).mix countermonotonic b)).cdf u =
      ((a : ℝ) * b + (1 - a) * (1 - b)) * (comonotonic 2).cdf u +
        ((a : ℝ) * (1 - b) + (1 - a) * b) * countermonotonic.cdf u := by
  rw [mix_markovProduct, markovProduct_mix, markovProduct_mix, comonotonic_markovProduct,
    comonotonic_markovProduct, countermonotonic_markovProduct_countermonotonic,
    markovProduct_comonotonic]
  simp only [cdf_mix]
  ring

/-! ## Idempotent copulas -/

/-- A copula is idempotent if `C * C = C`. -/
def IsIdempotent (C : Copula 2) : Prop := C.markovProduct C = C

theorem isIdempotent_comonotonic : (comonotonic 2).IsIdempotent := comonotonic_markovProduct _

theorem isIdempotent_independence : (independence 2).IsIdempotent :=
  independence_markovProduct _

theorem comonotonic_ne_countermonotonic : comonotonic 2 ≠ countermonotonic := by
  intro h
  have h1 := congrArg (fun C : Copula 2 => C.cdf ![unitHalf, unitHalf]) h
  simp only [cdf_comonotonic_two, cdf_countermonotonic, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h1
  have hu : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
  rw [hu] at h1
  norm_num at h1

/-- `W` is not idempotent: `W * W = M`. -/
theorem not_isIdempotent_countermonotonic : ¬ countermonotonic.IsIdempotent := by
  intro h
  unfold IsIdempotent at h
  rw [countermonotonic_markovProduct_countermonotonic] at h
  exact comonotonic_ne_countermonotonic h

theorem IsIdempotent.transpose {C : Copula 2} (h : C.IsIdempotent) :
    C.transpose.IsIdempotent := by
  unfold IsIdempotent at *
  rw [← transpose_markovProduct, h]

/-- `aM + (1-a)Π` is idempotent only for `a ∈ {0,1}`. -/
theorem isIdempotent_mix_comonotonic_independence_iff (a : I) :
    ((comonotonic 2).mix (independence 2) a).IsIdempotent ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    unfold IsIdempotent at h
    rw [markovProduct_mix_comonotonic_independence] at h
    have h1 := congrArg (fun C : Copula 2 => C.cdf ![unitHalf, unitHalf]) h
    simp only [cdf_mix, cdf_comonotonic_two, cdf_independence, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.Icc.coe_mul] at h1
    have hu : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
    rw [hu, min_self] at h1
    have ha : (a : ℝ) * (a - 1) = 0 := by linear_combination 4 * h1
    rcases mul_eq_zero.mp ha with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext (by simpa [sub_eq_zero] using h0)
  · rintro (h | h) <;> subst h
    · simpa using isIdempotent_independence
    · simpa using isIdempotent_comonotonic

/-- If `C` is left invertible (`Cᵀ * C = M`), then `C * Cᵀ` is idempotent. -/
theorem isIdempotent_markovProduct_transpose {C : Copula 2}
    (h : C.transpose.markovProduct C = comonotonic 2) :
    (C.markovProduct C.transpose).IsIdempotent := by
  unfold IsIdempotent
  rw [markovProduct_assoc, ← markovProduct_assoc C.transpose C C.transpose, h,
    comonotonic_markovProduct]

/-- Copulas with `ξ(C) = 1` give idempotents `C * Cᵀ`. -/
theorem isIdempotent_markovProduct_transpose_of_chatterjeeXi_eq_one {C : Copula 2}
    (h : C.chatterjeeXi = 1) : (C.markovProduct C.transpose).IsIdempotent :=
  isIdempotent_markovProduct_transpose ((transpose_markovProduct_self_eq_comonotonic_iff C).mpr h)

/-! ## Left and right inverses -/

/-- `C` has a left inverse for the Markov product if and only if `ξ(C) = 1`; the transpose
is then a left inverse. -/
theorem exists_left_inverse_iff (C : Copula 2) :
    (∃ A : Copula 2, A.markovProduct C = comonotonic 2) ↔ C.chatterjeeXi = 1 := by
  constructor
  · rintro ⟨A, hA⟩
    have h := chatterjeeXi_markovProduct_le A C
    rw [hA, chatterjeeXi_comonotonic] at h
    exact le_antisymm C.chatterjeeXi_le_one h
  · intro h
    exact ⟨C.transpose, (transpose_markovProduct_self_eq_comonotonic_iff C).mpr h⟩

/-- `C` has a right inverse for the Markov product if and only if `ξ(Cᵀ) = 1`; the transpose
is then a right inverse. -/
theorem exists_right_inverse_iff (C : Copula 2) :
    (∃ B : Copula 2, C.markovProduct B = comonotonic 2) ↔ C.transpose.chatterjeeXi = 1 := by
  rw [← exists_left_inverse_iff]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B.transpose, ?_⟩
    rw [← transpose_markovProduct, hB]
    exact isExchangeable_comonotonic
  · rintro ⟨A, hA⟩
    refine ⟨A.transpose, ?_⟩
    have := congrArg transpose hA
    rw [transpose_markovProduct, transpose_transpose] at this
    rw [this]
    exact isExchangeable_comonotonic

theorem markovProduct_transpose_eq_comonotonic_iff (C : Copula 2) :
    C.markovProduct C.transpose = comonotonic 2 ↔ C.transpose.chatterjeeXi = 1 := by
  simpa using transpose_markovProduct_self_eq_comonotonic_iff C.transpose

/-- A copula with a left inverse `A` and a right inverse `B` is invertible with
`A = B = Cᵀ`. -/
theorem eq_transpose_of_left_right_inverse {A B C : Copula 2}
    (hA : A.markovProduct C = comonotonic 2) (hB : C.markovProduct B = comonotonic 2) :
    A = C.transpose ∧ B = C.transpose := by
  have hAB : A = B := by
    calc A = A.markovProduct (C.markovProduct B) := by rw [hB, markovProduct_comonotonic]
      _ = (A.markovProduct C).markovProduct B := (markovProduct_assoc _ _ _).symm
      _ = B := by rw [hA, comonotonic_markovProduct]
  have hT : C.transpose.markovProduct C = comonotonic 2 :=
    (transpose_markovProduct_self_eq_comonotonic_iff C).mpr
      ((exists_left_inverse_iff C).mp ⟨A, hA⟩)
  have hTB : C.transpose = B := by
    calc C.transpose = C.transpose.markovProduct (C.markovProduct B) := by
          rw [hB, markovProduct_comonotonic]
      _ = (C.transpose.markovProduct C).markovProduct B := (markovProduct_assoc _ _ _).symm
      _ = B := by rw [hT, comonotonic_markovProduct]
  exact ⟨hAB.trans hTB.symm, hTB.symm⟩

end ProbabilityTheory.Copula
