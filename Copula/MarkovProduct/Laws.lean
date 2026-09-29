/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rearrangement
import Copula.Rank.Symmetry
import Copula.UnitInterval

/-! # Algebraic laws of the Markov product

Further properties of the Darsow–Nguyen–Olsen Markov product `A * B = A.markovProduct B`
(Darsow, Nguyen and Olsen, *Copulas and Markov processes*, Illinois J. Math. 36 (1992);
Durante and Sempi, *Principles of Copula Theory*, §5.2), complementing
`Copula.MarkovProduct` (associativity, `M` is the identity, `Π` is absorbing) and
`Copula.Rearrangement` (`W * W = M`, products of graph copulas):

* the classical CDF formula `(A * B)(u,v) = ∫₀¹ ∂₂A(u,s) ∂₁B(s,v) ds`, with the partial
  derivatives realized by the conditional distribution functions of `Aᵀ` and `B`
  (`cdf_markovProduct_eq_integral`);
* the transposition law `(A * B)ᵀ = Bᵀ * Aᵀ` (`transpose_markovProduct`);
* multiplication by a graph copula on the right transforms the second coordinate
  (`markovProduct_graphCopula_right`), so `C * W` and `W * C` are the reflections of `C`
  in the second and first coordinate;
* `ξ(C) = 6 ∫₀¹ (Cᵀ * C)(t,t) dt - 2`, and `Cᵀ * C = M` if and only if `ξ(C) = 1`
  (in particular for completely dependent copulas, which are left invertible);
* the data-processing inequality `ξ(A * B) ≤ ξ(B)` for Chatterjee's xi.
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ## Disintegration along the first coordinate -/

theorem map_pair_eq_compProd_conditionalKernel (C : Copula 2) :
    C.toMeasure.map (fun x => (x 0, x 1)) = (volume : Measure I) ⊗ₘ C.conditionalKernel := by
  have h := compProd_map_condDistrib (μ := C.toMeasure)
    (mα := inferInstance) (mβ := inferInstance)
    (X := fun x : Fin 2 → I => x 0) (Y := fun x => x 1)
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  rw [C.map_eval] at h
  exact h.symm

/-- Integrals of products of bounded functions of the two coordinates, disintegrated along the
first coordinate. -/
theorem integral_mul_eq_integral_conditionalKernel (C : Copula 2) {f g : I → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ t, |f t| ≤ 1) (hg1 : ∀ s, |g s| ≤ 1) :
    (∫ x, f (x 0) * g (x 1) ∂C.toMeasure) =
      ∫ t : I, f t * ∫ s, g s ∂(C.conditionalKernel t) := by
  have hF : Measurable fun p : I × I => f p.1 * g p.2 :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hint : Integrable (fun p : I × I => f p.1 * g p.2)
      ((volume : Measure I) ⊗ₘ C.conditionalKernel) := by
    refine Integrable.of_bound hF.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hf1 p.1
    have h2 := hg1 p.2
    nlinarith [abs_nonneg (f p.1), abs_nonneg (g p.2)]
  have hm : Measurable fun x : Fin 2 → I => (x 0, x 1) := by fun_prop
  have h1 : (∫ x, f (x 0) * g (x 1) ∂C.toMeasure) =
      ∫ p, f p.1 * g p.2 ∂(C.toMeasure.map fun x => (x 0, x 1)) :=
    (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm
  rw [h1, map_pair_eq_compProd_conditionalKernel, Measure.integral_compProd hint]
  simp only [integral_const_mul]

theorem measureReal_comp_eq_integral (κ η : Kernel I I) [IsMarkovKernel κ] [IsMarkovKernel η]
    (t : I) {S : Set I} (hS : MeasurableSet S) :
    ((η ∘ₖ κ) t).real S = ∫ s, (η s).real S ∂(κ t) := by
  rw [Kernel.comp_apply]
  unfold Measure.real
  rw [Measure.bind_apply hS η.aemeasurable, integral_toReal (η.measurable_coe hS).aemeasurable
    (Eventually.of_forall fun s => measure_lt_top _ _)]

theorem abs_conditionalCDF_le_one (C : Copula 2) (u t : I) : |C.conditionalCDF u t| ≤ 1 := by
  rw [abs_of_nonneg (C.conditionalCDF_nonneg u t)]
  exact C.conditionalCDF_le_one u t

theorem abs_indicator_one_le_one (S : Set I) (t : I) : |S.indicator (1 : I → ℝ) t| ≤ 1 := by
  by_cases h : t ∈ S <;> simp [h]

/-! ## The CDF of the Markov product -/

/-- The classical formula `(A * B)(u,v) = ∫₀¹ ∂₂A(u,s) ∂₁B(s,v) ds`: the partial derivative
`∂₂A(u,s) = P(U ≤ u | V = s)` is the conditional CDF of the transpose. -/
theorem cdf_markovProduct_eq_integral (A B : Copula 2) (u v : I) :
    (A.markovProduct B).cdf ![u, v] =
      ∫ s : I, A.transpose.conditionalCDF s u * B.conditionalCDF s v := by
  have hG : Measurable fun s => B.conditionalCDF s v := B.measurable_conditionalCDF_left v
  have hI : Measurable ((Iic u).indicator (1 : I → ℝ)) :=
    measurable_one.indicator measurableSet_Iic
  rw [cdf_markovProduct]
  -- the integrand is the conditional average of `B`'s conditional CDF
  have h1 : (∫ t in Iic u, ((B.conditionalKernel ∘ₖ A.conditionalKernel) t).real (Iic v)) =
      ∫ t : I, (Iic u).indicator (1 : I → ℝ) t *
        ∫ s, B.conditionalCDF s v ∂(A.conditionalKernel t) := by
    rw [← integral_indicator measurableSet_Iic]
    congr 1
    funext t
    by_cases ht : t ∈ Iic u
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Pi.one_apply, one_mul,
        measureReal_comp_eq_integral _ _ t measurableSet_Iic]
      rfl
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  rw [h1, ← A.integral_mul_eq_integral_conditionalKernel hI hG (abs_indicator_one_le_one _)
    (fun s => B.abs_conditionalCDF_le_one s v)]
  -- pass to the transpose and disintegrate along its first coordinate
  have h2 := A.integral_transpose
    (fun y => B.conditionalCDF (y 0) v * (Iic u).indicator (1 : I → ℝ) (y 1))
    ((hG.comp (measurable_pi_apply 0)).mul (hI.comp (measurable_pi_apply 1)))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  have h3 : (∫ x, (Iic u).indicator (1 : I → ℝ) (x 0) * B.conditionalCDF (x 1) v ∂A.toMeasure) =
      ∫ x, B.conditionalCDF (x 1) v * (Iic u).indicator (1 : I → ℝ) (x 0) ∂A.toMeasure := by
    congr 1
    funext x
    ring
  rw [h3, ← h2, A.transpose.integral_mul_eq_integral_conditionalKernel hG hI
    (fun s => B.abs_conditionalCDF_le_one s v) (abs_indicator_one_le_one _)]
  congr 1
  funext s
  rw [integral_indicator_one measurableSet_Iic]
  unfold conditionalCDF
  ring

/-- The transposition law of the Markov product, `(A * B)ᵀ = Bᵀ * Aᵀ`. -/
theorem transpose_markovProduct (A B : Copula 2) :
    (A.markovProduct B).transpose = B.transpose.markovProduct A.transpose := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_markovProduct_eq_integral, cdf_markovProduct_eq_integral,
    transpose_transpose]
  congr 1
  funext s
  ring

/-! ## Graph copulas on the right -/

/-- Multiplying by the graph copula of a measure-preserving map `f` on the right applies `f`
to the second coordinate. -/
theorem markovProduct_graphCopula_right (C : Copula 2) (f : I → I)
    (hf : MeasurePreserving f volume volume) :
    C.markovProduct (graphCopula f hf) =
      C.rearrange ![id, f] (fun i => by
        fin_cases i
        · exact MeasurePreserving.id volume
        · exact hf) := by
  apply ext
  have hk : (graphCopula f hf).conditionalKernel ∘ₖ C.conditionalKernel =ᵐ[volume]
      C.conditionalKernel.map f := by
    filter_upwards [C.kernel_comp_ae_congr_left (conditionalKernel_graphCopula f hf)] with u hu
    rw [hu, Kernel.deterministic_comp_eq_map]
  have hC : C.toMeasure =
      ((volume : Measure I) ⊗ₘ C.conditionalKernel).map (fun p => ![p.1, p.2]) := by
    rw [← toMeasure_ofKernel C.conditionalKernel C.conditionalKernel_comp_volume,
      ofKernel_conditionalKernel]
  have hg : Measurable fun x : Fin 2 → I => fun i => (![id, f] : Fin 2 → I → I) i (x i) := by
    refine Measurable.of_eval fun i => ?_
    fin_cases i
    · exact measurable_pi_apply 0
    · exact hf.measurable.comp (measurable_pi_apply 1)
  have hp : Measurable fun p : I × I => ![p.1, p.2] := by fun_prop
  rw [markovProduct, toMeasure_ofKernel, Measure.compProd_congr hk,
    Measure.compProd_map hf.measurable, toMeasure_rearrange, hC,
    Measure.map_map hp (measurable_id.prodMap hf.measurable), Measure.map_map hg hp]
  congr 1
  funext p i
  fin_cases i <;> rfl

/-- Right multiplication by `W` reflects the second coordinate: `C * W = C.reflect {1}`. -/
@[simp] theorem markovProduct_countermonotonic (C : Copula 2) :
    C.markovProduct countermonotonic = C.reflect {1} := by
  rw [← graphCopula_symm, markovProduct_graphCopula_right]
  exact shuffle_reflection C

/-- Left multiplication by `W` reflects the first coordinate: `W * C = C.reflect {0}`. -/
@[simp] theorem countermonotonic_markovProduct (C : Copula 2) :
    countermonotonic.markovProduct C = C.reflect {0} := by
  have hW : countermonotonic.transpose = countermonotonic := isExchangeable_countermonotonic
  have h := transpose_markovProduct C.transpose countermonotonic
  rw [transpose_transpose, hW, markovProduct_countermonotonic, ← transpose_reflect_first,
    transpose_transpose] at h
  exact h.symm

/-! ## Left invertibility and Chatterjee's xi -/

/-- `(Cᵀ * C)(u,v) = ∫₀¹ ∂₁C(s,u) ∂₁C(s,v) ds`. -/
theorem cdf_transpose_markovProduct_self (C : Copula 2) (u v : I) :
    (C.transpose.markovProduct C).cdf ![u, v] =
      ∫ s : I, C.conditionalCDF s u * C.conditionalCDF s v := by
  rw [cdf_markovProduct_eq_integral, transpose_transpose]

/-- Chatterjee's xi through the diagonal of `Cᵀ * C`: `ξ(C) = 6 ∫₀¹ (Cᵀ * C)(t,t) dt - 2`. -/
theorem chatterjeeXi_eq_integral_diagonal_transpose_markovProduct (C : Copula 2) :
    C.chatterjeeXi = 6 * (∫ t : I, (C.transpose.markovProduct C).cdf ![t, t]) - 2 := by
  have h (t : I) : (C.transpose.markovProduct C).cdf ![t, t] =
      ∫ u : I, C.conditionalCDF u t ^ 2 := by
    rw [cdf_transpose_markovProduct_self]
    simp only [sq]
  simp_rw [h]
  rfl

/-- `Cᵀ * C = M` (i.e. `C` is left invertible) if and only if `ξ(C) = 1`. -/
theorem transpose_markovProduct_self_eq_comonotonic_iff (C : Copula 2) :
    C.transpose.markovProduct C = comonotonic 2 ↔ C.chatterjeeXi = 1 := by
  rw [chatterjeeXi_eq_integral_diagonal_transpose_markovProduct]
  set E := C.transpose.markovProduct C
  have hdiag (D : Copula 2) : Continuous fun t : I => D.cdf ![t, t] :=
    D.continuous_cdf.comp (by fun_prop)
  constructor
  · intro h
    rw [h]
    simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one, min_self]
    rw [integral_unit_id]
    norm_num
  · intro h
    have hint : (∫ t : I, ((t : ℝ) - E.cdf ![t, t])) = 0 := by
      rw [integral_sub (integrable_continuous_unit volume continuous_subtype_val)
        (integrable_continuous_unit volume (hdiag E)), integral_unit_id]
      linarith
    have hle (t : I) : E.cdf ![t, t] ≤ (t : ℝ) := by
      have := E.cdf_le_comonotonic ![t, t]
      rw [cdf_comonotonic_two] at this
      simpa using this
    have hae := (integral_eq_zero_iff_of_nonneg (fun t => sub_nonneg.mpr (hle t))
      (integrable_continuous_unit volume (continuous_subtype_val.sub (hdiag E)))).mp hint
    have heq := (Continuous.ae_eq_iff_eq volume (continuous_subtype_val.sub (hdiag E))
      continuous_zero).mp hae
    have hd (t : I) : E.cdf ![t, t] = t := by
      have := congrFun heq t
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      linarith
    apply ext_cdf_two
    intro u v
    rw [cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply le_antisymm
    · have := E.cdf_le_comonotonic ![u, v]
      rw [cdf_comonotonic_two] at this
      simpa using this
    · have hm : E.cdf ![min u v, min u v] ≤ E.cdf ![u, v] := by
        apply E.monotone_cdf
        intro i
        fin_cases i
        · exact min_le_left u v
        · exact min_le_right u v
      rw [hd] at hm
      calc min (u : ℝ) v = ((min u v : I) : ℝ) := by
            rcases le_total u v with huv | huv
            · rw [min_eq_left huv, min_eq_left (show (u : ℝ) ≤ v from huv)]
            · rw [min_eq_right huv, min_eq_right (show (v : ℝ) ≤ u from huv)]
        _ ≤ E.cdf ![u, v] := hm

/-- Completely dependent copulas are left invertible: `Cᵀ * C = M`. -/
theorem IsCompletelyDependent.transpose_markovProduct_self {C : Copula 2}
    (h : C.IsCompletelyDependent) : C.transpose.markovProduct C = comonotonic 2 :=
  (transpose_markovProduct_self_eq_comonotonic_iff C).mpr h.chatterjeeXi_eq_one

/-! ## Data processing for Chatterjee's xi -/

/-- Jensen's inequality `(∫ g)² ≤ ∫ g²` for a `[0,1]`-valued function and a probability
measure. -/
theorem sq_integral_le_integral_sq_of_unit {ν : Measure I} [IsProbabilityMeasure ν] {g : I → ℝ}
    (hg : Measurable g) (hg0 : ∀ s, 0 ≤ g s) (hg1 : ∀ s, g s ≤ 1) :
    (∫ s, g s ∂ν) ^ 2 ≤ ∫ s, g s ^ 2 ∂ν := by
  have hb (s : I) : ‖g s‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hg1 s
  have hi : Integrable g ν := Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall hb)
  have hi2 : Integrable (fun s => g s ^ 2) ν :=
    Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable 1 (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hg0 s, hg1 s])
  set m := ∫ s, g s ∂ν
  have hv : 0 ≤ ∫ s, (g s - m) ^ 2 ∂ν := integral_nonneg fun s => sq_nonneg _
  have ha : Integrable (fun s => g s ^ 2 - (2 * m) * g s) ν := hi2.sub (hi.const_mul _)
  have h1 : (∫ s, (g s - m) ^ 2 ∂ν) = ∫ s, ((g s ^ 2 - (2 * m) * g s) + m ^ 2) ∂ν := by
    congr 1
    funext s
    ring
  have h2 : (∫ s, ((g s ^ 2 - (2 * m) * g s) + m ^ 2) ∂ν) =
      (∫ s, (g s ^ 2 - (2 * m) * g s) ∂ν) + m ^ 2 := by
    rw [integral_add ha (integrable_const _), integral_const, probReal_univ, one_smul]
  have h3 : (∫ s, (g s ^ 2 - (2 * m) * g s) ∂ν) = (∫ s, g s ^ 2 ∂ν) - 2 * m * m := by
    rw [integral_sub hi2 (hi.const_mul _), integral_const_mul]
  rw [h1, h2, h3] at hv
  nlinarith

/-- Averaging a bounded measurable function against the conditional laws recovers the uniform
second marginal. -/
theorem integral_integral_conditionalKernel (C : Copula 2) {g : I → ℝ} (hg : Measurable g)
    (hg1 : ∀ s, |g s| ≤ 1) : (∫ u : I, ∫ s, g s ∂C.conditionalKernel u) = ∫ s : I, g s := by
  have hi : Integrable g ((C.conditionalKernel ∘ₖ Kernel.const Unit (volume : Measure I)) ()) := by
    rw [← Measure.comp_eq_comp_const_apply, C.conditionalKernel_comp_volume]
    exact Integrable.of_bound hg.aestronglyMeasurable 1
      (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hg1 s)
  have h := Kernel.integral_comp hi
  rw [← Measure.comp_eq_comp_const_apply, C.conditionalKernel_comp_volume] at h
  exact h.symm

/-- The data-processing inequality for Chatterjee's xi: `ξ(A * B) ≤ ξ(B)`. Following the
transition of `A` before that of `B` cannot increase the dependence of the endpoint on the
starting point. -/
theorem chatterjeeXi_markovProduct_le (A B : Copula 2) :
    (A.markovProduct B).chatterjeeXi ≤ B.chatterjeeXi := by
  rw [chatterjeeXi_eq_of_kernel_ae _ _ (conditionalKernel_markovProduct A B)]
  have key (t : I) :
      (∫ u : I, (((B.conditionalKernel ∘ₖ A.conditionalKernel) u).real (Iic t)) ^ 2) ≤
        ∫ u : I, B.conditionalCDF u t ^ 2 := by
    have hg := B.measurable_conditionalCDF_left t
    have hsq : Measurable fun s => B.conditionalCDF s t ^ 2 := hg.pow_const 2
    have hsq1 (s : I) : |B.conditionalCDF s t ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [B.conditionalCDF_nonneg s t, B.conditionalCDF_le_one s t]
    have hJ (u : I) : (((B.conditionalKernel ∘ₖ A.conditionalKernel) u).real (Iic t)) ^ 2 ≤
        ∫ s, B.conditionalCDF s t ^ 2 ∂A.conditionalKernel u := by
      rw [measureReal_comp_eq_integral _ _ u measurableSet_Iic]
      exact sq_integral_le_integral_sq_of_unit hg (B.conditionalCDF_nonneg · t)
        (B.conditionalCDF_le_one · t)
    have hRi : Integrable fun u : I => ∫ s, B.conditionalCDF s t ^ 2 ∂A.conditionalKernel u := by
      refine Integrable.of_bound hsq.stronglyMeasurable.integral_kernel.aestronglyMeasurable 1
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_integral_le_integral_abs).trans ?_
      calc (∫ s, |B.conditionalCDF s t ^ 2| ∂A.conditionalKernel u)
          ≤ ∫ _s, (1 : ℝ) ∂A.conditionalKernel u :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const _) (Eventually.of_forall hsq1)
        _ = 1 := by simp
    calc (∫ u : I, (((B.conditionalKernel ∘ₖ A.conditionalKernel) u).real (Iic t)) ^ 2)
        ≤ ∫ u : I, ∫ s, B.conditionalCDF s t ^ 2 ∂A.conditionalKernel u :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hRi
            (Eventually.of_forall hJ)
      _ = ∫ u : I, B.conditionalCDF u t ^ 2 :=
          A.integral_integral_conditionalKernel hsq hsq1
  have h := integral_mono_of_nonneg
    (Eventually.of_forall fun t => integral_nonneg fun u => sq_nonneg _)
    B.integrable_integral_conditionalCDF_sq (Eventually.of_forall key)
  unfold chatterjeeXi
  linarith

end ProbabilityTheory.Copula
