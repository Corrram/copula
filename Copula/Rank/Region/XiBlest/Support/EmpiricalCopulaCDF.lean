import Copula.Rank.Region.XiBlest.Support.EmpiricalConcentration
import Copula.Patchwork.Approximation
import Copula.Rank.Integration

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def lowerCubeIndicator (t : Fin 2 → I) : (Fin 2 → I) → ℝ := (Iic t).indicator (fun _ => 1)

theorem lowerCubeIndicator_measurable (t : Fin 2 → I) : Measurable (lowerCubeIndicator t) :=
  measurable_const.indicator measurableSet_Iic

theorem lowerCubeIndicator_mem (t x : Fin 2 → I) : lowerCubeIndicator t x ∈ Icc (0 : ℝ) 1 := by
  unfold lowerCubeIndicator
  by_cases h : x ∈ Iic t <;> simp [h]

theorem lowerCubeIndicator_mono {s t : Fin 2 → I} (hst : s ≤ t) (x : Fin 2 → I) :
    lowerCubeIndicator s x ≤ lowerCubeIndicator t x := by
  unfold lowerCubeIndicator
  by_cases hs : x ∈ Iic s
  · have ht : x ∈ Iic t := le_trans hs hst
    simp [hs,ht]
  · simp only [Set.indicator_of_notMem hs]
    exact (lowerCubeIndicator_mem t x).1

noncomputable def empiricalCopulaCDF {Ω : Type*} (X : ℕ → Ω → (Fin 2 → I))
    (n : ℕ) (ω : Ω) (t : Fin 2 → I) : ℝ :=
  empiricalMean (fun i ω => lowerCubeIndicator t (X i ω)) n ω

theorem empiricalCopulaCDF_mono {Ω : Type*} (X : ℕ → Ω → (Fin 2 → I)) (n : ℕ) (ω : Ω) :
    Monotone (empiricalCopulaCDF X n ω) := by
  intro s t hst
  unfold empiricalCopulaCDF empiricalMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact Finset.sum_le_sum fun i _ => lowerCubeIndicator_mono hst (X i ω)

theorem lowerCubeIndicator_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (C : Copula 2) (X : Ω → (Fin 2 → I)) (hX : Measurable X) (hlaw : μ.map X=C.toMeasure) (t : Fin 2 → I) :
    (∫ ω, lowerCubeIndicator t (X ω) ∂μ)=C.cdf t := by
  rw [← integral_map hX.aemeasurable (lowerCubeIndicator_measurable t).aestronglyMeasurable,hlaw]
  unfold lowerCubeIndicator
  rw [integral_indicator measurableSet_Iic]
  simp [Copula.cdf]

theorem empiricalCopulaCDF_grid_deviation {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Copula 2) (X : ℕ → Ω → (Fin 2 → I))
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i)=C.toMeasure)
    (grid : ι → (Fin 2 → I)) (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0≤ε) :
    μ.real {ω | ∃ t, ε ≤ |empiricalCopulaCDF X n ω (grid t)-C.cdf (grid t)|} ≤
      (Fintype.card ι : ℝ)*2*Real.exp (-(n : ℝ)*ε^2/2) := by
  apply empiricalMean_finite_deviation μ (fun t i ω => lowerCubeIndicator (grid t) (X i ω))
    (fun t i => (lowerCubeIndicator_measurable _).comp (hX i))
    (fun t => hI.comp (fun _ => lowerCubeIndicator (grid t)) (fun _ => lowerCubeIndicator_measurable _))
    (fun t i ω => lowerCubeIndicator_mem _ _) (fun t => C.cdf (grid t))
    (fun t => ⟨C.cdf_nonneg _,C.cdf_le_one _⟩)
    (fun t i => lowerCubeIndicator_mean μ C (X i) (hX i) (hlaw i) (grid t)) n hn ε hε

/-- Monotonicity extends a finite-grid CDF error bound to the whole square. -/
theorem cdf_grid_error_bound {m n : ℕ} (C : Copula 2) (F : (Fin 2 → I) → ℝ) (hF : Monotone F)
    (P : IntervalPartition m) (Q : IntervalPartition n) (ε dx dy : ℝ)
    (hx : ∀ i, P.width i ≤ dx) (hy : ∀ j, Q.width j ≤ dy)
    (hgrid : ∀ i j, |F ![P.point i,Q.point j]-C.cdf ![P.point i,Q.point j]| ≤ ε)
    (u v : I) : |F ![u,v]-C.cdf ![u,v]| ≤ ε+dx+dy := by
  obtain ⟨i,hi⟩ := P.exists_cell u
  obtain ⟨j,hj⟩ := Q.exists_cell v
  have hl : ![P.point i.castSucc,Q.point j.castSucc] ≤ ![u,v] := by intro k; fin_cases k <;> simp [hi.1,hj.1]
  have hr : ![u,v] ≤ ![P.point i.succ,Q.point j.succ] := by intro k; fin_cases k <;> simp [hi.2,hj.2]
  have hFl := hF hl
  have hFr := hF hr
  have hCl := C.monotone_cdf hl
  have hCr := C.monotone_cdf hr
  have hgl := abs_le.mp (hgrid i.castSucc j.castSucc)
  have hgr := abs_le.mp (hgrid i.succ j.succ)
  have hb := C.cdf_sub_le_sum_abs ![P.point i.succ,Q.point j.succ] ![P.point i.castSucc,Q.point j.castSucc]
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hb
  change _ ≤ |P.width i|+|Q.width j| at hb
  rw [abs_of_pos (P.width_pos i),abs_of_pos (Q.width_pos j)] at hb
  rw [abs_le]
  constructor <;> linarith [hgl.1,hgl.2,hgr.1,hgr.2,hx i,hy j]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
