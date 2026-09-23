import Copula.Rank.Region.XiBlest.Support.PartitionIntegration
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def partitionAverage {n : ℕ} (P : IntervalPartition n) (f : I → ℝ) (i : Fin n) : ℝ :=
  ∫ u : I, f (partitionEmbed P i u)

noncomputable def partitionAverageError {n : ℕ} (P : IntervalPartition n) (f : I → ℝ) : ℝ :=
  ∑ i, P.width i * ∫ u : I, |partitionAverage P f i-f (partitionEmbed P i u)|

theorem partitionAverage_sub_le {n : ℕ} (P : IntervalPartition n) (f g : I → ℝ) (i : Fin n)
    (hf : Integrable (fun u => f (partitionEmbed P i u)))
    (hg : Integrable (fun u => g (partitionEmbed P i u))) :
    |partitionAverage P f i-partitionAverage P g i| ≤ ∫ u : I, |f (partitionEmbed P i u)-g (partitionEmbed P i u)| := by
  unfold partitionAverage
  rw [← integral_sub hf hg]
  exact abs_integral_le_integral_abs

theorem partitionAverageError_nonneg {n : ℕ} (P : IntervalPartition n) (f : I → ℝ) :
    0 ≤ partitionAverageError P f :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.width_pos i).le (integral_nonneg fun _ => abs_nonneg _)

theorem partitionAverageError_approx {n : ℕ} (P : IntervalPartition n) (f g : I → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfi : ∀ i, Integrable (fun u => f (partitionEmbed P i u)))
    (hgi : ∀ i, Integrable (fun u => g (partitionEmbed P i u)))
    (δ : ℝ) (hδ : ∀ i u v, |g (partitionEmbed P i u)-g (partitionEmbed P i v)| ≤ δ) :
    partitionAverageError P f ≤ 2*(∫ u : I, |f u-g u|)+δ := by
  have hgavg (i : Fin n) (u : I) : |partitionAverage P g i-g (partitionEmbed P i u)| ≤ δ := by
    have hh := integral_mono ((hgi i).sub (integrable_const (g (partitionEmbed P i u)))).abs
      (integrable_const δ) (fun v => hδ i v u)
    have he : partitionAverage P g i-g (partitionEmbed P i u) =
        ∫ v : I, (g (partitionEmbed P i v)-g (partitionEmbed P i u)) := by
      rw [integral_sub (hgi i) (integrable_const _)]
      simp [partitionAverage]
    rw [he]
    exact (abs_integral_le_integral_abs).trans (by simpa using hh)
  have hi (i : Fin n) : (∫ u : I, |partitionAverage P f i-f (partitionEmbed P i u)|) ≤
      2*(∫ u : I, |f (partitionEmbed P i u)-g (partitionEmbed P i u)|)+δ := by
    have hp (u : I) : |partitionAverage P f i-f (partitionEmbed P i u)| ≤
        (∫ v : I, |f (partitionEmbed P i v)-g (partitionEmbed P i v)|)+δ+
        |f (partitionEmbed P i u)-g (partitionEmbed P i u)| := by
      have ht := abs_add_three (partitionAverage P f i-partitionAverage P g i)
        (partitionAverage P g i-g (partitionEmbed P i u)) (g (partitionEmbed P i u)-f (partitionEmbed P i u))
      have h1 := partitionAverage_sub_le P f g i (hfi i) (hgi i)
      have h2 := hgavg i u
      rw [abs_sub_comm (g (partitionEmbed P i u))] at ht
      have he : partitionAverage P f i-partitionAverage P g i+
          (partitionAverage P g i-g (partitionEmbed P i u))+(g (partitionEmbed P i u)-f (partitionEmbed P i u)) =
          partitionAverage P f i-f (partitionEmbed P i u) := by ring
      rw [he] at ht
      linarith
    have hh := integral_mono ((integrable_const _).sub (hfi i)).abs
      ((integrable_const _).add ((hfi i).sub (hgi i)).abs) hp
    simp only [Pi.add_apply,Pi.sub_apply] at hh
    rw [integral_add (g := fun u => |f (partitionEmbed P i u)-g (partitionEmbed P i u)|)
      (integrable_const _) ((hfi i).sub (hgi i)).abs] at hh
    simp only [integral_const,probReal_univ,one_smul] at hh
    linarith
  unfold partitionAverageError
  calc
    _ ≤ ∑ i, P.width i*(2*(∫ u : I, |f (partitionEmbed P i u)-g (partitionEmbed P i u)|)+δ) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (P.width_pos i).le
    _ = 2*(∫ u : I, |f u-g u|)+δ := by
      rw [integral_partition P (fun u => |f u-g u|) (continuous_abs.measurable.comp (hf.sub hg)) (fun i => ((hfi i).sub (hgi i)).abs)]
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,P.sum_width,one_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem partitionEmbed_dist_le_width {n : ℕ} (P : IntervalPartition n) (i : Fin n) (u v : I) :
    dist (partitionEmbed P i u) (partitionEmbed P i v) ≤ P.width i := by
  change |((P.point i.castSucc : ℝ)+P.width i*(u : ℝ))-((P.point i.castSucc : ℝ)+P.width i*(v : ℝ))| ≤ _
  have he : (P.point i.castSucc : ℝ)+P.width i*(u : ℝ)-((P.point i.castSucc : ℝ)+P.width i*(v : ℝ)) =
      P.width i*((u : ℝ)-(v : ℝ)) := by ring
  rw [he,abs_mul,abs_of_pos (P.width_pos i)]
  have huv : |(u : ℝ)-(v : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [u.property.1,v.property.2],by linarith [u.property.2,v.property.1]⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left huv (P.width_pos i).le

/-- Cell averaging on uniform grids converges in L1 for every measurable integrable
function whose restrictions through the affine cell maps are integrable. -/
theorem partitionAverageError_tendsto (f : I → ℝ) (hf : Measurable f) (hi : Integrable f)
    (hfi : ∀ (k : ℕ) (i : Fin (k+1)),
      Integrable (fun u => f (partitionEmbed (IntervalPartition.uniform (k+1) (by omega)) i u))) :
    Tendsto (fun k => partitionAverageError (IntervalPartition.uniform (k+1) (by omega)) f) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g,hg,_⟩ := hi.exists_boundedContinuous_integral_sub_le (show 0 < ε/6 by linarith)
  obtain ⟨δ,hδ,hgδ⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε/3) (by linarith)
  have hw : Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hw.eventually (gt_mem_nhds hδ)] with k hk
  let P := IntervalPartition.uniform (k+1) (by omega)
  have hos (i : Fin (k+1)) (u v : I) : |g (partitionEmbed P i u)-g (partitionEmbed P i v)| ≤ ε/3 := by
    have hd : dist (partitionEmbed P i u) (partitionEmbed P i v) < δ := by
      apply lt_of_le_of_lt (partitionEmbed_dist_le_width P i u v)
      simpa only [P,IntervalPartition.width_uniform,Nat.cast_add,Nat.cast_one] using hk
    exact (hgδ hd).le
  have he := partitionAverageError_approx P f g hf g.continuous.measurable (hfi k)
    (fun i => Copula.integrable_continuous_unit volume (g.continuous.comp (partitionEmbed_continuous P i))) (ε/3) hos
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (partitionAverageError_nonneg P f)]
  simp only [Real.norm_eq_abs] at hg
  linarith

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
