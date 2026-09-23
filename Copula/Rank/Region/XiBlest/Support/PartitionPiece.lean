import Copula.Rank.Region.XiBlest.Support.PartitionIntegration

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {n : ℕ} (P : IntervalPartition n)

noncomputable def partitionPiece (i : Fin n) (f : I → ℝ) (u : I) : ℝ :=
  if P.point i.castSucc < u ∧ u ≤ P.point i.succ then f (P.coord i u) else 0

theorem partition_coord_continuous (i : Fin n) : Continuous (P.coord i) := by
  unfold IntervalPartition.coord
  fun_prop

theorem partitionPiece_measurable (i : Fin n) {f : I → ℝ} (hf : Measurable f) :
    Measurable (partitionPiece P i f) :=
  (hf.comp (partition_coord_continuous P i).measurable).ite measurableSet_Ioc measurable_const

theorem partitionEmbed_strict_lower (i : Fin n) (u : I) (hu : 0 < u) :
    P.point i.castSucc < partitionEmbed P i u := by
  change (P.point i.castSucc : ℝ) < (P.point i.castSucc : ℝ)+P.width i*(u : ℝ)
  exact lt_add_of_pos_right _ (mul_pos (P.width_pos i) hu)

theorem partitionPiece_embed (i r : Fin n) (f : I → ℝ) (u : I) (hu : 0 < u) :
    partitionPiece P i f (partitionEmbed P r u) = if r=i then f u else 0 := by
  rcases lt_trichotomy r i with h | rfl | h
  · have ho : P.point r.succ ≤ P.point i.castSucc := P.strictMono.monotone (by
      show r.val+1 ≤ i.val; exact h)
    have he := (partitionEmbed_upper P r u).trans ho
    simp only [partitionPiece,not_lt_of_ge he,false_and,ite_false,ne_of_lt h]
  · simp only [partitionPiece,partitionEmbed_strict_lower P r u hu,partitionEmbed_upper,
      and_self,ite_true,partition_coord_embed_self]
  · have ho : P.point i.succ ≤ P.point r.castSucc := P.strictMono.monotone (by
      show i.val+1 ≤ r.val; exact h)
    have he := ho.trans_lt (partitionEmbed_strict_lower P r u hu)
    simp only [partitionPiece,not_le_of_gt he,and_false,ite_false,ne_of_gt h]

theorem partitionPiece_embed_ae (i r : Fin n) (f : I → ℝ) :
    (fun u => partitionPiece P i f (partitionEmbed P r u)) =ᵐ[volume]
      fun u => if r=i then f u else 0 := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with u hu
  exact partitionPiece_embed P i r f u (lt_of_le_of_ne u.property.1 (Ne.symm hu))


theorem partitionPiece_integrable (i : Fin n) {f : I → ℝ}
    (hf : Measurable f) (hi : Integrable f) : Integrable (partitionPiece P i f) := by
  apply integrable_partition P (partitionPiece_measurable P i hf)
  intro r
  have he := partitionPiece_embed_ae P i r f
  by_cases h : r=i
  · exact hi.congr (by simpa only [h,ite_true] using he.symm)
  · exact (integrable_const (0 : ℝ)).congr (by simpa only [h,ite_false] using he.symm)

theorem partitionPiece_prefix_embed (i r : Fin n) (f : I → ℝ) (t : I) :
    (fun u => (Iic t).indicator (partitionPiece P i f) (partitionEmbed P r u)) =ᵐ[volume]
      fun u => if r=i then (Iic (P.coord i t)).indicator f u else 0 := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with u hu
  have hu' : 0 < u := lt_of_le_of_ne u.property.1 (Ne.symm hu)
  have he := partitionPiece_embed P i r f u hu'
  by_cases h : r=i
  · subst r
    simp only [ite_true] at he ⊢
    by_cases ht : P.point i.castSucc ≤ t
    · have heq := partitionEmbed_le_iff P i u t ht
      simp only [indicator,mem_Iic,heq,he]
    · have ht' : t < P.point i.castSucc := lt_of_not_ge ht
      have hnt : ¬ partitionEmbed P i u ≤ t := not_le_of_gt (ht'.trans_le (partitionEmbed_lower P i u))
      have hz : P.coord i t=0 := P.coord_of_le i t ht'.le
      simp only [indicator,mem_Iic,hnt,ite_false,hz,not_le_of_gt hu']
  · simp only [h,ite_false] at he ⊢
    simp only [indicator,he,ite_self]

theorem integral_partitionPiece_Iic (i : Fin n) {f : I → ℝ}
    (hf : Measurable f) (hi : Integrable f) (t : I) :
    (∫ u in Iic t, partitionPiece P i f u) = P.width i * ∫ u in Iic (P.coord i t), f u := by
  have hm := (partitionPiece_measurable P i hf).indicator (measurableSet_Iic (a := t))
  have he := partitionPiece_prefix_embed P i
  have hj (r : Fin n) : Integrable (fun u => (Iic t).indicator (partitionPiece P i f) (partitionEmbed P r u)) := by
    by_cases h : r=i
    · exact (hi.indicator measurableSet_Iic).congr (by simpa only [h,ite_true] using (he r f t).symm)
    · exact (integrable_const (0 : ℝ)).congr (by simpa only [h,ite_false] using (he r f t).symm)
  rw [← integral_indicator measurableSet_Iic,integral_partition P _ hm hj]
  have heint (r : Fin n) :
      (∫ u : I, (Iic t).indicator (partitionPiece P i f) (partitionEmbed P r u)) =
        if r=i then ∫ u in Iic (P.coord i t), f u else 0 := by
    rw [integral_congr_ae (he r f t)]
    by_cases h : r=i <;> simp [h,integral_indicator measurableSet_Iic]
  simp_rw [heint]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]


theorem partitionSum_embed_ae (f : Fin n → I → ℝ) (r : Fin n) :
    (fun u => ∑ i, partitionPiece P i (f i) (partitionEmbed P r u)) =ᵐ[volume] f r := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with u hu
  simp only [partitionPiece_embed P _ _ _ u (lt_of_le_of_ne u.property.1 (Ne.symm hu))]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem integral_partitionSum_sq (f : Fin n → I → ℝ) (hf : ∀ i, Measurable (f i))
    (hi : ∀ i, Integrable (fun u => f i u^2)) :
    (∫ u : I, (∑ i, partitionPiece P i (f i) u)^2) = ∑ i, P.width i * ∫ u : I, f i u^2 := by
  have hm : Measurable (fun u => (∑ i, partitionPiece P i (f i) u)^2) :=
    (Finset.measurable_sum _ (fun i _ => partitionPiece_measurable P i (hf i))).pow_const 2
  have he (r : Fin n) : (fun u => (∑ i, partitionPiece P i (f i) (partitionEmbed P r u))^2) =ᵐ[volume]
      fun u => f r u^2 := (partitionSum_embed_ae P f r).fun_comp (fun x : ℝ => x^2)
  rw [integral_partition P _ hm (fun r => (hi r).congr (he r).symm)]
  simp_rw [integral_congr_ae (he _)]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
