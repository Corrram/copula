import Copula.Rank.Region.XiBlest.Support.PartitionEmbed

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem partition_coord_embed_self {n : ℕ} (P : IntervalPartition n) (i : Fin n) (u : I) :
    P.coord i (partitionEmbed P i u)=u := by
  apply Subtype.ext
  rw [P.coe_coord_of_mem i _ (partitionEmbed_lower P i u) (partitionEmbed_upper P i u)]
  change ((P.point i.castSucc : ℝ)+P.width i*(u : ℝ)-(P.point i.castSucc : ℝ))/P.width i = _
  field_simp [(P.width_pos i).ne']
  ring

theorem partition_coord_embed {n : ℕ} (P : IntervalPartition n) (i r : Fin n) (u : I) :
    P.coord r (partitionEmbed P i u) = if r < i then 1 else if r=i then u else 0 := by
  rcases lt_trichotomy r i with h | h | h
  · rw [ite_eq_left h]
    apply P.coord_of_ge
    have ho : P.point r.succ ≤ P.point i.castSucc := P.strictMono.monotone (by
      show r.val+1 ≤ i.val
      exact h)
    exact ho.trans (partitionEmbed_lower P i u)
  · subst r
    simp only [lt_self_iff_false,ite_false,ite_true,partition_coord_embed_self]
  · rw [ite_eq_right (not_lt_of_gt h),ite_eq_right (ne_of_gt h)]
    apply P.coord_of_le
    have ho : P.point i.succ ≤ P.point r.castSucc := P.strictMono.monotone (by
      show i.val+1 ≤ r.val
      exact h)
    exact (partitionEmbed_upper P i u).trans ho

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
