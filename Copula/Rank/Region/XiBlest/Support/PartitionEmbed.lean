import Copula.Checkerboard
import Copula.Rank.Integration

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Affine embedding of the unit interval into one partition cell. -/
def partitionEmbed {n : ℕ} (P : IntervalPartition n) (i : Fin n) (u : I) : I :=
  ⟨(P.point i.castSucc : ℝ)+P.width i*(u : ℝ),
    add_nonneg (P.point i.castSucc).property.1 (mul_nonneg (P.width_pos i).le u.property.1),
    by have h := mul_le_mul_of_nonneg_left u.property.2 (P.width_pos i).le
       have hp := (P.point i.succ).property.2
       dsimp only [IntervalPartition.width] at *
       nlinarith⟩

theorem partitionEmbed_continuous {n : ℕ} (P : IntervalPartition n) (i : Fin n) :
    Continuous (partitionEmbed P i) := by unfold partitionEmbed; fun_prop

theorem partitionEmbed_lower {n : ℕ} (P : IntervalPartition n) (i : Fin n) (u : I) :
    P.point i.castSucc ≤ partitionEmbed P i u := by
  change (P.point i.castSucc : ℝ) ≤ (P.point i.castSucc : ℝ)+P.width i*(u : ℝ)
  exact le_add_of_nonneg_right (mul_nonneg (P.width_pos i).le u.property.1)

theorem partitionEmbed_upper {n : ℕ} (P : IntervalPartition n) (i : Fin n) (u : I) :
    partitionEmbed P i u ≤ P.point i.succ := by
  change (P.point i.castSucc : ℝ)+P.width i*(u : ℝ) ≤ (P.point i.succ : ℝ)
  have h := mul_le_mul_of_nonneg_left u.property.2 (P.width_pos i).le
  dsimp only [IntervalPartition.width] at *
  nlinarith

theorem partitionEmbed_le_iff {n : ℕ} (P : IntervalPartition n) (i : Fin n) (u v : I)
    (hv : P.point i.castSucc ≤ v) :
    partitionEmbed P i u ≤ v ↔ u ≤ P.coord i v := by
  by_cases h : P.point i.succ ≤ v
  · rw [P.coord_of_ge i v h]
    exact iff_of_true ((partitionEmbed_upper P i u).trans h) u.property.2
  · have hv' : v ≤ P.point i.succ := le_of_not_ge h
    change (P.point i.castSucc : ℝ)+P.width i*(u : ℝ) ≤ (v : ℝ) ↔ (u : ℝ) ≤ (P.coord i v : ℝ)
    rw [P.coe_coord_of_mem i v hv hv',le_div_iff₀ (P.width_pos i)]
    constructor <;> intro h <;> nlinarith

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
