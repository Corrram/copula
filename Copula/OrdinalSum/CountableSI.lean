import Copula.OrdinalSum.Countable
import Copula.OrdinalSum.Cut
import Copula.Dependence.Examples

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- Every partition endpoint is a diagonal fixed point of the countable sum. -/
theorem countableOrdinalSumPi_diagonal_fixed (P : CountableIntervalPartition)
    (n : ℕ) :
    (countableOrdinalSumPi P).diagonal (P.point n) = P.point n := by
  have hc (k : ℕ) :
      (P.coord k (P.point n) : ℝ) * P.coord k (P.point n) =
        P.coord k (P.point n) := by
    by_cases h : k < n
    · have hkn : k + 1 ≤ n := Nat.succ_le_iff.mpr h
      have hp : P.point (k + 1) ≤ P.point n := P.strictMono.monotone hkn
      rw [P.coord_of_ge k (P.point n) hp]
      norm_num
    · have hnk : n ≤ k := Nat.le_of_not_gt h
      have hp : P.point n ≤ P.point k := P.strictMono.monotone hnk
      rw [P.coord_of_le k (P.point n) hp]
      norm_num
  change (countableOrdinalSumPi P).cdf ![P.point n, P.point n] =
    (P.point n : ℝ)
  rw [cdf_countableOrdinalSumPi]
  simp_rw [hc]
  exact (P.hasSum_width_mul_coord (P.point n)).tsum_eq


private theorem coord_interp (P : CountableIntervalPartition)
    (k j : ℕ) (v : I) (hl : P.point k ≤ v) (hr : v ≤ P.point (k+1)) :
    (P.coord j v : ℝ) =
      (1 - (P.coord k v : ℝ)) * P.coord j (P.point k) +
        (P.coord k v : ℝ) * P.coord j (P.point (k+1)) := by
  rcases lt_trichotomy j k with hj | rfl | hj
  · have hbefore : j + 1 ≤ k := by omega
    rw [P.coord_of_ge j v ((P.strictMono.monotone hbefore).trans hl),
      P.coord_of_ge j (P.point k) (P.strictMono.monotone hbefore),
      P.coord_of_ge j (P.point (k+1))
        (P.strictMono.monotone (by omega))]
    ring
  · rw [P.coord_of_le j (P.point j) (le_refl _),
      P.coord_of_ge j (P.point (j+1)) (le_refl _)]
    simp
  · have hafter : k + 1 ≤ j := by omega
    rw [P.coord_of_le j v (hr.trans (P.strictMono.monotone hafter)),
      P.coord_of_le j (P.point k) (P.strictMono.monotone (by omega)),
      P.coord_of_le j (P.point (k+1)) (P.strictMono.monotone hafter)]
    ring

private theorem cdf_interp (P : CountableIntervalPartition)
    (k : ℕ) (u v : I) (hl : P.point k ≤ v) (hr : v ≤ P.point (k+1)) :
    (countableOrdinalSumPi P).cdf ![u,v] =
      (1 - (P.coord k v : ℝ)) *
        (countableOrdinalSumPi P).cdf ![u,P.point k] +
      (P.coord k v : ℝ) *
        (countableOrdinalSumPi P).cdf ![u,P.point (k+1)] := by
  let F (w : I) (j : ℕ) : ℝ :=
    P.width j * ((P.coord j u : ℝ) * P.coord j w)
  have hs (w : I) : Summable (F w) := by
    simpa [F, cdf_independence, Fin.prod_univ_two] using
      P.summable_cdf (fun _ => independence 2) u w
  have hf (j : ℕ) :
      F v j =
        (1 - (P.coord k v : ℝ)) * F (P.point k) j +
          (P.coord k v : ℝ) * F (P.point (k+1)) j := by
    dsimp [F]
    rw [coord_interp P k j v hl hr]
    ring
  simp only [cdf_countableOrdinalSumPi]
  change (∑' j, F v j) =
    (1 - (P.coord k v : ℝ)) * (∑' j, F (P.point k) j) +
      (P.coord k v : ℝ) * (∑' j, F (P.point (k+1)) j)
  simp_rw [hf]
  rw [Summable.tsum_add ((hs (P.point k)).mul_left _)
    ((hs (P.point (k+1))).mul_left _)]
  simp_rw [tsum_mul_left]
private theorem countablePi_si_on_block (P : CountableIntervalPartition)
    (k : ℕ) (v : I) (hl : P.point k ≤ v) (hr : v ≤ P.point (k+1)) :
    ∀ a b c : I, a ≤ b → b ≤ c →
      ((b : ℝ) - (a : ℝ)) * (countableOrdinalSumPi P).cdf ![c,v] +
        ((c : ℝ) - (b : ℝ)) * (countableOrdinalSumPi P).cdf ![a,v] ≤
          ((c : ℝ) - (a : ℝ)) * (countableOrdinalSumPi P).cdf ![b,v] := by
  let C := countableOrdinalSumPi P
  let t : ℝ := P.coord k v
  have ht0 : 0 ≤ t := (P.coord k v).property.1
  have ht1 : t ≤ 1 := (P.coord k v).property.2
  have hfun (u : I) : C.cdf ![u,v] =
      (1-t) * min (u : ℝ) (P.point k) +
        t * min (u : ℝ) (P.point (k+1)) := by
    dsimp [C,t]
    rw [cdf_interp P k u v hl hr,
      (countableOrdinalSumPi P).cdf_right_cut (P.point k) u
        (countableOrdinalSumPi_diagonal_fixed P k),
      (countableOrdinalSumPi P).cdf_right_cut (P.point (k+1)) u
        (countableOrdinalSumPi_diagonal_fixed P (k+1))]
  intro a b c hab hbc
  have hL := isSI_comonotonic a b c (P.point k) hab hbc
  have hR := isSI_comonotonic a b c (P.point (k+1)) hab hbc
  simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hL hR
  have hL' := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr ht1)
  have hR' := mul_le_mul_of_nonneg_left hR ht0
  rw [hfun a, hfun b, hfun c]
  nlinarith [hL', hR']
theorem countableOrdinalSumPi_isSI (P : CountableIntervalPartition) :
    (countableOrdinalSumPi P).IsSI := by
  intro a b c v hab hbc
  by_cases hv : v = 1
  · subst v
    simp only [cdf_two_one_right]
    nlinarith
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_ne v.property.2 (by
    intro h
    apply hv
    apply Subtype.ext
    exact h)
  have hev : ∀ᶠ n : ℕ in atTop, (v : ℝ) < P.point n :=
    P.tendsto_one.eventually (eventually_gt_nhds hv1)
  obtain ⟨n, hn⟩ := hev.exists
  have hex : ∃ k : ℕ, v ≤ P.point (k+1) := by
    exact ⟨n, le_of_lt (hn.trans (P.strictMono (Nat.lt_succ_self n)))⟩
  let k := Nat.find hex
  have hR : v ≤ P.point (k+1) := Nat.find_spec hex
  have hL : P.point k ≤ v := by
    by_cases hk : k = 0
    · simp [hk, P.zero]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hprev : k - 1 < k := by omega
      have hnot : ¬ v ≤ P.point ((k-1)+1) := Nat.find_min hex hprev
      have heq : k - 1 + 1 = k := by omega
      rw [heq] at hnot
      exact le_of_not_ge hnot
  exact countablePi_si_on_block P k v hL hR a b c hab hbc
end ProbabilityTheory.Copula
