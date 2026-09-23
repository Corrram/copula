import Copula.Rank.Region.TauFootruleBeta.Support.RankMoments
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Finite shuffles with increasing strips

The construction is a sum of actual uniform segment laws. The tiling conditions
state that the horizontal and vertical strips partition the unit interval;
zero-width strips are allowed throughout.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support

noncomputable def stripCut (s a u : ℝ) : ℝ := min s (max 0 (u - a))

theorem stripCut_eq_min_sub {s a u : ℝ} (hs : 0 ≤ s) :
    stripCut s a u = min u (a + s) - min u a := by
  unfold stripCut
  rcases le_total u a with h | h
  · rw [max_eq_left (by linarith), min_eq_right hs,
      min_eq_left (by linarith), min_eq_left h]
    ring
  · rw [max_eq_right (by linarith), min_eq_right h]
    rcases le_total u (a + s) with h' | h'
    · rw [min_eq_right (by linarith), min_eq_left h']
    · rw [min_eq_left (by linarith), min_eq_right h']
      ring

theorem stripCut_zero {s a u : ℝ} (hs : 0 ≤ s) (hu : u ≤ a) :
    stripCut s a u = 0 := by
  rw [stripCut, max_eq_left (sub_nonpos.mpr hu), min_eq_right hs]

theorem stripCut_full {s a u : ℝ} (hu : a + s ≤ u) :
    stripCut s a u = s :=
  min_eq_left ((by linarith : s ≤ u - a).trans (le_max_right _ _))

theorem stripCut_inside {s a u : ℝ} (h0 : a ≤ u) (h1 : u ≤ a + s) :
    stripCut s a u = u - a := by
  rw [stripCut, max_eq_right (sub_nonneg.mpr h0), min_eq_right (by linarith)]

structure ShuffleStrip where
  x : ℝ
  y : ℝ
  width : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  width_nonneg : 0 ≤ width
  x_end : x + width ≤ 1
  y_end : y + width ≤ 1

namespace ShuffleStrip

noncomputable def point (S : ShuffleStrip) (u : I) : Fin 2 → I :=
  ![⟨S.x + S.width * u, ⟨by nlinarith [S.x_nonneg, S.width_nonneg, u.property.1],
      by nlinarith [S.x_end, S.width_nonneg, u.property.2]⟩⟩,
    ⟨S.y + S.width * u, ⟨by nlinarith [S.y_nonneg, S.width_nonneg, u.property.1],
      by nlinarith [S.y_end, S.width_nonneg, u.property.2]⟩⟩]

@[fun_prop] theorem continuous_point (S : ShuffleStrip) : Continuous S.point := by
  unfold point
  fun_prop

noncomputable def law (S : ShuffleStrip) : Measure (Fin 2 → I) :=
  ENNReal.ofReal S.width • (volume : Measure I).map S.point

instance (S : ShuffleStrip) : IsFiniteMeasure S.law := by
  constructor
  simp [law, Measure.map_apply S.continuous_point.measurable]

theorem law_univ (S : ShuffleStrip) : S.law univ = ENNReal.ofReal S.width := by
  simp [law, Measure.map_apply S.continuous_point.measurable]

theorem law_Iic (S : ShuffleStrip) (u : Fin 2 → I) :
    S.law (Iic u) = ENNReal.ofReal
      (min (stripCut S.width S.x (u 0)) (stripCut S.width S.y (u 1))) := by
  by_cases hs : S.width = 0
  · simp [law, hs, stripCut]
  have hspos : 0 < S.width := lt_of_le_of_ne S.width_nonneg (Ne.symm hs)
  rw [law, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply S.continuous_point.measurable measurableSet_Iic]
  by_cases hx : (u 0 : ℝ) < S.x
  · have he : S.point ⁻¹' Iic u = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have ht0 := ht 0
      change S.x + S.width * (t : ℝ) ≤ u 0 at ht0
      nlinarith [t.property.1]
    rw [he, measure_empty, mul_zero]
    simp [stripCut, max_eq_left (sub_nonpos.mpr hx.le), S.width_nonneg]
  by_cases hy : (u 1 : ℝ) < S.y
  · have he : S.point ⁻¹' Iic u = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have ht1 := ht 1
      change S.y + S.width * (t : ℝ) ≤ u 1 at ht1
      nlinarith [t.property.1]
    rw [he, measure_empty, mul_zero]
    simp [stripCut, max_eq_left (sub_nonpos.mpr hy.le), S.width_nonneg]
  have hx' : 0 ≤ (u 0 : ℝ) - S.x := by linarith
  have hy' : 0 ≤ (u 1 : ℝ) - S.y := by linarith
  let r := min S.width (min ((u 0 : ℝ) - S.x) ((u 1 : ℝ) - S.y))
  have hr0 : 0 ≤ r := le_min S.width_nonneg (le_min hx' hy')
  have hr1 : r ≤ S.width := min_le_left _ _
  let t : I := ⟨r / S.width, ⟨div_nonneg hr0 S.width_nonneg,
    (div_le_one hspos).mpr hr1⟩⟩
  have he : S.point ⁻¹' Iic u = Iic t := by
    ext z
    simp only [mem_preimage, mem_Iic, Pi.le_def]
    change (∀ i, S.point z i ≤ u i) ↔ (z : ℝ) ≤ r / S.width
    rw [le_div_iff₀ hspos]
    dsimp [r]
    rw [le_min_iff, le_min_iff]
    constructor
    · intro hz
      have h0 := hz 0
      have h1 := hz 1
      change S.x + S.width * (z : ℝ) ≤ u 0 at h0
      change S.y + S.width * (z : ℝ) ≤ u 1 at h1
      exact ⟨by nlinarith [z.property.2], by constructor <;> nlinarith⟩
    · intro hz i
      fin_cases i
      · change S.x + S.width * (z : ℝ) ≤ u 0
        nlinarith [hz.2.1]
      · change S.y + S.width * (z : ℝ) ≤ u 1
        nlinarith [hz.2.2]
  rw [he, unitInterval.volume_Iic, ← ENNReal.ofReal_mul S.width_nonneg]
  congr 1
  change S.width * (r / S.width) = _
  rw [mul_div_cancel₀ _ hs]
  simp only [stripCut, max_eq_right hx', max_eq_right hy', r]
  simp only [min_def]
  split_ifs <;> linarith

theorem integral_law (S : ShuffleStrip) {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂S.law) = S.width * ∫ u : I, f (S.point u) := by
  rw [law, integral_smul_measure,
    integral_map S.continuous_point.measurable.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal S.width_nonneg]
  rfl

end ShuffleStrip

structure PositiveShuffle (n : ℕ) where
  strip : Fin n → ShuffleStrip
  total : ∑ i, (strip i).width = 1
  tile_x : ∀ u : I, ∑ i, stripCut (strip i).width (strip i).x u = u
  tile_y : ∀ u : I, ∑ i, stripCut (strip i).width (strip i).y u = u

namespace PositiveShuffle

variable {n : ℕ}

noncomputable def law (S : PositiveShuffle n) : Measure (Fin 2 → I) :=
  ∑ i, (S.strip i).law

instance (S : PositiveShuffle n) : IsFiniteMeasure S.law := by
  unfold law
  infer_instance

instance (S : PositiveShuffle n) : IsProbabilityMeasure S.law := by
  constructor
  simp only [law, Measure.finsetSum_apply, ShuffleStrip.law_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (S.strip i).width_nonneg), S.total]
  norm_num

theorem law_Iic (S : PositiveShuffle n) (u : Fin 2 → I) :
    S.law (Iic u) = ENNReal.ofReal (∑ i,
      min (stripCut (S.strip i).width (S.strip i).x (u 0))
        (stripCut (S.strip i).width (S.strip i).y (u 1))) := by
  simp only [law, Measure.finsetSum_apply, ShuffleStrip.law_Iic]
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro i _
  exact le_min (le_min (S.strip i).width_nonneg (le_max_left _ _))
    (le_min (S.strip i).width_nonneg (le_max_left _ _))

theorem marginal (S : PositiveShuffle n) (j : Fin 2) :
    S.law.map (fun x => x j) = volume := by
  apply Measure.ext_of_Iic
  intro u
  rw [Measure.map_apply (measurable_pi_apply _) measurableSet_Iic]
  fin_cases j
  · have he : (fun x : Fin 2 → I => x 0) ⁻¹' Iic u = Iic ![u, 1] := by
      ext x
      simp only [mem_preimage, mem_Iic, Pi.le_def, Fin.forall_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨fun h => ⟨h, (x 1).property.2⟩, fun h => h.1⟩
    change S.law ((fun x => x 0) ⁻¹' Iic u) = _
    rw [he, law_Iic, unitInterval.volume_Iic, ← S.tile_x u]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change min (stripCut (S.strip i).width (S.strip i).x u)
      (stripCut (S.strip i).width (S.strip i).y 1) = _
    have hy : stripCut (S.strip i).width (S.strip i).y 1 = (S.strip i).width := by
      unfold stripCut
      apply min_eq_left
      exact le_trans (by linarith [(S.strip i).y_end]) (le_max_right _ _)
    rw [hy]
    exact min_eq_left (min_le_left _ _)
  · have he : (fun x : Fin 2 → I => x 1) ⁻¹' Iic u = Iic ![1, u] := by
      ext x
      simp only [mem_preimage, mem_Iic, Pi.le_def, Fin.forall_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨fun h => ⟨(x 0).property.2, h⟩, fun h => h.2⟩
    change S.law ((fun x => x 1) ⁻¹' Iic u) = _
    rw [he, law_Iic, unitInterval.volume_Iic, ← S.tile_y u]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change min (stripCut (S.strip i).width (S.strip i).x 1)
      (stripCut (S.strip i).width (S.strip i).y u) = _
    have hx : stripCut (S.strip i).width (S.strip i).x 1 = (S.strip i).width := by
      unfold stripCut
      apply min_eq_left
      exact le_trans (by linarith [(S.strip i).x_end]) (le_max_right _ _)
    rw [hx]
    exact min_eq_right (min_le_left _ _)

noncomputable def copula (S : PositiveShuffle n) : Copula 2 where
  measure := ⟨S.law, inferInstance⟩
  marginal_eq := S.marginal

theorem cdf (S : PositiveShuffle n) (u : Fin 2 → I) :
    S.copula.cdf u = ∑ i,
      min (stripCut (S.strip i).width (S.strip i).x (u 0))
        (stripCut (S.strip i).width (S.strip i).y (u 1)) := by
  change (S.law (Iic u)).toReal = _
  rw [S.law_Iic, ENNReal.toReal_ofReal]
  apply Finset.sum_nonneg
  intro i _
  exact le_min (le_min (S.strip i).width_nonneg (le_max_left _ _))
    (le_min (S.strip i).width_nonneg (le_max_left _ _))

theorem integral_copula (S : PositiveShuffle n) {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂S.copula.toMeasure) =
      ∑ i, (S.strip i).width * ∫ u : I, f ((S.strip i).point u) := by
  change (∫ x, f x ∂(∑ i, (S.strip i).law)) = _
  rw [integral_finsetSum_measure]
  · exact Finset.sum_congr rfl fun i _ => (S.strip i).integral_law hf
  · intro i _
    exact Copula.integrable_continuous_cube _ hf

theorem footrule (S : PositiveShuffle n) : S.copula.spearmanFootrule =
    1 - 3 * ∑ i, (S.strip i).width * |(S.strip i).x - (S.strip i).y| := by
  rw [footrule_eq_abs_moment, S.integral_copula (by fun_prop)]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun u : I => |(((S.strip i).point u) 0 : ℝ) - ((S.strip i).point u) 1|) =
      fun _ : I => |(S.strip i).x - (S.strip i).y| := by
    funext u
    congr 1
    change (S.strip i).x + (S.strip i).width * u -
      ((S.strip i).y + (S.strip i).width * u) = _
    ring
  rw [he]
  simp

theorem cdf_point (S : PositiveShuffle n) (π : Equiv.Perm (Fin n))
    (hx : ∀ i j, i < j → (S.strip i).x + (S.strip i).width ≤ (S.strip j).x)
    (hy : ∀ i j, π i < π j → (S.strip i).y + (S.strip i).width ≤ (S.strip j).y)
    (i : Fin n) (u : I) :
    S.copula.cdf ((S.strip i).point u) =
      (S.strip i).width * u + ∑ j, if j < i ∧ π j < π i then (S.strip j).width else 0 := by
  rw [S.cdf]
  have ht (j : Fin n) :
      min (stripCut (S.strip j).width (S.strip j).x (((S.strip i).point u) 0))
        (stripCut (S.strip j).width (S.strip j).y (((S.strip i).point u) 1)) =
      (if j = i then (S.strip i).width * (u : ℝ) else 0) +
        (if j < i ∧ π j < π i then (S.strip j).width else 0) := by
    have hw := (S.strip i).width_nonneg
    have hu0 := u.property.1
    have hu1 := u.property.2
    change min (stripCut (S.strip j).width (S.strip j).x ((S.strip i).x + (S.strip i).width * u))
      (stripCut (S.strip j).width (S.strip j).y ((S.strip i).y + (S.strip i).width * u)) = _
    by_cases hij : j = i
    · subst j
      rw [stripCut_inside (by nlinarith) (by nlinarith),
        stripCut_inside (by nlinarith) (by nlinarith)]
      simp
    rw [ite_eq_right hij]
    by_cases hji : j < i ∧ π j < π i
    · rw [ite_eq_left hji, stripCut_full (by nlinarith [hx j i hji.1]),
        stripCut_full (by nlinarith [hy j i hji.2]), min_self, zero_add]
    rw [ite_eq_right hji, zero_add]
    by_cases hj : j < i
    · have hπ : π i < π j := lt_of_le_of_ne (le_of_not_gt (fun h => hji ⟨hj, h⟩))
        (fun he => hij (π.injective he.symm))
      rw [stripCut_zero (a := (S.strip j).y) (S.strip j).width_nonneg
        (by nlinarith [hy i j hπ])]
      exact min_eq_right (le_min (S.strip j).width_nonneg (le_max_left _ _))
    · have hi : i < j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hij)
      rw [stripCut_zero (S.strip j).width_nonneg (by nlinarith [hx i j hi])]
      exact min_eq_left (le_min (S.strip j).width_nonneg (le_max_left _ _))
  simp_rw [ht, Finset.sum_add_distrib]
  simp

theorem tau (S : PositiveShuffle n) (π : Equiv.Perm (Fin n))
    (hx : ∀ i j, i < j → (S.strip i).x + (S.strip i).width ≤ (S.strip j).x)
    (hy : ∀ i j, π i < π j → (S.strip i).y + (S.strip i).width ≤ (S.strip j).y) :
    S.copula.kendallTau = 4 * (∑ i, (S.strip i).width *
      ((S.strip i).width / 2 + ∑ j, if j < i ∧ π j < π i then (S.strip j).width else 0)) - 1 := by
  rw [Copula.kendallTau, S.integral_copula S.copula.continuous_cdf]
  simp_rw [S.cdf_point π hx hy]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_add ((Copula.integrable_continuous_unit volume (by fun_prop)).const_mul _)
      (integrable_const _), integral_const_mul, Copula.integral_unit_id, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

end PositiveShuffle
end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
