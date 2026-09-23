import Copula.Rank.Region.XiBlest.Support.Shuffle
import Copula.Rank.Region.XiBlest.Support.Functional
import Copula.TailDependence.Basic

/-! # Equal-width permutation shuffles

The parameter n denotes n+1 strips. Every permutation is allowed, including
the one-strip case. The construction uses uniform laws on the actual segments.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem PositiveShuffle.rho {n : ℕ} (S : PositiveShuffle n) :
    S.copula.spearmanRho =
      1 - 6 * ∑ i, (S.strip i).width * ((S.strip i).x - (S.strip i).y) ^ 2 := by
  rw [Copula.spearmanRho_eq_one_sub, S.integral_copula (by fun_prop)]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun u : I => ((((S.strip i).point u) 0 : ℝ) -
      ((S.strip i).point u) 1) ^ 2) =
      fun _ : I => ((S.strip i).x - (S.strip i).y) ^ 2 := by
    funext u
    congr 1
    change (S.strip i).x + (S.strip i).width * u -
      ((S.strip i).y + (S.strip i).width * u) = _
    ring
  rw [he]
  simp

namespace PermutationShuffle

variable (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))

noncomputable def strip (i : Fin (n + 1)) : ShuffleStrip where
  x := (i : ℝ) / (n + 1)
  y := (π i : ℝ) / (n + 1)
  width := 1 / (n + 1)
  x_nonneg := by positivity
  y_nonneg := by positivity
  width_nonneg := by positivity
  x_end := by
    rw [← add_div, div_le_one (by positivity)]
    exact_mod_cast i.isLt
  y_end := by
    rw [← add_div, div_le_one (by positivity)]
    exact_mod_cast (π i).isLt

private theorem telescope (m : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin m, (f (i.val + 1) - f i.val)) = f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simpa using (show (∑ i : Fin m, (f (i.val + 1) - f i.val)) +
      (f (m + 1) - f m) = f (m + 1) - f 0 by rw [ih]; ring)

theorem tile (u : I) :
    (∑ i : Fin (n + 1), stripCut (1 / ((n : ℝ) + 1)) (i / ((n : ℝ) + 1)) u) = u := by
  simp_rw [stripCut_eq_min_sub (by positivity : 0 ≤ 1 / ((n : ℝ) + 1)), ← add_div]
  have h := telescope (n + 1) (fun i => min (u : ℝ) ((i : ℝ) / (n + 1)))
  simpa [Nat.cast_add, Nat.cast_one, min_eq_left u.property.2,
    min_eq_right u.property.1, ne_of_gt (by positivity : 0 < (n : ℝ) + 1)] using h

noncomputable def shuffle : PositiveShuffle (n + 1) where
  strip := strip n π
  total := by simp [strip]; field_simp
  tile_x := tile n
  tile_y := by
    intro u
    change (∑ i : Fin (n + 1), stripCut (1 / ((n : ℝ) + 1))
      ((π i : ℝ) / (n + 1)) u) = u
    rw [Equiv.sum_comp π (fun i : Fin (n + 1) =>
      stripCut (1 / ((n : ℝ) + 1)) ((i : ℝ) / (n + 1)) u)]
    exact tile n u

noncomputable def copula : Copula 2 := (shuffle n π).copula

theorem ordered_x (i j : Fin (n + 1)) (h : i < j) :
    ((shuffle n π).strip i).x + ((shuffle n π).strip i).width ≤
      ((shuffle n π).strip j).x := by
  change (i : ℝ) / (n + 1) + 1 / (n + 1) ≤ (j : ℝ) / (n + 1)
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast h

theorem ordered_y (i j : Fin (n + 1)) (h : π i < π j) :
    ((shuffle n π).strip i).y + ((shuffle n π).strip i).width ≤
      ((shuffle n π).strip j).y := by
  change (π i : ℝ) / (n + 1) + 1 / (n + 1) ≤ (π j : ℝ) / (n + 1)
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast h

theorem rho : (copula n π).spearmanRho =
    1 - 6 * (∑ i : Fin (n + 1), ((π i : ℝ) - i) ^ 2) / ((n : ℝ) + 1) ^ 3 := by
  rw [copula, PositiveShuffle.rho]
  simp only [shuffle, strip]
  rw [mul_div_assoc, Finset.sum_div]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  ring


noncomputable def graphMap (u : I) : I :=
  ⟨min 1 (max 0 (∑ i : Fin (n + 1),
    if (strip n π i).x < (u : ℝ) ∧ (u : ℝ) < (strip n π i).x + (strip n π i).width
    then (strip n π i).y + (u : ℝ) - (strip n π i).x else 0)),
    le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem measurable_graphMap : Measurable (graphMap n π) := by
  apply Measurable.subtype_mk
  apply Measurable.min measurable_const
  apply Measurable.max measurable_const
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_subtype_coe).inter
      (measurableSet_lt measurable_subtype_coe measurable_const)
  · fun_prop
  · fun_prop

theorem graphMap_point (i : Fin (n + 1)) (u : I) (hu0 : 0 < u) (hu1 : u < 1) :
    graphMap n π ((strip n π i).point u 0) = (strip n π i).point u 1 := by
  have hw : 0 < (strip n π i).width := by dsimp [strip]; positivity
  have hp : (strip n π i).x < ((strip n π i).point u 0 : ℝ) ∧
      ((strip n π i).point u 0 : ℝ) < (strip n π i).x + (strip n π i).width := by
    change (strip n π i).x < (strip n π i).x + (strip n π i).width * u ∧
      (strip n π i).x + (strip n π i).width * u < (strip n π i).x + (strip n π i).width
    have h0 : (0 : ℝ) < u := hu0
    have h1 : (u : ℝ) < 1 := hu1
    constructor <;> nlinarith
  apply Subtype.ext
  change min 1 (max 0 (∑ j : Fin (n + 1),
    if (strip n π j).x < ((strip n π i).point u 0 : ℝ) ∧
      ((strip n π i).point u 0 : ℝ) < (strip n π j).x + (strip n π j).width
    then (strip n π j).y + ((strip n π i).point u 0 : ℝ) - (strip n π j).x else 0)) = _
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left hp]
    have he : (strip n π i).y + ((strip n π i).point u 0 : ℝ) - (strip n π i).x =
        ((strip n π i).point u 1 : ℝ) := by
      change (strip n π i).y + ((strip n π i).x + (strip n π i).width * u) -
        (strip n π i).x = (strip n π i).y + (strip n π i).width * u
      ring
    rw [he, max_eq_right ((strip n π i).point u 1).property.1,
      min_eq_right ((strip n π i).point u 1).property.2]
  · intro j _ hji
    apply ite_eq_right
    intro hj
    rcases lt_or_gt_of_ne hji with h | h
    · have ho := ordered_x n π j i h
      change (strip n π j).x + (strip n π j).width ≤ (strip n π i).x at ho
      linarith [hj.2, hp.1]
    · have ho := ordered_x n π i j h
      change (strip n π i).x + (strip n π i).width ≤ (strip n π j).x at ho
      linarith [hj.1, hp.2]
  · simp

theorem functional : HasFunctionalWitness (copula n π) := by
  refine ⟨graphMap n π, measurable_graphMap n π, ?_⟩
  change ∀ᵐ x ∂(∑ i : Fin (n + 1), (strip n π i).law), _
  rw [ae_finsetSum_measure_iff]
  intro i _
  apply Measure.ae_smul_measure
  apply (ae_map_iff (strip n π i).continuous_point.measurable.aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply 1)
      ((measurable_graphMap n π).comp (measurable_pi_apply 0)))).2
  filter_upwards [(volume : Measure I).ae_ne 0, (volume : Measure I).ae_ne 1] with u h0 h1
  exact (graphMap_point n π i u (lt_of_le_of_ne u.property.1 (Ne.symm h0))
    (lt_of_le_of_ne u.property.2 h1)).symm

theorem xi : (copula n π).chatterjeeXi = 1 := (functional n π).xi_eq_one

/-- Number of inverted pairs, using zero-based strip indices. -/
def inversions : ℕ :=
  ∑ i : Fin (n + 1), (Finset.univ.filter (fun j => j < i ∧ π i < π j)).card

private theorem pair_count (m : ℕ) :
    (∑ i : Fin m, ∑ j : Fin m, if j < i then (1 : ℝ) else 0) =
      (m : ℝ) * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff,
      not_lt_of_ge (Fin.le_last _), ite_false, add_zero, Fin.castSucc_lt_last,
      ite_true]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem tau : (copula n π).kendallTau =
    1 - 4 * (inversions n π : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  classical
  have hi : (inversions n π : ℝ) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if j < i ∧ π i < π j then (1 : ℝ) else 0 := by
    simp [inversions]
  have hc : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if j < i ∧ π j < π i then (1 : ℝ) else 0) + (inversions n π : ℝ) =
        ((n : ℝ) + 1) * n / 2 := by
    rw [hi, ← Finset.sum_add_distrib]
    have he (i j : Fin (n + 1)) :
        (if j < i ∧ π j < π i then (1 : ℝ) else 0) +
        (if j < i ∧ π i < π j then (1 : ℝ) else 0) = if j < i then 1 else 0 := by
      by_cases h : j < i
      · have hn : π j ≠ π i := fun he => (ne_of_lt h) (π.injective he)
        rcases lt_or_gt_of_ne hn with hp | hp <;> simp [h, hp, not_lt_of_gt hp]
      · simp [h]
    simp_rw [← Finset.sum_add_distrib, he]
    simpa using pair_count (n + 1)
  rw [copula, PositiveShuffle.tau _ π (ordered_x n π) (ordered_y n π)]
  simp only [shuffle, strip]
  have he (i : Fin (n + 1)) :
      (∑ j : Fin (n + 1), if j < i ∧ π j < π i then 1 / ((n : ℝ) + 1) else 0) =
      (∑ j : Fin (n + 1), if j < i ∧ π j < π i then (1 : ℝ) else 0) / (n + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  simp_rw [he]
  have ht (c : ℝ) : 1 / ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1) / 2 + c / (n + 1)) =
      (1 / 2 + c) / ((n : ℝ) + 1) ^ 2 := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  simp_rw [ht]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith [hc]


private theorem cut_lower (i : Fin (n + 1)) (t : I) (ht : (t : ℝ) ≤ 1 / ((n : ℝ) + 1)) :
    stripCut (1 / ((n : ℝ) + 1)) (i / ((n : ℝ) + 1)) t =
      if i = 0 then (t : ℝ) else 0 := by
  by_cases hi : i = 0
  · subst i
    simp only [Fin.val_zero, Nat.cast_zero, zero_div, ite_true]
    rw [stripCut_inside t.property.1 (by simpa using ht), sub_zero]
  · rw [ite_eq_right hi]
    apply stripCut_zero (by positivity)
    apply ht.trans
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    have : 1 ≤ i.val := by
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    exact_mod_cast this

theorem diagonal_lower (t : I) (ht : (t : ℝ) ≤ 1 / ((n : ℝ) + 1)) :
    (copula n π).diagonal t = if π 0 = 0 then (t : ℝ) else 0 := by
  rw [Copula.diagonal, copula, PositiveShuffle.cdf]
  change (∑ i : Fin (n + 1),
    min (stripCut (1 / ((n : ℝ) + 1)) (i / ((n : ℝ) + 1)) t)
      (stripCut (1 / ((n : ℝ) + 1)) ((π i : ℝ) / (n + 1)) t)) = _
  simp_rw [cut_lower n _ t ht]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · split_ifs <;> simp_all [min_eq_right t.property.1]
  · intro i _ hi
    rw [ite_eq_right hi]
    split_ifs <;> simp [min_eq_left t.property.1]
  · simp

private theorem cut_upper (i : Fin (n + 1)) (t : I) (ht : (t : ℝ) ≤ 1 / ((n : ℝ) + 1)) :
    1 / ((n : ℝ) + 1) - stripCut (1 / ((n : ℝ) + 1)) (i / ((n : ℝ) + 1)) (1 - t) =
      if i = Fin.last n then (t : ℝ) else 0 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hid : (n : ℝ) / (n + 1) + 1 / (n + 1) = 1 := by field_simp
  by_cases hi : i = Fin.last n
  · subst i
    rw [ite_eq_left rfl, stripCut_inside (by simp only [Fin.val_last]; linarith)
      (by simp only [Fin.val_last]; linarith [t.property.1])]
    simp only [Fin.val_last]
    linarith
  · rw [ite_eq_right hi, stripCut_full, sub_self]
    have hi' : (i : ℝ) + 1 ≤ n := by
      have : i.val + 1 ≤ n := by have := i.isLt; simp only [Fin.ext_iff, Fin.val_last] at hi; omega
      exact_mod_cast this
    have hle : (i : ℝ) / (n + 1) + 1 / (n + 1) ≤ n / (n + 1) := by
      rw [← add_div]
      exact (div_le_div_iff_of_pos_right hn).mpr hi'
    linarith

theorem diagonal_upper (t : I) (ht : (t : ℝ) ≤ 1 / ((n : ℝ) + 1)) :
    (copula n π).diagonal (unitInterval.symm t) =
      1 - 2 * (t : ℝ) + if π (Fin.last n) = Fin.last n then (t : ℝ) else 0 := by
  let w : ℝ := 1 / ((n : ℝ) + 1)
  let a : Fin (n + 1) → ℝ := fun i => stripCut w (i / ((n : ℝ) + 1)) (1 - t)
  let b : Fin (n + 1) → ℝ := fun i => stripCut w ((π i : ℝ) / (n + 1)) (1 - t)
  have ha : ∑ i, a i = 1 - t := tile n (unitInterval.symm t)
  have hb : ∑ i, b i = 1 - t := (shuffle n π).tile_y (unitInterval.symm t)
  have hw : (∑ _ : Fin (n + 1), w) = 1 := (shuffle n π).total
  have he (i : Fin (n + 1)) : min (a i) (b i) = a i + b i - w + min (w - a i) (w - b i) := by
    rcases le_total (a i) (b i) with h | h
    · rw [min_eq_left h, min_eq_right (by linarith)]
      ring
    · rw [min_eq_right h, min_eq_left (by linarith)]
      ring
  have hr : (∑ i, min (w - a i) (w - b i)) =
      if π (Fin.last n) = Fin.last n then (t : ℝ) else 0 := by
    change (∑ i : Fin (n + 1), min
      (w - stripCut w (i / ((n : ℝ) + 1)) (1 - t))
      (w - stripCut w ((π i : ℝ) / (n + 1)) (1 - t))) = _
    simp only [w, cut_upper n _ t ht]
    rw [Finset.sum_eq_single (Fin.last n)]
    · split_ifs <;> simp_all [min_eq_right t.property.1]
    · intro i _ hi
      rw [ite_eq_right hi]
      split_ifs <;> simp [min_eq_left t.property.1]
    · simp
  rw [Copula.diagonal, copula, PositiveShuffle.cdf]
  change (∑ i, min (a i) (b i)) = _
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib, ha, hb, hw, hr]
  ring

private theorem eventually_small :
    ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t ∧ (t : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
  let a : I := ⟨1 / ((n : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]⟩
  have ha : (0 : I) < a := by change (0 : ℝ) < 1 / ((n : ℝ) + 1); positivity
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t),
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
  exact ⟨ht, le_of_lt hta⟩

theorem lower_tail : (copula n π).HasLowerTailDependence (if π 0 = 0 then 1 else 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_small n] with t ht
  rw [Copula.lowerTailRatio, diagonal_lower n π t ht.2]
  split_ifs
  · exact (div_self (ne_of_gt (show (0 : ℝ) < t from ht.1))).symm
  · simp

theorem upper_tail : (copula n π).HasUpperTailDependence
    (if π (Fin.last n) = Fin.last n then 1 else 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_small n] with t ht
  rw [Copula.upperTailRatio_eq, diagonal_upper n π t ht.2]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
  split_ifs <;> field_simp <;> ring

end PermutationShuffle
end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
