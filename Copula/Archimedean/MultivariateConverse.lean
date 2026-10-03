/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Multivariate
import Copula.Archimedean.Converse
import Copula.Multivariate.Survival
import Mathlib.Analysis.Convex.Continuous

/-!
# The converse of McNeil–Nešlehová: `d`-copula generators are `d`-monotone

**McNeil–Nešlehová (2009), Theorem 2.2 ("only if" part).** If `C(u) = ψ(φ(u₁) + ⋯ + φ(u_d))` is
a `d`-copula, then the inverse generator `ψ` is `d`-monotone on `(0, ∞)`
(`HasArchimedeanGenerator.isMultiplyMonotone`). Together with the "if" part
(`MultivariateGenerator.copula`) this characterizes the generators of `d`-dimensional
Archimedean copulas (`exists_hasArchimedeanGenerator_iff`).

The proof has two independent halves.

* **From the copula to corner sums.** Points `ψ(yᵢ)` of the unit interval are mapped by the
  copula to `ψ(∑ yᵢ)` (`HasArchimedeanGenerator.cdf_eq_toFun_sum`), so the partial finite
  differences of `C` over boxes with corners `ψ(yᵢ)` and `ψ(yᵢ + hᵢ)` are the alternating corner
  sums `∑_{t ⊆ s} (-1)^{|t|} ψ(x + ∑_{i ∈ t} hᵢ)`. These are probabilities, hence nonnegative, for
  every `x > 0`, `hᵢ ≥ 0` and `|s| ≤ d` (`HasArchimedeanGenerator.hasNonnegCornerSums`).
* **From corner sums to `d`-monotonicity** (Williamson 1956; this is the analytic content of
  the converse). A function with nonnegative corner sums of all orders `≤ n` on `(0, ∞)` is
  `n`-monotone (`HasNonnegCornerSums.isMultiplyMonotone`), by induction on `n`:
  orders `≤ 2` give nonnegativity, antitonicity and (through nondecreasing increments,
  `convexOn_of_antitoneOn_of_increment_le`) convexity. For `n ≥ 3`, the difference quotients
  `k_c(x) = (f(x) - f(x + c)) / c` have nonnegative corner sums of orders `≤ n - 1`, hence are
  convex; their pointwise limit `-f'₊` (minus the right derivative of the convex function `f`) is
  therefore convex, hence continuous on `(0, ∞)`, which forces the left and right derivatives
  of `f` to agree. So `f` is differentiable and `-f' = lim k_c` inherits nonnegative corner sums
  of orders `≤ n - 1`.

No continuity or differentiability of `ψ` is assumed: it is a consequence.

References: A. J. McNeil and J. Nešlehová, *Multivariate Archimedean copulas, d-monotone
functions and ℓ₁-norm symmetric distributions*, Ann. Statist. 37 (2009) 3059–3097, Theorem 2.2;
R. E. Williamson, *Multiply monotone functions and their Laplace transforms*, Duke Math. J. 23
(1956) 189–207.
-/

open Set Filter Topology
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-! ### Corner sums under reindexing -/

section CornerSum

theorem cornerSum_map {ι κ : Type*} (e : ι ↪ κ) (f : ℝ → ℝ) (x : ℝ) (h : κ → ℝ)
    (s : Finset ι) : cornerSum f x h (s.map e) = cornerSum f x (h ∘ e) s := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | @insert j s hj ih =>
    have hj' : e j ∉ s.map e := by simpa using hj
    rw [Finset.map_insert, cornerSum_insert _ _ _ hj', cornerSum_insert _ _ _ hj, ih, ih]
    rfl

/-- Adding a coordinate in front: `Δ_{(c, h)} f (x) = Δ_h f (x) - Δ_h f (x + c)`. -/
theorem cornerSum_fin_cons {k : ℕ} (f : ℝ → ℝ) (x c : ℝ) (h : Fin k → ℝ) :
    cornerSum f x (Fin.cons c h : Fin (k + 1) → ℝ) Finset.univ =
      cornerSum f x h Finset.univ - cornerSum f (x + c) h Finset.univ := by
  rw [Fin.univ_succ, Finset.cons_eq_insert, cornerSum_insert _ _ _
    (by simp), cornerSum_map, cornerSum_map, Fin.cons_zero]
  rfl

/-- Corner sums of the difference quotient `(f(x) - f(x + c)) / c`. -/
theorem cornerSum_diffQuot {ι : Type*} (f : ℝ → ℝ) (x c : ℝ) (h : ι → ℝ) (s : Finset ι) :
    cornerSum (fun y => (f y - f (y + c)) / c) x h s =
      (cornerSum f x h s - cornerSum f (x + c) h s) / c := by
  unfold cornerSum
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  rw [add_right_comm x c]
  ring

end CornerSum

/-! ### Functions with nonnegative corner sums -/

/-- `f` has nonnegative alternating corner sums of all orders `≤ n` on `(0, ∞)`:
`∑_{t ⊆ {1,…,k}} (-1)^{|t|} f(x + ∑_{i ∈ t} hᵢ) ≥ 0` for `k ≤ n`, `x > 0`, `hᵢ ≥ 0`. -/
def HasNonnegCornerSums (n : ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ k ≤ n, ∀ x, 0 < x → ∀ h : Fin k → ℝ, (∀ i, 0 ≤ h i) → 0 ≤ cornerSum f x h Finset.univ

namespace HasNonnegCornerSums

variable {n : ℕ} {f : ℝ → ℝ}

theorem mono {m : ℕ} (hf : HasNonnegCornerSums n f) (hmn : m ≤ n) : HasNonnegCornerSums m f :=
  fun k hk => hf k (hk.trans hmn)

theorem nonneg (hf : HasNonnegCornerSums n f) {x : ℝ} (hx : 0 < x) : 0 ≤ f x := by
  have h := hf 0 (Nat.zero_le n) x hx Fin.elim0 (fun i => i.elim0)
  rwa [Finset.univ_eq_empty, cornerSum_empty] at h

theorem antitoneOn (hf : HasNonnegCornerSums n f) (hn : 1 ≤ n) : AntitoneOn f (Ioi 0) := by
  intro x hx y _ hxy
  have h := hf 1 hn x hx (fun _ => y - x) (fun _ => sub_nonneg.2 hxy)
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, cornerSum_singleton,
    add_sub_cancel] at h
  linarith

theorem corner_two (hf : HasNonnegCornerSums n f) (hn : 2 ≤ n) {x a b : ℝ} (hx : 0 < x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ f x - f (x + b) - f (x + a) + f (x + a + b) := by
  have h := hf 2 hn x hx ![a, b] (fun i => by fin_cases i <;> simpa)
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl,
    cornerSum_pair _ _ _ (by decide)] at h
  simpa using h

theorem convexOn (hf : HasNonnegCornerSums n f) (hn : 2 ≤ n) : ConvexOn ℝ (Ioi 0) f := by
  have hshift : ∀ ε, 0 < ε → ConvexOn ℝ (Ici 0) (fun t => f (t + ε)) := by
    intro ε hε
    apply convexOn_of_antitoneOn_of_increment_le
    · intro a ha b hb hab
      exact hf.antitoneOn (by omega) (show a + ε ∈ Ioi 0 from add_pos_of_nonneg_of_pos ha hε)
        (show b + ε ∈ Ioi 0 from add_pos_of_nonneg_of_pos hb hε) (by simpa using hab)
    · intro a b c ha hab hc
      have h := hf.corner_two hn (x := a + ε) (a := b - a) (b := c)
        (add_pos_of_nonneg_of_pos ha hε) (sub_nonneg.2 hab) hc
      have e1 : a + ε + (b - a) = b + ε := by ring
      have e2 : a + ε + (b - a) + c = b + c + ε := by ring
      have e3 : a + ε + c = a + c + ε := by ring
      rw [e2, e1, e3] at h
      linarith
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  set ε := min x y with hε
  have hε0 : 0 < ε := lt_min hx hy
  have h := (hshift ε hε0).2 (show x - ε ∈ Ici (0 : ℝ) from
      mem_Ici.2 (sub_nonneg.2 (min_le_left _ _)))
    (show y - ε ∈ Ici (0 : ℝ) from mem_Ici.2 (sub_nonneg.2 (min_le_right _ _))) ha hb hab
  simp only [smul_eq_mul, sub_add_cancel] at h
  have he : a * (x - ε) + b * (y - ε) + ε = a * x + b * y := by
    linear_combination (-ε) * hab
  rw [he] at h
  exact h

/-- The difference quotients `(f(x) - f(x + c)) / c`, `c > 0`, have nonnegative corner sums of
one order less. -/
theorem diffQuot (hf : HasNonnegCornerSums (n + 1) f) {c : ℝ} (hc : 0 < c) :
    HasNonnegCornerSums n (fun y => (f y - f (y + c)) / c) := by
  intro k hk x hx h hh
  rw [cornerSum_diffQuot, ← cornerSum_fin_cons]
  apply div_nonneg _ hc.le
  apply hf (k + 1) (by omega) x hx
  intro i
  refine Fin.cases hc.le (fun j => ?_) i
  simpa using hh j

/-- The difference quotients converge to minus the right derivative. -/
theorem tendsto_diffQuot (hf : HasNonnegCornerSums n f) (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun c => (f x - f (x + c)) / c) (𝓝[>] 0) (𝓝 (-derivWithin f (Ioi x) x)) := by
  have hint : x ∈ interior (Ioi (0 : ℝ)) := by rw [interior_Ioi]; exact hx
  have hd := (hf.convexOn hn).hasDerivWithinAt_rightDeriv_of_mem_interior hint
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi] at hd
  have hmap : Tendsto (fun c => x + c) (𝓝[>] 0) (𝓝[>] x) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun c : ℝ => x + c) (𝓝 0) (𝓝 (x + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact lt_add_of_pos_right x hc
  refine (hd.comp hmap).neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc0 : c ≠ 0 := ne_of_gt hc
  simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
  field_simp
  ring

/-- For `n ≥ 3`, minus the right derivative is convex on `(0, ∞)`. -/
theorem convexOn_neg_rightDeriv (hf : HasNonnegCornerSums (n + 3) f) :
    ConvexOn ℝ (Ioi 0) (fun x => -derivWithin f (Ioi x) x) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ Ioi (0 : ℝ) := (convex_Ioi 0) hx hy ha hb hab
  have hk : ∀ c ∈ Ioi (0 : ℝ), (f (a • x + b • y) - f (a • x + b • y + c)) / c ≤
      a • ((f x - f (x + c)) / c) + b • ((f y - f (y + c)) / c) :=
    fun c hc => ((hf.diffQuot hc).convexOn (by omega)).2 hx hy ha hb hab
  have h1 := hf.tendsto_diffQuot (by omega) hz
  have h2 := ((hf.tendsto_diffQuot (by omega) hx).const_smul a).add
    ((hf.tendsto_diffQuot (by omega) hy).const_smul b)
  exact le_of_tendsto_of_tendsto h1 h2 (eventually_nhdsWithin_of_forall hk)

/-- For `n ≥ 3`, `f` is differentiable on `(0, ∞)`: the right derivative is continuous, so it
agrees with the left derivative. -/
theorem hasDerivAt (hf : HasNonnegCornerSums (n + 3) f) {x : ℝ} (hx : 0 < x) :
    HasDerivAt f (derivWithin f (Ioi x) x) x := by
  have hfc := hf.convexOn (by omega)
  have hint : x ∈ interior (Ioi (0 : ℝ)) := by rw [interior_Ioi]; exact hx
  have hcont : ContinuousAt (fun y => -derivWithin f (Ioi y) y) x :=
    (hf.convexOn_neg_rightDeriv.continuousOn isOpen_Ioi).continuousAt (Ioi_mem_nhds hx)
  have hle : derivWithin f (Iio x) x ≤ derivWithin f (Ioi x) x :=
    hfc.leftDeriv_le_rightDeriv_of_mem_interior hint
  have hge : derivWithin f (Ioi x) x ≤ derivWithin f (Iio x) x := by
    have hlim : Tendsto (fun y => derivWithin f (Ioi y) y) (𝓝[<] x)
        (𝓝 (derivWithin f (Ioi x) x)) := by
      have := hcont.tendsto.neg
      simp only [neg_neg] at this
      exact this.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hx] with y hy
    have hyint : y ∈ interior (Ioi (0 : ℝ)) := by rw [interior_Ioi]; exact hy.1
    exact (hfc.rightDeriv_le_slope_of_mem_interior hyint (show x ∈ Ioi 0 from hx) hy.2).trans
      (hfc.slope_le_leftDeriv_of_mem_interior (show y ∈ Ioi 0 from hy.1) hint hy.2)
  have hL := hfc.hasDerivWithinAt_leftDeriv_of_mem_interior hint
  have hR := hfc.hasDerivWithinAt_rightDeriv_of_mem_interior hint
  rw [le_antisymm hle hge] at hL
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  exact ⟨(hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).1 hL,
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hR⟩

theorem differentiableOn (hf : HasNonnegCornerSums (n + 3) f) : DifferentiableOn ℝ f (Ioi 0) :=
  fun _ hx => (hf.hasDerivAt hx).differentiableAt.differentiableWithinAt

/-- For `n ≥ 3`, `-f'` has nonnegative corner sums of orders `≤ n - 1`. -/
theorem neg_deriv (hf : HasNonnegCornerSums (n + 3) f) :
    HasNonnegCornerSums (n + 2) (fun x => -deriv f x) := by
  intro k hk x hx h hh
  have hpts : ∀ t ∈ (Finset.univ : Finset (Fin k)).powerset, 0 < x + ∑ i ∈ t, h i :=
    fun t ht => add_sum_pos hx (fun i _ => hh i) ht
  rw [cornerSum_congr (g := fun y => -derivWithin f (Ioi y) y)
    (fun t ht => by rw [(hf.hasDerivAt (hpts t ht)).deriv])]
  have hlim : Tendsto (fun c => cornerSum (fun y => (f y - f (y + c)) / c) x h Finset.univ)
      (𝓝[>] 0) (𝓝 (cornerSum (fun y => -derivWithin f (Ioi y) y) x h Finset.univ)) := by
    unfold cornerSum
    apply tendsto_finsetSum
    intro t ht
    exact (hf.tendsto_diffQuot (by omega) (hpts t ht)).const_mul _
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun c (hc : 0 < c) =>
    (hf.diffQuot hc) k hk x hx h hh)

/-- **Williamson's characterization**: nonnegative corner sums of all orders `≤ n` on `(0, ∞)`
imply `n`-monotonicity. -/
theorem isMultiplyMonotone : ∀ {n : ℕ} {f : ℝ → ℝ}, HasNonnegCornerSums n f →
    IsMultiplyMonotone n f
  | 0, _, hf => fun _ hx => hf.nonneg hx
  | 1, _, hf => ⟨fun _ hx => hf.nonneg hx, hf.antitoneOn le_rfl⟩
  | 2, _, hf => ⟨fun _ hx => hf.nonneg hx, hf.antitoneOn (by norm_num), hf.convexOn le_rfl⟩
  | _ + 3, _, hf => ⟨fun _ hx => hf.nonneg hx, hf.differentiableOn, isMultiplyMonotone hf.neg_deriv⟩

end HasNonnegCornerSums

/-- **`n`-monotone functions are exactly the functions with nonnegative alternating corner sums
of all orders `≤ n` on `(0, ∞)`** (Williamson 1956; McNeil–Nešlehová 2009). -/
theorem isMultiplyMonotone_iff_hasNonnegCornerSums {n : ℕ} {f : ℝ → ℝ} :
    IsMultiplyMonotone n f ↔ HasNonnegCornerSums n f := by
  classical
  refine ⟨fun hf k hk x hx h hh => ?_, HasNonnegCornerSums.isMultiplyMonotone⟩
  exact hf.cornerSum_nonneg (by simpa using hk) hx (fun i _ => hh i)

/-! ### From the copula to corner sums -/

namespace BivariateGenerator

/-- The inverse generator is right-continuous at `0`: it takes every value of `(0,1]`. -/
theorem continuousWithinAt_toFun_zero (g : BivariateGenerator) :
    ContinuousWithinAt g.toFun (Ici 0) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set m : ℝ := max (1 - ε / 2) (1 / 2) with hm
  have hm1 : m < 1 := max_lt (by linarith) (by norm_num)
  have hm0 : 1 / 2 ≤ m := le_max_right _ _
  let u : I := ⟨m, by linarith, hm1.le⟩
  have hu0 : u ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    simp only [u, Set.Icc.coe_zero] at this
    linarith
  have hu1 : u ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    simp only [u, Set.Icc.coe_one] at this
    linarith
  refine ⟨g.invFun u, g.invFun_pos hu0 hu1, fun s hs hds => ?_⟩
  have hs0 : 0 ≤ s := hs
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0] at hds
  have h1 := g.antitone hs0 (g.inv_nonneg u hu0) hds.le
  rw [g.right_inv u hu0] at h1
  have h2 := g.toFun_le_one hs0
  rw [Real.dist_eq, g.toFun_zero, abs_of_nonpos (by linarith)]
  have : (u : ℝ) = m := rfl
  have h3 : 1 - ε / 2 ≤ m := le_max_left _ _
  linarith

/-- The inverse generator of a bivariate generator is continuous on `[0, ∞)`. -/
theorem continuousOn_toFun (g : BivariateGenerator) : ContinuousOn g.toFun (Ici 0) :=
  g.convex.continuousOn_Ici g.continuousWithinAt_toFun_zero

end BivariateGenerator

section Copula

variable {d : ℕ} {C : Copula d} {g : BivariateGenerator}

/-- An Archimedean copula maps the point `(ψ(y₁), …, ψ(y_d))` to `ψ(y₁ + ⋯ + y_d)`, for all
`yᵢ ≥ 0` (including the case where some `ψ(yᵢ) = 0`). -/
theorem HasArchimedeanGenerator.cdf_toI (hC : HasArchimedeanGenerator C g) (y : Fin d → ℝ)
    (hy : ∀ i, 0 ≤ y i) : C.cdf (fun i => g.toI (hy i)) = g.toFun (∑ i, y i) := by
  by_cases hpos : ∀ i, 0 < g.toFun (y i)
  · rw [hC _ (fun i => g.toI_ne_zero (hy i) (hpos i))]
    congr 1
    exact Finset.sum_congr rfl fun i _ => g.invFun_toI (hy i) (hpos i)
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hz : g.toFun (y i) = 0 := le_antisymm hi (g.nonneg _ (hy i))
    rw [C.cdf_eq_zero_of_coord_eq_zero _ i (Subtype.ext (by simp [hz]))]
    have hsum : y i ≤ ∑ j, y j := Finset.single_le_sum (fun j _ => hy j) (Finset.mem_univ i)
    have := g.antitone (hy i) (Finset.sum_nonneg fun j _ => hy j) hsum
    have hs0 : 0 ≤ ∑ j, y j := Finset.sum_nonneg fun j _ => hy j
    linarith [g.nonneg _ hs0]

/-- **The generator of a `d`-dimensional Archimedean copula has nonnegative corner sums of all
orders `≤ d`.** -/
theorem HasArchimedeanGenerator.hasNonnegCornerSums (hC : HasArchimedeanGenerator C g) :
    HasNonnegCornerSums d g.toFun := by
  classical
  intro k hk x hx h hh
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Finset.univ_eq_empty, cornerSum_empty]
    exact g.nonneg x hx.le
  set i0 : Fin d := ⟨0, by omega⟩
  set H : Fin d → ℝ := fun i => if hi : (i : ℕ) < k then h ⟨i, hi⟩ else 0 with hH
  have hH0 : ∀ i, 0 ≤ H i := by
    intro i
    simp only [hH]
    split_ifs
    · exact hh _
    · exact le_rfl
  have hHe : H ∘ Fin.castLEEmb hk = h := by
    funext j
    simp [hH, j.isLt]
  set t : Finset (Fin d) := Finset.univ.map (Fin.castLEEmb hk)
  have hct : cornerSum g.toFun x h Finset.univ = cornerSum g.toFun x H t := by
    rw [cornerSum_map, hHe]
  rw [hct]
  set y : Fin d → ℝ := fun i => if i = i0 then x else 0 with hy
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i
    simp only [hy]
    split_ifs
    · exact hx.le
    · exact le_rfl
  have hya : ∀ i, 0 ≤ y i + H i := fun i => add_nonneg (hy0 i) (hH0 i)
  set a : Fin d → I := fun i => g.toI (hya i)
  set b : Fin d → I := fun i => g.toI (hy0 i)
  have hab : a ≤ b := by
    intro i
    show g.toFun (y i + H i) ≤ g.toFun (y i)
    exact g.antitone (hy0 i) (hya i) (le_add_of_nonneg_right (hH0 i))
  have hnn : 0 ≤ partialIncrement C.cdf a b t := by
    rw [C.partialIncrement_cdf a b t hab]
    exact MeasureTheory.measureReal_nonneg
  convert hnn using 1
  unfold partialIncrement cornerSum
  apply Finset.sum_congr rfl
  intro r _
  have hz : ∀ i, 0 ≤ y i + if i ∈ r then H i else 0 := by
    intro i
    split_ifs
    · exact hya i
    · simpa using hy0 i
  have hcorner : corner a b r = fun i => g.toI (hz i) := by
    funext i
    apply Subtype.ext
    by_cases hi : i ∈ r <;> simp [corner, hi, a, b]
  rw [hcorner, hC.cdf_toI _ hz, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
  congr 2
  simp [hy]

/-- **McNeil–Nešlehová (2009), Theorem 2.2, "only if"**: the inverse generator of a
`d`-dimensional Archimedean copula is `d`-monotone on `(0, ∞)`. -/
theorem HasArchimedeanGenerator.isMultiplyMonotone (hC : HasArchimedeanGenerator C g) :
    IsMultiplyMonotone d g.toFun :=
  hC.hasNonnegCornerSums.isMultiplyMonotone

/-- **McNeil–Nešlehová (2009), Theorem 2.2**: a bivariate Archimedean generator generates a
`d`-dimensional copula `ψ(φ(u₁) + ⋯ + φ(u_d))` if and only if `ψ` is `d`-monotone. -/
theorem exists_hasArchimedeanGenerator_iff (g : BivariateGenerator) :
    (∃ C : Copula d, HasArchimedeanGenerator C g) ↔ IsMultiplyMonotone d g.toFun := by
  refine ⟨fun ⟨_, hC⟩ => hC.isMultiplyMonotone, fun h => ?_⟩
  let G : MultivariateGenerator d :=
    { g with continuousOn := g.continuousOn_toFun, multiplyMonotone := h }
  exact ⟨G.copula, G.hasArchimedeanGenerator_copula⟩

end Copula

end ProbabilityTheory.Copula
