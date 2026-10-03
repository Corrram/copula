/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# `d`-monotone functions and alternating corner sums

McNeil and Nešlehová (2009, Definition 2.3) call a real function `ψ` on `(0, ∞)` *`d`-monotone*
(`d ≥ 2`) if it is differentiable up to order `d - 2`, the derivatives satisfy
`(-1)^k ψ^{(k)} ≥ 0` for `k ≤ d - 2`, and `(-1)^{d-2} ψ^{(d-2)}` is nonincreasing and convex;
`1`-monotone means nonnegative and nonincreasing. We encode this recursively
(`IsMultiplyMonotone`): a function is `(n+3)`-monotone if it is nonnegative and differentiable on
`(0, ∞)` and `-ψ'` is `(n+2)`-monotone.

The analytic heart of the Archimedean construction in dimension `d` is the sign of the alternating
corner sums
`cornerSum ψ x h s = ∑_{t ⊆ s} (-1)^{|t|} ψ(x + ∑_{i ∈ t} hᵢ)`,
which are exactly the rectangle increments of `u ↦ ψ(∑ φ(uᵢ))`. We prove
(`IsMultiplyMonotone.cornerSum_nonneg`) that a `d`-monotone `ψ` has nonnegative corner sums
for all `s` with `|s| ≤ d`, all `x > 0` and all `hᵢ ≥ 0` (the "if" direction of
McNeil–Nešlehová 2009, Theorem 2.2, in its analytic form; Williamson 1956), and extend this to
`x = 0` for continuous `ψ` (`IsMultiplyMonotone.cornerSum_nonneg_of_nonneg`). The proof is by
induction on `d` via the mean value theorem; the base case `d = 2` is the convexity of `ψ`.
Completely monotone functions (Kimberling 1974) are `d`-monotone for every `d`.

Power functions `c (1 + t)^{-α}` with `c ≥ 0`, `α > 0` are `d`-monotone for every `d`
(`isMultiplyMonotone_one_add_rpow_neg`); they generate the Clayton family.
-/

open Set Filter Topology
open scoped BigOperators

namespace ProbabilityTheory.Copula

/-! ### Alternating corner sums -/

section CornerSum

variable {ι : Type*}

/-- The alternating corner sum `∑_{t ⊆ s} (-1)^{|t|} f(x + ∑_{i ∈ t} hᵢ)`, i.e. the iterated
difference `(-Δ_{h_{i₁}}) ⋯ (-Δ_{h_{iₖ}}) f (x)` over the coordinates of `s`. -/
noncomputable def cornerSum (f : ℝ → ℝ) (x : ℝ) (h : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * f (x + ∑ i ∈ t, h i)

@[simp]
theorem cornerSum_empty (f : ℝ → ℝ) (x : ℝ) (h : ι → ℝ) : cornerSum f x h ∅ = f x := by
  simp [cornerSum]

/-- The recursion `cornerSum f x h (insert j s) = A(x) - A(x + hⱼ)` with `A = cornerSum f · h s`. -/
theorem cornerSum_insert [DecidableEq ι] (f : ℝ → ℝ) (x : ℝ) (h : ι → ℝ) {s : Finset ι}
    {j : ι} (hj : j ∉ s) :
    cornerSum f x h (insert j s) = cornerSum f x h s - cornerSum f (x + h j) h s := by
  unfold cornerSum
  rw [Finset.sum_powerset_insert hj, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hjt : j ∉ t := fun h' => hj (Finset.mem_powerset.mp ht h')
  rw [Finset.card_insert_of_notMem hjt, Finset.sum_insert hjt, pow_succ, ← add_assoc]
  ring

theorem cornerSum_neg (f : ℝ → ℝ) (x : ℝ) (h : ι → ℝ) (s : Finset ι) :
    cornerSum (fun y => -f y) x h s = -cornerSum f x h s := by
  simp [cornerSum, Finset.sum_neg_distrib]

theorem cornerSum_singleton (f : ℝ → ℝ) (x : ℝ) (h : ι → ℝ) (j : ι) :
    cornerSum f x h {j} = f x - f (x + h j) := by
  classical
  rw [← insert_empty_eq, cornerSum_insert _ _ _ (Finset.notMem_empty j)]
  simp

theorem cornerSum_pair [DecidableEq ι] (f : ℝ → ℝ) (x : ℝ) (h : ι → ℝ) {j k : ι}
    (hjk : j ≠ k) :
    cornerSum f x h {j, k} = f x - f (x + h k) - f (x + h j) + f (x + h j + h k) := by
  rw [cornerSum_insert _ _ _ (by simpa using hjk), cornerSum_singleton, cornerSum_singleton]
  ring_nf

/-- Corner sums are differentiable in the base point, with the corner sum of the derivative. -/
theorem hasDerivAt_cornerSum {f f' : ℝ → ℝ} {x : ℝ} {h : ι → ℝ} {s : Finset ι}
    (hf : ∀ t ∈ s.powerset, HasDerivAt f (f' (x + ∑ i ∈ t, h i)) (x + ∑ i ∈ t, h i)) :
    HasDerivAt (fun y => cornerSum f y h s) (cornerSum f' x h s) x := by
  unfold cornerSum
  apply HasDerivAt.fun_sum
  intro t ht
  exact ((hf t ht).comp_add_const x _).const_mul _

/-- Corner sums depend only on the values of `f` on the corners. -/
theorem cornerSum_congr {f g : ℝ → ℝ} {x : ℝ} {h : ι → ℝ} {s : Finset ι}
    (hfg : ∀ t ∈ s.powerset, f (x + ∑ i ∈ t, h i) = g (x + ∑ i ∈ t, h i)) :
    cornerSum f x h s = cornerSum g x h s :=
  Finset.sum_congr rfl fun t ht => by rw [hfg t ht]

theorem add_sum_nonneg {x : ℝ} {h : ι → ℝ} {s : Finset ι} (hx : 0 ≤ x)
    (hh : ∀ i ∈ s, 0 ≤ h i) {t : Finset ι} (ht : t ∈ s.powerset) : 0 ≤ x + ∑ i ∈ t, h i :=
  add_nonneg hx (Finset.sum_nonneg fun i hi => hh i (Finset.mem_powerset.mp ht hi))

theorem add_sum_pos {x : ℝ} {h : ι → ℝ} {s : Finset ι} (hx : 0 < x)
    (hh : ∀ i ∈ s, 0 ≤ h i) {t : Finset ι} (ht : t ∈ s.powerset) : 0 < x + ∑ i ∈ t, h i :=
  add_pos_of_pos_of_nonneg hx (Finset.sum_nonneg fun i hi => hh i (Finset.mem_powerset.mp ht hi))

end CornerSum

/-! ### `d`-monotone functions -/

/-- **`d`-monotone functions** on `(0, ∞)` (McNeil–Nešlehová 2009, Definition 2.3), defined
recursively: `0`-monotone means nonnegative, `1`-monotone nonnegative and nonincreasing,
`2`-monotone nonnegative, nonincreasing and convex, and `(n+3)`-monotone means nonnegative,
differentiable, with `-ψ'` being `(n+2)`-monotone. -/
def IsMultiplyMonotone : ℕ → (ℝ → ℝ) → Prop
  | 0, f => ∀ x, 0 < x → 0 ≤ f x
  | 1, f => (∀ x, 0 < x → 0 ≤ f x) ∧ AntitoneOn f (Ioi 0)
  | 2, f => (∀ x, 0 < x → 0 ≤ f x) ∧ AntitoneOn f (Ioi 0) ∧ ConvexOn ℝ (Ioi 0) f
  | n + 3, f => (∀ x, 0 < x → 0 ≤ f x) ∧ DifferentiableOn ℝ f (Ioi 0) ∧
      IsMultiplyMonotone (n + 2) (fun x => -deriv f x)

namespace IsMultiplyMonotone

theorem nonneg : ∀ {n : ℕ} {f : ℝ → ℝ}, IsMultiplyMonotone n f → ∀ x, 0 < x → 0 ≤ f x
  | 0, _, hf => hf
  | 1, _, hf => hf.1
  | 2, _, hf => hf.1
  | _ + 3, _, hf => hf.1

/-- `d`-monotonicity depends only on the values on `(0, ∞)`. -/
theorem congr : ∀ {n : ℕ} {f g : ℝ → ℝ}, IsMultiplyMonotone n f → EqOn f g (Ioi 0) →
    IsMultiplyMonotone n g
  | 0, _, _, hf, hfg => fun x hx => hfg hx ▸ hf x hx
  | 1, _, _, hf, hfg => ⟨fun x hx => hfg hx ▸ hf.1 x hx, hf.2.congr hfg⟩
  | 2, _, _, hf, hfg => ⟨fun x hx => hfg hx ▸ hf.1 x hx, hf.2.1.congr hfg, hf.2.2.congr hfg⟩
  | n + 3, f, g, hf, hfg => by
    refine ⟨fun x hx => hfg hx ▸ hf.1 x hx, hf.2.1.congr fun x hx => (hfg hx).symm, ?_⟩
    refine congr (n := n + 2) hf.2.2 fun x hx => ?_
    have : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx) hfg
    simp only [this.deriv_eq]

/-- Nonnegative multiples of `d`-monotone functions are `d`-monotone. -/
theorem const_mul : ∀ {n : ℕ} {f : ℝ → ℝ}, IsMultiplyMonotone n f → ∀ {c : ℝ}, 0 ≤ c →
    IsMultiplyMonotone n (fun x => c * f x)
  | 0, _, hf, _, hc => fun x hx => mul_nonneg hc (hf x hx)
  | 1, _, hf, _, hc => ⟨fun x hx => mul_nonneg hc (hf.1 x hx),
      fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (hf.2 hx hy hxy) hc⟩
  | 2, _, hf, _, hc => ⟨fun x hx => mul_nonneg hc (hf.1 x hx),
      fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (hf.2.1 hx hy hxy) hc,
      by simpa [smul_eq_mul] using hf.2.2.smul hc⟩
  | n + 3, f, hf, c, hc => by
    refine ⟨fun x hx => mul_nonneg hc (hf.1 x hx), hf.2.1.const_mul c, ?_⟩
    refine congr (n := n + 2) (const_mul (n := n + 2) hf.2.2 hc) fun x hx => ?_
    have hd : DifferentiableAt ℝ f x := hf.2.1.differentiableAt (isOpen_Ioi.mem_nhds hx)
    simp only [deriv_const_mul c hd]
    ring

/-- A `d`-monotone function is nonincreasing on `(0, ∞)` for `d ≥ 1`. -/
theorem antitoneOn : ∀ {n : ℕ} {f : ℝ → ℝ}, IsMultiplyMonotone (n + 1) f → AntitoneOn f (Ioi 0)
  | 0, _, hf => hf.2
  | 1, _, hf => hf.2.1
  | n + 2, f, hf => by
    have hg := nonneg hf.2.2
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (hf.2.1.continuousOn) (by rw [interior_Ioi]; exact hf.2.1)
    intro x hx
    rw [interior_Ioi] at hx
    linarith [hg x hx]

end IsMultiplyMonotone

private theorem convex_corner {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) {x a b : ℝ} (hx : 0 < x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ f x - f (x + b) - f (x + a) + f (x + a + b) := by
  have hg : ConvexOn ℝ (Ici 0) (fun t => f (x + t)) := by
    refine ⟨convex_Ici 0, fun a ha b hb p q hp hq hpq => ?_⟩
    have ha' : x + a ∈ Ioi 0 := add_pos_of_pos_of_nonneg hx ha
    have hb' : x + b ∈ Ioi 0 := add_pos_of_pos_of_nonneg hx hb
    have h := hf.2 ha' hb' hp hq hpq
    have he : p • (x + a) + q • (x + b) = x + (p • a + q • b) := by
      simp only [smul_eq_mul]
      linear_combination x * hpq
    rw [he] at h
    simpa [smul_eq_mul] using h
  have := BivariateGenerator.convex_increment hg le_rfl le_rfl ha hb
  simp only [zero_add, add_zero] at this
  rw [show x + a + b = x + (a + b) by ring]
  linarith

/-- **Corner sums of `d`-monotone functions are nonnegative** (McNeil–Nešlehová 2009,
Theorem 2.2, analytic part; Williamson 1956): for `|s| ≤ d`, `x > 0` and `hᵢ ≥ 0`,
`∑_{t ⊆ s} (-1)^{|t|} ψ(x + ∑_{i ∈ t} hᵢ) ≥ 0`. -/
theorem IsMultiplyMonotone.cornerSum_nonneg {ι : Type*} [DecidableEq ι] :
    ∀ {n : ℕ} {f : ℝ → ℝ}, IsMultiplyMonotone n f → ∀ {h : ι → ℝ} {s : Finset ι},
      s.card ≤ n → ∀ {x : ℝ}, 0 < x → (∀ i ∈ s, 0 ≤ h i) → 0 ≤ cornerSum f x h s
  | n, f, hf, h, s, hs, x, hx, hh => by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0, cornerSum_empty]
      exact hf.nonneg x hx
    obtain ⟨j, s', hjs', rfl, -⟩ := Finset.card_eq_succ.mp (Nat.succ_pred_eq_of_pos hpos).symm
    rw [Finset.card_insert_of_notMem hjs'] at hs
    match n, f, hf with
    | 0, _, _ => omega
    | 1, f, hf =>
      have hs' : s' = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hs'
      rw [cornerSum_insert _ _ _ hjs', cornerSum_empty, cornerSum_empty, sub_nonneg]
      exact hf.2 hx (add_pos_of_pos_of_nonneg hx (hh j (Finset.mem_insert_self j _)))
        (le_add_of_nonneg_right (hh j (Finset.mem_insert_self j _)))
    | 2, f, hf =>
      rcases Nat.eq_zero_or_pos s'.card with h0 | hpos'
      · rw [Finset.card_eq_zero.mp h0, cornerSum_insert _ _ _ (Finset.notMem_empty j),
          cornerSum_empty, cornerSum_empty, sub_nonneg]
        exact hf.2.1 hx (add_pos_of_pos_of_nonneg hx (hh j (by simp)))
          (le_add_of_nonneg_right (hh j (by simp)))
      · obtain ⟨k, s'', hks'', rfl, -⟩ :=
          Finset.card_eq_succ.mp (Nat.succ_pred_eq_of_pos hpos').symm
        rw [Finset.card_insert_of_notMem hks''] at hs
        have hs'' : s'' = ∅ := Finset.card_eq_zero.mp (by omega)
        subst hs''
        have hjk : j ≠ k := fun hjk => hjs' (by simp [hjk])
        rw [insert_empty_eq, cornerSum_pair _ _ _ hjk]
        exact convex_corner hf.2.2 hx (hh j (by simp)) (hh k (by simp))
    | m + 3, f, hf =>
      have hcard' : s'.card ≤ m + 2 := by omega
      set A : ℝ → ℝ := fun y => cornerSum f y h s' with hA
      have hderiv : ∀ y, 0 < y →
          HasDerivAt A (cornerSum (fun z => deriv f z) y h s') y := by
        intro y hy
        apply hasDerivAt_cornerSum
        intro t ht
        have hpos := add_sum_pos hy (fun i hi => hh i (Finset.mem_insert_of_mem hi)) ht
        exact (hf.2.1.differentiableAt (isOpen_Ioi.mem_nhds hpos)).hasDerivAt
      have hanti : AntitoneOn A (Ioi 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
          (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
          (fun y hy => by
            rw [interior_Ioi] at hy
            exact (hderiv y hy).differentiableAt.differentiableWithinAt)
        intro y hy
        rw [interior_Ioi] at hy
        rw [(hderiv y hy).deriv]
        have hrec := IsMultiplyMonotone.cornerSum_nonneg hf.2.2 hcard' hy
          (fun i hi => hh i (Finset.mem_insert_of_mem hi))
        rw [cornerSum_neg] at hrec
        linarith
      rw [cornerSum_insert _ _ _ hjs', sub_nonneg]
      exact hanti hx (add_pos_of_pos_of_nonneg hx (hh j (Finset.mem_insert_self j _)))
        (le_add_of_nonneg_right (hh j (Finset.mem_insert_self j _)))

/-- **Corner sums at the boundary point `x = 0`**, for `ψ` continuous on `[0, ∞)`. -/
theorem IsMultiplyMonotone.cornerSum_nonneg_of_nonneg {ι : Type*} [DecidableEq ι] {n : ℕ}
    {f : ℝ → ℝ} (hf : IsMultiplyMonotone n f) (hc : ContinuousOn f (Ici 0)) {h : ι → ℝ}
    {s : Finset ι} (hs : s.card ≤ n) {x : ℝ} (hx : 0 ≤ x) (hh : ∀ i ∈ s, 0 ≤ h i) :
    0 ≤ cornerSum f x h s := by
  rcases hx.lt_or_eq with hx | rfl
  · exact hf.cornerSum_nonneg hs hx hh
  have hlim : Tendsto (fun y => cornerSum f y h s) (𝓝[>] 0) (𝓝 (cornerSum f 0 h s)) := by
    unfold cornerSum
    apply tendsto_finsetSum
    intro t ht
    apply Tendsto.const_mul
    have hc0 : ContinuousWithinAt f (Ici 0) (0 + ∑ i ∈ t, h i) :=
      hc _ (add_sum_nonneg le_rfl hh ht)
    have hmap : Tendsto (fun y : ℝ => y + ∑ i ∈ t, h i) (𝓝[>] 0)
        (𝓝[Ici 0] (0 + ∑ i ∈ t, h i)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact ((continuous_id.add continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact add_sum_nonneg (le_of_lt hy) hh ht
    exact hc0.tendsto.comp hmap
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hf.cornerSum_nonneg hs hy hh

/-! ### Power functions -/

private theorem hasDerivAt_one_add_rpow_neg (c α : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => c * (1 + t) ^ (-α)) (c * ((-α) * (1 + x) ^ (-α - 1))) x := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id x).const_add 1
  have h2 := h1.rpow_const (p := -α) (Or.inl (by linarith))
  simpa using h2.const_mul c

/-- **`c (1 + t)^{-α}` is `d`-monotone for every `d`** (`c ≥ 0`, `α > 0`); these functions are
completely monotone and generate the Clayton family. -/
theorem isMultiplyMonotone_one_add_rpow_neg : ∀ (n : ℕ) {c α : ℝ}, 0 ≤ c → 0 < α →
    IsMultiplyMonotone n (fun t => c * (1 + t) ^ (-α))
  | 0, c, α, hc, _ => fun x hx => mul_nonneg hc (Real.rpow_nonneg (by linarith) _)
  | 1, c, α, hc, hα => ⟨fun x hx => mul_nonneg hc (Real.rpow_nonneg (by linarith) _),
      fun x hx y _ hxy => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith [show (0 : ℝ) < x from hx]) (by linarith)
          (by linarith)) hc⟩
  | 2, c, α, hc, hα => by
    refine ⟨fun x hx => mul_nonneg hc (Real.rpow_nonneg (by linarith) _),
      fun x hx y _ hxy => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith [show (0 : ℝ) < x from hx]) (by linarith)
          (by linarith)) hc, ?_⟩
    apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
      (fun x hx => (hasDerivAt_one_add_rpow_neg c α hx).continuousAt.continuousWithinAt)
    · rw [interior_Ioi]
      exact fun x hx => (hasDerivAt_one_add_rpow_neg c α hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro x hx y hy hxy
      rw [(hasDerivAt_one_add_rpow_neg c α hx).deriv, (hasDerivAt_one_add_rpow_neg c α hy).deriv]
      have hx' : (0 : ℝ) < 1 + x := by linarith [show (0 : ℝ) < x from hx]
      have h := Real.rpow_le_rpow_of_nonpos hx' (by linarith : 1 + x ≤ 1 + y)
        (by linarith : -α - 1 ≤ 0)
      have : 0 ≤ c * α := mul_nonneg hc hα.le
      nlinarith
  | n + 3, c, α, hc, hα => by
    refine ⟨fun x hx => mul_nonneg hc (Real.rpow_nonneg (by linarith) _),
      fun x hx => (hasDerivAt_one_add_rpow_neg c α hx).differentiableAt.differentiableWithinAt, ?_⟩
    refine IsMultiplyMonotone.congr (n := n + 2)
      (isMultiplyMonotone_one_add_rpow_neg (n + 2) (c := c * α) (α := α + 1)
        (mul_nonneg hc hα.le) (by linarith)) fun x hx => ?_
    simp only [(hasDerivAt_one_add_rpow_neg c α hx).deriv]
    rw [show -α - 1 = -(α + 1) by ring]
    ring

end ProbabilityTheory.Copula
