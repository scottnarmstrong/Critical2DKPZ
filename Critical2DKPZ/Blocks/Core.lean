/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.TimeBlocks
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Definitions.BlockCount
public import Critical2DKPZ.Definitions.BlockTime
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.SmoothedEndpointDist
import Mathlib.Tactic
import Mathlib.Probability.Independence.Integration

/-!
# Finite block kernels and discrepancy expansions

The block interval `(t (i - 1), t i]` uses the polymer endpoint convention. The
definitions here are independent of the particular geometric grid; the paper's grid is obtained by
specializing `t` to `blockTime N ρ`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Blocks

/-- The block kernel is the point-to-point partition function on one time block. -/
def blockKernel (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (x y : Site) (ω : Disorder) : ℝ :=
  pointToPoint β (t (i - 1)) (t i - t (i - 1)) x y ω

/-- The block mass is the heat-start partition function in equation (7.3). -/
def blockMass (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (ω : Disorder) : ℝ :=
  smoothedP2Plane β (t (i - 1)) (t i) 0 ω

/-- The block discrepancy subtracts the outgoing mass times the walk kernel, as in equation (7.5). -/
def blockDiscrepancy (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (x y : Site) (ω : Disorder) : ℝ :=
  blockKernel β t i x y ω - pointToPlane β (t (i - 1)) (t i - t (i - 1)) x ω * srwKernel (t i) y

/-- The block ratio divides the heat-start mass by the product of individual block masses, as in equation (7.8). -/
def blockRatio (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) (ω : Disorder) : ℝ :=
  smoothedP2Plane β (t (r - 1)) (t s) 0 ω / ∏ i ∈ Finset.Icc r s, blockMass β t i ω

/-- `(D_u ∘ ⋯ ∘ D_{u+k-1})(x,y)`; the empty composition is the identity kernel. -/
def discrepancyString (β : ℝ) (t : ℕ → ℕ) (u : ℕ) : ℕ → Site → Site → Disorder → ℝ
  | 0, x, y, _ => if x = y then 1 else 0
  | k + 1, x, y, ω =>
      ∑' z, discrepancyString β t u k x z ω * blockDiscrepancy β t (u + k) z y ω

/-- A finite terminal support bound for one discrepancy kernel. -/
def blockDiscrepancySupport (t : ℕ → ℕ) (i : ℕ) (x : Site) : Finset Site :=
  Polymer.endpoints x (t i - t (i - 1)) ∪ Polymer.endpoints 0 (t i)

/-- A finite terminal support bound for a discrepancy string. -/
def discrepancyStringSupport (t : ℕ → ℕ) (u : ℕ) : ℕ → Site → Finset Site
  | 0, x => {x}
  | k + 1, x =>
      (discrepancyStringSupport t u k x).biUnion (fun z => blockDiscrepancySupport t (u + k) z)

/-- Incoming walk sites used by the closed discrepancy. -/
def closedStartSupport (t : ℕ → ℕ) (u : ℕ) : Finset Site :=
  Polymer.endpoints 0 (t (u - 1))

/-- All possible first discrepancy endpoints over the incoming support. -/
def closedFirstSupport (t : ℕ → ℕ) (u : ℕ) : Finset Site :=
  (closedStartSupport t u).biUnion (fun x => blockDiscrepancySupport t u x)

/-- All possible terminal sites of the discrepancy tail after the first block. -/
def closedTailSupport (t : ℕ → ℕ) (u k : ℕ) : Finset Site :=
  (closedFirstSupport t u).biUnion (fun z => discrepancyStringSupport t (u + 1) k z)

/-- The closed discrepancy pairs a discrepancy string with the incoming walk kernel and the terminal block mass. -/
def closedDiscrepancy (β : ℝ) (t : ℕ → ℕ) (u v : ℕ) (ω : Disorder) : ℝ :=
  ∑' x, ∑' y, srwKernel (t (u - 1)) x * discrepancyString β t u (v - u) x y ω *
    pointToPlane β (t (v - 1)) (t v - t (v - 1)) y ω

/-- The open discrepancy mass pairs a discrepancy string with the incoming walk kernel and the remaining partition function. -/
def openDiscrepancyMass (β : ℝ) (t : ℕ → ℕ) (T u v : ℕ) (ω : Disorder) : ℝ :=
  ∑' x, ∑' y, srwKernel (t (u - 1)) x * discrepancyString β t u (v - u) x y ω *
    pointToPlane β (t (v - 1)) (T - t (v - 1)) y ω

/-- The unnormalized open discrepancy profile. -/
def openCorrectorNumerator (β : ℝ) (t : ℕ → ℕ) (u s : ℕ)
    (ω : Disorder) (y : Site) : ℝ :=
  ∑' x, srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω

/-- The open corrector is the normalized discrepancy-string profile in equation (7.49). -/
def openCorrector (β : ℝ) (t : ℕ → ℕ) (u s : ℕ) (ω : Disorder) (y : Site) : ℝ :=
  openCorrectorNumerator β t u s ω y / ∏ i ∈ Finset.Icc u s, blockMass β t i ω

/-- The unnormalized endpoint profile on a block range. -/
def blockEndpointNumerator (β : ℝ) (t : ℕ → ℕ) (r s : ℕ)
    (ω : Disorder) (y : Site) : ℝ :=
  ∑' x, srwKernel (t (r - 1)) x *
    pointToPoint β (t (r - 1)) (t s - t (r - 1)) x y ω

/-- A finite reachable support bound for a block endpoint profile. -/
def blockEndpointSupport (t : ℕ → ℕ) (r s : ℕ) : Finset Site :=
  (Polymer.endpoints 0 (t (r - 1))).biUnion
    (fun x => Polymer.endpoints x (t s - t (r - 1)))

/-- `𝔍(r,s)`: disjoint integer intervals `[u,v] ⊆ [r,s]` with `u < v`; adjacent intervals are
allowed. -/
def intervalFamilies (r s : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((Finset.Icc r s ×ˢ Finset.Icc r s).filter (fun I => I.1 < I.2)).powerset.filter
    (fun F => ∀ I ∈ F, ∀ J ∈ F, I ≠ J → I.2 < J.1 ∨ J.2 < I.1)

/-- The block good event bounds each block mass within one half of unity, as in equation (7.9). -/
def blockGoodSet (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) : Set Disorder :=
  {ω | ∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2}

/-- The grid block count is the integer part of `|log δ| / (2 log ρ)`, as in Remark 7.2. -/
def gridBlocks (δ ρ : ℝ) : ℕ := ⌊|Real.log δ| / (2 * Real.log ρ)⌋₊

/-- `ρ̃ = δ^{-1/(2J̃)}`, the adjusted grid ratio. -/
def gridRatio (δ ρ : ℝ) : ℝ := δ ^ (-(1 : ℝ) / (2 * gridBlocks δ ρ))

/-- The block discrepancy has zero total mass in its terminal coordinate. -/
theorem tsum_blockDiscrepancy (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (x : Site) (ω : Disorder) :
    ∑' y, blockDiscrepancy β t i x y ω = 0 := by
  let a := t (i - 1)
  let n := t i - t (i - 1)
  have hpoint : Summable (fun y : Site => pointToPoint β a n x y ω) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints x n)
    intro y hy
    exact Polymer.pointToPoint_eq_zero_of_not_mem β a n x y ω hy
  have hkernel : Summable (fun y : Site => srwKernel (t i) y) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 (t i))
    intro y hy
    simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem (t i) 0 y hy
  unfold blockDiscrepancy blockKernel
  rw [hpoint.tsum_sub (hkernel.mul_left (pointToPlane β a n x ω)),
    Polymer.tsum_pointToPoint, tsum_mul_left]
  have hprob : ∑' y : Site, srwKernel (t i) y = 1 := by
    simpa only [sub_zero] using Polymer.tsum_srwKernel (t i) 0
  rw [hprob]
  ring

/-- A discrepancy kernel vanishes outside the union of its two finite endpoint supports. -/
theorem blockDiscrepancy_eq_zero_of_not_mem_support (β : ℝ) (t : ℕ → ℕ) (i : ℕ)
    (x y : Site) (ω : Disorder) (hy : y ∉ blockDiscrepancySupport t i x) :
    blockDiscrepancy β t i x y ω = 0 := by
  have hy' : y ∉ Polymer.endpoints x (t i - t (i - 1)) := by
    intro h
    exact hy (Finset.mem_union_left _ h)
  have hy'' : y ∉ Polymer.endpoints 0 (t i) := by
    intro h
    exact hy (Finset.mem_union_right _ h)
  unfold blockDiscrepancy blockKernel
  have hpoint := Polymer.pointToPoint_eq_zero_of_not_mem β (t (i - 1))
    (t i - t (i - 1)) x y ω hy'
  have hkernel : srwKernel (t i) y = 0 := by
    simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem (t i) 0 y hy''
  rw [hpoint, hkernel, mul_zero, sub_zero]

/-- A discrepancy string vanishes outside its recursively defined finite support. -/
theorem discrepancyString_eq_zero_of_not_mem_support (β : ℝ) (t : ℕ → ℕ) (u k : ℕ)
    (x y : Site) (ω : Disorder) (hy : y ∉ discrepancyStringSupport t u k x) :
    discrepancyString β t u k x y ω = 0 := by
  revert x y ω hy
  induction k with
  | zero =>
      intro x y ω hy
      simp only [discrepancyStringSupport, Finset.mem_singleton] at hy
      have hxy : x ≠ y := fun h => hy h.symm
      simp [discrepancyString, hxy]
  | succ k ih =>
      intro x y ω hy
      change y ∉ (discrepancyStringSupport t u k x).biUnion
        (fun z => blockDiscrepancySupport t (u + k) z) at hy
      change (∑' z, discrepancyString β t u k x z ω *
        blockDiscrepancy β t (u + k) z y ω) = _
      calc
        _ = ∑' z, (0 : ℝ) := tsum_congr fun z => by
          by_cases hz : z ∈ discrepancyStringSupport t u k x
          · have hyz : y ∉ blockDiscrepancySupport t (u + k) z := by
              intro hmem
              exact hy (Finset.mem_biUnion.2 ⟨z, hz, hmem⟩)
            rw [blockDiscrepancy_eq_zero_of_not_mem_support β t (u + k) z y ω hyz, mul_zero]
          · rw [ih x z ω hz, zero_mul]
        _ = 0 := tsum_zero

/-- The string can be expanded from its first discrepancy kernel as well as its last. -/
theorem discrepancyString_leftFactor (β : ℝ) (t : ℕ → ℕ) (u k : ℕ)
    (x y : Site) (ω : Disorder) :
    discrepancyString β t u (k + 1) x y ω =
      ∑' z, blockDiscrepancy β t u x z ω * discrepancyString β t (u + 1) k z y ω := by
  induction k generalizing x y with
  | zero =>
      change (∑' z, (if x = z then 1 else 0) *
          blockDiscrepancy β t u z y ω) =
        ∑' z, blockDiscrepancy β t u x z ω * (if z = y then 1 else 0)
      calc
        _ = blockDiscrepancy β t u x y ω := by
          rw [tsum_eq_single x]
          · simp
          · intro z hz
            by_cases h : x = z
            · exact (hz h.symm).elim
            · simp [h]
        _ = _ := by
          rw [tsum_eq_single y]
          · simp
          · intro z hz
            simp [hz]
  | succ k ih =>
      have hdouble : Summable (fun p : Site × Site =>
          (blockDiscrepancy β t u x p.1 ω *
            discrepancyString β t (u + 1) k p.1 p.2 ω) *
              blockDiscrepancy β t (u + k + 1) p.2 y ω) := by
        let sz := blockDiscrepancySupport t u x
        let sw := sz.biUnion (fun z => discrepancyStringSupport t (u + 1) k z)
        apply summable_of_ne_finset_zero (s := sz ×ˢ sw)
        intro p hp
        by_cases hpz : p.1 ∈ sz
        · by_cases hpw : p.2 ∈ sw
          · exact (hp (Finset.mem_product.mpr ⟨hpz, hpw⟩)).elim
          · have hpwz : p.2 ∉ discrepancyStringSupport t (u + 1) k p.1 := by
              intro hmem
              exact hpw (Finset.mem_biUnion.2 ⟨p.1, hpz, hmem⟩)
            rw [discrepancyString_eq_zero_of_not_mem_support β t (u + 1) k
              p.1 p.2 ω hpwz, mul_zero, zero_mul]
        · rw [blockDiscrepancy_eq_zero_of_not_mem_support β t u x p.1 ω hpz,
            zero_mul, zero_mul]
      calc
        _ = ∑' w, ∑' z, (blockDiscrepancy β t u x z ω *
              discrepancyString β t (u + 1) k z w ω) *
                blockDiscrepancy β t (u + k + 1) w y ω := by
          apply tsum_congr
          intro w
          have hadd : u + (k + 1) = u + k + 1 := by omega
          rw [ih x w, tsum_mul_right, hadd]
        _ = ∑' z, ∑' w, (blockDiscrepancy β t u x z ω *
              discrepancyString β t (u + 1) k z w ω) *
                blockDiscrepancy β t (u + k + 1) w y ω :=
          Summable.tsum_comm (f := fun z w =>
            (blockDiscrepancy β t u x z ω *
              discrepancyString β t (u + 1) k z w ω) *
                blockDiscrepancy β t (u + k + 1) w y ω) hdouble
        _ = ∑' z, blockDiscrepancy β t u x z ω *
              discrepancyString β t (u + 1) (k + 1) z y ω := by
          apply tsum_congr
          intro z
          rw [discrepancyString]
          rw [← tsum_mul_left]
          apply tsum_congr
          intro w
          ring_nf

/-- Finite first-block expansion of a closed discrepancy. -/
theorem closedDiscrepancy_eq_finiteSum_firstFactor (β : ℝ) (t : ℕ → ℕ)
    (u k : ℕ) (ω : Disorder) :
    closedDiscrepancy β t u (u + k + 1) ω =
      ∑ x ∈ closedStartSupport t u, ∑ z ∈ closedFirstSupport t u,
        ∑ y ∈ closedTailSupport t u k,
          srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
            discrepancyString β t (u + 1) k z y ω *
              pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω := by
  classical
  let sx := closedStartSupport t u
  let sz := closedFirstSupport t u
  let sy := closedTailSupport t u k
  have hlen : (u + k + 1) - u = k + 1 := by omega
  have htime : (u + k + 1) - 1 = u + k := by omega
  have hinner (x : Site) (hx : x ∈ sx) :
      ∑' y, srwKernel (t (u - 1)) x *
          discrepancyString β t u (k + 1) x y ω *
            pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω =
        ∑ z ∈ sz, ∑ y ∈ sy,
          srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
            discrepancyString β t (u + 1) k z y ω *
              pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω := by
    have hxStart : x ∈ closedStartSupport t u := by simpa [sx] using hx
    let f : Site → Site → ℝ := fun z y =>
      srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
        discrepancyString β t (u + 1) k z y ω *
          pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω
    have hdouble : Summable (Function.uncurry f) := by
      apply summable_of_ne_finset_zero (s := sz ×ˢ sy)
      intro p hp
      by_cases hpz : p.1 ∈ sz
      · by_cases hpy : p.2 ∈ sy
        · exact (hp (Finset.mem_product.mpr ⟨hpz, hpy⟩)).elim
        · have hpTail : p.2 ∉ discrepancyStringSupport t (u + 1) k p.1 := by
            intro hmem
            exact hpy (Finset.mem_biUnion.2 ⟨p.1, hpz, hmem⟩)
          change f p.1 p.2 = 0
          simp [f, discrepancyString_eq_zero_of_not_mem_support β t (u + 1) k
            p.1 p.2 ω hpTail]
      · have hpD : p.1 ∉ blockDiscrepancySupport t u x := by
          intro hmem
          exact hpz (Finset.mem_biUnion.2 ⟨x, hxStart, hmem⟩)
        change f p.1 p.2 = 0
        simp [f, blockDiscrepancy_eq_zero_of_not_mem_support β t u x p.1 ω hpD]
    have hfactor :
        ∑' y, srwKernel (t (u - 1)) x *
            discrepancyString β t u (k + 1) x y ω *
              pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω =
          ∑' y, ∑' z, f z y := by
      apply tsum_congr
      intro y
      rw [discrepancyString_leftFactor]
      calc
        _ = (∑' z, srwKernel (t (u - 1)) x *
              (blockDiscrepancy β t u x z ω *
                discrepancyString β t (u + 1) k z y ω)) *
                pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω := by
          rw [← tsum_mul_left]
        _ = ∑' z, f z y := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro z
          dsimp [f]
          ring
    have hswap : ∑' y, ∑' z, f z y = ∑' z, ∑' y, f z y :=
      Summable.tsum_comm (f := f) hdouble
    have hfinite : ∑' z, ∑' y, f z y = ∑ z ∈ sz, ∑ y ∈ sy, f z y := by
      have hinnerFinite (z : Site) : ∑' y, f z y = ∑ y ∈ sy, f z y := by
        apply tsum_eq_sum
        intro y hy
        by_cases hz : z ∈ sz
        · have hyz : y ∉ discrepancyStringSupport t (u + 1) k z := by
            intro hmem
            exact hy (Finset.mem_biUnion.2 ⟨z, hz, hmem⟩)
          simp [f, discrepancyString_eq_zero_of_not_mem_support β t (u + 1) k
            z y ω hyz]
        · have hD : blockDiscrepancy β t u x z ω = 0 := by
            have hDsupport : z ∉ blockDiscrepancySupport t u x := by
              intro hmem
              exact hz (Finset.mem_biUnion.2 ⟨x, hxStart, hmem⟩)
            exact blockDiscrepancy_eq_zero_of_not_mem_support β t u x z ω hDsupport
          simp [f, hD]
      rw [tsum_congr hinnerFinite]
      apply tsum_eq_sum
      intro z hz
      have hDsupport : z ∉ blockDiscrepancySupport t u x := by
        intro hmem
        exact hz (Finset.mem_biUnion.2 ⟨x, hxStart, hmem⟩)
      have hD := blockDiscrepancy_eq_zero_of_not_mem_support β t u x z ω hDsupport
      simp [f, hD]
    calc
      _ = ∑' y, ∑' z, f z y := hfactor
      _ = ∑' z, ∑' y, f z y := hswap
      _ = _ := hfinite
  have hout :
      ∑' x, ∑' y, srwKernel (t (u - 1)) x *
          discrepancyString β t u (k + 1) x y ω *
            pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω =
        ∑ x ∈ sx, ∑ z ∈ sz, ∑ y ∈ sy,
          srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
            discrepancyString β t (u + 1) k z y ω *
              pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω := by
    have houter : ∑' x, ∑' y, srwKernel (t (u - 1)) x *
        discrepancyString β t u (k + 1) x y ω *
          pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω =
        ∑ x ∈ sx, ∑' y, srwKernel (t (u - 1)) x *
          discrepancyString β t u (k + 1) x y ω *
            pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω := by
      apply tsum_eq_sum
      intro x hx
      have hx0 : srwKernel (t (u - 1)) x = 0 := by
        simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem
          (t (u - 1)) 0 x hx
      simp [hx0]
    rw [houter]
    apply Finset.sum_congr rfl
    intro x hx
    exact hinner x hx
  unfold closedDiscrepancy
  rw [hlen, htime]
  exact hout



/-- Averaging a block discrepancy against the incoming heat profile gives zero. -/
theorem heatStart_integral_blockDiscrepancy (β : ℝ) (t : ℕ → ℕ) (u : ℕ)
    (ht : t (u - 1) ≤ t u) (y : Site) :
    ∑' x, srwKernel (t (u - 1)) x *
      ∫ ω, blockDiscrepancy β t u x y ω ∂disorderLaw = 0 := by
  let a := t (u - 1)
  let d := t u - t (u - 1)
  have hpoint (x : Site) :
      ∫ ω, blockDiscrepancy β t u x y ω ∂disorderLaw =
        srwKernel d (y - x) - srwKernel (t u) y := by
    unfold blockDiscrepancy blockKernel
    rw [integral_sub (Polymer.integrable_pointToPoint β a d x y)
      ((Polymer.integrable_pointToPlane β a d x).mul_const (srwKernel (t u) y)),
      integral_mul_const, Polymer.integral_pointToPoint,
      Polymer.integral_pointToPlane]
    ring
  have hs1 : Summable (fun x : Site => srwKernel a x * srwKernel d (y - x)) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 a)
    intro x hx
    have hx0 : srwKernel a x = 0 := by
      simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
    rw [hx0, zero_mul]
  have hs2 : Summable (fun x : Site => srwKernel a x * srwKernel (t u) y) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 a)
    intro x hx
    have hx0 : srwKernel a x = 0 := by
      simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
    rw [hx0, zero_mul]
  have hconv : ∑' x, srwKernel a x * srwKernel d (y - x) = srwKernel (t u) y := by
    have h := Polymer.srwKernel_convolution a d 0 y
    have hadd : a + d = t u := by dsimp [a, d]; omega
    rw [hadd] at h
    simpa only [sub_zero] using h.symm
  have hprob : ∑' x : Site, srwKernel a x = 1 := by
    simpa only [sub_zero] using Polymer.tsum_srwKernel a 0
  simp_rw [hpoint]
  calc
    ∑' x, srwKernel a x * (srwKernel d (y - x) - srwKernel (t u) y) =
        ∑' x, (srwKernel a x * srwKernel d (y - x) -
          srwKernel a x * srwKernel (t u) y) := by
            congr 1
            funext x
            ring
    _ = (∑' x, srwKernel a x * srwKernel d (y - x)) -
        ∑' x, srwKernel a x * srwKernel (t u) y := hs1.tsum_sub hs2
    _ = srwKernel (t u) y - srwKernel (t u) y := by
      rw [hconv, tsum_mul_right, hprob]
      ring
    _ = 0 := sub_self _

/-- A block has positive mass, including when its time interval is empty. -/
theorem blockMass_pos (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (ω : Disorder) :
    0 < blockMass β t i ω := by
  exact Polymer.smoothedP2Plane_pos β (t (i - 1)) (t i) 0 ω

/-- At equal times, the smoothed point-to-plane mass is one. -/
theorem smoothedP2Plane_eq_one_of_eq (β : ℝ) (n : ℕ) (ω : Disorder) :
    smoothedP2Plane β n n 0 ω = 1 := by
  rw [Polymer.smoothedP2Plane_eq_sum]
  simp only [Nat.sub_self, Polymer.pointToPlane_zero, mul_one]
  exact Polymer.sum_srwKernel_endpoints n 0

/-- The empty block ratio is one. -/
theorem blockRatio_empty (β : ℝ) (t : ℕ → ℕ) (r : ℕ) (hr : 1 ≤ r) (ω : Disorder) :
    blockRatio β t r (r - 1) ω = 1 := by
  have hlt : r - 1 < r := by omega
  unfold blockRatio
  rw [Finset.Icc_eq_empty_of_lt hlt, Finset.prod_empty, div_one]
  exact smoothedP2Plane_eq_one_of_eq β (t (r - 1)) ω

/-- The ratio of a single block is one. -/
theorem blockRatio_self (β : ℝ) (t : ℕ → ℕ) (r : ℕ) (ω : Disorder) :
    blockRatio β t r r ω = 1 := by
  unfold blockRatio blockMass
  simp only [Finset.Icc_self, Finset.prod_singleton]
  exact div_self (ne_of_gt (Polymer.smoothedP2Plane_pos β
    (t (r - 1)) (t r) 0 ω))

/-- Appending one polymer block composes the unnormalized endpoint profile. -/
theorem blockEndpointNumerator_append (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hrs : r ≤ s) (ω : Disorder) (y : Site) :
    blockEndpointNumerator β t r (s + 1) ω y =
      ∑' z, blockEndpointNumerator β t r s ω z *
        blockKernel β t (s + 1) z y ω := by
  let a := t (r - 1)
  let n := t s - t (r - 1)
  let m := t (s + 1) - t s
  let sx := Polymer.endpoints 0 a
  let sz := sx.biUnion (fun x => Polymer.endpoints x n)
  have hrprev : r - 1 ≤ s := by omega
  have hprev : t (r - 1) ≤ t s := ht hrprev
  have hnext : t s ≤ t (s + 1) := ht (Nat.le_succ s)
  have hadd : a + n = t s := by dsimp [a, n]; omega
  have htotal : t (s + 1) - a = n + m := by dsimp [a, n, m]; omega
  have hCK (x : Site) :
      pointToPoint β a (t (s + 1) - a) x y ω =
        ∑' z, pointToPoint β a n x z ω *
          pointToPoint β (t s) m z y ω := by
    have h := Polymer.pointToPoint_chapmanKolmogorov β a n m x y ω
    rw [← htotal, hadd] at h
    exact h
  have hdouble : Summable (fun p : Site × Site =>
      srwKernel a p.1 *
        (pointToPoint β a n p.1 p.2 ω * pointToPoint β (t s) m p.2 y ω)) := by
    apply summable_of_ne_finset_zero (s := sx ×ˢ sz)
    intro p hp
    by_cases hx : p.1 ∈ sx
    · by_cases hz : p.2 ∈ sz
      · exact (hp (Finset.mem_product.mpr ⟨hx, hz⟩)).elim
      · have hz' : p.2 ∉ Polymer.endpoints p.1 n := by
          intro hmem
          exact hz (Finset.mem_biUnion.2 ⟨p.1, hx, hmem⟩)
        rw [Polymer.pointToPoint_eq_zero_of_not_mem β a n p.1 p.2 ω hz']
        simp
    · have hx0 : srwKernel a p.1 = 0 := by
        simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem a 0 p.1 hx
      rw [hx0]
      simp
  calc
    _ = ∑' x, ∑' z, srwKernel a x *
          (pointToPoint β a n x z ω * pointToPoint β (t s) m z y ω) := by
      unfold blockEndpointNumerator
      apply tsum_congr
      intro x
      rw [hCK x]
      rw [← tsum_mul_left]
    _ = ∑' z, ∑' x, srwKernel a x *
          (pointToPoint β a n x z ω * pointToPoint β (t s) m z y ω) :=
        (Summable.tsum_comm (f := fun x z => srwKernel a x *
          (pointToPoint β a n x z ω * pointToPoint β (t s) m z y ω)) hdouble
          ).symm
    _ = ∑' z, (∑' x, srwKernel a x * pointToPoint β a n x z ω) *
          pointToPoint β (t s) m z y ω := by
      apply tsum_congr
      intro z
      calc
        _ = ∑' x, (srwKernel a x * pointToPoint β a n x z ω) *
              pointToPoint β (t s) m z y ω := by
          apply tsum_congr
          intro x
          ring
        _ = _ := by rw [← tsum_mul_right]
    _ = ∑' z, blockEndpointNumerator β t r s ω z *
          blockKernel β t (s + 1) z y ω := by
      apply tsum_congr
      intro z
      have hleft : (∑' x, srwKernel a x * pointToPoint β a n x z ω) =
          blockEndpointNumerator β t r s ω z := by
        rfl
      rw [hleft]
      dsimp [blockKernel, m]

/-- Summing the unnormalized endpoint profile gives the smoothed partition function. -/
theorem tsum_blockEndpointNumerator (β : ℝ) (t : ℕ → ℕ) (r s : ℕ)
    (ω : Disorder) :
    ∑' y, blockEndpointNumerator β t r s ω y =
      smoothedP2Plane β (t (r - 1)) (t s) 0 ω := by
  let a := t (r - 1)
  let n := t s - a
  let sx := Polymer.endpoints 0 a
  let sy := sx.biUnion (fun x => Polymer.endpoints x n)
  have hdouble : Summable (fun p : Site × Site =>
      srwKernel a p.1 * pointToPoint β a n p.1 p.2 ω) := by
    apply summable_of_ne_finset_zero (s := sx ×ˢ sy)
    intro p hp
    by_cases hx : p.1 ∈ sx
    · by_cases hy : p.2 ∈ sy
      · exact (hp (Finset.mem_product.mpr ⟨hx, hy⟩)).elim
      · have hy' : p.2 ∉ Polymer.endpoints p.1 n := by
          intro hmem
          exact hy (Finset.mem_biUnion.2 ⟨p.1, hx, hmem⟩)
        rw [Polymer.pointToPoint_eq_zero_of_not_mem β a n p.1 p.2 ω hy']
        simp
    · have hx0 : srwKernel a p.1 = 0 := by
        simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem a 0 p.1 hx
      rw [hx0]
      simp
  calc
    _ = ∑' x, ∑' y, srwKernel a x * pointToPoint β a n x y ω :=
        Summable.tsum_comm (f := fun x y => srwKernel a x *
          pointToPoint β a n x y ω) hdouble
    _ = ∑' x, srwKernel a x * pointToPlane β a n x ω := by
      apply tsum_congr
      intro x
      calc
        _ = srwKernel a x * ∑' y, pointToPoint β a n x y ω := tsum_mul_left
        _ = srwKernel a x * pointToPlane β a n x ω := by
          rw [Polymer.tsum_pointToPoint]
    _ = smoothedP2Plane β (t (r - 1)) (t s) 0 ω := by
      unfold smoothedP2Plane
      simp only [a, n, sub_zero]

/-- The endpoint profile vanishes outside its finite reachable support. -/
theorem blockEndpointNumerator_eq_zero_of_not_mem_support (β : ℝ) (t : ℕ → ℕ)
    (r s : ℕ) (ω : Disorder) (y : Site)
    (hy : y ∉ blockEndpointSupport t r s) :
    blockEndpointNumerator β t r s ω y = 0 := by
  unfold blockEndpointNumerator
  calc
    _ = ∑' x, (0 : ℝ) := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ Polymer.endpoints 0 (t (r - 1))
      · have hyx : y ∉ Polymer.endpoints x (t s - t (r - 1)) := by
          intro hmem
          exact hy (Finset.mem_biUnion.2 ⟨x, hx, hmem⟩)
        rw [Polymer.pointToPoint_eq_zero_of_not_mem β (t (r - 1))
          (t s - t (r - 1)) x y ω hyx]
        ring
      · have hx0 : srwKernel (t (r - 1)) x = 0 := by
          simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem
            (t (r - 1)) 0 x hx
        rw [hx0]
        simp
    _ = 0 := tsum_zero

/-- Pairing the endpoint numerator with the next block mass gives the extended smoothed mass. -/
theorem blockEndpointNumerator_resetCoeff (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hrs : r ≤ s) (ω : Disorder) :
    smoothedP2Plane β (t (r - 1)) (t (s + 1)) 0 ω =
      ∑' z, blockEndpointNumerator β t r s ω z *
        pointToPlane β (t s) (t (s + 1) - t s) z ω := by
  let m := t (s + 1) - t s
  let sz := blockEndpointSupport t r s
  let sy := sz.biUnion (fun z => Polymer.endpoints z m)
  have hdouble : Summable (fun p : Site × Site =>
      blockEndpointNumerator β t r s ω p.1 *
        pointToPoint β (t s) m p.1 p.2 ω) := by
    apply summable_of_ne_finset_zero (s := sz ×ˢ sy)
    intro p hp
    by_cases hz : p.1 ∈ sz
    · by_cases hy : p.2 ∈ sy
      · exact (hp (Finset.mem_product.mpr ⟨hz, hy⟩)).elim
      · have hy' : p.2 ∉ Polymer.endpoints p.1 m := by
          intro hmem
          exact hy (Finset.mem_biUnion.2 ⟨p.1, hz, hmem⟩)
        rw [Polymer.pointToPoint_eq_zero_of_not_mem β (t s) m p.1 p.2 ω hy']
        simp
    · rw [blockEndpointNumerator_eq_zero_of_not_mem_support β t r s ω p.1 hz]
      simp
  calc
    _ = ∑' y, blockEndpointNumerator β t r (s + 1) ω y := by
      symm
      exact tsum_blockEndpointNumerator β t r (s + 1) ω
    _ = ∑' y, ∑' z, blockEndpointNumerator β t r s ω z *
          blockKernel β t (s + 1) z y ω := by
      apply tsum_congr
      intro y
      rw [blockEndpointNumerator_append β t ht r s hrs ω y]
    _ = ∑' y, ∑' z, blockEndpointNumerator β t r s ω z *
          pointToPoint β (t s) m z y ω := by
      apply tsum_congr
      intro y
      apply tsum_congr
      intro z
      dsimp [blockKernel, m]
    _ = ∑' z, ∑' y, blockEndpointNumerator β t r s ω z *
          pointToPoint β (t s) m z y ω :=
        Summable.tsum_comm (f := fun z y =>
          blockEndpointNumerator β t r s ω z * pointToPoint β (t s) m z y ω) hdouble
    _ = ∑' z, blockEndpointNumerator β t r s ω z *
          pointToPlane β (t s) m z ω := by
      apply tsum_congr
      intro z
      calc
        _ = blockEndpointNumerator β t r s ω z *
              ∑' y, pointToPoint β (t s) m z y ω := by rw [tsum_mul_left]
        _ = blockEndpointNumerator β t r s ω z *
              pointToPlane β (t s) m z ω := by rw [Polymer.tsum_pointToPoint]
        _ = _ := by rfl

/-- Appending a block splits the endpoint profile into its heat reset and discrepancy. -/
theorem blockEndpointNumerator_discrepancyRecurrence (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hrs : r ≤ s) (ω : Disorder) (y : Site) :
    blockEndpointNumerator β t r (s + 1) ω y =
      smoothedP2Plane β (t (r - 1)) (t (s + 1)) 0 ω * srwKernel (t (s + 1)) y +
        ∑' z, blockEndpointNumerator β t r s ω z *
          blockDiscrepancy β t (s + 1) z y ω := by
  let sz := blockEndpointSupport t r s
  let d : Site → ℝ := fun z => blockDiscrepancy β t (s + 1) z y ω
  let p : Site → ℝ := fun z =>
    pointToPlane β (t s) (t (s + 1) - t s) z ω * srwKernel (t (s + 1)) y
  have hD : Summable (fun z : Site => blockEndpointNumerator β t r s ω z * d z) := by
    apply summable_of_ne_finset_zero (s := sz)
    intro z hz
    rw [blockEndpointNumerator_eq_zero_of_not_mem_support β t r s ω z hz]
    simp
  have hP : Summable (fun z : Site => blockEndpointNumerator β t r s ω z * p z) := by
    apply summable_of_ne_finset_zero (s := sz)
    intro z hz
    rw [blockEndpointNumerator_eq_zero_of_not_mem_support β t r s ω z hz]
    simp
  calc
    _ = ∑' z, (blockEndpointNumerator β t r s ω z * d z +
          blockEndpointNumerator β t r s ω z * p z) := by
      rw [blockEndpointNumerator_append β t ht r s hrs ω y]
      apply tsum_congr
      intro z
      dsimp [d, p, blockKernel, blockDiscrepancy]
      ring
    _ = (∑' z, blockEndpointNumerator β t r s ω z * d z) +
          ∑' z, blockEndpointNumerator β t r s ω z * p z := hD.tsum_add hP
    _ = (∑' z, blockEndpointNumerator β t r s ω z * d z) +
          (∑' z, blockEndpointNumerator β t r s ω z *
            pointToPlane β (t s) (t (s + 1) - t s) z ω) *
              srwKernel (t (s + 1)) y := by
      congr 1
      calc
        _ = ∑' z, (blockEndpointNumerator β t r s ω z *
              pointToPlane β (t s) (t (s + 1) - t s) z ω) *
                srwKernel (t (s + 1)) y := by
          apply tsum_congr
          intro z
          dsimp [p]
          ring
        _ = _ := by rw [tsum_mul_right]
    _ = _ := by
      rw [blockEndpointNumerator_resetCoeff β t ht r s hrs ω]
      dsimp [d]
      ring

/-- The open-corrector numerator evolves by convolution with the next discrepancy kernel. -/
theorem openCorrectorNumerator_append (β : ℝ) (t : ℕ → ℕ) (u s : ℕ)
    (hus : u ≤ s) (ω : Disorder) (y : Site) :
    openCorrectorNumerator β t u (s + 1) ω y =
      ∑' z, openCorrectorNumerator β t u s ω z *
        blockDiscrepancy β t (s + 1) z y ω := by
  let k := s + 1 - u
  let a := t (u - 1)
  let sx := Polymer.endpoints 0 a
  let sz := sx.biUnion (fun x => discrepancyStringSupport t u k x)
  have hlen : s + 1 + 1 - u = k + 1 := by dsimp [k]; omega
  have hidx : u + k = s + 1 := by dsimp [k]; omega
  have hdouble : Summable (fun p : Site × Site =>
      srwKernel a p.1 *
        (discrepancyString β t u k p.1 p.2 ω *
          blockDiscrepancy β t (s + 1) p.2 y ω)) := by
    apply summable_of_ne_finset_zero (s := sx ×ˢ sz)
    intro p hp
    by_cases hx : p.1 ∈ sx
    · by_cases hz : p.2 ∈ sz
      · exact (hp (Finset.mem_product.mpr ⟨hx, hz⟩)).elim
      · have hz' : p.2 ∉ discrepancyStringSupport t u k p.1 := by
          intro hmem
          exact hz (Finset.mem_biUnion.2 ⟨p.1, hx, hmem⟩)
        rw [discrepancyString_eq_zero_of_not_mem_support β t u k p.1 p.2 ω hz']
        simp
    · have hx0 : srwKernel a p.1 = 0 := by
        simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem a 0 p.1 hx
      rw [hx0]
      simp
  calc
    _ = ∑' x, ∑' z, srwKernel a x *
          (discrepancyString β t u k x z ω *
            blockDiscrepancy β t (s + 1) z y ω) := by
      unfold openCorrectorNumerator
      apply tsum_congr
      intro x
      rw [hlen, discrepancyString, hidx, ← tsum_mul_left]
    _ = ∑' z, ∑' x, srwKernel a x *
          (discrepancyString β t u k x z ω *
            blockDiscrepancy β t (s + 1) z y ω) :=
        (Summable.tsum_comm (f := fun x z => srwKernel a x *
          (discrepancyString β t u k x z ω *
            blockDiscrepancy β t (s + 1) z y ω)) hdouble).symm
    _ = ∑' z, (∑' x, srwKernel a x * discrepancyString β t u k x z ω) *
          blockDiscrepancy β t (s + 1) z y ω := by
      apply tsum_congr
      intro z
      calc
        _ = ∑' x, (srwKernel a x * discrepancyString β t u k x z ω) *
              blockDiscrepancy β t (s + 1) z y ω := by
          apply tsum_congr
          intro x
          ring
        _ = _ := by rw [← tsum_mul_right]
    _ = ∑' z, openCorrectorNumerator β t u s ω z *
          blockDiscrepancy β t (s + 1) z y ω := by
      apply tsum_congr
      intro z
      rfl

/-- A discrepancy string of length one is its single block kernel. -/
theorem discrepancyString_one (β : ℝ) (t : ℕ → ℕ) (u : ℕ)
    (x y : Site) (ω : Disorder) :
    discrepancyString β t u 1 x y ω = blockDiscrepancy β t u x y ω := by
  change (∑' z, (if x = z then (1 : ℝ) else 0) *
    blockDiscrepancy β t u z y ω) = _
  rw [tsum_eq_single x]
  · simp
  · intro z hz
    simp [hz.symm]

/-- For a single block, the smoothed endpoint distribution is the walk kernel plus the open corrector. -/
theorem smoothedEndpointDist_singleBlock_expansion (β : ℝ) (t : ℕ → ℕ) (u : ℕ)
    (ω : Disorder) (y : Site) :
    smoothedEndpointDist β (t (u - 1)) (t u) 0 ω y =
      srwKernel (t u) y + openCorrector β t u u ω y := by
  let a := t (u - 1)
  let b := t u
  let q : Site → ℝ := fun x => srwKernel a x
  let d : Site → ℝ := fun x => blockDiscrepancy β t u x y ω
  let p : Site → ℝ := fun x => pointToPlane β a (b - a) x ω
  have hfinite (f : Site → ℝ) : Summable (fun x : Site => q x * f x) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 a)
    intro x hx
    have hx0 : q x = 0 := by
      dsimp [q]
      simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
    rw [hx0, zero_mul]
  have hsplit :
      (∑' x, q x * blockKernel β t u x y ω) =
        (∑' x, q x * d x) + blockMass β t u ω * srwKernel b y := by
    have hD := hfinite d
    have hP := hfinite (fun x => p x * srwKernel b y)
    calc
      _ = ∑' x, (q x * d x + q x * (p x * srwKernel b y)) := by
        apply tsum_congr
        intro x
        dsimp [q, d, p, a, b]
        simp only [blockKernel, blockDiscrepancy]
        ring
      _ = (∑' x, q x * d x) + ∑' x, q x * (p x * srwKernel b y) :=
        hD.tsum_add hP
      _ = (∑' x, q x * d x) + blockMass β t u ω * srwKernel b y := by
        congr 1
        calc
          _ = ∑' x, (q x * p x) * srwKernel b y := by
            apply tsum_congr
            intro x
            ring
          _ = (∑' x, q x * p x) * srwKernel b y := by rw [← tsum_mul_right]
          _ = blockMass β t u ω * srwKernel b y := by
            congr 1
            unfold blockMass smoothedP2Plane
            simp only [q, p, a, b, sub_zero]
  have hnum :
      (∑' x, srwKernel a (x - 0) *
          pointToPoint β a (b - a) x y ω) =
        (∑' x, q x * d x) + blockMass β t u ω * srwKernel b y := by
    simpa only [sub_zero, blockKernel, q, d] using hsplit
  have hmass : 0 < blockMass β t u ω := blockMass_pos β t u ω
  have hopen : openCorrector β t u u ω y =
      (∑' x, q x * d x) / blockMass β t u ω := by
    unfold openCorrector openCorrectorNumerator
    have hlen : u + 1 - u = 1 := by omega
    rw [hlen]
    simp_rw [discrepancyString_one]
    simp only [Finset.Icc_self, Finset.prod_singleton, q, d, a]
  unfold smoothedEndpointDist
  rw [show t u - t (u - 1) = b - a by rfl]
  rw [show smoothedP2Plane β (t (u - 1)) (t u) 0 ω = blockMass β t u ω by rfl]
  rw [hnum, hopen]
  field_simp [ne_of_gt hmass]
  ring

/-- There is only the empty interval family on a one-block range. -/
theorem intervalFamilies_self (r : ℕ) : intervalFamilies r r = {∅} := by
  unfold intervalFamilies
  have hpairs : Finset.Icc r r ×ˢ Finset.Icc r r = {(r, r)} := by simp
  rw [hpairs]
  have hempty : ({(r, r)} : Finset (ℕ × ℕ)).filter
      (fun I => I.1 < I.2) = ∅ := by
    simp
  rw [hempty]
  simp

/-- The interval expansion holds on a one-block range. -/
theorem blockRatio_eq_sum_intervalFamilies_self (β : ℝ) (t : ℕ → ℕ)
    (r : ℕ) (ω : Disorder) :
    blockRatio β t r r ω = ∑ F ∈ intervalFamilies r r, ∏ I ∈ F,
      closedDiscrepancy β t I.1 I.2 ω /
        ∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω := by
  rw [blockRatio_self, intervalFamilies_self]
  simp

/-- Each discrepancy kernel has every finite moment. -/
theorem memLp_blockDiscrepancy (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (x y : Site)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => blockDiscrepancy β t i x y ω) p disorderLaw := by
  unfold blockDiscrepancy blockKernel
  exact (Polymer.memLp_pointToPoint β (t (i - 1)) (t i - t (i - 1)) x y p hp).sub
    ((Polymer.memLp_pointToPlane β (t (i - 1)) (t i - t (i - 1)) x p hp).mul_const _)

/-- Every finite discrepancy string has every finite moment. -/
theorem memLp_discrepancyString (β : ℝ) (t : ℕ → ℕ) (u k : ℕ) (x y : Site)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    MemLp (fun ω => discrepancyString β t u k x y ω) p disorderLaw := by
  induction k generalizing x y p with
  | zero =>
      change MemLp (fun _ : Disorder => if x = y then (1 : ℝ) else 0) p disorderLaw
      split_ifs <;> exact memLp_const _
  | succ k ih =>
      have hp2zero : 2 * p ≠ 0 := by
        intro hz
        rcases mul_eq_zero.mp hz with htwo | hp
        · norm_num at htwo
        · exact hp0 hp
      have hp2top : 2 * p ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hpTop
      have heq : (fun ω => discrepancyString β t u (k + 1) x y ω) =
          fun ω => ∑ z ∈ discrepancyStringSupport t u k x,
            discrepancyString β t u k x z ω * blockDiscrepancy β t (u + k) z y ω := by
        funext ω
        change (∑' z, discrepancyString β t u k x z ω *
          blockDiscrepancy β t (u + k) z y ω) = _
        apply tsum_eq_sum
        intro z hz
        have hzero := discrepancyString_eq_zero_of_not_mem_support β t u k
          x z ω hz
        rw [hzero, zero_mul]
      rw [heq]
      exact memLp_finsetSum _ fun z hz => Polymer.memLp_mul_double p
        (ih x z (2 * p) hp2zero hp2top)
        (memLp_blockDiscrepancy β t (u + k) z y (2 * p) hp2top)

/-- The smoothed polymer mass factors into its product of block masses and the block ratio. -/
theorem smoothedP2Plane_eq_prod_blockMass_mul_blockRatio (β : ℝ) (t : ℕ → ℕ)
    (r s : ℕ) (ω : Disorder) :
    smoothedP2Plane β (t (r - 1)) (t s) 0 ω =
      (∏ i ∈ Finset.Icc r s, blockMass β t i ω) * blockRatio β t r s ω := by
  unfold blockRatio
  have hp : 0 < ∏ i ∈ Finset.Icc r s, blockMass β t i ω :=
    Finset.prod_pos fun i _ => blockMass_pos β t i ω
  field_simp [hp.ne']

/-- A block mass is measurable with respect to the time slice used by that block. -/
theorem measurable_blockMass (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)] (blockMass β t i) := by
  change Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
    (smoothedP2Plane β (t (i - 1)) (t i) 0)
  by_cases h : t (i - 1) ≤ t i
  · exact Polymer.measurable_smoothedP2Plane_block β (t (i - 1)) (t i) h 0
  · have hlt : t i < t (i - 1) := Nat.lt_of_not_ge h
    have hzero : t i - t (i - 1) = 0 := Nat.sub_eq_zero_of_le hlt.le
    have heq : smoothedP2Plane β (t (i - 1)) (t i) 0 = fun _ => 1 := by
      funext ω
      rw [Polymer.smoothedP2Plane_eq_sum]
      simp only [hzero, Polymer.pointToPlane_zero, mul_one]
      exact Polymer.sum_srwKernel_endpoints (t (i - 1)) 0
    rw [heq]
    exact measurable_const

/-- One discrepancy kernel is measurable on its own time slice. -/
theorem measurable_blockDiscrepancy (β : ℝ) (t : ℕ → ℕ) (i : ℕ)
    (hi : t (i - 1) ≤ t i) (x y : Site) :
    Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
      (fun ω => blockDiscrepancy β t i x y ω) := by
  let a := t (i - 1)
  let b := t i
  have hab : a ≤ b := hi
  have hpt : Measurable[Gaussian.disorderBlock a b]
      (fun ω => pointToPoint β a (b - a) x y ω) := by
    convert Polymer.measurable_pointToPoint_block β a (b - a) x y using 1
    rw [Nat.add_sub_of_le hab]
  have hpl : Measurable[Gaussian.disorderBlock a b]
      (fun ω => pointToPlane β a (b - a) x ω) := by
    convert Polymer.measurable_pointToPlane_block β a (b - a) x using 1
    rw [Nat.add_sub_of_le hab]
  change Measurable[Gaussian.disorderBlock a b]
    (fun ω => pointToPoint β a (b - a) x y ω -
      pointToPlane β a (b - a) x ω * srwKernel b y)
  exact hpt.sub (hpl.mul_const _)

/-- A discrepancy string is measurable on any time block containing all its factors. -/
theorem measurable_discrepancyString_block (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (u k v : ℕ) (huk : u + k ≤ v) (x y : Site) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (fun ω => discrepancyString β t u k x y ω) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (u - 1)) (t v)
  induction k generalizing x y with
  | zero =>
      exact measurable_const
  | succ k ih =>
      have huk' : u + k ≤ v := by omega
      have hstart : t (u - 1) ≤ t (u + k - 1) := by
        apply ht
        omega
      have htime : u + k ≤ v := by omega
      have hend : t (u + k) ≤ t v := ht htime
      have hsub := Gaussian.disorderBlock_mono hstart hend
      have hlast' (z : Site) : Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
          (fun ω => blockDiscrepancy β t (u + k) z y ω) := by
        exact (measurable_blockDiscrepancy β t (u + k) (ht (by omega)) z y).mono
          hsub le_rfl
      change Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
        (fun ω => ∑' z, discrepancyString β t u k x z ω *
          blockDiscrepancy β t (u + k) z y ω)
      exact Measurable.tsum fun z => (ih huk' x z).mul (hlast' z)

/-- The closed discrepancy is measurable on the union of its constituent blocks. -/
theorem measurable_closedDiscrepancy (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (u v : ℕ) (huv : u ≤ v) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (closedDiscrepancy β t u v) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (u - 1)) (t v)
  have huv' : u + (v - u) ≤ v := by omega
  have hstr (x y : Site) :=
    measurable_discrepancyString_block β t ht u (v - u) v huv' x y
  have hstart : t (u - 1) ≤ t (v - 1) := by
    apply ht
    omega
  have hlast (y : Site) : Measurable[Gaussian.disorderBlock (t (v - 1)) (t v)]
      (fun ω => pointToPlane β (t (v - 1)) (t v - t (v - 1)) y ω) := by
    convert Polymer.measurable_pointToPlane_block β (t (v - 1))
      (t v - t (v - 1)) y using 1
    rw [Nat.add_sub_of_le (ht (by omega))]
  have hlast' (y : Site) : Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (fun ω => pointToPlane β (t (v - 1)) (t v - t (v - 1)) y ω) :=
    (hlast y).mono (Gaussian.disorderBlock_mono hstart le_rfl) le_rfl
  unfold closedDiscrepancy
  apply Measurable.tsum
  intro x
  apply Measurable.tsum
  intro y
  exact (measurable_const.mul (hstr x y)).mul (hlast' y)

/-- Integrating the first discrepancy block against any bounded future observable cancels. -/
theorem closedDiscrepancy_integral_mul_eq_zero (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (u v : ℕ) (hu : 1 ≤ u) (huv : u < v)
    (Y : Disorder → ℝ)
    (hY : Measurable[Gaussian.disorderBlock (t u) (t v)] Y)
    (hYb : ∃ M : ℝ, ∀ ω, |Y ω| ≤ M) :
    ∫ ω, closedDiscrepancy β t u v ω * Y ω ∂disorderLaw = 0 := by
  classical
  let k := v - u - 1
  let sx := closedStartSupport t u
  let sz := closedFirstSupport t u
  let sy := closedTailSupport t u k
  have hindex : u + k + 1 = v := by dsimp [k]; omega
  obtain ⟨M, hM⟩ := hYb
  have hYglobal : Measurable Y := hY.mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hYfour : MemLp Y 4 disorderLaw :=
    MemLp.of_bound hYglobal.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact hM ω)
  have htermInt (x z y : Site) : Integrable (fun ω =>
      srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
        discrepancyString β t (u + 1) k z y ω *
          pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω)
      disorderLaw := by
    have hDfour := memLp_blockDiscrepancy β t u x z 4 (by norm_num)
    have hTfour := memLp_discrepancyString β t (u + 1) k z y 4
      (by norm_num) (by norm_num)
    have hPfour := Polymer.memLp_pointToPlane β (t (u + k))
      (t (u + k + 1) - t (u + k)) y 4 (by norm_num)
    have hDdouble : MemLp (fun ω => blockDiscrepancy β t u x z ω) (2 * 2) disorderLaw :=
      by convert hDfour using 1; norm_num
    have hTdouble : MemLp (fun ω => discrepancyString β t (u + 1) k z y ω)
        (2 * 2) disorderLaw := by convert hTfour using 1; norm_num
    have hDT : MemLp (fun ω => blockDiscrepancy β t u x z ω *
        discrepancyString β t (u + 1) k z y ω) 2 disorderLaw := by
      simpa using Polymer.memLp_mul_double 2 hDdouble hTdouble
    have hPdouble : MemLp (fun ω =>
        pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω)
        (2 * 2) disorderLaw := by convert hPfour using 1; norm_num
    have hYdouble : MemLp Y (2 * 2) disorderLaw := by convert hYfour using 1; norm_num
    have hPY : MemLp (fun ω =>
        pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω)
        2 disorderLaw := by
      simpa using Polymer.memLp_mul_double 2 hPdouble hYdouble
    have hDTone : MemLp (fun ω => blockDiscrepancy β t u x z ω *
        discrepancyString β t (u + 1) k z y ω) (2 * 1) disorderLaw := by
      simpa using hDT
    have hPYone : MemLp (fun ω =>
        pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω)
        (2 * 1) disorderLaw := by simpa using hPY
    have hprod : MemLp (fun ω =>
        (blockDiscrepancy β t u x z ω * discrepancyString β t (u + 1) k z y ω) *
          (pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω))
        1 disorderLaw := by
      simpa using Polymer.memLp_mul_double 1 hDTone hPYone
    have heq : (fun ω => srwKernel (t (u - 1)) x *
        blockDiscrepancy β t u x z ω * discrepancyString β t (u + 1) k z y ω *
          pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω) =
        fun ω => srwKernel (t (u - 1)) x *
          ((blockDiscrepancy β t u x z ω * discrepancyString β t (u + 1) k z y ω) *
            (pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω)) := by
      funext ω
      ring
    rw [heq]
    exact memLp_one_iff_integrable.mp (hprod.const_mul _)
  have htermFactor (x z y : Site) :
      ∫ ω, srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
          discrepancyString β t (u + 1) k z y ω *
            pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω
          ∂disorderLaw =
        srwKernel (t (u - 1)) x *
          (∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw) *
            (∫ ω, discrepancyString β t (u + 1) k z y ω *
              (pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω)
              ∂disorderLaw) := by
    let D : Disorder → ℝ := fun ω => blockDiscrepancy β t u x z ω
    let F : Disorder → ℝ := fun ω => discrepancyString β t (u + 1) k z y ω *
      (pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω)
    have hDmeas : Measurable[Gaussian.disorderBlock (t (u - 1)) (t u)] D := by
      exact measurable_blockDiscrepancy β t u (ht (by omega)) x z
    have hDglobal : Measurable D := hDmeas.mono
      (Gaussian.disorderBlock_le _ _) le_rfl
    have hTail0 := measurable_discrepancyString_block β t ht (u + 1) k v
      (by omega) z y
    have hTail : Measurable[Gaussian.disorderBlock (t u) (t v)]
        (fun ω => discrepancyString β t (u + 1) k z y ω) := by
      have hstart : (u + 1) - 1 = u := by omega
      rw [hstart] at hTail0
      exact hTail0
    have hP0 : Measurable[Gaussian.disorderBlock (t (u + k)) (t (u + k + 1))]
        (fun ω => pointToPlane β (t (u + k))
          (t (u + k + 1) - t (u + k)) y ω) := by
      convert Polymer.measurable_pointToPlane_block β (t (u + k))
        (t (u + k + 1) - t (u + k)) y using 1
      rw [Nat.add_sub_of_le (ht (by omega))]
    have hP : Measurable[Gaussian.disorderBlock (t u) (t v)]
        (fun ω => pointToPlane β (t (u + k))
          (t (u + k + 1) - t (u + k)) y ω) := by
      have hstart : t u ≤ t (u + k) := ht (by omega)
      have hend : t (u + k + 1) ≤ t v := by rw [hindex]
      have hmono := Gaussian.disorderBlock_mono hstart hend
      simpa only [hindex] using hP0.mono hmono le_rfl
    have hFmeas : Measurable[Gaussian.disorderBlock (t u) (t v)] F := by
      exact hTail.mul (hP.mul hY)
    have hFglobal : Measurable F := hFmeas.mono
      (Gaussian.disorderBlock_le _ _) le_rfl
    have hIndep : IndepFun D F disorderLaw := by
      exact (IndepFun_iff D F disorderLaw).2 fun a b ha hb =>
        (Indep_iff _ _ _).1
          (Gaussian.indep_disorderBlock_of_le (m := t (u - 1)) (n := t u)
            (a := t u) (b := t v) (le_rfl)) a b
          (hDmeas.comap_le a ha) (hFmeas.comap_le b hb)
    have hfactor := hIndep.integral_fun_mul_eq_mul_integral
      hDglobal.aestronglyMeasurable hFglobal.aestronglyMeasurable
    have heq : (fun ω => srwKernel (t (u - 1)) x *
        blockDiscrepancy β t u x z ω * discrepancyString β t (u + 1) k z y ω *
          pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω) =
        fun ω => srwKernel (t (u - 1)) x * (D ω * F ω) := by
      funext ω
      dsimp [D, F]
      ring
    rw [heq, integral_const_mul, hfactor]
    ring
  have hcancel (z : Site) :
      ∑ x ∈ sx, srwKernel (t (u - 1)) x *
        ∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw = 0 := by
    have htsum := heatStart_integral_blockDiscrepancy β t u (ht (by omega)) z
    have hfinite : ∑' x, srwKernel (t (u - 1)) x *
        ∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw =
      ∑ x ∈ sx, srwKernel (t (u - 1)) x *
        ∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw := by
      apply tsum_eq_sum
      intro x hx
      have hx0 : srwKernel (t (u - 1)) x = 0 := by
        simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem
          (t (u - 1)) 0 x hx
      simp [hx0]
    rw [hfinite] at htsum
    exact htsum
  have hexp (ω : Disorder) : closedDiscrepancy β t u v ω =
      ∑ x ∈ sx, ∑ z ∈ sz, ∑ y ∈ sy,
        srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
          discrepancyString β t (u + 1) k z y ω *
            pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω := by
    rw [← hindex]
    simpa [sx, sz, sy, k] using
      closedDiscrepancy_eq_finiteSum_firstFactor β t u k ω
  have hfun : (fun ω => closedDiscrepancy β t u v ω * Y ω) = fun ω =>
      ∑ x ∈ sx, ∑ z ∈ sz, ∑ y ∈ sy,
        srwKernel (t (u - 1)) x * blockDiscrepancy β t u x z ω *
          discrepancyString β t (u + 1) k z y ω *
            pointToPlane β (t (u + k)) (t (u + k + 1) - t (u + k)) y ω * Y ω := by
    funext ω
    rw [hexp ω]
    simp only [Finset.sum_mul]
  rw [hfun]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun z _ =>
    integrable_finsetSum _ (fun y _ => htermInt x z y)))]
  simp_rw [integral_finsetSum _ (fun z _ => integrable_finsetSum _
    (fun y _ => htermInt _ z y))]
  simp_rw [integral_finsetSum _ (fun y _ => htermInt _ _ y), htermFactor]
  calc
    _ = ∑ y ∈ sy, ∑ z ∈ sz, ∑ x ∈ sx,
          srwKernel (t (u - 1)) x *
            (∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw) *
              (∫ ω, discrepancyString β t (u + 1) k z y ω *
                (pointToPlane β (t (u + k))
                  (t (u + k + 1) - t (u + k)) y ω * Y ω) ∂disorderLaw) := by
      calc
        _ = ∑ x ∈ sx, ∑ y ∈ sy, ∑ z ∈ sz,
              (srwKernel (t (u - 1)) x *
                (∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw)) *
                  (∫ ω, discrepancyString β t (u + 1) k z y ω *
                    (pointToPlane β (t (u + k))
                      (t (u + k + 1) - t (u + k)) y ω * Y ω) ∂disorderLaw) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact Finset.sum_comm
        _ = ∑ y ∈ sy, ∑ x ∈ sx, ∑ z ∈ sz,
              (srwKernel (t (u - 1)) x *
                (∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw)) *
                  (∫ ω, discrepancyString β t (u + 1) k z y ω *
                    (pointToPlane β (t (u + k))
                      (t (u + k + 1) - t (u + k)) y ω * Y ω) ∂disorderLaw) :=
          Finset.sum_comm
        _ = ∑ y ∈ sy, ∑ z ∈ sz, ∑ x ∈ sx,
              (srwKernel (t (u - 1)) x *
                (∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw)) *
                  (∫ ω, discrepancyString β t (u + 1) k z y ω *
                    (pointToPlane β (t (u + k))
                      (t (u + k + 1) - t (u + k)) y ω * Y ω) ∂disorderLaw) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      apply Finset.sum_eq_zero
      intro z hz
      calc
        ∑ x ∈ sx, (srwKernel (t (u - 1)) x *
            ∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw) *
              (∫ ω, discrepancyString β t (u + 1) k z y ω *
                (pointToPlane β (t (u + k))
                  (t (u + k + 1) - t (u + k)) y ω * Y ω) ∂disorderLaw) =
          (∑ x ∈ sx, srwKernel (t (u - 1)) x *
            ∫ ω, blockDiscrepancy β t u x z ω ∂disorderLaw) *
              (∫ ω, discrepancyString β t (u + 1) k z y ω *
                (pointToPlane β (t (u + k))
                  (t (u + k + 1) - t (u + k)) y ω * Y ω) ∂disorderLaw) :=
          (Finset.sum_mul sx _ _).symm
        _ = 0 := by rw [hcancel z, zero_mul]

/-- The masses of successive monotone time blocks are jointly independent. -/
theorem iIndepFun_blockMass (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t) :
    iIndepFun (fun i : {i : ℕ // 1 ≤ i} => blockMass β t i) disorderLaw := by
  apply Polymer.independent_of_blockMeasurable
    (fun i : {i : ℕ // 1 ≤ i} => t (i.val - 1))
    (fun i => t i.val)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro k hk₁ hk₂
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · change t (i.val - 1) < k ∧ k ≤ t i.val at hk₁
      change t (j.val - 1) < k ∧ k ≤ t j.val at hk₂
      rcases hk₁ with ⟨hk₁l, hk₁r⟩
      rcases hk₂ with ⟨hk₂l, hk₂r⟩
      have htime : t i.val ≤ t (j.val - 1) := by
        apply ht
        omega
      omega
    · change t (i.val - 1) < k ∧ k ≤ t i.val at hk₁
      change t (j.val - 1) < k ∧ k ≤ t j.val at hk₂
      rcases hk₁ with ⟨hk₁l, hk₁r⟩
      rcases hk₂ with ⟨hk₂l, hk₂r⟩
      have htime : t j.val ≤ t (i.val - 1) := by
        apply ht
        omega
      omega
  · intro i
    exact measurable_blockMass β t i.val

end Critical2DKPZ.Blocks

end
