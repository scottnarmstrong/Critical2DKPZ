/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawGoodSet
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! # Block measurability and factorization over connected components -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem measurable_truncatedInverse_block_local (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)] (truncatedInverse β t i) := by
  have hmass : Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
      (blockMass β t i) := measurable_blockMass β t i
  have hdefect : Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
      (fun ω => |blockMass β t i ω - 1|) := by
    have hreal : Measurable (fun x : ℝ => |x - 1|) := by fun_prop
    exact hreal.comp hmass
  have hgood : MeasurableSet[Gaussian.disorderBlock (t (i - 1)) (t i)]
      {ω | |blockMass β t i ω - 1| ≤ 1 / 2} :=
    isClosed_Iic.measurableSet.preimage hdefect
  unfold truncatedInverse
  exact Measurable.ite hgood hmass.inv measurable_const

/-- A truncated corrector is measurable with respect to the time interval it uses. -/
theorem measurable_truncatedCorrector_block (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (u v : ℕ) (huv : u < v) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (truncatedCorrector β t u v) := by
  have hclosed : Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (closedDiscrepancy β t u v) :=
    measurable_closedDiscrepancy β t ht u v (Nat.le_of_lt huv)
  have hM (i : ℕ) (hi : i ∈ Finset.Icc u v) :
      Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
        (truncatedInverse β t i) := by
    have hi' := Finset.mem_Icc.mp hi
    have hstart : t (u - 1) ≤ t (i - 1) := ht (by omega)
    have hstop : t i ≤ t v := ht hi'.2
    exact (measurable_truncatedInverse_block_local β t i).mono
      (Gaussian.disorderBlock_mono hstart hstop) le_rfl
  unfold truncatedCorrector
  apply hclosed.mul
  apply Finset.measurable_prod
  intro i hi
  exact hM i hi

/-- The good-block indicator, as a real-valued measurable function on its block. -/
theorem measurable_goodBlockIndicator (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
      (fun ω : Disorder => if |blockMass β t i ω - 1| ≤ 1 / 2 then (1 : ℝ) else 0) := by
  have hmass : Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)] (blockMass β t i) :=
    measurable_blockMass β t i
  have hdefect : Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
      (fun ω => |blockMass β t i ω - 1|) := by
    have hreal : Measurable (fun x : ℝ => |x - 1|) := by fun_prop
    exact hreal.comp hmass
  have hset : MeasurableSet[Gaussian.disorderBlock (t (i - 1)) (t i)]
      {ω | |blockMass β t i ω - 1| ≤ 1 / 2} :=
    isClosed_Iic.measurableSet.preimage hdefect
  exact Measurable.ite hset measurable_const measurable_const

/-- Different maximal bonded runs have disjoint block spans. -/
theorem pairComponents_span_disjoint {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    {c d : ℕ × ℕ} (hc : c ∈ pairComponents r s F G)
    (hd : d ∈ pairComponents r s F G) (hcd : c ≠ d) :
    c.2 < d.1 ∨ d.2 < c.1 := by
  classical
  have hc' := Finset.mem_filter.mp hc
  have hd' := Finset.mem_filter.mp hd
  have hcs := Finset.mem_product.mp hc'.1
  have hds := Finset.mem_product.mp hd'.1
  have hcb := hc'.2.2.1
  have hcl := hc'.2.2.2.1
  have hcr := hc'.2.2.2.2
  have hdb := hd'.2.2.1
  have hdl := hd'.2.2.2.1
  have hdr := hd'.2.2.2.2
  rcases le_total c.1 d.1 with hle | hle
  · by_cases hstart : c.1 = d.1
    · have hends : c.2 = d.2 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hbond := hdb c.2 (Finset.mem_Ico.mpr ⟨by omega, hlt⟩)
          exact hcr hbond
        · have hbond := hcb d.2 (Finset.mem_Ico.mpr ⟨by omega, hgt⟩)
          exact hdr hbond
      exact False.elim (hcd (Prod.ext hstart hends))
    · have hstart' : c.1 < d.1 := by omega
      by_contra hnot
      have hbond := hcb (d.1 - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      exact hdl hbond
  · by_cases hstart : d.1 = c.1
    · have hends : c.2 = d.2 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hbond := hdb c.2 (Finset.mem_Ico.mpr ⟨by omega, hlt⟩)
          exact hcr hbond
        · have hbond := hcb d.2 (Finset.mem_Ico.mpr ⟨by omega, hgt⟩)
          exact hdr hbond
      exact False.elim (hcd (Prod.ext hstart.symm hends))
    · have hstart' : d.1 < c.1 := by omega
      by_contra hnot
      have hbond := hdb (c.1 - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      exact hcl hbond

/-- Pairwise-disjoint maximal spans induce disjoint time-block sigma fields. -/
theorem pairComponents_time_disjoint {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    (t : ℕ → ℕ) (ht : Monotone t) {c d : ℕ × ℕ}
    (hc : c ∈ pairComponents r s F G) (hd : d ∈ pairComponents r s F G)
    (hcd : c ≠ d) :
    Disjoint (Set.Ioc (t (c.1 - 1)) (t c.2))
      (Set.Ioc (t (d.1 - 1)) (t d.2)) := by
  rcases pairComponents_span_disjoint hc hd hcd with hcd' | hdc'
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have htime : t c.2 ≤ t (d.1 - 1) := ht (by omega)
    exact (not_lt_of_ge (hx.2.trans htime)) hy.1
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have htime : t d.2 ≤ t (c.1 - 1) := ht (by omega)
    exact (not_lt_of_ge (hy.2.trans htime)) hx.1

end Critical2DKPZ.OnePoint

end
