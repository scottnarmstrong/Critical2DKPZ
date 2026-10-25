/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPositiveTerminalAverage
public import Critical2DKPZ.SHF.Moments.WordDominationScaledBall
import Mathlib.Tactic

/-! # Support control for the endpoint average -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.Polymer
open scoped BigOperators

attribute [local instance] Classical.propDecidable

private theorem collisionWord_endpointAverage_duration_le_scaledBall
    {h N : ℕ} (hN : 1 ≤ N) {R : ℝ} (hR : 0 ≤ R)
    (y : Fin h → Site) (k : ℕ) :
    (∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
      (if ∀ i,
            ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
        ∏ i, srwKernel (k + 1) (z i - y i) else 0)) ≤
      ∑ z ∈ Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R),
        ∏ i, srwKernel (k + 1) (z i - y i) := by
  classical
  let E : Finset (Fin h → Site) :=
    Fintype.piFinset (fun i => endpoints (y i) (k + 1))
  let A : Finset (Fin h → Site) :=
    Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R)
  let good : Finset (Fin h → Site) := E.filter fun z =>
    ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2
  have hgoodSub : good ⊆ A := by
    intro z hz
    have hz' : z ∈ E.filter (fun z =>
        ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2) := by
      simpa only [good] using hz
    have hzgood := (Finset.mem_filter.mp hz').2
    apply Fintype.mem_piFinset.mpr
    intro i
    exact mem_collisionWordScaledBallSites_of_scaledNorm hN hR (z i) (hzgood i)
  have hrewrite :
      (∑ z ∈ E,
        (if ∀ i,
              ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
          ∏ i, srwKernel (k + 1) (z i - y i) else 0)) =
        ∑ z ∈ good, ∏ i, srwKernel (k + 1) (z i - y i) := by
    symm
    change (∑ z ∈ E.filter (fun z : Fin h → Site =>
          ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2),
        ∏ i, srwKernel (k + 1) (z i - y i)) = _
    exact Finset.sum_filter (s := E)
      (p := fun z : Fin h → Site =>
        ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2)
      (f := fun z => ∏ i, srwKernel (k + 1) (z i - y i))
  rw [show (∑ z ∈ E,
      (if ∀ i,
            ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
        ∏ i, srwKernel (k + 1) (z i - y i) else 0)) =
      ∑ z ∈ good, ∏ i, srwKernel (k + 1) (z i - y i) from hrewrite]
  exact Finset.sum_le_sum_of_subset_of_nonneg hgoodSub (by
    intro z hz hnot
    exact Finset.prod_nonneg fun i hi => kernel_nonneg (k + 1) (z i - y i))

/-- A compactly supported terminal indicator is bounded by the normalized
common-duration walk average, with every averaged endpoint in the finite
scaled support ball. -/
theorem replicaTerminalIndicator_le_scaledBallWalkHorizonAverage
    {h N : ℕ} (hN : 1 ≤ N) {R : ℝ} (hR : 0 ≤ R)
    (A₀ : Finset Site)
    (hA₀ : ∀ y ∈ A₀,
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane y‖ ≤ R) :
    ∀ y : Fin h → Site,
      (∏ i, (if y i ∈ A₀ then (1 : ℝ) else 0)) ≤
        ((2 : ℝ) ^ h / N) *
          ∑ k ∈ Finset.range N,
            ∑ z ∈ Fintype.piFinset
              (fun _ : Fin h => collisionWordScaledBallSites N R),
              ∏ i, srwKernel (k + 1) (z i - y i) := by
  classical
  have hNpos : 0 < N := by omega
  let f : Fin h → Site → ℝ := fun i y => if y ∈ A₀ then 1 else 0
  have hfnonneg : ∀ i y, 0 ≤ f i y := by
    intro i y
    simp only [f]
    split_ifs <;> norm_num
  have hfbound : ∀ i y,
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane y‖ ≤ R → f i y ≤ 1 := by
    intro i y hy
    dsimp [f]
    split_ifs <;> norm_num
  have hfzero : ∀ i y,
      ¬ ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane y‖ ≤ R → f i y = 0 := by
    intro i y hy
    dsimp [f]
    have hnot : y ∉ A₀ := by
      intro hyA
      exact hy (hA₀ y hyA)
    simp [hnot]
  have hprofile := replicaTerminalProfile_le_positiveWalkHorizonAverage
    hNpos R 1 (by norm_num) f hfnonneg hfbound hfzero
  intro y
  calc
    (∏ i, (if y i ∈ A₀ then (1 : ℝ) else 0)) = ∏ i, f i (y i) := by
      rfl
    _ ≤ ((2 : ℝ) ^ h * 1 ^ h / N) *
        ∑ k ∈ Finset.range N,
          ∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
            (if ∀ i,
                  ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
              ∏ i, srwKernel (k + 1) (z i - y i) else 0) := hprofile y
    _ ≤ ((2 : ℝ) ^ h / N) *
        ∑ k ∈ Finset.range N,
          ∑ z ∈ Fintype.piFinset
            (fun _ : Fin h => collisionWordScaledBallSites N R),
            ∏ i, srwKernel (k + 1) (z i - y i) := by
      have hterm (k : ℕ) :
          (∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
            (if ∀ i,
                  ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
              ∏ i, srwKernel (k + 1) (z i - y i) else 0)) ≤
          ∑ z ∈ Fintype.piFinset
            (fun _ : Fin h => collisionWordScaledBallSites N R),
              ∏ i, srwKernel (k + 1) (z i - y i) :=
        collisionWord_endpointAverage_duration_le_scaledBall hN hR y k
      have hsum := Finset.sum_le_sum (s := Finset.range N)
        (fun k hk => hterm k)
      have hfac : 0 ≤ (2 : ℝ) ^ h / N := by positivity
      simpa [div_eq_mul_inv, one_pow] using
        mul_le_mul_of_nonneg_left hsum hfac

end Critical2DKPZ.SHF.Moments

end
