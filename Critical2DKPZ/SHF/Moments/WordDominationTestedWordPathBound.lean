/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPairWordGeometry
public import Critical2DKPZ.SHF.Moments.WordDominationTerminalSupport
public import Critical2DKPZ.SHF.Moments.WordDominationWordHorizonExtension
public import Critical2DKPZ.SHF.Moments.WordDominationCellProfile
public import Critical2DKPZ.SHF.Moments.WordDominationTestDomination
public import Critical2DKPZ.SHF.Moments.WordDominationPositivity
import Mathlib.Tactic

/-! # Compact word coefficients as boundary path pairings -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

private theorem isCollisionConfiguration_bot_for_tested_pairing {h : ℕ}
    (x : LatticeConfiguration h) : IsCollisionConfiguration (⊥ : ReplicaPartition h) x := by
  constructor
  · intro i j hij
    have hij' : i = j := by simpa using hij
    exact congrArg x hij'
  · intro i j hi _ _
    obtain ⟨k, hik, hrel⟩ := hi
    have heq : i = k := by simpa using hrel
    exact (hik heq.symm).elim

/-- The absolute value of a compactly supported tensor pairing is bounded by
the CCR hatted path after averaging the last `N` free durations. The factors
may have either sign; `hφ` bounds their absolute values. -/
theorem testedBlockWord_nonnegative_le_variancePathPairing
    (ϑ : ℝ) {h m N : ℕ} (hN : 1 ≤ N) {s t : ℝ}
    (L : ℕ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hwindow : evenCeil (N * t) - evenCeil (N * s) + N ≤ L)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    (hφ : ∀ i p, |φ i p| ≤ M)
    (hφR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (w : CollisionWord h (m + 1)) :
    |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤
      (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
        Real.exp ((lam / (L : ℝ)) *
          ((evenCeil (N * t) - evenCeil (N * s) + N : ℕ) : ℝ)) *
        ∑ x ∈ Fintype.piFinset
            (fun _ : Fin h => collisionWordScaledBallSites N (2 * (R + 2))),
          ∑ z ∈ Fintype.piFinset
            (fun _ : Fin h => collisionWordScaledBallSites N (2 * (R + 2))),
            varianceWeightedHattedPairWordPath L (lam / (L : ℝ))
              (criticalBeta ϑ N) ⊥ (List.ofFn w.1) x z := by
  classical
  let ψ : Fin h → C_c(Plane × Plane, ℝ) := fun i => compactAbs (φ i)
  let R₀ : ℝ := 2 * (R + 2)
  let A₀ : Finset Site := collisionWordScaledBallSites N R
  let A : Finset Site := collisionWordScaledBallSites N R₀
  let X₀ : Finset (Fin h → Site) := Fintype.piFinset fun _ => A₀
  let X : Finset (Fin h → Site) := Fintype.piFinset fun _ => A
  let n : ℕ := evenCeil (N * t) - evenCeil (N * s)
  let β : ℝ := criticalBeta ϑ N
  let κ : ℝ := lam / (L : ℝ)
  have hNpos : 0 < N := by omega
  have hN' : 1 ≤ N := hN
  have hR₀ : 0 ≤ R₀ := by dsimp [R₀]; positivity
  have hψnonneg (i : Fin h) (p : Plane × Plane) : 0 ≤ ψ i p := by
    change 0 ≤ |φ i p|
    positivity
  have hψbound (i : Fin h) (p : Plane × Plane) : |ψ i p| ≤ M := by
    change abs (abs (φ i p)) ≤ M
    simpa only [abs_abs] using hφ i p
  have hψR (i : Fin h) (p : Plane × Plane) (hp : ψ i p ≠ 0) :
      ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R := by
    have hp' : |φ i p| ≠ 0 := by
      change |φ i p| ≠ 0 at hp
      exact hp
    have hp'' : φ i p ≠ 0 := abs_ne_zero.mp hp'
    exact hφR i p hp''
  have hA₀sub : A₀ ⊆ A := by
    dsimp [A₀, A, R₀]
    exact collisionWord_scaledBall_subset_enlarged hN hR
  have hA₀scaled (y : Site) (hy : y ∈ A₀) :
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane y‖ ≤ R₀ := by
    exact collisionWord_scaledNorm_le_two_mul_of_mem_scaledBall hN hR hy
  have hsum := collisionWord_testedBlockWord_eq_sum_on_scaledBall
    ϑ hNpos s t R hR ψ hψR (List.ofFn w.1)
  have hKnonneg (x y : Fin h → Site) :
      0 ≤ blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := by
    exact blockWordKernel_nonneg (sigmaSq β) (sigmaSq_nonneg β)
      (List.ofFn w.1) n x y
  have hrowBound (x : Fin h → Site) (hx : x ∈ X₀) :
      (∑ y ∈ X₀, blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) ≤
        ((2 : ℝ) ^ h / N) *
          Real.exp (κ * ((n + N : ℕ) : ℝ)) *
            ∑ z ∈ X, varianceWeightedHattedPairWordPath L κ β
              ⊥ (List.ofFn w.1) x z := by
    have hprofile (y : Fin h → Site) :
        (∏ i, (if y i ∈ A₀ then (1 : ℝ) else 0)) ≤
          ((2 : ℝ) ^ h / N) *
            ∑ k ∈ Finset.range N,
              ∑ z ∈ X, ∏ i, srwKernel (k + 1) (z i - y i) := by
      exact replicaTerminalIndicator_le_scaledBallWalkHorizonAverage
        hN hR₀ A₀ hA₀scaled y
    have hprodIndicator (y : Fin h → Site) (hy : y ∈ X₀) :
        (∏ i, (if y i ∈ A₀ then (1 : ℝ) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hyi : y i ∈ A₀ := Fintype.mem_piFinset.mp hy i
      simp [hyi]
    have hrowEnlarge :
        (∑ y ∈ X₀, blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) ≤
          ((2 : ℝ) ^ h / N) *
            ∑ k ∈ Finset.range N,
              ∑ z ∈ X,
                ∑ y ∈ X₀,
                  blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                    ∏ i, srwKernel (k + 1) (z i - y i) := by
      calc
        _ = ∑ y ∈ X₀,
              blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y * 1 := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [mul_one]
        _ ≤ ∑ y ∈ X₀,
              ((2 : ℝ) ^ h / N) *
                ∑ k ∈ Finset.range N,
                  ∑ z ∈ X,
                    blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                      ∏ i, srwKernel (k + 1) (z i - y i) := by
                apply Finset.sum_le_sum
                intro y hy
                have hprof := hprofile y
                rw [hprodIndicator y hy] at hprof
                calc
                  _ ≤ blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                      (((2 : ℝ) ^ h / N) *
                        ∑ k ∈ Finset.range N, ∑ z ∈ X,
                          ∏ i, srwKernel (k + 1) (z i - y i)) := by
                    exact mul_le_mul_of_nonneg_left hprof (hKnonneg x y)
                  _ = ((2 : ℝ) ^ h / N) *
                        ∑ k ∈ Finset.range N, ∑ z ∈ X,
                          blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                            ∏ i, srwKernel (k + 1) (z i - y i) := by
                    let c : ℝ := (2 : ℝ) ^ h / N
                    let K0 : ℝ := blockWordKernel (sigmaSq β)
                      (List.ofFn w.1) n x y
                    have hdist : K0 *
                        (∑ k ∈ Finset.range N, ∑ z ∈ X,
                          ∏ i, srwKernel (k + 1) (z i - y i)) =
                        ∑ k ∈ Finset.range N, ∑ z ∈ X,
                          K0 * ∏ i, srwKernel (k + 1) (z i - y i) := by
                      calc
                        _ = ∑ k ∈ Finset.range N,
                              K0 * ∑ z ∈ X, ∏ i, srwKernel (k + 1) (z i - y i) :=
                            Finset.mul_sum (Finset.range N)
                              (fun k => ∑ z ∈ X, ∏ i, srwKernel (k + 1) (z i - y i)) K0
                        _ = _ := by
                          apply Finset.sum_congr rfl
                          intro k hk
                          exact Finset.mul_sum X
                            (fun z => ∏ i, srwKernel (k + 1) (z i - y i)) K0
                    calc
                      _ = c * (blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                            ∑ k ∈ Finset.range N, ∑ z ∈ X,
                              ∏ i, srwKernel (k + 1) (z i - y i)) := by ring
                      _ = c * ∑ k ∈ Finset.range N, ∑ z ∈ X,
                            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                              ∏ i, srwKernel (k + 1) (z i - y i) := by
                        rw [← hdist]
        _ = ((2 : ℝ) ^ h / N) *
              ∑ k ∈ Finset.range N, ∑ z ∈ X, ∑ y ∈ X₀,
                blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                  ∏ i, srwKernel (k + 1) (z i - y i) := by
              have hswap :
                  (∑ y ∈ X₀, ∑ k ∈ Finset.range N, ∑ z ∈ X,
                    blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                      ∏ i, srwKernel (k + 1) (z i - y i)) =
                  ∑ k ∈ Finset.range N, ∑ z ∈ X, ∑ y ∈ X₀,
                    blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                      ∏ i, srwKernel (k + 1) (z i - y i) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro k hk
                exact Finset.sum_comm
              rw [← Finset.mul_sum, hswap]
    have hreorder :
        (∑ k ∈ Finset.range N,
          ∑ z ∈ X, ∑ y ∈ X₀,
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
              ∏ i, srwKernel (k + 1) (z i - y i)) =
          ∑ z ∈ X, ∑ k ∈ Finset.range N, ∑ y ∈ X₀,
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
              ∏ i, srwKernel (k + 1) (z i - y i) := by
      exact Finset.sum_comm
    rw [hreorder] at hrowEnlarge
    have hrowBounded :
        (∑ z ∈ X, ∑ k ∈ Finset.range N, ∑ y ∈ X₀,
          blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
            ∏ i, srwKernel (k + 1) (z i - y i)) ≤
          ∑ z ∈ X,
            Real.exp (κ * ((n + N : ℕ) : ℝ)) *
              varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z := by
      apply Finset.sum_le_sum
      intro z hz
      let f : (Fin h → Site) → ℝ := fun y => ∏ i, srwKernel (N) (z i - y i)
      have hsum_le (k : ℕ) (hk : k ∈ Finset.range N) :
          (∑ y ∈ X₀,
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
              ∏ i, srwKernel (k + 1) (z i - y i)) ≤
            ∑' y : Fin h → Site,
              blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                ∏ i, srwKernel (k + 1) (z i - y i) := by
        have hsummable := summable_mul_blockWordKernel_row
          (sigmaSq β) (List.ofFn w.1) n x
          (fun y => ∏ i, srwKernel (k + 1) (z i - y i))
        apply hsummable.sum_le_tsum
        intro y hy
        exact mul_nonneg (hKnonneg x y)
          (Finset.prod_nonneg fun i hi => kernel_nonneg (k + 1) (z i - y i))
      have hsumAll :
          (∑ k ∈ Finset.range N, ∑ y ∈ X₀,
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
              ∏ i, srwKernel (k + 1) (z i - y i)) ≤
            ∑ k ∈ Finset.range N, ∑' y : Fin h → Site,
              blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
                ∏ i, srwKernel (k + 1) (z i - y i) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hsum_le k hk
      have hwordHorizon := blockWordKernel_positiveHorizonExtension_le_varianceHattedPath
        β lam hlam ⊥ (List.ofFn w.1) (n := n) (K := N) (L := L)
        (by omega) (by simpa [n] using hwindow) x z
        (isCollisionConfiguration_bot_for_tested_pairing x)
      simpa [κ] using hsumAll.trans hwordHorizon
    calc
      _ ≤ ((2 : ℝ) ^ h / N) *
          ∑ z ∈ X, ∑ k ∈ Finset.range N, ∑ y ∈ X₀,
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y *
              ∏ i, srwKernel (k + 1) (z i - y i) := hrowEnlarge
      _ ≤ ((2 : ℝ) ^ h / N) *
          ∑ z ∈ X,
            Real.exp (κ * ((n + N : ℕ) : ℝ)) *
              varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z :=
        mul_le_mul_of_nonneg_left hrowBounded (by positivity)
      _ = ((2 : ℝ) ^ h / N) *
          Real.exp (κ * ((n + N : ℕ) : ℝ)) *
            ∑ z ∈ X, varianceWeightedHattedPairWordPath L κ β
              ⊥ (List.ofFn w.1) x z := by
        let c : ℝ := (2 : ℝ) ^ h / N
        let e : ℝ := Real.exp (κ * ((n + N : ℕ) : ℝ))
        calc
          _ = ∑ z ∈ X, c * (e *
                varianceWeightedHattedPairWordPath L κ β ⊥
                  (List.ofFn w.1) x z) := by
              exact Finset.mul_sum X
                (fun z => e * varianceWeightedHattedPairWordPath L κ β ⊥
                  (List.ofFn w.1) x z) c
          _ = ∑ z ∈ X, (c * e) *
                varianceWeightedHattedPairWordPath L κ β ⊥
                  (List.ofFn w.1) x z := by
              apply Finset.sum_congr rfl
              intro z hz
              ring
          _ = c * e * ∑ z ∈ X,
                varianceWeightedHattedPairWordPath L κ β ⊥
                  (List.ofFn w.1) x z := by
              exact (Finset.mul_sum X
                (fun z => varianceWeightedHattedPairWordPath L κ β ⊥
                  (List.ofFn w.1) x z) (c * e)).symm
  have hfinite : testedBlockWord ϑ N s t ψ (List.ofFn w.1) =
      ∑ x ∈ X₀, ∑ y ∈ X₀,
        (∏ i, cellTestWeight N (ψ i) (x i) (y i)) *
          blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := by
    simpa [ψ, X₀, n, β] using hsum
  have hweight (x y : Fin h → Site) (hx : x ∈ X₀) (hy : y ∈ X₀) :
      (∏ i, cellTestWeight N (ψ i) (x i) (y i)) ≤ (4 * M / N) ^ h := by
    have hbound := abs_prod_cellTestWeight_le_scaledBallIndicators
      hNpos ψ M R hM hR hψbound hψR x y
    have hxA : ∀ i, x i ∈ A₀ := Fintype.mem_piFinset.mp hx
    have hyA : ∀ i, y i ∈ A₀ := Fintype.mem_piFinset.mp hy
    have hxA' : ∀ i, x i ∈ collisionWordScaledBallSites N R := by
      simpa [A₀] using hxA
    have hyA' : ∀ i, y i ∈ collisionWordScaledBallSites N R := by
      simpa [A₀] using hyA
    have hprodnonneg :
        0 ≤ ∏ i, cellTestWeight N (ψ i) (x i) (y i) :=
      Finset.prod_nonneg fun i hi => cellTestWeight_nonneg N (ψ i)
        (hψnonneg i) (x i) (y i)
    have hbound' :
        |∏ i, cellTestWeight N (ψ i) (x i) (y i)| ≤ (4 * M / N) ^ h := by
      have hbound'' := hbound
      simp [hxA', hyA'] at hbound''
      exact hbound''
    rw [abs_of_nonneg hprodnonneg] at hbound'
    exact hbound'
  have hsumBound :
      (∑ x ∈ X₀, ∑ y ∈ X₀,
        (∏ i, cellTestWeight N (ψ i) (x i) (y i)) *
          blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) ≤
        (4 * M / N) ^ h *
          ∑ x ∈ X₀, ∑ y ∈ X₀,
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := by
    calc
      _ ≤ ∑ x ∈ X₀, ∑ y ∈ X₀,
            (4 * M / N) ^ h *
              blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_right (hweight x y hx hy) (hKnonneg x y)
      _ = (4 * M / N) ^ h *
            ∑ x ∈ X₀, ∑ y ∈ X₀,
              blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := by
          let c : ℝ := (4 * M / N) ^ h
          change (∑ x ∈ X₀, ∑ y ∈ X₀,
              c * blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) =
            c * ∑ x ∈ X₀, ∑ y ∈ X₀,
              blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y
          calc
            _ = ∑ x ∈ X₀, c * ∑ y ∈ X₀,
                  blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := by
                apply Finset.sum_congr rfl
                intro x hx
                exact (Finset.mul_sum X₀
                  (fun y => blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) c).symm
            _ = _ := (Finset.mul_sum X₀
              (fun x => ∑ y ∈ X₀,
                blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) c).symm
  have hrowSum :
      (∑ x ∈ X₀, ∑ y ∈ X₀,
        blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) ≤
        ((2 : ℝ) ^ h / N) *
          Real.exp (κ * ((n + N : ℕ) : ℝ)) *
            ∑ x ∈ X, ∑ z ∈ X,
              varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z := by
    calc
      _ ≤ ∑ x ∈ X₀,
            ((2 : ℝ) ^ h / N) *
              Real.exp (κ * ((n + N : ℕ) : ℝ)) *
                ∑ z ∈ X,
                  varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z := by
          apply Finset.sum_le_sum
          intro x hx
          exact hrowBound x hx
      _ = ((2 : ℝ) ^ h / N) *
          Real.exp (κ * ((n + N : ℕ) : ℝ)) *
            ∑ x ∈ X₀, ∑ z ∈ X,
              varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z := by
          let c : ℝ := (2 : ℝ) ^ h / N *
            Real.exp (κ * ((n + N : ℕ) : ℝ))
          change (∑ x ∈ X₀, c *
              ∑ z ∈ X,
                varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z) =
            c * ∑ x ∈ X₀, ∑ z ∈ X,
              varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z
          exact (Finset.mul_sum X₀
            (fun x => ∑ z ∈ X,
              varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z) c).symm
      _ ≤ ((2 : ℝ) ^ h / N) *
          Real.exp (κ * ((n + N : ℕ) : ℝ)) *
            ∑ x ∈ X, ∑ z ∈ X,
              varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z := by
          have hXsubset : X₀ ⊆ X := by
            intro x hx
            apply Fintype.mem_piFinset.mpr
            intro i
            exact hA₀sub (Fintype.mem_piFinset.mp hx i)
          have hpathnn (x z : Fin h → Site) :
              0 ≤ varianceWeightedHattedPairWordPath L κ β ⊥
                (List.ofFn w.1) x z :=
            varianceWeightedHattedPairWordPath_nonneg L κ β ⊥ (List.ofFn w.1) x z
          have hsumMono :
              (∑ x ∈ X₀, ∑ z ∈ X,
                varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z) ≤
              ∑ x ∈ X, ∑ z ∈ X,
                varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hXsubset
            intro x hx hnot
            exact Finset.sum_nonneg fun z hz => hpathnn x z
          exact mul_le_mul_of_nonneg_left hsumMono (by positivity)
  calc
    _ ≤ testedBlockWord ϑ N s t ψ (List.ofFn w.1) :=
      abs_testedBlockWord_le_abs_testedBlockWord ϑ N s t φ (List.ofFn w.1)
    _ = ∑ x ∈ X₀, ∑ y ∈ X₀,
          (∏ i, cellTestWeight N (ψ i) (x i) (y i)) *
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := hfinite
    _ ≤ (4 * M / N) ^ h *
          ((2 : ℝ) ^ h / N) *
            Real.exp (κ * ((n + N : ℕ) : ℝ)) *
              ∑ x ∈ X, ∑ z ∈ X,
                varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z := by
          calc
            _ ≤ (4 * M / N) ^ h *
                ∑ x ∈ X₀, ∑ y ∈ X₀,
                  blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := hsumBound
            _ ≤ _ := by
                have hc : 0 ≤ (4 * M / N) ^ h := by positivity
                calc
                  _ = (4 * M / N) ^ h *
                      ((∑ x ∈ X₀, ∑ y ∈ X₀,
                        blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y)) := by ring
                  _ ≤ (4 * M / N) ^ h *
                      (((2 : ℝ) ^ h / N) *
                        Real.exp (κ * ((n + N : ℕ) : ℝ)) *
                          ∑ x ∈ X, ∑ z ∈ X,
                            varianceWeightedHattedPairWordPath L κ β ⊥
                              (List.ofFn w.1) x z) :=
                    mul_le_mul_of_nonneg_left hrowSum hc
                  _ = _ := by ring

end Critical2DKPZ.SHF.Moments

end
