/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.ConditionalFlat
import Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.Tactic

/-! # Spatial first-collision expansion for terminal observables -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.Collision

open Critical2DKPZ.Polymer

/-- The two free heat kernels tested against a future terminal second moment. -/
def terminalCollisionHeat (r : ℕ) (w v : Site) (F : Site → ℝ) : ℝ :=
  ∑' z, srwKernel r (z - w) * srwKernel r (z - v) * F z


/-- A simultaneous free step advances both kernels in the collision heat. -/
theorem pairStep_terminalCollisionHeat_succ (r : ℕ) (w v : Site) (F : Site → ℝ) :
    pairStep (fun x y => terminalCollisionHeat r x y F) w v =
      terminalCollisionHeat (r + 1) w v F := by
  let c : ℝ := (4 : ℝ)⁻¹
  have hterm (i j : Fin 4) :
      Summable (fun z =>
        (c * srwKernel r (z - (w + srwStep i))) *
          (c * srwKernel r (z - (v + srwStep j))) * F z) := by
    apply summable_of_ne_finset_zero (s := endpoints (w + srwStep i) r)
    intro z hz
    rw [srwKernel_eq_zero_of_not_mem r (w + srwStep i) z hz]
    simp [c]
  have hsumJ (i : Fin 4) :
      Summable (fun z => ∑ j : Fin 4,
        (c * srwKernel r (z - (w + srwStep i))) *
          (c * srwKernel r (z - (v + srwStep j))) * F z) := by
    apply summable_of_ne_finset_zero (s := endpoints (w + srwStep i) r)
    intro z hz
    apply Finset.sum_eq_zero
    intro j hj
    rw [srwKernel_eq_zero_of_not_mem r (w + srwStep i) z hz]
    simp [c]
  unfold pairStep
  change (∑ i : Fin 4, ∑ j : Fin 4,
      ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹) *
        (∑' z, srwKernel r (z - (w + srwStep i)) *
          srwKernel r (z - (v + srwStep j)) * F z)) = _
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑' z,
        (c * srwKernel r (z - (w + srwStep i))) *
          (c * srwKernel r (z - (v + srwStep j))) * F z := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      simp only [c]
      ring
    _ = ∑ i : Fin 4, ∑' z, ∑ j : Fin 4,
        (c * srwKernel r (z - (w + srwStep i))) *
          (c * srwKernel r (z - (v + srwStep j))) * F z := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Summable.tsum_finsetSum (fun j hj => hterm i j)).symm
    _ = ∑' z, ∑ i : Fin 4, ∑ j : Fin 4,
        (c * srwKernel r (z - (w + srwStep i))) *
          (c * srwKernel r (z - (v + srwStep j))) * F z := by
      exact (Summable.tsum_finsetSum (s := Finset.univ)
        (fun i hi => hsumJ i)).symm
    _ = terminalCollisionHeat (r + 1) w v F := by
      unfold terminalCollisionHeat
      apply tsum_congr
      intro z
      have hqw : srwKernel (r + 1) (z - w) =
          ∑ i : Fin 4, c * srwKernel r (z - (w + srwStep i)) := by
        rw [Critical2DKPZ.srwKernel_succ, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← sub_add_eq_sub_sub]
        simp only [div_eq_mul_inv]
        dsimp [c]
        ring
      have hqv : srwKernel (r + 1) (z - v) =
          ∑ j : Fin 4, c * srwKernel r (z - (v + srwStep j)) := by
        rw [Critical2DKPZ.srwKernel_succ, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← sub_add_eq_sub_sub]
        simp only [div_eq_mul_inv]
        dsimp [c]
        ring
      have hprod :
          (∑ i : Fin 4, ∑ j : Fin 4,
            (c * srwKernel r (z - (w + srwStep i)) *
              (c * srwKernel r (z - (v + srwStep j)))) * F z) =
            (∑ i : Fin 4, c * srwKernel r (z - (w + srwStep i))) *
              (∑ j : Fin 4, c * srwKernel r (z - (v + srwStep j))) * F z := by
        calc
          _ = (∑ i : Fin 4, ∑ j : Fin 4,
              c * srwKernel r (z - (w + srwStep i)) *
                (c * srwKernel r (z - (v + srwStep j)))) * F z := by
                calc
                  _ = ∑ i : Fin 4,
                      (∑ j : Fin 4,
                        c * srwKernel r (z - (w + srwStep i)) *
                          (c * srwKernel r (z - (v + srwStep j)))) * F z := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact (Finset.sum_mul Finset.univ (fun j =>
                      c * srwKernel r (z - (w + srwStep i)) *
                        (c * srwKernel r (z - (v + srwStep j))) ) (F z)).symm
                  _ = _ := by
                    exact (Finset.sum_mul Finset.univ (fun i =>
                      ∑ j : Fin 4,
                        c * srwKernel r (z - (w + srwStep i)) *
                          (c * srwKernel r (z - (v + srwStep j)))) (F z)).symm
          _ = _ := congrArg (fun x : ℝ => x * F z)
            (Fintype.sum_mul_sum
              (fun i : Fin 4 => c * srwKernel r (z - (w + srwStep i)))
              (fun j : Fin 4 => c * srwKernel r (z - (v + srwStep j)))).symm
      rw [hqw, hqv]
      calc
        ∑ i : Fin 4, ∑ j : Fin 4,
            ((c * srwKernel r (z - (w + srwStep i))) *
              (c * srwKernel r (z - (v + srwStep j)))) * F z =
            (∑ i : Fin 4, c * srwKernel r (z - (w + srwStep i))) *
              (∑ j : Fin 4, c * srwKernel r (z - (v + srwStep j))) * F z := hprod
        _ = _ := by ring

/-- The terminal collision heat at time zero evaluates the profile when the two starting sites coincide. -/
theorem terminalCollisionHeat_zero (w v : Site) (F : Site → ℝ) :
    terminalCollisionHeat 0 w v F = if w = v then F w else 0 := by
  unfold terminalCollisionHeat
  by_cases h : w = v
  · subst v
    simp [srwKernel_zero, sub_eq_zero, eq_comm]
  · have hz (z : Site) :
        srwKernel 0 (z - w) * srwKernel 0 (z - v) * F z = 0 := by
      rw [srwKernel_zero, srwKernel_zero]
      by_cases hzw : z = w
      · subst z
        simp [h, sub_eq_zero]
      · simp [hzw, sub_eq_zero, eq_comm]
    simp_rw [hz]
    simp [h]

/-- The terminal walk mean at time zero evaluates the original profile. -/
@[simp]
theorem terminalWalkMean_zero (w : Site) (f : Site → ℝ) :
    terminalWalkMean 0 w f = f w := by
  simp [terminalWalkMean, srwKernel_zero, sub_eq_zero, eq_comm]

/-- The terminal pair moment at time zero is the product of the two profile values. -/
@[simp]
theorem terminalPairMoment_zero (β : ℝ) (w v : Site) (f g : Site → ℝ) :
    terminalPairMoment β 0 w v f g = f w * g v := by
  simp [terminalPairMoment]

/-- One independent pair step advances both terminal walk means by one time unit. -/
theorem pairStep_terminalWalkMean_mul (n : ℕ) (w v : Site)
    (f g : Site → ℝ) :
    pairStep (fun x y => terminalWalkMean n x f * terminalWalkMean n y g) w v =
      terminalWalkMean (n + 1) w f * terminalWalkMean (n + 1) v g := by
  rw [terminalWalkMean_succ, terminalWalkMean_succ]
  unfold pairStep
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        ((4 : ℝ)⁻¹ * terminalWalkMean n (w + srwStep i) f) *
          ((4 : ℝ)⁻¹ * terminalWalkMean n (v + srwStep j) g) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i : Fin 4,
          (4 : ℝ)⁻¹ * terminalWalkMean n (w + srwStep i) f) *
        (∑ j : Fin 4,
          (4 : ℝ)⁻¹ * terminalWalkMean n (v + srwStep j) g) :=
      (Fintype.sum_mul_sum _ _).symm

/-- A constant factor passes through the independent pair step. -/
theorem pairStep_const_mul (c : ℝ) (H : Site → Site → ℝ) (w v : Site) :
    pairStep (fun x y => c * H x y) w v = c * pairStep H w v := by
  unfold pairStep
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        c * ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹ * H (w + srwStep i) (v + srwStep j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ i : Fin 4, ∑ j : Fin 4,
        (4 : ℝ)⁻¹ * (4 : ℝ)⁻¹ * H (w + srwStep i) (v + srwStep j) := by
      calc
        _ = ∑ i : Fin 4, c * ∑ j : Fin 4,
            (4 : ℝ)⁻¹ * (4 : ℝ)⁻¹ * H (w + srwStep i) (v + srwStep j) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.mul_sum Finset.univ (fun j : Fin 4 =>
            (4 : ℝ)⁻¹ * (4 : ℝ)⁻¹ * H (w + srwStep i) (v + srwStep j)) c).symm
        _ = _ := (Finset.mul_sum Finset.univ (fun i : Fin 4 =>
          ∑ j : Fin 4,
            (4 : ℝ)⁻¹ * (4 : ℝ)⁻¹ * H (w + srwStep i) (v + srwStep j)) c).symm

/-- One pair step applied to the diagonal pair moment equals the one step terminal collision heat. -/
theorem pairStep_terminalPairDiagonal (β : ℝ) (n : ℕ) (w v : Site)
    (f g : Site → ℝ) :
    pairStep (fun x y =>
      if x = y then terminalPairMoment β n x y f g else 0) w v =
        terminalCollisionHeat 1 w v
          (fun z => terminalPairMoment β n z z f g) := by
  let F : Site → ℝ := fun z => terminalPairMoment β n z z f g
  have hfun : (fun x y =>
      if x = y then terminalPairMoment β n x y f g else 0) =
        fun x y => terminalCollisionHeat 0 x y F := by
    funext x y
    rw [terminalCollisionHeat_zero]
    by_cases h : x = y <;> simp [F, h]
  rw [hfun, pairStep_terminalCollisionHeat_succ]

/-- First selected common noise for a general terminal observable. -/
theorem terminalPairMoment_firstCollision (β : ℝ) (n : ℕ) (w v : Site)
    (f g : Site → ℝ) :
    terminalPairMoment β n w v f g =
      terminalWalkMean n w f * terminalWalkMean n v g +
        sigmaSq β * ∑ r ∈ Finset.Icc 1 n,
          terminalCollisionHeat r w v
            (fun z => terminalPairMoment β (n - r) z z f g) := by
  induction n generalizing w v with
  | zero => simp
  | succ n ih =>
    rw [terminalPairMoment_recurrence]
    have hdecomp : (fun x y => terminalPairMoment β n x y f g) =
        fun x y => terminalWalkMean n x f * terminalWalkMean n y g +
          sigmaSq β * ∑ r ∈ Finset.Icc 1 n,
            terminalCollisionHeat r x y
              (fun z => terminalPairMoment β (n - r) z z f g) := by
      funext x y
      exact ih x y
    have hsum :
        (∑ r ∈ Finset.Icc 1 (n + 1),
          terminalCollisionHeat r w v
            (fun z => terminalPairMoment β (n + 1 - r) z z f g)) =
          terminalCollisionHeat 1 w v
            (fun z => terminalPairMoment β n z z f g) +
          ∑ r ∈ Finset.Icc 1 n,
            terminalCollisionHeat (r + 1) w v
              (fun z => terminalPairMoment β (n - r) z z f g) := by
      rw [sum_Icc_first]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      funext z
      congr 1
      omega
    have hpairSum :
        pairStep (fun x y =>
          ∑ r ∈ Finset.Icc 1 n,
            terminalCollisionHeat r x y
              (fun z => terminalPairMoment β (n - r) z z f g)) w v =
          ∑ r ∈ Finset.Icc 1 n,
            terminalCollisionHeat (r + 1) w v
              (fun z => terminalPairMoment β (n - r) z z f g) := by
      rw [pairStep_sum]
      apply Finset.sum_congr rfl
      intro r hr
      exact pairStep_terminalCollisionHeat_succ r w v
        (fun z => terminalPairMoment β (n - r) z z f g)
    calc
      _ = pairStep (fun x y => terminalWalkMean n x f * terminalWalkMean n y g) w v +
            sigmaSq β *
              pairStep (fun x y =>
                ∑ r ∈ Finset.Icc 1 n,
                  terminalCollisionHeat r x y
                    (fun z => terminalPairMoment β (n - r) z z f g)) w v +
            sigmaSq β * pairStep (fun x y =>
              if x = y then terminalPairMoment β n x y f g else 0) w v := by
        rw [hdecomp, pairStep_add, pairStep_const_mul, pairStep_sum]
      _ = terminalWalkMean (n + 1) w f * terminalWalkMean (n + 1) v g +
            sigmaSq β *
              (terminalCollisionHeat 1 w v
                  (fun z => terminalPairMoment β n z z f g) +
                ∑ r ∈ Finset.Icc 1 n,
                  terminalCollisionHeat (r + 1) w v
                    (fun z => terminalPairMoment β (n - r) z z f g)) := by
        rw [pairStep_terminalWalkMean_mul, hpairSum, pairStep_terminalPairDiagonal]
        ring
      _ = terminalWalkMean (n + 1) w f * terminalWalkMean (n + 1) v g +
            sigmaSq β * ∑ r ∈ Finset.Icc 1 (n + 1),
              terminalCollisionHeat r w v
                (fun z => terminalPairMoment β (n + 1 - r) z z f g) := by
        rw [hsum]

/-- A weighted collision kernel is the squared evolved signed profile against its weight. -/
theorem terminalCollisionProfileWeighted_tsum (r : ℕ) (A : Finset Site)
    (ν F : Site → ℝ) :
    (∑ w ∈ A, ∑ v ∈ A, ν w * ν v * terminalCollisionHeat r w v F) =
      ∑' z, (heatEvolveFinite r A ν z) ^ 2 * F z := by
  let C : Finset Site := A.biUnion fun w => endpoints w r
  have hsupport (z : Site) (hz : z ∉ C) : heatEvolveFinite r A ν z = 0 := by
    unfold heatEvolveFinite
    apply Finset.sum_eq_zero
    intro w hw
    have hzw : z ∉ endpoints w r := by
      intro hz'
      exact hz (Finset.mem_biUnion.mpr ⟨w, hw, hz'⟩)
    rw [srwKernel_eq_zero_of_not_mem r w z hzw, mul_zero]
  have hzero (w v : Site) (hw : w ∈ A) (z : Site) (hz : z ∉ C) :
      srwKernel r (z - w) * srwKernel r (z - v) * F z = 0 := by
    have hzw : z ∉ endpoints w r := by
      intro hz'
      exact hz (Finset.mem_biUnion.mpr ⟨w, hw, hz'⟩)
    rw [srwKernel_eq_zero_of_not_mem r w z hzw]
    simp
  have hcollision (w v : Site) (hw : w ∈ A) :
      terminalCollisionHeat r w v F =
        ∑ z ∈ C, srwKernel r (z - w) * srwKernel r (z - v) * F z := by
    unfold terminalCollisionHeat
    exact tsum_eq_sum (s := C) (hzero w v hw)
  have hpoint (z : Site) :
      (heatEvolveFinite r A ν z) ^ 2 * F z =
        ∑ w ∈ A, ∑ v ∈ A,
          (ν w * ν v) *
            (srwKernel r (z - w) * srwKernel r (z - v) * F z) := by
    unfold heatEvolveFinite
    rw [pow_two]
    calc
      _ = (∑ w ∈ A, ∑ v ∈ A,
          (ν w * srwKernel r (z - w)) * (ν v * srwKernel r (z - v))) * F z := by
        rw [Finset.sum_mul_sum]
      _ = ∑ w ∈ A, ∑ v ∈ A,
          ((ν w * srwKernel r (z - w)) * (ν v * srwKernel r (z - v))) * F z := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro v hv
        ring
  have hsupport2 (z : Site) (hz : z ∉ C) :
      (heatEvolveFinite r A ν z) ^ 2 * F z = 0 := by
    rw [hsupport z hz]
    simp
  rw [tsum_eq_sum (s := C) hsupport2]
  simp_rw [hpoint]
  calc
    _ = ∑ w ∈ A, ∑ v ∈ A, (ν w * ν v) *
          ∑ z ∈ C, srwKernel r (z - w) * srwKernel r (z - v) * F z := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      rw [← hcollision w v hw]
    _ = ∑ w ∈ A, ∑ z ∈ C, ∑ v ∈ A,
          (ν w * ν v) *
            (srwKernel r (z - w) * srwKernel r (z - v) * F z) := by
      apply Finset.sum_congr rfl
      intro w hw
      calc
        _ = ∑ v ∈ A, ∑ z ∈ C,
              (ν w * ν v) *
                (srwKernel r (z - w) * srwKernel r (z - v) * F z) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mul_sum]
        _ = ∑ z ∈ C, ∑ v ∈ A,
              (ν w * ν v) *
                (srwKernel r (z - w) * srwKernel r (z - v) * F z) := Finset.sum_comm
    _ = ∑ z ∈ C, ∑ w ∈ A, ∑ v ∈ A,
          (ν w * ν v) *
            (srwKernel r (z - w) * srwKernel r (z - v) * F z) := by
      rw [Finset.sum_comm]
    _ = _ := rfl

/-- The deterministic signed-profile variance is the weighted heat energy. -/
theorem terminalProfile_firstCollision_finite (β : ℝ) (n : ℕ) (A : Finset Site)
    (ν f : Site → ℝ) :
    (∑ w ∈ A, ∑ v ∈ A, ν w * ν v *
      (terminalPairMoment β n w v f f -
        terminalWalkMean n w f * terminalWalkMean n v f)) =
      sigmaSq β * ∑ r ∈ Finset.Icc 1 n, ∑' z,
        (heatEvolveFinite r A ν z) ^ 2 *
          terminalPairMoment β (n - r) z z f f := by
  have hpair (w v : Site) :
      terminalPairMoment β n w v f f -
        terminalWalkMean n w f * terminalWalkMean n v f =
          sigmaSq β * ∑ r ∈ Finset.Icc 1 n,
            terminalCollisionHeat r w v
              (fun z => terminalPairMoment β (n - r) z z f f) := by
    rw [terminalPairMoment_firstCollision]
    ring
  calc
    _ = ∑ w ∈ A, ∑ v ∈ A, ∑ r ∈ Finset.Icc 1 n,
          sigmaSq β * ((ν w * ν v) *
            terminalCollisionHeat r w v
              (fun z => terminalPairMoment β (n - r) z z f f)) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      rw [hpair, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ r ∈ Finset.Icc 1 n, ∑ w ∈ A, ∑ v ∈ A,
          sigmaSq β * ((ν w * ν v) *
            terminalCollisionHeat r w v
              (fun z => terminalPairMoment β (n - r) z z f f)) := by
      calc
        _ = ∑ w ∈ A, ∑ r ∈ Finset.Icc 1 n, ∑ v ∈ A,
              sigmaSq β * ((ν w * ν v) *
                terminalCollisionHeat r w v
                  (fun z => terminalPairMoment β (n - r) z z f f)) := by
          apply Finset.sum_congr rfl
          intro w hw
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = sigmaSq β * ∑ r ∈ Finset.Icc 1 n, ∑ w ∈ A, ∑ v ∈ A,
          (ν w * ν v) *
            terminalCollisionHeat r w v
              (fun z => terminalPairMoment β (n - r) z z f f) := by
      calc
        _ = ∑ r ∈ Finset.Icc 1 n, ∑ w ∈ A,
              sigmaSq β * ∑ v ∈ A,
                ((ν w * ν v) *
                  terminalCollisionHeat r w v
                    (fun z => terminalPairMoment β (n - r) z z f f)) := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro w hw
          rw [Finset.mul_sum]
        _ = ∑ r ∈ Finset.Icc 1 n, sigmaSq β * ∑ w ∈ A, ∑ v ∈ A,
              (ν w * ν v) *
                terminalCollisionHeat r w v
                  (fun z => terminalPairMoment β (n - r) z z f f) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
        _ = _ := (Finset.mul_sum (Finset.Icc 1 n) (fun r =>
          ∑ w ∈ A, ∑ v ∈ A,
            (ν w * ν v) *
              terminalCollisionHeat r w v
                (fun z => terminalPairMoment β (n - r) z z f f)) (sigmaSq β)).symm
    _ = sigmaSq β * ∑ r ∈ Finset.Icc 1 n, ∑' z,
          (heatEvolveFinite r A ν z) ^ 2 *
            terminalPairMoment β (n - r) z z f f := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact terminalCollisionProfileWeighted_tsum r A ν
        (fun z => terminalPairMoment β (n - r) z z f f)

/-- Conditional first-selected-collision formula for a past-measurable finite profile. -/
theorem condVar_randomTerminalProfilePolymer_eq_WFC (β : ℝ) (a b : ℕ)
    (hab : a ≤ b) (A : Finset Site) (η : Disorder → Site → ℝ) (f : Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (randomTerminalProfilePolymer β a b η f))
    (hXint : Integrable (randomTerminalProfilePolymer β a b η f) disorderLaw)
    (hX2meas : Measurable (fun ω => randomTerminalProfilePolymer β a b η f ω ^ 2))
    (hX2int : Integrable
      (fun ω => randomTerminalProfilePolymer β a b η f ω ^ 2) disorderLaw) :
    (fun ω =>
      disorderLaw[(fun ξ => randomTerminalProfilePolymer β a b η f ξ ^ 2) |
        disorderPast a] ω -
          (disorderLaw[randomTerminalProfilePolymer β a b η f | disorderPast a] ω) ^ 2) =ᵐ[
        disorderLaw] fun ω =>
          sigmaSq β * ∑ r ∈ Finset.Icc 1 (b - a), ∑' z,
            (heatEvolveFinite r A (η ω) z) ^ 2 *
              terminalPairMoment β (b - a - r) z z f f := by
  have hXprodmeas : Measurable (fun ω =>
      randomTerminalProfilePolymer β a b η f ω *
        randomTerminalProfilePolymer β a b η f ω) := by
    simpa only [pow_two] using hX2meas
  have hXprodint : Integrable (fun ω =>
      randomTerminalProfilePolymer β a b η f ω *
        randomTerminalProfilePolymer β a b η f ω) disorderLaw := by
    simpa only [pow_two] using hX2int
  have hmean := condExp_randomTerminalProfilePolymer β a b hab A η f
    hsupp hmeasη hXmeas hXint
  have hsecond := condExp_randomTerminalProfilePolymer_mul β a b hab A η f f
    hsupp hmeasη hXprodmeas hXprodint
  have hdet (ω : Disorder) :
      (∑ w ∈ A, ∑ v ∈ A, η ω w * η ω v *
        terminalPairMoment β (b - a) w v f f) -
          (∑ w ∈ A, η ω w * terminalWalkMean (b - a) w f) ^ 2 =
        sigmaSq β * ∑ r ∈ Finset.Icc 1 (b - a), ∑' z,
          (heatEvolveFinite r A (η ω) z) ^ 2 *
            terminalPairMoment β (b - a - r) z z f f := by
    have hmeanSq :
        (∑ w ∈ A, η ω w * terminalWalkMean (b - a) w f) ^ 2 =
          ∑ w ∈ A, ∑ v ∈ A,
            (η ω w * η ω v) *
              (terminalWalkMean (b - a) w f * terminalWalkMean (b - a) v f) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    have hdiff :
        (∑ w ∈ A, ∑ v ∈ A, η ω w * η ω v *
          terminalPairMoment β (b - a) w v f f) -
            (∑ w ∈ A, η ω w * terminalWalkMean (b - a) w f) ^ 2 =
          ∑ w ∈ A, ∑ v ∈ A, (η ω w * η ω v) *
            (terminalPairMoment β (b - a) w v f f -
              terminalWalkMean (b - a) w f * terminalWalkMean (b - a) v f) := by
      rw [hmeanSq]
      calc
        _ = ∑ w ∈ A,
            ((∑ v ∈ A, η ω w * η ω v *
                terminalPairMoment β (b - a) w v f f) -
              ∑ v ∈ A, (η ω w * η ω v) *
                (terminalWalkMean (b - a) w f * terminalWalkMean (b - a) v f)) := by
          rw [← Finset.sum_sub_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro v hv
          ring
    rw [hdiff]
    exact terminalProfile_firstCollision_finite β (b - a) A (η ω) f
  filter_upwards [hmean, hsecond] with ω hmeanω hsecondω
  have hsecondω' :
      disorderLaw[(fun ξ => randomTerminalProfilePolymer β a b η f ξ ^ 2) |
        disorderPast a] ω =
          ∑ w ∈ A, ∑ v ∈ A, η ω w * η ω v *
            terminalPairMoment β (b - a) w v f f := by
    simpa only [pow_two] using hsecondω
  rw [hsecondω', hmeanω]
  simpa only [terminalWalkMean] using hdet ω

end Critical2DKPZ.Collision

end
