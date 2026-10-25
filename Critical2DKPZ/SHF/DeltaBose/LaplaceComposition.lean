/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CausalComposition
public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
public import Critical2DKPZ.SHF.DeltaBose.PathKernel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-!
# Laplace transforms of causal positive kernels

Positive temporal composition becomes spatial kernel composition after a
Laplace transform. The causal extension and positive-time translation are
kept explicit so Tonelli applies without finiteness assumptions.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The positive scalar Laplace weight. -/
noncomputable def laplaceTimeWeight (rate t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rate * t)))

/-- Time integration of a kernel against the positive Laplace weight. -/
noncomputable def laplaceTimeKernel {X Y : Type*} (rate : ℝ) (K : TimeKernel X Y)
    (x : X) (y : Y) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), laplaceTimeWeight rate t * K (t, x, y)

/-- The Laplace transform preserves joint measurability of a time kernel. -/
theorem measurable_laplaceTimeKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rate : ℝ) {K : TimeKernel X Y} (hK : Measurable K) :
    Measurable (Function.uncurry (laplaceTimeKernel rate K)) := by
  have hW : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
    unfold laplaceTimeWeight
    fun_prop
  have hF : Measurable (fun p : (X × Y) × ℝ =>
      laplaceTimeWeight rate p.2 * K (p.2, p.1.1, p.1.2)) := by
    exact (hW.comp measurable_snd).mul (hK.comp (by fun_prop))
  exact hF.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

/-- Causal extension does not change a positive-time Laplace transform. -/
theorem laplaceTimeKernel_causalKernel {X Y : Type*} (rate : ℝ)
    (K : TimeKernel X Y) (x : X) (y : Y) :
    laplaceTimeKernel rate (causalKernel K) x y = laplaceTimeKernel rate K x y := by
  unfold laplaceTimeKernel
  rw [← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht : 0 < t
  · simp [Set.indicator, ht, causalKernel_of_pos K ht]
  · simp [Set.indicator, ht]

/-- Translating the positive half-line in a causal integrand contributes the
corresponding exponential factor. -/
theorem lintegral_laplace_causal_translate {rate q : ℝ} (hq : 0 < q)
    (F : ℝ → ℝ≥0∞) (hF : ∀ s ≤ 0, F s = 0) :
    (∫⁻ t in Ioi (0 : ℝ), laplaceTimeWeight rate t * F (t - q)) =
      laplaceTimeWeight rate q *
        ∫⁻ s in Ioi (0 : ℝ), laplaceTimeWeight rate s * F s := by
  let G : ℝ → ℝ≥0∞ := fun t => laplaceTimeWeight rate t * F (t - q)
  have hset : (Ioi (0 : ℝ)).indicator G = (Ioi q).indicator G := by
    funext t
    by_cases htq : q < t
    · by_cases ht0 : 0 < t
      · simp [Set.indicator, ht0, htq, G]
      · have ht0' : t ≤ 0 := le_of_not_gt ht0
        have harg : t - q ≤ 0 := by linarith
        simp [Set.indicator, ht0, htq, G, hF (t - q) harg]
    · have htle : t ≤ q := le_of_not_gt htq
      have harg : t - q ≤ 0 := sub_nonpos.mpr htle
      by_cases ht0 : 0 < t
      · simp [Set.indicator, ht0, htq, G, hF (t - q) harg]
      · simp [Set.indicator, ht0, htq, G]
  have hrestrict :
      (∫⁻ t in Ioi (0 : ℝ), G t) = ∫⁻ t in Ioi q, G t := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    rw [hset]
  have htrans : (∫⁻ t in Ioi q, G t) =
      ∫⁻ s in Ioi (0 : ℝ), laplaceTimeWeight rate (s + q) * F s := by
    let H : ℝ → ℝ≥0∞ := fun s => laplaceTimeWeight rate (s + q) * F s
    have hm : MeasurePreserving (fun t : ℝ => t - q) := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-q)
    have he := hm.lintegral_comp_emb (MeasurableEquiv.subRight q).measurableEmbedding
      ((Ioi (0 : ℝ)).indicator H)
    have hi : (fun t : ℝ => (Ioi (0 : ℝ)).indicator H (t - q)) =
        (Ioi q).indicator (fun t => H (t - q)) := by
      funext t
      by_cases ht : q < t
      · simp [Set.indicator, ht, sub_pos.mpr ht]
      · have harg : t - q ≤ 0 := sub_nonpos.mpr (le_of_not_gt ht)
        simp [Set.indicator, ht, not_lt.mpr harg]
    rw [hi, lintegral_indicator measurableSet_Ioi,
      lintegral_indicator measurableSet_Ioi] at he
    simpa only [H, G, sub_add_cancel] using he
  have hexp (s : ℝ) : laplaceTimeWeight rate (s + q) =
      laplaceTimeWeight rate q * laplaceTimeWeight rate s := by
    unfold laplaceTimeWeight
    rw [show -(rate * (s + q)) = -(rate * q) + -(rate * s) by ring, Real.exp_add,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc (∫⁻ t in Ioi (0 : ℝ), laplaceTimeWeight rate t * F (t - q))
      = ∫⁻ t in Ioi q, G t := hrestrict
    _ = ∫⁻ s in Ioi (0 : ℝ), laplaceTimeWeight rate (s + q) * F s := htrans
    _ = laplaceTimeWeight rate q *
          ∫⁻ s in Ioi (0 : ℝ), laplaceTimeWeight rate s * F s := by
          rw [show (fun s : ℝ => laplaceTimeWeight rate (s + q) * F s) =
            fun s => laplaceTimeWeight rate q * (laplaceTimeWeight rate s * F s) by
              funext s
              rw [hexp, mul_assoc]]
          rw [lintegral_const_mul' _ _ (by
            unfold laplaceTimeWeight
            exact ENNReal.ofReal_ne_top)]

/-- Integrating a causal time composition against an exponential weight
turns it into spatial composition of the two Laplace transforms. -/
theorem laplaceTimeKernel_timeKernelComp_causal {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) [SFinite ν] {K : TimeKernel X Y} {L : TimeKernel Y Z}
    (hK : Measurable K) (hL : Measurable L) (rate : ℝ) (x : X) (z : Z) :
    laplaceTimeKernel rate (timeKernelComp ν (causalKernel K) (causalKernel L)) x z =
      spatialKernelComp ν (laplaceTimeKernel rate K) (laplaceTimeKernel rate L) x z := by
  let Kc := causalKernel K
  let Lc := causalKernel L
  let H : Y → ℝ≥0∞ := fun y => laplaceTimeKernel rate Lc y z
  have hKc : Measurable Kc := measurable_causalKernel hK
  have hLc : Measurable Lc := measurable_causalKernel hL
  have hH : Measurable H := by
    exact (measurable_laplaceTimeKernel rate hLc).comp
      (measurable_id.prodMk measurable_const)
  have hF : Measurable (fun p : ℝ × (ℝ × Y) =>
      laplaceTimeWeight rate p.1 *
        (Kc (p.2.1, x, p.2.2) * Lc (p.1 - p.2.1, p.2.2, z))) := by
    exact (by
      have hW : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
        unfold laplaceTimeWeight
        fun_prop
      exact (hW.comp measurable_fst).mul
        ((hKc.comp (by fun_prop)).mul (hLc.comp (by fun_prop))))
  have hA : Measurable (fun p : ℝ × Y =>
      Kc (p.1, x, p.2) * (laplaceTimeWeight rate p.1 * H p.2)) := by
    have hW : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
      unfold laplaceTimeWeight
      fun_prop
    exact (hKc.comp (by fun_prop)).mul
      ((hW.comp measurable_fst).mul (hH.comp measurable_snd))
  calc
    laplaceTimeKernel rate (timeKernelComp ν Kc Lc) x z
        = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ q : ℝ × Y,
            laplaceTimeWeight rate t *
              (Kc (q.1, x, q.2) * Lc (t - q.1, q.2, z)) ∂(volume.prod ν) := by
          rw [laplaceTimeKernel]
          apply lintegral_congr
          intro t
          rw [timeKernelComp]
          change laplaceTimeWeight rate t *
              (∫⁻ q : ℝ × Y, Kc (q.1, x, q.2) * Lc (t - q.1, q.2, z)
                ∂(volume.prod ν)) =
            ∫⁻ q : ℝ × Y, laplaceTimeWeight rate t *
              (Kc (q.1, x, q.2) * Lc (t - q.1, q.2, z)) ∂(volume.prod ν)
          exact (lintegral_const_mul _
            ((hKc.comp (by fun_prop)).mul (hLc.comp (by fun_prop)))).symm
    _ = ∫⁻ q : ℝ × Y, ∫⁻ t in Ioi (0 : ℝ),
          laplaceTimeWeight rate t *
            (Kc (q.1, x, q.2) * Lc (t - q.1, q.2, z)) ∂volume ∂(volume.prod ν) := by
          exact lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ q : ℝ × Y, Kc (q.1, x, q.2) *
          (laplaceTimeWeight rate q.1 * H q.2) ∂(volume.prod ν) := by
          apply lintegral_congr
          intro q
          by_cases hq : 0 < q.1
          · rw [show (fun t : ℝ => laplaceTimeWeight rate t *
                (Kc (q.1, x, q.2) * Lc (t - q.1, q.2, z))) =
                fun t => Kc (q.1, x, q.2) *
                  (laplaceTimeWeight rate t * Lc (t - q.1, q.2, z)) by
                  funext t
                  ac_rfl]
            have hInner : Measurable (fun t : ℝ =>
                laplaceTimeWeight rate t * Lc (t - q.1, q.2, z)) := by
              have hW : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
                unfold laplaceTimeWeight
                fun_prop
              exact (hW.mul (hLc.comp (by fun_prop)))
            rw [lintegral_const_mul _ hInner]
            · rw [lintegral_laplace_causal_translate (rate := rate) (q := q.1) hq
                (fun s => Lc (s, q.2, z)) (by
                  intro s hs
                  exact causalKernel_of_nonpos L hs q.2 z)]
              simp [H, laplaceTimeKernel]
          · have hqn : q.1 ≤ 0 := le_of_not_gt hq
            change (∫⁻ t in Ioi (0 : ℝ), laplaceTimeWeight rate t *
              (causalKernel K (q.1, x, q.2) *
                Lc (t - q.1, q.2, z))) = _
            rw [causalKernel_of_nonpos K hqn]
            simp [Kc, causalKernel_of_nonpos K hqn]
    _ = ∫⁻ y, (laplaceTimeKernel rate K x y) * H y ∂ν := by
          rw [lintegral_prod _ hA.aemeasurable]
          rw [lintegral_lintegral_swap hA.aemeasurable]
          apply lintegral_congr
          intro y
          rw [show (fun r : ℝ => Kc (r, x, y) * (laplaceTimeWeight rate r * H y)) =
              fun r => (Kc (r, x, y) * laplaceTimeWeight rate r) * H y by
                funext r
                ac_rfl]
          have hKr : Measurable (fun r : ℝ =>
              Kc (r, x, y) * laplaceTimeWeight rate r) := by
            have hW : Measurable (fun r : ℝ => laplaceTimeWeight rate r) := by
              unfold laplaceTimeWeight
              fun_prop
            exact (hKc.comp (by fun_prop)).mul hW
          rw [lintegral_mul_const _ hKr]
          · rw [show (fun r : ℝ => Kc (r, x, y) * laplaceTimeWeight rate r) =
                fun r => (Ioi (0 : ℝ)).indicator
                  (fun r => laplaceTimeWeight rate r * K (r, x, y)) r by
                funext r
                by_cases hr : 0 < r
                · simp [Set.indicator, hr, Kc, mul_comm]
                · have hrn : r ≤ 0 := le_of_not_gt hr
                  simp [Set.indicator, hr, Kc, hrn]]
            rw [lintegral_indicator measurableSet_Ioi]
            rfl
    _ = spatialKernelComp ν (laplaceTimeKernel rate K) (laplaceTimeKernel rate L) x z := by
          rw [spatialKernelComp]
          apply lintegral_congr
          intro y
          change laplaceTimeKernel rate K x y *
            laplaceTimeKernel rate (causalKernel L) y z = _
          rw [laplaceTimeKernel_causalKernel rate L y z]

/-- The Laplace transform of a chronological collision word is the spatial
composition of its integrated incoming, collision, and later-word blocks. -/
theorem laplaceTimeKernel_pathTimeKernel_cons {n : ℕ} (θ rate : ℝ)
    (α : CollisionPair n) (w : List (CollisionPair n)) {X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y]
    {eX : X → Configuration n} {eY : Y → Configuration n}
    (hX : Measurable eX) (hY : Measurable eY) (x : X) (y : Y) :
    laplaceTimeKernel rate (pathTimeKernel θ (α :: w) eX eY) x y =
      spatialKernelComp (X := X) (Y := FusedConfiguration α) (Z := Y) volume
        (laplaceTimeKernel rate
        (freeTimeKernel eX (collisionEmbedding α)))
        (spatialKernelComp (X := FusedConfiguration α)
          (Y := FusedConfiguration α) (Z := Y) volume (laplaceTimeKernel rate
          (collisionTimeKernel α θ))
          (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) eY))) x y := by
  let G : TimeKernel (FusedConfiguration α) Y :=
    timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
      (pathTimeKernel θ w (collisionEmbedding α) eY)
  have hPathC : causalKernel (pathTimeKernel θ w (collisionEmbedding α) eY) =
      pathTimeKernel θ w (collisionEmbedding α) eY :=
    pathTimeKernel_causal θ w (collisionEmbedding α) eY
  have hGcausal : causalKernel G = G := by
    have h := timeKernelComp_causal volume (collisionTimeKernel α θ)
      (pathTimeKernel θ w (collisionEmbedding α) eY)
    simpa [G, hPathC] using h
  have hGmeas : Measurable G := by
    exact measurable_timeKernelComp volume
      (measurable_causalKernel (measurable_collisionTimeKernel α θ))
      (measurable_pathTimeKernel θ w (measurable_collisionEmbedding α) hY)
  have hOuter := laplaceTimeKernel_timeKernelComp_causal volume
    (measurable_freeTimeKernel hX (measurable_collisionEmbedding α)) hGmeas rate x y
  have hInner : laplaceTimeKernel rate G =
      spatialKernelComp (X := FusedConfiguration α) (Y := FusedConfiguration α) (Z := Y)
        volume (laplaceTimeKernel rate (collisionTimeKernel α θ))
        (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) eY)) := by
    funext a b
    simpa [G, hPathC] using
      (laplaceTimeKernel_timeKernelComp_causal volume
        (measurable_collisionTimeKernel α θ)
        (measurable_pathTimeKernel θ w (measurable_collisionEmbedding α) hY)
        rate a b)
  calc
    laplaceTimeKernel rate (pathTimeKernel θ (α :: w) eX eY) x y =
        laplaceTimeKernel rate
          (timeKernelComp volume (causalKernel (freeTimeKernel eX (collisionEmbedding α)))
            (causalKernel G)) x y := by
              change laplaceTimeKernel rate
                (timeKernelComp volume
                  (causalKernel (freeTimeKernel eX (collisionEmbedding α))) G) x y = _
              rw [hGcausal]
    _ = spatialKernelComp volume
          (laplaceTimeKernel rate (freeTimeKernel eX (collisionEmbedding α)))
          (laplaceTimeKernel rate G) x y := hOuter
    _ = spatialKernelComp volume
          (laplaceTimeKernel rate (freeTimeKernel eX (collisionEmbedding α)))
          (spatialKernelComp volume (laplaceTimeKernel rate (collisionTimeKernel α θ))
            (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) eY))) x y := by
              rw [hInner]

/-- The Laplace transform of a collision block is its damped resolvent. -/
theorem laplaceTimeKernel_collisionTimeKernel {n : ℕ} (α : CollisionPair n)
    (θ rate : ℝ) (z w : FusedConfiguration α) :
    laplaceTimeKernel rate (collisionTimeKernel α θ) z w =
      collisionResolvent α θ rate z w := by
  rfl

/-- A nonnegative Laplace rate only decreases the integrated swapping kernel. -/
theorem laplaceTimeKernel_swapping_le_integrated {n : ℕ} (α β : CollisionPair n)
    {rate : ℝ} (hrate : 0 ≤ rate) (z : FusedConfiguration α) (w : FusedConfiguration β) :
    laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)) z w ≤
      integratedSwappingKernel α β z w := by
  unfold laplaceTimeKernel integratedSwappingKernel
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hexp : Real.exp (-(rate * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hrate ht.le))
  have hweight : laplaceTimeWeight rate t ≤ 1 := by
    unfold laplaceTimeWeight
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hexp
  change laplaceTimeWeight rate t * ENNReal.ofReal (swappingKernel α β t z w) ≤ _
  exact (mul_le_mul' hweight le_rfl).trans_eq (one_mul _)

/-- The damped Laplace transform of a swapping block inherits the integrated
Schur bound. -/
theorem laplaceTimeKernel_swapping_l2_sq_le {n : ℕ} (α β : CollisionPair n)
    (hne : α ≠ β) {rate : ℝ} (hrate : 0 ≤ rate)
    {f : FusedConfiguration β → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ w : FusedConfiguration β,
        laplaceTimeKernel rate
          (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)) z w * f w) ^ 2) ≤
      integratedPotentialRowConstant ^ 2 *
        ∫⁻ w : FusedConfiguration β, f w ^ 2 := by
  calc
    _ ≤ ∫⁻ z : FusedConfiguration α,
        (∫⁻ w : FusedConfiguration β,
          integratedSwappingKernel α β z w * f w) ^ 2 := by
          apply lintegral_mono
          intro z
          have hAct :
              (∫⁻ w : FusedConfiguration β,
                laplaceTimeKernel rate
                  (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)) z w * f w) ≤
              ∫⁻ w : FusedConfiguration β, integratedSwappingKernel α β z w * f w := by
            apply lintegral_mono
            intro w
            exact mul_le_mul' (laplaceTimeKernel_swapping_le_integrated α β hrate z w) le_rfl
          exact pow_le_pow_left₀ (by positivity) hAct 2
    _ ≤ integratedPotentialRowConstant ^ 2 *
          ∫⁻ w : FusedConfiguration β, f w ^ 2 :=
        integratedSwappingKernel_l2_sq_le α β hne hf






end Critical2DKPZ.DeltaBose
