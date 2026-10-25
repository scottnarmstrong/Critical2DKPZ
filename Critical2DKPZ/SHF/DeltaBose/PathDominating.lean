/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PathLaplaceBounds
public import Critical2DKPZ.SHF.DeltaBose.SupTimeKernel
public import Critical2DKPZ.SHF.DeltaBose.SupBlockBounds
import Mathlib.Tactic

/-!
# Supremum and Laplace majorants for collision paths

The dominating kernel recursively combines one pointwise-supremum block with
Laplace-integrated blocks. This is the kernel-level majorant used for path and
diagram form bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The recursively split supremum/Laplace dominating kernel of a collision
path, with a half-time split at each new letter. -/
noncomputable def pathDominatingKernel {n : ℕ} (θ rate : ℝ)
    (w : List (CollisionPair n)) {X : Type}
    (eX : X → Configuration n) (τ₀ : ℝ) : X → Configuration n → ℝ≥0∞ :=
  match w with
  | [] => supTimeKernel rate τ₀ (freeTimeKernel eX id)
  | α :: w => fun x y =>
      spatialKernelComp volume
        (supTimeKernel rate (τ₀ / 2) (freeTimeKernel eX (collisionEmbedding α)))
        (laplaceTimeKernel rate
          (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
            (pathTimeKernel θ w (collisionEmbedding α) id))) x y +
      spatialKernelComp volume
        (laplaceTimeKernel rate (freeTimeKernel eX (collisionEmbedding α)))
        (fun z y' =>
          spatialKernelComp volume
            (supTimeKernel rate (τ₀ / 4) (collisionTimeKernel α θ))
            (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) id)) z y' +
          spatialKernelComp volume
            (laplaceTimeKernel rate (collisionTimeKernel α θ))
            (pathDominatingKernel θ rate w (collisionEmbedding α) (τ₀ / 4)) z y') x y

/-- The empty path is dominated by its free-block pointwise supremum. -/
theorem pathTimeKernel_le_pathDominatingKernel_nil {n : ℕ}
    (θ rate : ℝ) {X : Type}
    (eX : X → Configuration n)
    {τ₀ τ : ℝ} (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ)
    (x : X) (y : Configuration n) :
    laplaceTimeWeight rate τ * pathTimeKernel θ [] eX id (τ, x, y) ≤
      pathDominatingKernel θ rate [] eX τ₀ x y := by
  rw [pathTimeKernel, pathDominatingKernel, causalKernel_of_pos _
    (lt_of_lt_of_le hτ₀ hτ)]
  exact le_supTimeKernel rate (freeTimeKernel eX id) hτ x y

private theorem lintegral_swap_restrict_time {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SFinite μ] (A : Set ℝ) (hA : MeasurableSet A)
    {F : ℝ → Y → ℝ≥0∞}
    (hF : Measurable (fun p : ℝ × Y => F p.1 p.2)) :
    (∫⁻ y, ∫⁻ t in A, F t y ∂volume ∂μ) =
      ∫⁻ t in A, ∫⁻ y, F t y ∂μ ∂volume := by
  classical
  let G : Y × ℝ → ℝ≥0∞ := fun p => if p.2 ∈ A then F p.2 p.1 else 0
  have hG : Measurable G := by
    apply Measurable.ite (measurableSet_preimage measurable_snd hA)
    · exact hF.comp measurable_swap
    · exact measurable_const
  calc
    (∫⁻ y, ∫⁻ t in A, F t y ∂volume ∂μ) =
        ∫⁻ y, ∫⁻ t, G (y, t) ∂volume ∂μ := by
          apply lintegral_congr
          intro y
          rw [← lintegral_indicator hA]
          apply lintegral_congr
          intro t
          simp [Set.indicator, G]
    _ = ∫⁻ t, ∫⁻ y, G (y, t) ∂μ ∂volume :=
          lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ t in A, ∫⁻ y, F t y ∂μ ∂volume := by
          rw [← lintegral_indicator hA]
          apply lintegral_congr
          intro t
          by_cases ht : t ∈ A <;> simp [G, ht, Set.indicator]

private theorem setLIntegral_reflect_sub {t : ℝ} (F : ℝ → ℝ≥0∞) :
    (∫⁻ r in Iio t, F (t - r) ∂volume) = ∫⁻ s in Ioi (0 : ℝ), F s ∂volume := by
  have hm : MeasurePreserving (fun r : ℝ => t - r) := volume.measurePreserving_sub_left t
  have h := hm.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.subLeft t).measurableEmbedding F (Ioi (0 : ℝ))
  have hpre' : (fun r : ℝ => t - r) ⁻¹' Ioi (0 : ℝ) = Iio t := by
    ext r
    change 0 < t - r ↔ r < t
    constructor <;> intro h <;> linarith
  rw [hpre'] at h
  exact h

private theorem laplaceTimeWeight_add (rate s t : ℝ) :
    laplaceTimeWeight rate (s + t) =
      laplaceTimeWeight rate s * laplaceTimeWeight rate t := by
  unfold laplaceTimeWeight
  rw [show -(rate * (s + t)) = -(rate * s) + -(rate * t) by ring,
    Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

private theorem continuousOn_freeKernel_time {n : ℕ} (x y : Configuration n) :
    ContinuousOn (fun t : ℝ => freeKernel n t x y) (Ioi 0) := by
  unfold freeKernel
  apply continuousOn_finsetProd
  intro i hi
  have hmap : Continuous (fun t : ℝ => (t, y i - x i)) := by fun_prop
  exact continuousOn_heatKernel.comp hmap.continuousOn (by
    intro t ht
    exact ht)

/-- The free time kernel is continuous in time on the positive half-line. -/
theorem continuousOn_freeTimeKernel_time {n : ℕ} {X Y : Type}
    {eX : X → Configuration n} {eY : Y → Configuration n}
    (x : X) (y : Y) :
    ContinuousOn (fun t : ℝ => freeTimeKernel eX eY (t, x, y)) (Ioi 0) := by
  change ContinuousOn
    (fun t : ℝ => ENNReal.ofReal (freeKernel n t (eX x) (eY y))) (Ioi 0)
  exact ENNReal.continuous_ofReal.continuousOn.comp
    (continuousOn_freeKernel_time (eX x) (eY y))
    (by intro t ht; exact Set.mem_univ _)

private theorem continuousOn_collisionKernel_time {n : ℕ} (α : CollisionPair n)
    (θ : ℝ) (y z : FusedConfiguration α) :
    ContinuousOn (fun t : ℝ => collisionKernel α θ t y z) (Ioi 0) := by
  have hscalarMap : Continuous (fun t : ℝ => (θ, t)) := by fun_prop
  have hscalar : ContinuousOn (fun t : ℝ => scalarDensity θ t) (Ioi 0) := by
    exact continuousOn_scalarDensity.comp hscalarMap.continuousOn (by
      intro t ht
      exact ht)
  have hcenterMap : Continuous (fun t : ℝ => (t / 2, z.1 - y.1)) := by fun_prop
  have hcenter : ContinuousOn (fun t : ℝ => heatKernel (t / 2) (z.1 - y.1))
      (Ioi 0) := by
    exact continuousOn_heatKernel.comp hcenterMap.continuousOn (by
      intro t ht
      change 0 < t / 2
      exact div_pos ht (by norm_num))
  have hspectator :
      ContinuousOn (fun t : ℝ => ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i))
        (Ioi 0) := by
    apply continuousOn_finsetProd
    intro i hi
    have hmap : Continuous (fun t : ℝ => (t, z.2 i - y.2 i)) := by fun_prop
    exact continuousOn_heatKernel.comp hmap.continuousOn (by
      intro t ht
      exact ht)
  unfold collisionKernel
  exact ((continuousOn_const.mul hscalar).mul hcenter).mul hspectator

/-- The collision time kernel is continuous in time on the positive half-line. -/
theorem continuousOn_collisionTimeKernel_time {n : ℕ} (α : CollisionPair n)
    (θ : ℝ) (y z : FusedConfiguration α) :
    ContinuousOn (fun t : ℝ => collisionTimeKernel α θ (t, y, z)) (Ioi 0) := by
  change ContinuousOn (fun t : ℝ => ENNReal.ofReal (collisionKernel α θ t y z)) (Ioi 0)
  exact ENNReal.continuous_ofReal.continuousOn.comp
    (continuousOn_collisionKernel_time α θ y z)
    (by intro t ht; exact Set.mem_univ _)

/-- One causal composition is bounded by splitting at half its total time:
the first block uses a pointwise supremum, or the remaining block uses its
given tail majorant. -/
private theorem laplaceTimeKernelComp_split {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) [SFinite μ] {K : TimeKernel X Y} {L : TimeKernel Y Z}
    (hK : Measurable K) (hL : Measurable L) (rate : ℝ)
    {τ₀ τ : ℝ} (hτ : τ₀ ≤ τ)
    (R : Y → Z → ℝ≥0∞)
    (hLtail : ∀ {s : ℝ}, τ₀ / 2 ≤ s → ∀ y z,
      laplaceTimeWeight rate s * L (s, y, z) ≤ R y z)
    (x : X) (z : Z) :
    laplaceTimeWeight rate τ *
        timeKernelComp μ (causalKernel K) (causalKernel L) (τ, x, z) ≤
      spatialKernelComp μ (supTimeKernel rate (τ₀ / 2) K)
          (laplaceTimeKernel rate L) x z +
        spatialKernelComp μ (laplaceTimeKernel rate K) R x z := by
  let W : ℝ → ℝ≥0∞ := fun s => laplaceTimeWeight rate s
  let F : ℝ → Y → ℝ≥0∞ := fun r y =>
    (W r * K (r, x, y)) * (W (τ - r) * L (τ - r, y, z))
  have hW : Measurable W := by
    dsimp [W, laplaceTimeWeight]
    fun_prop
  have hF : Measurable (fun p : ℝ × Y => F p.1 p.2) := by
    dsimp [F]
    exact ((hW.comp measurable_fst).mul (hK.comp (by fun_prop))).mul
      ((hW.comp (by fun_prop)).mul (hL.comp (by fun_prop)))
  have hweightTop (s : ℝ) : W s ≠ ⊤ := by
    simp [W, laplaceTimeWeight]
  have hleft :
      W τ * timeKernelComp μ (causalKernel K) (causalKernel L) (τ, x, z) =
        ∫⁻ r in Ioo (0 : ℝ) τ, ∫⁻ y, F r y ∂μ ∂volume := by
    rw [timeKernelComp_causal_eq μ hK hL τ x z]
    rw [← lintegral_const_mul' (W τ) _ (hweightTop τ)]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro r hr
    calc
      W τ * (∫⁻ y, K (r, x, y) * L (τ - r, y, z) ∂μ) =
          ∫⁻ y, W τ * (K (r, x, y) * L (τ - r, y, z)) ∂μ :=
            (lintegral_const_mul' (W τ) _ (hweightTop τ)).symm
      _ = ∫⁻ y, F r y ∂μ := by
            apply lintegral_congr
            intro y
            dsimp [F, W]
            rw [show τ = r + (τ - r) by ring]
            rw [laplaceTimeWeight_add]
            rw [show r + (τ - r) - r = τ - r by ring]
            ac_rfl
  let Hset : Set ℝ := Ioo (0 : ℝ) τ ∩ Ici (τ / 2)
  let Lset : Set ℝ := Ioo (0 : ℝ) τ \ Ici (τ / 2)
  have hsplit :
      (∫⁻ r in Ioo (0 : ℝ) τ, ∫⁻ y, F r y ∂μ ∂volume) =
        (∫⁻ r in Hset, ∫⁻ y, F r y ∂μ ∂volume) +
          ∫⁻ r in Lset, ∫⁻ y, F r y ∂μ ∂volume := by
    dsimp [Hset, Lset]
    exact (lintegral_inter_add_sdiff (μ := volume) (B := Ici (τ / 2))
      (fun r => ∫⁻ y, F r y ∂μ) (Ioo (0 : ℝ) τ) measurableSet_Ici).symm
  have hHset : MeasurableSet Hset := measurableSet_Ioo.inter measurableSet_Ici
  have hLset : MeasurableSet Lset := measurableSet_Ioo.diff measurableSet_Ici
  have hHsubset : Hset ⊆ Iio τ := by
    intro r hr
    exact hr.1.2
  have hLsubset : Lset ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact hr.1.1
  have hreflect (G : ℝ → ℝ≥0∞) :
      (∫⁻ r in Iio τ, G (τ - r) ∂volume) = ∫⁻ s in Ioi (0 : ℝ), G s ∂volume :=
    setLIntegral_reflect_sub G
  have hhigh :
      (∫⁻ r in Hset, ∫⁻ y, F r y ∂μ ∂volume) ≤
        spatialKernelComp μ (supTimeKernel rate (τ₀ / 2) K)
          (laplaceTimeKernel rate L) x z := by
    unfold spatialKernelComp
    rw [← lintegral_swap_restrict_time μ Hset hHset hF]
    apply lintegral_mono
    intro y
    have hrestMeas : Measurable (fun r : ℝ =>
        W (τ - r) * L (τ - r, y, z)) := by
      exact (hW.comp (by fun_prop)).mul (hL.comp (by fun_prop))
    calc
      (∫⁻ r in Hset,
        (W r * K (r, x, y)) * (W (τ - r) * L (τ - r, y, z)) ∂volume)
        ≤ ∫⁻ r in Hset,
            supTimeKernel rate (τ₀ / 2) K x y *
              (W (τ - r) * L (τ - r, y, z)) ∂volume := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hHset] with r hr
              have hr : τ / 2 ≤ r := hr.2
              have hthreshold : τ₀ / 2 ≤ r := by linarith
              exact mul_le_mul' (le_supTimeKernel rate K hthreshold x y) le_rfl
      _ = supTimeKernel rate (τ₀ / 2) K x y *
            ∫⁻ r in Hset, W (τ - r) * L (τ - r, y, z) ∂volume :=
              lintegral_const_mul _ hrestMeas
      _ ≤ supTimeKernel rate (τ₀ / 2) K x y *
            ∫⁻ r in Iio τ, W (τ - r) * L (τ - r, y, z) ∂volume :=
              mul_le_mul' le_rfl (lintegral_mono_set hHsubset)
      _ = supTimeKernel rate (τ₀ / 2) K x y *
            laplaceTimeKernel rate L y z := by
              calc
                _ = supTimeKernel rate (τ₀ / 2) K x y *
                    ∫⁻ r in Iio τ,
                      (fun s => W s * L (s, y, z)) (τ - r) ∂volume := by rfl
                _ = _ := by
                  rw [hreflect (fun s => W s * L (s, y, z))]
                  rfl
  have hlow :
      (∫⁻ r in Lset, ∫⁻ y, F r y ∂μ ∂volume) ≤
        spatialKernelComp μ (laplaceTimeKernel rate K) R x z := by
    unfold spatialKernelComp
    rw [← lintegral_swap_restrict_time μ Lset hLset hF]
    apply lintegral_mono
    intro y
    have hfirstMeas : Measurable (fun r : ℝ => W r * K (r, x, y)) := by
      exact (hW.comp measurable_id).mul (hK.comp (by fun_prop))
    calc
      (∫⁻ r in Lset,
        (W r * K (r, x, y)) * (W (τ - r) * L (τ - r, y, z)) ∂volume)
        ≤ ∫⁻ r in Lset, (W r * K (r, x, y)) * R y z ∂volume := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hLset] with r hr
              have hn : ¬ τ / 2 ≤ r := hr.2
              have hr : r < τ / 2 := lt_of_not_ge hn
              have hthreshold : τ₀ / 2 ≤ τ - r := by linarith
              exact mul_le_mul' le_rfl (hLtail hthreshold y z)
      _ = R y z * ∫⁻ r in Lset, W r * K (r, x, y) ∂volume := by
              calc
                _ = ∫⁻ r in Lset, R y z * (W r * K (r, x, y)) ∂volume := by
                  apply setLIntegral_congr_fun hLset
                  intro r hr
                  ac_rfl
                _ = _ := lintegral_const_mul _ hfirstMeas
      _ ≤ R y z * laplaceTimeKernel rate K x y := by
              unfold laplaceTimeKernel
              exact mul_le_mul' le_rfl (lintegral_mono_set hLsubset)
      _ = laplaceTimeKernel rate K x y * R y z := by rw [mul_comm]
  calc
    W τ * timeKernelComp μ (causalKernel K) (causalKernel L) (τ, x, z)
      = ∫⁻ r in Ioo (0 : ℝ) τ, ∫⁻ y, F r y ∂μ ∂volume := hleft
    _ = (∫⁻ r in Hset, ∫⁻ y, F r y ∂μ ∂volume) +
          ∫⁻ r in Lset, ∫⁻ y, F r y ∂μ ∂volume := hsplit
    _ ≤ spatialKernelComp μ (supTimeKernel rate (τ₀ / 2) K)
          (laplaceTimeKernel rate L) x z +
        spatialKernelComp μ (laplaceTimeKernel rate K) R x z := add_le_add hhigh hlow

/-- Every damped path slice is bounded by the recursively split supremum and
Laplace majorant. -/
theorem pathTimeKernel_le_pathDominatingKernel (θ rate : ℝ) {n : ℕ} :
    ∀ (w : List (CollisionPair n)) {X : Type} [MeasurableSpace X]
      {eX : X → Configuration n}, Measurable eX →
      ∀ {τ₀ τ : ℝ}, 0 < τ₀ → τ₀ ≤ τ →
        ∀ (x : X) (y : Configuration n),
          laplaceTimeWeight rate τ * pathTimeKernel θ w eX id (τ, x, y) ≤
            pathDominatingKernel θ rate w eX τ₀ x y := by
  intro w
  induction w with
  | nil =>
      intro X _ eX hX τ₀ τ hτ₀ hτ x y
      exact pathTimeKernel_le_pathDominatingKernel_nil θ rate eX hτ₀ hτ x y
  | cons α w ih =>
      intro X _ eX hX τ₀ τ hτ₀ hτ x y
      let I : TimeKernel X (FusedConfiguration α) :=
        freeTimeKernel eX (collisionEmbedding α)
      let J : TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
        collisionTimeKernel α θ
      let T : TimeKernel (FusedConfiguration α) (Configuration n) :=
        pathTimeKernel θ w (collisionEmbedding α) id
      let Q : TimeKernel (FusedConfiguration α) (Configuration n) :=
        timeKernelComp volume (causalKernel J) T
      let TailR : FusedConfiguration α → Configuration n → ℝ≥0∞ :=
        pathDominatingKernel θ rate w (collisionEmbedding α) (τ₀ / 4)
      let R : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun u v =>
        spatialKernelComp volume (supTimeKernel rate (τ₀ / 4) J)
          (laplaceTimeKernel rate T) u v +
        spatialKernelComp volume (laplaceTimeKernel rate J)
          TailR u v
      have hI : Measurable I := by
        exact measurable_freeTimeKernel hX (measurable_collisionEmbedding α)
      have hJ : Measurable J := measurable_collisionTimeKernel α θ
      have hT : Measurable T :=
        measurable_pathTimeKernel θ w (measurable_collisionEmbedding α) measurable_id
      have hTcausal : causalKernel T = T :=
        pathTimeKernel_causal θ w (collisionEmbedding α) id
      have hQ : Measurable Q :=
        measurable_timeKernelComp volume (measurable_causalKernel hJ) hT
      have hQcausal : causalKernel Q = Q := by
        simpa [Q, hTcausal] using timeKernelComp_causal volume J T
      have hTtail : ∀ {s : ℝ}, τ₀ / 4 ≤ s → ∀ u v,
          laplaceTimeWeight rate s * T (s, u, v) ≤
            TailR u v := by
        intro s hs u v
        exact ih (X := FusedConfiguration α) (eX := collisionEmbedding α)
          (measurable_collisionEmbedding α) (τ₀ := τ₀ / 4) (τ := s)
          (by positivity) hs u v
      have hTtailSplit : ∀ {s : ℝ}, (τ₀ / 2) / 2 ≤ s → ∀ u v,
          laplaceTimeWeight rate s * T (s, u, v) ≤
            pathDominatingKernel θ rate w (collisionEmbedding α) (τ₀ / 4) u v := by
        intro s hs u v
        apply hTtail
        linarith
      have hQtail : ∀ {s : ℝ}, τ₀ / 2 ≤ s → ∀ u v,
          laplaceTimeWeight rate s * Q (s, u, v) ≤ R u v := by
        intro s hs u v
        have hinner := laplaceTimeKernelComp_split volume hJ hT rate
          (τ₀ := τ₀ / 2) (τ := s) hs TailR hTtailSplit u v
        change laplaceTimeWeight rate s *
          timeKernelComp volume (causalKernel J) T (s, u, v) ≤ R u v
        have hquarter : (τ₀ / 2) / 2 = τ₀ / 4 := by ring
        simpa [R, TailR, hquarter, hTcausal] using hinner
      have hOuter := laplaceTimeKernelComp_split volume hI hQ rate hτ R hQtail x y
      change laplaceTimeWeight rate τ *
          timeKernelComp volume (causalKernel I) Q (τ, x, y) ≤ _
      rw [← hQcausal]
      simpa [pathDominatingKernel, I, J, T, Q, R] using hOuter

/-- The recursively defined path majorant is jointly measurable. -/
theorem measurable_pathDominatingKernel (θ rate : ℝ) {n : ℕ}
    (w : List (CollisionPair n)) {X : Type} [MeasurableSpace X]
    {eX : X → Configuration n} (hX : Measurable eX)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    Measurable (Function.uncurry (pathDominatingKernel θ rate w eX τ₀)) := by
  induction w generalizing X eX hX τ₀ hτ₀ with
  | nil =>
      change Measurable (Function.uncurry
        (supTimeKernel rate τ₀ (freeTimeKernel eX id)))
      exact measurable_supTimeKernel (measurable_freeTimeKernel hX measurable_id)
        (fun x y => continuousOn_freeTimeKernel_time (eY := id) x y) rate hτ₀
  | cons α w ih =>
      let I : TimeKernel X (FusedConfiguration α) :=
        freeTimeKernel eX (collisionEmbedding α)
      let J : TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
        collisionTimeKernel α θ
      let T : TimeKernel (FusedConfiguration α) (Configuration n) :=
        pathTimeKernel θ w (collisionEmbedding α) id
      let Q : TimeKernel (FusedConfiguration α) (Configuration n) :=
        timeKernelComp volume (causalKernel J) T
      let Tail : FusedConfiguration α → Configuration n → ℝ≥0∞ :=
        pathDominatingKernel θ rate w (collisionEmbedding α) (τ₀ / 4)
      let Inner : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z y' =>
        spatialKernelComp volume (supTimeKernel rate (τ₀ / 4) J)
          (laplaceTimeKernel rate T) z y' +
        spatialKernelComp volume (laplaceTimeKernel rate J) Tail z y'
      have hI : Measurable I :=
        measurable_freeTimeKernel hX (measurable_collisionEmbedding α)
      have hJ : Measurable J :=
        measurable_collisionTimeKernel α θ
      have hT : Measurable T :=
        measurable_pathTimeKernel θ w (measurable_collisionEmbedding α) measurable_id
      have hQ : Measurable Q := measurable_timeKernelComp volume
        (measurable_causalKernel hJ) hT
      have hSupI : Measurable (Function.uncurry
          (supTimeKernel rate (τ₀ / 2) I)) :=
        measurable_supTimeKernel (K := I) hI
          (fun (x : X) (y : FusedConfiguration α) =>
            by simpa only [I] using
              (continuousOn_freeTimeKernel_time (eY := collisionEmbedding α) x y))
          rate (by positivity)
      have hSupJ : Measurable (Function.uncurry
          (supTimeKernel rate (τ₀ / 4) J)) :=
        measurable_supTimeKernel (K := J) hJ
          (fun (x y : FusedConfiguration α) =>
            by simpa only [J] using continuousOn_collisionTimeKernel_time α θ x y)
          rate (by positivity)
      have hLapQ : Measurable (Function.uncurry
          (laplaceTimeKernel rate Q)) :=
        measurable_laplaceTimeKernel rate hQ
      have hLapI : Measurable (Function.uncurry
          (laplaceTimeKernel rate I)) :=
        measurable_laplaceTimeKernel rate hI
      have hLapJ : Measurable (Function.uncurry
          (laplaceTimeKernel rate J)) :=
        measurable_laplaceTimeKernel rate hJ
      have hLapT : Measurable (Function.uncurry
          (laplaceTimeKernel rate T)) :=
        measurable_laplaceTimeKernel rate hT
      have hTail : Measurable (Function.uncurry
          Tail) :=
        ih (X := FusedConfiguration α) (eX := collisionEmbedding α)
          (hX := measurable_collisionEmbedding α) (τ₀ := τ₀ / 4)
          (hτ₀ := by positivity)
      have hInner : Measurable (Function.uncurry
          (spatialKernelComp volume (supTimeKernel rate (τ₀ / 4) J)
            (laplaceTimeKernel rate T))) :=
        measurable_spatialKernelComp volume hSupJ hLapT
      have hTailComp : Measurable (Function.uncurry
          (spatialKernelComp volume (laplaceTimeKernel rate J) Tail)) :=
        measurable_spatialKernelComp volume hLapJ hTail
      have hInnerSum : Measurable (Function.uncurry Inner) := hInner.add hTailComp
      have hSecond : Measurable (Function.uncurry
          (spatialKernelComp volume (laplaceTimeKernel rate I) Inner)) :=
        measurable_spatialKernelComp volume hLapI hInnerSum
      have hFirst : Measurable (Function.uncurry
          (spatialKernelComp volume (supTimeKernel rate (τ₀ / 2) I)
            (laplaceTimeKernel rate Q))) :=
        measurable_spatialKernelComp volume hSupI hLapQ
      change Measurable (Function.uncurry (fun x y =>
        spatialKernelComp volume (supTimeKernel rate (τ₀ / 2) I)
          (laplaceTimeKernel rate Q) x y +
        spatialKernelComp volume (laplaceTimeKernel rate I) Inner x y))
      exact hFirst.add hSecond

end Critical2DKPZ.DeltaBose
