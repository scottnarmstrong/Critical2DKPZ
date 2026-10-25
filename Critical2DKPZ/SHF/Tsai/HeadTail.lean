/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CoveringKernel
public import Critical2DKPZ.SHF.DeltaBose.PathKernel
public import Critical2DKPZ.SHF.Tsai.WeightedFormBound
public import Critical2DKPZ.SHF.Tsai.Tech
import Mathlib.Tactic

/-! # Head and tail factors for long collision words -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Transposing a measurable positive kernel swaps the two endpoint spaces and exponents. -/
theorem WeightedFormBound.transpose {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ} {K : X → Y → ℝ≥0∞} {c : ℝ≥0∞}
    (hKm : Measurable (Function.uncurry K))
    (h : WeightedFormBound μ ν wX wY p p' K c) :
    WeightedFormBound ν μ wY wX p' p (fun y x => K x y) c := by
  intro f g hf hg
  let F : X → Y → ℝ≥0∞ := fun x y => f x * K x y * g y
  have hK : Measurable (Function.uncurry (fun x y => K x y)) := hKm
  have hF : Measurable (Function.uncurry F) := hf.comp measurable_fst |>.mul hK |>.mul (hg.comp measurable_snd)
  have hswap := lintegral_lintegral_swap (μ := μ) (ν := ν) hF.aemeasurable
  have hKx (y : Y) : Measurable (fun x : X => K x y) :=
    hKm.comp (measurable_id.prodMk measurable_const)
  have hKy (x : X) : Measurable (fun y : Y => K x y) :=
    hKm.comp (measurable_const.prodMk measurable_id)
  have hEq :
      (∫⁻ y, g y * (∫⁻ x, K x y * f x ∂μ) ∂ν) =
        ∫⁻ x, f x * (∫⁻ y, K x y * g y ∂ν) ∂μ := by
    calc
      _ = ∫⁻ y, ∫⁻ x, F x y ∂μ ∂ν := by
        apply lintegral_congr
        intro y
        calc
          g y * (∫⁻ x, K x y * f x ∂μ) =
              ∫⁻ x, g y * (K x y * f x) ∂μ :=
                (lintegral_const_mul (g y) ((hKx y).mul hf)).symm
          _ = ∫⁻ x, F x y ∂μ := by
                apply lintegral_congr
                intro x
                dsimp [F]
                ac_rfl
      _ = ∫⁻ x, ∫⁻ y, F x y ∂ν ∂μ := hswap.symm
      _ = _ := by
        apply lintegral_congr
        intro x
        calc
          ∫⁻ y, F x y ∂ν = ∫⁻ y, f x * (K x y * g y) ∂ν := by
            apply lintegral_congr
            intro y
            dsimp [F]
            ac_rfl
          _ = f x * (∫⁻ y, K x y * g y ∂ν) :=
            lintegral_const_mul (f x) ((hKy x).mul hg)
  calc
    (∫⁻ y, g y * (∫⁻ x, (fun y x => K x y) y x * f x ∂μ) ∂ν) =
        ∫⁻ x, f x * (∫⁻ y, K x y * g y ∂ν) ∂μ := hEq
    _ ≤ c * (∫⁻ x, (f x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') *
          (∫⁻ y, (g y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p) := by
          have hBound := h g f hg hf
          calc
            _ ≤ c * (∫⁻ y, (g y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p) *
                  (∫⁻ x, (f x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') := hBound
            _ = _ := by ac_rfl



/-- The incoming `Lᵖ → L²` estimate in the adjoint orientation used by a head factor. -/
theorem weightedFormBound_incoming_adjoint {n : ℕ} (α : CollisionPair n) {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
      WeightedFormBound volume volume (fun x => a * configurationOneNorm x) (fun _ => 0) 2 p
        (fun (x : Configuration n) (z : FusedConfiguration α) =>
          ENNReal.ofReal (incomingKernel α t z x)) (ENNReal.ofReal (c * t ^ (-1 / p))) := by
  obtain ⟨c, hc, hIncoming⟩ := weightedFormBound_incoming_to_L2 α hp ha
  refine ⟨c, hc, fun t ht => ?_⟩
  have hK : Measurable (Function.uncurry
      (fun z : FusedConfiguration α => fun x : Configuration n =>
        ENNReal.ofReal (incomingKernel α t z x))) := by
    change Measurable (fun z : FusedConfiguration α × Configuration n =>
      ENNReal.ofReal (incomingKernel α t z.1 z.2))
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hForward := hIncoming t ht
  exact WeightedFormBound.transpose hK hForward

/-- The head of a word `α :: β :: ⋯`: the incoming at `α`, its collision block, and the free motion until `β`
merges at `z`, in total time `s`. -/
noncomputable def headKernel {n : ℕ} (θ : ℝ) (α β : CollisionPair n) (s : ℝ) (x : Configuration n)
    (z : FusedConfiguration β) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioo 0 s, ∫⁻ u in Set.Ioo r s, ∫⁻ z₁ : FusedConfiguration α, ∫⁻ z₁' : FusedConfiguration α,
    ENNReal.ofReal (incomingKernel α r z₁ x) * ENNReal.ofReal (collisionKernel α θ (u - r) z₁ z₁') *
      ENNReal.ofReal (swappingKernel α β (s - u) z₁' z)

/-- The tail from the merge of `β` at `z`: its collision block, then every admissible continuation word, ending
at `y` after total time `t`. -/
noncomputable def tailKernel {n : ℕ} (θ : ℝ) (β : CollisionPair n) (t : ℝ) (z : FusedConfiguration β)
    (y : Configuration n) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ w : CollisionWord n m,
    if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
      ∫⁻ u in Set.Ioo 0 t, ∫⁻ z' : FusedConfiguration β, ENNReal.ofReal (collisionKernel β θ u z z') *
        diagramKernel θ (List.ofFn w.1) (t - u) (collisionEmbedding β z') y
    else 0

/-- One prescribed continuation word in the tail expansion. -/
noncomputable def tailWordKernel {n : ℕ} (θ : ℝ) (β : CollisionPair n)
    (w : List (CollisionPair n)) (t : ℝ) (z : FusedConfiguration β)
    (y : Configuration n) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
    ENNReal.ofReal (collisionKernel β θ u z z') *
      diagramKernel θ w (t - u) (collisionEmbedding β z') y

/-- The causal time-kernel representation of the head factor. -/
noncomputable def headTimeKernel {n : ℕ} (θ : ℝ) (α β : CollisionPair n) :
    TimeKernel (Configuration n) (FusedConfiguration β) :=
  timeKernelComp volume (causalKernel (freeTimeKernel id (collisionEmbedding α)))
    (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
      (causalKernel (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β))))

/-- A single tail word, as a causal time-kernel composition. -/
noncomputable def tailWordTimeKernel {n : ℕ} (θ : ℝ) (β : CollisionPair n)
    (w : List (CollisionPair n)) : TimeKernel (FusedConfiguration β) (Configuration n) :=
  timeKernelComp volume (causalKernel (collisionTimeKernel β θ))
    (causalKernel (pathTimeKernel θ w (collisionEmbedding β) id))

/-- The explicit head integral is the chronological composition of its three strands. -/
theorem headKernel_eq_headTimeKernel {n : ℕ} (θ : ℝ) (α β : CollisionPair n)
    (s : ℝ) (x : Configuration n) (z : FusedConfiguration β) :
    headKernel θ α β s x z = headTimeKernel θ α β (s, x, z) := by
  have hP : Measurable (freeTimeKernel (fun x : Configuration n => x) (collisionEmbedding α)) :=
    measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α)
  have hJ : Measurable (collisionTimeKernel α θ) := measurable_collisionTimeKernel α θ
  have hS : Measurable (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)) :=
    measurable_freeTimeKernel (measurable_collisionEmbedding α) (measurable_collisionEmbedding β)
  change (∫⁻ r in Ioo 0 s, ∫⁻ u in Ioo r s,
      ∫⁻ z₁ : FusedConfiguration α, ∫⁻ z₁' : FusedConfiguration α,
        ENNReal.ofReal (freeKernel n r x (collisionEmbedding α z₁)) *
          ENNReal.ofReal (collisionKernel α θ (u - r) z₁ z₁') *
            ENNReal.ofReal (freeKernel n (s - u) (collisionEmbedding α z₁')
              (collisionEmbedding β z))) = headTimeKernel θ α β (s, x, z)
  exact (timeKernelComp_three_causal_eq volume volume hP hJ hS s x z).symm


/-- A tail word is one collision block followed by its chronological diagram path. -/
theorem tailWordKernel_eq_tailWordTimeKernel {n : ℕ} (θ : ℝ) (β : CollisionPair n)
    (w : List (CollisionPair n)) (t : ℝ) (z : FusedConfiguration β) (y : Configuration n) :
    tailWordKernel θ β w t z y =
      tailWordTimeKernel θ β w (t, z, y) := by
  have hJ : Measurable (collisionTimeKernel β θ) := measurable_collisionTimeKernel β θ
  have hPath : Measurable
      (pathTimeKernel θ w (collisionEmbedding β) (fun y : Configuration n => y)) :=
    measurable_pathTimeKernel θ w (measurable_collisionEmbedding β) measurable_id
  have hPathEq := pathTimeKernel_eq_diagram θ w
    (measurable_collisionEmbedding β) (measurable_id : Measurable (fun y : Configuration n => y))
  have hpoint (u : ℝ) (z' : FusedConfiguration β) (hu : u ∈ Ioo 0 t) :
      diagramKernel θ w (t - u) (collisionEmbedding β z') y =
        pathTimeKernel θ w (collisionEmbedding β) id (t - u, z', y) := by
    rw [hPathEq]
    have hcausal : causalKernel
        (fun p : ℝ × FusedConfiguration β × Configuration n =>
          diagramKernel θ w p.1 (collisionEmbedding β p.2.1) p.2.2)
        (t - u, z', y) = diagramKernel θ w (t - u) (collisionEmbedding β z') y := by
      exact causalKernel_of_pos _ (sub_pos.mpr hu.2) z' y
    simpa using hcausal.symm
  calc
    (∫⁻ u in Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
        ENNReal.ofReal (collisionKernel β θ u z z') *
          diagramKernel θ w (t - u) (collisionEmbedding β z') y) =
      ∫⁻ u in Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
        ENNReal.ofReal (collisionKernel β θ u z z') *
          pathTimeKernel θ w (collisionEmbedding β) id (t - u, z', y) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
            apply lintegral_congr_ae
            filter_upwards [] with z'
            exact congrArg (fun q => ENNReal.ofReal (collisionKernel β θ u z z') * q)
              (hpoint u z' hu)
    _ = tailWordTimeKernel θ β w (t, z, y) := by
      unfold tailWordTimeKernel
      exact (timeKernelComp_causal_eq volume hJ hPath t z y).symm

end Critical2DKPZ.SHF.Tsai

end
