/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.OrderedComposition
public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.Tactic

/-! # Causal composition of collision diagrams

Chronological collision paths factor into kernels on full or fused configuration spaces, with product Lebesgue measure on each intermediate collision space. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- A free strand between two specified endpoint embeddings. -/
noncomputable def freeTimeKernel {n : ℕ} {X Y : Type} (eX : X → Configuration n)
    (eY : Y → Configuration n) : TimeKernel X Y :=
  fun p => ENNReal.ofReal (freeKernel n p.1 (eX p.2.1) (eY p.2.2))

/-- The repeated-collision block as a time-dependent kernel. -/
noncomputable def collisionTimeKernel {n : ℕ} (α : CollisionPair n) (θ : ℝ) :
    TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
  fun p => ENNReal.ofReal (collisionKernel α θ p.1 p.2.1 p.2.2)

/-- The free time kernel is measurable when its configuration maps are measurable. -/
theorem measurable_freeTimeKernel {n : ℕ} {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {eX : X → Configuration n} {eY : Y → Configuration n} (hX : Measurable eX) (hY : Measurable eY) :
    Measurable (freeTimeKernel eX eY) :=
  ((measurable_freeKernel n).comp
    (measurable_fst.prodMk ((hX.comp measurable_snd.fst).prodMk (hY.comp measurable_snd.snd)))).ennreal_ofReal

/-- The collision time kernel is jointly measurable in time and fused endpoints. -/
theorem measurable_collisionTimeKernel {n : ℕ} (α : CollisionPair n) (θ : ℝ) :
    Measurable (collisionTimeKernel α θ) := by
  have hp : Measurable (fun p : ℝ × FusedConfiguration α × FusedConfiguration α =>
      ((θ, p.1), p.2)) := (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  exact ((measurable_collisionKernel α).comp hp).ennreal_ofReal

/-- A word as a chronological composition of free strands and collision blocks. -/
noncomputable def pathTimeKernel {n : ℕ} (θ : ℝ) (w : List (CollisionPair n))
    {X Y : Type} (eX : X → Configuration n) (eY : Y → Configuration n) : TimeKernel X Y :=
  match w with
  | [] => causalKernel (freeTimeKernel eX eY)
  | α :: w => timeKernelComp volume (causalKernel (freeTimeKernel eX (collisionEmbedding α)))
      (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
        (pathTimeKernel θ w (collisionEmbedding α) eY))

/-- Every chronological path is jointly measurable, including arbitrary measurable endpoints. -/
theorem measurable_pathTimeKernel {n : ℕ} (θ : ℝ) (w : List (CollisionPair n)) :
    ∀ {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
      {eX : X → Configuration n} {eY : Y → Configuration n},
      Measurable eX → Measurable eY → Measurable (pathTimeKernel θ w eX eY) := by
  induction w with
  | nil =>
    intro X Y _ _ eX eY hX hY
    exact measurable_causalKernel (measurable_freeTimeKernel hX hY)
  | cons α w ih =>
    intro X Y _ _ eX eY hX hY
    exact measurable_timeKernelComp volume
      (measurable_causalKernel (measurable_freeTimeKernel hX (measurable_collisionEmbedding α)))
      (measurable_timeKernelComp volume (measurable_causalKernel (measurable_collisionTimeKernel α θ))
        (ih (measurable_collisionEmbedding α) hY))

/-- Extending a time kernel by zero at nonpositive times is idempotent. -/
theorem causalKernel_idem {X Y : Type*} (K : TimeKernel X Y) :
    causalKernel (causalKernel K) = causalKernel K := by
  funext ⟨t, x, y⟩
  by_cases ht : 0 < t <;> simp only [causalKernel, ht, ite_true, ite_false]

/-- The chronological path vanishes at nonpositive elapsed time. -/
theorem pathTimeKernel_causal {n : ℕ} (θ : ℝ) (w : List (CollisionPair n)) :
    ∀ {X Y : Type} (eX : X → Configuration n) (eY : Y → Configuration n),
      causalKernel (pathTimeKernel θ w eX eY) = pathTimeKernel θ w eX eY := by
  induction w with
  | nil =>
    intro X Y eX eY
    exact causalKernel_idem (freeTimeKernel eX eY)
  | cons α w ih =>
    intro X Y eX eY
    have ht := ih (collisionEmbedding α) eY
    have hm := timeKernelComp_causal volume (collisionTimeKernel α θ)
      (pathTimeKernel θ w (collisionEmbedding α) eY)
    simp only [ht] at hm
    have ho := timeKernelComp_causal volume (freeTimeKernel eX (collisionEmbedding α))
      (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
        (pathTimeKernel θ w (collisionEmbedding α) eY))
    simpa only [hm, pathTimeKernel] using ho

/-- The composition representation agrees with the original ordered diagram integral. -/
theorem pathTimeKernel_eq_diagram {n : ℕ} (θ : ℝ) (w : List (CollisionPair n)) :
    ∀ {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
      {eX : X → Configuration n} {eY : Y → Configuration n},
      Measurable eX → Measurable eY →
      pathTimeKernel θ w eX eY =
        causalKernel (fun p => diagramKernel θ w p.1 (eX p.2.1) (eY p.2.2)) := by
  induction w with
  | nil => intro X Y _ _ eX eY hX hY; rfl
  | cons α w ih =>
    intro X Y _ _ eX eY hX hY
    let M : TimeKernel (FusedConfiguration α) Y :=
      fun p => diagramKernel θ w p.1 (collisionEmbedding α p.2.1) (eY p.2.2)
    have hM : Measurable M := measurable_diagramKernel_comp w measurable_const measurable_fst
      ((measurable_collisionEmbedding α).comp measurable_snd.fst) (hY.comp measurable_snd.snd)
    have ht : pathTimeKernel θ w (collisionEmbedding α) eY = causalKernel M :=
      ih (measurable_collisionEmbedding α) hY
    funext ⟨t, x, y⟩
    rw [pathTimeKernel, ht, timeKernelComp_three_causal_eq volume volume
      (measurable_freeTimeKernel hX (measurable_collisionEmbedding α))
      (measurable_collisionTimeKernel α θ) hM]
    by_cases hpos : 0 < t
    · rw [causalKernel_of_pos _ hpos]
      rfl
    · rw [causalKernel_of_nonpos _ (not_lt.mp hpos), Ioo_eq_empty_of_le (not_lt.mp hpos),
        Measure.restrict_empty, lintegral_zero_measure]

end Critical2DKPZ.DeltaBose
