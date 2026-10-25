/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PotentialProductRows
public import Critical2DKPZ.SHF.DeltaBose.IncomingMass
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Tactic

/-! # Fused heat-potential row bounds -/

@[expose] public section

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Nonnegative form of the two equal-time Gaussian convolution. -/
theorem lintegral_heatKernel_mul_sameTime {t : ℝ} (ht : 0 < t) (a b : Plane) :
    (∫⁻ z : Plane,
      ENNReal.ofReal (heatKernel t (z - a)) * ENNReal.ofReal (heatKernel t (z - b))) =
      ENNReal.ofReal (heatKernel (2 * t) (b - a)) := by
  calc (∫⁻ z : Plane,
        ENNReal.ofReal (heatKernel t (z - a)) * ENNReal.ofReal (heatKernel t (z - b)))
      = ∫⁻ z : Plane, ENNReal.ofReal
          (heatKernel t (z - a) * heatKernel t (z - b)) := by
            apply lintegral_congr
            intro z
            rw [← ENNReal.ofReal_mul (Critical2DKPZ.heatKernel_pos ht _).le]
    _ = ENNReal.ofReal (∫ z : Plane,
          heatKernel t (z - a) * heatKernel t (z - b)) :=
          (ofReal_integral_eq_lintegral_ofReal
            (integrable_heatKernel_mul_sameTime ht a b)
            (Filter.Eventually.of_forall fun z =>
              mul_nonneg (Critical2DKPZ.heatKernel_pos ht _).le (Critical2DKPZ.heatKernel_pos ht _).le)).symm
    _ = ENNReal.ofReal (heatKernel (2 * t) (b - a)) := by
          rw [integral_heatKernel_mul_sameTime ht a b]

/-- When the potential couples two spectators, their row is bounded by the
half-time constant times the doubled-time heat kernel of the fused center. -/
theorem lintegral_fusedPairPotential_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} (ht : 0 < t) (a b : Plane) (x : ι → Plane)
    (i j : ι) (hij : i ≠ j) :
    (∫⁻ p : Plane × (ι → Plane),
      (ENNReal.ofReal (heatKernel t (p.1 - a)) *
        ENNReal.ofReal (heatKernel t (p.1 - b))) *
        ((∏ k, ENNReal.ofReal (heatKernel t (p.2 k - x k))) *
          heatPotential (p.2 i - p.2 j))) ≤
      heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t) (b - a)) := by
  let A : Plane → ℝ≥0∞ := fun c =>
    ENNReal.ofReal (heatKernel t (c - a)) * ENNReal.ofReal (heatKernel t (c - b))
  let B : (ι → Plane) → ℝ≥0∞ := fun v =>
    (∏ k, ENNReal.ofReal (heatKernel t (v k - x k))) * heatPotential (v i - v j)
  change (∫⁻ p : Plane × (ι → Plane), A p.1 * B p.2) ≤ _
  have hA : Measurable A := by
    dsimp [A]
    have ha : Measurable (fun c : Plane => heatKernel t (c - a)) := by
      unfold heatKernel
      fun_prop
    have hb : Measurable (fun c : Plane => heatKernel t (c - b)) := by
      unfold heatKernel
      fun_prop
    exact ha.ennreal_ofReal.mul hb.ennreal_ofReal
  have hB : Measurable B := by
    dsimp [B]
    have hp : Measurable (fun v : ι → Plane =>
        ∏ k, ENNReal.ofReal (heatKernel t (v k - x k))) := by
      apply Finset.measurable_fun_prod
      intro k hk
      unfold heatKernel
      fun_prop
    have hw : Measurable (fun v : ι → Plane => heatPotential (v i - v j)) := by
      exact measurable_heatPotential.comp
        ((measurable_pi_apply i).sub (measurable_pi_apply j))
    exact hp.mul hw
  have hF : Measurable (fun p : Plane × (ι → Plane) => A p.1 * B p.2) :=
    (hA.comp measurable_fst).mul (hB.comp measurable_snd)
  have hpair := lintegral_tensorHeatKernel_mul_pairPotential_le ht i j hij x
  have hcenter := lintegral_heatKernel_mul_sameTime ht a b
  calc (∫⁻ p : Plane × (ι → Plane), A p.1 * B p.2)
      = ∫⁻ c : Plane, ∫⁻ v : ι → Plane, A c * B v := by
          rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
    _ = (∫⁻ c : Plane, A c) * (∫⁻ v : ι → Plane, B v) := by
          calc (∫⁻ c : Plane, ∫⁻ v : ι → Plane, A c * B v)
              = ∫⁻ c : Plane, A c * (∫⁻ v : ι → Plane, B v) := by
                  apply lintegral_congr
                  intro c
                  exact lintegral_const_mul (A c) hB
            _ = _ := lintegral_mul_const _ hA
    _ ≤ (∫⁻ c : Plane, A c) * heatPotentialRowBound t :=
          mul_le_mul_right hpair _
    _ = heatPotentialRowBound t *
          ENNReal.ofReal (heatKernel (2 * t) (b - a)) := by
          rw [hcenter]
          ac_rfl

/-- When the potential couples one spectator to the fused center, the same
half-time row bound leaves the doubled-time center heat kernel. -/
theorem lintegral_fusedShiftedPotential_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} (ht : 0 < t) (a b : Plane) (x : ι → Plane) (i : ι) :
    (∫⁻ p : Plane × (ι → Plane),
      (ENNReal.ofReal (heatKernel t (p.1 - a)) *
        ENNReal.ofReal (heatKernel t (p.1 - b))) *
        ((∏ k, ENNReal.ofReal (heatKernel t (p.2 k - x k))) *
          heatPotential (p.2 i - p.1))) ≤
      heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t) (b - a)) := by
  let A : Plane → ℝ≥0∞ := fun c =>
    ENNReal.ofReal (heatKernel t (c - a)) * ENNReal.ofReal (heatKernel t (c - b))
  let B : Plane × (ι → Plane) → ℝ≥0∞ := fun p =>
    (∏ k, ENNReal.ofReal (heatKernel t (p.2 k - x k))) *
      heatPotential (p.2 i - p.1)
  change (∫⁻ p : Plane × (ι → Plane), A p.1 * B p) ≤ _
  have hA : Measurable A := by
    dsimp [A]
    have ha : Measurable (fun c : Plane => heatKernel t (c - a)) := by
      unfold heatKernel
      fun_prop
    have hb : Measurable (fun c : Plane => heatKernel t (c - b)) := by
      unfold heatKernel
      fun_prop
    exact ha.ennreal_ofReal.mul hb.ennreal_ofReal
  have hB : Measurable B := by
    dsimp [B]
    have hp : Measurable (fun p : Plane × (ι → Plane) =>
        ∏ k, ENNReal.ofReal (heatKernel t (p.2 k - x k))) := by
      apply Finset.measurable_fun_prod
      intro k hk
      unfold heatKernel
      fun_prop
    have hw : Measurable (fun p : Plane × (ι → Plane) =>
        heatPotential (p.2 i - p.1)) := by
      apply measurable_heatPotential.comp
      fun_prop
    exact hp.mul hw
  have hF : Measurable (fun p : Plane × (ι → Plane) => A p.1 * B p) :=
    (hA.comp measurable_fst).mul hB
  have hcenter := lintegral_heatKernel_mul_sameTime ht a b
  calc (∫⁻ p : Plane × (ι → Plane), A p.1 * B p)
      = ∫⁻ c : Plane, ∫⁻ v : ι → Plane, A c * B (c, v) := by
          rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
    _ ≤ ∫⁻ c : Plane, A c * heatPotentialRowBound t := by
          apply lintegral_mono
          intro c
          have hrow := lintegral_tensorHeatKernel_mul_shiftedPotential_le ht i x c
          calc (∫⁻ v : ι → Plane, A c * B (c, v))
              = A c * ∫⁻ v : ι → Plane, B (c, v) :=
                  lintegral_const_mul (A c)
                    (hB.comp (measurable_const.prodMk measurable_id))
            _ ≤ A c * heatPotentialRowBound t := mul_le_mul_right hrow (A c)
    _ = heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t) (b - a)) := by
          rw [lintegral_mul_const _ hA, hcenter]
          ac_rfl

/-- The incoming kernel factors into the merged-center and spectator heat kernels. -/
theorem ofReal_incomingKernel_eq_prod {n : ℕ} (β : CollisionPair n) {t : ℝ}
    (ht : 0 < t) (w : FusedConfiguration β) (x : Configuration n) :
    ENNReal.ofReal (incomingKernel β t w x) =
      (ENNReal.ofReal (heatKernel t (w.1 - x β.1.1)) *
        ENNReal.ofReal (heatKernel t (w.1 - x β.1.2))) *
        ∏ i : Spectator β,
          ENNReal.ofReal (heatKernel t (w.2 i - x i.1)) := by
  rw [incomingKernel_eq_prod]
  rw [ENNReal.ofReal_mul (mul_nonneg (Critical2DKPZ.heatKernel_pos ht _).le
    (Critical2DKPZ.heatKernel_pos ht _).le)]
  rw [ENNReal.ofReal_mul (Critical2DKPZ.heatKernel_pos ht _).le]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Critical2DKPZ.heatKernel_pos ht _).le)]

/-- The first member of the colliding pair is mapped to the fused position. -/
@[simp] theorem collisionEmbedding_pair_left {n : ℕ} (α : CollisionPair n)
    (z : FusedConfiguration α) : (collisionEmbedding α z) α.1.1 = z.1 := by
  simp [collisionEmbedding]

/-- The second member of the colliding pair is mapped to the fused position. -/
@[simp] theorem collisionEmbedding_pair_right {n : ℕ} (α : CollisionPair n)
    (z : FusedConfiguration α) : (collisionEmbedding α z) α.1.2 = z.1 := by
  simp [collisionEmbedding]

/-- The collision embedding preserves each spectator position. -/
@[simp] theorem collisionEmbedding_spectator_apply {n : ℕ} (α : CollisionPair n)
    (z : FusedConfiguration α) (i : Spectator α) :
    (collisionEmbedding α z) i.1 = z.2 i := by
  simp [collisionEmbedding, i.2.1, i.2.2]

/-- The heat potential of a displacement is unchanged when its endpoints are exchanged. -/
theorem heatPotential_sub_swap (x y : Plane) :
    heatPotential (x - y) = heatPotential (y - x) := by
  rw [← neg_sub y x, heatPotential_neg]

/-- Difference of two independent planar coordinates is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_plane_sub :
    QuasiMeasurePreserving (fun p : Plane × Plane => p.1 - p.2)
      (volume.prod volume) volume := by
  exact (quasiMeasurePreserving_fst (μ := (volume : Measure Plane))
    (ν := (volume : Measure Plane))).comp
      (measurePreserving_sub_prod (μ := (volume : Measure Plane))
        (ν := (volume : Measure Plane))).quasiMeasurePreserving

/-- Two distinct coordinates of a finite product have a planar difference with
the same null sets as planar volume. -/
theorem quasiMeasurePreserving_pi_coordinateDiff {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    QuasiMeasurePreserving (fun y : ι → Plane => y i - y j)
      (volume : Measure (ι → Plane)) volume := by
  classical
  let κ := {k : ι // k ≠ i}
  let j' : κ := ⟨j, hij.symm⟩
  have he : QuasiMeasurePreserving (fun v : κ → Plane => v j')
      (volume : Measure (κ → Plane)) volume :=
    quasiMeasurePreserving_eval (fun _ : κ => (volume : Measure Plane)) j'
  have hid : QuasiMeasurePreserving id (volume : Measure Plane) volume :=
    QuasiMeasurePreserving.id _
  have hprod := MeasureTheory.QuasiMeasurePreserving.prodMap he hid
  have hswap := (measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure Plane))).quasiMeasurePreserving
  have hsplit := (measurePreserving_splitCoordinate i).quasiMeasurePreserving
  have hcomp := hswap.comp hprod |>.comp hsplit
  have hdiff := quasiMeasurePreserving_plane_sub.comp hcomp
  have heq : ((fun p : Plane × Plane => p.1 - p.2) ∘
      (Prod.swap ∘ Prod.map (fun v : κ → Plane => v j') id) ∘ splitCoordinate i) =
      (fun y => y i - y j) := by
    funext y
    simp [splitCoordinate_apply, j']
  exact hdiff.congr (by fun_prop)
    (Filter.Eventually.of_forall fun y => congrFun heq y)

/-- Difference of a spectator coordinate and the fused center has the same
null sets as planar volume. -/
theorem quasiMeasurePreserving_fused_centerDiff {ι : Type*} [Fintype ι]
    (i : ι) :
    QuasiMeasurePreserving (fun p : Plane × (ι → Plane) => p.2 i - p.1)
      (volume : Measure (Plane × (ι → Plane))) volume := by
  have he : QuasiMeasurePreserving (fun v : ι → Plane => v i)
      (volume : Measure (ι → Plane)) volume :=
    quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure Plane)) i
  have hid : QuasiMeasurePreserving id (volume : Measure Plane) volume :=
    QuasiMeasurePreserving.id _
  have hprod := MeasureTheory.QuasiMeasurePreserving.prodMap he hid
  have hin := (measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure (ι → Plane)))).quasiMeasurePreserving
  have hpair := hprod.comp hin
  have hsub := quasiMeasurePreserving_plane_sub.comp hpair
  have hsource : (volume : Measure (Plane × (ι → Plane))) =
      (volume : Measure Plane).prod (volume : Measure (ι → Plane)) :=
    Measure.volume_eq_prod Plane (ι → Plane)
  rw [hsource]
  exact hsub

/-- Difference of two spectator coordinates, viewed on a fused space, has the
same null sets as planar volume. -/
theorem quasiMeasurePreserving_fused_spectatorDiff {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    QuasiMeasurePreserving (fun p : Plane × (ι → Plane) => p.2 i - p.2 j)
      (volume : Measure (Plane × (ι → Plane))) volume := by
  have hsnd : QuasiMeasurePreserving Prod.snd
      (volume : Measure (Plane × (ι → Plane))) (volume : Measure (ι → Plane)) := by
    rw [Measure.volume_eq_prod]
    exact quasiMeasurePreserving_snd
  exact (quasiMeasurePreserving_pi_coordinateDiff i j hij).comp hsnd

/-- A swapping row with its potential weight expressed on two beta spectators. -/
theorem lintegral_swappingPotential_row_of_spectatorPair {n : ℕ}
    (α β : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (z : FusedConfiguration α) (i j : Spectator β) (hij : i ≠ j)
    (hweight : ∀ w : FusedConfiguration β,
      heatPotential ((collisionEmbedding β w) α.1.1 -
        (collisionEmbedding β w) α.1.2) = heatPotential (w.2 i - w.2 j)) :
    (∫⁻ w : FusedConfiguration β,
      ENNReal.ofReal (swappingKernel α β t z w) *
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2)) ≤
      heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t)
        ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)) := by
  let x := collisionEmbedding α z
  have hswap (w : FusedConfiguration β) :
      swappingKernel α β t z w = incomingKernel β t w x := by
    simp [swappingKernel, incomingKernel, x]
  have he (w : FusedConfiguration β) :
      ENNReal.ofReal (swappingKernel α β t z w) *
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2) =
      (ENNReal.ofReal (heatKernel t (w.1 - x β.1.1)) *
        ENNReal.ofReal (heatKernel t (w.1 - x β.1.2))) *
        ((∏ k : Spectator β,
          ENNReal.ofReal (heatKernel t (w.2 k - x k.1))) *
          heatPotential (w.2 i - w.2 j)) := by
    rw [hswap, ofReal_incomingKernel_eq_prod β ht w x, hweight]
    ac_rfl
  calc (∫⁻ w : FusedConfiguration β,
        ENNReal.ofReal (swappingKernel α β t z w) *
          heatPotential ((collisionEmbedding β w) α.1.1 -
            (collisionEmbedding β w) α.1.2))
      = ∫⁻ w : FusedConfiguration β,
          (ENNReal.ofReal (heatKernel t (w.1 - x β.1.1)) *
            ENNReal.ofReal (heatKernel t (w.1 - x β.1.2))) *
            ((∏ k : Spectator β,
              ENNReal.ofReal (heatKernel t (w.2 k - x k.1))) *
              heatPotential (w.2 i - w.2 j)) := by
                apply lintegral_congr
                exact he
    _ ≤ heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t)
          (x β.1.2 - x β.1.1)) := by
            exact lintegral_fusedPairPotential_row_le ht (x β.1.1) (x β.1.2)
              (fun k : Spectator β => x k.1) i j hij

/-- A swapping row with its potential weight expressed between a beta spectator
and the merged center. -/
theorem lintegral_swappingPotential_row_of_centerSpectator {n : ℕ}
    (α β : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (z : FusedConfiguration α) (i : Spectator β)
    (hweight : ∀ w : FusedConfiguration β,
      heatPotential ((collisionEmbedding β w) α.1.1 -
        (collisionEmbedding β w) α.1.2) = heatPotential (w.2 i - w.1)) :
    (∫⁻ w : FusedConfiguration β,
      ENNReal.ofReal (swappingKernel α β t z w) *
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2)) ≤
      heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t)
        ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)) := by
  let x := collisionEmbedding α z
  have hswap (w : FusedConfiguration β) :
      swappingKernel α β t z w = incomingKernel β t w x := by
    simp [swappingKernel, incomingKernel, x]
  have he (w : FusedConfiguration β) :
      ENNReal.ofReal (swappingKernel α β t z w) *
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2) =
      (ENNReal.ofReal (heatKernel t (w.1 - x β.1.1)) *
        ENNReal.ofReal (heatKernel t (w.1 - x β.1.2))) *
        ((∏ k : Spectator β,
          ENNReal.ofReal (heatKernel t (w.2 k - x k.1))) *
          heatPotential (w.2 i - w.1)) := by
    rw [hswap, ofReal_incomingKernel_eq_prod β ht w x, hweight]
    ac_rfl
  calc (∫⁻ w : FusedConfiguration β,
        ENNReal.ofReal (swappingKernel α β t z w) *
          heatPotential ((collisionEmbedding β w) α.1.1 -
            (collisionEmbedding β w) α.1.2))
      = ∫⁻ w : FusedConfiguration β,
          (ENNReal.ofReal (heatKernel t (w.1 - x β.1.1)) *
            ENNReal.ofReal (heatKernel t (w.1 - x β.1.2))) *
            ((∏ k : Spectator β,
              ENNReal.ofReal (heatKernel t (w.2 k - x k.1))) *
              heatPotential (w.2 i - w.1)) := by
                apply lintegral_congr
                exact he
    _ ≤ heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t)
          (x β.1.2 - x β.1.1)) := by
            exact lintegral_fusedShiftedPotential_row_le ht (x β.1.1) (x β.1.2)
              (fun k : Spectator β => x k.1) i

/-- The potential row bound for disjoint collision pairs. -/
theorem lintegral_swappingPotential_row_disjoint {n : ℕ}
    (α β : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (z : FusedConfiguration α)
    (h11 : α.1.1 ≠ β.1.1) (h12 : α.1.1 ≠ β.1.2)
    (h21 : α.1.2 ≠ β.1.1) (h22 : α.1.2 ≠ β.1.2) :
    (∫⁻ w : FusedConfiguration β,
      ENNReal.ofReal (swappingKernel α β t z w) *
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2)) ≤
      heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t)
        ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)) := by
  let i : Spectator β := ⟨α.1.1, ⟨h11, h12⟩⟩
  let j : Spectator β := ⟨α.1.2, ⟨h21, h22⟩⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Subtype.val he
    exact (ne_of_lt α.2) hv
  apply lintegral_swappingPotential_row_of_spectatorPair α β ht z i j hij
  intro w
  change heatPotential ((collisionEmbedding β w) i.1 -
      (collisionEmbedding β w) j.1) = heatPotential (w.2 i - w.2 j)
  rw [collisionEmbedding_spectator_apply, collisionEmbedding_spectator_apply]

/-- The potential-weighted swapping row bound for every distinct pair of
collision labels. -/
theorem lintegral_swappingPotential_row_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) {t : ℝ} (ht : 0 < t)
    (z : FusedConfiguration α) :
    (∫⁻ w : FusedConfiguration β,
      ENNReal.ofReal (swappingKernel α β t z w) *
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2)) ≤
      heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t)
        ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)) := by
  by_cases h11 : α.1.1 = β.1.1
  · have h12 : α.1.1 ≠ β.1.2 := by
      intro h
      have hα := α.2
      have hβ := β.2
      omega
    have h21 : α.1.2 ≠ β.1.1 := by
      intro h
      have hα := α.2
      have hβ := β.2
      omega
    have h22 : α.1.2 ≠ β.1.2 := by
      intro h
      apply hne
      apply Subtype.ext
      exact Prod.ext h11 h
    let i : Spectator β := ⟨α.1.2, ⟨h21, h22⟩⟩
    apply lintegral_swappingPotential_row_of_centerSpectator α β ht z i
    intro w
    have hfirst : (collisionEmbedding β w) α.1.1 = w.1 := by
      rw [h11, collisionEmbedding_pair_left]
    have hsecond : (collisionEmbedding β w) α.1.2 = w.2 i := by
      rw [show α.1.2 = i.1 by rfl, collisionEmbedding_spectator_apply]
    rw [hfirst, hsecond]
    exact heatPotential_sub_swap _ _
  · by_cases h12 : α.1.1 = β.1.2
    · have h21 : α.1.2 ≠ β.1.1 := by
        intro h
        have hα := α.2
        have hβ := β.2
        omega
      have h22 : α.1.2 ≠ β.1.2 := by
        intro h
        have hα := α.2
        omega
      let i : Spectator β := ⟨α.1.2, ⟨h21, h22⟩⟩
      apply lintegral_swappingPotential_row_of_centerSpectator α β ht z i
      intro w
      have hfirst : (collisionEmbedding β w) α.1.1 = w.1 := by
        rw [h12, collisionEmbedding_pair_right]
      have hsecond : (collisionEmbedding β w) α.1.2 = w.2 i := by
        rw [show α.1.2 = i.1 by rfl, collisionEmbedding_spectator_apply]
      rw [hfirst, hsecond]
      exact heatPotential_sub_swap _ _
    · by_cases h21 : α.1.2 = β.1.1
      · have h12' : α.1.1 ≠ β.1.2 := h12
        let i : Spectator β := ⟨α.1.1, ⟨h11, h12'⟩⟩
        apply lintegral_swappingPotential_row_of_centerSpectator α β ht z i
        intro w
        have hfirst : (collisionEmbedding β w) α.1.1 = w.2 i := by
          rw [show α.1.1 = i.1 by rfl, collisionEmbedding_spectator_apply]
        have hsecond : (collisionEmbedding β w) α.1.2 = w.1 := by
          rw [h21, collisionEmbedding_pair_left]
        rw [hfirst, hsecond]
      · by_cases h22 : α.1.2 = β.1.2
        · have h12' : α.1.1 ≠ β.1.2 := by
            intro h
            have hα := α.2
            omega
          have h21' : α.1.1 ≠ β.1.1 := h11
          let i : Spectator β := ⟨α.1.1, ⟨h21', h12'⟩⟩
          apply lintegral_swappingPotential_row_of_centerSpectator α β ht z i
          intro w
          have hfirst : (collisionEmbedding β w) α.1.1 = w.2 i := by
            rw [show α.1.1 = i.1 by rfl, collisionEmbedding_spectator_apply]
          have hsecond : (collisionEmbedding β w) α.1.2 = w.1 := by
            rw [h22, collisionEmbedding_pair_right]
          rw [hfirst, hsecond]
        · exact lintegral_swappingPotential_row_disjoint α β ht z h11 h12 h21 h22

/-- The potential weight for a distinct pair is finite almost everywhere on
the fused input space. -/
theorem heatPotential_swappingWeight_ne_top_ae {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) :
    ∀ᵐ w : FusedConfiguration β,
      heatPotential ((collisionEmbedding β w) α.1.1 -
        (collisionEmbedding β w) α.1.2) ≠ ⊤ := by
  by_cases h11 : α.1.1 = β.1.1
  · have h12 : α.1.1 ≠ β.1.2 := by
      intro h
      have hα := α.2
      have hβ := β.2
      omega
    have h21 : α.1.2 ≠ β.1.1 := by
      intro h
      have hα := α.2
      have hβ := β.2
      omega
    have h22 : α.1.2 ≠ β.1.2 := by
      intro h
      apply hne
      apply Subtype.ext
      exact Prod.ext h11 h
    let i : Spectator β := ⟨α.1.2, ⟨h21, h22⟩⟩
    have hweight (w : FusedConfiguration β) :
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2) = heatPotential (w.2 i - w.1) := by
      have hfirst : (collisionEmbedding β w) α.1.1 = w.1 := by
        rw [h11, collisionEmbedding_pair_left]
      have hsecond : (collisionEmbedding β w) α.1.2 = w.2 i := by
        rw [show α.1.2 = i.1 by rfl, collisionEmbedding_spectator_apply]
      rw [hfirst, hsecond]
      exact heatPotential_sub_swap _ _
    have ha := (quasiMeasurePreserving_fused_centerDiff i).ae heatPotential_ne_top_ae
    filter_upwards [ha] with w hw
    rw [hweight]
    exact hw
  · by_cases h12 : α.1.1 = β.1.2
    · have h21 : α.1.2 ≠ β.1.1 := by
        intro h
        have hα := α.2
        have hβ := β.2
        omega
      have h22 : α.1.2 ≠ β.1.2 := by
        intro h
        have hα := α.2
        omega
      let i : Spectator β := ⟨α.1.2, ⟨h21, h22⟩⟩
      have hweight (w : FusedConfiguration β) :
          heatPotential ((collisionEmbedding β w) α.1.1 -
            (collisionEmbedding β w) α.1.2) = heatPotential (w.2 i - w.1) := by
        have hfirst : (collisionEmbedding β w) α.1.1 = w.1 := by
          rw [h12, collisionEmbedding_pair_right]
        have hsecond : (collisionEmbedding β w) α.1.2 = w.2 i := by
          rw [show α.1.2 = i.1 by rfl, collisionEmbedding_spectator_apply]
        rw [hfirst, hsecond]
        exact heatPotential_sub_swap _ _
      have ha := (quasiMeasurePreserving_fused_centerDiff i).ae heatPotential_ne_top_ae
      filter_upwards [ha] with w hw
      rw [hweight]
      exact hw
    · by_cases h21 : α.1.2 = β.1.1
      · let i : Spectator β := ⟨α.1.1, ⟨h11, h12⟩⟩
        have hweight (w : FusedConfiguration β) :
            heatPotential ((collisionEmbedding β w) α.1.1 -
              (collisionEmbedding β w) α.1.2) = heatPotential (w.2 i - w.1) := by
          have hfirst : (collisionEmbedding β w) α.1.1 = w.2 i := by
            rw [show α.1.1 = i.1 by rfl, collisionEmbedding_spectator_apply]
          have hsecond : (collisionEmbedding β w) α.1.2 = w.1 := by
            rw [h21, collisionEmbedding_pair_left]
          rw [hfirst, hsecond]
        have ha := (quasiMeasurePreserving_fused_centerDiff i).ae heatPotential_ne_top_ae
        filter_upwards [ha] with w hw
        rw [hweight]
        exact hw
      · by_cases h22 : α.1.2 = β.1.2
        · have h12' : α.1.1 ≠ β.1.2 := by
            intro h
            have hα := α.2
            omega
          let i : Spectator β := ⟨α.1.1, ⟨h11, h12'⟩⟩
          have hweight (w : FusedConfiguration β) :
              heatPotential ((collisionEmbedding β w) α.1.1 -
                (collisionEmbedding β w) α.1.2) = heatPotential (w.2 i - w.1) := by
            have hfirst : (collisionEmbedding β w) α.1.1 = w.2 i := by
              rw [show α.1.1 = i.1 by rfl, collisionEmbedding_spectator_apply]
            have hsecond : (collisionEmbedding β w) α.1.2 = w.1 := by
              rw [h22, collisionEmbedding_pair_right]
            rw [hfirst, hsecond]
          have ha := (quasiMeasurePreserving_fused_centerDiff i).ae heatPotential_ne_top_ae
          filter_upwards [ha] with w hw
          rw [hweight]
          exact hw
        · let i : Spectator β := ⟨α.1.1, ⟨h11, h12⟩⟩
          let j : Spectator β := ⟨α.1.2, ⟨h21, h22⟩⟩
          have hweight (w : FusedConfiguration β) :
              heatPotential ((collisionEmbedding β w) α.1.1 -
                (collisionEmbedding β w) α.1.2) = heatPotential (w.2 i - w.2 j) := by
            change heatPotential ((collisionEmbedding β w) i.1 -
                (collisionEmbedding β w) j.1) = heatPotential (w.2 i - w.2 j)
            rw [collisionEmbedding_spectator_apply, collisionEmbedding_spectator_apply]
          have hij : i ≠ j := by
            intro he
            have hv := congrArg Subtype.val he
            exact (ne_of_lt α.2) hv
          have ha := (quasiMeasurePreserving_fused_spectatorDiff i j hij).ae
            heatPotential_ne_top_ae
          filter_upwards [ha] with w hw
          rw [hweight]
          exact hw

end Critical2DKPZ.DeltaBose
