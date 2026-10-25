/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleGapKernel
public import Critical2DKPZ.SHF.Flow.HeatConvolutionENN
public import Critical2DKPZ.SHF.Flow.ScalarCutUniqueness
public import Critical2DKPZ.SHF.DeltaBose.MomentKernelTwoL2
import Mathlib.Tactic

/-! # Convolution identities for the center and gap heat strands -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Pulling a measurable constant through the time triangle in the ENNReal
form. -/
theorem lintegral_const_mul_timeTriangle {h : ℝ} {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (c : ℝ≥0∞) :
    (∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h, c * F r u) =
      c * ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h, F r u := by
  have hInner (r : ℝ) : Measurable (fun u : ℝ => F r u) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hOuter : Measurable (fun r : ℝ => ∫⁻ u in Ioo r h, F r u) :=
    measurable_lintegral_Ioo measurable_id measurable_const hF
  calc
    (∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h, c * F r u) =
        ∫⁻ r in Ioo (0 : ℝ) h, c * ∫⁻ u in Ioo r h, F r u := by
          apply lintegral_congr_ae
          filter_upwards [] with r
          exact lintegral_const_mul c (hInner r)
    _ = c * ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h, F r u :=
      lintegral_const_mul c hOuter

/-- Fubini reverses the two integrations on an ordered positive-time triangle. -/
theorem lintegral_positiveTriangle_flip {b : ℝ} {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ v in Ioo (0 : ℝ) b, ∫⁻ w in Ioo v b, F v w) =
      ∫⁻ w in Ioo (0 : ℝ) b, ∫⁻ v in Ioo (0 : ℝ) w, F v w := by
  let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < b}
  let G : ℝ → ℝ → ℝ≥0∞ := fun v w => if (v, w) ∈ S then F v w else 0
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hG : Measurable (Function.uncurry G) := by
    dsimp [G]
    exact Measurable.ite hS hF measurable_const
  have hleft : (∫⁻ v in Ioo (0 : ℝ) b, ∫⁻ w in Ioo v b, F v w) =
      ∫⁻ v, ∫⁻ w, G v w := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr_ae
    filter_upwards [] with v
    by_cases hv : v ∈ Ioo (0 : ℝ) b
    · simp only [Set.indicator_of_mem hv]
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr_ae
      filter_upwards [] with w
      by_cases hw : w ∈ Ioo v b
      · have hcond : (v, w) ∈ S := by
          dsimp [S]
          exact ⟨hv.1, ⟨hw.1, hw.2⟩⟩
        change Set.indicator (Ioo v b) (fun w => F v w) w = G v w
        rw [Set.indicator_of_mem hw]
        change F v w = (if (v, w) ∈ S then F v w else 0)
        rw [ite_eq_left hcond]
      · have hcond : (v, w) ∉ S := by
          dsimp [S]
          rintro ⟨_, hvw, hwb⟩
          exact hw ⟨hvw, hwb⟩
        change Set.indicator (Ioo v b) (fun w => F v w) w = G v w
        rw [Set.indicator_of_notMem hw]
        change 0 = (if (v, w) ∈ S then F v w else 0)
        rw [ite_eq_right hcond]
    · have hcond (w : ℝ) : (v, w) ∉ S := by
        dsimp [S]
        rintro ⟨hv0, hvw, hwb⟩
        exact hv ⟨hv0, hvw.trans hwb⟩
      simp only [Set.indicator_of_notMem hv]
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with w
      change (if (v, w) ∈ S then F v w else 0) = 0
      rw [ite_eq_right (hcond w)]
  have hright : (∫⁻ w in Ioo (0 : ℝ) b, ∫⁻ v in Ioo (0 : ℝ) w, F v w) =
      ∫⁻ w, ∫⁻ v, G v w := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr_ae
    filter_upwards [] with w
    by_cases hw : w ∈ Ioo (0 : ℝ) b
    · simp only [Set.indicator_of_mem hw]
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr_ae
      filter_upwards [] with v
      by_cases hv : v ∈ Ioo (0 : ℝ) w
      · have hcond : (v, w) ∈ S := by
          dsimp [S]
          exact ⟨hv.1, ⟨hv.2, hw.2⟩⟩
        change Set.indicator (Ioo (0 : ℝ) w) (fun v => F v w) v = G v w
        rw [Set.indicator_of_mem hv]
        change F v w = (if (v, w) ∈ S then F v w else 0)
        rw [ite_eq_left hcond]
      · have hcond : (v, w) ∉ S := by
          dsimp [S]
          rintro ⟨hv0, hvw, _⟩
          exact hv ⟨hv0, hvw⟩
        change Set.indicator (Ioo (0 : ℝ) w) (fun v => F v w) v = G v w
        rw [Set.indicator_of_notMem hv]
        change 0 = (if (v, w) ∈ S then F v w else 0)
        rw [ite_eq_right hcond]
    · have hcond (v : ℝ) : (v, w) ∉ S := by
        dsimp [S]
        rintro ⟨hv0, hvw, hwb⟩
        exact hw ⟨hv0.trans hvw, hwb⟩
      simp only [Set.indicator_of_notMem hw]
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with v
      change (if (v, w) ∈ S then F v w else 0) = 0
      rw [ite_eq_right (hcond v)]
  calc
    _ = ∫⁻ v, ∫⁻ w, G v w := hleft
    _ = ∫⁻ w, ∫⁻ v, G v w := lintegral_lintegral_swap hG.aemeasurable
    _ = _ := hright.symm

/-- The scalar cut identity in product Lebesgue coordinates, in the form used
when a collision interval crosses a fixed time cut. -/
theorem scalarCutKernelENN_ae_eq_sum_product (θ : ℝ) :
    ∀ᵐ q : ℝ × ℝ ∂(volume.prod volume),
      0 < q.1 → 0 < q.2 →
        scalarCutKernelENN θ q.1 q.2 =
          ENNReal.ofReal (scalarDensity θ (q.1 + q.2)) := by
  let Q : Set Plane := Critical2DKPZ.Analysis.positiveQuadrant
  have hQ : MeasurableSet Q := by
    change MeasurableSet ({p : Plane | 0 < p 0} ∩ {p | 0 < p 1})
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt measurable_const (by fun_prop))
  have hplane := scalarCutKernelENN_ae_eq_ofReal_scalarDensity_sum θ
  have hplane' : ∀ᵐ p ∂volume,
      p ∈ Q → scalarCutKernelENN θ (planeCoordEquiv p).1 (planeCoordEquiv p).2 =
        ENNReal.ofReal (scalarDensity θ (p 0 + p 1)) :=
    ae_imp_of_ae_restrict hplane
  have hcoords := measurePreserving_planeCoordEquiv.symm.quasiMeasurePreserving.ae hplane'
  filter_upwards [hcoords] with q hq
  have hpos : planeCoordEquiv.symm q ∈ Q ↔ 0 < q.1 ∧ 0 < q.2 := by
    simp [Q, planeCoordEquiv, Critical2DKPZ.Analysis.positiveQuadrant,
      MeasurableEquiv.trans_apply]
  intro hq₁ hq₂
  have hqQ : planeCoordEquiv.symm q ∈ Q := hpos.mpr ⟨hq₁, hq₂⟩
  have h := hq hqQ
  simpa [planeCoordEquiv, MeasurableEquiv.trans_apply] using h


/-- The scalar cut identity remains valid after reflecting its first time
coordinate inside a bounded interval. -/
theorem scalarCutKernelENN_ae_eq_sum_reflect (θ a : ℝ) :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      p.1 ∈ Ioo (0 : ℝ) a → 0 < p.2 →
        scalarCutKernelENN θ (a - p.1) p.2 =
          ENNReal.ofReal (scalarDensity θ (a - p.1 + p.2)) := by
  let τ : ℝ × ℝ → ℝ × ℝ := fun p => (a - p.1, p.2)
  have hτ : MeasurePreserving τ (volume.prod volume) (volume.prod volume) :=
    (volume.measurePreserving_sub_left a).prod (MeasurePreserving.id volume)
  have h := hτ.quasiMeasurePreserving.ae (scalarCutKernelENN_ae_eq_sum_product θ)
  filter_upwards [h] with p hp
  intro hp₁ hp₂
  have hpos₁ : 0 < a - p.1 := sub_pos.mpr hp₁.2
  simpa only [τ] using hp hpos₁ hp₂

/-- Integrating the reflected scalar cut kernel over a rectangle is the same
as integrating the scalar density at the sum of the cut durations. -/
theorem lintegral_scalarCutKernelENN_reflect_rect {θ a b : ℝ}
    {W : ℝ × ℝ → ℝ≥0∞} (hW : Measurable W) :
    (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
      W (r, v) * scalarCutKernelENN θ (a - r) v) =
    (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
      W (r, v) * ENNReal.ofReal (scalarDensity θ (a - r + v))) := by
  let R : Set (ℝ × ℝ) := Ioo (0 : ℝ) a ×ˢ Ioo (0 : ℝ) b
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => W p * scalarCutKernelENN θ (a - p.1) p.2
  let G : ℝ × ℝ → ℝ≥0∞ := fun p => W p *
    ENNReal.ofReal (scalarDensity θ (a - p.1 + p.2))
  have hF : Measurable F := by
    dsimp [F]
    exact hW.mul ((measurable_scalarCutKernelENN θ).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))
  have hG : Measurable G := by
    dsimp [G]
    exact hW.mul ((measurable_scalarDensity.comp (by fun_prop :
      Measurable (fun p : ℝ × ℝ => (θ, a - p.1 + p.2)))).ennreal_ofReal)
  have hR : MeasurableSet R := measurableSet_Ioo.prod measurableSet_Ioo
  have hEq : ∫⁻ p in R, F p ∂(volume.prod volume) =
      ∫⁻ p in R, G p ∂(volume.prod volume) := by
    apply lintegral_congr_ae
    filter_upwards [(scalarCutKernelENN_ae_eq_sum_reflect θ a).filter_mono ae_restrict_le,
      ae_restrict_mem hR] with p hp hmem
    change p.1 ∈ Ioo (0 : ℝ) a ∧ p.2 ∈ Ioo (0 : ℝ) b at hmem
    have hcut := hp hmem.1 hmem.2.1
    simp only [F, G]
    rw [hcut]
  calc
    _ = ∫⁻ p in R, F p ∂(volume.prod volume) := by
      rw [setLIntegral_prod F (hF.aemeasurable.restrict)]
    _ = ∫⁻ p in R, G p ∂(volume.prod volume) := hEq
    _ = _ := by rw [setLIntegral_prod G (hG.aemeasurable.restrict)]

/-- Fubini exchanges two bounded interval variables. -/
theorem lintegral_Ioo_rectangle_swap {a b c d : ℝ} {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, F x y) =
      ∫⁻ y in Ioo c d, ∫⁻ x in Ioo a b, F x y := by
  exact lintegral_lintegral_swap hF.aemeasurable

/-- The product of two gap collision contributions is the four-time integral
with the reciprocal free bridge between the collisions. -/
theorem twoParticleGapCollisionKernel_mul_collision_quadIntegral
    {a b θ : ℝ} (x y : Plane) :
    (∫⁻ z : Plane,
      twoParticleGapCollisionKernel θ a x z * twoParticleGapCollisionKernel θ b z y) =
      ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
        ∫⁻ s in Ioo (0 : ℝ) b, ∫⁻ v in Ioo s b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            (ENNReal.ofReal (heatKernel (2 * r) x) *
              (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (v - s)) *
                (ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
                  ENNReal.ofReal ((4 * Real.pi * (a - u + s))⁻¹)))) := by
  let SA : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < a}
  let SB : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < b}
  let LA : (ℝ × ℝ) → Plane → ℝ≥0∞ := fun p z =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (p.2 - p.1)) *
      (ENNReal.ofReal (heatKernel (2 * p.1) x) *
        ENNReal.ofReal (heatKernel (2 * (a - p.2)) z))
  let LB : (ℝ × ℝ) → Plane → ℝ≥0∞ := fun p z =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (p.2 - p.1)) *
      (ENNReal.ofReal (heatKernel (2 * p.1) z) *
        ENNReal.ofReal (heatKernel (2 * (b - p.2)) y))
  let FA : Plane → (ℝ × ℝ) → ℝ≥0∞ := fun z p => if p ∈ SA then LA p z else 0
  let FB : Plane → (ℝ × ℝ) → ℝ≥0∞ := fun z p => if p ∈ SB then LB p z else 0
  have hSA : MeasurableSet SA := by
    dsimp [SA]
    measurability
  have hSB : MeasurableSet SB := by
    dsimp [SB]
    measurability
  have hLA : Measurable (fun q : ((ℝ × ℝ) × Plane) => LA q.1 q.2) := by
    dsimp [LA]
    have hmCoeff : Measurable (fun q : (ℝ × ℝ) × Plane =>
        4 * Real.pi * scalarDensity θ (q.1.2 - q.1.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun q : (ℝ × ℝ) × Plane => (θ, q.1.2 - q.1.1))))
    have hmStart : Measurable (fun q : (ℝ × ℝ) × Plane => heatKernel (2 * q.1.1) x) := by
      unfold heatKernel
      fun_prop
    have hmTail : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * (a - q.1.2)) q.2) := by
      unfold heatKernel
      fun_prop
    exact hmCoeff.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
  have hLB : Measurable (fun q : ((ℝ × ℝ) × Plane) => LB q.1 q.2) := by
    dsimp [LB]
    have hmCoeff : Measurable (fun q : (ℝ × ℝ) × Plane =>
        4 * Real.pi * scalarDensity θ (q.1.2 - q.1.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun q : (ℝ × ℝ) × Plane => (θ, q.1.2 - q.1.1))))
    have hmStart : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * q.1.1) q.2) := by
      unfold heatKernel
      fun_prop
    have hmTail : Measurable (fun q : (ℝ × ℝ) × Plane => heatKernel (2 * (b - q.1.2)) y) := by
      unfold heatKernel
      fun_prop
    exact hmCoeff.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
  have hFA : Measurable (Function.uncurry FA) := by
    dsimp [Function.uncurry, FA]
    have hcomp : Measurable (fun q : Plane × (ℝ × ℝ) => LA q.2 q.1) := by
      dsimp [LA]
      have hmCoeff : Measurable (fun q : Plane × (ℝ × ℝ) =>
          4 * Real.pi * scalarDensity θ (q.2.2 - q.2.1)) := by
        exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
          Measurable (fun q : Plane × (ℝ × ℝ) => (θ, q.2.2 - q.2.1))))
      have hmStart : Measurable (fun q : Plane × (ℝ × ℝ) =>
          heatKernel (2 * q.2.1) x) := by
        unfold heatKernel
        fun_prop
      have hmTail : Measurable (fun q : Plane × (ℝ × ℝ) =>
          heatKernel (2 * (a - q.2.2)) q.1) := by
        unfold heatKernel
        fun_prop
      exact hmCoeff.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
    exact Measurable.ite (measurableSet_preimage measurable_snd hSA)
      hcomp measurable_const
  have hFB : Measurable (Function.uncurry FB) := by
    dsimp [Function.uncurry, FB]
    have hcomp : Measurable (fun q : Plane × (ℝ × ℝ) => LB q.2 q.1) := by
      dsimp [LB]
      have hmCoeff : Measurable (fun q : Plane × (ℝ × ℝ) =>
          4 * Real.pi * scalarDensity θ (q.2.2 - q.2.1)) := by
        exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
          Measurable (fun q : Plane × (ℝ × ℝ) => (θ, q.2.2 - q.2.1))))
      have hmStart : Measurable (fun q : Plane × (ℝ × ℝ) =>
          heatKernel (2 * q.2.1) q.1) := by
        unfold heatKernel
        fun_prop
      have hmTail : Measurable (fun q : Plane × (ℝ × ℝ) =>
          heatKernel (2 * (b - q.2.2)) y) := by
        unfold heatKernel
        fun_prop
      exact hmCoeff.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
    exact Measurable.ite (measurableSet_preimage measurable_snd hSB)
      hcomp measurable_const
  let H : Plane → ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ≥0∞ :=
    fun z q => FA z q.1 * FB z q.2
  have hH : Measurable (Function.uncurry H) := by
    dsimp [Function.uncurry, H]
    exact (hFA.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hFB.comp (measurable_fst.prodMk measurable_snd.snd))
  let K : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun q => ∫⁻ z : Plane, H z q
  have hK : Measurable K := by
    dsimp [K]
    have hHswap : Measurable (Function.uncurry (fun q z => H z q)) := by
      exact hH.comp measurable_swap
    exact hHswap.lintegral_prod_right (ν := volume)
  have hLAfix (z : Plane) : Measurable (Function.uncurry (fun r u => LA (r, u) z)) := by
    dsimp [Function.uncurry, LA]
    have hmCoeff : Measurable (fun p : ℝ × ℝ =>
        4 * Real.pi * scalarDensity θ (p.2 - p.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1))))
    have hmStart : Measurable (fun p : ℝ × ℝ => heatKernel (2 * p.1) x) := by
      unfold heatKernel
      fun_prop
    have hmTail : Measurable (fun p : ℝ × ℝ => heatKernel (2 * (a - p.2)) z) := by
      unfold heatKernel
      fun_prop
    exact hmCoeff.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
  have hLBfix (z : Plane) : Measurable (Function.uncurry (fun r u => LB (r, u) z)) := by
    dsimp [Function.uncurry, LB]
    have hmCoeff : Measurable (fun p : ℝ × ℝ =>
        4 * Real.pi * scalarDensity θ (p.2 - p.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1))))
    have hmStart : Measurable (fun p : ℝ × ℝ => heatKernel (2 * p.1) z) := by
      unfold heatKernel
      fun_prop
    have hmTail : Measurable (fun p : ℝ × ℝ => heatKernel (2 * (b - p.2)) y) := by
      unfold heatKernel
      fun_prop
    exact hmCoeff.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
  have hCA (z : Plane) : twoParticleGapCollisionKernel θ a x z =
      ∫⁻ p : ℝ × ℝ, FA z p ∂(volume.prod volume) := by
    calc
      twoParticleGapCollisionKernel θ a x z =
          ∫⁻ p : ℝ × ℝ,
            ({p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < a}.indicator
              (Function.uncurry fun r u =>
                ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
                  (ENNReal.ofReal (heatKernel (2 * r) x) *
                    ENNReal.ofReal (heatKernel (2 * (a - u)) z))) p)
            ∂(volume.prod volume) :=
        Critical2DKPZ.DeltaBose.lintegral_orderedPair_eq a (hLAfix z)
      _ = ∫⁻ p : ℝ × ℝ, FA z p ∂(volume.prod volume) := by
        apply lintegral_congr_ae
        filter_upwards [] with p
        change Set.indicator SA (fun p : ℝ × ℝ => LA p z) p = FA z p
        simp [FA, SA, Set.indicator]
  have hCB (z : Plane) : twoParticleGapCollisionKernel θ b z y =
      ∫⁻ p : ℝ × ℝ, FB z p ∂(volume.prod volume) := by
    calc
      twoParticleGapCollisionKernel θ b z y =
          ∫⁻ p : ℝ × ℝ,
            ({p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < b}.indicator
              (Function.uncurry fun r u =>
                ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
                  (ENNReal.ofReal (heatKernel (2 * r) z) *
                    ENNReal.ofReal (heatKernel (2 * (b - u)) y))) p)
            ∂(volume.prod volume) :=
        Critical2DKPZ.DeltaBose.lintegral_orderedPair_eq b (hLBfix z)
      _ = ∫⁻ p : ℝ × ℝ, FB z p ∂(volume.prod volume) := by
        apply lintegral_congr_ae
        filter_upwards [] with p
        change Set.indicator SB (fun p : ℝ × ℝ => LB p z) p = FB z p
        simp [FB, SB, Set.indicator]
  have hproduct (z : Plane) :
      twoParticleGapCollisionKernel θ a x z * twoParticleGapCollisionKernel θ b z y =
        ∫⁻ p : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, H z (p, q)
          ∂(volume.prod volume) ∂(volume.prod volume) := by
    rw [hCA z, hCB z]
    exact (lintegral_lintegral_mul
      ((hFA.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      ((hFB.comp (measurable_const.prodMk measurable_id)).aemeasurable)).symm
  have hHfixed (z : Plane) :
      AEMeasurable (Function.uncurry (fun p q => H z (p, q)))
        ((volume.prod volume).prod (volume.prod volume)) := by
    exact (hH.comp (measurable_const.prodMk measurable_id)).aemeasurable
  let Base : (ℝ × ℝ) → (ℝ × ℝ) → ℝ≥0∞ := fun p q =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (p.2 - p.1)) *
      (ENNReal.ofReal (heatKernel (2 * p.1) x) *
        (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (q.2 - q.1)) *
          (ENNReal.ofReal (heatKernel (2 * (b - q.2)) y) *
            ENNReal.ofReal ((4 * Real.pi * (a - p.2 + q.1))⁻¹))))
  have hBase : Measurable (Function.uncurry Base) := by
    dsimp [Base]
    have hmCoeff₁ : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        4 * Real.pi * scalarDensity θ (w.1.2 - w.1.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (θ, w.1.2 - w.1.1))))
    have hmHeat₁ : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        heatKernel (2 * w.1.1) x) := by
      unfold heatKernel
      fun_prop
    have hmCoeff₂ : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        4 * Real.pi * scalarDensity θ (w.2.2 - w.2.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (θ, w.2.2 - w.2.1))))
    have hmHeat₂ : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        heatKernel (2 * (b - w.2.2)) y) := by
      unfold heatKernel
      fun_prop
    have hmRecip : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        (4 * Real.pi * (a - w.1.2 + w.2.1))⁻¹) := by fun_prop
    exact hmCoeff₁.ennreal_ofReal.mul (hmHeat₁.ennreal_ofReal.mul
      (hmCoeff₂.ennreal_ofReal.mul (hmHeat₂.ennreal_ofReal.mul hmRecip.ennreal_ofReal)))
  have hKval (p q : ℝ × ℝ) :
      K (p, q) = if p ∈ SA ∧ q ∈ SB then Base p q else 0 := by
    by_cases hp : p ∈ SA
    · by_cases hq : q ∈ SB
      · have hpoint (z : Plane) : H z (p, q) =
            (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (p.2 - p.1)) *
              (ENNReal.ofReal (heatKernel (2 * p.1) x) *
                (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (q.2 - q.1)) *
                  ENNReal.ofReal (heatKernel (2 * (b - q.2)) y)))) *
              (ENNReal.ofReal (heatKernel (2 * (a - p.2)) z) *
                ENNReal.ofReal (heatKernel (2 * q.1) z)) := by
          simp only [H, FA, FB, ite_eq_left hp, ite_eq_left hq, LA, LB]
          ac_rfl
        have hmHeat : Measurable (fun z : Plane =>
            ENNReal.ofReal (heatKernel (2 * (a - p.2)) z) *
              ENNReal.ofReal (heatKernel (2 * q.1) z)) := by
          exact ((measurable_heatKernel (2 * (a - p.2))).ennreal_ofReal).mul
            ((measurable_heatKernel (2 * q.1)).ennreal_ofReal)
        have hα : 0 < a - p.2 := sub_pos.mpr hp.2.2
        have hβ : 0 < q.1 := hq.1
        have hconvBase := lintegral_heatKernel_initialProduct
          (mul_pos (show 0 < (2 : ℝ) by norm_num) hα)
          (mul_pos (show 0 < (2 : ℝ) by norm_num) hβ) (0 : Plane) (0 : Plane)
        have heven : ∀ z : Plane,
            heatKernel (2 * q.1) (0 - z) = heatKernel (2 * q.1) z := by
          intro z
          rw [show 0 - z = -z by abel, heatKernel_neg]
        have hconv :
            (∫⁻ z : Plane,
              ENNReal.ofReal (heatKernel (2 * (a - p.2)) z) *
                ENNReal.ofReal (heatKernel (2 * q.1) z)) =
              ENNReal.ofReal ((4 * Real.pi * (a - p.2 + q.1))⁻¹) := by
          calc
            _ = ENNReal.ofReal
                (heatKernel (2 * ((a - p.2) + q.1)) (0 : Plane)) := by
                  simpa only [heven, show 2 * (a - p.2) + 2 * q.1 =
                    2 * ((a - p.2) + q.1) by ring, sub_zero, sub_self] using hconvBase
            _ = ENNReal.ofReal ((4 * Real.pi * (a - p.2 + q.1))⁻¹) := by
                  rw [heatKernel_at_zero]
                  congr 2
                  ring
        calc
          K (p, q) = ∫⁻ z : Plane,
              (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (p.2 - p.1)) *
                (ENNReal.ofReal (heatKernel (2 * p.1) x) *
                  (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (q.2 - q.1)) *
                    ENNReal.ofReal (heatKernel (2 * (b - q.2)) y)))) *
                (ENNReal.ofReal (heatKernel (2 * (a - p.2)) z) *
                  ENNReal.ofReal (heatKernel (2 * q.1) z)) := by
                  apply lintegral_congr_ae
                  filter_upwards [] with z
                  exact hpoint z
          _ = (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (p.2 - p.1)) *
                (ENNReal.ofReal (heatKernel (2 * p.1) x) *
                  (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (q.2 - q.1)) *
                    ENNReal.ofReal (heatKernel (2 * (b - q.2)) y)))) *
                ∫⁻ z : Plane,
                  ENNReal.ofReal (heatKernel (2 * (a - p.2)) z) *
                    ENNReal.ofReal (heatKernel (2 * q.1) z) :=
                  lintegral_const_mul _ hmHeat
          _ = Base p q := by
                rw [hconv]
                dsimp [Base]
                ac_rfl
          _ = if p ∈ SA ∧ q ∈ SB then Base p q else 0 := by
                rw [ite_eq_left ⟨hp, hq⟩]
      · have hz (z : Plane) : H z (p, q) = 0 := by simp [H, FA, FB, hq]
        simp [K, hz, hp, hq]
    · have hz (z : Plane) : H z (p, q) = 0 := by simp [H, FA, FB, hp]
      simp [K, hz, hp]
  have hRect : MeasurableSet (SA ×ˢ SB) := hSA.prod hSB
  calc
    (∫⁻ z : Plane,
        twoParticleGapCollisionKernel θ a x z * twoParticleGapCollisionKernel θ b z y) =
        ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), K q
          ∂((volume.prod volume).prod (volume.prod volume)) := by
          calc
            _ = ∫⁻ z : Plane, ∫⁻ p : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, H z (p, q)
                  ∂(volume.prod volume) ∂(volume.prod volume) := by
                    apply lintegral_congr_ae
                    filter_upwards [] with z
                    exact hproduct z
            _ = ∫⁻ z : Plane, ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), H z q
                  ∂((volume.prod volume).prod (volume.prod volume)) := by
                    apply lintegral_congr_ae
                    filter_upwards [] with z
                    exact lintegral_lintegral (hHfixed z)
            _ = ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), ∫⁻ z : Plane, H z q :=
                  lintegral_lintegral_swap hH.aemeasurable
            _ = ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), K q
                  ∂((volume.prod volume).prod (volume.prod volume)) := by
                  apply lintegral_congr_ae
                  filter_upwards [] with q
                  rfl
    _ = ∫⁻ p : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, K (p, q)
          ∂(volume.prod volume) ∂(volume.prod volume) :=
            lintegral_prod (μ := volume.prod volume) (ν := volume.prod volume)
              K hK.aemeasurable
    _ = ∫⁻ p in SA, ∫⁻ q in SB, Base p q := by
          calc
            (∫⁻ p : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, K (p, q)
                ∂(volume.prod volume) ∂(volume.prod volume)) =
                ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), K q
                  ∂((volume.prod volume).prod (volume.prod volume)) :=
                    (lintegral_prod (μ := volume.prod volume) (ν := volume.prod volume)
                      K hK.aemeasurable).symm
            _ = ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ),
                  (SA ×ˢ SB).indicator (Function.uncurry Base) q
                    ∂((volume.prod volume).prod (volume.prod volume)) := by
                  apply lintegral_congr_ae
                  filter_upwards [] with q
                  by_cases hq : q ∈ SA ×ˢ SB
                  · have hmem : q.1 ∈ SA ∧ q.2 ∈ SB := by
                      simpa only [Set.mem_prod] using hq
                    rw [Set.indicator_of_mem hq]
                    simp [hKval, hmem, Function.uncurry]
                  · have hmem : ¬(q.1 ∈ SA ∧ q.2 ∈ SB) := by
                      simpa only [Set.mem_prod] using hq
                    rw [Set.indicator_of_notMem hq]
                    simp [hKval, hmem]
            _ = ∫⁻ q in SA ×ˢ SB, Function.uncurry Base q
                  ∂((volume.prod volume).prod (volume.prod volume)) :=
                    lintegral_indicator hRect (Function.uncurry Base)
            _ = ∫⁻ p in SA, ∫⁻ q in SB, Base p q :=
                  setLIntegral_prod (μ := volume.prod volume) (ν := volume.prod volume)
                    (s := SA) (t := SB) (Function.uncurry Base)
                    (hBase.aemeasurable.restrict)
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
          ∫⁻ s in Ioo (0 : ℝ) b, ∫⁻ v in Ioo s b,
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
              (ENNReal.ofReal (heatKernel (2 * r) x) *
                (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (v - s)) *
                  (ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
                    ENNReal.ofReal ((4 * Real.pi * (a - u + s))⁻¹)))) := by
          have hBaseFix (p : ℝ × ℝ) :
              Measurable (Function.uncurry (fun s v => Base p (s, v))) := by
            change Measurable (fun q : ℝ × ℝ => Base p q)
            dsimp [Base]
            have hmCoeffStart : Measurable (fun q : ℝ × ℝ =>
                4 * Real.pi * scalarDensity θ (p.2 - p.1)) := measurable_const
            have hmCoeff : Measurable (fun q : ℝ × ℝ =>
                4 * Real.pi * scalarDensity θ (q.2 - q.1)) := by
              exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
                Measurable (fun q : ℝ × ℝ => (θ, q.2 - q.1))))
            have hmStart : Measurable (fun q : ℝ × ℝ => heatKernel (2 * p.1) x) :=
              measurable_const
            have hmTail : Measurable (fun q : ℝ × ℝ =>
                heatKernel (2 * (b - q.2)) y) := by
              unfold heatKernel
              fun_prop
            have hmRecip : Measurable (fun q : ℝ × ℝ =>
                (4 * Real.pi * (a - p.2 + q.1))⁻¹) := by fun_prop
            exact hmCoeffStart.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul
              (hmCoeff.ennreal_ofReal.mul (hmTail.ennreal_ofReal.mul
                hmRecip.ennreal_ofReal)))
          have hinner (p : ℝ × ℝ) :
              (∫⁻ q in SB, Base p q) =
                ∫⁻ s in Ioo (0 : ℝ) b, ∫⁻ v in Ioo s b, Base p (s, v) := by
            have hfun : Function.uncurry (fun s v => Base p (s, v)) =
                (fun q : ℝ × ℝ => Base p q) := by
              funext q
              cases q
              rfl
            calc
              (∫⁻ q in SB, Base p q) =
                  ∫⁻ q : ℝ × ℝ, SB.indicator (fun q => Base p q) q := by
                    rw [← lintegral_indicator hSB]
              _ = ∫⁻ s in Ioo (0 : ℝ) b, ∫⁻ v in Ioo s b, Base p (s, v) := by
                    have horder :=
                      (Critical2DKPZ.DeltaBose.lintegral_orderedPair_eq b
                        (hBaseFix p)).symm
                    rw [hfun] at horder
                    simpa only [SB] using horder
          have houterMeas : Measurable (fun p : ℝ × ℝ => ∫⁻ q in SB, Base p q) :=
            hBase.lintegral_prod_right (ν := volume.restrict SB)
          calc
            (∫⁻ p in SA, ∫⁻ q in SB, Base p q) =
                ∫⁻ p, SA.indicator (fun p => ∫⁻ q in SB, Base p q) p := by
                  rw [← lintegral_indicator hSA]
            _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
                  ∫⁻ q in SB, Base (r, u) q := by
                    have houterMeas' : Measurable (Function.uncurry
                        (fun r u => ∫⁻ q in SB, Base (r, u) q)) := by
                      change Measurable (fun p : ℝ × ℝ => ∫⁻ q in SB, Base p q)
                      exact houterMeas
                    exact (Critical2DKPZ.DeltaBose.lintegral_orderedPair_eq a
                      houterMeas').symm
            _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
                  ∫⁻ s in Ioo (0 : ℝ) b, ∫⁻ v in Ioo s b, Base (r, u) (s, v) := by
                    apply lintegral_congr_ae
                    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
                    apply lintegral_congr_ae
                    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
                    exact hinner (r, u)

/-- The center heat strand in the two-particle coordinates composes by the
ordinary planar heat semigroup. -/
theorem lintegral_twoParticle_center_heat_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : Plane) :
    (∫⁻ z : Plane,
      ENNReal.ofReal (heatKernel (a / 2) (z - x)) *
        ENNReal.ofReal (heatKernel (b / 2) (y - z))) =
      ENNReal.ofReal (heatKernel ((a + b) / 2) (y - x)) := by
  simpa only [show a / 2 + b / 2 = (a + b) / 2 by ring] using
    lintegral_heatKernel_initialProduct
      (div_pos ha (by norm_num : (0 : ℝ) < 2))
      (div_pos hb (by norm_num : (0 : ℝ) < 2)) x y

/-- The relative free strand composes by the planar heat semigroup with relative time `2t`. -/
theorem lintegral_twoParticle_gapHeat_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : Plane) :
    (∫⁻ z : Plane,
      ENNReal.ofReal (heatKernel (2 * a) (z - x)) *
        ENNReal.ofReal (heatKernel (2 * b) (y - z))) =
      ENNReal.ofReal (heatKernel (2 * (a + b)) (y - x)) := by
  simpa only [show 2 * a + 2 * b = 2 * (a + b) by ring] using
    lintegral_heatKernel_initialProduct
      (mul_pos (show 0 < (2 : ℝ) by norm_num) ha)
      (mul_pos (show 0 < (2 : ℝ) by norm_num) hb) x y


/-- The free relative-coordinate kernels compose. -/
theorem twoParticleGapFreeKernel_semigroup {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : Plane) :
    (∫⁻ z : Plane,
      twoParticleGapFreeKernel a x z * twoParticleGapFreeKernel b z y) =
      twoParticleGapFreeKernel (a + b) x y := by
  simpa only [twoParticleGapFreeKernel] using
    lintegral_twoParticle_gapHeat_mul ha hb x y

/-- A collision completed before the cut composes with a free strand to give
the corresponding part of the longer collision triangle. -/
theorem twoParticleGapCollision_free_piece {a b θ : ℝ} (hb : 0 < b)
    (x y : Plane) :
    (∫⁻ z : Plane,
      twoParticleGapCollisionKernel θ a x z * twoParticleGapFreeKernel b z y) =
      ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
          (ENNReal.ofReal (heatKernel (2 * r) x) *
            ENNReal.ofReal (heatKernel (2 * (a + b - u)) y)) := by
  let H : ℝ → ℝ → Plane → ℝ≥0∞ := fun r u z =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
      (ENNReal.ofReal (heatKernel (2 * r) x) *
        (ENNReal.ofReal (heatKernel (2 * (a - u)) z) *
          ENNReal.ofReal (heatKernel (2 * b) (y - z))))
  have hH : Measurable (fun q : (ℝ × ℝ) × Plane => H q.1.1 q.1.2 q.2) := by
    dsimp [H]
    have hmCoeff : Measurable (fun q : (ℝ × ℝ) × Plane =>
        4 * Real.pi * scalarDensity θ (q.1.2 - q.1.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun q : (ℝ × ℝ) × Plane => (θ, q.1.2 - q.1.1))))
    have hmStart : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * q.1.1) x) := by
      unfold heatKernel
      fun_prop
    have hmTail : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * (a - q.1.2)) q.2) := by
      unfold heatKernel
      fun_prop
    have hmFree : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * b) (y - q.2)) :=
      (measurable_heatKernel (2 * b)).comp (measurable_const.sub measurable_snd)
    exact hmCoeff.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul
      (hmTail.ennreal_ofReal.mul hmFree.ennreal_ofReal))
  have htimeSwap :=
    Critical2DKPZ.DeltaBose.lintegral_timeTriangle_configuration_swap
      (μ := volume) a hH
  calc
    (∫⁻ z : Plane,
        twoParticleGapCollisionKernel θ a x z * twoParticleGapFreeKernel b z y) =
        ∫⁻ z : Plane, ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, H r u z := by
          apply lintegral_congr_ae
          filter_upwards [] with z
          let B : ℝ → ℝ → ℝ≥0∞ := fun r u =>
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
              (ENNReal.ofReal (heatKernel (2 * r) x) *
                ENNReal.ofReal (heatKernel (2 * (a - u)) z))
          have hB : Measurable (Function.uncurry B) := by
            dsimp [B]
            have hmCoeff : Measurable (fun p : ℝ × ℝ =>
                4 * Real.pi * scalarDensity θ (p.2 - p.1)) := by
              exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
                Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1))))
            have hmStart : Measurable (fun p : ℝ × ℝ => heatKernel (2 * p.1) x) := by
              unfold heatKernel
              fun_prop
            have hmTail : Measurable (fun p : ℝ × ℝ =>
                heatKernel (2 * (a - p.2)) z) := by
              unfold heatKernel
              fun_prop
            exact hmCoeff.ennreal_ofReal.mul
              (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
          have hpull := lintegral_const_mul_timeTriangle (h := a) hB
            (ENNReal.ofReal (heatKernel (2 * b) (y - z)))
          change (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, B r u) *
              ENNReal.ofReal (heatKernel (2 * b) (y - z)) =
            ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, H r u z
          calc
            _ = ENNReal.ofReal (heatKernel (2 * b) (y - z)) *
                  ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, B r u := mul_comm _ _
            _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
                  ENNReal.ofReal (heatKernel (2 * b) (y - z)) * B r u := hpull.symm
            _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, H r u z := by
                  apply lintegral_congr_ae
                  filter_upwards [] with r
                  apply lintegral_congr_ae
                  filter_upwards [] with u
                  dsimp [H, B]
                  ac_rfl
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, ∫⁻ z : Plane, H r u z :=
      htimeSwap
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            (ENNReal.ofReal (heatKernel (2 * r) x) *
              ENNReal.ofReal (heatKernel (2 * (a + b - u)) y)) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          let c : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            ENNReal.ofReal (heatKernel (2 * r) x)
          have hTailMeas : Measurable (fun z : Plane =>
              ENNReal.ofReal (heatKernel (2 * (a - u)) z) *
                ENNReal.ofReal (heatKernel (2 * b) (y - z))) := by
            exact ((measurable_heatKernel (2 * (a - u))).ennreal_ofReal).mul
              (((measurable_heatKernel (2 * b)).comp
                (measurable_const.sub measurable_id)).ennreal_ofReal)
          have hconv : (∫⁻ z : Plane,
              ENNReal.ofReal (heatKernel (2 * (a - u)) z) *
                ENNReal.ofReal (heatKernel (2 * b) (y - z))) =
              ENNReal.ofReal (heatKernel (2 * (a + b - u)) y) := by
            simpa only [show 2 * (a - u) + 2 * b = 2 * (a + b - u) by ring,
              sub_zero] using
                lintegral_heatKernel_initialProduct
                  (mul_pos (show 0 < (2 : ℝ) by norm_num) (sub_pos.mpr hu.2))
                  (mul_pos (show 0 < (2 : ℝ) by norm_num) hb) (0 : Plane) y
          calc
            (∫⁻ z : Plane, H r u z) = ∫⁻ z : Plane, c *
                (ENNReal.ofReal (heatKernel (2 * (a - u)) z) *
                  ENNReal.ofReal (heatKernel (2 * b) (y - z))) := by
                    apply lintegral_congr
                    intro z
                    dsimp [H, c]
                    ac_rfl
            _ = c * ∫⁻ z : Plane,
                ENNReal.ofReal (heatKernel (2 * (a - u)) z) *
                  ENNReal.ofReal (heatKernel (2 * b) (y - z)) :=
                    lintegral_const_mul c hTailMeas
            _ = ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
                  (ENNReal.ofReal (heatKernel (2 * r) x) *
                    ENNReal.ofReal (heatKernel (2 * (a + b - u)) y)) := by
                    rw [hconv]
                    dsimp [c]
                    ac_rfl

/-- A free strand before a collision gives the part of the longer collision
triangle completed entirely after the cut. -/
theorem twoParticleGapFree_collision_piece {a b θ : ℝ} (ha : 0 < a)
    (x y : Plane) :
    (∫⁻ z : Plane,
      twoParticleGapFreeKernel a x z * twoParticleGapCollisionKernel θ b z y) =
      ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b,
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
          (ENNReal.ofReal (heatKernel (2 * (a + r)) x) *
            ENNReal.ofReal (heatKernel (2 * (b - u)) y)) := by
  let H : ℝ → ℝ → Plane → ℝ≥0∞ := fun r u z =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
      (ENNReal.ofReal (heatKernel (2 * (b - u)) y) *
        (ENNReal.ofReal (heatKernel (2 * a) (z - x)) *
          ENNReal.ofReal (heatKernel (2 * r) z)))
  have hH : Measurable (fun q : (ℝ × ℝ) × Plane => H q.1.1 q.1.2 q.2) := by
    dsimp [H]
    have hmCoeff : Measurable (fun q : (ℝ × ℝ) × Plane =>
        4 * Real.pi * scalarDensity θ (q.1.2 - q.1.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun q : (ℝ × ℝ) × Plane => (θ, q.1.2 - q.1.1))))
    have hmTail : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * (b - q.1.2)) y) := by
      unfold heatKernel
      fun_prop
    have hmFree : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * a) (q.2 - x)) :=
      (measurable_heatKernel (2 * a)).comp (measurable_snd.sub_const x)
    have hmStart : Measurable (fun q : (ℝ × ℝ) × Plane =>
        heatKernel (2 * q.1.1) q.2) := by
      unfold heatKernel
      fun_prop
    exact hmCoeff.ennreal_ofReal.mul (hmTail.ennreal_ofReal.mul
      (hmFree.ennreal_ofReal.mul hmStart.ennreal_ofReal))
  have htimeSwap :=
    Critical2DKPZ.DeltaBose.lintegral_timeTriangle_configuration_swap
      (μ := volume) b hH
  calc
    (∫⁻ z : Plane,
        twoParticleGapFreeKernel a x z * twoParticleGapCollisionKernel θ b z y) =
        ∫⁻ z : Plane, ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, H r u z := by
          apply lintegral_congr_ae
          filter_upwards [] with z
          let B : ℝ → ℝ → ℝ≥0∞ := fun r u =>
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
              (ENNReal.ofReal (heatKernel (2 * r) z) *
                ENNReal.ofReal (heatKernel (2 * (b - u)) y))
          have hB : Measurable (Function.uncurry B) := by
            dsimp [B]
            have hmCoeff : Measurable (fun p : ℝ × ℝ =>
                4 * Real.pi * scalarDensity θ (p.2 - p.1)) := by
              exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
                Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1))))
            have hmTail : Measurable (fun p : ℝ × ℝ =>
                heatKernel (2 * (b - p.2)) y) := by
              unfold heatKernel
              fun_prop
            have hmStart : Measurable (fun p : ℝ × ℝ => heatKernel (2 * p.1) z) := by
              unfold heatKernel
              fun_prop
            exact hmCoeff.ennreal_ofReal.mul
              (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
          have hpull := lintegral_const_mul_timeTriangle (h := b) hB
            (ENNReal.ofReal (heatKernel (2 * a) (z - x)))
          dsimp [twoParticleGapFreeKernel, twoParticleGapCollisionKernel]
          change ENNReal.ofReal (heatKernel (2 * a) (z - x)) *
              ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, B r u =
            ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, H r u z
          calc
            _ = ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b,
                  ENNReal.ofReal (heatKernel (2 * a) (z - x)) * B r u :=
              hpull.symm
            _ = ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, H r u z := by
                  apply lintegral_congr_ae
                  filter_upwards [] with r
                  apply lintegral_congr_ae
                  filter_upwards [] with u
                  dsimp [H, B]
                  ac_rfl
    _ = ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, ∫⁻ z : Plane, H r u z :=
      htimeSwap
    _ = ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            (ENNReal.ofReal (heatKernel (2 * (a + r)) x) *
              ENNReal.ofReal (heatKernel (2 * (b - u)) y)) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          let c : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            ENNReal.ofReal (heatKernel (2 * (b - u)) y)
          have hPairMeas : Measurable (fun z : Plane =>
              ENNReal.ofReal (heatKernel (2 * a) (z - x)) *
                ENNReal.ofReal (heatKernel (2 * r) z)) := by
            have hmStart : Measurable (fun z : Plane => heatKernel (2 * r) z) := by
              unfold heatKernel
              fun_prop
            exact (((measurable_heatKernel (2 * a)).comp
              (measurable_id.sub_const x)).ennreal_ofReal).mul
                hmStart.ennreal_ofReal
          have hconv : (∫⁻ z : Plane,
              ENNReal.ofReal (heatKernel (2 * a) (z - x)) *
                ENNReal.ofReal (heatKernel (2 * r) z)) =
              ENNReal.ofReal (heatKernel (2 * (a + r)) x) := by
            have hconv' := lintegral_heatKernel_initialProduct
              (mul_pos (show 0 < (2 : ℝ) by norm_num) ha)
              (mul_pos (show 0 < (2 : ℝ) by norm_num) hr.1) x (0 : Plane)
            have heven : ∀ z : Plane, heatKernel (2 * r) (0 - z) = heatKernel (2 * r) z := by
              intro z
              rw [show 0 - z = -z by abel, heatKernel_neg]
            have htime : 2 * a + 2 * r = 2 * (a + r) := by ring
            have hneg : 0 - x = -x := by abel
            simpa only [heven, htime, hneg, heatKernel_neg] using hconv'
          calc
            (∫⁻ z : Plane, H r u z) = ∫⁻ z : Plane, c *
                (ENNReal.ofReal (heatKernel (2 * a) (z - x)) *
                  ENNReal.ofReal (heatKernel (2 * r) z)) := by
                    apply lintegral_congr
                    intro z
                    dsimp [H, c]
                    ac_rfl
            _ = c * ∫⁻ z : Plane,
                ENNReal.ofReal (heatKernel (2 * a) (z - x)) *
                  ENNReal.ofReal (heatKernel (2 * r) z) :=
                    lintegral_const_mul c hPairMeas
            _ = ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
                  (ENNReal.ofReal (heatKernel (2 * (a + r)) x) *
                    ENNReal.ofReal (heatKernel (2 * (b - u)) y)) := by
                    rw [hconv]
                    dsimp [c]
                    ac_rfl

end Critical2DKPZ.SHF.Flow

end
