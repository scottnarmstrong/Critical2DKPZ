/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleGapComposition
import Mathlib.Tactic

/-! # The collision contribution crossing a time cut -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Splitting a positive Lebesgue integral at an interior point. The omitted
singleton has zero Lebesgue measure. -/
theorem lintegral_Ioo_split {l m r : ℝ} (hlm : l < m) (hmr : m < r)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioo l r, F x) =
      (∫⁻ x in Ioo l m, F x) + (∫⁻ x in Ioo m r, F x) := by
  have hset : Ioo l r = Ioo l m ∪ ({m} ∪ Ioo m r) := by
    ext x
    simp only [mem_Ioo, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hlx, hxr⟩
      by_cases hxm : x < m
      · exact Or.inl ⟨hlx, hxm⟩
      · right
        by_cases hxeq : x = m
        · exact Or.inl hxeq
        · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt hxm) (Ne.symm hxeq), hxr⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, lt_trans hx.2 hmr⟩
      · rcases hx with hxm | hx
        · subst x
          exact ⟨hlm, hmr⟩
        · exact ⟨lt_trans hlm hx.1, hx.2⟩
  have hdisj₁ : Disjoint (Ioo l m) ({m} ∪ Ioo m r) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx₁ hx₂
    rcases hx₂ with hxm | hx₂
    · simp only [mem_singleton_iff] at hxm
      subst x
      exact (lt_irrefl m) hx₁.2
    · exact (not_lt_of_ge hx₂.1.le) hx₁.2
  have hdisj₂ : Disjoint ({m} : Set ℝ) (Ioo m r) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxm hx
    simp only [mem_singleton_iff] at hxm
    subst x
    exact (lt_irrefl m) hx.1
  calc
    (∫⁻ x in Ioo l r, F x) = ∫⁻ x in Ioo l m ∪ ({m} ∪ Ioo m r), F x := by
      rw [hset]
    _ = (∫⁻ x in Ioo l m, F x) + (∫⁻ x in ({m} ∪ Ioo m r), F x) :=
      lintegral_union (by measurability) hdisj₁
    _ = (∫⁻ x in Ioo l m, F x) +
          ((∫⁻ x in {m}, F x) + (∫⁻ x in Ioo m r, F x)) := by
            rw [lintegral_union measurableSet_Ioo hdisj₂]
    _ = _ := by simp

/-- Translation preserves the integral on a translated open interval. -/
theorem lintegral_Ioo_translate (c l r : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioo (c + l) (c + r), F x) =
      ∫⁻ x in Ioo l r, F (c + x) := by
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight c
  have hmp : MeasurePreserving (fun x : ℝ => x + c) volume volume :=
    measurePreserving_add_right volume c
  have h := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding F
    (Ioo (c + l) (c + r))
  have hpre : (fun x : ℝ => x + c) ⁻¹' Ioo (c + l) (c + r) = Ioo l r := by
    ext x
    simp only [Set.mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  calc
    (∫⁻ x in Ioo (c + l) (c + r), F x) =
        ∫⁻ x in Ioo l r, F (x + c) := by simpa only [hpre] using h.symm
    _ = ∫⁻ x in Ioo l r, F (c + x) := by
          apply lintegral_congr_ae
          filter_upwards [] with x
          congr 1
          ring

/-- The two collision intervals compose to the scalar cut kernel, including
the `4π` normalization of the relative heat strand. -/
theorem twoParticleGapCollisionKernel_mul_collision_scalarCut {a b θ : ℝ}
    (x y : Plane) :
    (∫⁻ z : Plane,
      twoParticleGapCollisionKernel θ a x z * twoParticleGapCollisionKernel θ b z y) =
      ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
        ENNReal.ofReal (4 * Real.pi) *
          (ENNReal.ofReal (heatKernel (2 * r) x) *
            (ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
              scalarCutKernelENN θ (a - r) v)) := by
  let G : ℝ → ℝ → ℝ → ℝ → ℝ≥0∞ := fun r u s v =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
      (ENNReal.ofReal (heatKernel (2 * r) x) *
        (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (v - s)) *
          (ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
            ENNReal.ofReal ((4 * Real.pi * (a - u + s))⁻¹))))
  have hTriangle (r u : ℝ) :
      Measurable (Function.uncurry (fun s v => G r u s v)) := by
    dsimp [Function.uncurry, G]
    have hmJ₂ : Measurable (fun p : ℝ × ℝ =>
        4 * Real.pi * scalarDensity θ (p.2 - p.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1))))
    have hmTail : Measurable (fun p : ℝ × ℝ =>
        heatKernel (2 * (b - p.2)) y) := by
      unfold heatKernel
      fun_prop
    have hmBridge : Measurable (fun p : ℝ × ℝ =>
        (4 * Real.pi * (a - u + p.1))⁻¹) := by fun_prop
    have hmRest : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ (p.2 - p.1)) *
          (ENNReal.ofReal (heatKernel (2 * (b - p.2)) y) *
            ENNReal.ofReal ((4 * Real.pi * (a - u + p.1))⁻¹))) := by
      exact hmJ₂.ennreal_ofReal.mul (hmTail.ennreal_ofReal.mul hmBridge.ennreal_ofReal)
    exact (measurable_const.ennreal_ofReal).mul
      ((measurable_const.ennreal_ofReal).mul hmRest)
  let A : ℝ → ℝ → ℝ → ℝ≥0∞ := fun r u v =>
    ∫⁻ s in Ioo (0 : ℝ) v, G r u s v
  have hA (r : ℝ) : Measurable (Function.uncurry (fun u v => A r u v)) := by
    apply measurable_lintegral_Ioo measurable_const measurable_snd
    have hF : Measurable
        (Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => G r p.1 s p.2)) := by
      dsimp [Function.uncurry, G]
      have hmJ₁ : Measurable (fun q : ((ℝ × ℝ) × ℝ) =>
          4 * Real.pi * scalarDensity θ (q.1.1 - r)) := by
        exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
          Measurable (fun q : ((ℝ × ℝ) × ℝ) => (θ, q.1.1 - r))))
      have hmStart : Measurable (fun q : ((ℝ × ℝ) × ℝ) => heatKernel (2 * r) x) :=
        measurable_const
      have hmJ₂ : Measurable (fun q : ((ℝ × ℝ) × ℝ) =>
          4 * Real.pi * scalarDensity θ (q.1.2 - q.2)) := by
        exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
          Measurable (fun q : ((ℝ × ℝ) × ℝ) => (θ, q.1.2 - q.2))))
      have hmTail : Measurable (fun q : ((ℝ × ℝ) × ℝ) =>
          heatKernel (2 * (b - q.1.2)) y) := by
        unfold heatKernel
        fun_prop
      have hmBridge : Measurable (fun q : ((ℝ × ℝ) × ℝ) =>
          (4 * Real.pi * (a - q.1.1 + q.2))⁻¹) := by fun_prop
      have hmRest : Measurable (fun q : ((ℝ × ℝ) × ℝ) =>
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (q.1.2 - q.2)) *
            (ENNReal.ofReal (heatKernel (2 * (b - q.1.2)) y) *
              ENNReal.ofReal ((4 * Real.pi * (a - q.1.1 + q.2))⁻¹))) := by
        exact hmJ₂.ennreal_ofReal.mul (hmTail.ennreal_ofReal.mul hmBridge.ennreal_ofReal)
      exact hmJ₁.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmRest)
    exact hF
  have hInner (r v : ℝ) :
      (∫⁻ α in Ioo (0 : ℝ) (a - r), ∫⁻ s in Ioo (0 : ℝ) v,
        G r (r + α) s v) =
      ENNReal.ofReal (4 * Real.pi) *
        (ENNReal.ofReal (heatKernel (2 * r) x) *
          (ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
            scalarCutKernelENN θ (a - r) v)) := by
    let c : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi) *
      (ENNReal.ofReal (heatKernel (2 * r) x) *
        ENNReal.ofReal (heatKernel (2 * (b - v)) y))
    have hc : c ≠ ∞ := by
      dsimp [c]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    have hPoint (α s : ℝ) (hα : α ∈ Ioo (0 : ℝ) (a - r))
        (hs : s ∈ Ioo (0 : ℝ) v) :
        G r (r + α) s v = c *
          (ENNReal.ofReal (scalarDensity θ α) *
            (ENNReal.ofReal (scalarDensity θ (v - s)) *
              ENNReal.ofReal ((a - r - α + s)⁻¹))) := by
      have hbridge : 0 < a - r - α + s := by
        rcases hα with ⟨_, hα⟩
        rcases hs with ⟨hs, _⟩
        linarith
      have hscale : (4 * Real.pi : ℝ) *
          ((4 * Real.pi * (a - r - α + s))⁻¹) =
            (a - r - α + s)⁻¹ := by
        have hpi : (4 * Real.pi : ℝ) ≠ 0 := by positivity
        field_simp [hpi, ne_of_gt hbridge]
      have hscaleENN : ENNReal.ofReal (4 * Real.pi) *
          ENNReal.ofReal ((4 * Real.pi * (a - r - α + s))⁻¹) =
            ENNReal.ofReal ((a - r - α + s)⁻¹) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi : ℝ)), hscale]
      calc
        G r (r + α) s v =
            ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (heatKernel (2 * r) x) *
              ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
                ENNReal.ofReal (scalarDensity θ α) *
                  ENNReal.ofReal (scalarDensity θ (v - s)) *
                    (ENNReal.ofReal (4 * Real.pi) *
                      ENNReal.ofReal ((4 * Real.pi * (a - r - α + s))⁻¹)) := by
                dsimp [G]
                rw [show r + α - r = α by ring,
                  show a - (r + α) + s = a - r - α + s by ring,
                  ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi : ℝ)),
                  ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi : ℝ))]
                ac_rfl
        _ = ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (heatKernel (2 * r) x) *
              ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
                ENNReal.ofReal (scalarDensity θ α) *
                  ENNReal.ofReal (scalarDensity θ (v - s)) *
                    ENNReal.ofReal ((a - r - α + s)⁻¹) := by
                rw [hscaleENN]
        _ = c *
            (ENNReal.ofReal (scalarDensity θ α) *
              (ENNReal.ofReal (scalarDensity θ (v - s)) *
                ENNReal.ofReal ((a - r - α + s)⁻¹))) := by
                dsimp [c]
                ac_rfl
    calc
      (∫⁻ α in Ioo (0 : ℝ) (a - r), ∫⁻ s in Ioo (0 : ℝ) v,
          G r (r + α) s v) =
          ∫⁻ α in Ioo (0 : ℝ) (a - r), ∫⁻ s in Ioo (0 : ℝ) v,
            c * (ENNReal.ofReal (scalarDensity θ α) *
              (ENNReal.ofReal (scalarDensity θ (v - s)) *
                ENNReal.ofReal ((a - r - α + s)⁻¹))) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with α hα
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
              exact hPoint α s hα hs
      _ = c * (∫⁻ α in Ioo (0 : ℝ) (a - r), ∫⁻ s in Ioo (0 : ℝ) v,
            ENNReal.ofReal (scalarDensity θ α) *
              (ENNReal.ofReal (scalarDensity θ (v - s)) *
                ENNReal.ofReal ((a - r - α + s)⁻¹))) :=
              (lintegral_const_mul_double c hc).symm
      _ = _ := by
            rw [scalarCutKernelENN]
            dsimp [c]
            ac_rfl
  calc
    (∫⁻ z : Plane,
        twoParticleGapCollisionKernel θ a x z * twoParticleGapCollisionKernel θ b z y) =
        ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
          ∫⁻ s in Ioo (0 : ℝ) b, ∫⁻ v in Ioo s b, G r u s v := by
            simpa only [G] using
              twoParticleGapCollisionKernel_mul_collision_quadIntegral (a := a) (b := b)
                (θ := θ) x y
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a,
          ∫⁻ v in Ioo (0 : ℝ) b, ∫⁻ s in Ioo (0 : ℝ) v, G r u s v := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
            exact lintegral_positiveTriangle_flip (hTriangle r u)
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
          ∫⁻ u in Ioo r a, ∫⁻ s in Ioo (0 : ℝ) v, G r u s v := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            exact lintegral_Ioo_rectangle_swap (hA r)
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
          ∫⁻ α in Ioo (0 : ℝ) (a - r), ∫⁻ s in Ioo (0 : ℝ) v,
            G r (r + α) s v := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
            have hshift := Critical2DKPZ.DeltaBose.lintegral_Ioo_sub_right r a
              (fun α => A r (r + α) v)
            calc
              (∫⁻ u in Ioo r a, A r u v) =
                  ∫⁻ u in Ioo r a, (fun α => A r (r + α) v) (u - r) := by
                    apply lintegral_congr_ae
                    filter_upwards [] with u
                    congr 1
                    ring
              _ = ∫⁻ α in Ioo (0 : ℝ) (a - r), A r (r + α) v := hshift.symm
              _ = ∫⁻ α in Ioo (0 : ℝ) (a - r), ∫⁻ s in Ioo (0 : ℝ) v,
                    G r (r + α) s v := rfl
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
          ENNReal.ofReal (4 * Real.pi) *
            (ENNReal.ofReal (heatKernel (2 * r) x) *
              (ENNReal.ofReal (heatKernel (2 * (b - v)) y) *
                scalarCutKernelENN θ (a - r) v)) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
            exact hInner r v

/-- The collision–collision convolution is the crossing part of one longer
collision interval. -/
theorem twoParticleGapCollisionKernel_mul_collision_eq_crossing {a b θ : ℝ}
    (x y : Plane) :
    (∫⁻ z : Plane,
      twoParticleGapCollisionKernel θ a x z * twoParticleGapCollisionKernel θ b z y) =
      ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ (a - r + v)) *
          (ENNReal.ofReal (heatKernel (2 * r) x) *
            ENNReal.ofReal (heatKernel (2 * (b - v)) y)) := by
  let W : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (4 * Real.pi) *
      (ENNReal.ofReal (heatKernel (2 * p.1) x) *
        ENNReal.ofReal (heatKernel (2 * (b - p.2)) y))
  have hW : Measurable W := by
    dsimp [W]
    have hmX : Measurable (fun p : ℝ × ℝ => heatKernel (2 * p.1) x) := by
      unfold heatKernel
      fun_prop
    have hmY : Measurable (fun p : ℝ × ℝ => heatKernel (2 * (b - p.2)) y) := by
      unfold heatKernel
      fun_prop
    exact measurable_const.ennreal_ofReal.mul
      (hmX.ennreal_ofReal.mul hmY.ennreal_ofReal)
  have hscalar := lintegral_scalarCutKernelENN_reflect_rect
    (θ := θ) (a := a) (b := b) (W := W) hW
  calc
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
          W (r, v) * scalarCutKernelENN θ (a - r) v := by
            simpa only [W, mul_assoc] using
              twoParticleGapCollisionKernel_mul_collision_scalarCut (a := a) (b := b)
                (θ := θ) x y
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
          W (r, v) * ENNReal.ofReal (scalarDensity θ (a - r + v)) := hscalar
    _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (a - r + v)) *
            (ENNReal.ofReal (heatKernel (2 * r) x) *
              ENNReal.ofReal (heatKernel (2 * (b - v)) y)) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
            dsimp [W]
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi : ℝ))]
            ac_rfl

/-- Cutting a long collision interval at an intermediate time gives the two
one-sided pieces and the crossing piece. -/
theorem twoParticleGapCollisionKernel_split {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : Plane) :
    twoParticleGapCollisionKernel θ (a + b) x y =
      (∫⁻ z : Plane,
        twoParticleGapCollisionKernel θ a x z * twoParticleGapFreeKernel b z y) +
      (∫⁻ z : Plane,
        twoParticleGapFreeKernel a x z * twoParticleGapCollisionKernel θ b z y) +
      (∫⁻ z : Plane,
        twoParticleGapCollisionKernel θ a x z * twoParticleGapCollisionKernel θ b z y) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun r u =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
      (ENNReal.ofReal (heatKernel (2 * r) x) *
        ENNReal.ofReal (heatKernel (2 * (a + b - u)) y))
  have hF : Measurable (Function.uncurry F) := by
    dsimp [F]
    have hmJ : Measurable (fun p : ℝ × ℝ =>
        4 * Real.pi * scalarDensity θ (p.2 - p.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1))))
    have hmStart : Measurable (fun p : ℝ × ℝ => heatKernel (2 * p.1) x) := by
      unfold heatKernel
      fun_prop
    have hmTail : Measurable (fun p : ℝ × ℝ =>
        heatKernel (2 * (a + b - p.2)) y) := by
      unfold heatKernel
      fun_prop
    exact hmJ.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
  have hpreMeas : Measurable (fun r : ℝ => ∫⁻ u in Ioo r a, F r u) :=
    measurable_lintegral_Ioo measurable_id measurable_const hF
  have hcrossMeas : Measurable (fun r : ℝ =>
      ∫⁻ u in Ioo a (a + b), F r u) :=
    measurable_lintegral_Ioo measurable_const measurable_const hF
  have hfirstSplit :
      (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r (a + b), F r u) =
        (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, F r u) +
          (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo a (a + b), F r u) := by
    calc
      _ = ∫⁻ r in Ioo (0 : ℝ) a,
            ((∫⁻ u in Ioo r a, F r u) + (∫⁻ u in Ioo a (a + b), F r u)) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
              exact lintegral_Ioo_split hr.2 (by linarith [hb]) (F r)
      _ = _ := lintegral_add_aux hpreMeas hcrossMeas
  have hpostShift :
      (∫⁻ r in Ioo a (a + b), ∫⁻ u in Ioo r (a + b), F r u) =
        ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, F (a + r) (a + u) := by
    let H : ℝ → ℝ≥0∞ := fun r => ∫⁻ u in Ioo r (a + b), F r u
    calc
      (∫⁻ r in Ioo a (a + b), H r) =
          ∫⁻ r in Ioo (0 : ℝ) b, H (a + r) := by
            simpa only [add_zero] using
              (lintegral_Ioo_translate a 0 b H)
      _ = ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, F (a + r) (a + u) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            exact lintegral_Ioo_translate a r b (F (a + r))
  have hpostFormula :
      (∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b, F (a + r) (a + u)) =
        ∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            (ENNReal.ofReal (heatKernel (2 * (a + r)) x) *
              ENNReal.ofReal (heatKernel (2 * (b - u)) y)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    dsimp [F]
    rw [show a + u - (a + r) = u - r by ring,
      show a + b - (a + u) = b - u by ring]
  have hcrossShift :
      (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo a (a + b), F r u) =
        ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (a - r + v)) *
            (ENNReal.ofReal (heatKernel (2 * r) x) *
              ENNReal.ofReal (heatKernel (2 * (b - v)) y)) := by
    calc
      _ = ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b, F r (a + v) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            simpa only [add_zero] using lintegral_Ioo_translate a 0 b (F r)
      _ = _ := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
            dsimp [F]
            rw [show a + v - r = a - r + v by ring,
              show a + b - (a + v) = b - v by ring]
  have hpreConv := twoParticleGapCollision_free_piece (a := a) (b := b)
    (θ := θ) hb x y
  have hpostConv := twoParticleGapFree_collision_piece (a := a) (b := b)
    (θ := θ) ha x y
  have hcrossConv := twoParticleGapCollisionKernel_mul_collision_eq_crossing
    (a := a) (b := b) (θ := θ) x y
  calc
    twoParticleGapCollisionKernel θ (a + b) x y =
        (∫⁻ r in Ioo (0 : ℝ) (a + b), ∫⁻ u in Ioo r (a + b), F r u) := rfl
    _ = (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, F r u) +
          (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo a (a + b), F r u) +
          (∫⁻ r in Ioo a (a + b), ∫⁻ u in Ioo r (a + b), F r u) := by
            rw [lintegral_Ioo_split ha (by linarith [hb])
              (fun r => ∫⁻ u in Ioo r (a + b), F r u), hfirstSplit]
    _ = (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ u in Ioo r a, F r u) +
          (∫⁻ r in Ioo (0 : ℝ) b, ∫⁻ u in Ioo r b,
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
              (ENNReal.ofReal (heatKernel (2 * (a + r)) x) *
                ENNReal.ofReal (heatKernel (2 * (b - u)) y))) +
          (∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ v in Ioo (0 : ℝ) b,
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ (a - r + v)) *
              (ENNReal.ofReal (heatKernel (2 * r) x) *
                ENNReal.ofReal (heatKernel (2 * (b - v)) y))) := by
            rw [hpostShift, hpostFormula, hcrossShift]
            ac_rfl
    _ = _ := by
          rw [← hpreConv, ← hpostConv, ← hcrossConv]

/-- Joint measurability of a gap collision kernel in its terminal point. -/
theorem measurable_twoParticleGapCollisionKernel (θ h : ℝ) (x : Plane) :
    Measurable (twoParticleGapCollisionKernel θ h x) := by
  let F : ℝ → ℝ → Plane → ℝ≥0∞ := fun r u z =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
      (ENNReal.ofReal (heatKernel (2 * r) x) *
        ENNReal.ofReal (heatKernel (2 * (h - u)) z))
  have hF : Measurable
      (Function.uncurry (fun (p : ℝ × Plane) (u : ℝ) => F p.1 u p.2)) := by
    dsimp [Function.uncurry, F]
    have hmJ : Measurable (fun q : (ℝ × Plane) × ℝ =>
        4 * Real.pi * scalarDensity θ (q.2 - q.1.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun q : (ℝ × Plane) × ℝ => (θ, q.2 - q.1.1))))
    have hmStart : Measurable (fun q : (ℝ × Plane) × ℝ => heatKernel (2 * q.1.1) x) := by
      unfold heatKernel
      fun_prop
    have hmTail : Measurable (fun q : (ℝ × Plane) × ℝ =>
        heatKernel (2 * (h - q.2)) q.1.2) := by
      unfold heatKernel
      fun_prop
    exact hmJ.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
  have hInner : Measurable (fun p : ℝ × Plane =>
      ∫⁻ u in Ioo p.1 h, F p.1 u p.2) :=
    measurable_lintegral_Ioo measurable_fst measurable_const hF
  have hOuter : Measurable (Function.uncurry (fun z r =>
      ∫⁻ u in Ioo r h, F r u z)) := by
    exact hInner.comp measurable_swap
  change Measurable (fun z : Plane => ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h, F r u z)
  exact measurable_lintegral_Ioo measurable_const measurable_const hOuter

/-- The relative-coordinate two-particle kernel satisfies its semigroup law. -/
theorem twoParticleGapKernel_semigroup {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : Plane) :
    (∫⁻ z : Plane,
      twoParticleGapKernel θ a x z * twoParticleGapKernel θ b z y) =
      twoParticleGapKernel θ (a + b) x y := by
  let P : ℝ → Plane → Plane → ℝ≥0∞ := fun t u v => twoParticleGapFreeKernel t u v
  let C : ℝ → Plane → Plane → ℝ≥0∞ := fun t u v => twoParticleGapCollisionKernel θ t u v
  have hP₁ : Measurable (fun z : Plane => P a x z) := by
    dsimp [P, twoParticleGapFreeKernel]
    exact ((measurable_heatKernel (2 * a)).comp (measurable_id.sub_const x)).ennreal_ofReal
  have hP₂ : Measurable (fun z : Plane => P b z y) := by
    dsimp [P, twoParticleGapFreeKernel]
    exact ((measurable_heatKernel (2 * b)).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  have hC₁ : Measurable (fun z : Plane => C a x z) := by
    exact measurable_twoParticleGapCollisionKernel θ a x
  have hC₂ : Measurable (fun z : Plane => C b z y) := by
    dsimp [C, twoParticleGapCollisionKernel]
    have hG : Measurable (fun q : ((Plane × ℝ) × ℝ) =>
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ (q.2 - q.1.2)) *
          (ENNReal.ofReal (heatKernel (2 * q.1.2) q.1.1) *
            ENNReal.ofReal (heatKernel (2 * (b - q.2)) y))) := by
      have hmJ : Measurable (fun q : ((Plane × ℝ) × ℝ) =>
          4 * Real.pi * scalarDensity θ (q.2 - q.1.2)) := by
        exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
          Measurable (fun q : ((Plane × ℝ) × ℝ) => (θ, q.2 - q.1.2))))
      have hmStart : Measurable (fun q : ((Plane × ℝ) × ℝ) =>
          heatKernel (2 * q.1.2) q.1.1) := by
        unfold heatKernel
        fun_prop
      have hmTail : Measurable (fun q : ((Plane × ℝ) × ℝ) =>
          heatKernel (2 * (b - q.2)) y) := by
        unfold heatKernel
        fun_prop
      exact hmJ.ennreal_ofReal.mul (hmStart.ennreal_ofReal.mul hmTail.ennreal_ofReal)
    have hInner : Measurable (fun p : Plane × ℝ =>
        ∫⁻ u in Ioo p.2 b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - p.2)) *
            (ENNReal.ofReal (heatKernel (2 * p.2) p.1) *
              ENNReal.ofReal (heatKernel (2 * (b - u)) y))) := by
      apply measurable_lintegral_Ioo measurable_snd measurable_const
      exact hG
    have hOuter : Measurable (Function.uncurry (fun z r =>
        ∫⁻ u in Ioo r b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            (ENNReal.ofReal (heatKernel (2 * r) z) *
              ENNReal.ofReal (heatKernel (2 * (b - u)) y)))) := by
      change Measurable (fun p : Plane × ℝ =>
        ∫⁻ u in Ioo p.2 b,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - p.2)) *
            (ENNReal.ofReal (heatKernel (2 * p.2) p.1) *
              ENNReal.ofReal (heatKernel (2 * (b - u)) y)))
      exact hInner
    exact measurable_lintegral_Ioo measurable_const measurable_const hOuter
  have hPP : Measurable (fun z : Plane => P a x z * P b z y) := hP₁.mul hP₂
  have hPC : Measurable (fun z : Plane => P a x z * C b z y) := hP₁.mul hC₂
  have hCP : Measurable (fun z : Plane => C a x z * P b z y) := hC₁.mul hP₂
  have hCC : Measurable (fun z : Plane => C a x z * C b z y) := hC₁.mul hC₂
  have hRemainder : Measurable (fun z : Plane =>
      P a x z * C b z y + (C a x z * P b z y + C a x z * C b z y)) :=
    hPC.add (hCP.add hCC)
  have hExpand (z : Plane) :
      twoParticleGapKernel θ a x z * twoParticleGapKernel θ b z y =
        P a x z * P b z y +
          (P a x z * C b z y + (C a x z * P b z y + C a x z * C b z y)) := by
    simp [twoParticleGapKernel, P, C, twoParticleGapFreeKernel, twoParticleGapCollisionKernel]
    ring
  calc
    _ = ∫⁻ z : Plane, P a x z * P b z y +
          (P a x z * C b z y + (C a x z * P b z y + C a x z * C b z y)) := by
            apply lintegral_congr_ae
            filter_upwards [] with z
            exact hExpand z
    _ = (∫⁻ z : Plane, P a x z * P b z y) +
          (∫⁻ z : Plane, P a x z * C b z y) +
            ((∫⁻ z : Plane, C a x z * P b z y) +
              (∫⁻ z : Plane, C a x z * C b z y)) := by
            calc
              _ = (∫⁻ z : Plane, P a x z * P b z y) +
                    (∫⁻ z : Plane,
                      P a x z * C b z y + (C a x z * P b z y + C a x z * C b z y)) :=
                      lintegral_add_aux hPP hRemainder
              _ = (∫⁻ z : Plane, P a x z * P b z y) +
                    ((∫⁻ z : Plane, P a x z * C b z y) +
                      ∫⁻ z : Plane, C a x z * P b z y + C a x z * C b z y) := by
                      congr 1
                      exact lintegral_add_aux hPC (hCP.add hCC)
              _ = _ := by
                      calc
                        _ = (∫⁻ z : Plane, P a x z * P b z y) +
                            ((∫⁻ z : Plane, P a x z * C b z y) +
                              ((∫⁻ z : Plane, C a x z * P b z y) +
                                ∫⁻ z : Plane, C a x z * C b z y)) :=
                              congrArg (fun q : ℝ≥0∞ =>
                        (∫⁻ z : Plane, P a x z * P b z y) +
                          ((∫⁻ z : Plane, P a x z * C b z y) + q))
                                (lintegral_add_aux hCP hCC)
                        _ = _ := by ac_rfl
    _ = twoParticleGapKernel θ (a + b) x y := by
          change ((∫⁻ z : Plane, P a x z * P b z y) +
                (∫⁻ z : Plane, P a x z * C b z y)) +
                ((∫⁻ z : Plane, C a x z * P b z y) +
                  ∫⁻ z : Plane, C a x z * C b z y) =
              twoParticleGapFreeKernel (a + b) x y +
                twoParticleGapCollisionKernel θ (a + b) x y
          rw [twoParticleGapFreeKernel_semigroup ha hb x y,
            twoParticleGapCollisionKernel_split ha hb x y]
          ac_rfl

end Critical2DKPZ.SHF.Flow

end
