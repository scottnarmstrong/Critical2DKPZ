/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.DoubleLaplaceUniqueness
public import Critical2DKPZ.Analysis.DoubleLaplaceUniquenessOnBoxes
public import Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Prod

/-! # The scalar cut kernel for the two-particle semigroup -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The Euclidean plane is identified with its two Lebesgue coordinates. -/
noncomputable def planeCoordEquiv : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

/-- The coordinate equivalence preserves Lebesgue measure. -/
theorem measurePreserving_planeCoordEquiv :
    MeasurePreserving planeCoordEquiv volume (volume.prod volume) := by
  let h1 : MeasurePreserving ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm)
      volume (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin 2)
  let h2 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
      (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) (volume.prod volume) :=
    volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  change MeasurePreserving
    (fun p : Plane => (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm p)) volume (volume.prod volume)
  exact h2.comp h1

/-- Integrals on the positive quadrant equal the corresponding product Lebesgue integrals in two coordinates. -/
theorem lintegral_plane_positiveQuadrant {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ p in Critical2DKPZ.Analysis.positiveQuadrant,
      F (planeCoordEquiv p)) =
        ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), F (s, t) := by
  let Q : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  have hpre : planeCoordEquiv ⁻¹' Q = Critical2DKPZ.Analysis.positiveQuadrant := by
    ext p
    simp [Q, planeCoordEquiv, Critical2DKPZ.Analysis.positiveQuadrant,
      MeasurableEquiv.trans_apply]
  calc
    (∫⁻ p in Critical2DKPZ.Analysis.positiveQuadrant,
        F (planeCoordEquiv p)) =
      ∫⁻ p in planeCoordEquiv ⁻¹' Q, F (planeCoordEquiv p) := by rw [hpre]
    _ = ∫⁻ q in Q, F q ∂(volume.prod volume) := by
      exact measurePreserving_planeCoordEquiv.setLIntegral_comp_preimage
        (s := Q) (by measurability) hF
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), F (s, t) := by
      exact setLIntegral_prod F (hF.aemeasurable.restrict)

/-- The positive scalar integral appearing when a collision interval straddles a time cut. -/
noncomputable def scalarCutKernelENN (θ s v : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioo (0 : ℝ) s, ∫⁻ b in Ioo (0 : ℝ) v,
    ENNReal.ofReal (scalarDensity θ a) *
      ENNReal.ofReal (scalarDensity θ (v - b)) *
      ENNReal.ofReal ((s - a + b)⁻¹)

/-- The scalar cut kernel is jointly measurable in its endpoint times. -/
theorem measurable_scalarCutKernelENN (θ : ℝ) :
    Measurable (fun p : ℝ × ℝ => scalarCutKernelENN θ p.1 p.2) := by
  unfold scalarCutKernelENN
  apply measurable_lintegral_Ioo measurable_const measurable_fst
  apply measurable_lintegral_Ioo measurable_const (measurable_snd.comp measurable_fst)
  have hja : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ => scalarDensity θ q.1.2) := by
    exact measurable_scalarDensity.comp
      (measurable_const.prodMk (measurable_snd.comp measurable_fst))
  have hjb : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      scalarDensity θ (q.1.1.2 - q.2)) := by
    have harg : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
        (θ, q.1.1.2 - q.2)) := by fun_prop
    simpa only [Function.comp_def] using measurable_scalarDensity.comp harg
  have hden : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      (q.1.1.1 - q.1.2 + q.2)⁻¹) := by fun_prop
  exact (hja.ennreal_ofReal.mul hjb.ennreal_ofReal).mul hden.ennreal_ofReal

/-- Translation of a positive half-line integral to elapsed time. -/
theorem lintegral_Ioi_sub_right (r : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi r, F (t - r)) = ∫⁻ x in Ioi (0 : ℝ), F x := by
  have hm : MeasurePreserving (fun t : ℝ => t - r) := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-r)
  have h := hm.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.subRight r).measurableEmbedding F (Ioi (0 : ℝ))
  have hpre : (fun t : ℝ => t - r) ⁻¹' Ioi (0 : ℝ) = Ioi r := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro ht <;> linarith
  simpa only [hpre] using h

/-- Tonelli changes the ordered variables `(total time, first duration)` into
two independent positive durations. -/
theorem lintegral_positiveTriangle_sum {H : ℝ × ℝ → ℝ≥0∞}
    (hH : Measurable H) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) t, H (a, t - a)) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ), H (a, x) := by
  let G : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.2 ∧ p.2 < p.1 then H (p.2, p.1 - p.2) else 0
  have hG : Measurable G := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst))
      (hH.comp (measurable_snd.prodMk (measurable_fst.sub measurable_snd)))
      measurable_const
  have hleft :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) t, H (a, t - a)) =
        ∫⁻ t, ∫⁻ a, G (t, a) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr_ae
    filter_upwards [] with t
    by_cases ht : 0 < t
    · simp only [Set.indicator_of_mem (mem_Ioi.mpr ht)]
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr_ae
      filter_upwards [] with a
      by_cases ha : a ∈ Ioo (0 : ℝ) t
      · have ha' : 0 < a ∧ a < t := by simpa only [mem_Ioo] using ha
        simp [G, ha']
      · have ha' : ¬ (0 < a ∧ a < t) := by simpa only [mem_Ioo] using ha
        simp [G, ha']
    · rw [indicator_of_notMem (notMem_Ioi.mpr (le_of_not_gt ht))]
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with a
      have ha : ¬ (0 < a ∧ a < t) := by
        intro h
        exact (not_lt_of_ge (le_of_not_gt ht)) (h.1.trans h.2)
      simp [G, ha]
  calc
    _ = ∫⁻ t, ∫⁻ a, G (t, a) := hleft
    _ = ∫⁻ a, ∫⁻ t, G (t, a) := lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ), H (a, x) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr_ae
      filter_upwards [] with a
      by_cases ha : 0 < a
      · simp only [Set.indicator_of_mem (mem_Ioi.mpr ha)]
        calc
          (∫⁻ t, G (t, a)) = ∫⁻ t in Ioi a, H (a, t - a) := by
            rw [← lintegral_indicator measurableSet_Ioi]
            apply lintegral_congr_ae
            filter_upwards [] with t
            by_cases ht : a < t
            · simp only [Set.indicator_of_mem (mem_Ioi.mpr ht)]
              simp [G, ha, ht]
            · simp only [Set.indicator_of_notMem (notMem_Ioi.mpr (le_of_not_gt ht))]
              simp [G, ha, ht]
          _ = ∫⁻ x in Ioi (0 : ℝ), H (a, x) :=
            lintegral_Ioi_sub_right a (fun x => H (a, x))
      · rw [indicator_of_notMem (notMem_Ioi.mpr (le_of_not_gt ha))]
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with t
        have hcond : ¬ (0 < a ∧ a < t) := by
          intro h
          exact ha h.1
        simp [G, hcond]

/-- Tonelli swaps two independently restricted one-dimensional variables. -/
theorem lintegral_swap_restrict_restrict {A B : Set ℝ}
    {F : ℝ → ℝ → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    (∫⁻ x in A, ∫⁻ y in B, F x y) = ∫⁻ y in B, ∫⁻ x in A, F x y := by
  exact lintegral_lintegral_swap hF.aemeasurable

/-- The product of two ordered positive-time triangles becomes four independent
positive durations under Tonelli and translation. -/
theorem lintegral_doublePositiveTriangle_sum
    {H : ℝ × ℝ → ℝ × ℝ → ℝ≥0∞}
    (hH : Measurable (Function.uncurry H)) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      ∫⁻ a in Ioo (0 : ℝ) t, ∫⁻ b in Ioo (0 : ℝ) v,
        H (a, t - a) (b, v - b)) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), H (a, x) (b, z) := by
  have hswap (t : ℝ) :
      (∫⁻ v in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) t,
        ∫⁻ b in Ioo (0 : ℝ) v, H (a, t - a) (b, v - b)) =
      ∫⁻ a in Ioo (0 : ℝ) t, ∫⁻ v in Ioi (0 : ℝ),
        ∫⁻ b in Ioo (0 : ℝ) v, H (a, t - a) (b, v - b) := by
    let F : ℝ → ℝ → ℝ≥0∞ := fun v a =>
      ∫⁻ b in Ioo (0 : ℝ) v, H (a, t - a) (b, v - b)
    have hF : Measurable (Function.uncurry F) := by
      apply measurable_lintegral_Ioo measurable_const measurable_fst
      have harg : Measurable (fun q : (ℝ × ℝ) × ℝ =>
          ((q.1.2, t - q.1.2), (q.2, q.1.1 - q.2))) := by fun_prop
      exact hH.comp harg
    exact lintegral_swap_restrict_restrict hF
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) t,
        ∫⁻ v in Ioi (0 : ℝ), ∫⁻ b in Ioo (0 : ℝ) v,
          H (a, t - a) (b, v - b) := by
      apply lintegral_congr_ae
      filter_upwards [] with t
      exact hswap t
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) t,
        ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ),
          H (a, t - a) (b, z) := by
      apply lintegral_congr_ae
      filter_upwards [] with t
      apply lintegral_congr_ae
      filter_upwards [] with a
      have hSlice : Measurable (fun p : ℝ × ℝ => H (a, t - a) p) := by
        exact hH.comp (measurable_const.prodMk measurable_id)
      exact lintegral_positiveTriangle_sum hSlice
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), H (a, x) (b, z) := by
      let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
      have hZ : Measurable (fun q : (ℝ × ℝ) × ℝ =>
          ∫⁻ z, H q.1 (q.2, z) ∂μ) := by
        apply Measurable.lintegral_prod_right
        have harg : Measurable (fun r : ((ℝ × ℝ) × ℝ) × ℝ =>
            (r.1.1, (r.1.2, r.2))) :=
          measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
        exact hH.comp harg
      have hB : Measurable (fun p : ℝ × ℝ =>
          ∫⁻ b, ∫⁻ z, H p (b, z) ∂μ ∂μ) := by
        apply Measurable.lintegral_prod_right
        exact hZ.comp measurable_id
      change (∫⁻ t in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) t,
          ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), H (a, t - a) (b, z)) = _
      exact lintegral_positiveTriangle_sum hB

/-- The four-duration integrand after taking the two Laplace transforms of a
cut collision interval. -/
noncomputable def scalarCutTransformIntegrandENN (θ rateS rateT : ℝ)
    (p q : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rateS * (p.1 + p.2) + rateT * (q.1 + q.2)))) *
    ENNReal.ofReal (scalarDensity θ p.1) *
    ENNReal.ofReal (scalarDensity θ q.2) *
    ENNReal.ofReal ((p.2 + q.1)⁻¹)

/-- A single scalar-density factor in the cut Laplace transform. -/
noncomputable def scalarCutDensityLaplaceFactorENN (θ rate t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rate * t))) * ENNReal.ofReal (scalarDensity θ t)

/-- The damped reciprocal factor coupling the two crossing durations. -/
noncomputable def scalarCutReciprocalFactorENN (rateS rateT x b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rateS * x + rateT * b))) *
    ENNReal.ofReal ((x + b)⁻¹)

/-- Split the exponential in the four-duration integrand into its independent
left, crossing, and right factors. -/
theorem scalarCutTransformIntegrandENN_eq_mul (θ rateS rateT : ℝ)
    (a x b z : ℝ) :
    scalarCutTransformIntegrandENN θ rateS rateT (a, x) (b, z) =
      scalarCutDensityLaplaceFactorENN θ rateS a *
        scalarCutReciprocalFactorENN rateS rateT x b *
          scalarCutDensityLaplaceFactorENN θ rateT z := by
  dsimp [scalarCutTransformIntegrandENN, scalarCutDensityLaplaceFactorENN,
    scalarCutReciprocalFactorENN]
  have he : Real.exp (-(rateS * (a + x) + rateT * (b + z))) =
      Real.exp (-(rateS * a)) *
        (Real.exp (-(rateS * x + rateT * b)) * Real.exp (-(rateT * z))) := by
    rw [show -(rateS * (a + x) + rateT * (b + z)) =
        -(rateS * a) + (-(rateS * x + rateT * b) + -(rateT * z)) by ring,
      Real.exp_add, Real.exp_add]
  rw [he, ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
  ac_rfl

/-- Pulling a finite constant through two positive integrals. -/
theorem lintegral_const_mul_double (c : ℝ≥0∞) (hc : c ≠ ∞)
    {A B : Set ℝ} {F : ℝ → ℝ → ℝ≥0∞} :
    c * (∫⁻ a in A, ∫⁻ b in B, F a b) =
      ∫⁻ a in A, ∫⁻ b in B, c * F a b := by
  calc
    c * (∫⁻ a in A, ∫⁻ b in B, F a b) =
        ∫⁻ a in A, c * (∫⁻ b in B, F a b) :=
          (lintegral_const_mul' c _ hc).symm
    _ = ∫⁻ a in A, ∫⁻ b in B, c * F a b := by
      apply lintegral_congr_ae
      filter_upwards [] with a
      exact (lintegral_const_mul' c _ hc).symm

/-- The double Laplace transform of the cut kernel is an integral over four positive durations. -/
theorem scalarCut_laplace_flatten (θ rateS rateT : ℝ) :
    (∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v))) * scalarCutKernelENN θ s v) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ),
          scalarCutTransformIntegrandENN θ rateS rateT (a, x) (b, z) := by
  let H : ℝ × ℝ → ℝ × ℝ → ℝ≥0∞ := fun p q =>
    scalarCutTransformIntegrandENN θ rateS rateT p q
  have hH : Measurable (Function.uncurry H) := by
    have hm : Measurable (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) =>
        scalarCutTransformIntegrandENN θ rateS rateT r.1 r.2) := by
      unfold scalarCutTransformIntegrandENN
      have hja : Measurable (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) =>
          scalarDensity θ r.1.1) := by
        exact measurable_scalarDensity.comp
          (measurable_const.prodMk (measurable_fst.fst))
      have hjb : Measurable (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) =>
          scalarDensity θ r.2.2) := by
        exact measurable_scalarDensity.comp
          (measurable_const.prodMk (measurable_snd.snd))
      exact (((by fun_prop : Measurable (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) =>
          ENNReal.ofReal (Real.exp
            (-(rateS * (r.1.1 + r.1.2) + rateT * (r.2.1 + r.2.2)))))).mul
          hja.ennreal_ofReal).mul hjb.ennreal_ofReal).mul
            (by fun_prop : Measurable (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) =>
              ENNReal.ofReal ((r.1.2 + r.2.1)⁻¹)))
    exact hm
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        ∫⁻ a in Ioo (0 : ℝ) s, ∫⁻ b in Ioo (0 : ℝ) v,
          ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v))) *
            ENNReal.ofReal (scalarDensity θ a) *
              ENNReal.ofReal (scalarDensity θ (v - b)) *
                ENNReal.ofReal ((s - a + b)⁻¹) := by
      apply lintegral_congr_ae
      filter_upwards [] with s
      apply lintegral_congr_ae
      filter_upwards [] with v
      rw [scalarCutKernelENN]
      simpa only [mul_assoc] using lintegral_const_mul_double
        (ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v)))) ENNReal.ofReal_ne_top
        (A := Ioo (0 : ℝ) s) (B := Ioo (0 : ℝ) v)
        (F := fun a b => ENNReal.ofReal (scalarDensity θ a) *
          ENNReal.ofReal (scalarDensity θ (v - b)) * ENNReal.ofReal ((s - a + b)⁻¹))
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        ∫⁻ a in Ioo (0 : ℝ) s, ∫⁻ b in Ioo (0 : ℝ) v,
          H (a, s - a) (b, v - b) := by
      apply lintegral_congr_ae
      filter_upwards [] with s
      apply lintegral_congr_ae
      filter_upwards [] with v
      apply lintegral_congr_ae
      filter_upwards [] with a
      apply lintegral_congr_ae
      filter_upwards [] with b
      simp only [H, scalarCutTransformIntegrandENN]
      rw [show a + (s - a) = s by ring,
        show b + (v - b) = v by ring,
        show s - a + b = (s - a) + b by ring]
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ),
          H (a, x) (b, z) := lintegral_doublePositiveTriangle_sum hH
    _ = _ := rfl

/-- The double Laplace transform factors into two scalar-density transforms and the transform of the reciprocal crossing factor. -/
theorem scalarCut_laplace_factor (θ rateS rateT : ℝ) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
      ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ),
        scalarCutTransformIntegrandENN θ rateS rateT (a, x) (b, z)) =
      (∫⁻ a in Ioi (0 : ℝ), scalarCutDensityLaplaceFactorENN θ rateS a) *
        ((∫⁻ z in Ioi (0 : ℝ), scalarCutDensityLaplaceFactorENN θ rateT z) *
          (∫⁻ x in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ),
            scalarCutReciprocalFactorENN rateS rateT x b)) := by
  let A : ℝ → ℝ≥0∞ := scalarCutDensityLaplaceFactorENN θ rateS
  let B : ℝ → ℝ≥0∞ := scalarCutDensityLaplaceFactorENN θ rateT
  let C : ℝ → ℝ → ℝ≥0∞ := scalarCutReciprocalFactorENN rateS rateT
  have hA : Measurable A := by
    dsimp [A, scalarCutDensityLaplaceFactorENN]
    exact (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-(rateS * t))))).mul
      (measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hB : Measurable B := by
    dsimp [B, scalarCutDensityLaplaceFactorENN]
    exact (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-(rateT * t))))).mul
      (measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hC : Measurable (Function.uncurry C) := by
    change Measurable (fun p : ℝ × ℝ =>
      scalarCutReciprocalFactorENN rateS rateT p.1 p.2)
    unfold scalarCutReciprocalFactorENN
    fun_prop
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ b in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), A a * (C x b * B z) := by
      apply lintegral_congr_ae
      filter_upwards [] with a
      apply lintegral_congr_ae
      filter_upwards [] with x
      apply lintegral_congr_ae
      filter_upwards [] with b
      apply lintegral_congr_ae
      filter_upwards [] with z
      rw [scalarCutTransformIntegrandENN_eq_mul]
      ac_rfl
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ b in Ioi (0 : ℝ), (A a * C x b) * ∫⁻ z in Ioi (0 : ℝ), B z := by
      apply lintegral_congr_ae
      filter_upwards [] with a
      apply lintegral_congr_ae
      filter_upwards [] with x
      apply lintegral_congr_ae
      filter_upwards [] with b
      calc
        (∫⁻ z in Ioi (0 : ℝ), A a * (C x b * B z)) =
            ∫⁻ z in Ioi (0 : ℝ), (A a * C x b) * B z := by
              apply lintegral_congr_ae
              filter_upwards [] with z
              ac_rfl
        _ = (A a * C x b) * ∫⁻ z in Ioi (0 : ℝ), B z :=
          lintegral_const_mul (A a * C x b) hB
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        (A a * ∫⁻ z in Ioi (0 : ℝ), B z) *
          ∫⁻ b in Ioi (0 : ℝ), C x b := by
      apply lintegral_congr_ae
      filter_upwards [] with a
      apply lintegral_congr_ae
      filter_upwards [] with x
      calc
        (∫⁻ b in Ioi (0 : ℝ), (A a * C x b) * ∫⁻ z in Ioi (0 : ℝ), B z) =
            ∫⁻ b in Ioi (0 : ℝ),
              (A a * ∫⁻ z in Ioi (0 : ℝ), B z) * C x b := by
                apply lintegral_congr_ae
                filter_upwards [] with b
                ac_rfl
        _ = (A a * ∫⁻ z in Ioi (0 : ℝ), B z) *
              ∫⁻ b in Ioi (0 : ℝ), C x b :=
                lintegral_const_mul (A a * ∫⁻ z in Ioi (0 : ℝ), B z) (hC.comp
                  (measurable_const.prodMk measurable_id))
    _ = (∫⁻ a in Ioi (0 : ℝ), A a) *
          ((∫⁻ z in Ioi (0 : ℝ), B z) *
            (∫⁻ x in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), C x b)) := by
      calc
        _ = ∫⁻ a in Ioi (0 : ℝ),
              A a * ((∫⁻ z in Ioi (0 : ℝ), B z) *
                ∫⁻ x in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), C x b) := by
              apply lintegral_congr_ae
              filter_upwards [] with a
              rw [lintegral_const_mul (A a * ∫⁻ z in Ioi (0 : ℝ), B z)
                (hC.lintegral_prod_right (ν := volume.restrict (Ioi (0 : ℝ))))]
              exact mul_assoc _ _ _
        _ = _ := by
              rw [lintegral_mul_const _ hA]

/-- The one-variable Laplace integral of a scalar-density factor, in
`ENNReal` form. -/
theorem lintegral_scalarCutDensityLaplaceFactorENN (θ rate : ℝ)
    (hrate : 0 < rate) (hθ : θ < Real.log rate) :
    (∫⁻ t in Ioi (0 : ℝ), scalarCutDensityLaplaceFactorENN θ rate t) =
      ENNReal.ofReal ((Real.log rate - θ)⁻¹) := by
  have hInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(rate * t)) * scalarDensity θ t) (Ioi (0 : ℝ)) :=
    integrable_scalarDensity_laplace hrate hθ
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => Real.exp (-(rate * t)) * scalarDensity θ t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (scalarDensity_pos θ ht).le
  calc
    (∫⁻ t in Ioi (0 : ℝ), scalarCutDensityLaplaceFactorENN θ rate t) =
        ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      unfold scalarCutDensityLaplaceFactorENN
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    _ = ENNReal.ofReal
          (∫ t in Ioi (0 : ℝ), Real.exp (-(rate * t)) * scalarDensity θ t) :=
        (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
    _ = ENNReal.ofReal ((Real.log rate - θ)⁻¹) := by
      rw [integral_scalarDensity_laplace hrate hθ]

/-- The elementary exponential Laplace integral in `ENNReal` form. -/
theorem lintegral_exp_neg_mul_Ioi {rate : ℝ} (hrate : 0 < rate) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(rate * t)))) =
      ENNReal.ofReal (rate⁻¹) := by
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-(rate * t))) (Ioi (0 : ℝ)) := by
    have h := integrableOn_exp_mul_Ioi (a := -rate) (by linarith) 0
    apply h.congr
    filter_upwards [] with t
    congr 1
    ring
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => Real.exp (-(rate * t))) := by
    filter_upwards [] with t
    exact (Real.exp_pos _).le
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(rate * t)))) =
        ENNReal.ofReal (∫ t in Ioi (0 : ℝ), Real.exp (-(rate * t))) :=
          (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
    _ = ENNReal.ofReal (rate⁻¹) := by
      congr 1
      rw [show (fun t : ℝ => Real.exp (-(rate * t))) =
          fun t => Real.exp ((-rate) * t) by
            funext t
            congr 1
            ring]
      rw [integral_exp_mul_Ioi (a := -rate) (by linarith) 0]
      simp

/-- A finite-interval exponential integral. -/
theorem integral_exp_neg_mul_interval {rate lo hi : ℝ} (hrate : rate ≠ 0) :
    (∫ t in lo..hi, Real.exp (-(rate * t))) =
      (Real.exp (-(rate * lo)) - Real.exp (-(rate * hi))) / rate := by
  rw [show (fun t : ℝ => Real.exp (-(rate * t))) =
      fun t => Real.exp ((-rate) * t) by
        funext t
        congr 1
        ring]
  rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) (by simpa using hrate)]
  rw [integral_exp]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The same finite-interval exponential integral written as a set integral. -/
theorem integral_exp_neg_mul_Ioo {rate lo hi : ℝ} (hlo : lo ≤ hi)
    (hrate : rate ≠ 0) :
    (∫ t in Ioo lo hi, Real.exp (-(rate * t))) =
      (Real.exp (-(rate * lo)) - Real.exp (-(rate * hi))) / rate := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlo]
  exact integral_exp_neg_mul_interval hrate

/-- Integrating the exponential across a cut, with the reciprocal total
duration held fixed. -/
theorem integral_exp_two_rates_Ioo {rateS rateT r : ℝ} (hr : 0 < r)
    (hrates : rateS ≠ rateT) :
    (∫ x in Ioo (0 : ℝ) r,
      Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) =
        (Real.exp (-(rateT * r)) - Real.exp (-(rateS * r))) /
          ((rateS - rateT) * r) := by
  let δ := rateS - rateT
  have hδ : δ ≠ 0 := sub_ne_zero.mpr hrates
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
  have hfun : (fun x : ℝ =>
      Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) =
        fun x => (Real.exp (-(rateT * r)) * r⁻¹) * Real.exp (-(δ * x)) := by
    funext x
    dsimp [δ]
    rw [show -(rateS * x + rateT * (r - x)) =
      -(rateT * r) + -((rateS - rateT) * x) by ring, Real.exp_add]
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_exp_neg_mul_interval hδ]
  have hE : Real.exp (-(rateS * r)) =
      Real.exp (-(rateT * r)) * Real.exp (-(δ * r)) := by
    rw [show -(rateS * r) = -(rateT * r) + -(δ * r) by dsimp [δ]; ring,
      Real.exp_add]
  rw [hE]
  dsimp [δ]
  field_simp
  simp only [mul_zero, neg_zero, Real.exp_zero]

/-- The finite-interval exponential integral, represented as an `ENNReal`
integral. -/
theorem lintegral_exp_neg_mul_Ioo {rate lo hi : ℝ} (hlohi : lo ≤ hi) :
    (∫⁻ t in Ioo lo hi, ENNReal.ofReal (Real.exp (-(rate * t)))) =
      ENNReal.ofReal (∫ t in Ioo lo hi, Real.exp (-(rate * t))) := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-(rate * t))) := by fun_prop
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-(rate * t))) (Ioo lo hi) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlohi).mp
      (hcont.intervalIntegrable lo hi)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo lo hi)]
      (fun t : ℝ => Real.exp (-(rate * t))) := by
    filter_upwards [] with t
    exact (Real.exp_pos _).le
  exact (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm

/-- The logarithmic mass of an interval under reciprocal Lebesgue measure. -/
theorem lintegral_inv_Ioo {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    (∫⁻ t in Ioo lo hi, ENNReal.ofReal (t⁻¹)) =
      ENNReal.ofReal (Real.log hi - Real.log lo) := by
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Icc lo hi) := by
    apply continuousOn_inv₀.mono
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hlo ht.1)
  have hInt : IntegrableOn (fun t : ℝ => t⁻¹) (Ioo lo hi) := by
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hlohi).mp
      (hcont.intervalIntegrable_of_Icc hlohi)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo lo hi)] (fun t : ℝ => t⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact inv_nonneg.mpr (le_of_lt (lt_trans hlo ht.1))
  calc
    (∫⁻ t in Ioo lo hi, ENNReal.ofReal (t⁻¹)) =
        ENNReal.ofReal (∫ t in Ioo lo hi, t⁻¹) :=
          (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
    _ = ENNReal.ofReal (Real.log hi - Real.log lo) := by
      congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlohi,
        integral_inv_of_pos hlo (lt_of_lt_of_le hlo hlohi), Real.log_div
          (ne_of_gt (lt_of_lt_of_le hlo hlohi)) (ne_of_gt hlo)]

/-- The transform of the reciprocal crossing factor. For ordered positive
rates, this is the Frullani quotient. -/
theorem lintegral_scalarCutReciprocalFactorENN_of_lt {rateT rateS : ℝ}
    (hT : 0 < rateT) (hTS : rateT < rateS) :
    (∫⁻ x in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ),
      scalarCutReciprocalFactorENN rateS rateT x b) =
        ENNReal.ofReal ((Real.log rateS - Real.log rateT) / (rateS - rateT)) := by
  let H : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(rateS * p.1 + rateT * p.2))) *
      ENNReal.ofReal ((p.1 + p.2)⁻¹)
  have hH : Measurable H := by
    dsimp [H]
    fun_prop
  have hTriangle := lintegral_positiveTriangle_sum hH
  have hInner (r : ℝ) (hr : 0 < r) :
      (∫⁻ x in Ioo (0 : ℝ) r, H (x, r - x)) =
        ENNReal.ofReal ((Real.exp (-(rateT * r)) -
          Real.exp (-(rateS * r))) / ((rateS - rateT) * r)) := by
    have hfun : (fun x : ℝ => H (x, r - x)) = fun x =>
        ENNReal.ofReal (Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) := by
      funext x
      dsimp [H]
      rw [show x + (r - x) = r by ring,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [hfun]
    have hcont : ContinuousOn (fun x : ℝ =>
        Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) (Icc 0 r) := by fun_prop
    have hInt : IntegrableOn (fun x : ℝ =>
        Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) (Ioo 0 r) := by
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).mp
        (hcont.intervalIntegrable_of_Icc hr.le)
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)]
        (fun x : ℝ => Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hr.le)
    calc
      (∫⁻ x in Ioo (0 : ℝ) r,
          ENNReal.ofReal (Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹)) =
          ENNReal.ofReal (∫ x in Ioo (0 : ℝ) r,
            Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) :=
              (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
      _ = ENNReal.ofReal ((Real.exp (-(rateT * r)) -
            Real.exp (-(rateS * r))) / ((rateS - rateT) * r)) := by
              rw [integral_exp_two_rates_Ioo hr (ne_of_gt hTS)]
  have hParam (r : ℝ) (hr : 0 < r) :
      (Real.exp (-(rateT * r)) - Real.exp (-(rateS * r))) /
          ((rateS - rateT) * r) =
        (rateS - rateT)⁻¹ *
          ∫ t in Ioo rateT rateS, Real.exp (-(r * t)) := by
    rw [integral_exp_neg_mul_Ioo (rate := r) (lo := rateT) (hi := rateS)
      hTS.le hr.ne']
    field_simp
  have hparamNonneg : 0 ≤ (rateS - rateT)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hTS.le)
  have hExpMeas : Measurable (Function.uncurry (fun r t : ℝ =>
      ENNReal.ofReal (Real.exp (-(r * t))))) := by
    fun_prop
  calc
    (∫⁻ x in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ),
        scalarCutReciprocalFactorENN rateS rateT x b) =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ x in Ioo (0 : ℝ) r, H (x, r - x) := by
        change (∫⁻ x in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), H (x, b)) = _
        exact hTriangle.symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal
        ((rateS - rateT)⁻¹ *
          ∫ t in Ioo rateT rateS, Real.exp (-(r * t))) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          rw [hInner r hr, hParam r hr]
    _ = ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal ((rateS - rateT)⁻¹) *
          ∫⁻ t in Ioo rateT rateS, ENNReal.ofReal (Real.exp (-(r * t))) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          rw [ENNReal.ofReal_mul hparamNonneg,
            lintegral_exp_neg_mul_Ioo (rate := r) (lo := rateT) (hi := rateS)
              hTS.le]
    _ = ENNReal.ofReal ((rateS - rateT)⁻¹) *
        (∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioo rateT rateS,
          ENNReal.ofReal (Real.exp (-(r * t)))) := by
          exact lintegral_const_mul' (ENNReal.ofReal ((rateS - rateT)⁻¹)) _
            ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((rateS - rateT)⁻¹) *
        (∫⁻ t in Ioo rateT rateS, ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(r * t)))) := by
          congr 1
          exact lintegral_swap_restrict_restrict hExpMeas
    _ = ENNReal.ofReal ((rateS - rateT)⁻¹) *
        (∫⁻ t in Ioo rateT rateS, ENNReal.ofReal (t⁻¹)) := by
          congr 1
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          calc
            (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(r * t)))) =
                ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * r))) := by
                  apply lintegral_congr_ae
                  filter_upwards [] with r
                  congr 2
                  ring
            _ = ENNReal.ofReal (t⁻¹) :=
                lintegral_exp_neg_mul_Ioi (lt_trans hT ht.1)
    _ = ENNReal.ofReal ((rateS - rateT)⁻¹) *
        ENNReal.ofReal (Real.log rateS - Real.log rateT) := by
          rw [lintegral_inv_Ioo hT hTS.le]
    _ = ENNReal.ofReal
        ((Real.log rateS - Real.log rateT) / (rateS - rateT)) := by
          rw [← ENNReal.ofReal_mul hparamNonneg]
          congr 1
          field_simp

/-- Integrating the exponential across a cut without the reciprocal duration. -/
theorem integral_exp_two_rates_noRecip_Ioo {rateS rateT r : ℝ} (hr : 0 < r)
    (hrates : rateS ≠ rateT) :
    (∫ x in Ioo (0 : ℝ) r, Real.exp (-(rateS * x + rateT * (r - x)))) =
      (Real.exp (-(rateT * r)) - Real.exp (-(rateS * r))) / (rateS - rateT) := by
  have hfun : (fun x : ℝ =>
      Real.exp (-(rateS * x + rateT * (r - x)))) = fun x =>
        r * (Real.exp (-(rateS * x + rateT * (r - x))) * r⁻¹) := by
    funext x
    field_simp [ne_of_gt hr]
  rw [hfun, integral_const_mul, integral_exp_two_rates_Ioo hr hrates]
  field_simp [ne_of_gt hr]

/-- The double Laplace transform of the density evaluated at the sum of its
two time variables. -/
theorem scalarDensity_sum_doubleLaplaceENN_of_lt {θ rateT rateS : ℝ}
    (hT : 0 < rateT) (hTS : rateT < rateS)
    (hθT : θ < Real.log rateT) (hθS : θ < Real.log rateS) :
    (∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v)) *
        scalarDensity θ (s + v))) =
      ENNReal.ofReal (((Real.log rateT - θ)⁻¹ -
        (Real.log rateS - θ)⁻¹) / (rateS - rateT)) := by
  let H : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(rateS * p.1 + rateT * p.2)) *
      scalarDensity θ (p.1 + p.2))
  have hH : Measurable H := by
    dsimp [H]
    have hj : Measurable (fun p : ℝ × ℝ => scalarDensity θ (p.1 + p.2)) := by
      exact measurable_scalarDensity.comp
        (measurable_const.prodMk (measurable_fst.add measurable_snd))
    exact ((by fun_prop : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(rateS * p.1 + rateT * p.2)))).mul hj).ennreal_ofReal
  have hInner (r : ℝ) (hr : 0 < r) :
      (∫⁻ x in Ioo (0 : ℝ) r, H (x, r - x)) =
        ENNReal.ofReal (scalarDensity θ r *
          ((Real.exp (-(rateT * r)) - Real.exp (-(rateS * r))) /
            (rateS - rateT))) := by
    have hfun : (fun x : ℝ => H (x, r - x)) = fun x =>
        ENNReal.ofReal (Real.exp (-(rateS * x + rateT * (r - x))) *
          scalarDensity θ r) := by
      funext x
      dsimp [H]
      rw [show x + (r - x) = r by ring]
    rw [hfun]
    have hcont : ContinuousOn (fun x : ℝ =>
        Real.exp (-(rateS * x + rateT * (r - x))) * scalarDensity θ r)
          (Icc 0 r) := by fun_prop
    have hInt : IntegrableOn (fun x : ℝ =>
        Real.exp (-(rateS * x + rateT * (r - x))) * scalarDensity θ r)
          (Ioo 0 r) := by
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).mp
        (hcont.intervalIntegrable_of_Icc hr.le)
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)]
        (fun x : ℝ => Real.exp (-(rateS * x + rateT * (r - x))) *
          scalarDensity θ r) := by
      filter_upwards [] with x
      exact mul_nonneg (Real.exp_pos _).le (scalarDensity_pos θ hr).le
    calc
      (∫⁻ x in Ioo (0 : ℝ) r,
          ENNReal.ofReal (Real.exp (-(rateS * x + rateT * (r - x))) *
            scalarDensity θ r)) =
        ENNReal.ofReal (∫ x in Ioo (0 : ℝ) r,
          Real.exp (-(rateS * x + rateT * (r - x))) * scalarDensity θ r) :=
            (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
      _ = ENNReal.ofReal (scalarDensity θ r *
          ∫ x in Ioo (0 : ℝ) r,
            Real.exp (-(rateS * x + rateT * (r - x)))) := by
              congr 1
              rw [show (fun x : ℝ =>
                Real.exp (-(rateS * x + rateT * (r - x))) * scalarDensity θ r) =
                  fun x => scalarDensity θ r *
                    Real.exp (-(rateS * x + rateT * (r - x))) by
                      funext x
                      ring,
                integral_const_mul]
      _ = ENNReal.ofReal (scalarDensity θ r *
          ((Real.exp (-(rateT * r)) - Real.exp (-(rateS * r))) /
            (rateS - rateT))) := by
              rw [integral_exp_two_rates_noRecip_Ioo hr (ne_of_gt hTS)]
  let Δ : ℝ → ℝ := fun r =>
    Real.exp (-(rateT * r)) * scalarDensity θ r -
      Real.exp (-(rateS * r)) * scalarDensity θ r
  have hΔint : Integrable Δ (volume.restrict (Ioi (0 : ℝ))) := by
    dsimp [Δ]
    exact (integrable_scalarDensity_laplace hT hθT).sub
      (integrable_scalarDensity_laplace (lt_trans hT hTS) hθS)
  have hΔnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] Δ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp [Δ]
    have he : Real.exp (-(rateS * r)) ≤ Real.exp (-(rateT * r)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_lt_mul_of_pos_right hTS hr
      nlinarith
    rw [← sub_mul]
    exact mul_nonneg (sub_nonneg.mpr he) (scalarDensity_pos θ hr).le
  have hΔlap : (∫ r in Ioi (0 : ℝ), Δ r) =
      (Real.log rateT - θ)⁻¹ - (Real.log rateS - θ)⁻¹ := by
    dsimp [Δ]
    rw [integral_sub (integrable_scalarDensity_laplace hT hθT)
      (integrable_scalarDensity_laplace (lt_trans hT hTS) hθS),
      integral_scalarDensity_laplace hT hθT,
      integral_scalarDensity_laplace (lt_trans hT hTS) hθS]
  have hk : 0 ≤ (rateS - rateT)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hTS.le)
  have hparam (r : ℝ) (hr : 0 < r) :
      scalarDensity θ r *
          ((Real.exp (-(rateT * r)) - Real.exp (-(rateS * r))) /
            (rateS - rateT)) = (rateS - rateT)⁻¹ * Δ r := by
    dsimp [Δ]
    field_simp [ne_of_gt (sub_pos.mpr hTS)]
  calc
    (∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v)) *
          scalarDensity θ (s + v))) =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ x in Ioo (0 : ℝ) r, H (x, r - x) := by
        change (∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ), H (s, v)) = _
        exact (lintegral_positiveTriangle_sum hH).symm
    _ = ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal ((rateS - rateT)⁻¹) * ENNReal.ofReal (Δ r) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          rw [hInner r hr, hparam r hr, ENNReal.ofReal_mul hk]
    _ = ENNReal.ofReal ((rateS - rateT)⁻¹) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Δ r) :=
          lintegral_const_mul' (ENNReal.ofReal ((rateS - rateT)⁻¹)) _
            ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((rateS - rateT)⁻¹) *
        ENNReal.ofReal (∫ r in Ioi (0 : ℝ), Δ r) := by
          rw [(ofReal_integral_eq_lintegral_ofReal hΔint hΔnonneg).symm]
    _ = ENNReal.ofReal
        (((Real.log rateT - θ)⁻¹ - (Real.log rateS - θ)⁻¹) /
          (rateS - rateT)) := by
          rw [hΔlap, ← ENNReal.ofReal_mul hk]
          congr 1
          field_simp

/-- The double Laplace transform of the cut collision kernel, evaluated by
its two scalar-density factors and the reciprocal crossing factor. -/
theorem scalarCut_doubleLaplaceENN_of_lt {θ rateT rateS : ℝ}
    (hT : 0 < rateT) (hTS : rateT < rateS)
    (hθT : θ < Real.log rateT) (hθS : θ < Real.log rateS) :
    (∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v))) *
        scalarCutKernelENN θ s v) =
      ENNReal.ofReal ((Real.log rateS - θ)⁻¹ *
        ((Real.log rateT - θ)⁻¹ *
          ((Real.log rateS - Real.log rateT) / (rateS - rateT)))) := by
  rw [scalarCut_laplace_flatten, scalarCut_laplace_factor,
    lintegral_scalarCutDensityLaplaceFactorENN θ rateS (lt_trans hT hTS) hθS,
    lintegral_scalarCutDensityLaplaceFactorENN θ rateT hT hθT,
    lintegral_scalarCutReciprocalFactorENN_of_lt hT hTS]
  have hJS : 0 ≤ (Real.log rateS - θ)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hθS.le)
  have hJT : 0 ≤ (Real.log rateT - θ)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hθT.le)
  rw [← ENNReal.ofReal_mul hJT, ← ENNReal.ofReal_mul hJS]

end Critical2DKPZ.SHF.Flow

end
