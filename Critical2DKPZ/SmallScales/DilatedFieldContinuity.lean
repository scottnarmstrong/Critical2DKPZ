/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.SmallBallKernel
public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Analysis.Sobolev.TestFunctionFamily
public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Spatial continuity of distribution pairings -/

@[expose] public section

noncomputable section

open Filter Topology
open MeasureTheory
open TopologicalSpace
open scoped BoundedContinuousFunction CompactlySupported Distributions

namespace Critical2DKPZ.SmallScales

/-- Pairing a distribution with a fixed-scale dilated test is continuous in its spatial center. -/
theorem continuous_dilated_test_pairing (T : Distr) (φ : TestFn) (ε : ℝ) :
    Continuous (fun x : Plane => T (φ.dilate ε x)) := by
  rcases eq_or_ne ε 0 with hε | hε
  · subst ε
    have hzero (x : Plane) : φ.dilate 0 x = 0 := by
      apply TestFunction.ext
      intro y
      simp [TestFn.dilate]
    simpa only [hzero, map_zero] using (continuous_const : Continuous fun _ : Plane => (0 : ℝ))
  · apply continuous_iff_continuousAt.mpr
    intro x₀
    let q : Plane → Plane := fun x =>
      Critical2DKPZ.localizer 0 (x - x₀) • (x - x₀) + x₀
    have hcut : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => Critical2DKPZ.localizer 0 (x - x₀)) :=
      (Critical2DKPZ.localizer 0).contDiff.comp (contDiff_id.sub contDiff_const)
    have hq : ContDiff ℝ (⊤ : ℕ∞) q := by
      dsimp [q]
      exact hcut.smul (contDiff_id.sub contDiff_const) |>.add contDiff_const
    let Q : Set Plane := Metric.closedBall x₀ 2
    have hQcompact : IsCompact Q := by
      dsimp [Q]
      exact isCompact_closedBall x₀ 2
    have hqQ (x : Plane) : q x ∈ Q := by
      have hcutNonneg : 0 ≤ Critical2DKPZ.localizer 0 (x - x₀) :=
        Critical2DKPZ.localizer_nonneg 0 (x - x₀)
      have hcutLe : Critical2DKPZ.localizer 0 (x - x₀) ≤ 1 :=
        Critical2DKPZ.localizer_le_one 0 (x - x₀)
      rw [Metric.mem_closedBall, dist_eq_norm]
      dsimp [q]
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcutNonneg]
      by_cases hcutZero : Critical2DKPZ.localizer 0 (x - x₀) = 0
      · simp [hcutZero]
      · have hxSupport : x - x₀ ∈ tsupport (Critical2DKPZ.localizer 0) :=
          subset_tsupport _ hcutZero
        have hxNorm : ‖x - x₀‖ ≤ 2 := by
          have hxBall := (Critical2DKPZ.tsupport_localizer 0) ▸ hxSupport
          rw [Metric.mem_closedBall, dist_eq_norm] at hxBall
          simpa using hxBall
        calc
          Critical2DKPZ.localizer 0 (x - x₀) * ‖x - x₀‖ ≤
              1 * ‖x - x₀‖ := mul_le_mul_of_nonneg_right hcutLe (norm_nonneg _)
          _ ≤ 2 := by simpa using hxNorm
    let S : Set Plane := tsupport φ
    let K : Set Plane :=
      (fun p : Plane × Plane => p.1 + ε • p.2) '' (Q ×ˢ S)
    have hKcompact : IsCompact K := by
      dsimp [K]
      apply (hQcompact.prod φ.hasCompactSupport.isCompact).image
      fun_prop
    let K' : Compacts Plane := ⟨K, hKcompact⟩
    let f : Plane → TestFn := fun x => φ.dilate ε (q x)
    have hSupport (x : Plane) : tsupport (f x) ⊆ K := by
      apply closure_minimal ?_ hKcompact.isClosed
      intro y hy
      have hφnonzero : φ (ε⁻¹ • (y - q x)) ≠ 0 := by
        intro hz
        apply hy
        simp [f, TestFn.dilate, hz]
      have hz : ε⁻¹ • (y - q x) ∈ S := by
        exact subset_tsupport φ hφnonzero
      have himage : q x + ε • (ε⁻¹ • (y - q x)) ∈ K := by
        exact ⟨(q x, ε⁻¹ • (y - q x)), ⟨hqQ x, hz⟩, rfl⟩
      have heq : q x + ε • (ε⁻¹ • (y - q x)) = y := by
        calc
          q x + ε • (ε⁻¹ • (y - q x)) = q x + (ε * ε⁻¹) • (y - q x) := by
            rw [smul_smul]
          _ = q x + (y - q x) := by rw [mul_inv_cancel₀ hε, one_smul]
          _ = y := by abel
      rw [← heq]
      exact himage
    have hqparam : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => q p.1) :=
      hq.comp contDiff_fst
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : Plane × Plane => ε⁻¹ • (p.2 - q p.1)) := by
      fun_prop
    have hfjoint : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : Plane × Plane => f p.1 p.2) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun p : Plane × Plane => ε⁻¹ ^ 2 * φ (ε⁻¹ • (p.2 - q p.1)))
      exact contDiff_const.mul (φ.contDiff.comp harg)
    have hfcont : Continuous f := continuous_testFn_family K' f hSupport hfjoint
    have hgcont : Continuous (fun x : Plane => T (f x)) := T.continuous.comp hfcont
    have hlocal : ∀ᶠ x in 𝓝 x₀, q x = x := by
      filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
      have hdist : dist x x₀ < 1 := by simpa [Metric.mem_ball] using hx
      have hxBall : x - x₀ ∈ Metric.closedBall (0 : Plane) 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        simpa [dist_eq_norm] using hdist.le
      have hcutOne : Critical2DKPZ.localizer 0 (x - x₀) = 1 :=
        Critical2DKPZ.localizer_eq_one_of_mem_closedBall 0 (by simpa using hxBall)
      dsimp [q]
      rw [hcutOne]
      simp
    have hpairEq : (fun x => T (f x)) =ᶠ[𝓝 x₀]
        (fun x => T (φ.dilate ε x)) := by
      filter_upwards [hlocal] with x hx
      exact congrArg (fun z => T (φ.dilate ε z)) hx
    exact hgcont.continuousAt.congr hpairEq

/-- Almost-everywhere measurable evaluations of a random distribution, together with samplewise
spatial continuity, give a measurable modification of the translated-dilate pairing. -/
theorem exists_measurable_modification_joint_dilated_test_pairing_of_aemeasurable_sections
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (t ε : ℝ) (φ : TestFn)
    (hsections : ∀ x : Plane, AEMeasurable
      (fun ω => H t 0 ω (φ.dilate ε x)) P) :
    ∃ G : Plane × Ω → ℝ, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ x : Plane,
        G (x, ω) = H t 0 ω (φ.dilate ε x) := by
  let hId : StronglyMeasurable (id : Plane → Plane) := stronglyMeasurable_id
  let c : ℕ → SimpleFunc Plane Plane := hId.approx
  let f : Plane → Ω → ℝ := fun x ω => H t 0 ω (φ.dilate ε x)
  let v : Plane → Ω → ℝ := fun x => (hsections x).mk (f x)
  let Gₙ : ℕ → Plane × Ω → ℝ := fun n z => v (c n z.1) z.2
  have hGₙ (n : ℕ) : Measurable (Gₙ n) := by
    have hsections_meas (x : Plane) : Measurable (v x) := by
      exact (hsections x).measurable_mk
    have hfinite : Measurable (fun p : (c n).range × Ω => v p.1 p.2) := by
      have hswap : Measurable (fun p : Ω × (c n).range => v p.2 p.1) :=
        measurable_from_prod_countable_left fun q => hsections_meas q.1
      convert hswap.comp measurable_swap using 1
      funext p
      rfl
    have hmap : Measurable (fun z : Plane × Ω =>
        ((⟨c n z.1, SimpleFunc.mem_range_self _ _⟩ : (c n).range), z.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      exact ((c n).measurable.comp measurable_fst).subtype_mk
    change Measurable (fun z : Plane × Ω =>
      (fun p : (c n).range × Ω => v p.1 p.2)
        ((⟨c n z.1, SimpleFunc.mem_range_self _ _⟩ : (c n).range), z.2))
    exact hfinite.comp hmap
  have hcenters : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ q : (c n).range,
      f q.1 ω = v q.1 ω := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro q
    exact (hsections q.1).ae_eq_mk
  let G : Plane × Ω → ℝ := fun z => limsup (fun n => Gₙ n z) atTop
  have hG : Measurable G := by
    exact Measurable.limsup hGₙ
  refine ⟨G, hG, ?_⟩
  filter_upwards [hcenters] with ω hω x
  have hconv : Tendsto (fun n => Gₙ n (x, ω)) atTop (𝓝 (f x ω)) := by
    have hactual : Tendsto (fun n => f (c n x) ω) atTop (𝓝 (f x ω)) := by
      exact (continuous_dilated_test_pairing (H t 0 ω) φ ε).continuousAt.tendsto.comp
        (hId.tendsto_approx x)
    apply hactual.congr'
    filter_upwards [] with n
    exact hω n ⟨c n x, SimpleFunc.mem_range_self _ _⟩
  have hlimsup : limsup (fun n => Gₙ n (x, ω)) atTop = f x ω := hconv.limsup_eq
  exact hlimsup

end Critical2DKPZ.SmallScales

end
