/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzFubini
public import Critical2DKPZ.Extensions.ScaleLimit.SpectralContraction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Continuous primitive versions of differentiable L2 curves -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- A continuous real-parameter L2 curve has a jointly measurable version. -/
theorem exists_real_joint_L2_version (V : ℝ → Lp ℝ 2 P) (hV : Continuous V) :
    ∃ v : ℝ → Ω → ℝ, Measurable (Function.uncurry v) ∧
      ∀ t, v t =ᵐ[P] (V t : Ω → ℝ) := by
  let e : ℝ → Plane := fun r => r • PiLp.single 2 (0 : Fin 2) (1 : ℝ)
  have he : Continuous e := continuous_id.smul continuous_const
  have he0 (r : ℝ) : e r 0 = r := by simp [e]
  obtain ⟨G, hGm, hG⟩ := exists_jointlyMeasurable_Lp_version P
    (fun y : Plane => V (y 0)) (hV.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0))
  refine ⟨fun r ω => G (e r) ω, ?_, ?_⟩
  · exact hGm.comp ((he.measurable.comp measurable_fst).prodMk measurable_snd)
  · intro r
    simpa only [he0] using hG (e r)

/-- On a compact parameter interval, a continuous L2 curve's measurable
version is jointly square integrable. -/
theorem integral_L2_version_sq_prod (V : ℝ → Lp ℝ 2 P) (hV : Continuous V)
    (v : ℝ → Ω → ℝ) (hvm : Measurable (Function.uncurry v))
    (hrep : ∀ t, v t =ᵐ[P] (V t : Ω → ℝ)) (α β : ℝ) :
    Integrable (fun q : ℝ × Ω => v q.1 q.2 ^ 2)
      ((volume.restrict (Set.Icc α β)).prod P) := by
  apply (integrable_prod_iff (hvm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun t =>
    ((memLp_congr_ae (hrep t)).mpr (Lp.memLp (V t))).integrable_sq), ?_⟩
  have heq : (fun t : ℝ => ∫ ω, ‖v t ω ^ 2‖ ∂P) = fun t => ‖V t‖ ^ 2 := by
    funext t
    calc
      _ = ∫ ω, ‖V t ω‖ ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hrep t] with ω hω
        rw [hω, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs]
      _ = _ := (norm_Lp_two_sq P (V t)).symm
  change Integrable (fun t : ℝ => ∫ ω, ‖v t ω ^ 2‖ ∂P) _
  rw [heq]
  exact (hV.norm.pow 2).integrableOn_Icc

/-- The same representative is jointly integrable on compact time intervals. -/
theorem integral_L2_version_prod (V : ℝ → Lp ℝ 2 P) (hV : Continuous V)
    (v : ℝ → Ω → ℝ) (hvm : Measurable (Function.uncurry v))
    (hrep : ∀ t, v t =ᵐ[P] (V t : Ω → ℝ)) (α β : ℝ) :
    Integrable (Function.uncurry v) ((volume.restrict (Set.Icc α β)).prod P) := by
  have hs := integral_L2_version_sq_prod P V hV v hvm hrep α β
  apply (hs.add (integrable_const 1)).mono' hvm.aestronglyMeasurable
  filter_upwards [] with q
  change |v q.1 q.2| ≤ v q.1 q.2 ^ 2 + 1
  apply abs_le.mpr
  constructor <;> nlinarith only [sq_nonneg (v q.1 q.2 - 1), sq_nonneg (v q.1 q.2 + 1)]

/-- A primitive of a jointly measurable derivative is a version of the original
L2 curve at each fixed time. The primitive has continuous paths on a single
full-measure event; no intersection over uncountably many times is used. -/
theorem L2_curve_primitive_version (F V : ℝ → Lp ℝ 2 P)
    (hV : Continuous V) (α β : ℝ)
    (hder : ∀ r ∈ Set.Icc α β, HasDerivAt F (V r) r)
    (v : ℝ → Ω → ℝ) (hvm : Measurable (Function.uncurry v))
    (hrep : ∀ t, v t =ᵐ[P] (V t : Ω → ℝ)) :
    (∀ r ∈ Set.Icc α β,
      (fun ω => F α ω + ∫ t in Set.Icc α r, v t ω) =ᵐ[P] (F r : Ω → ℝ)) ∧
    ∀ᵐ ω ∂P, ContinuousOn (fun r => F α ω + ∫ t in Set.Icc α r, v t ω) (Set.Icc α β) := by
  have hvprod := integral_L2_version_prod P V hV v hvm hrep α β
  refine ⟨?_, ?_⟩
  · intro r hr
    have hVr : Integrable V (volume.restrict (Set.Icc α r)) := hV.integrableOn_Icc
    have hfprod := integral_L2_version_prod P V hV v hvm hrep α r
    have hcomm := integral_L2_ae_eq P (volume.restrict (Set.Icc α r)) V hVr hfprod
      (fun t => (hrep t).symm)
    have hFTC : (∫ t in Set.Icc α r, V t) = F r - F α := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.1]
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        rw [Set.uIcc_of_le hr.1] at ht
        exact hder t ⟨ht.1, ht.2.trans hr.2⟩
      · exact hV.intervalIntegrable α r
    rw [hFTC] at hcomm
    filter_upwards [hcomm, Lp.coeFn_sub (F r) (F α)] with ω hω hsub
    change _ = F r ω - F α ω at hsub
    rw [← hω, hsub]
    ring
  · filter_upwards [hvprod.prod_left_ae] with ω hω
    exact continuousOn_const.add (intervalIntegral.continuousOn_primitive_Icc hω)

end Critical2DKPZ.Extensions.ScaleLimit
