/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.TestFn
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Critical2DKPZ.Assembly.HeatStartLog
import Critical2DKPZ.JointConvergence.ThmToyJointLimit
import Critical2DKPZ.JointConvergence.ThmToyJointLimitEstimates
import Critical2DKPZ.SHF.Symmetries.LatticeReversal
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.Linarith

/-! # Finite moments of tested regularized KPZ fields

Time reversal transports the reversed-field moment bound to every admissible
forward width. The transport uses equality of laws, without identifying
realizations of the two fields.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.Extensions.Common

/-- Every admissible positive regularization width has finite tested moments
of every finite exponent at least one. -/
theorem memLp_kpzRegularized_pairing (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) (hδt : δ < t)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞) (_hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    MemLp (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) p P := by
  let q : ℝ := p.toReal + 2
  have hq : 1 < q := by dsimp [q]; linarith [ENNReal.toReal_nonneg (a := p)]
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  obtain ⟨_C, _hC, hbound⟩ :=
    JointConvergence.kpzRegularizedReversed_test_rpow_log_width_bound ϑ P Z hZ
      (fun hs hst hδ x g =>
        SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g)
      (fun k s t δ x g h =>
        SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ k s t δ x g h)
      (fun s t δ x h₀ hs hst hδ =>
        ⟨(SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
            ϑ P Z hZ s t δ x h₀ hs hst hδ).1,
          (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
            ϑ P Z hZ s t δ x h₀ hs hst hδ).2.1⟩)
      0 t t le_rfl ht ht (by simp) h₀ φ hq
  have hrev := hbound δ ⟨hδ, hδt⟩
  let f : Ω → ℝ := fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω
  let g : Ω → ℝ := fun ω => ∫ x, φ x * kpzRegularizedReversed P Z 0 t δ h₀ x ω
  have hgq : MemLp g (ENNReal.ofReal q) P := by
    apply (integrable_norm_rpow_iff hrev.1 (by simp [hq0]) (by simp)).mp
    simpa only [g, Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le] using hrev.2.1
  have hpq : p ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_toReal hp_top]
    apply ENNReal.ofReal_le_ofReal
    dsimp [q]
    linarith
  have hgp : MemLp g p P := hgq.mono_exponent hpq
  have hf : AEMeasurable f P :=
    JointConvergence.aemeasurable_integral_kpzRegularized ϑ P Z hZ t δ hδt hδ h₀ φ
  have hF : AEMeasurable (fun ω (_ : Fin 1) => f ω) P :=
    aemeasurable_pi_iff.mpr fun _ => hf
  have hG : AEMeasurable (fun ω (_ : Fin 1) => g ω) P :=
    aemeasurable_pi_iff.mpr fun _ => hrev.1.aemeasurable
  have hlaw : P.map (fun ω (_ : Fin 1) => f ω) =
      P.map (fun ω (_ : Fin 1) => g ω) := by
    simpa only [f, g, sub_self] using
      JointConvergence.kpzRegularized_reverse_law_of ϑ P Z hZ t
        (SHF.Symmetries.isCriticalSHF_reverse_fdd ϑ P Z hZ t)
        1 (fun _ => t) (fun _ => δ) (fun _ => h₀) (fun _ => φ)
        (fun _ => ⟨hδ, hδt, le_rfl⟩)
  have hpush : MemLp (fun v : Fin 1 → ℝ => v 0) p
      (P.map (fun ω (_ : Fin 1) => g ω)) := by
    exact (memLp_map_measure_iff (measurable_pi_apply 0).aestronglyMeasurable hG).2 hgp
  rw [← hlaw] at hpush
  exact hpush.comp_of_map hF

end Critical2DKPZ.Extensions.Common

end
