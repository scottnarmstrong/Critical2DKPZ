/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HeatField
public import Critical2DKPZ.Extensions.ScaleLimit.ScalarNormalization
public import Critical2DKPZ.Extensions.ScaleLimit.SlutskyTools
public import Critical2DKPZ.Extensions.ScaleLimit.EventualLawTransfer
import Critical2DKPZ.Provider.ShfLogNormality
import Mathlib.Tactic

/-! # The scalar Gaussian limit on a geometric grid

The scalar SHF theorem is composed with geometric widths. The resulting
logarithmic clock differs from `log n` by a constant, removed by Slutsky.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The geometric scalar limit, indexed so that every raw heat-start field is
evaluated at an admissible time. -/
theorem scalar_clt_geometric_succ (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (ρ : ℝ) (hρ : 1 < ρ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Fheat Z (tau ρ (n + 1)) 0 ω -
        ∫ ω', Fheat Z (tau ρ (n + 1)) 0 ω' ∂P) /
          Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)))
      atTop id (fun _ => P) (gaussianReal 0 1) := by
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn => by omega⟩
  let ε : ℕ → Set.Ioo (0 : ℝ) 1 := fun n =>
    ⟨Real.sqrt (tau ρ (n + 1)), Real.sqrt_pos.mpr (tau_pos hρ _), by
      have hsq := Real.sq_sqrt (tau_pos hρ (n + 1)).le
      have hnonneg := Real.sqrt_nonneg (tau ρ (n + 1))
      have hlt := tau_lt_one hρ (Nat.zero_lt_succ n)
      nlinarith⟩
  have hεsq (n : ℕ) : (ε n : ℝ) ^ 2 = tau ρ (n + 1) :=
    Real.sq_sqrt (tau_pos hρ (n + 1)).le
  have hεzero : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ((tendsto_tau_zero hρ).comp hsucc)
  have hεwithin : Tendsto (fun n => (ε n : ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεzero, Eventually.of_forall (fun n => (ε n).property.1)⟩
  have hεfilter : Tendsto ε atTop
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def] using hεwithin
  have hunit := Critical2DKPZ.Provider.shf_logNormality ϑ P Z hZ 0
  have hmain : TendstoInDistribution
      (fun n ω => (Fheat Z ((ε n : ℝ) ^ 2) 0 ω -
        ∫ ω', Fheat Z ((ε n : ℝ) ^ 2) 0 ω' ∂P) /
          Real.sqrt (Real.log (Real.log (ε n : ℝ)⁻¹)))
      atTop id (fun _ => P) (gaussianReal 0 1) := by
    refine ⟨?_, hunit.aemeasurable_limit, ?_⟩
    · intro n
      simpa only [Fheat] using hunit.forall_aemeasurable (ε n)
    · convert! hunit.tendsto.comp hεfilter using 1
  let A : ℕ → ℝ := fun n => Real.log ((n + 1 : ℕ) : ℝ)
  let c₀ : ℝ := Real.log (Real.log ρ / 2)
  have hA : Tendsto A atTop atTop := by
    simpa only [A, Function.comp_def] using
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsucc)
  have hclock (n : ℕ) : Real.log (Real.log (ε n : ℝ)⁻¹) = A n + c₀ :=
    loglog_inv_sqrt_tau hρ (Nat.zero_lt_succ n)
  let W : ℕ → Ω → ℝ := fun n ω =>
    (Fheat Z (tau ρ (n + 1)) 0 ω - ∫ ω', Fheat Z (tau ρ (n + 1)) 0 ω' ∂P) /
      Real.sqrt (A n + c₀)
  have hW : TendstoInDistribution W atTop id (fun _ => P) (gaussianReal 0 1) := by
    simpa only [hεsq, hclock, W] using hmain
  let c : ℕ → ℝ := fun n => Real.sqrt (A n + c₀) / Real.sqrt (A n)
  have hc : Tendsto c atTop (𝓝 1) := tendsto_sqrt_add_div_sqrt A hA c₀
  have hscaled := tendstoInDistribution_smul_of_tendsto P (gaussianReal 0 1) hW hc
  have hmatch : ∀ᶠ n in atTop,
      (fun ω => c n * W n ω) = (fun ω =>
        (Fheat Z (tau ρ (n + 1)) 0 ω - ∫ ω', Fheat Z (tau ρ (n + 1)) 0 ω' ∂P) /
          Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ))) := by
    filter_upwards [hA.eventually_gt_atTop (max 0 (-c₀))] with n hn
    have hApos : 0 < A n := lt_of_le_of_lt (le_max_left _ _) hn
    have hAc : 0 < A n + c₀ := by linarith [le_max_right 0 (-c₀)]
    have hsA : Real.sqrt (A n) ≠ 0 := (Real.sqrt_pos.mpr hApos).ne'
    have hsAc : Real.sqrt (A n + c₀) ≠ 0 := (Real.sqrt_pos.mpr hAc).ne'
    funext ω
    change (Real.sqrt (A n + c₀) / Real.sqrt (A n)) *
      ((Fheat Z (tau ρ (n + 1)) 0 ω - ∫ ω', Fheat Z (tau ρ (n + 1)) 0 ω' ∂P) /
        Real.sqrt (A n + c₀)) =
      (Fheat Z (tau ρ (n + 1)) 0 ω - ∫ ω', Fheat Z (tau ρ (n + 1)) 0 ω' ∂P) /
        Real.sqrt (A n)
    field_simp [hsA, hsAc]
  have hm (n : ℕ) : AEMeasurable (fun ω =>
      (Fheat Z (tau ρ (n + 1)) 0 ω - ∫ ω', Fheat Z (tau ρ (n + 1)) 0 ω' ∂P) /
        Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ))) P :=
    ((aemeasurable_Fheat ϑ P Z hZ _ (tau_pos hρ _) (tau_lt_one hρ (Nat.zero_lt_succ n)) 0).sub_const _).div_const _
  exact (tendstoInDistribution_congr_of_eventually_map_eq hscaled.forall_aemeasurable hm
    hscaled.aemeasurable_limit (hmatch.mono (fun _ h => congrArg (fun f : Ω → ℝ => P.map f) h))).mp
      hscaled

/-- The centered heat-start logarithms on the geometric grid have the scalar
Gaussian limit with normalization `sqrt (log n)`. -/
theorem scalar_clt_geometric (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (ρ : ℝ) (hρ : 1 < ρ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Fheat Z (tau ρ n) 0 ω -
        ∫ ω', Fheat Z (tau ρ n) 0 ω' ∂P) / Real.sqrt (Real.log (n : ℝ)))
      atTop id (fun _ => P) (gaussianReal 0 1) := by
  have hs := scalar_clt_geometric_succ ϑ P Z hZ ρ hρ
  have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b + 1, fun n hn => by omega⟩
  have hseq : TendstoInDistribution
      (fun (n : ℕ) ω => (Fheat Z (tau ρ (n - 1 + 1)) 0 ω -
        ∫ ω', Fheat Z (tau ρ (n - 1 + 1)) 0 ω' ∂P) /
          Real.sqrt (Real.log ((n - 1 + 1 : ℕ) : ℝ)))
      atTop id (fun _ => P) (gaussianReal 0 1) :=
    ⟨fun n => hs.forall_aemeasurable (n - 1), hs.aemeasurable_limit, hs.tendsto.comp hpred⟩
  have hm (n : ℕ) : AEMeasurable (fun ω => (Fheat Z (tau ρ n) 0 ω -
      ∫ ω', Fheat Z (tau ρ n) 0 ω' ∂P) / Real.sqrt (Real.log (n : ℝ))) P := by
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero, Real.log_zero, Real.sqrt_zero, div_zero]
      exact measurable_const.aemeasurable
    · exact ((aemeasurable_Fheat ϑ P Z hZ _ (tau_pos hρ _)
        (tau_lt_one hρ (Nat.pos_of_ne_zero hn)) 0).sub_const _).div_const _
  have hmap : ∀ᶠ n in atTop,
      P.map (fun ω => (Fheat Z (tau ρ (n - 1 + 1)) 0 ω -
        ∫ ω', Fheat Z (tau ρ (n - 1 + 1)) 0 ω' ∂P) /
          Real.sqrt (Real.log ((n - 1 + 1 : ℕ) : ℝ))) =
      P.map (fun ω => (Fheat Z (tau ρ n) 0 ω -
        ∫ ω', Fheat Z (tau ρ n) 0 ω' ∂P) / Real.sqrt (Real.log (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.sub_add_cancel hn]
  exact (tendstoInDistribution_congr_of_eventually_map_eq hseq.forall_aemeasurable hm
    hseq.aemeasurable_limit hmap).mp hseq

end Critical2DKPZ.Extensions.ScaleLimit
