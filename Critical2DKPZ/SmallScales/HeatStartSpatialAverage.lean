/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.HeatStartMoments
public import Critical2DKPZ.SmallScales.HeatStartLogCLT
public import Critical2DKPZ.SmallScales.SpatialAverageL2
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.Assembly.RegularizedInvariance

/-! # Centered heat-start averages inherit the variance bound -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.LocalSobolev
open Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction CompactlySupported Distributions Topology

universe u

namespace Critical2DKPZ.SmallScales

private theorem heatStartLog_identDistrib_of_symmetries (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (hδ : 0 < δ) (x : Plane) :
    IdentDistrib (heatStartLog Z s t δ x) (heatStartLog Z s t δ 0) P P := by
  let Zshift : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun a b ω =>
    (Z a b ω).map fun p => (p.1 + -x, p.2 + -x)
  have hZshift : IsCriticalSHF ϑ P Zshift := by
    simpa only [Zshift] using hsym.1 (-x)
  let hbase := Critical2DKPZ.SHF.Positivity.isCriticalSHF_heat_bounded_pairing
    ϑ P Z hZ hs hst hδ 0
    (1 : Plane →ᵇ ℝ)
  let htranslated := Critical2DKPZ.SHF.Positivity.isCriticalSHF_heat_bounded_pairing
    ϑ P Zshift hZshift hs hst hδ 0
    (1 : Plane →ᵇ ℝ)
  let Y0 : Ω → ℝ := fun ω =>
    shfPairing Z s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω
  let Yx : Ω → ℝ := fun ω =>
    shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
  let Yshift : Ω → ℝ := fun ω =>
    shfPairing Zshift s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω
  have hpair (ω : Ω) : Yshift ω = Yx ω := by
    have h := Critical2DKPZ.Assembly.shfPairing_compAffine Z s t (-x)
      (LinearIsometryEquiv.refl ℝ Plane) (fun y => heatKernel δ (y - 0))
      (fun _ => 1) ω
    have hZmap :
        (fun p : Plane × Plane =>
          (-x + (LinearIsometryEquiv.refl ℝ Plane) p.1,
            -x + (LinearIsometryEquiv.refl ℝ Plane) p.2)) =
          (fun p => (p.1 + -x, p.2 + -x)) := by
      funext p
      apply Prod.ext
      · change -x + p.1 = p.1 + -x
        abel
      · change -x + p.2 = p.2 + -x
        abel
    have hkernel :
        (fun y : Plane => heatKernel δ
          (-x + (LinearIsometryEquiv.refl ℝ Plane) y - 0)) =
          (fun y => heatKernel δ (y - x)) := by
      funext y
      congr 1
      change -x + y - 0 = y - x
      abel
    change shfPairing (fun a b ω => (Z a b ω).map (fun p => (p.1 + -x, p.2 + -x)))
      s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω = _
    rw [← hZmap]
    rw [hkernel] at h
    simpa only [sub_zero] using h
  have htranslated' := htranslated.2.2.2.congr
    (fun _ => Filter.EventuallyEq.rfl)
    (Filter.Eventually.of_forall hpair)
  have hmap : P.map Y0 = P.map Yx := by
    have hlim := tendsto_nhds_unique hbase.2.2.2.tendsto htranslated'.tendsto
    exact congrArg ProbabilityMeasure.toMeasure hlim
  have hYxInt : Integrable Yx P := by
    have hae : Yshift =ᵐ[P] Yx := Filter.Eventually.of_forall hpair
    exact htranslated.2.1.congr hae
  have hPairIdent : IdentDistrib Yx Y0 P P :=
    ⟨hYxInt.aemeasurable, hbase.2.1.aemeasurable, hmap.symm⟩
  change IdentDistrib (fun ω => Real.log
    (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω))
    (fun ω => Real.log
      (shfPairing Z s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω)) P P
  exact hPairIdent.comp Real.measurable_log

/-- A nonnegative unit-mass spatial average of centered heat-start logarithms has second moment
bounded by the pointwise variance bound. -/
theorem heatStartLog_centered_average_memLp_and_sq_le
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z)
    {τ₀ τ₁ s T δ C δM : ℝ} (hτ₀ : 0 < τ₀)
    (hmoment : ∀ s' T' δ' : ℝ, 0 ≤ s' → τ₀ ≤ T' - s' → T' - s' ≤ τ₁ →
      0 < δ' → δ' ≤ δM → ∀ y : Plane,
        MemLp (heatStartLog Z s' T' δ' y) 2 P ∧
          0 ≤ -∫ ω, heatStartLog Z s' T' δ' y ω ∂P ∧
          Var[heatStartLog Z s' T' δ' y; P] ≤
            -2 * ∫ ω, heatStartLog Z s' T' δ' y ω ∂P ∧
          -2 * ∫ ω, heatStartLog Z s' T' δ' y ω ∂P ≤ Real.log (Real.log δ'⁻¹) + C)
    (hs : 0 ≤ s)
    (hτlo : τ₀ ≤ T - s) (hτhi : T - s ≤ τ₁)
    (hδ : 0 < δ) (hδle : δ ≤ δM)
    (hδlog : δ ≤ Real.exp (-Real.exp (-C)))
    (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y) (hφ₁ : ∫ y, φ y = 1) :
    MemLp (fun ω => ∫ y, φ y *
        (heatStartLog Z s T δ y ω - ∫ ω', heatStartLog Z s T δ 0 ω' ∂P)) 2 P ∧
      ∫ ω, |∫ y, φ y *
        (heatStartLog Z s T δ y ω - ∫ ω', heatStartLog Z s T δ 0 ω' ∂P)| ^ 2 ∂P ≤
        Real.log (Real.log δ⁻¹) + C := by
  have hst : s < T := by linarith [hτlo]
  have hdelta : δ ≤ δM := hδle
  let m : ℝ := ∫ ω, heatStartLog Z s T δ 0 ω ∂P
  let F : Plane × Ω → ℝ := fun q => heatStartLog Z s T δ q.1 q.2 - m
  have hFjoint : AEMeasurable F (volume.prod P) := by
    let μ : Ω → Measure (Plane × Plane) := Z s T
    have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
      filter_upwards [hZ.2.1 s T hs hst] with ω hω
      exact hω.1
    have h := Critical2DKPZ.JointConvergence.aemeasurable_log_heatPairing_joint P μ
      (hZ.1 s T hs hst) hlocal δ hδ (fun _ : Plane => (1 : ℝ))
      measurable_const (fun _ => by norm_num)
    have hlog : AEMeasurable (fun q : Plane × Ω => heatStartLog Z s T δ q.1 q.2)
        (volume.prod P) := by
      simpa only [μ, heatStartLog, shfPairing, mul_one] using h
    exact hlog.sub aemeasurable_const
  have hFsec (y : Plane) : AEStronglyMeasurable (fun ω => F (y, ω)) P := by
    have hlogpkg := hsym.2.2.2.2.2.2 s T δ y (0 : Plane →ᵇ ℝ) hs hst hδ
    have hlogId : (fun ω => Real.log (shfPairing Z s T
        (fun z => heatKernel δ (z - y)) (fun _ => Real.exp (0 : ℝ)) ω)) =ᵐ[P]
        heatStartLog Z s T δ y := by
      filter_upwards [] with ω
      simp [heatStartLog, shfPairing]
    have hLmeas : AEMeasurable (heatStartLog Z s T δ y) P := by
      exact hlogpkg.2.1.congr hlogId
    change AEStronglyMeasurable (fun ω => heatStartLog Z s T δ y ω - m) P
    exact hLmeas.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hMom (y : Plane) :
      MemLp (heatStartLog Z s T δ y) 2 P ∧
        0 ≤ -∫ ω, heatStartLog Z s T δ y ω ∂P ∧
        Var[heatStartLog Z s T δ y; P] ≤ -2 * ∫ ω, heatStartLog Z s T δ y ω ∂P ∧
        -2 * ∫ ω, heatStartLog Z s T δ y ω ∂P ≤ Real.log (Real.log δ⁻¹) + C :=
    hmoment s T δ hs hτlo hτhi hδ hdelta y
  have hmean (y : Plane) : ∫ ω, heatStartLog Z s T δ y ω ∂P = m := by
    dsimp [m]
    exact (heatStartLog_identDistrib_of_symmetries ϑ P Z hZ hsym hs hst hδ y).integral_eq
  have hSq (y : Plane) : Integrable (fun ω => |F (y, ω)| ^ 2) P ∧
      ∫ ω, |F (y, ω)| ^ 2 ∂P ≤ Real.log (Real.log δ⁻¹) + C := by
    have hFmem : MemLp (fun ω => heatStartLog Z s T δ y ω - m) 2 P := by
      change MemLp (heatStartLog Z s T δ y - fun _ : Ω => m) 2 P
      exact (hMom y).1.sub (memLp_const m)
    have hFsq := (memLp_two_iff_integrable_sq
      ((hMom y).1.aestronglyMeasurable.sub aestronglyMeasurable_const)).1 hFmem
    have hvar : ∫ ω, |F (y, ω)| ^ 2 ∂P = Var[heatStartLog Z s T δ y; P] := by
      have h := (variance_eq_integral ((hMom y).1.aemeasurable))
      rw [hmean y] at h
      simpa [F, m, sq_abs] using h.symm
    refine ⟨?_, ?_⟩
    · simpa [sq_abs] using hFsq
    · rw [hvar]
      calc
        Var[heatStartLog Z s T δ y; P] ≤ -2 * ∫ ω, heatStartLog Z s T δ y ω ∂P :=
          (hMom y).2.2.1
        _ ≤ Real.log (Real.log δ⁻¹) + C := (hMom y).2.2.2
  have hMnonneg : 0 ≤ Real.log (Real.log δ⁻¹) + C := by
    have hδlog' : Real.exp (-C) ≤ Real.log δ⁻¹ := by
      have hlog : Real.log δ ≤ -Real.exp (-C) := by
        calc
          Real.log δ ≤ Real.log (Real.exp (-Real.exp (-C))) := Real.log_le_log hδ hδlog
          _ = -Real.exp (-C) := Real.log_exp _
      rw [Real.log_inv]
      linarith
    have hpos : 0 < Real.log δ⁻¹ := lt_of_lt_of_le (Real.exp_pos _) hδlog'
    have hloglog : -C ≤ Real.log (Real.log δ⁻¹) := by
      calc
        -C = Real.log (Real.exp (-C)) := (Real.log_exp _).symm
        _ ≤ Real.log (Real.log δ⁻¹) := Real.log_le_log (Real.exp_pos _) hδlog'
    linarith
  exact integral_test_second_moment_le_of_uniform_square P hFjoint hFsec hMnonneg hSq φ hφ hφ₁

end Critical2DKPZ.SmallScales

end
