/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Hybrid
public import Critical2DKPZ.SHF.Tsai.NonlinearChainLimits
public import Critical2DKPZ.SHF.Tsai.CouplingIndependence
public import Critical2DKPZ.SHF.Tsai.BlockMomentTransport
public import Critical2DKPZ.SHF.Tsai.BlockMoments

/-! # Limits of the dense-time hybrid expectations

At an interior splice the left and right blocks are independent on the
product coupling. The bounded nonlinear chain-limit theorem gives convergence
and integrability. At either endpoint the hybrid expectation is constant.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Interior hybrid observables are integrable and their expectations converge. -/
theorem exists_hybridPairing_integral_limit {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s c t : ℝ} (hs : s ∈ D) (hc : c ∈ D) (ht : t ∈ D) (hsc : s < c) (hct : c < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : Continuous H) (CH : ℝ) (hCH : ∀ z, ‖H z‖ ≤ CH) :
    ∃ L : ℝ,
      (∀ ℓ, Integrable (fun ω => H (hybridPairing Z Z' s c t (heatMollifier ℓ) g g' ω)) (P'.prod P)) ∧
      Tendsto (fun ℓ => ∫ ω, H (hybridPairing Z Z' s c t (heatMollifier ℓ) g g' ω) ∂P'.prod P)
        atTop (𝓝 L) := by
  classical
  let A (i : Fin 2) (ω : Ω' × Ω) :=
    Fin.cons (α := fun _ : Fin 2 => Measure (Plane × Plane)) (Z' s c ω.1)
      (fun _ => Z c t ω.2) i
  let C (k : ℕ) (ω : Ω' × Ω) := A (Fin.ofNat 2 k) ω
  let τ : ℕ → ℝ := fun k => if k = 0 then c - s else t - c
  have hτ (k : ℕ) (_hk : k ≤ 1) : 0 < τ k := by
    by_cases hk0 : k = 0
    · simpa only [τ, ite_eq_left hk0] using sub_pos.mpr hsc
    · simpa only [τ, ite_eq_right hk0] using sub_pos.mpr hct
  have hC (k : ℕ) (hk : k ≤ 1) : HasDeltaBoseMoments θ (τ k) (P'.prod P) (C k) := by
    interval_cases k
    · exact (hZ'.hasDeltaBoseMoments hs hc hsc).comp_measurePreserving measurePreserving_fst
    · exact (hZ.hasDeltaBoseMoments hc ht hct).comp_measurePreserving measurePreserving_snd
  have hind1 : iIndepFun (fun _ : Fin 1 => Z c t) P := iIndepFun.of_subsingleton
  have hindA : iIndepFun A (P'.prod P) :=
    iIndepFun_fin_cons_prod P P' (Z' s c) (fun _ : Fin 1 => Z c t)
      (hZ'.1 s hs c hc hsc).1 (fun _ => (hZ.1 c hc t ht hct).1) hind1
  have hindC : iIndepFun (fun k : Fin (1 + 1) => C k) (P'.prod P) := by
    simpa only [C, Fin.ofNat_eq_cast, Fin.cast_val_eq_self] using hindA
  have hg (a b) : MemLp (g a b) 2 :=
    (g a b).continuous.memLp_of_hasCompactSupport (g a b).hasCompactSupport
  have hg' (a b) : MemLp (g' a b) 2 :=
    (g' a b).continuous.memLp_of_hasCompactSupport (g' a b).hasCompactSupport
  have h := exists_integral_comp_chainPairings_limit (P'.prod P) 1 τ hτ C hC hindC
    (fun _ => heatMollifier) (fun _ => isL2ApplicableMollifier_heatMollifier)
    (fun a b => g a b) (fun a b => g' a b) hg hg' H hH CH hCH
  exact h

/-- Hybrid values converge at every splice in the closed interval, including both endpoints. -/
theorem exists_hybridValue_limit {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s c t : ℝ} (hs : s ∈ D) (hc : c ∈ D) (ht : t ∈ D)
    (hsc : s ≤ c) (hct : c ≤ t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : Continuous H) (CH : ℝ) (hCH : ∀ z, ‖H z‖ ≤ CH) :
    ∃ L : ℝ, Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H c ℓ) atTop (𝓝 L) := by
  by_cases hcs : c = s
  · subst c
    simp only [hybridValue, ite_true]
    exact ⟨_, tendsto_const_nhds⟩
  by_cases hct' : c = t
  · subst c
    simp only [hybridValue, ite_eq_right hcs, ite_true]
    exact ⟨_, tendsto_const_nhds⟩
  have hsc' : s < c := lt_of_le_of_ne hsc (Ne.symm hcs)
  have hct'' : c < t := lt_of_le_of_ne hct hct'
  obtain ⟨L, _hI, hL⟩ := exists_hybridPairing_integral_limit D P P' Z Z' hZ hZ' hs hc ht
    hsc' hct'' g g' H hH CH hCH
  exact ⟨L, by simpa only [hybridValue, ite_eq_right hcs, ite_eq_right hct'] using hL⟩

end Critical2DKPZ.SHF.Tsai

end
