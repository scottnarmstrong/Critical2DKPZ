/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordContinuumApproximation
public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceWindows
import Mathlib.Tactic

/-! Uniform discrete cutoff errors and continuum cutoff limits imply convergence of the full two-particle entrance integral. -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Uniform discrete exhaustion errors and continuum cutoff limits imply the uncut entrance limit on every positive finite horizon. -/
theorem tendsto_pairTwoTestedEntranceWindow_full_of_cutoff_limits
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (hB : ∀ η : ℕ → C_c(ℝ × Plane, ℝ),
      (∀ k p, η k p ∈ Set.Icc (0 : ℝ) 1) →
      (∀ (k : ℕ) (p : ℝ × Plane), T / ((k : ℝ) + 3) ≤ p.1 →
        p.1 ≤ T - T / ((k : ℝ) + 3) → ‖p.2‖ ≤ k → η k p = 1) →
      ∀ ε > 0, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        |pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (fun _ => 1) -
          pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (η k)| ≤ ε)
    (hC : ∀ η : C_c(ℝ × Plane, ℝ),
      (∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) →
      Tendsto (fun N => pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ η) atTop
        (𝓝 ((1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
          η (p.1, p.2.2.1) *
            ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
              pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1)
                φ ![p.2.1, p.2.2.2] p.2.2.1)
          ∂(volume.restrict (Set.Ioo 0 T)).prod
            ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)))))) :
    Tendsto (fun N => pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (fun _ => 1)) atTop
      (𝓝 ((1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
        (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
          pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1)
            φ ![p.2.1, p.2.2.2] p.2.2.1
        ∂(volume.restrict (Set.Ioo 0 T)).prod
          ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))))) := by
  obtain ⟨η, hrange, hsupport, hplateau, hlim⟩ :=
    exists_pairTwo_continuum_entrance_approximation
      (ϑ - Real.eulerMascheroniConstant) T hT φ
  let μ := ((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
    ((volume : Measure Plane).prod ((volume : Measure Plane).prod (volume : Measure Plane)))
  let F := fun p : ℝ × (Plane × (Plane × Plane)) =>
    (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
      pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1)
        φ ![p.2.1, p.2.2.2] p.2.2.1
  let c : ℝ := (1 / 4 : ℝ) * ∫ p, F p ∂μ
  let ck : ℕ → ℝ := fun k => (1 / 4 : ℝ) * ∫ p, η k (p.1, p.2.2.1) * F p ∂μ
  have hlim' : Tendsto ck atTop (𝓝 c) := hlim
  change Tendsto (fun N => pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (fun _ => 1)) atTop (𝓝 c)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hb := hB η hrange hplateau (ε / 4) hε4
  have hc := (Metric.tendsto_nhds.mp hlim') (ε / 4) hε4
  obtain ⟨k, hkB, hkC⟩ := (hb.and hc).exists
  have hcutlim : Tendsto
      (fun N => pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (η k)) atTop (𝓝 (ck k)) :=
    hC (η k) (hsupport k)
  have hcut := (Metric.tendsto_nhds.mp hcutlim) (ε / 4) hε4
  filter_upwards [hkB, hcut] with N hBN hCN
  have htriangle := dist_triangle4
    (pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (fun _ => 1))
    (pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (η k)) (ck k) c
  simp only [Real.dist_eq] at htriangle hCN hkC ⊢
  linarith only [htriangle, hBN, hCN, hkC, hε]

end Critical2DKPZ.SHF.Moments
