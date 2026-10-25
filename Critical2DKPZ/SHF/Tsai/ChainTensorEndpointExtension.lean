/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TensorEndpointDensity
public import Critical2DKPZ.SHF.Tsai.ChainEndpointApproximation

/-! # Extension of chain limits to `L²` endpoint tensors

Uniform second-moment bounds for endpoint differences extend convergence in probability
from compact tensor tests to all `L²` endpoint representatives.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Compact tensor convergence for a chain extends to all L² endpoint representatives. -/
theorem tendstoInMeasure_chain_tensor_of_compact {θ ρ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    (C : Ω → Measure (Plane × Plane)) (hC : HasDeltaBoseMoments θ ρ P C) (hρ : 0 < ρ)
    (hconv : ∀ g g' : C_c(Plane, ℝ),
      TendstoInMeasure P (fun n ω => ∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k n) K) atTop
          (fun ω => ∫ p, g p.1 * g' p.2 ∂C ω))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    TendstoInMeasure P (fun n ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k n) K) atTop
        (fun ω => ∫ p, g p.1 * g' p.2 ∂C ω) := by
  obtain ⟨CL, _hCL, hCL⟩ := exists_chainPairing_sub_left_sq_bound K τ hτ B hB hind w hw
  obtain ⟨CR, _hCR, hCR⟩ := exists_chainPairing_sub_right_sq_bound K τ hτ B hB hind w hw
  have hindC : iIndepFun (fun _ : Fin 1 => C) P := iIndepFun.of_subsingleton
  obtain ⟨DL, _hDL, hDL⟩ := exists_chainPairing_sub_left_sq_bound 0 (fun _ => ρ)
    (fun _ _ => hρ) (fun _ => C) (fun _ _ => hC) hindC w hw
  obtain ⟨DR, _hDR, hDR⟩ := exists_chainPairing_sub_right_sq_bound 0 (fun _ => ρ)
    (fun _ _ => hρ) (fun _ => C) (fun _ _ => hC) hindC w hw
  apply tendstoInMeasure_of_compact_tensor_endpoints P
    (fun f h n ω => ∫ p, f p.1 * h p.2 ∂chainProduct (fun k => B k ω) (fun k => w k n) K)
    (fun f h ω => ∫ p, f p.1 * h p.2 ∂C ω) CL CR DL DR
    (fun f h f' hf hh hf' n => hCL n f h f' hf hh hf')
    (fun f f' h' hf hf' hh' n => hCR n f f' h' hf hf' hh')
    (fun f h f' hf hh hf' => ?_) (fun f f' h' hf hf' hh' => ?_) hconv g g' hg hg'
  · simpa only [chainProduct] using hDL 0 f h f' hf hh hf'
  · simpa only [chainProduct] using hDR 0 f f' h' hf hf' hh'

end Critical2DKPZ.SHF.Tsai

end
