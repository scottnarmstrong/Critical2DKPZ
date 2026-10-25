/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainSwap
public import Critical2DKPZ.SHF.Tsai.CenteredFourthLimits
public import Critical2DKPZ.SHF.Tsai.CouplingIndependence
import Critical2DKPZ.SHF.Tsai.BlockMomentTransport
import Critical2DKPZ.SHF.Tsai.HeatMollifier
import Critical2DKPZ.SHF.Tsai.ChainNonlinearIntegrability

/-! # Replacement of a whole interval

When the replaced interval has no prefix or suffix, the zero-connector Taylor
bound is controlled by the actual centered fourth moment of its single block.
The product probability coupling preserves the two original expectations.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Two moment blocks with the same time parameter obey the whole-interval Taylor comparison, with remainder integrability. -/
theorem integrable_and_abs_integral_block_swap_le {θ τ : ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (A : Ω → Measure (Plane × Plane)) (A' : Ω' → Measure (Plane × Plane))
    (hA : HasDeltaBoseMoments θ τ P A) (hA' : HasDeltaBoseMoments θ τ P' A') (hτ : 0 < τ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ i k, MemLp (g i k) 2) (hg' : ∀ i k, MemLp (g' i k) 2)
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    Integrable (fun ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω)) P ∧
    Integrable (fun ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A' ω)) P' ∧
    Integrable (fun ω => ∑ i, ((∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω) -
      ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂heatBlock τ) ^ 4) P ∧
    |(∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω) ∂P) -
      ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A' ω) ∂P'| ≤
      CH / 12 * ∫ ω, ∑ i, ((∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω) -
        ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂heatBlock τ) ^ 4 ∂P := by
  classical
  let B (_k : ℕ) (ω : Ω' × Ω) := A ω.2
  let R (ω : Ω' × Ω) := A' ω.1
  have hB (k : ℕ) (_ : k ≤ 0) : HasDeltaBoseMoments θ τ (P'.prod P) (B k) :=
    hA.comp_measurePreserving measurePreserving_snd
  have hR : HasDeltaBoseMoments θ τ (P'.prod P) R :=
    hA'.comp_measurePreserving measurePreserving_fst
  have hind1 : iIndepFun (fun _ : Fin 1 => A) P := iIndepFun.of_subsingleton
  have hind : iIndepFun (fun k : Fin 2 => if (k : ℕ) ≤ 0 then B k else R) (P'.prod P) := by
    have h := iIndepFun_fin_snoc_prod P P' A' (fun _ : Fin 1 => A) hA'.1 (fun _ => hA.1) hind1
    have heq : (fun i : Fin 2 => fun ω : Ω' × Ω =>
        Fin.snoc (α := fun _ : Fin 2 => Measure (Plane × Plane)) (fun _ => A ω.2) (A' ω.1) i) =
        (fun k : Fin 2 => if (k : ℕ) ≤ 0 then B k else R) := by
      funext k ω
      fin_cases k <;> rfl
    rwa [heq] at h
  obtain ⟨_M, _hM, hLimit⟩ := exists_integral_sum_centeredChainPairings_four_limit 0 0 le_rfl
    (fun _ => τ) (fun _ _ => hτ) (fun _ => A) (fun _ _ => hA) hind1 g g' hg hg'
  have hI := (hLimit (fun _ => heatMollifier) (fun _ => isL2ApplicableMollifier_heatMollifier)).1 0
  have hbound := (abs_integral_comp_chain_swap_le 0 0 le_rfl (fun _ => τ) (fun _ _ => hτ)
    B R hB hR hind (fun _ => heatMollifier 0)
    (fun _ => ⟨heatMollifier, isL2ApplicableMollifier_heatMollifier, 0, rfl⟩)
    g g' hg hg' H hH CH hCH).2
  simp only [chainProduct, Function.update_self] at hI hbound
  have hOrig : (∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω.2) ∂P'.prod P) =
      ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω) ∂P := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_fun_snd (μ := P') (ν := P) (fun ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω))
  have hRep : (∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A' ω.1) ∂P'.prod P) =
      ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A' ω) ∂P' := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_fun_fst (μ := P') (ν := P) (fun ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A' ω))
  have hMoment : (∫ ω : Ω' × Ω, ∑ i, ((∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω.2) -
      ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂heatBlock τ) ^ 4 ∂P'.prod P) =
      ∫ ω, ∑ i, ((∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω) -
        ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂heatBlock τ) ^ 4 ∂P := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_fun_snd (μ := P') (ν := P) (fun ω => ∑ i,
        ((∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂A ω) -
          ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂heatBlock τ) ^ 4)
  have hH0 (z) : ‖H z‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) z
  have hind1' : iIndepFun (fun _ : Fin 1 => A') P' := iIndepFun.of_subsingleton
  have hIA := integrable_comp_chainPairings P 0 (fun _ => τ) (fun _ _ => hτ)
    (fun _ => A) (fun _ _ => hA) hind1 (fun _ => heatMollifier)
    (fun _ => isL2ApplicableMollifier_heatMollifier) 0 g g' hg hg' H hH.continuous CH hH0
  have hIA' := integrable_comp_chainPairings P' 0 (fun _ => τ) (fun _ _ => hτ)
    (fun _ => A') (fun _ _ => hA') hind1' (fun _ => heatMollifier)
    (fun _ => isL2ApplicableMollifier_heatMollifier) 0 g g' hg hg' H hH.continuous CH hH0
  simpa only [chainProduct, B, R, hOrig, hRep, hMoment] using
    And.intro hIA (And.intro hIA' (And.intro hI hbound))

end Critical2DKPZ.SHF.Tsai

end
