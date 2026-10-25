/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabAdjacentMomentLimit
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Tactic

/-! Compact tests varying with the lattice scale admit two-block moment limits. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai Critical2DKPZ.DeltaBose
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- Uniformly converging measurable tests on one common compact window may
vary with the lattice scale in the two-block compact moment limit. -/
theorem tendsto_slabTwoBlockCompactIntegral_varying_with_integrability (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (F : C_c((Fin 4 → Plane × Plane), ℝ))
    (H : ℕ → (Fin 4 → Plane × Plane) → ℝ) (hH : ∀ N, Measurable (H N))
    (K : Set (Plane × Plane)) (hK : IsCompact K)
    (hFs : Function.support F ⊆ Set.univ.pi fun _ => K)
    (hHs : ∀ N, Function.support (H N) ⊆ Set.univ.pi fun _ => K)
    (hUniform : ∀ δ > 0, ∀ᶠ N : ℕ in atTop, ∀ q, |H N q - F q| ≤ δ) :
    Tendsto
      (fun N => ∫ ω, ∫ q, H N q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N r u ω)) ∂disorderLaw) atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F)) ∧
      ∀ᶠ N : ℕ in atTop, Integrable (fun ω => ∫ q, H N q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N r u ω))) disorderLaw := by
  classical
  obtain ⟨g, g', hg, hg', hone⟩ := exists_compactTensor_majorant K hK
  let ρ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  let Tψ : C_c((Fin 4 → Plane × Plane), ℝ) := slabCompactPiTensorTest (fun _ => ρ)
  let πN : ℕ → Disorder → Measure (Fin 4 → Plane × Plane) := fun N ω =>
    slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω) (polymerMeasure ϑ N r u ω)
  let M : ℕ → Disorder → ℝ := fun N ω =>
    (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
      (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) ^ 2
  have hMass : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (M N) disorderLaw ∧ ∫ ω, M N ω ∂disorderLaw ≤ C := by
    rcases lt_or_eq_of_le htr with hgap | heq
    · exact eventually_slabSeparatedTensorMass_sq_bound ϑ hFlatSixthMomentInput hs hst hgap hru g g' hg hg'
    · subst r
      exact eventually_slabAdjacentTensorMass_sq_bound ϑ hFlatSixthMomentInput hs hst hru g g' hg hg'
  obtain ⟨C, hC, hMass⟩ := hMass
  have hSigma (N : ℕ) (ω : Disorder) :
      SigmaFinite (polymerMeasure ϑ N s t ω) ∧ SigmaFinite (polymerMeasure ϑ N r u ω) := by
    exact ⟨@MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N s t ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω),
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N r u ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N r u ω)⟩
  have hLF (N : ℕ) (ω : Disorder) : IsLocallyFiniteMeasure (πN N ω) := by
    obtain ⟨hμ, hν⟩ := hSigma N ω
    exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
      (Fin 4) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
      (fun i => if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N r u ω)
      (by intro i; split_ifs <;> assumption) (fun _ => inferInstance)
      (by intro i; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  have hπMeas (N : ℕ) : Measurable (πN N) := by
    exact measurable_piMeasure_of_locallyFinite 4
      (fun i ω => if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N r u ω)
      (by intro i; split_ifs <;> exact measurable_polymerMeasure ϑ N _ _)
      (by intro i ω; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  have hImeas (N : ℕ) (f : (Fin 4 → Plane × Plane) → ℝ) (hf : Measurable f) :
      Measurable (fun ω => ∫ q, f q ∂πN N ω) := by
    let κ : Kernel Disorder (Fin 4 → Plane × Plane) := ⟨πN N, hπMeas N⟩
    exact (hf.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hTnonneg (q : Fin 4 → Plane × Plane) : 0 ≤ Tψ q := by
    simp only [Tψ, slabCompactPiTensorTest_apply, ρ, compactTensorTest_apply]
    exact Finset.prod_nonneg fun i _ => mul_nonneg (hg _) (hg' _)
  have hTone (q : Fin 4 → Plane × Plane) (hq : q ∈ Set.univ.pi fun _ => K) : Tψ q = 1 := by
    simp only [Tψ, slabCompactPiTensorTest_apply, ρ, compactTensorTest_apply]
    exact Finset.prod_eq_one fun i _ => hone (q i) ((Set.mem_univ_pi.mp hq) i)
  have hTint (N : ℕ) (ω : Disorder) : Integrable (fun q => Tψ q) (πN N ω) :=
    integrable_compactTest_of_locallyFinite _ (hLF N ω) Tψ
  have hTmass (N : ℕ) (ω : Disorder) : (∫ q, Tψ q ∂πN N ω) = M N ω := by
    obtain ⟨hμ, hν⟩ := hSigma N ω
    have h := integral_slabCompactPiTensorTest_twoBlock hμ hν (fun _ => ρ)
    simpa [Tψ, πN, M, ρ, compactTensorTest_apply] using h
  have hFint (N : ℕ) (ω : Disorder) : Integrable (fun q => F q) (πN N ω) :=
    integrable_compactTest_of_locallyFinite _ (hLF N ω) F
  obtain ⟨B, hB⟩ := F.continuous.bounded_above_of_compact_support F.hasCompactSupport
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hFpoint (q : Fin 4 → Plane × Plane) : ‖F q‖ ≤ B * Tψ q := by
    by_cases hq : q ∈ Set.univ.pi fun _ => K
    · rw [hTone q hq, mul_one]; exact hB q
    · have hz : F q = 0 := Function.notMem_support.mp (fun h => hq (hFs h))
      rw [hz, norm_zero]
      exact mul_nonneg hB0 (hTnonneg q)
  have hFouter : ∀ᶠ N : ℕ in atTop, Integrable (fun ω => ∫ q, F q ∂πN N ω) disorderLaw := by
    filter_upwards [hMass] with N hMN
    apply (hMN.1.const_mul B).mono' (hImeas N F F.measurable).aestronglyMeasurable
    filter_upwards [] with ω
    have h := norm_integral_le_of_norm_le ((hTint N ω).const_mul B) (Eventually.of_forall hFpoint)
    simpa only [integral_const_mul, hTmass] using h
  have hApprox (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => ∫ q, H N q ∂πN N ω) disorderLaw ∧
      |(∫ ω, ∫ q, H N q ∂πN N ω ∂disorderLaw) -
        (∫ ω, ∫ q, F q ∂πN N ω ∂disorderLaw)| ≤ δ * C := by
    filter_upwards [hMass, hFouter, hUniform δ hδ] with N hMN hFN hUN
    have hpoint (q : Fin 4 → Plane × Plane) : ‖H N q - F q‖ ≤ δ * Tψ q := by
      by_cases hq : q ∈ Set.univ.pi fun _ => K
      · rw [hTone q hq, mul_one, Real.norm_eq_abs]; exact hUN q
      · have hHz : H N q = 0 := Function.notMem_support.mp (fun h => hq (hHs N h))
        have hFz : F q = 0 := Function.notMem_support.mp (fun h => hq (hFs h))
        rw [hHz, hFz, sub_self, norm_zero]
        exact mul_nonneg hδ.le (hTnonneg q)
    have hDiffInt (ω : Disorder) : Integrable (fun q => H N q - F q) (πN N ω) :=
      ((hTint N ω).const_mul δ).mono'
        ((hH N).sub F.measurable).aestronglyMeasurable (Eventually.of_forall hpoint)
    have hHInt (ω : Disorder) : Integrable (H N) (πN N ω) :=
      ((hDiffInt ω).add (hFint N ω)).congr (Eventually.of_forall fun q => sub_add_cancel _ _)
    have hInner (ω : Disorder) :
        ‖(∫ q, H N q ∂πN N ω) - ∫ q, F q ∂πN N ω‖ ≤ δ * M N ω := by
      rw [← integral_sub (hHInt ω) (hFint N ω)]
      have h := norm_integral_le_of_norm_le ((hTint N ω).const_mul δ) (Eventually.of_forall hpoint)
      simpa only [integral_const_mul, hTmass] using h
    have hOuterDiff : Integrable
        (fun ω => (∫ q, H N q ∂πN N ω) - ∫ q, F q ∂πN N ω) disorderLaw :=
      (hMN.1.const_mul δ).mono'
        ((hImeas N (H N) (hH N)).sub (hImeas N F F.measurable)).aestronglyMeasurable
        (Eventually.of_forall hInner)
    have hOuterH : Integrable (fun ω => ∫ q, H N q ∂πN N ω) disorderLaw :=
      (hOuterDiff.add hFN).congr (Eventually.of_forall fun ω => sub_add_cancel _ _)
    refine ⟨hOuterH, ?_⟩
    rw [← integral_sub hOuterH hFN]
    have h := norm_integral_le_of_norm_le (hMN.1.const_mul δ) (Eventually.of_forall hInner)
    rw [Real.norm_eq_abs, integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hMN.2 hδ.le)
  have hFixed : Tendsto (fun N => ∫ ω, ∫ q, F q ∂πN N ω ∂disorderLaw) atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F)) := by
    rcases lt_or_eq_of_le htr with hgap | heq
    · exact tendsto_slabSeparatedCompactIntegral ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hgap hru F
    · subst r
      exact tendsto_slabAdjacentCompactIntegral ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hru F
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ : ℝ := ε / (2 * (C + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hδC : δ * C < ε / 2 := by
      have heq : δ * (2 * (C + 1)) = ε := by dsimp [δ]; field_simp
      nlinarith only [hδ, heq]
    have hfixed := (Metric.tendsto_nhds.mp hFixed) (ε / 2) (half_pos hε)
    filter_upwards [hApprox δ hδ, hfixed] with N hAN hFN
    rw [Real.dist_eq] at hFN ⊢
    exact (abs_sub_le _ _ _).trans_lt (by linarith only [hAN.2, hFN, hδC])
  · filter_upwards [hApprox 1 one_pos] with N hN
    exact hN.1


end Critical2DKPZ.SHF.Flow

end
