/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.CommonSubsequence
public import Critical2DKPZ.SHF.Limit.Equiv
public import Critical2DKPZ.SHF.Tsai.Defs
import Mathlib.Order.Filter.AtTopBot.Finite

/-! # The common process is a critical SHF limit -/

@[expose] public section

open MeasureTheory Filter
open scoped CompactlySupported Topology
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai

noncomputable section

namespace Critical2DKPZ.SHF.Existence

private theorem aemeasurable_polymerMeasure_compact_pairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (f : C_c(Plane × Plane, ℝ)) :
    AEMeasurable (fun ω => ∫ p, f p ∂(polymerMeasure ϑ N s t ω)) disorderLaw := by
  have hpair := SHF.Moments.integrable_pairing_rescaledP2P ϑ N s t
    f.continuous f.hasCompactSupport
  have hmeas0 := hpair.swap.aestronglyMeasurable.integral_prod_right'.aemeasurable
  have hmeas : AEMeasurable (fun ω =>
      ∫ p, f p * rescaledP2P ϑ N s t p ω ∂(volume : Measure (Plane × Plane)))
      disorderLaw := by
    change AEMeasurable (fun ω =>
      ∫ p, (f : Plane × Plane → ℝ) p * rescaledP2P ϑ N s t p ω) disorderLaw at hmeas0
    exact hmeas0
  have hEq : (fun ω => ∫ p, f p ∂(polymerMeasure ϑ N s t ω)) =ᵐ[disorderLaw]
      (fun ω => ∫ p, f p * rescaledP2P ϑ N s t p ω) :=
    Filter.Eventually.of_forall fun ω => integral_polymerMeasure ϑ N s t ω f
  exact hmeas.congr hEq.symm

private theorem aemeasurable_polymerMeasure_first_marginal_pairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (f : C_c(Plane, ℝ)) :
    AEMeasurable (fun ω => ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst))
      disorderLaw := by
  by_cases hN0 : N = 0
  · subst N
    have hzero (ω : Disorder) : polymerMeasure ϑ 0 s t ω = 0 := by
      rw [polymerMeasure]
      ext A hA
      simp [rescaledP2P]
    have hEq : (fun ω =>
        ∫ x, f x ∂((polymerMeasure ϑ 0 s t ω).map Prod.fst)) =ᵐ[disorderLaw]
        fun _ => (0 : ℝ) := by
      filter_upwards [] with ω
      rw [hzero]
      simp
    exact aemeasurable_const.congr hEq.symm
  · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hmeas := aemeasurable_rescaledP2Plane_pairing ϑ N s t f
    have hEq : (fun ω => ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) =ᵐ[
        disorderLaw] fun ω => ∫ x, f x * rescaledP2Plane ϑ N s t x ω :=
      Filter.Eventually.of_forall fun ω => integral_map_fst_polymerMeasure ϑ hN s t ω f
    exact hmeas.congr hEq.symm

private theorem aemeasurable_polymerMeasure_pair_and_marginal_integrals (ϑ : ℝ) (N k : ℕ)
    (s t : Fin k → ℝ) (φ : Fin k → C_c(Plane × Plane, ℝ))
    (χ : Fin k → C_c(Plane, ℝ)) :
    AEMeasurable (fun ω i =>
      ((∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)),
       (∫ x, χ i x ∂((polymerMeasure ϑ N (s i) (t i) ω).map Prod.fst)))) disorderLaw := by
  apply aemeasurable_pi_iff.mpr
  intro i
  exact (aemeasurable_polymerMeasure_compact_pairing ϑ N (s i) (t i) (φ i)).prodMk
    (aemeasurable_polymerMeasure_first_marginal_pairing ϑ N (s i) (t i) (χ i))

local instance projectiveSHFPairingProbabilityMeasureTopology (k : ℕ) :
    TopologicalSpace { μ : Measure (Fin k → ℝ × ℝ) // IsProbabilityMeasure μ } :=
  ProbabilityMeasure.instTopologicalSpace

/-- The common process has the required full-sequence convergence of compact
and flat finite-dimensional pairings. -/
theorem projectiveSHFCommonProcess_pairings_tendsto (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant))
    {μ : Measure (SHFTimePair → SHFPairRadonMeasure)} [IsProbabilityMeasure μ]
    (hProjective : IsProjectiveLimit (α := fun _ : SHFTimePair => SHFPairRadonMeasure) μ
      (projectiveSHFFamily ϑ))
    (k : ℕ) (s t : Fin k → ℝ) (hTimes : ∀ i, 0 ≤ s i ∧ s i < t i)
    (φ : Fin k → C_c(Plane × Plane, ℝ)) (χ : Fin k → C_c(Plane, ℝ)) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
        ((∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)),
         (∫ x, χ i x ∂((polymerMeasure ϑ N (s i) (t i) ω).map Prod.fst))))
      atTop
      (fun ω i =>
        ((∫ p, φ i p ∂(projectiveSHFCommonProcess (s i) (t i) ω)),
         (∫ x, χ i x ∂((projectiveSHFCommonProcess (s i) (t i) ω).map Prod.fst))))
      (fun _ => disorderLaw) μ := by
  classical
  obtain ⟨B, hB, D, hD, hDB, hdense, htimesD⟩ :=
    exists_countable_dense_interval_with_finite_times s t hTimes
  have hD0 : ∀ r ∈ D, 0 ≤ r := fun r hr => (hDB hr).1
  let sourceReadout : ℕ → Disorder → Fin k → ℝ × ℝ := fun N ω i =>
    ((∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)),
     (∫ x, χ i x ∂((polymerMeasure ϑ N (s i) (t i) ω).map Prod.fst)))
  let limitReadout : (SHFTimePair → SHFPairRadonMeasure) → Fin k → ℝ × ℝ := fun ω i =>
    ((∫ p, φ i p ∂(projectiveSHFCommonProcess (s i) (t i) ω)),
     (∫ x, χ i x ∂((projectiveSHFCommonProcess (s i) (t i) ω).map Prod.fst)))
  have hsource : ∀ N, AEMeasurable (sourceReadout N) disorderLaw := by
    intro N
    exact aemeasurable_polymerMeasure_pair_and_marginal_integrals ϑ N k s t φ χ
  obtain ⟨ψ₀, hψ₀, Ω₀, mΩ₀, P₀, hP₀, Z₀, hZ₀⟩ :=
    exists_polymerSubseqLimit ϑ D hD hD0 (fun n => n) strictMono_id
  let η₀ := (fun n => n) ∘ ψ₀
  have hη₀ : StrictMono η₀ := strictMono_id.comp hψ₀
  have hCommon₀ := @projectiveSHFCommonProcess_isPolymerSubseqLimit ϑ hDenseSubseqLimitsInput hT μ inferInstance
    hProjective B hB D hD hDB hdense η₀ hη₀ Ω₀ mΩ₀ P₀ hP₀ Z₀ hZ₀
  have hlimitAE : AEMeasurable limitReadout μ := by
    exact (hCommon₀.2 k s t (fun i =>
      ⟨(htimesD i).1, (htimesD i).2, (hTimes i).2⟩) φ χ).aemeasurable_limit
  have hweakSubseq : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ,
        Tendsto (fun n =>
          (⟨disorderLaw.map (sourceReadout (ns (ms n))), inferInstance⟩ :
            ProbabilityMeasure (Fin k → ℝ × ℝ))) atTop
          (𝓝 (⟨μ.map limitReadout, inferInstance⟩ :
            ProbabilityMeasure (Fin k → ℝ × ℝ))) := by
    intro ns hns
    obtain ⟨θ, hθ, hnsθ⟩ := strictMono_subseq_of_tendsto_atTop hns
    let φseq := ns ∘ θ
    obtain ⟨ψ, hψ, Ω', mΩ', P', hP', Z', hZ'⟩ :=
      exists_polymerSubseqLimit ϑ D hD hD0 φseq hnsθ
    let η := φseq ∘ ψ
    have hη : StrictMono η := hnsθ.comp hψ
    have hCommon := @projectiveSHFCommonProcess_isPolymerSubseqLimit ϑ hDenseSubseqLimitsInput hT μ inferInstance
      hProjective B hB D hD hDB hdense η hη Ω' mΩ' P' hP' Z' hZ'
    have hdist := hCommon.2 k s t (fun i =>
      ⟨(htimesD i).1, (htimesD i).2, (hTimes i).2⟩) φ χ
    refine ⟨θ ∘ ψ, ?_⟩
    convert hdist.tendsto using 1
    rfl
  have hdistTendsto : Tendsto
      (fun N =>
        (⟨disorderLaw.map (sourceReadout N), inferInstance⟩ :
          ProbabilityMeasure (Fin k → ℝ × ℝ))) atTop
      (𝓝 (⟨μ.map limitReadout, inferInstance⟩ :
        ProbabilityMeasure (Fin k → ℝ × ℝ))) :=
    Filter.tendsto_of_subseq_tendsto hweakSubseq
  exact ⟨hsource, hlimitAE, hdistTendsto⟩


/-- The Kolmogorov common process is critical and is a dense SHF on every
countable dense bounded time window. -/
theorem exists_isCriticalSHF_isDenseSHF_of (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF ϑ P Z ∧
      ∀ B : ℝ, 0 < B → ∀ D : Set ℝ, D.Countable → D ⊆ Set.Icc 0 B → Set.Icc 0 B ⊆ closure D →
        IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z := by
  obtain ⟨μ, hμ, hProjective⟩ := exists_projectiveSHFLimit ϑ hDenseSubseqLimitsInput hT
  let Ω := SHFTimePair → SHFPairRadonMeasure
  let Z : ℝ → ℝ → Ω → Measure (Plane × Plane) := projectiveSHFCommonProcess
  refine ⟨Ω, inferInstance, μ, hμ, Z, ?_, ?_⟩
  · apply (@isCriticalSHF_iff_polymerMeasure ϑ Ω inferInstance μ hμ Z).2
    refine ⟨?_, ?_, ?_⟩
    · intro s t hs hst
      exact measurable_projectiveSHFCommonProcess s t hs hst
    · intro s t hs hst
      let j : SHFTimePair := ⟨(s, t), hs, hst⟩
      filter_upwards [projectiveSHFLimit_flatMarginal_ae ϑ hProjective j] with ω hflat
      have hcoord := projectiveSHFCommonProcess_eq_coordinate j ω
      change IsLocallyFiniteMeasure (projectiveSHFCommonProcess s t ω) ∧
        IsLocallyFiniteMeasure (Measure.map Prod.fst (projectiveSHFCommonProcess s t ω))
      have hcoord' : projectiveSHFCommonProcess s t ω = (ω j : Measure (Plane × Plane)) := by
        simpa [j, projectiveSHFPairStart, projectiveSHFPairEnd] using hcoord
      exact ⟨projectiveSHFCommonProcess_pair_locallyFinite s t hs hst ω, by
        rw [hcoord']
        exact hflat⟩
    · intro k s t hTimes φ χ
      exact @projectiveSHFCommonProcess_pairings_tendsto ϑ hDenseSubseqLimitsInput hT μ hμ hProjective
        k s t hTimes φ χ
  · intro B hB D hD hDB hdense
    obtain ⟨ψ, hψ, Ω', mΩ', P', hP', Z', hZ'⟩ :=
      exists_polymerSubseqLimit ϑ D hD (fun r hr => (hDB hr).1) (fun n => n) strictMono_id
    have hCommon := @projectiveSHFCommonProcess_isPolymerSubseqLimit ϑ hDenseSubseqLimitsInput hT μ hμ
      hProjective B hB D hD hDB hdense ψ hψ Ω' mΩ' P' hP' Z' hZ'
    exact @hDenseSubseqLimitsInput D hD (fun r hr => (hDB hr).1) ψ hψ Ω inferInstance μ hμ Z hCommon

end Critical2DKPZ.SHF.Existence

end
