/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Smoothing.EndpointDistribution
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-! # Translation of the origin estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Polymer
open Critical2DKPZ.Collision

private def disorderShiftEquiv (x : Site) : Disorder ≃ᵐ Disorder :=
  MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
    (Critical2DKPZ.Gaussian.spatialTranslation x).symm

private theorem disorderShift_eq_equiv (x : Site) :
    (fun (ω : Disorder) (p : ℕ × Site) => ω (p.1, p.2 + x)) = disorderShiftEquiv x := by
  funext ω p
  simp [disorderShiftEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Critical2DKPZ.Gaussian.spatialTranslation]

private theorem integrableLog_shiftedWeightedProfile (β : ℝ) (n N : ℕ)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω z, z ∉ A → η ω z = 0)
    (hnn : ∀ ω z, 0 ≤ η ω z) (hmass : ∀ ω, ∑ z ∈ A, η ω z = 1)
    (hmeas : ∀ z, Measurable[disorderPast n] (η · z))
    (f : Site → ℝ) (L : ℝ)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ L) :
    Measurable (fun ω => Real.log (profileP2Fun β n N (η ω) f ω)) ∧
      Measurable (fun ω => Real.log (profileP2Fun β n N (η ω) (fun _ => 1) ω)) ∧
      (∀ ω, |Real.log (profileP2Fun β n N (η ω) f ω) -
        Real.log (profileP2Fun β n N (η ω) (fun _ => 1) ω)| ≤ L) := by
  have hweighted : Measurable (randomTerminalProfilePolymer β n N η f) :=
    measurable_randomTerminalProfilePolymer β n N A η f hsupp hmeas
  have hflat : Measurable (randomTerminalProfilePolymer β n N η (fun _ => 1)) :=
    measurable_randomTerminalProfilePolymer β n N A η (fun _ => 1) hsupp hmeas
  constructor
  · exact Real.measurable_log.comp (by
      change Measurable (fun ω => profileP2Fun β n N (η ω) f ω) at hweighted
      exact hweighted)
  constructor
  · exact Real.measurable_log.comp (by
      change Measurable (fun ω => profileP2Fun β n N (η ω) (fun _ => 1) ω) at hflat
      exact hflat)
  · intro ω
    exact abs_log_profileP2Fun_sub_le β n N (η ω) A (hsupp ω)
      (hnn ω) (hmass ω) f L hf ω

/-- Spatial translation extends the origin profile-comparison and logarithmic-moment bounds uniformly to all lattice starting sites. -/
theorem prop_PF_logTails_of (hO : PropPFOriginBound) (hL : LogTailsOriginBound) (A : ℝ) :
    (∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A,
      ∃ G : Site → Set Disorder, ∀ x : Site,
        MeasurableSet[disorderPast (evenCeil (Real.sqrt δ * N))] (G x) ∧
        (disorderLaw (G x)ᶜ).toReal ≤ C / |Real.log δ| ∧
        ∫ ω in G x, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) (fun _ => 1) ω -
          profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
            (fun _ => 1) ω| ∂disorderLaw ≤ C / |Real.log δ| ∧
        (∫ ω in G x, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) (fun _ => 1) ω ^ 2
            ∂disorderLaw ≤ C * |Real.log δ|) ∧
        (∫ ω in G x, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
            (fun _ => 1) ω ^ 2 ∂disorderLaw ≤ C * |Real.log δ|) ∧
        ∀ (f : Site → ℝ) (M : ℝ), (∀ z, |f z| ≤ M) →
          ∫ ω in G x, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) f ω -
            profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
              f ω| ∂disorderLaw ≤ C * M * Real.sqrt (Real.log |Real.log δ|) / |Real.log δ|) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (f : Site → ℝ) (L : ℝ), (∀ z, 0 < f z ∧ |Real.log (f z)| ≤ L) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ x : Site,
          eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) f ω)) p disorderLaw ≤
            ENNReal.ofReal (C * Real.log |Real.log δ| + L + ε) ∧
          eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
              f ω)) p disorderLaw ≤
            ENNReal.ofReal (C * Real.log |Real.log δ| + L + ε)) := by
  constructor
  · obtain ⟨δ₀, C, hδ₀, hδ₀lt, hOrigin⟩ := hO A
    refine ⟨δ₀, C, hδ₀, hδ₀lt, ?_⟩
    intro δ hδ hδle
    have hN := hOrigin δ hδ hδle
    filter_upwards [hN] with N hN
    intro ϑ hϑ
    obtain ⟨G₀, hG₀meas, hG₀prob, hG₀abs, hG₀endpointSq, hG₀smoothSq,
      hG₀weighted⟩ := hN ϑ hϑ
    refine ⟨fun x => (fun (ω : Disorder) (p : ℕ × Site) => ω (p.1, p.2 + x)) ⁻¹' G₀,
      ?_⟩
    intro x
    let τ : Disorder → Disorder :=
      fun ω p => ω (p.1, p.2 + x)
    have hτeq : τ = disorderShiftEquiv x := by
      dsimp [τ]
      exact disorderShift_eq_equiv x
    have hτemb : MeasurableEmbedding τ := by
      rw [hτeq]
      exact (disorderShiftEquiv x).measurableEmbedding
    have hMP : MeasurePreserving τ disorderLaw disorderLaw := by
      exact measurePreserving_disorderShift x
    let Gx : Set Disorder := τ ⁻¹' G₀
    have hGxmeas : MeasurableSet[disorderPast (evenCeil (Real.sqrt δ * N))] Gx := by
      dsimp [Gx, τ]
      exact hG₀meas.preimage (measurable_disorderShift_past
        (evenCeil (Real.sqrt δ * N)) x)
    have hGxprob : (disorderLaw Gxᶜ).toReal ≤ C / |Real.log δ| := by
      have hpre : Gxᶜ = τ ⁻¹' G₀ᶜ := by
        ext ω
        simp [Gx]
      rw [hpre, hMP.measure_preimage_emb hτemb G₀ᶜ]
      exact hG₀prob
    let n : ℕ := evenCeil (Real.sqrt δ * N)
    let m : ℕ := evenCeil (δ * N)
    have hendpointEq (ω : Disorder) :
        profileP2Fun (criticalBeta ϑ N) n N (endpointDist (criticalBeta ϑ N) n x ω)
            (fun _ => 1) ω =
          profileP2Fun (criticalBeta ϑ N) n N
            (endpointDist (criticalBeta ϑ N) n 0 (τ ω)) (fun _ => 1) (τ ω) := by
      simpa [n, τ] using
        profileP2Fun_endpointDist_translate (criticalBeta ϑ N) n N x (fun _ => 1) ω
    have hsmoothedEq (ω : Disorder) :
        profileP2Fun (criticalBeta ϑ N) n N
            (smoothedEndpointDist (criticalBeta ϑ N) m n x ω) (fun _ => 1) ω =
          profileP2Fun (criticalBeta ϑ N) n N
            (smoothedEndpointDist (criticalBeta ϑ N) m n 0 (τ ω)) (fun _ => 1) (τ ω) := by
      simpa [n, m, τ] using
        profileP2Fun_smoothedEndpointDist_translate (criticalBeta ϑ N) m n N x
          (fun _ => 1) ω
    have hAbsIntegrand (ω : Disorder) :
        |profileP2Fun (criticalBeta ϑ N) n N
              (endpointDist (criticalBeta ϑ N) n x ω) (fun _ => 1) ω -
            profileP2Fun (criticalBeta ϑ N) n N
              (smoothedEndpointDist (criticalBeta ϑ N) m n x ω) (fun _ => 1) ω| =
          (fun ξ => |profileP2Fun (criticalBeta ϑ N) n N
                (endpointDist (criticalBeta ϑ N) n 0 ξ) (fun _ => 1) ξ -
              profileP2Fun (criticalBeta ϑ N) n N
                (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) (fun _ => 1) ξ|)
            (τ ω) := by
      rw [hendpointEq, hsmoothedEq]
    have hAbs :
        ∫ ω in Gx,
            |profileP2Fun (criticalBeta ϑ N) n N
                  (endpointDist (criticalBeta ϑ N) n x ω) (fun _ => 1) ω -
                profileP2Fun (criticalBeta ϑ N) n N
                  (smoothedEndpointDist (criticalBeta ϑ N) m n x ω) (fun _ => 1) ω|
            ∂disorderLaw ≤ C / |Real.log δ| := by
      calc
        _ = ∫ ω in Gx,
              (fun ξ => |profileP2Fun (criticalBeta ϑ N) n N
                    (endpointDist (criticalBeta ϑ N) n 0 ξ) (fun _ => 1) ξ -
                  profileP2Fun (criticalBeta ϑ N) n N
                    (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) (fun _ => 1) ξ|)
                (τ ω) ∂disorderLaw := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hAbsIntegrand
        _ = ∫ ω in G₀,
              |profileP2Fun (criticalBeta ϑ N) n N
                    (endpointDist (criticalBeta ϑ N) n 0 ω) (fun _ => 1) ω -
                  profileP2Fun (criticalBeta ϑ N) n N
                    (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ω) (fun _ => 1) ω|
                ∂disorderLaw := by
              simpa only [Gx] using
                (hMP.setIntegral_preimage_emb hτemb
                  (fun ξ => |profileP2Fun (criticalBeta ϑ N) n N
                      (endpointDist (criticalBeta ϑ N) n 0 ξ) (fun _ => 1) ξ -
                    profileP2Fun (criticalBeta ϑ N) n N
                      (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) (fun _ => 1) ξ|)
                  G₀)
        _ ≤ C / |Real.log δ| := hG₀abs
    refine ⟨hGxmeas, hGxprob, hAbs, ?_, ?_, ?_⟩
    · have hEq (ω : Disorder) :
          profileP2Fun (criticalBeta ϑ N) n N
              (endpointDist (criticalBeta ϑ N) n x ω) (fun _ => 1) ω ^ 2 =
            (fun ξ => profileP2Fun (criticalBeta ϑ N) n N
                (endpointDist (criticalBeta ϑ N) n 0 ξ) (fun _ => 1) ξ ^ 2) (τ ω) := by
        rw [hendpointEq]
      calc
        _ = ∫ ω in Gx,
              (fun ξ => profileP2Fun (criticalBeta ϑ N) n N
                  (endpointDist (criticalBeta ϑ N) n 0 ξ) (fun _ => 1) ξ ^ 2)
                (τ ω) ∂disorderLaw := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => hEq ω
        _ = ∫ ω in G₀, profileP2Fun (criticalBeta ϑ N) n N
              (endpointDist (criticalBeta ϑ N) n 0 ω) (fun _ => 1) ω ^ 2 ∂disorderLaw :=
              by
                simpa only [Gx] using
                  (hMP.setIntegral_preimage_emb hτemb
                    (fun ξ => profileP2Fun (criticalBeta ϑ N) n N
                      (endpointDist (criticalBeta ϑ N) n 0 ξ) (fun _ => 1) ξ ^ 2) G₀)
        _ ≤ C * |Real.log δ| := hG₀endpointSq
    · have hEq (ω : Disorder) :
          profileP2Fun (criticalBeta ϑ N) n N
              (smoothedEndpointDist (criticalBeta ϑ N) m n x ω) (fun _ => 1) ω ^ 2 =
            (fun ξ => profileP2Fun (criticalBeta ϑ N) n N
                (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) (fun _ => 1) ξ ^ 2)
              (τ ω) := by
        rw [hsmoothedEq]
      calc
        _ = ∫ ω in Gx,
              (fun ξ => profileP2Fun (criticalBeta ϑ N) n N
                  (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) (fun _ => 1) ξ ^ 2)
                (τ ω) ∂disorderLaw := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => hEq ω
        _ = ∫ ω in G₀, profileP2Fun (criticalBeta ϑ N) n N
              (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ω) (fun _ => 1) ω ^ 2
              ∂disorderLaw := by
              simpa only [Gx] using
                (hMP.setIntegral_preimage_emb hτemb
                  (fun ξ => profileP2Fun (criticalBeta ϑ N) n N
                    (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) (fun _ => 1) ξ ^ 2)
                  G₀)
        _ ≤ C * |Real.log δ| := hG₀smoothSq
    · intro f M hf
      let fₓ : Site → ℝ := fun z => f (z + x)
      have hfₓ : ∀ z, |fₓ z| ≤ M := fun z => hf (z + x)
      have hendpointWeightedEq (ω : Disorder) :
          profileP2Fun (criticalBeta ϑ N) n N
              (endpointDist (criticalBeta ϑ N) n x ω) f ω =
            profileP2Fun (criticalBeta ϑ N) n N
              (endpointDist (criticalBeta ϑ N) n 0 (τ ω)) fₓ (τ ω) := by
        simpa [n, τ, fₓ] using
          profileP2Fun_endpointDist_translate (criticalBeta ϑ N) n N x f ω
      have hsmoothedWeightedEq (ω : Disorder) :
          profileP2Fun (criticalBeta ϑ N) n N
              (smoothedEndpointDist (criticalBeta ϑ N) m n x ω) f ω =
            profileP2Fun (criticalBeta ϑ N) n N
              (smoothedEndpointDist (criticalBeta ϑ N) m n 0 (τ ω)) fₓ (τ ω) := by
        simpa [n, m, τ, fₓ] using
          profileP2Fun_smoothedEndpointDist_translate (criticalBeta ϑ N) m n N x f ω
      have hEq (ω : Disorder) :
          |profileP2Fun (criticalBeta ϑ N) n N
                (endpointDist (criticalBeta ϑ N) n x ω) f ω -
              profileP2Fun (criticalBeta ϑ N) n N
                (smoothedEndpointDist (criticalBeta ϑ N) m n x ω) f ω| =
            (fun ξ => |profileP2Fun (criticalBeta ϑ N) n N
                  (endpointDist (criticalBeta ϑ N) n 0 ξ) fₓ ξ -
                profileP2Fun (criticalBeta ϑ N) n N
                  (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) fₓ ξ|) (τ ω) := by
        rw [hendpointWeightedEq, hsmoothedWeightedEq]
      calc
        _ = ∫ ω in Gx,
              (fun ξ => |profileP2Fun (criticalBeta ϑ N) n N
                    (endpointDist (criticalBeta ϑ N) n 0 ξ) fₓ ξ -
                  profileP2Fun (criticalBeta ϑ N) n N
                    (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) fₓ ξ|)
                (τ ω) ∂disorderLaw := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => hEq ω
        _ = ∫ ω in G₀,
              |profileP2Fun (criticalBeta ϑ N) n N
                    (endpointDist (criticalBeta ϑ N) n 0 ω) fₓ ω -
                profileP2Fun (criticalBeta ϑ N) n N
                    (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ω) fₓ ω|
              ∂disorderLaw := by
              simpa only [Gx] using
                (hMP.setIntegral_preimage_emb hτemb
                  (fun ξ => |profileP2Fun (criticalBeta ϑ N) n N
                      (endpointDist (criticalBeta ϑ N) n 0 ξ) fₓ ξ -
                    profileP2Fun (criticalBeta ϑ N) n N
                      (smoothedEndpointDist (criticalBeta ϑ N) m n 0 ξ) fₓ ξ|)
                  G₀)
        _ ≤ C * M * Real.sqrt (Real.log |Real.log δ|) / |Real.log δ| :=
              hG₀weighted fₓ M hfₓ
  · intro p hp hpTop
    obtain ⟨C₁, δ₁, hδ₁, hLogOrigin⟩ := hL A p hp hpTop
    let δ₂ : ℝ := min δ₁ (Real.exp (-Real.exp 1))
    have hδ₂ : 0 < δ₂ := by
      dsimp [δ₂]
      exact lt_min hδ₁ (Real.exp_pos _)
    refine ⟨|C₁| + 1, δ₂, hδ₂, ?_⟩
    intro δ hδ hδlt ϑ hϑ f L hf ε hε
    have hlogδ : Real.log δ < -Real.exp 1 := by
      have : δ < Real.exp (-Real.exp 1) := lt_of_lt_of_le hδlt (min_le_right _ _)
      exact (Real.log_lt_iff_lt_exp hδ).2 this
    have hloglog : 1 ≤ Real.log |Real.log δ| := by
      have habs : Real.exp 1 < |Real.log δ| := by
        rw [abs_of_neg (lt_trans hlogδ (neg_lt_zero.mpr (Real.exp_pos 1)))]
        linarith
      calc
        1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log |Real.log δ| := Real.log_le_log (Real.exp_pos 1) habs.le
    have hflatN := hLogOrigin δ hδ (lt_of_lt_of_le hδlt (min_le_left _ _))
    filter_upwards [hflatN] with N hflatN
    have hflat := hflatN ϑ hϑ
    intro x
    let n : ℕ := evenCeil (Real.sqrt δ * N)
    let m : ℕ := evenCeil (δ * N)
    let β : ℝ := criticalBeta ϑ N
    let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x)
    have hτeq : τ = disorderShiftEquiv x := by
      dsimp [τ]
      exact disorderShift_eq_equiv x
    have hMP : MeasurePreserving τ disorderLaw disorderLaw := by
      exact measurePreserving_disorderShift x
    have hsqrtδ : δ ≤ Real.sqrt δ := by
      apply (Real.le_sqrt hδ.le hδ.le).2
      have hδlt₁ : δ < 1 := by
        calc
          δ < δ₂ := hδlt
          _ ≤ Real.exp (-Real.exp 1) := by dsimp [δ₂]; exact min_le_right _ _
          _ < 1 := Real.exp_lt_one_iff.mpr
            (neg_lt_zero.mpr (Real.exp_pos (1 : ℝ)))
      nlinarith
    have hmn : m ≤ n := by
      dsimp [m, n]
      apply evenCeil_mono
      exact mul_le_mul_of_nonneg_right hsqrtδ (Nat.cast_nonneg N)
    have hLogEndpointData :
        (∀ ω z, z ∉ Polymer.endpoints 0 n →
            endpointDist β n 0 ω z = 0) ∧
        (∀ ω z, 0 ≤ endpointDist β n 0 ω z) ∧
        (∀ ω, ∑ z ∈ Polymer.endpoints 0 n, endpointDist β n 0 ω z = 1) ∧
        (∀ z, Measurable[disorderPast n] (fun ω => endpointDist β n 0 ω z)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ω z hz
        exact Polymer.endpointDist_eq_zero_of_not_mem β n 0 z ω hz
      · intro ω z
        exact Polymer.endpointDist_nonneg β n 0 z ω
      · intro ω
        have hsum : (∑' z, endpointDist β n 0 ω z) =
            ∑ z ∈ Polymer.endpoints 0 n, endpointDist β n 0 ω z := by
          apply tsum_eq_sum
          intro z hz
          exact Polymer.endpointDist_eq_zero_of_not_mem β n 0 z ω hz
        rw [← hsum]
        exact Polymer.tsum_endpointDist β n 0 ω
      · intro z
        exact Polymer.measurable_endpointDist_past β n 0 z
    have hLogSmoothedData :
        (∀ ω z, z ∉ (Polymer.endpoints 0 m).biUnion
            (fun y => Polymer.endpoints y (n - m)) →
            smoothedEndpointDist β m n 0 ω z = 0) ∧
        (∀ ω z, 0 ≤ smoothedEndpointDist β m n 0 ω z) ∧
        (∀ ω, ∑ z ∈ (Polymer.endpoints 0 m).biUnion
            (fun y => Polymer.endpoints y (n - m)), smoothedEndpointDist β m n 0 ω z = 1) ∧
        (∀ z, Measurable[disorderPast n]
            (fun ω => smoothedEndpointDist β m n 0 ω z)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ω z hz
        exact Smoothing.smoothedEndpointDist_eq_zero_of_not_mem β 0 z ω hz
      · intro ω z
        exact Smoothing.smoothedEndpointDist_nonneg β 0 z ω
      · intro ω
        have hsum : (∑' z, smoothedEndpointDist β m n 0 ω z) =
            ∑ z ∈ (Polymer.endpoints 0 m).biUnion
              (fun y => Polymer.endpoints y (n - m)), smoothedEndpointDist β m n 0 ω z := by
          apply tsum_eq_sum
          intro z hz
          exact Smoothing.smoothedEndpointDist_eq_zero_of_not_mem β 0 z ω hz
        rw [← hsum]
        exact Smoothing.tsum_smoothedEndpointDist β hmn 0 ω
      · intro z
        have hblock : Gaussian.disorderBlock m n ≤ disorderPast n := by
          rw [← Gaussian.disorderBlock_zero n]
          exact Gaussian.disorderBlock_mono (Nat.zero_le m) le_rfl
        exact (Polymer.measurable_smoothedEndpointDist_block β m n hmn 0 z).mono
          hblock le_rfl
    have hfshift : ∀ z, 0 < (fun y => f (y + x)) z ∧
        |Real.log ((fun y => f (y + x)) z)| ≤ L := fun z => hf (z + x)
    have hEndpointLog := integrableLog_shiftedWeightedProfile β n N
      (fun ω z => endpointDist β n 0 ω z) (Polymer.endpoints 0 n)
      hLogEndpointData.1 hLogEndpointData.2.1 hLogEndpointData.2.2.1
      hLogEndpointData.2.2.2 (fun z => f (z + x)) L hfshift
    have hSmoothedLog := integrableLog_shiftedWeightedProfile β n N
      (fun ω z => smoothedEndpointDist β m n 0 ω z)
      ((Polymer.endpoints 0 m).biUnion (fun y => Polymer.endpoints y (n - m)))
      hLogSmoothedData.1 hLogSmoothedData.2.1 hLogSmoothedData.2.2.1
      hLogSmoothedData.2.2.2 (fun z => f (z + x)) L hfshift
    have hLnonneg : 0 ≤ L := le_trans (abs_nonneg (Real.log (f 0))) (hf 0).2
    have hEndOrigin :
        eLpNorm (fun ω => Real.log (profileP2Fun β n N
          (endpointDist β n 0 ω) (fun _ => 1) ω)) p disorderLaw ≤
          ENNReal.ofReal (C₁ * Real.log |Real.log δ|) := hflat.1
    have hSmoothOrigin :
        eLpNorm (fun ω => Real.log (profileP2Fun β n N
          (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω)) p disorderLaw ≤
          ENNReal.ofReal (C₁ * Real.log |Real.log δ|) := hflat.2
    have hEndDiffBound : ∀ ω,
        |Real.log (profileP2Fun β n N (endpointDist β n 0 ω)
            (fun z => f (z + x)) ω) -
          Real.log (profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω)| ≤ L :=
      hEndpointLog.2.2
    have hSmoothDiffBound : ∀ ω,
        |Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω)
            (fun z => f (z + x)) ω) -
          Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω)| ≤ L :=
      hSmoothedLog.2.2
    have hEndDiffMeas : Measurable (fun ω =>
        Real.log (profileP2Fun β n N (endpointDist β n 0 ω)
            (fun z => f (z + x)) ω) -
          Real.log (profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω)) :=
      hEndpointLog.1.sub hEndpointLog.2.1
    have hSmoothDiffMeas : Measurable (fun ω =>
        Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω)
            (fun z => f (z + x)) ω) -
          Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω)) :=
      hSmoothedLog.1.sub hSmoothedLog.2.1
    have hEndDiffLp : eLpNorm (fun ω =>
        Real.log (profileP2Fun β n N (endpointDist β n 0 ω)
            (fun z => f (z + x)) ω) -
          Real.log (profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω))
          p disorderLaw ≤ ENNReal.ofReal L := by
      calc
        _ ≤ disorderLaw Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal L :=
          eLpNorm_le_of_ae_bound hEndDiffMeas.aestronglyMeasurable
            (Filter.Eventually.of_forall fun ω => by
              rw [Real.norm_eq_abs]
              exact hEndDiffBound ω)
        _ = ENNReal.ofReal L := by simp
    have hSmoothDiffLp : eLpNorm (fun ω =>
        Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω)
            (fun z => f (z + x)) ω) -
          Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω))
          p disorderLaw ≤ ENNReal.ofReal L := by
      calc
        _ ≤ disorderLaw Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal L :=
          eLpNorm_le_of_ae_bound hSmoothDiffMeas.aestronglyMeasurable
            (Filter.Eventually.of_forall fun ω => by
              rw [Real.norm_eq_abs]
              exact hSmoothDiffBound ω)
        _ = ENNReal.ofReal L := by simp
    have hEndFlatMeas : Measurable (fun ω =>
        Real.log (profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω)) :=
      hEndpointLog.2.1
    have hSmoothFlatMeas : Measurable (fun ω =>
        Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω)) :=
      hSmoothedLog.2.1
    have hloglog0 : 0 ≤ Real.log |Real.log δ| := by linarith [hloglog]
    have hCLnonneg : 0 ≤ (|C₁| + 1) * Real.log |Real.log δ| :=
      mul_nonneg (by positivity) hloglog0
    have hCEnd : C₁ * Real.log |Real.log δ| ≤
        (|C₁| + 1) * Real.log |Real.log δ| := by
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₁]) hloglog0
    have hEndBound :
        eLpNorm (fun ω => Real.log (profileP2Fun β n N
          (endpointDist β n x ω) f ω)) p disorderLaw ≤
          ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ| + L + ε) := by
      let F : Disorder → ℝ := fun ω => Real.log (profileP2Fun β n N
          (endpointDist β n 0 ω) (fun z => f (z + x)) ω)
      let F₀ : Disorder → ℝ := fun ω => Real.log (profileP2Fun β n N
          (endpointDist β n 0 ω) (fun _ => 1) ω)
      let H : Disorder → ℝ := F - F₀
      have hHmeas : Measurable H := by
        exact hEndDiffMeas
      have hpoint (ω : Disorder) :
          Real.log (profileP2Fun β n N (endpointDist β n x ω) f ω) = F (τ ω) := by
        simpa [F, β, n, τ] using
          congrArg Real.log (profileP2Fun_endpointDist_translate
            (criticalBeta ϑ N) n N x f ω)
      have hadd (ω : Disorder) : F (τ ω) = F₀ (τ ω) + H (τ ω) := by
        dsimp [H]
        ring
      have hsum (ω : Disorder) :
          Real.log (profileP2Fun β n N (endpointDist β n x ω) f ω) =
            F₀ (τ ω) + H (τ ω) := (hpoint ω).trans (hadd ω)
      have hcompFlat : eLpNorm (fun ω => F₀ (τ ω)) p disorderLaw =
          eLpNorm F₀ p disorderLaw := by
        change eLpNorm (F₀ ∘ τ) p disorderLaw = _
        exact eLpNorm_comp_measurePreserving (p := p) (g := F₀)
          hEndFlatMeas.aestronglyMeasurable hMP
      have hcompDiff : eLpNorm (fun ω => H (τ ω)) p disorderLaw =
          eLpNorm H p disorderLaw := by
        change eLpNorm (H ∘ τ) p disorderLaw = _
        exact eLpNorm_comp_measurePreserving (p := p) (g := H)
          hHmeas.aestronglyMeasurable hMP
      calc
        _ = eLpNorm (fun ω => F₀ (τ ω) + H (τ ω)) p disorderLaw := by
          apply eLpNorm_congr_ae
          exact Filter.Eventually.of_forall hsum
        _ ≤ eLpNorm (fun ω => F₀ (τ ω)) p disorderLaw +
              eLpNorm (fun ω => H (τ ω)) p disorderLaw := eLpNorm_add_le hp
        _ = eLpNorm F₀ p disorderLaw + eLpNorm H p disorderLaw := by
          rw [hcompFlat, hcompDiff]
        _ ≤ ENNReal.ofReal (C₁ * Real.log |Real.log δ|) + ENNReal.ofReal L :=
          add_le_add hEndOrigin hEndDiffLp
        _ ≤ ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ|) +
              ENNReal.ofReal L := by
          exact add_le_add (ENNReal.ofReal_le_ofReal hCEnd) le_rfl
        _ = ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ| + L) := by
          rw [ENNReal.ofReal_add hCLnonneg hLnonneg]
        _ ≤ ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ| + L + ε) :=
          ENNReal.ofReal_le_ofReal (by linarith)
    have hSmoothBound :
        eLpNorm (fun ω => Real.log (profileP2Fun β n N
          (smoothedEndpointDist β m n x ω) f ω)) p disorderLaw ≤
          ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ| + L + ε) := by
      let F : Disorder → ℝ := fun ω => Real.log (profileP2Fun β n N
          (smoothedEndpointDist β m n 0 ω) (fun z => f (z + x)) ω)
      let F₀ : Disorder → ℝ := fun ω => Real.log (profileP2Fun β n N
          (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω)
      let H : Disorder → ℝ := F - F₀
      have hHmeas : Measurable H := hSmoothDiffMeas
      have hpoint (ω : Disorder) :
          Real.log (profileP2Fun β n N (smoothedEndpointDist β m n x ω) f ω) = F (τ ω) := by
        simpa [F, β, n, m, τ] using
          congrArg Real.log (profileP2Fun_smoothedEndpointDist_translate
            (criticalBeta ϑ N) m n N x f ω)
      have hadd (ω : Disorder) : F (τ ω) = F₀ (τ ω) + H (τ ω) := by
        dsimp [H]
        ring
      have hsum (ω : Disorder) :
          Real.log (profileP2Fun β n N (smoothedEndpointDist β m n x ω) f ω) =
            F₀ (τ ω) + H (τ ω) := (hpoint ω).trans (hadd ω)
      have hcompFlat : eLpNorm (fun ω => F₀ (τ ω)) p disorderLaw =
          eLpNorm F₀ p disorderLaw := by
        change eLpNorm (F₀ ∘ τ) p disorderLaw = _
        exact eLpNorm_comp_measurePreserving (p := p) (g := F₀)
          hSmoothFlatMeas.aestronglyMeasurable hMP
      have hcompDiff : eLpNorm (fun ω => H (τ ω)) p disorderLaw =
          eLpNorm H p disorderLaw := by
        change eLpNorm (H ∘ τ) p disorderLaw = _
        exact eLpNorm_comp_measurePreserving (p := p) (g := H)
          hHmeas.aestronglyMeasurable hMP
      calc
        _ = eLpNorm (fun ω => F₀ (τ ω) + H (τ ω)) p disorderLaw := by
          apply eLpNorm_congr_ae
          exact Filter.Eventually.of_forall hsum
        _ ≤ eLpNorm (fun ω => F₀ (τ ω)) p disorderLaw +
              eLpNorm (fun ω => H (τ ω)) p disorderLaw := eLpNorm_add_le hp
        _ = eLpNorm F₀ p disorderLaw + eLpNorm H p disorderLaw := by
          rw [hcompFlat, hcompDiff]
        _ ≤ ENNReal.ofReal (C₁ * Real.log |Real.log δ|) + ENNReal.ofReal L :=
          add_le_add hSmoothOrigin hSmoothDiffLp
        _ ≤ ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ|) +
              ENNReal.ofReal L := by
          exact add_le_add (ENNReal.ofReal_le_ofReal hCEnd) le_rfl
        _ = ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ| + L) := by
          rw [ENNReal.ofReal_add hCLnonneg hLnonneg]
        _ ≤ ENNReal.ofReal ((|C₁| + 1) * Real.log |Real.log δ| + L + ε) :=
          ENNReal.ofReal_le_ofReal (by linarith)
    exact ⟨hEndBound, hSmoothBound⟩

end Critical2DKPZ.FutureProfiles

end
