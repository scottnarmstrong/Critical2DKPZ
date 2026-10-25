/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Basic
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
import Critical2DKPZ.SHF.Moments.WordDominationFlatProduct
import Critical2DKPZ.SHF.Positivity.LawFatou
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Passage of a discrete L² modulus to a stochastic heat flow -/

@[expose] public section

open MeasureTheory Filter
open scoped CompactlySupported ENNReal Topology
open Critical2DKPZ.SHF.Moments

noncomputable section

namespace Critical2DKPZ.SHF.TimeContinuity

open Critical2DKPZ.SHF.Limit

/-- Compact polymer pairings have uniformly small mean squared differences when both time endpoints are close, on bounded time windows with durations bounded away from zero. Their squared differences are integrable by `Critical2DKPZ.SHF.Flow.memLp_polymerPairing_two`. -/
def PolymerL2Modulus (ϑ : ℝ) (Φ : C_c(Plane × Plane, ℝ)) (τ T : ℝ) : Prop :=
  ∀ ε > 0, ∃ η > 0, ∀ᶠ N : ℕ in atTop, ∀ s t s' t' : ℝ,
    0 ≤ s → τ ≤ t - s → t ≤ T → 0 ≤ s' → τ ≤ t' - s' → t' ≤ T →
      |s - s'| + |t - t'| ≤ η →
        ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω) -
          ∫ p, Φ p ∂(polymerMeasure ϑ N s' t' ω)) ^ 2 ∂disorderLaw ≤ ε

/-- Joint compact polymer moments of orders one through four converge along moving nonnegative time intervals to the corresponding delta-Bose moment integrals. -/
def PolymerMovingMomentLimit (ϑ : ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → n ≤ 4 → ∀ {s t : ℝ}, 0 ≤ s → s < t → ∀ (sN tN : ℕ → ℝ),
    Tendsto sN atTop (𝓝 s) → Tendsto tN atTop (𝓝 t) → (∀ N, 0 ≤ sN N) →
    ∀ φ : Fin n → C_c(Plane × Plane, ℝ),
      Tendsto (fun N : ℕ => ∫ ω, ∏ i, (∫ p, φ i p * rescaledP2P ϑ N (sN N) (tN N) p ω) ∂disorderLaw)
        atTop
        (𝓝 (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, φ i (x i, y i)) *
            (DeltaBose.momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal))

private theorem aestronglyMeasurable_polymerCompactPairing (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (Φ : C_c(Plane × Plane, ℝ)) :
    AEStronglyMeasurable
      (fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) disorderLaw := by
  let G : (Plane × Plane) × Disorder → ℝ :=
    fun q => Φ q.1 * rescaledP2P ϑ N s t q.1 q.2
  have hpair : Integrable G (volume.prod disorderLaw) := by
    exact SHF.Moments.integrable_pairing_rescaledP2P ϑ N s t
      Φ.continuous Φ.hasCompactSupport
  have hswap : Integrable (fun q : Disorder × (Plane × Plane) => G (q.2, q.1))
      (disorderLaw.prod volume) := hpair.swap
  have hraw : AEStronglyMeasurable
      (fun ω => ∫ p : Plane × Plane,
        Φ p * rescaledP2P ϑ N s t p ω ∂volume) disorderLaw := by
    simpa only [G, Prod.fst, Prod.snd] using
      hswap.aestronglyMeasurable.integral_prod_right'
  have heq : (fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) =ᵐ[disorderLaw]
      (fun ω => ∫ p, Φ p * rescaledP2P ϑ N s t p ω ∂volume) :=
    Filter.Eventually.of_forall fun ω => integral_polymerMeasure ϑ N s t ω Φ
  exact hraw.congr heq.symm

private theorem integrable_polymerCompactPairing_sq_of_majorant
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (Φ : C_c(Plane × Plane, ℝ))
    (hM : Integrable (fun ω =>
      (∫ p : Plane × Plane, compactAbs Φ p * rescaledP2P ϑ N s t p ω ∂volume) ^ 2)
      disorderLaw) :
    Integrable (fun ω => (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) ^ 2) disorderLaw := by
  let A : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)
  let M : Disorder → ℝ := fun ω =>
    ∫ p : Plane × Plane, compactAbs Φ p * rescaledP2P ϑ N s t p ω ∂volume
  have hAmeas : AEStronglyMeasurable A disorderLaw := by
    exact aestronglyMeasurable_polymerCompactPairing ϑ N s t Φ
  have hMnonneg (ω : Disorder) : 0 ≤ M ω := by
    apply integral_nonneg
    intro p
    exact mul_nonneg
      (show 0 ≤ compactAbs Φ p by change 0 ≤ |Φ p|; positivity)
      (SHF.Moments.rescaledP2P_nonneg ϑ N s t p ω)
  let G : (Plane × Plane) × Disorder → ℝ :=
    fun q => Φ q.1 * rescaledP2P ϑ N s t q.1 q.2
  have hpair : Integrable G (volume.prod disorderLaw) := by
    exact SHF.Moments.integrable_pairing_rescaledP2P ϑ N s t
      Φ.continuous Φ.hasCompactSupport
  have hswap : Integrable (fun q : Disorder × (Plane × Plane) => G (q.2, q.1))
      (disorderLaw.prod volume) := hpair.swap
  have hspatial : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => Φ p * rescaledP2P ϑ N s t p ω) volume := by
    have h := (integrable_prod_iff hswap.aestronglyMeasurable).mp hswap
    simpa only [G, Prod.fst, Prod.snd] using h.1
  have hAeq : A = fun ω =>
      ∫ p : Plane × Plane, Φ p * rescaledP2P ϑ N s t p ω ∂volume := by
    funext ω
    exact integral_polymerMeasure ϑ N s t ω Φ
  have hbound : ∀ᵐ ω ∂disorderLaw, |A ω| ≤ M ω := by
    filter_upwards [hspatial] with ω hω
    rw [hAeq]
    calc
      |∫ p : Plane × Plane, Φ p * rescaledP2P ϑ N s t p ω ∂volume| ≤
          ∫ p : Plane × Plane, |Φ p * rescaledP2P ϑ N s t p ω| ∂volume :=
        abs_integral_le_integral_abs
      _ = M ω := by
        dsimp [M]
        apply integral_congr_ae
        filter_upwards [] with p
        calc
          |Φ p * rescaledP2P ϑ N s t p ω| =
              |Φ p| * |rescaledP2P ϑ N s t p ω| := abs_mul _ _
          _ = |Φ p| * rescaledP2P ϑ N s t p ω := by
            rw [abs_of_nonneg (SHF.Moments.rescaledP2P_nonneg ϑ N s t p ω)]
          _ = compactAbs Φ p * rescaledP2P ϑ N s t p ω := by rfl
  have hA2meas : AEStronglyMeasurable (fun ω => A ω ^ 2) disorderLaw :=
    hAmeas.pow 2
  have hA2 : Integrable (fun ω => A ω ^ 2) disorderLaw := by
    apply hM.mono' hA2meas
    filter_upwards [hbound] with ω hω
    calc
      ‖A ω ^ 2‖ = A ω ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ = |A ω| ^ 2 := by rw [sq_abs]
      _ ≤ M ω ^ 2 := (sq_le_sq₀ (abs_nonneg (A ω)) (hMnonneg ω)).mpr hω
  simpa only [A] using hA2

private theorem eventually_integrable_polymerCompactPairing_sq
    (ϑ : ℝ) (Φ : C_c(Plane × Plane, ℝ)) {τ T : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
      Integrable (fun ω => (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) ^ 2) disorderLaw := by
  let φ : Fin 2 → C_c(Plane × Plane, ℝ) := fun _ => Φ
  obtain ⟨B, hB, hN⟩ := SHF.Moments.eventually_integral_compactAbs_pairing_product_fin_le
    ϑ (h := 2) (by norm_num) φ (τ := τ) (T := T) hτ
  filter_upwards [hN] with N hN
  intro s t hs hst ht
  have hMsq : Integrable (fun ω =>
      (∫ p : Plane × Plane,
        compactAbs Φ p * rescaledP2P ϑ N s t p ω ∂volume) ^ 2) disorderLaw := by
    simpa [φ, Fin.prod_univ_succ] using (hN s t hs hst ht).1
  exact integrable_polymerCompactPairing_sq_of_majorant ϑ N s t Φ hMsq

/-- A discrete L² modulus passes to every `IsCriticalSHF` limit. Fatou's lemma in law
also supplies the integrability of the limiting squared difference. -/
theorem isCriticalSHF_L2_modulus_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (Φ : C_c(Plane × Plane, ℝ))
    {τ T : ℝ} (hτ : 0 < τ) (hmod : PolymerL2Modulus ϑ Φ τ T) :
    ∀ ε > 0, ∃ η > 0, ∀ s t s' t' : ℝ,
      0 ≤ s → τ ≤ t - s → t ≤ T → 0 ≤ s' → τ ≤ t' - s' → t' ≤ T →
      |s - s'| + |t - t'| ≤ η →
        Integrable (fun ω =>
          (∫ p, Φ p ∂(Z s t ω) - ∫ p, Φ p ∂(Z s' t' ω)) ^ 2) P ∧
        ∫ ω, (∫ p, Φ p ∂(Z s t ω) - ∫ p, Φ p ∂(Z s' t' ω)) ^ 2 ∂P ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, hmodN⟩ := hmod ε hε
  refine ⟨η, hη, ?_⟩
  intro s t s' t' hs hst ht hs' hs't ht' hclose
  have hst' : s < t := by linarith
  have hs't' : s' < t' := by linarith
  let sV : Fin 2 → ℝ := ![s, s']
  let tV : Fin 2 → ℝ := ![t, t']
  let φV : Fin 2 → C_c(Plane × Plane, ℝ) := fun _ => Φ
  let ψV : Fin 2 → C_c(Plane, ℝ) := fun _ => 0
  let readout : (Fin 2 → ℝ × ℝ) → ℝ := fun v => (v 0).1 - (v 1).1
  let A : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)
  let B : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, Φ p ∂(polymerMeasure ϑ N s' t' ω)
  let X : ℕ → Disorder → ℝ := fun N ω => A N ω - B N ω
  let Y : Ω → ℝ := fun ω => ∫ p, Φ p ∂(Z s t ω) - ∫ p, Φ p ∂(Z s' t' ω)
  have htimes : ∀ i, 0 ≤ sV i ∧ sV i < tV i := by
    intro i
    fin_cases i <;> simp [sV, tV, hs, hs', hst', hs't']
  have hvec := hZ.2.2 2 sV tV htimes φV ψV
  have hdist : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P := by
    have hread := hvec.continuous_comp (g := readout) (by fun_prop)
    simpa [Function.comp_def, X, Y, A, B, sV, tV, φV, ψV, readout,
      integral_polymerMeasure] using hread
  let Xsq : ℕ → Disorder → ℝ := fun N ω => X N ω ^ 2
  let Ysq : Ω → ℝ := fun ω => Y ω ^ 2
  have hdistSq : TendstoInDistribution Xsq atTop Ysq (fun _ => disorderLaw) P := by
    have h := hdist.continuous_comp (g := fun x : ℝ => x ^ 2) (by fun_prop)
    simpa only [Xsq, Ysq, Function.comp_def] using h
  have hAint := eventually_integrable_polymerCompactPairing_sq
    ϑ Φ (τ := τ) (T := T) hτ
  have hBint := eventually_integrable_polymerCompactPairing_sq
    ϑ Φ (τ := τ) (T := T) hτ
  have hXint : ∀ᶠ N : ℕ in atTop, Integrable (Xsq N) disorderLaw := by
    filter_upwards [hAint, hBint] with N hAN hBN
    have hAmeas : AEStronglyMeasurable (A N) disorderLaw :=
      aestronglyMeasurable_polymerCompactPairing ϑ N s t Φ
    have hBmeas : AEStronglyMeasurable (B N) disorderLaw :=
      aestronglyMeasurable_polymerCompactPairing ϑ N s' t' Φ
    have hA2 : Integrable (fun ω => (A N ω) ^ 2) disorderLaw := by
      simpa [A] using hAN s t hs hst ht
    have hB2 : Integrable (fun ω => (B N ω) ^ 2) disorderLaw := by
      simpa [B] using hBN s' t' hs' hs't ht'
    have hXmeas : AEStronglyMeasurable (fun ω => (A N ω - B N ω) ^ 2) disorderLaw :=
      (hAmeas.sub hBmeas).pow 2
    have hRHS : Integrable (fun ω => 2 * (A N ω ^ 2) + 2 * (B N ω ^ 2)) disorderLaw :=
      (hA2.const_mul 2).add (hB2.const_mul 2)
    have hpoint (ω : Disorder) :
        ‖(A N ω - B N ω) ^ 2‖ ≤ 2 * (A N ω ^ 2) + 2 * (B N ω ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (A N ω + B N ω)]
    have hdom := hRHS.mono' hXmeas (Filter.Eventually.of_forall hpoint)
    simpa [Xsq, X] using hdom
  have hmodBound : ∀ᶠ N : ℕ in atTop, ∫ ω, Xsq N ω ∂disorderLaw ≤ ε := by
    filter_upwards [hmodN] with N hN
    simpa [Xsq, X, A, B] using
      hN s t s' t' hs hst ht hs' hs't ht' hclose
  have hlinBound : ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal (Xsq N ω) ∂disorderLaw ≤ ENNReal.ofReal ε := by
    filter_upwards [hXint, hmodBound] with N hInt hBound
    have hEq := ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun ω => sq_nonneg (X N ω))
    calc
      _ = ENNReal.ofReal (∫ ω, Xsq N ω ∂disorderLaw) := hEq.symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hBound
  have hfatou :=
    SHF.Positivity.lintegral_ofReal_le_liminf_of_tendstoInDistribution_nonneg
      hdistSq (fun _ _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hliminf : liminf (fun N =>
      ∫⁻ ω, ENNReal.ofReal (Xsq N ω) ∂disorderLaw) atTop ≤ ENNReal.ofReal ε := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro b hb
    obtain ⟨N, hlow, hupp⟩ := (hb.and hlinBound).exists
    exact hlow.trans hupp
  have hYnn : 0 ≤ᵐ[P] Ysq := Filter.Eventually.of_forall fun ω => sq_nonneg (Y ω)
  have hYmeas : AEStronglyMeasurable Ysq P := hdistSq.aemeasurable_limit.aestronglyMeasurable
  have hYlinfinite :
      (∫⁻ ω, ENNReal.ofReal (Ysq ω) ∂P) < ∞ := by
    exact lt_of_le_of_lt (hfatou.trans hliminf) ENNReal.ofReal_lt_top
  have hYint : Integrable Ysq P :=
    (lintegral_ofReal_ne_top_iff_integrable hYmeas hYnn).mp
      hYlinfinite.ne
  have hYlinEq := ofReal_integral_eq_lintegral_ofReal hYint hYnn
  have hYofRealBound : ENNReal.ofReal (∫ ω, Ysq ω ∂P) ≤ ENNReal.ofReal ε := by
    rw [hYlinEq]
    exact hfatou.trans hliminf
  have hYbound : ∫ ω, Ysq ω ∂P ≤ ε := by
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hYofRealBound
  exact ⟨by simpa [Ysq, Y] using hYint, by simpa [Ysq, Y] using hYbound⟩

end Critical2DKPZ.SHF.TimeContinuity

end
