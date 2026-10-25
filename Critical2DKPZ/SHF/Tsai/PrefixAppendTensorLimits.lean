/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConditionalRightAverageLimits
public import Critical2DKPZ.SHF.Tsai.ChainAppendMoments
import Critical2DKPZ.SHF.Tsai.ChainLocalFiniteness

/-! # Appending an independent block at a fixed connector

For a fixed compact initial test, convergence in probability of prefix pairings on all
terminal `L²` tests is preserved by appending an independent block through a fixed mollifier.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- A prefix-pairing limit in probability is preserved by appending an independent block through a fixed mollifier. -/
theorem tendstoInMeasure_chain_append_prod {θ τ ρ : ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (K : ℕ) (σ : Fin (K + 1) → ℝ) (hσ : ∀ i, 0 < σ i)
    (B : Fin (K + 1) → Ω → Measure (Plane × Plane))
    (hB : ∀ i, HasDeltaBoseMoments θ (σ i) P (B i)) (hind : iIndepFun B P)
    (C : Ω → Measure (Plane × Plane)) (hC : HasDeltaBoseMoments θ ρ P C) (hρ : 0 < ρ)
    (A : Ω' → Measure (Plane × Plane)) (hA : HasDeltaBoseMoments θ τ P' A) (hτ : 0 < τ)
    (u : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k)) (r : ℕ)
    (g g' : C_c(Plane, ℝ))
    (hconv : ∀ f : Plane → ℝ, MemLp f 2 →
      TendstoInMeasure P (fun n ω => ∫ p, g p.1 * f p.2
        ∂chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω) (fun k => u k n) K) atTop
          (fun ω => ∫ p, g p.1 * f p.2 ∂C ω)) :
    TendstoInMeasure (P'.prod P) (fun n ω => ∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure
        (chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω.2) (fun k => u k n) K)
        (u K r) (A ω.1)) atTop
      (fun ω => ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure (C ω.2) (u K r) (A ω.1)) := by
  classical
  have hg : MemLp g 2 := g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hg' : MemLp g' 2 := g'.continuous.memLp_of_hasCompactSupport g'.hasCompactSupport
  have hprefix (n : ℕ) := chainPairing_four_append_prod P P' K σ hσ B hB hind A hA hτ
    u hu (fun k => if k = K then r else n) g g' hg hg'
  have heq (n : ℕ) (ω : Ω) :
      chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω)
        (fun k => u k (if k = K then r else n)) K =
      chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω) (fun k => u k n) K := by
    apply chainProduct_congr_connectors
    intro k hk
    rw [ite_eq_right (Nat.ne_of_lt hk)]
  simp only [heq] at hprefix
  have hindC : iIndepFun (fun _ : Fin 1 => C) P := iIndepFun.of_subsingleton
  have htarget := chainPairing_four_append_prod P P' 0 (fun _ => ρ) (fun _ => hρ)
    (fun _ => C) (fun _ => hC) hindC A hA hτ
    (fun _ => u K) (fun _ => hu K) (fun _ => r) g g' hg hg'
  simp only [chainProduct] at htarget
  let Bn (k : ℕ) := B (Fin.ofNat (K + 1) k)
  let σn (k : ℕ) := σ (Fin.ofNat (K + 1) k)
  have hindn : iIndepFun (fun k : Fin (K + 1) => Bn k) P := by
    simpa only [Bn, Fin.ofNat_eq_cast, Fin.cast_val_eq_self] using hind
  have hLF (n : ℕ) : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure
      (chainProduct (fun k => Bn k ω) (fun k => u k n) K) :=
    ae_locallyFinite_chainProduct K σn (fun _ _ => hσ _) Bn (fun _ _ => hB _) hindn u hu n
  exact tendstoInMeasure_smoothedProduct_right_of_tensor_limits P P'
    (fun n ω => chainProduct (fun k => Bn k ω) (fun k => u k n) K) C hLF hC.2.1
    A hA hτ (u K r) ((hu K).1 r) ((hu K).2.1 r).measurable ((hu K).2.2.1 r)
    g g' hconv (fun n => (hprefix n).2.aestronglyMeasurable) htarget.2.aestronglyMeasurable
    (fun n => (hprefix n).1) htarget.1

end Critical2DKPZ.SHF.Tsai

end
