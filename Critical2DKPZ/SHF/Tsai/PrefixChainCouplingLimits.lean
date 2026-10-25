/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.PrefixAppendTensorLimits
public import Critical2DKPZ.SHF.Tsai.ChainCoarseCouplingLaws
import Critical2DKPZ.SHF.Tsai.ProbabilityLimitTransport

/-! # Transfer of prefix-pairing limits between couplings

A fixed-connector prefix-pairing limit on an independent-copy space also holds for the
original flow, by equality of the joint laws of its blocks.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- A prefix tensor limit gives the fixed-final-connector limit on the original probability space. -/
theorem tendstoInMeasure_chain_coarse_prefix {θ ρ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (σ : Fin (K + 2) → ℝ) (hσ : ∀ i, 0 < σ i)
    (B : Fin (K + 2) → Ω → Measure (Plane × Plane))
    (hB : ∀ i, HasDeltaBoseMoments θ (σ i) P (B i)) (hind : iIndepFun B P)
    (C : Ω → Measure (Plane × Plane)) (hC : HasDeltaBoseMoments θ ρ P C) (hρ : 0 < ρ)
    (φ : (Fin (K + 1) → Measure (Plane × Plane)) → Measure (Plane × Plane))
    (hφ : Measurable φ) (hFactor : C =ᵐ[P] fun ω => φ (fun i => B i.castSucc ω))
    (u : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k)) (r : ℕ)
    (g g' : C_c(Plane, ℝ))
    (hconv : ∀ f : Plane → ℝ, MemLp f 2 →
      TendstoInMeasure P (fun n ω => ∫ p, g p.1 * f p.2
        ∂chainProduct (fun k => B (Fin.ofNat (K + 1) k).castSucc ω) (fun k => u k n) K) atTop
          (fun ω => ∫ p, g p.1 * f p.2 ∂C ω)) :
    TendstoInMeasure P (fun n ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B (Fin.ofNat (K + 2) k) ω)
        (fun k => u k (if k = K then r else n)) (K + 1)) atTop
      (fun ω => ∫ p, g p.1 * g' p.2
        ∂smoothedProductMeasure (C ω) (u K r) (B (Fin.last (K + 1)) ω)) := by
  classical
  have hg : MemLp g 2 := g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hg' : MemLp g' 2 := g'.continuous.memLp_of_hasCompactSupport g'.hasCompactSupport
  let Bp (i : Fin (K + 1)) := B i.castSucc
  have hindp : iIndepFun Bp P := hind.precomp (Fin.castSucc_injective (K + 1))
  have hcopy := tendstoInMeasure_chain_append_prod P P K (fun i => σ i.castSucc)
    (fun i => hσ i.castSucc) Bp (fun i => hB i.castSucc) hindp C hC hρ
    (B (Fin.last (K + 1))) (hB _) (hσ _) u hu r g g' hconv
  have heq (n : ℕ) (ω : Ω) :
      chainProduct (fun k => Bp (Fin.ofNat (K + 1) k) ω)
        (fun k => u k (if k = K then r else n)) K =
      chainProduct (fun k => Bp (Fin.ofNat (K + 1) k) ω) (fun k => u k n) K := by
    apply chainProduct_congr_connectors
    intro k hk
    rw [ite_eq_right (Nat.ne_of_lt hk)]
  have hLaw (n : ℕ) := map_chain_coarse_readouts_eq_snoc_prod P (K + 1) B
    (fun i => (hB i).1) (fun i => (hB i).2.1) hind C hC.1 hC.2.1 φ hφ hFactor
    (fun k => u k (if k = K then r else n))
    (fun k => ((hu k).2.1 _).measurable) (u K r) ((hu K).2.1 r).measurable
    (fun p => g p.1 * g' p.2) (by fun_prop)
  have hLaw' (n : ℕ) : P.map (fun ω =>
      ((∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B (Fin.ofNat (K + 2) k) ω)
        (fun k => u k (if k = K then r else n)) (K + 1)),
       ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure (C ω) (u K r) (B (Fin.last (K + 1)) ω))) =
      (P.prod P).map (fun ω : Ω × Ω =>
      ((∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure
        (chainProduct (fun k => Bp (Fin.ofNat (K + 1) k) ω.2) (fun k => u k n) K)
        (u K r) (B (Fin.last (K + 1)) ω.1)),
       ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure (C ω.2) (u K r) (B (Fin.last (K + 1)) ω.1))) := by
    simpa only [chainProduct_fin_snoc, heq, Bp, ite_true] using hLaw n
  have hX (n : ℕ) := (chainPairing_four_finiteBlocks (K + 1) σ hσ B hB hind u hu
    (fun k => if k = K then r else n) g g' hg hg').2.aestronglyMeasurable.aemeasurable
  have hY := aemeasurable_integral_smoothedProduct P C (B (Fin.last (K + 1)))
    hC.1 (hB _).1 hC.2.1 (hB _).2.1 (u K r) ((hu K).2.1 r).measurable
    (fun p => g p.1 * g' p.2) (by fun_prop)
  have hXcopy (n : ℕ) := chainPairing_four_append_prod P P K (fun i => σ i.castSucc)
    (fun i => hσ i.castSucc) Bp (fun i => hB i.castSucc) hindp
    (B (Fin.last (K + 1))) (hB _) (hσ _) u hu (fun k => if k = K then r else n) g g' hg hg'
  simp only [heq] at hXcopy
  have hYcopy := aemeasurable_integral_smoothedProduct (P.prod P)
    (fun ω : Ω × Ω => C ω.2) (fun ω : Ω × Ω => B (Fin.last (K + 1)) ω.1)
    (hC.1.comp measurable_snd) ((hB _).1.comp measurable_fst)
    ((measurePreserving_snd : MeasurePreserving Prod.snd (P.prod P) P).quasiMeasurePreserving.ae hC.2.1)
    ((measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).quasiMeasurePreserving.ae (hB _).2.1)
    (u K r) ((hu K).2.1 r).measurable (fun p => g p.1 * g' p.2) (by fun_prop)
  exact tendstoInMeasure_of_pair_law_eq P (P.prod P) _ _ _ _ hX hY
    (fun n => (hXcopy n).2.aestronglyMeasurable.aemeasurable) hYcopy hLaw' hcopy

end Critical2DKPZ.SHF.Tsai

end
