/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CouplingIndependence
public import Critical2DKPZ.SHF.Tsai.TwoBlockReadouts

/-! # Joint laws of chains and their coarse-prefix products

A coarse prefix is a measurable function of its elementary increments. Replacing the final
independent block by an independent copy preserves the joint law of the full-chain and
coarse-prefix product pairings.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace Critical2DKPZ.SHF.Tsai

/-- Replacing the final independent block by an independent copy preserves the joint law of the full-chain and coarse-prefix product pairings. -/
theorem map_chain_coarse_readouts_eq_snoc_prod {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (B : Fin (n + 1) → Ω → Measure (Plane × Plane)) (hB : ∀ i, Measurable (B i))
    (hBlf : ∀ i, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B i ω)) (hind : iIndepFun B P)
    (C : Ω → Measure (Plane × Plane)) (hC : Measurable C)
    (hClf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (C ω))
    (φ : (Fin n → Measure (Plane × Plane)) → Measure (Plane × Plane)) (hφ : Measurable φ)
    (hFactor : C =ᵐ[P] fun ω => φ (fun i => B i.castSucc ω))
    (u : ℕ → Plane → ℝ) (hu : ∀ k, Measurable (u k))
    (w : Plane → ℝ) (hw : Measurable w) (F : Plane × Plane → ℝ) (hF : Measurable F) :
    P.map (fun ω =>
      ((∫ p, F p ∂chainProduct (fun k => B (Fin.ofNat (n + 1) k) ω) u n),
        ∫ p, F p ∂smoothedProductMeasure (C ω) w (B (Fin.last n) ω))) =
    (P.prod P).map (fun ω : Ω × Ω =>
      ((∫ p, F p ∂chainProduct (fun k => Fin.snoc (α := fun _ : Fin (n + 1) => Measure (Plane × Plane))
          (fun i => B i.castSucc ω.2) (B (Fin.last n) ω.1) (Fin.ofNat (n + 1) k)) u n),
        ∫ p, F p ∂smoothedProductMeasure (C ω.2) w (B (Fin.last n) ω.1))) := by
  classical
  let E := CompactExhaustion.choice (Plane × Plane)
  let D (ω : Ω × Ω) := Fin.snoc (α := fun _ : Fin (n + 1) => Measure (Plane × Plane))
    (fun i => B i.castSucc ω.2) (B (Fin.last n) ω.1)
  let Ψ (q : (Fin (n + 1) → Measure (Plane × Plane)) × Measure (Plane × Plane)) :=
    (modifiedChainReadout E n u F q.1,
      modifiedTwoBlockReadout E w F (q.2, q.1 (Fin.last n)))
  have hΨ : Measurable Ψ :=
    ((measurable_modifiedChainReadout E n u hu F hF).comp measurable_fst).prodMk
      ((measurable_modifiedTwoBlockReadout E w hw F hF).comp
        (measurable_snd.prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_fst)))
  have hDm : Measurable D := measurable_fin_snoc_prod (B (Fin.last n)) (fun i : Fin n => B i.castSucc)
    (hB _) (fun i => hB _)
  have hSrcm : Measurable (fun ω => ((fun i => B i ω), C ω)) := (Measurable.of_eval hB).prodMk hC
  have hTgtm : Measurable (fun ω : Ω × Ω => (D ω, C ω.2)) := hDm.prodMk (hC.comp measurable_snd)
  have hMap := congrArg (fun ν : Measure ((Fin (n + 1) → Measure (Plane × Plane)) × Measure (Plane × Plane)) => ν.map Ψ)
    (iIndepFun.map_eq_map_snoc_prod_with_factor P n B hB hind C φ hφ hFactor)
  rw [Measure.map_map hΨ hSrcm, Measure.map_map hΨ hTgtm] at hMap
  have hBgood : ∀ᵐ ω ∂P, ∀ i, IsLocallyFiniteMeasure (B i ω) := ae_all_iff.2 hBlf
  have hDgood : ∀ᵐ ω : Ω × Ω ∂P.prod P, ∀ i, IsLocallyFiniteMeasure (D ω i) := by
    filter_upwards [(measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).quasiMeasurePreserving.ae hBgood,
      (measurePreserving_snd : MeasurePreserving Prod.snd (P.prod P) P).quasiMeasurePreserving.ae hBgood]
      with ω hω₁ hω₂
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [D, Fin.snoc_last] using hω₁ (Fin.last n)
    · simpa only [D, Fin.snoc_castSucc] using hω₂ j.castSucc
  have hSrc : (fun ω =>
      ((∫ p, F p ∂chainProduct (fun k => B (Fin.ofNat (n + 1) k) ω) u n),
        ∫ p, F p ∂smoothedProductMeasure (C ω) w (B (Fin.last n) ω))) =ᵐ[P]
      Ψ ∘ (fun ω => ((fun i => B i ω), C ω)) := by
    filter_upwards [hBgood, hClf] with ω hω hωC
    let : IsLocallyFiniteMeasure (C ω) := hωC
    let : IsLocallyFiniteMeasure (B (Fin.last n) ω) := hω _
    change (_, _) = (modifiedChainReadout E n u F (fun i => B i ω),
      modifiedTwoBlockReadout E w F (C ω, B (Fin.last n) ω))
    rw [modifiedChainReadout_eq_finiteBlocks E n _ hω, modifiedTwoBlockReadout_eq_of_locallyFinite E]
  have hTgt : (fun ω : Ω × Ω =>
      ((∫ p, F p ∂chainProduct (fun k => D ω (Fin.ofNat (n + 1) k)) u n),
        ∫ p, F p ∂smoothedProductMeasure (C ω.2) w (B (Fin.last n) ω.1))) =ᵐ[P.prod P]
      Ψ ∘ (fun ω : Ω × Ω => (D ω, C ω.2)) := by
    filter_upwards [hDgood,
      (measurePreserving_snd : MeasurePreserving Prod.snd (P.prod P) P).quasiMeasurePreserving.ae hClf]
      with ω hω hωC
    let : IsLocallyFiniteMeasure (C ω.2) := hωC
    have hLast : D ω (Fin.last n) = B (Fin.last n) ω.1 := Fin.snoc_last _ _
    let : IsLocallyFiniteMeasure (B (Fin.last n) ω.1) := hLast ▸ hω _
    change (_, _) = (modifiedChainReadout E n u F (D ω),
      modifiedTwoBlockReadout E w F (C ω.2, D ω (Fin.last n)))
    rw [modifiedChainReadout_eq_finiteBlocks E n _ hω, hLast, modifiedTwoBlockReadout_eq_of_locallyFinite E]
  rw [Measure.map_congr hSrc, Measure.map_congr hTgt]
  exact hMap

end Critical2DKPZ.SHF.Tsai

end
