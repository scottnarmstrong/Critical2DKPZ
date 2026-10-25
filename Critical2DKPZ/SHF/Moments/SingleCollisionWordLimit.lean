/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitDiagram
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # One-letter tested word limits from the pair limit -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

private def wordLimitPairSpectatorIndexEquiv {h : ℕ} (α : CollisionPair h) :
    Fin 2 ⊕ Spectator α ≃ Fin h where
  toFun
    | Sum.inl j => if j = 0 then α.1.1 else α.1.2
    | Sum.inr i => i.1
  invFun i :=
    if h₀ : i = α.1.1 then Sum.inl 0
    else if h₁ : i = α.1.2 then Sum.inl 1
    else Sum.inr ⟨i, h₀, h₁⟩
  left_inv := by
    rintro (j | i)
    · have h21 : α.1.2 ≠ α.1.1 := ne_of_gt α.2
      fin_cases j <;> simp [h21]
    · simp [i.2.1, i.2.2]
  right_inv i := by
    by_cases h₀ : i = α.1.1
    · simp [h₀]
    · by_cases h₁ : i = α.1.2
      · have h21 : α.1.2 ≠ α.1.1 := ne_of_gt α.2
        simp [h₁, h21]
      · simp [h₀, h₁]

private noncomputable def wordLimitPairSpectatorConfigEquiv {h : ℕ} (α : CollisionPair h) :
    Configuration h ≃ᵐ Configuration 2 × (Spectator α → Plane) := by
  let e := wordLimitPairSpectatorIndexEquiv α
  exact (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Spectator α => Plane) e.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Spectator α => Plane))

private theorem wordLimitPairSpectatorConfigEquiv_apply {h : ℕ} (α : CollisionPair h)
    (x : Configuration h) :
    wordLimitPairSpectatorConfigEquiv α x =
      (pairRestrict α x, fun i : Spectator α => x i.1) := by
  classical
  let e := wordLimitPairSpectatorIndexEquiv α
  change MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin 2 ⊕ Spectator α => Plane)
    (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Spectator α => Plane) e.symm x) = _
  have hpi :
      MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Spectator α => Plane) e.symm x =
        fun j => x (e j) := by
    funext j
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin 2 ⊕ Spectator α => Plane) e.symm x (e j)
    simpa using h
  rw [hpi]
  change (fun j : Fin 2 => x (e (Sum.inl j)),
      fun i : Spectator α => x (e (Sum.inr i))) = _
  apply Prod.ext
  · funext j
    fin_cases j <;> simp [e, wordLimitPairSpectatorIndexEquiv, pairRestrict]
  · funext i
    simp [e, wordLimitPairSpectatorIndexEquiv]

private theorem measurePreserving_wordLimitPairSpectatorConfigEquiv {h : ℕ}
    (α : CollisionPair h) : MeasurePreserving (wordLimitPairSpectatorConfigEquiv α) := by
  let e := wordLimitPairSpectatorIndexEquiv α
  exact (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin 2 ⊕ Spectator α => Plane)).comp
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin 2 ⊕ Spectator α => Plane) e.symm)

private theorem wordLimit_planePair_integral {τ : ℝ}
    (φ : C_c(Plane × Plane, ℝ)) :
    (∫ x : Plane, ∫ y : Plane,
      φ (x, y) * heatKernel τ (y - x)) =
      ∫ p : Plane × Plane, φ p * heatKernel τ (p.2 - p.1) := by
  let g : Plane × Plane → ℝ := fun p => φ p * heatKernel τ (p.2 - p.1)
  have hcont : Continuous g := by
    exact φ.continuous.mul ((continuous_heatKernel τ).comp
      (continuous_snd.sub continuous_fst))
  have hcs : HasCompactSupport g :=
    φ.hasCompactSupport.mul_right
  have hInt : Integrable g := hcont.integrable_of_hasCompactSupport hcs
  have hprod := integral_prod g hInt
  rw [← Measure.volume_eq_prod Plane Plane] at hprod
  exact hprod.symm

private theorem wordLimit_freeTest_integral (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (φ : C_c(Plane × Plane, ℝ)) :
    (∫ x : Configuration 1, ∫ y : Configuration 1,
      (∏ _ : Fin 1, φ (x 0, y 0)) *
        (diagramKernel θ [] τ x y).toReal) =
      ∫ p : Plane × Plane, φ p * heatKernel τ (p.2 - p.1) := by
  let g : Plane × Plane → ℝ := fun p => φ p * heatKernel τ (p.2 - p.1)
  have hcont : Continuous g := by
    exact φ.continuous.mul ((continuous_heatKernel τ).comp
      (continuous_snd.sub continuous_fst))
  have hcs : HasCompactSupport g := φ.hasCompactSupport.mul_right
  have hInt : Integrable g := hcont.integrable_of_hasCompactSupport hcs
  let e : Configuration 1 ≃ᵐ Plane := MeasurableEquiv.piUnique (fun _ : Fin 1 => Plane)
  have hmp : MeasurePreserving e := volume_preserving_piUnique _
  have hmpProd : MeasurePreserving (e.prodCongr e) := hmp.prod hmp
  have hcompInt : Integrable (fun q : Configuration 1 × Configuration 1 =>
      g ((e.prodCongr e) q)) := hmpProd.integrable_comp_of_integrable hInt
  have hpoint (x : Configuration 1) (y : Configuration 1) :
      (∏ _ : Fin 1, φ (x 0, y 0)) *
          (diagramKernel θ [] τ x y).toReal =
        g ((e.prodCongr e) (x, y)) := by
    have hexy : (e.prodCongr e) (x, y) = (x 0, y 0) := by
      apply Prod.ext <;>
        simp [e, MeasurableEquiv.prodCongr, MeasurableEquiv.piUnique, Equiv.piUnique]
    rw [hexy]
    simp [g, diagramKernel, freeKernel,
      ENNReal.toReal_ofReal, heatKernel_nonneg hτ.le]
  have htargetInt : Integrable (fun q : Configuration 1 × Configuration 1 =>
      (∏ _ : Fin 1, φ (q.1 0, q.2 0)) * (diagramKernel θ [] τ q.1 q.2).toReal) := by
    apply hcompInt.congr
    exact Filter.Eventually.of_forall fun q => (hpoint q.1 q.2).symm
  calc
    _ = ∫ q : Configuration 1 × Configuration 1,
          (∏ _ : Fin 1, φ (q.1 0, q.2 0)) *
            (diagramKernel θ [] τ q.1 q.2).toReal := by
      simpa only [Measure.volume_eq_prod] using
        (integral_prod _ htargetInt).symm
    _ = ∫ q : Configuration 1 × Configuration 1, g ((e.prodCongr e) q) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => hpoint q.1 q.2
    _ = ∫ p : Plane × Plane, g p := hmpProd.integral_comp' g

private theorem wordLimit_single_diagram_integral_factorization (ϑ : ℝ) {h : ℕ}
    (α : CollisionPair h) {s t : ℝ} (hst : s < t)
    (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    (∫ x : Configuration h, ∫ y : Configuration h,
      (∏ i, φ i (x i, y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) [α] (t - s) x y).toReal) =
      (∫ p : Configuration 2, ∫ q : Configuration 2,
        (∏ j, (pairRestrict α φ) j (p j, q j)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) [pairTwo] (t - s) p q).toReal) *
        ∏ i : Spectator α, ∫ p : Plane × Plane,
          φ i.1 p * heatKernel (t - s) (p.2 - p.1) := by
  classical
  let θ := ϑ - Real.eulerMascheroniConstant
  let τ := t - s
  let A : Configuration 2 → Configuration 2 → ℝ := fun p q =>
    (∏ j, (pairRestrict α φ) j (p j, q j)) * (diagramKernel θ [pairTwo] τ p q).toReal
  let B : (Spectator α → Plane) → (Spectator α → Plane) → ℝ := fun z w =>
    ∏ i : Spectator α, φ i.1 (z i, w i) * heatKernel τ (w i - z i)
  have hsplit (x y : Configuration h) :
      (∏ i, φ i (x i, y i)) * (diagramKernel θ [α] τ x y).toReal =
        A (wordLimitPairSpectatorConfigEquiv α x).1 (wordLimitPairSpectatorConfigEquiv α y).1 *
          B (wordLimitPairSpectatorConfigEquiv α x).2 (wordLimitPairSpectatorConfigEquiv α y).2 := by
    rw [wordLimitPairSpectatorConfigEquiv_apply, wordLimitPairSpectatorConfigEquiv_apply,
      diagramKernel_single_eq]
    rw [ENNReal.toReal_mul]
    have htoReal (i : Spectator α) :
        (ENNReal.ofReal (heatKernel τ (y i.1 - x i.1))).toReal =
          heatKernel τ (y i.1 - x i.1) :=
      ENNReal.toReal_ofReal (heatKernel_nonneg (sub_nonneg.mpr hst.le) _)
    have htest :
        (∏ i : Fin h, φ i (x i, y i)) =
          (∏ j : Fin 2,
            (pairRestrict α φ) j (pairRestrict α x j, pairRestrict α y j)) *
            ∏ i : Spectator α, φ i.1 (x i.1, y i.1) := by
      calc
        _ = (∏ j : Fin 2,
              φ (if j = 0 then α.1.1 else α.1.2)
                (x (if j = 0 then α.1.1 else α.1.2),
                  y (if j = 0 then α.1.1 else α.1.2))) *
              ∏ i : Spectator α, φ i.1 (x i.1, y i.1) :=
          wordLimit_prod_pair_spectators α (fun i => φ i (x i, y i))
        _ = _ := by
          congr 1
    have hspec :
        (∏ i : Spectator α, φ i.1 (x i.1, y i.1)) *
          ∏ i : Spectator α, heatKernel τ (y i.1 - x i.1) =
        ∏ i : Spectator α,
          φ i.1 (x i.1, y i.1) * heatKernel τ (y i.1 - x i.1) := by
      rw [← Finset.prod_mul_distrib]
    simp only [A, B, htoReal, ENNReal.toReal_prod]
    rw [htest, ← hspec]
    ring

  have hinner (x : Configuration h) :
      (∫ y : Configuration h,
        (∏ i, φ i (x i, y i)) * (diagramKernel θ [α] τ x y).toReal) =
      (∫ q : Configuration 2, A (pairRestrict α x) q) *
        ∫ w : Spectator α → Plane, B (fun i => x i.1) w := by
    calc
      _ = ∫ q : Configuration 2 × (Spectator α → Plane),
          A (pairRestrict α x) q.1 * B (fun i => x i.1) q.2 := by
        calc
          _ = ∫ y : Configuration h,
              A (pairRestrict α x) (wordLimitPairSpectatorConfigEquiv α y).1 *
                B (fun i => x i.1) (wordLimitPairSpectatorConfigEquiv α y).2 := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun y => by
                simpa only [wordLimitPairSpectatorConfigEquiv_apply] using hsplit x y
          _ = _ :=
            (measurePreserving_wordLimitPairSpectatorConfigEquiv α).integral_comp'
              (fun q => A (pairRestrict α x) q.1 * B (fun i => x i.1) q.2)
      _ = _ := by
        exact integral_prod_mul (fun q => A (pairRestrict α x) q)
          (fun w => B (fun i => x i.1) w)

  calc
    _ = ∫ x : Configuration h,
          ((∫ q : Configuration 2, A (pairRestrict α x) q) *
            ∫ w : Spectator α → Plane, B (fun i => x i.1) w) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    _ = (∫ p : Configuration 2, ∫ q : Configuration 2, A p q) *
          ∫ z : Spectator α → Plane, ∫ w : Spectator α → Plane, B z w := by
      calc
        _ = ∫ x : Configuration h,
            (∫ q : Configuration 2, A (wordLimitPairSpectatorConfigEquiv α x).1 q) *
              ∫ w : Spectator α → Plane, B (wordLimitPairSpectatorConfigEquiv α x).2 w := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              simp only [wordLimitPairSpectatorConfigEquiv_apply]
        _ = ∫ pz : Configuration 2 × (Spectator α → Plane),
            (∫ q : Configuration 2, A pz.1 q) *
              ∫ w : Spectator α → Plane, B pz.2 w :=
            (measurePreserving_wordLimitPairSpectatorConfigEquiv α).integral_comp'
              (fun pz => (∫ q : Configuration 2, A pz.1 q) *
                ∫ w : Spectator α → Plane, B pz.2 w)
        _ = _ := by
          exact integral_prod_mul
            (fun p => ∫ q : Configuration 2, A p q)
            (fun z => ∫ w : Spectator α → Plane, B z w)
    _ = _ := by
      dsimp [A, B, θ, τ]
      have hInner (z : Spectator α → Plane) :
          (∫ w : Spectator α → Plane,
            ∏ i : Spectator α, φ i.1 (z i, w i) *
              heatKernel (t - s) (w i - z i)) =
            ∏ i : Spectator α, ∫ w : Plane,
              φ i.1 (z i, w) * heatKernel (t - s) (w - z i) :=
        integral_fintype_prod_volume_eq_prod
          (fun (i : Spectator α) w => φ i.1 (z i, w) * heatKernel (t - s) (w - z i))
      have hOuter :
          (∫ z : Spectator α → Plane,
            ∏ i : Spectator α, ∫ w : Plane,
              φ i.1 (z i, w) * heatKernel (t - s) (w - z i)) =
            ∏ i : Spectator α, ∫ z : Plane, ∫ w : Plane,
              φ i.1 (z, w) * heatKernel (t - s) (w - z) :=
        integral_fintype_prod_volume_eq_prod
          (fun (i : Spectator α) z => ∫ w : Plane,
            φ i.1 (z, w) * heatKernel (t - s) (w - z))
      rw [show (∫ z : Spectator α → Plane, ∫ w : Spectator α → Plane,
          ∏ i : Spectator α, φ i.1 (z i, w i) * heatKernel (t - s) (w i - z i)) =
          ∫ z : Spectator α → Plane, ∏ i : Spectator α, ∫ w : Plane,
            φ i.1 (z i, w) * heatKernel (t - s) (w - z i) from by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hInner]
      rw [hOuter]
      apply congrArg (fun r : ℝ =>
        (∫ p : Configuration 2, ∫ q : Configuration 2,
          (∏ j, (pairRestrict α φ) j (p j, q j)) *
            (diagramKernel (ϑ - Real.eulerMascheroniConstant) [pairTwo] (t - s) p q).toReal) * r)
      apply Finset.prod_congr rfl
      intro (i : Spectator α) hi
      exact wordLimit_planePair_integral (φ i.1)

/-- Every one-letter tested word at arbitrary replica count converges when the two-particle limit holds. -/
theorem testedBlockWord_tendsto_single_of (ϑ : ℝ) (hP : PairTwoWordLimit ϑ) {h : ℕ}
    (α : CollisionPair h) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (sN tN : ℕ → ℝ)
    (hsN : Tendsto sN atTop (𝓝 s)) (htN : Tendsto tN atTop (𝓝 t)) (hsN0 : ∀ N, 0 ≤ sN N)
    (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    Tendsto (fun N => testedBlockWord ϑ N (sN N) (tN N) φ [α]) atTop
      (𝓝 (∫ x : Configuration h, ∫ y : Configuration h,
        (∏ i, φ i (x i, y i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) [α] (t - s) x y).toReal)) := by
  have hpair := hP hs hst sN tN hsN htN hsN0 (pairRestrict α φ)
  have hfree (i : Spectator α) :=
    testedBlockWord_tendsto_nil ϑ hs hst sN tN hsN htN hsN0
      (fun _ : Fin 1 => φ i.1)
  have hfreeProd : Tendsto
      (fun N => ∏ i : Spectator α,
        testedBlockWord ϑ N (sN N) (tN N) (fun _ : Fin 1 => φ i.1) []) atTop
      (𝓝 (∏ i : Spectator α,
        ∫ x : Configuration 1, ∫ y : Configuration 1,
          (∏ _ : Fin 1, φ i.1 (x 0, y 0)) *
            (diagramKernel (ϑ - Real.eulerMascheroniConstant) [] (t - s) x y).toReal)) := by
    exact tendsto_finsetProd Finset.univ (fun i hi => hfree i)
  have htarget :
      (∫ x : Configuration h, ∫ y : Configuration h,
        (∏ i, φ i (x i, y i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) [α] (t - s) x y).toReal) =
        (∫ x : Configuration 2, ∫ y : Configuration 2,
          (∏ j, (pairRestrict α φ) j (x j, y j)) *
            (diagramKernel (ϑ - Real.eulerMascheroniConstant) [pairTwo] (t - s) x y).toReal) *
          ∏ i : Spectator α,
            ∫ x : Configuration 1, ∫ y : Configuration 1,
              (∏ _ : Fin 1, φ i.1 (x 0, y 0)) *
                (diagramKernel (ϑ - Real.eulerMascheroniConstant) [] (t - s) x y).toReal := by
    rw [wordLimit_single_diagram_integral_factorization ϑ α hst φ]
    apply congrArg (fun r : ℝ =>
      (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ j, (pairRestrict α φ) j (x j, y j)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) [pairTwo] (t - s) x y).toReal) * r)
    apply Finset.prod_congr rfl
    intro (i : Spectator α) hi
    exact (wordLimit_freeTest_integral (ϑ - Real.eulerMascheroniConstant)
      (sub_pos.mpr hst) (φ i.1)).symm
  rw [htarget]
  have hseq : ∀ N, testedBlockWord ϑ N (sN N) (tN N) φ [α] =
      testedBlockWord ϑ N (sN N) (tN N) (pairRestrict α φ) [pairTwo] *
        ∏ i : Spectator α,
          testedBlockWord ϑ N (sN N) (tN N) (fun _ : Fin 1 => φ i.1) [] := by
    intro N
    exact testedBlockWord_single_eq ϑ N (sN N) (tN N) α φ
  have hmul := hpair.mul hfreeProd
  apply hmul.congr'
  filter_upwards with N
  rw [hseq N]

end Critical2DKPZ.SHF.Moments

end
