/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactComposition
public import Critical2DKPZ.SHF.Tsai.ChainEndpointApproximation
public import Critical2DKPZ.SHF.Tsai.TensorEndpointDensity

/-! # Approximate composition on `L²` endpoint tensors

The compact-test composition axiom extends to all `L²` endpoint representatives by uniform
integrable second-moment bounds in both endpoints, without additional measurability
assumptions on the representatives.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Consecutive increments over three dense times are independent. -/
theorem IsDenseSHF.iIndepFun_twoConsecutive {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) {t₀ t₁ t₂ : ℝ}
    (h₀ : t₀ ∈ D) (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D) (h₀₁ : t₀ < t₁) (h₁₂ : t₁ < t₂) :
    iIndepFun (fun k : Fin 2 => if (k : ℕ) = 0 then Z t₀ t₁ else Z t₁ t₂) P := by
  let t : Fin 3 → ℝ := ![t₀, t₁, t₂]
  have ht : StrictMono t := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    fin_cases i
    · exact h₀₁
    · exact h₁₂
  have htD (i : Fin 3) : t i ∈ D := by
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  have h := hZ.2.2.1 2 t ht htD
  have heq : (fun i : Fin 2 => Z (t i.castSucc) (t i.succ)) =
      (fun k : Fin 2 => if (k : ℕ) = 0 then Z t₀ t₁ else Z t₁ t₂) := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

/-- The compact-test composition axiom extends to arbitrary `L²` endpoint tensors
by uniform integrable second-moment approximation in both endpoints. -/
theorem tendstoInMeasure_smoothedProductPairing_tensor (θ : ℝ) (D : Set ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    {t₀ t₁ t₂ : ℝ} (h₀ : t₀ ∈ D) (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D) (h₀₁ : t₀ < t₁) (h₁₂ : t₁ < t₂)
    (w : ℕ → Plane → ℝ) (hw : IsL2ApplicableMollifier w)
    (hwP : ∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω))
    (hconv : ∀ f : C_c(Plane × Plane, ℝ),
      TendstoInMeasure P (fun ℓ ω => smoothedProductPairing (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω) f -
        ∫ p, f p ∂(Z t₀ t₂ ω)) atTop (fun _ => 0))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    TendstoInMeasure P (fun ℓ ω => (∫ p, g p.1 * g' p.2 ∂(smoothedProductMeasure (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω))) -
        ∫ p, g p.1 * g' p.2 ∂(Z t₀ t₂ ω)) atTop (fun _ => 0) := by
  classical
  let B (k : ℕ) := if k = 0 then Z t₀ t₁ else Z t₁ t₂
  let τ (k : ℕ) := if k = 0 then t₁ - t₀ else t₂ - t₁
  have hτ (k : ℕ) (_ : k ≤ 1) : 0 < τ k := by
    dsimp only [τ]
    split_ifs <;> linarith only [h₀₁, h₁₂]
  have hB (k : ℕ) (_ : k ≤ 1) : HasDeltaBoseMoments θ (τ k) P (B k) := by
    dsimp only [B, τ]
    split_ifs
    · exact hZ.hasDeltaBoseMoments h₀ h₁ h₀₁
    · exact hZ.hasDeltaBoseMoments h₁ h₂ h₁₂
  have hind : iIndepFun (fun k : Fin (1 + 1) => B k) P :=
    hZ.iIndepFun_twoConsecutive h₀ h₁ h₂ h₀₁ h₁₂
  obtain ⟨CL, _, hCL⟩ := exists_chainPairing_sub_left_sq_bound 1 τ hτ B hB hind
    (fun _ => w) (fun _ => hw)
  obtain ⟨CR, _, hCR⟩ := exists_chainPairing_sub_right_sq_bound 1 τ hτ B hB hind
    (fun _ => w) (fun _ => hw)
  simp only [chainProduct, B, ite_eq_left (show (0 : ℕ) = 0 from rfl),
    ite_eq_right (by norm_num : (1 : ℕ) ≠ 0)] at hCL hCR
  let L : ℕ → Ω → Measure (Plane × Plane) := fun _ => Z t₀ t₂
  let κ : ℕ → ℝ := fun _ => t₂ - t₀
  have hκ (k : ℕ) (_ : k ≤ 0) : 0 < κ k := sub_pos.mpr (h₀₁.trans h₁₂)
  have hL (k : ℕ) (_ : k ≤ 0) : HasDeltaBoseMoments θ (κ k) P (L k) :=
    hZ.hasDeltaBoseMoments h₀ h₂ (h₀₁.trans h₁₂)
  have hindL : iIndepFun (fun k : Fin (0 + 1) => L k) P := by
    let : Subsingleton (Fin (0 + 1)) := ⟨fun i j => Fin.ext (by omega)⟩
    exact iIndepFun.of_subsingleton
  obtain ⟨DL, _, hDL⟩ := exists_chainPairing_sub_left_sq_bound 0 κ hκ L hL hindL
    (fun _ => w) (fun _ => hw)
  obtain ⟨DR, _, hDR⟩ := exists_chainPairing_sub_right_sq_bound 0 κ hκ L hL hindL
    (fun _ => w) (fun _ => hw)
  simp only [chainProduct, L] at hDL hDR
  let F (a b : Plane → ℝ) (ℓ : ℕ) (ω : Ω) :=
    ∫ p, a p.1 * b p.2 ∂smoothedProductMeasure (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)
  let G (a b : Plane → ℝ) (ω : Ω) := ∫ p, a p.1 * b p.2 ∂Z t₀ t₂ ω
  have hc (a b : C_c(Plane, ℝ)) : TendstoInMeasure P (F a b) atTop (G a b) := by
    have h := tendstoInMeasure_smoothedProductPairing_compactTensor θ D P Z hZ
      h₀ h₁ h₂ h₀₁ h₁₂ w hw hwP hconv a b
    simpa only [tendstoInMeasure_iff_norm, Pi.zero_apply, sub_zero] using h
  have hfull := tendstoInMeasure_of_compact_tensor_endpoints P F G CL CR DL DR
    (fun a b c ha hb hc n => hCL n a b c ha hb hc)
    (fun a b c ha hb hc n => hCR n a b c ha hb hc)
    (fun a b c ha hb hc => hDL 0 a b c ha hb hc)
    (fun a b c ha hb hc => hDR 0 a b c ha hb hc) hc g g' hg hg'
  simpa only [tendstoInMeasure_iff_norm, Pi.zero_apply, sub_zero] using hfull

end Critical2DKPZ.SHF.Tsai

end
