/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SignedChainMoments
public import Critical2DKPZ.SHF.Tsai.FourthMomentCancellation

/-! # Fourth-moment Cauchy convergence of endpoint chains

Two applicable connector families have vanishing fourth moment of their pairing
difference, with integrability of every fourth-power error.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Two applicable connector families have vanishing fourth-moment difference;
every fourth-power error is integrable. -/
theorem tendsto_integral_chainProduct_sub_pow_four {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (u v : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k))
    (hv : ∀ k, IsL2ApplicableMollifier (v k))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    (∀ ℓ, Integrable (fun ω => ((∫ p, g p.1 * g' p.2 ∂(chainProduct (fun k => B k ω) (fun k => u k ℓ) K)) -
        ∫ p, g p.1 * g' p.2 ∂(chainProduct (fun k => B k ω) (fun k => v k ℓ) K)) ^ 4) P) ∧
    Tendsto (fun ℓ => ∫ ω, ((∫ p, g p.1 * g' p.2 ∂(chainProduct (fun k => B k ω) (fun k => u k ℓ) K)) -
        ∫ p, g p.1 * g' p.2 ∂(chainProduct (fun k => B k ω) (fun k => v k ℓ) K)) ^ 4 ∂P) atTop (𝓝 0) := by
  classical
  let a (ℓ : ℕ) (ω : Ω) := ∫ p, g p.1 * g' p.2
    ∂chainProduct (fun k => B k ω) (fun k => u k ℓ) K
  let b (ℓ : ℕ) (ω : Ω) := ∫ p, g p.1 * g' p.2
    ∂chainProduct (fun k => B k ω) (fun k => v k ℓ) K
  let W (S : Finset (Fin 4)) (i : Fin 4) (k ℓ : ℕ) : Plane → ℝ :=
    if i ∈ S then v k ℓ else u k ℓ
  have hW (S) (i) (k) : IsL2ApplicableMollifier (W S i k) := by
    by_cases hi : i ∈ S
    · have heq : W S i k = v k := by funext ℓ x; simp only [W, ite_eq_left hi]
      rw [heq]
      exact hv k
    · have heq : W S i k = u k := by funext ℓ x; simp only [W, ite_eq_right hi]
      rw [heq]
      exact hu k
  have hpair (S : Finset (Fin 4)) (i : Fin 4) (ℓ : ℕ) (ω : Ω) :
      (∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => W S i k ℓ) K) =
        if i ∈ S then b ℓ ω else a ℓ ω := by
    by_cases hi : i ∈ S
    · have heq : (fun k => W S i k ℓ) = fun k => v k ℓ := by
        funext k
        exact ite_eq_left hi
      rw [heq, ite_eq_left hi]
    · have heq : (fun k => W S i k ℓ) = fun k => u k ℓ := by
        funext k
        exact ite_eq_right hi
      rw [heq, ite_eq_right hi]
  have hmix (S : Finset (Fin 4)) (ℓ : ℕ) :
      (fun ω => fourthMixedProduct S (a ℓ ω) (b ℓ ω)) =
        fun ω => ∏ i : Fin 4, ∫ p, g p.1 * g' p.2
          ∂chainProduct (fun k => B k ω) (fun k => W S i k ℓ) K := by
    funext ω
    simp only [fourthMixedProduct, hpair]
  have hform (S : Finset (Fin 4)) (ℓ : ℕ) :=
    integral_prod_chainProduct_eq K τ hτ B hB hind (n := 4) (by norm_num) (by norm_num)
      (W S) (hW S) ℓ (fun _ => g) (fun _ => g') (fun _ => hg) (fun _ => hg')
  have hI (S : Finset (Fin 4)) (ℓ : ℕ) :
      Integrable (fun ω => fourthMixedProduct S (a ℓ ω) (b ℓ ω)) P := by
    rw [hmix]
    exact (hform S ℓ).2.1
  let Kb (k : ℕ) := momentKernel 4 θ (τ k)
  have hKb (k) : Measurable (Function.uncurry (Kb k)) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration 4 × Configuration 4 =>
        momentKernel 4 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration 4 × Configuration 4 => ((θ, τ k), q))
      (measurable_momentKernel 4) (measurable_const.prodMk measurable_id)
  obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel 4 θ
  let c (k : ℕ) := ENNReal.ofReal (C * Real.exp (rate * τ k) * min (τ k) 1 ^ (-(4 : ℝ)))
  have hc (k : ℕ) (_ : k ≤ K) : c k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKF (k : ℕ) (hk : k ≤ K) : FormBound volume volume (Kb k) (c k) :=
    hC θ le_rfl (τ k) (hτ k hk)
  let G (x : Configuration 4) := ∏ i, g (x i)
  let F (y : Configuration 4) := ∏ i, g' (y i)
  have hG : MemLp G 2 := memLp_configuration_tensor (fun _ : Fin 4 => g) (fun _ => hg)
  have hF : MemLp F 2 := memLp_configuration_tensor (fun _ : Fin 4 => g') (fun _ => hg')
  let L := ∫ x : Configuration 4, ∫ y : Configuration 4,
    G x * (chainKernelLimit 4 Kb K x y).toReal * F y
  have hmoment (S : Finset (Fin 4)) (ℓ : ℕ) :
      (∫ ω, fourthMixedProduct S (a ℓ ω) (b ℓ ω) ∂P) =
        ∫ x : Configuration 4, ∫ y : Configuration 4,
          G x * (chainKernel 4 Kb (fun i k => W S i k ℓ) K x y).toReal * F y := by
    rw [hmix]
    exact (hform S ℓ).2.2
  have hlim (S : Finset (Fin 4)) :
      Tendsto (fun ℓ => ∫ ω, fourthMixedProduct S (a ℓ ω) (b ℓ ω) ∂P) atTop (𝓝 L) := by
    have h := tendsto_integral_chainKernel K Kb (fun k _ => hKb k) c hc hKF (W S) (hW S) G F hG hF
    simpa only [hmoment] using h
  exact tendsto_integral_sub_pow_four_of_mixed P a b L hI hlim

end Critical2DKPZ.SHF.Tsai

end
