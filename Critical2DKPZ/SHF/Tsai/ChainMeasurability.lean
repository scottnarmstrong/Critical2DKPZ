/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Products
public import Critical2DKPZ.SHF.Tsai.MeasureKernels
import Mathlib.Probability.Kernel.Composition.Prod

/-! # Measurable random endpoint chains

S-finite kernels are closed under product, finite density and push-forward.
This proves measurability of the literal endpoint chain without assuming
that its intermediate measures are locally finite.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A chain depends only on the input measures through its last block. -/
theorem chainProduct_congr_prefix (K : ℕ) (μ ν : ℕ → Measure (Plane × Plane))
    (h : ∀ k ≤ K, μ k = ν k) (w : ℕ → Plane → ℝ) : chainProduct μ w K = chainProduct ν w K := by
  induction K with
  | zero => exact h 0 (by omega)
  | succ K ih =>
    simp only [chainProduct]
    rw [ih (fun k hk => h k (by omega)), h (K + 1) le_rfl]

/-- The actual endpoint chain is represented by an s-finite measurable kernel. -/
theorem exists_chainProductKernel {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℕ → Kernel Ω (Plane × Plane)) (hκ : ∀ k, IsSFiniteKernel (κ k))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k)) (K : ℕ) :
    ∃ η : Kernel Ω (Plane × Plane), IsSFiniteKernel η ∧
      ∀ ω, η ω = chainProduct (fun k => κ k ω) w K := by
  induction K with
  | zero => exact ⟨κ 0, hκ 0, fun _ => rfl⟩
  | succ K ih =>
    obtain ⟨η, hη, hηeq⟩ := ih
    let : IsSFiniteKernel η := hη
    let : IsSFiniteKernel (κ (K + 1)) := hκ (K + 1)
    let ζ := η.prod (κ (K + 1))
    let ρ := ζ.withDensity (fun _ q => ENNReal.ofReal (w K (q.1.2 - q.2.1)))
    have hρ : IsSFiniteKernel ρ :=
      Kernel.IsSFiniteKernel.withDensity ζ (fun _ _ => ENNReal.ofReal_ne_top)
    let : IsSFiniteKernel ρ := hρ
    refine ⟨ρ.map (fun q => (q.1.1, q.2.2)), inferInstance, ?_⟩
    intro ω
    rw [Kernel.map_apply _ (by fun_prop)]
    rw [show ρ ω = (ζ ω).withDensity (fun q => ENNReal.ofReal (w K (q.1.2 - q.2.1))) from
      Kernel.withDensity_apply ζ (by fun_prop) ω]
    rw [show ζ ω = (η ω).prod (κ (K + 1) ω) from Kernel.prod_apply _ _ _, hηeq ω]
    rfl

/-- A chain of measurable, everywhere locally finite input blocks is measurable as a measure map. -/
theorem measurable_chainProduct {Ω : Type*} [MeasurableSpace Ω] (K : ℕ)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ ω, ∀ k ≤ K, IsLocallyFiniteMeasure (B k ω))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k)) :
    Measurable (fun ω => chainProduct (fun k => B k ω) w K) := by
  classical
  let κ (k : ℕ) : Kernel Ω (Plane × Plane) :=
    if hk : k ≤ K then ⟨B k, hB k hk⟩ else 0
  have hκ : ∀ k, IsSFiniteKernel (κ k) := by
    intro k
    dsimp only [κ]
    split_ifs with hk
    · apply isSFiniteKernel_of_locallyFinite
      exact fun ω => hlf ω k hk
    · infer_instance
  obtain ⟨η, _, hη⟩ := exists_chainProductKernel κ hκ w hw K
  have hcongr (ω : Ω) : η ω = chainProduct (fun k => B k ω) w K := by
    rw [hη ω]
    apply chainProduct_congr_prefix
    intro k hk
    simp only [κ, dite_eq_left hk]
    rfl
  have heq : (fun ω => chainProduct (fun k => B k ω) w K) = η := by
    funext ω
    exact (hcongr ω).symm
  rw [heq]
  exact η.measurable

/-- The exact positive-pairing measurability statement of dense-time uniqueness. -/
theorem measurable_lintegral_chainProduct {Ω : Type*} [MeasurableSpace Ω] (K : ℕ)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ ω, ∀ k ≤ K, IsLocallyFiniteMeasure (B k ω))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k))
    (F : Plane × Plane → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun ω => ∫⁻ p, F p ∂(chainProduct (fun k => B k ω) w K)) :=
  (Measure.measurable_lintegral hF).comp (measurable_chainProduct K B hB hlf w hw)

/-- A chain uses only the connector functions strictly before its final block. -/
theorem chainProduct_congr_connectors (K : ℕ) (μ : ℕ → Measure (Plane × Plane))
    (u v : ℕ → Plane → ℝ) (h : ∀ k < K, u k = v k) : chainProduct μ u K = chainProduct μ v K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [chainProduct]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h K (Nat.lt_succ_self K)]

/-- Restricting an input family to the finite chain prefix and extending it periodically gives the same chain. -/
theorem chainProduct_fin_restrict (K : ℕ) (μ : ℕ → Measure (Plane × Plane)) (w : ℕ → Plane → ℝ) :
    chainProduct (fun k => μ (Fin.ofNat (K + 1) k)) w K = chainProduct μ w K := by
  apply chainProduct_congr_prefix
  intro k hk
  have hk' : k < K + 1 := Nat.lt_succ_of_le hk
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_eq_of_lt hk']

/-- Appending a final finite block is exactly one further smoothed product of the prefix chain. -/
theorem chainProduct_fin_snoc (K : ℕ) (μ : Fin (K + 1) → Measure (Plane × Plane))
    (ν : Measure (Plane × Plane)) (w : ℕ → Plane → ℝ) :
    chainProduct (fun k => Fin.snoc (α := fun _ : Fin (K + 2) => Measure (Plane × Plane))
      μ ν (Fin.ofNat (K + 2) k)) w (K + 1) =
      smoothedProductMeasure (chainProduct (fun k => μ (Fin.ofNat (K + 1) k)) w K) (w K) ν := by
  have hlast : Fin.ofNat (K + 2) (K + 1) = Fin.last (K + 1) := by
    apply Fin.ext
    simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Fin.val_last, Nat.mod_eq_of_lt (Nat.lt_succ_self (K + 1))]
  rw [chainProduct, hlast, Fin.snoc_last]
  congr 1
  apply chainProduct_congr_prefix
  intro k hk
  have hfin : Fin.ofNat (K + 2) k = (Fin.ofNat (K + 1) k).castSucc := by
    apply Fin.ext
    simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Fin.val_castSucc,
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le hk), Nat.mod_eq_of_lt (by omega : k < K + 2)]
  rw [hfin, Fin.snoc_castSucc]

end Critical2DKPZ.SHF.Tsai

end
