/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabVaryingCompactMoment
public import Critical2DKPZ.SHF.Flow.PairingSlabReplicaCoordinates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic

/-! # Squared connector pairings with lattice-dependent compact tests -/

@[expose] public noncomputable section

open MeasureTheory Filter Set Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

private theorem support_slabReplicaFunction_subset {X : Type*} [MeasurableSpace X]
    (g : X × X → ℝ) (K : Set X) (hg : Function.support g ⊆ K ×ˢ K) :
    Function.support (fun q => ∏ i : Fin 2, g (slabReplicaArrayMeasurableEquiv X q i)) ⊆
      Set.univ.pi fun _ : Fin 4 => K := by
  intro q hq
  have hprod : (∏ i : Fin 2, g (slabReplicaArrayMeasurableEquiv X q i)) ≠ 0 := hq
  have h0 := hg ((Finset.prod_ne_zero_iff.mp hprod) 0 (Finset.mem_univ 0))
  have h1 := hg ((Finset.prod_ne_zero_iff.mp hprod) 1 (Finset.mem_univ 1))
  apply Set.mem_univ_pi.mpr
  intro i
  fin_cases i
  · exact h0.1
  · exact h1.1
  · exact h0.2
  · exact h1.2

/-- The square of a compact connector pairing has the expected moment limit
when its measurable compact test varies uniformly with the lattice scale.
The conclusion also records eventual integrability of these squares. -/
theorem tendsto_slabVaryingCompactPairing_sq_with_integrability (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (F : C_c((Plane × Plane) × (Plane × Plane), ℝ))
    (G : ℕ → ((Plane × Plane) × (Plane × Plane)) → ℝ) (hG : ∀ N, Measurable (G N))
    (K : Set (Plane × Plane)) (hK : IsCompact K)
    (hFs : Function.support F ⊆ K ×ˢ K) (hGs : ∀ N, Function.support (G N) ⊆ K ×ˢ K)
    (hUniform : ∀ δ > 0, ∀ᶠ N : ℕ in atTop, ∀ q, |G N q - F q| ≤ δ) :
    Tendsto
      (fun N => ∫ ω, (∫ q, G N q ∂
        ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))) ^ 2 ∂disorderLaw) atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)
        (slabReplicaSourceTest F))) ∧
      ∀ᶠ N : ℕ in atTop, Integrable (fun ω => (∫ q, G N q ∂
        ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))) ^ 2) disorderLaw := by
  let e := slabReplicaArrayMeasurableEquiv (Plane × Plane)
  let H : ℕ → (Fin 4 → Plane × Plane) → ℝ := fun N q => ∏ i : Fin 2, G N (e q i)
  have hH (N : ℕ) : Measurable (H N) := by
    apply Finset.measurable_prod
    intro i _
    exact (hG N).comp ((measurable_pi_apply i).comp e.measurable)
  have hFrep : (slabReplicaSourceTest F : (Fin 4 → Plane × Plane) → ℝ) =
      fun q => ∏ i : Fin 2, F (e q i) := rfl
  have hFsupport : Function.support (slabReplicaSourceTest F : (Fin 4 → Plane × Plane) → ℝ) ⊆
      Set.univ.pi fun _ => K := by
    rw [hFrep]
    exact support_slabReplicaFunction_subset F K hFs
  have hHsupport (N : ℕ) : Function.support (H N) ⊆ Set.univ.pi fun _ => K :=
    support_slabReplicaFunction_subset (G N) K (hGs N)
  obtain ⟨B, hB⟩ := F.continuous.bounded_above_of_compact_support F.hasCompactSupport
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hFabs (x : (Plane × Plane) × (Plane × Plane)) : |F x| ≤ B := by
    change ‖F.toContinuousMap x‖ ≤ B
    exact hB x
  have hUniformH : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ q,
      |H N q - slabReplicaSourceTest F q| ≤ ε := by
    intro ε hε
    let δ : ℝ := min 1 (ε / (2 * B + 2))
    have hδ : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδSmall : δ * (2 * B + 2) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    filter_upwards [hUniform δ hδ] with N hN q
    have hGabs (x) : |G N x| ≤ B + 1 := by
      calc
        _ = |G N x - F x + F x| := by rw [sub_add_cancel]
        _ ≤ |G N x - F x| + |F x| := abs_add_le _ _
        _ ≤ B + 1 := by linarith only [hN x, hFabs x, hδ1]
    rw [hFrep]
    change |(∏ i : Fin 2, G N (e q i)) - ∏ i : Fin 2, F (e q i)| ≤ ε
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    calc
      _ = |G N (e q 0) * (G N (e q 1) - F (e q 1)) +
          (G N (e q 0) - F (e q 0)) * F (e q 1)| := by congr 1; ring
      _ ≤ |G N (e q 0) * (G N (e q 1) - F (e q 1))| +
          |(G N (e q 0) - F (e q 0)) * F (e q 1)| := abs_add_le _ _
      _ ≤ (B + 1) * δ + δ * B := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul (hGabs _) (hN _) (abs_nonneg _) (by positivity))
          (mul_le_mul (hN _) (hFabs _) (abs_nonneg _) hδ.le)
      _ ≤ δ * (2 * B + 2) := by nlinarith only [hδ.le]
      _ ≤ ε := hδSmall
  have hLimit := tendsto_slabTwoBlockCompactIntegral_varying_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru
    (slabReplicaSourceTest F) H hH K hK hFsupport hHsupport hUniformH
  have hSource (N : ℕ) (ω : Disorder) :
      (∫ q, H N q ∂slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
        (polymerMeasure ϑ N r u ω)) =
        (∫ q, G N q ∂((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))) ^ 2 := by
    let : IsLocallyFiniteMeasure (polymerMeasure ϑ N s t ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω
    let : IsLocallyFiniteMeasure (polymerMeasure ϑ N r u ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ N r u ω
    simpa only [slabTwoBlockPiMeasure, H, e, Fin.prod_univ_two, slabReplicaArrayMeasurableEquiv,
      slabReplicaArrayEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one] using integral_slabReplicaFunction_sq (G N)
  simpa only [hSource] using hLimit


end Critical2DKPZ.SHF.Flow

end
