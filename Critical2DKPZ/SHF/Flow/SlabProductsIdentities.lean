/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsCore

/-! # Exact variance identities for annealed polymer slabs -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Limit
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- Integrate a bounded continuous test against a finitely supported four-site lattice step
function by its exact cell integrals. -/
theorem integral_finiteLatticeFourStep_test_eq_cellSum (N : ℕ) (hN : 0 < N)
    (F : ((Plane × Plane) × (Plane × Plane)) → ℝ) (hFm : Measurable F)
    (C : ℝ) (hFbound : ∀ p, ‖F p‖ ≤ C)
    (G : ((Site × Site) × (Site × Site)) → ℝ) (Q : Finset ((Site × Site) × (Site × Site)))
    (hzero : ∀ q ∉ Q, ∀ p ∈
      (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
        F p * G q = 0) :
    ∫ p : (Plane × Plane) × (Plane × Plane),
      F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2))
      ∂((volume : Measure (Plane × Plane)).prod volume) =
    ∑ q ∈ Q,
      (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2), F p) * G q := by
  classical
  let μ : Measure ((Plane × Plane) × (Plane × Plane)) :=
    (volume : Measure (Plane × Plane)).prod volume
  let A : ((Site × Site) × (Site × Site)) → Set ((Plane × Plane) × (Plane × Plane)) :=
    fun q => (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2)
  have hAmeas (q : (Site × Site) × (Site × Site)) : MeasurableSet (A q) := by
    exact ((measurableSet_cell N q.1.1).prod (measurableSet_cell N q.1.2)).prod
      ((measurableSet_cell N q.2.1).prod (measurableSet_cell N q.2.2))
  have hcellFinite (z : Site) : volume (cell N z) < ⊤ := by
    by_cases hz : z ∈ evenLattice
    · exact volume_cell_lt_top hN hz
    · simp [cell_eq_empty_of_not_even hz]
  have hpairFinite (a b : Site) :
      (volume : Measure (Plane × Plane)) (cell N a ×ˢ cell N b) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hcellFinite a) (hcellFinite b)
  have hAfin (q : (Site × Site) × (Site × Site)) : μ (A q) < ⊤ := by
    dsimp [μ, A]
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (hpairFinite q.1.1 q.1.2) (hpairFinite q.2.1 q.2.2)
  have hFint (q : (Site × Site) × (Site × Site)) : IntegrableOn F (A q) μ := by
    have hconst : IntegrableOn (fun _ : (Plane × Plane) × (Plane × Plane) => C) (A q) μ :=
      integrableOn_const (hAfin q).ne
    apply hconst.mono' hFm.aestronglyMeasurable
    filter_upwards [] with p
    exact hFbound p
  have hrepr (p : (Plane × Plane) × (Plane × Plane)) :
      F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2)) =
      ∑ q ∈ Q, Set.indicator (A q) (fun x => F x * G q) p := by
    let q₀ : (Site × Site) × (Site × Site) :=
      ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2))
    have hp₀ : p ∈ A q₀ := by
      exact ⟨⟨mem_cell_latticePoint N p.1.1, mem_cell_latticePoint N p.1.2⟩,
        ⟨mem_cell_latticePoint N p.2.1, mem_cell_latticePoint N p.2.2⟩⟩
    change F p * G q₀ = _
    rw [Finset.sum_eq_single q₀]
    · by_cases hq₀ : q₀ ∈ Q
      · simp [A, hp₀]
      · have hz := hzero q₀ hq₀ p (by
          exact ⟨⟨mem_cell_latticePoint N p.1.1, mem_cell_latticePoint N p.1.2⟩,
            ⟨mem_cell_latticePoint N p.2.1, mem_cell_latticePoint N p.2.2⟩⟩)
        simp [A, hp₀, hz]
    · intro q hq hqne
      have hnot : p ∉ A q := by
        intro hp
        have hq₀ : q₀ = q := by
          apply Prod.ext
          · apply Prod.ext
            · exact (mem_cell_iff N q.1.1 p.1.1).mp hp.1.1
            · exact (mem_cell_iff N q.1.2 p.1.2).mp hp.1.2
          · apply Prod.ext
            · exact (mem_cell_iff N q.2.1 p.2.1).mp hp.2.1
            · exact (mem_cell_iff N q.2.2 p.2.2).mp hp.2.2
        exact hqne hq₀.symm
      simp [A, hnot]
    · intro hq₀
      have hz := hzero q₀ hq₀ p (by
        exact ⟨⟨mem_cell_latticePoint N p.1.1, mem_cell_latticePoint N p.1.2⟩,
          ⟨mem_cell_latticePoint N p.2.1, mem_cell_latticePoint N p.2.2⟩⟩)
      simp [A, hp₀, hz]
  have hterm (q : (Site × Site) × (Site × Site)) :
      Integrable (fun p => Set.indicator (A q) (fun p => F p * G q) p) μ := by
    rw [integrable_indicator_iff (hAmeas q)]
    exact (hFint q).mul_const (G q)
  calc
    _ = ∫ p, ∑ q ∈ Q, Set.indicator (A q) (fun p => F p * G q) p ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hrepr
    _ = ∑ q ∈ Q, ∫ p, Set.indicator (A q) (fun p => F p * G q) p ∂μ := by
      rw [integral_finsetSum]
      intro q hq
      exact hterm q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [integral_indicator (hAmeas q), integral_mul_const]
      rfl

/-- Integrating out the middle disorder slab makes the separated product the conditional
expectation of the full polymer pairing; the squared error is exactly the variance loss. -/
theorem integral_sq_sub_slabProduct (ϑ : ℝ) (N : ℕ) {s t t' u : ℝ} (_hs : 0 ≤ s) (hst : s < t)
    (htt' : t < t') (ht'u : t' < u) (Φ : C_c(Plane × Plane, ℝ)) :
    Integrable (fun ω => (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2) disorderLaw ∧
    Integrable (fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t t')
      (polymerMeasure ϑ N t' u ω) Φ ^ 2) disorderLaw ∧
    ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω) - kernelProductPairing (polymerMeasure ϑ N s t ω)
        (slabMeanKernel ϑ N t t') (polymerMeasure ϑ N t' u ω) Φ) ^ 2 ∂disorderLaw =
      ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw -
        ∫ ω, kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t t')
          (polymerMeasure ϑ N t' u ω) Φ ^ 2 ∂disorderLaw := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [polymerMeasure_zero_at_zero, kernelProductPairing]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let b : ℕ := evenCeil ((N : ℝ) * t)
    let c : ℕ := evenCeil ((N : ℝ) * t')
    let Y : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)
    let S : Disorder → ℝ := fun ω =>
      kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t t')
        (polymerMeasure ϑ N t' u ω) Φ
    have hY : MemLp Y 2 disorderLaw := by
      exact memLp_polymerPairing_two ϑ N s u Φ
    have hYm : Measurable Y := by
      dsimp [Y]
      exact measurable_polymerPairing ϑ N s u Φ
    have hYint : Integrable Y disorderLaw := hY.integrable (by norm_num)
    let m : MeasurableSpace Disorder :=
      Gaussian.coordinateSigma (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hm : m ≤ MeasurableSpace.pi := by
      dsimp only [m]
      exact Gaussian.coordinateSigma_le (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hCEbase := Gaussian.condExp_coordinateSigma_ae_eq
      (fun _ : ℕ × Site => ProbabilityTheory.gaussianReal 0 1)
      (Gaussian.timeBlock b c)ᶜ hYm hYint
    have hCE : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c)ᶜ ω η) ∂disorderLaw := by
      simpa only [disorderLaw, m] using hCEbase
    have hCEresample : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
      filter_upwards [hCE] with ω hω
      rw [hω]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun η => congrArg Y
        (resample_compl_eq_swapped (Gaussian.timeBlock b c) ω η)
    have hbridge (ω : Disorder) :
        (∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw) = S ω := by
      dsimp [Y, S, b, c]
      exact integral_polymerPairing_resample_slab_eq_kernelProductPairing
        ϑ N hNpos (le_of_lt hst) (le_of_lt htt') (le_of_lt ht'u) Φ ω
    have hSce : S =ᵐ[disorderLaw] disorderLaw[Y | m] := by
      filter_upwards [hCEresample] with ω hω
      exact (hω.trans (hbridge ω)).symm
    have hCE2 := hY.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ)
      (m₀ := MeasurableSpace.pi) hm
    have hCE2S :
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) =ᵐ[disorderLaw] S :=
      hCE2.trans hSce.symm
    have hS : MemLp S 2 disorderLaw := by
      have hcond : MemLp (disorderLaw[Y | m]) 2 disorderLaw := hY.condExp (by norm_num)
      exact hcond.ae_eq hSce.symm
    have hSmCE : AEStronglyMeasurable[m]
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) disorderLaw :=
      aestronglyMeasurable_condExpL2 hm _
    have hSm : AEStronglyMeasurable[m] S disorderLaw := hSmCE.congr hCE2S
    have hdecomp := integral_sq_sub_condExp_eq (Ω := Disorder)
      (mΩ := MeasurableSpace.pi) disorderLaw hm hY hS hSm hSce
    have hYsq : Integrable (fun ω => Y ω ^ 2) disorderLaw := by
      have h := hY.integrable_norm_pow'
      apply h.congr
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, sq_abs]
    have hSsq : Integrable (fun ω => S ω ^ 2) disorderLaw := by
      have h := hS.integrable_norm_pow'
      apply h.congr
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, sq_abs]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · simpa only [Y] using hYsq
    · simpa only [S] using hSsq
    · simpa only [Y, S] using hdecomp.2

end Critical2DKPZ.SHF.Flow

end
