/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CommonCompositionFactors
public import Critical2DKPZ.SHF.Tsai.AdjacentPairLaws

/-! # Common coarse-interval factors on a finite grid

Equal interval laws give common two-block composition factors. Induction on
the terminal grid index composes these into one measurable function of the
elementary block tuple, valid almost surely for both processes.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set

namespace Critical2DKPZ.SHF.Tsai

/-- Equal marginal interval laws give one measurable grid-interval factor for both dense flows. -/
theorem exists_common_grid_interval_factor {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    (hlaw : ∀ s ∈ D, ∀ t ∈ D, s < t → P.map (Z s t) = P'.map (Z' s t))
    (m : ℕ) (t : ℕ → ℝ) (ht : StrictMonoOn t (Iic m)) (htD : ∀ k ≤ m, t k ∈ D)
    {a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    ∃ φ : (Fin m → Measure (Plane × Plane)) → Measure (Plane × Plane),
      Measurable φ ∧ (∀ μ, IsLocallyFiniteMeasure (φ μ)) ∧
      (Z (t a) (t b) =ᵐ[P] fun ω => φ (fun k => Z (t k) (t (k + 1)) ω)) ∧
      (Z' (t a) (t b) =ᵐ[P'] fun ω => φ (fun k => Z' (t k) (t (k + 1)) ω)) := by
  classical
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hbase : b = a + 1
    · subst b
      let E := CompactExhaustion.choice (Plane × Plane)
      let i : Fin m := ⟨a, by omega⟩
      let φ (μ : Fin m → Measure (Plane × Plane)) :=
        RandomMeasure.locallyFiniteMeasureModification E id (μ i)
      have hφm : Measurable φ :=
        (RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id).comp (measurable_pi_apply i)
      have horder : t a < t (a + 1) := ht (by change a ≤ m; omega) hb (by omega)
      refine ⟨φ, hφm, (fun μ => RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id _), ?_, ?_⟩
      · filter_upwards [(hZ.1 (t a) (htD a (by omega)) (t (a + 1)) (htD (a + 1) hb) horder).2] with ω hω
        exact (RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id
          (Z (t a) (t (a + 1)) ω) hω).symm
      · filter_upwards [(hZ'.1 (t a) (htD a (by omega)) (t (a + 1)) (htD (a + 1) hb) horder).2] with ω hω
        exact (RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id
          (Z' (t a) (t (a + 1)) ω) hω).symm
    · have hab' : a < b - 1 := by omega
      obtain ⟨ψ, hψ, _hψlf, hψAE, hψAE'⟩ := ih (b - 1) (by omega) hab' (by omega)
      have haD := htD a (by omega : a ≤ m)
      have hpD := htD (b - 1) (by omega : b - 1 ≤ m)
      have hbD := htD b hb
      have hap : t a < t (b - 1) := ht (by change a ≤ m; omega) (by change b - 1 ≤ m; omega) hab'
      have hpb : t (b - 1) < t b := ht (by change b - 1 ≤ m; omega) hb (by omega)
      have hPair := isDenseSHF_adjacent_pair_law_eq_of_law_eq P P' Z Z' hZ hZ' hlaw haD hpD hbD hap hpb
      obtain ⟨φ, hφ, hφlf, hφAE, hφAE'⟩ := exists_common_measurable_composition_factor
        P P' Z Z' hZ hZ' haD hpD hbD hap hpb hPair
      let j : Fin m := ⟨b - 1, by omega⟩
      let Φ (μ : Fin m → Measure (Plane × Plane)) := φ (ψ μ, μ j)
      refine ⟨Φ, hφ.comp (hψ.prodMk (measurable_pi_apply j)), (fun μ => hφlf _), ?_, ?_⟩
      · filter_upwards [hψAE, hφAE] with ω hω hω'
        change Z (t a) (t b) ω = φ (ψ (fun k => Z (t k) (t (k + 1)) ω), Z (t (b - 1)) (t (b - 1 + 1)) ω)
        rw [hω', hω, Nat.sub_add_cancel (by omega : 1 ≤ b)]
      · filter_upwards [hψAE', hφAE'] with ω hω hω'
        change Z' (t a) (t b) ω = φ (ψ (fun k => Z' (t k) (t (k + 1)) ω), Z' (t (b - 1)) (t (b - 1 + 1)) ω)
        rw [hω', hω, Nat.sub_add_cancel (by omega : 1 ≤ b)]

end Critical2DKPZ.SHF.Tsai

end
