/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PathMeasurability
import Critical2DKPZ.Extensions.ScaleLimit.ZeroReduction
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-! # Uniform initial-value tails along divergent scale sequences

The second moment at time zero tends to zero. Its values along any divergent
sequence are bounded, and Markov's inequality supplies a uniform tail bound.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Uniformly bounded second moments imply uniformly tight scalar values. -/
theorem exists_uniform_abs_tail_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (B : ℝ)
    (hB : ∀ i, (∫ ω, X i ω ^ 2 ∂P) ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ i, P {ω | M < |X i ω|} ≤ ENNReal.ofReal ε := by
  let C : ℝ := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let M : ℝ := C / ε + 1
  have hM1 : 1 < M := by dsimp [M]; linarith [div_pos hC hε]
  have hM : 0 < M := lt_trans zero_lt_one hM1
  have hBM : B ≤ ε * M ^ 2 := by
    have hCM : C ≤ ε * M := by
      dsimp [M]
      field_simp
      nlinarith
    have hMM : M ≤ M ^ 2 := by nlinarith
    have hBC : B ≤ C := by dsimp [C]; linarith [le_max_left B 0]
    nlinarith
  refine ⟨M, ?_⟩
  intro i
  have hint := (memLp_two_iff_integrable_sq (hX i).aestronglyMeasurable).mp (hX i)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun ω => sq_nonneg (X i ω))) hint (M ^ 2)
  have hsub : {ω | M < |X i ω|} ⊆ {ω | M ^ 2 ≤ X i ω ^ 2} := by
    intro ω hω
    exact (pow_le_pow_left₀ hM.le hω.le 2).trans_eq (sq_abs _)
  have htail : P.real {ω | M < |X i ω|} ≤ ε := by
    calc
      _ ≤ P.real {ω | M ^ 2 ≤ X i ω ^ 2} := measureReal_mono hsub
      _ ≤ B / M ^ 2 := (le_div_iff₀ (sq_pos_of_pos hM)).mpr (by nlinarith [hB i])
      _ ≤ ε := (div_le_iff₀ (sq_pos_of_pos hM)).mpr (by nlinarith)
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal htail

/-- Time-zero scale-path values are uniformly tight along every divergent scale sequence. -/
theorem kpz_initial_tail_bound
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn) (S : ℝ≥0)
    (u : ℕ → Set.Ioi (0 : ℝ)) (hu : Tendsto (fun n => (u n : ℝ)) atTop atTop) :
    ∀ ε > (0 : ℝ), ∃ M : ℝ, ∀ n,
      (P.map (fun ω => scalePath S (H t 0 ω) φ x (u n)))
        {f | M < |f ⟨0, by simp⟩|} ≤ ENNReal.ofReal ε := by
  have hlim := (tendsto_second_moment_scaledPairing_zero ϑ P Z hZ H hH ht φ x).comp
    (tendsto_Ioi_atTop.mpr hu)
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  intro ε hε
  obtain ⟨M, hM⟩ := exists_uniform_abs_tail_bound P
    (fun n ω => scaledPairing (H t 0 ω) φ x (u n) 0)
    (fun n => memLp_scaledPairing_two ϑ P Z hZ H hH ht φ x (u n) 0) B
    (fun n => hB ⟨n, rfl⟩) hε
  refine ⟨M, ?_⟩
  intro n
  have hset : MeasurableSet {f : ScalePath S | M < |f ⟨0, by simp⟩|} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_scalePath ϑ P Z hZ H hH ht x φ S (u n)) hset]
  exact hM n

end Critical2DKPZ.Extensions.ScaleLimit
