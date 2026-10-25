/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansion
public import Critical2DKPZ.SHF.Moments.CollisionWordMomentExpansion
public import Critical2DKPZ.SHF.Moments.AnnealedBounds
public import Critical2DKPZ.SHF.Moments.PairingFubini
public import Critical2DKPZ.SHF.Moments.LowReplicaWordIdentities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Geometric collision-word bounds for one replica -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

private instance instUniqueCollisionWordOneZero : Unique (CollisionWord 1 0) where
  default := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  uniq w := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i

private theorem tsum_one_replica_word_sum_eq_empty (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (φ : Fin 1 → C_c(Plane × Plane, ℝ)) :
    (∑' m : ℕ, ∑ w : CollisionWord 1 m,
      testedBlockWord ϑ N s t φ (List.ofFn w.1)) =
        testedBlockWord ϑ N s t φ [] := by
  classical
  rw [tsum_eq_single 0]
  · simp
  · intro m hm
    cases m with
    | zero => exact (hm rfl).elim
    | succ m => simp

private theorem testedBlockWord_one_empty_eq_annealed_pairing
    (ϑ : ℝ) (N : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (φ : Fin 1 → C_c(Plane × Plane, ℝ)) :
    testedBlockWord ϑ N s t φ [] =
      ∫ ω, (∫ p : Plane × Plane,
        φ 0 p * rescaledP2P ϑ N s t p ω ∂volume) ∂disorderLaw := by
  have hword := tsum_one_replica_word_sum_eq_empty ϑ N s t φ
  have hid := integral_prod_pairing_eq_wordSum ϑ N hs hst φ
  rw [hword, testedNonpairRemainder_eq_zero_of_h_le_two ϑ N (by omega) φ] at hid
  have hleft :
      (∫ ω, (∏ i : Fin 1,
        (∫ p : Plane × Plane,
          φ i p * rescaledP2P ϑ N s t p ω ∂volume)) ∂disorderLaw) =
        ∫ ω, (∫ p : Plane × Plane,
          φ 0 p * rescaledP2P ϑ N s t p ω ∂volume) ∂disorderLaw := by
    congr 1
    funext ω
    simp
  rw [hleft] at hid
  simpa using hid.symm

private theorem eventually_evenDuration_ge_half_tau (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s →
      (τ / 2) * (N : ℝ) ≤
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 / τ ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 / τ)
  filter_upwards [hlarge] with N hN
  intro s t hs hst
  have hst' : s ≤ t := by linarith
  have ht : 0 ≤ t := hs.trans hst'
  have hround := evenCeil_duration_error
    (mul_nonneg (Nat.cast_nonneg N) hs) (mul_nonneg (Nat.cast_nonneg N) ht)
  have hab : evenCeil ((N : ℝ) * s) ≤ evenCeil ((N : ℝ) * t) :=
    Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hst' (Nat.cast_nonneg N))
  have hcast :
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℝ) =
        ((evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℕ) : ℝ) := by
    -- The natural-number difference is well-defined because the clock is monotone.
    exact (Nat.cast_sub hab).symm
  have hround' :
      |((evenCeil ((N : ℝ) * t) : ℝ) - evenCeil ((N : ℝ) * s)) -
        ((N : ℝ) * (t - s))| < 2 := by
    convert hround using 1
    ring
  have hNτ : 4 ≤ (N : ℝ) * τ := (div_le_iff₀ hτ).mp hN
  rw [hcast]
  have hlower := (abs_lt.mp hround').1
  nlinarith

private theorem annealed_density_le_uniform_tau
    (ϑ : ℝ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ,
      0 ≤ s → τ ≤ t - s → ∀ p : Plane × Plane,
        0 ≤ ∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw ∧
        (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) ≤ A := by
  obtain ⟨A, hA, hwalk⟩ := scaled_srwKernel_bound (half_pos hτ)
  refine ⟨A, hA.le, ?_⟩
  filter_upwards [eventually_evenDuration_ge_half_tau τ hτ] with N hN
  intro s t hs hst p
  have hn0 : (τ / 2) * (N : ℝ) ≤
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℝ) := hN s t hs hst
  have hn : (τ / 2) * (N : ℝ) ≤
      ((evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℕ) : ℝ) := by
    simpa only [Nat.cast_sub (Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (show s ≤ t by linarith) (Nat.cast_nonneg N)))] using hn0
  rw [integral_rescaledP2P]
  constructor
  · exact mul_nonneg (by positivity)
      (Critical2DKPZ.srwKernel_nonneg _ _)
  · exact hwalk N (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) hn
      (latticePoint N p.2 - latticePoint N p.1)

private theorem abs_integral_one_replica_annealed_pairing_le
    (ϑ : ℝ) (N : ℕ) (s t A : ℝ) (φ : C_c(Plane × Plane, ℝ))
    (hbound : ∀ p, 0 ≤ ∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw ∧
      (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) ≤ A) :
    |∫ p : Plane × Plane, φ p *
        (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)| ≤
      A * ∫ p, |φ p| := by
  let g : Plane × Plane → ℝ := fun p =>
    ∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw
  have hφabs : Integrable (fun p : Plane × Plane => |φ p|) volume :=
    (φ.continuous.abs).integrable_of_hasCompactSupport φ.hasCompactSupport.abs
  have hmajor : Integrable (fun p : Plane × Plane => A * |φ p|) volume :=
    hφabs.const_mul A
  have hφprod : Integrable (fun p : Plane × Plane => φ p * g p) volume := by
    apply hmajor.mono'
    · exact (φ.continuous.measurable.mul
        (measurable_integral_rescaledP2P ϑ N s t)).aestronglyMeasurable
    · filter_upwards [] with p
      have hg := hbound p
      change |φ p * g p| ≤ A * |φ p|
      rw [abs_mul, abs_of_nonneg hg.1]
      calc
        |φ p| * g p ≤ |φ p| * A := mul_le_mul_of_nonneg_left hg.2 (abs_nonneg _)
        _ = A * |φ p| := by ring
  have habs := hφprod.norm
  have hmajorInt :
      (∫ p : Plane × Plane, |φ p * g p|) ≤
        ∫ p : Plane × Plane, A * |φ p| := by
    apply integral_mono habs hmajor
    intro p
    have hg := hbound p
    change |φ p * g p| ≤ A * |φ p|
    rw [abs_mul, abs_of_nonneg hg.1]
    calc
      |φ p| * g p ≤ |φ p| * A := mul_le_mul_of_nonneg_left hg.2 (abs_nonneg _)
      _ = A * |φ p| := by ring
  calc
    |∫ p : Plane × Plane, φ p * g p| ≤
        ∫ p : Plane × Plane, |φ p * g p| := abs_integral_le_integral_abs
    _ ≤ ∫ p : Plane × Plane, A * |φ p| := hmajorInt
    _ = A * ∫ p : Plane × Plane, |φ p| := by rw [integral_const_mul]

/-- The one-replica geometric estimate: all nonempty words vanish, and the empty-word
coefficient is bounded by the annealed random-walk density. -/
theorem testedBlockWord_geometric_le_one_replica (ϑ : ℝ) {τ T : ℝ} (hτ : 0 < τ)
    (φ : Fin 1 → C_c(Plane × Plane, ℝ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord 1 m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m := by
  obtain ⟨A, hA, hDensity⟩ := annealed_density_le_uniform_tau ϑ τ hτ
  let ψ : C_c(Plane × Plane, ℝ) := φ 0
  let C : ℝ := A * ∫ p : Plane × Plane, |ψ p|
  have hC : 0 ≤ C := mul_nonneg hA (integral_nonneg fun _ => abs_nonneg _)
  refine ⟨C, 0, hC, by norm_num, by norm_num, ?_⟩
  filter_upwards [hDensity] with N hDensity
  intro s t hs hst ht m
  have hstle : s ≤ t := by linarith
  have hword := testedBlockWord_one_empty_eq_annealed_pairing
    ϑ N hs hstle φ
  have hpair := integral_pairing_rescaledP2P ϑ N s t ψ.continuous ψ.hasCompactSupport
  have hbound := abs_integral_one_replica_annealed_pairing_le
    ϑ N s t A ψ (hDensity s t hs hst)
  have hzero :
      |testedBlockWord ϑ N s t φ []| ≤ C := by
    calc
      |testedBlockWord ϑ N s t φ []| =
          |∫ ω, (∫ p : Plane × Plane,
              ψ p * rescaledP2P ϑ N s t p ω ∂volume) ∂disorderLaw| := by
                simpa [ψ] using congrArg abs hword
      _ = |∫ p : Plane × Plane, ψ p *
              (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)| := by
                exact congrArg abs hpair
      _ ≤ A * ∫ p : Plane × Plane, |ψ p| := hbound
      _ = C := by rfl
  cases m with
  | zero =>
      simpa [C, instUniqueCollisionWordOneZero] using hzero
  | succ m =>
      simp

end Critical2DKPZ.SHF.Moments

end
