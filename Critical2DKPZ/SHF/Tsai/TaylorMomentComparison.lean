/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MultilinearMomentComparison
public import Critical2DKPZ.SHF.Tsai.TaylorFourthRemainder

/-! # Equality of integrable cubic Taylor expectations

Mixed coordinate moments of orders zero through three determine every
coefficient in the cubic Taylor polynomial at a fixed base point. This
algebraic step does not require a differentiability hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Matching mixed coordinate moments through order three identify the actual cubic Taylor expectations. -/
theorem integral_cubicTaylor_eq_of_coordinate_moments {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') {m : ℕ}
    (X : Ω → Fin m → ℝ) (Y : Ω' → Fin m → ℝ)
    (hX : ∀ k ≤ 3, ∀ q : Fin k → Fin m, Integrable (fun ω => ∏ i, X ω (q i)) P)
    (hY : ∀ k ≤ 3, ∀ q : Fin k → Fin m, Integrable (fun ω => ∏ i, Y ω (q i)) P')
    (hEq : ∀ k ≤ 3, ∀ q : Fin k → Fin m,
      (∫ ω, ∏ i, X ω (q i) ∂P) = ∫ ω, ∏ i, Y ω (q i) ∂P')
    (H : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) :
    Integrable (fun ω => ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => X ω)) P ∧
    Integrable (fun ω => ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => Y ω)) P' ∧
    (∫ ω, ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => X ω) ∂P) =
      ∫ ω, ∑ k ∈ Finset.range 4,
        (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => Y ω) ∂P' := by
  have hM (k : ℕ) (hk : k ≤ 3) := integral_multilinear_eq_of_coordinate_moments P P' X Y
    (hX k hk) (hY k hk) (hEq k hk) (iteratedFDeriv ℝ k H x)
  have hXI (k) (hk : k ∈ Finset.range 4) : Integrable (fun ω =>
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => X ω)) P :=
    ((hM k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).1).const_mul _
  have hYI (k) (hk : k ∈ Finset.range 4) : Integrable (fun ω =>
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => Y ω)) P' :=
    ((hM k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).2.1).const_mul _
  refine ⟨integrable_finsetSum _ hXI, integrable_finsetSum _ hYI, ?_⟩
  rw [integral_finsetSum _ hXI, integral_finsetSum _ hYI]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_const_mul,
    (hM k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).2.2]

end Critical2DKPZ.SHF.Tsai

end
