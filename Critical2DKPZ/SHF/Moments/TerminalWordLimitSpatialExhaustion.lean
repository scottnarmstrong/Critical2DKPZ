/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialError
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialCutoffGeometry
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalSpatialMajorant
import Mathlib.Tactic

/-! # Spatial cutoff exhaustion for the first-letter moving-word recursion -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

private theorem abs_triangular_clock_sum_le (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (F : ℕ → ℕ → ℝ)
    (hF : ∀ s ∈ Finset.Icc 1 n, ∀ r ∈ Finset.range (n - s + 1), |F s r| ≤ A) :
    |∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r| ≤
      ((n : ℝ) + 1)^2 * A := by
  have hinner (s : ℕ) (hs : s ∈ Finset.Icc 1 n) :
      |∑ r ∈ Finset.range (n - s + 1), F s r| ≤ ((n : ℝ) + 1) * A := by
    calc
      _ ≤ ∑ r ∈ Finset.range (n - s + 1), |F s r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.range (n - s + 1), A := Finset.sum_le_sum (fun r hr => hF s hs r hr)
      _ = ((n - s + 1 : ℕ) : ℝ) * A := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((n : ℝ) + 1) * A := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.add_le_add_right (Nat.sub_le n s) 1) hA
  have hcard : ((Finset.Icc 1 n).card : ℝ) ≤ (n : ℝ) + 1 := by
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n, |∑ r ∈ Finset.range (n - s + 1), F s r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.Icc 1 n, ((n : ℝ) + 1) * A := Finset.sum_le_sum hinner
    _ = ((Finset.Icc 1 n).card : ℝ) * (((n : ℝ) + 1) * A) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) * A) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (by positivity) hA)
    _ = _ := by ring

/-- The interior first-letter recursion admits a compact spatial cutoff away
from the next collision diagonal, uniformly in the moving microscopic volume. -/
theorem wordFirstLetter_spatial_cutoff_small_of_potentialDomination
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
    {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M) :
    ∀ ε > 0, ∃ χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
      (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
      (∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ p ≠ 0 →
        ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
          δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) ∧
      ∀ᶠ N : ℕ in atTop,
        |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
          if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
              η * N ≤ ((nN N - s - r : ℕ) : ℝ) then
            ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
              (((∏ i, srwKernel s (u i - xN N i)) *
                collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v) *
                wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ) *
              (1 - χ ((latticeRepresentative N (u α.1.1),
                         fun i : Spectator α => latticeRepresentative N (u i.1)),
                       (latticeRepresentative N (v α.1.1),
                         fun i : Spectator α => latticeRepresentative N (v i.1))))
          else 0| ≤ ε := by
  intro ε hε
  obtain ⟨B, hB, hB0, hmajor⟩ := exists_integrable_majorant_wordConsScaledSummand_interior
    ϑ hD α w hw hτ hη nN hn xN x hx Ψ M hM hΨ
  let C : ℝ := (τ + 2)^2
  have hC : 0 < C := sq_pos_of_pos (by linarith only [hτ])
  let κ : ℝ := ε / C
  have hκ : 0 < κ := div_pos hε hC
  obtain ⟨χ, hχ, hsupport, hiχ, hcut⟩ :=
    exists_wordSpatialCutoff_of_integrable_majorant α w hw B hB hB0 κ hκ
  refine ⟨χ, hχ, hsupport, ?_⟩
  have hcap := hn.eventually (Iio_mem_nhds (lt_add_one τ))
  filter_upwards [hmajor, hcut, hcap, eventually_gt_atTop 0] with N hbN hcutN hcapN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  let F := fun s r : ℕ =>
    if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧ η * N ≤ ((nN N - s - r : ℕ) : ℝ) then
      ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        (((∏ i, srwKernel s (u i - xN N i)) *
          collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v) *
          wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ) *
        (1 - χ ((latticeRepresentative N (u α.1.1),
          fun i : Spectator α => latticeRepresentative N (u i.1)),
          (latticeRepresentative N (v α.1.1),
          fun i : Spectator α => latticeRepresentative N (v i.1))))
    else 0
  change |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1), F s r| ≤ ε
  have hF (s : ℕ) (hs : s ∈ Finset.Icc 1 (nN N))
      (r : ℕ) (hr : r ∈ Finset.range (nN N - s + 1)) : |F s r| ≤ κ / (N : ℝ)^2 := by
    by_cases hinter : η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
        η * N ≤ ((nN N - s - r : ℕ) : ℝ)
    · have hfit : s + r ≤ nN N := by
        have hs' := (Finset.mem_Icc.mp hs).2
        have hr' := Finset.mem_range.mp hr
        omega
      let a := wordFusedInitialParityShift (nN N) α (xN N)
      let d := wordFusedCoordinateRepresentative N α a
      have hd : ‖d‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ :=
        norm_wordFusedInitialParityShift_representative_le N (nN N) α (xN N)
      dsimp only [F]
      rw [ite_eq_left hinter]
      exact wordFirstLetter_spatial_error_le_of_integrable_majorant hN
        (criticalBeta ϑ N) α w (nN N) s r hfit (xN N) Ψ B χ κ
        (hbN s r hinter.1 hinter.2.1 hfit hinter.2.2
          (wordFusedSiteEmbedding α a) (wordFusedInitialParityShift_site_norm_le (nN N) α (xN N)))
        (hiχ N (nN N - s) (nN N - s - r) d d)
        (hcutN (nN N - s) (nN N - s - r) d d hd hd)
    · simp only [F, ite_eq_right hinter, abs_zero]
      exact div_nonneg hκ.le (sq_nonneg _)
  have hnN : (nN N : ℝ) ≤ (τ + 1) * N := ((div_lt_iff₀ hNr).mp hcapN).le
  have hplus : (nN N : ℝ) + 1 ≤ (τ + 2) * N := by linarith only [hnN, hNr1]
  have hcount : ((nN N : ℝ) + 1)^2 ≤ C * (N : ℝ)^2 := by
    calc
      _ ≤ ((τ + 2) * N)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hplus
      _ = _ := mul_pow _ _ _
  have hA : 0 ≤ κ / (N : ℝ)^2 := div_nonneg hκ.le (sq_nonneg _)
  calc
    _ ≤ ((nN N : ℝ) + 1)^2 * (κ / (N : ℝ)^2) :=
      abs_triangular_clock_sum_le (nN N) _ hA F hF
    _ ≤ (C * (N : ℝ)^2) * (κ / (N : ℝ)^2) := mul_le_mul_of_nonneg_right hcount hA
    _ = C * κ := by rw [mul_assoc, mul_div_cancel₀ _ (pow_ne_zero 2 hNr.ne')]
    _ = ε := mul_div_cancel₀ ε hC.ne'

end Critical2DKPZ.SHF.Moments
