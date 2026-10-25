/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceDiagonalCenter
import Mathlib.Tactic

/-! # Vanishing short strips for centered diagonal entrance tests -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- If the moving entrance center approaches the zero of a linearly vanishing test at
`o(1 / log N)`, then the coincident microscopic strip vanishes after choosing its
macroscopic width sufficiently small. -/
theorem eventually_collisionEntrance_diagonal_short_strip_small
    (aN : ℕ → Site) (c : Plane) (L : ℝ) (hL : 0 ≤ L)
    (F : ℝ × Plane → ℝ)
    (hF : ∀ u x, 0 ≤ u → |F (u, x)| ≤ L * (u + ‖x - c‖))
    (hcenter : Tendsto
      (fun N : ℕ => ‖latticeRepresentative N (aN N) - c‖ *
        Real.log ((N : ℝ) + 2)) atTop (𝓝 0))
    (δmax : ℝ) (hδmax : 0 < δmax) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ δmax ∧ ∀ᶠ N : ℕ in atTop,
      |collisionEntrance N 0 (evenCeil ((N : ℝ) * δ) : ℕ)
          (aN N) (aN N) F| < ε := by
  obtain ⟨Creturn, Ccenter, Cmoment, hCreturn, hCcenter, hCmoment, hstrip⟩ :=
    exists_collisionEntrance_abs_le_linear_center_log
  intro ε hε
  let D : ℝ := max (L * Creturn) 1
  let E : ℝ := max (4 * L * Cmoment) 1
  let δ : ℝ := min δmax (min (1 / 2) (min (ε / (8 * D)) ((ε / (8 * E)) ^ 2)))
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδcap : δ ≤ δmax := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδhalf' : δ ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hδhalf
  have hδD : δ ≤ ε / (8 * D) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδE : δ ≤ (ε / (8 * E)) ^ 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmallCenter :
      ∀ᶠ N : ℕ in atTop, (L * Ccenter) *
        (‖latticeRepresentative N (aN N) - c‖ *
          Real.log ((N : ℝ) + 2)) < ε / 4 := by
    have hlim : Tendsto (fun N : ℕ => (L * Ccenter) *
        (‖latticeRepresentative N (aN N) - c‖ *
          Real.log ((N : ℝ) + 2))) atTop (𝓝 0) :=
      by simpa only [mul_zero] using
        (tendsto_const_nhds (x := L * Ccenter)).mul hcenter
    exact hlim.eventually_lt_const (by positivity)
  have hsmallN : ∀ᶠ N : ℕ in atTop, 3 * L * Creturn / (N : ℝ) < ε / 4 := by
    have hlim : Tendsto (fun N : ℕ => 3 * L * Creturn / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_nat (3 * L * Creturn)
    exact hlim.eventually_lt_const (by positivity)
  have hsmall6 : ∀ᶠ N : ℕ in atTop, 6 / (N : ℝ) < 2 * δ := by
    have hlim : Tendsto (fun N : ℕ => 6 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_nat 6
    exact hlim.eventually_lt_const (by positivity)
  refine ⟨δ, hδ, hδcap, ?_⟩
  filter_upwards [hsmallCenter, hsmallN, hsmall6, eventually_ge_atTop 6] with
      N hcenterSmall hNsmall hNsmall6 hN6
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  let K : ℕ := evenCeil ((N : ℝ) * δ)
  have hceil : (K : ℝ) ≤ (N : ℝ) * δ + 2 := by
    dsimp [K]
    exact (Critical2DKPZ.evenCeil_lt_add_two
      (mul_nonneg (Nat.cast_nonneg N) hδ.le)).le
  have hKupper : (K : ℝ) + 1 ≤ (N : ℝ) * δ + 3 := by linarith
  have hratio : ((K : ℝ) + 1) / N ≤ δ + 3 / (N : ℝ) := by
    rw [div_le_iff₀ hNr]
    calc
      (K : ℝ) + 1 ≤ (N : ℝ) * δ + 3 := hKupper
      _ = (δ + 3 / (N : ℝ)) * N := by field_simp [hNr.ne']
  have hKN : K ≤ N := by
    apply_mod_cast (show (K : ℝ) ≤ (N : ℝ) by
      calc
        (K : ℝ) ≤ (N : ℝ) * δ + 2 := hceil
        _ ≤ (N : ℝ) / 2 + 2 := by
          have hNδ : (N : ℝ) * δ ≤ (N : ℝ) / 2 :=
            mul_le_mul_of_nonneg_left hδhalf' (Nat.cast_nonneg N)
          linarith
        _ ≤ (N : ℝ) := by
          have hNreal6 : (6 : ℝ) ≤ N := by exact_mod_cast hN6
          nlinarith)
  let S : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹ * Real.sqrt ((K : ℝ) + 1)
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hSsq : S ^ 2 = 2 * (((K : ℝ) + 1) / N) := by
    dsimp [S]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2),
      Real.sq_sqrt (by positivity : 0 ≤ (K : ℝ) + 1)]
    field_simp [hNr.ne']
  have hSbound : S ≤ 2 * Real.sqrt δ := by
    apply (sq_le_sq₀ hSnonneg (by positivity)).mp
    calc
      S ^ 2 = 2 * (((K : ℝ) + 1) / N) := hSsq
      _ ≤ 2 * (δ + 3 / (N : ℝ)) := by gcongr
      _ ≤ 4 * δ := by
        calc
          2 * (δ + 3 / (N : ℝ)) = 2 * δ + 6 / (N : ℝ) := by ring
          _ ≤ 2 * δ + 2 * δ := add_le_add le_rfl hNsmall6.le
          _ = 4 * δ := by ring
      _ = (2 * Real.sqrt δ) ^ 2 := by rw [mul_pow, Real.sq_sqrt hδ.le]; ring
  have hfirst : L * Creturn * δ ≤ ε / 8 := by
    calc
      L * Creturn * δ ≤ D * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ.le
        exact le_max_left _ _
      _ ≤ D * (ε / (8 * D)) := mul_le_mul_of_nonneg_left hδD (le_of_lt hD)
      _ = ε / 8 := by field_simp [hD.ne']
  have hroot : Real.sqrt δ ≤ ε / (8 * E) := by
    by_contra hnot
    have hgt : ε / (8 * E) < Real.sqrt δ := lt_of_not_ge hnot
    have hsq := Real.sq_sqrt hδ.le
    have hq : 0 ≤ ε / (8 * E) := by positivity
    nlinarith [hδE]
  have hthird : 4 * L * Cmoment * Real.sqrt δ ≤ ε / 8 := by
    calc
      4 * L * Cmoment * Real.sqrt δ ≤ E * Real.sqrt δ := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg δ)
        exact le_max_left _ _
      _ ≤ E * (ε / (8 * E)) := mul_le_mul_of_nonneg_left hroot (le_of_lt hE)
      _ = ε / 8 := by field_simp [hE.ne']
  have hsecond : 3 * L * Creturn / (N : ℝ) < ε / 4 := hNsmall
  have hcenterSecond : (L * Ccenter) *
      (‖latticeRepresentative N (aN N) - c‖ * Real.log ((N : ℝ) + 2)) < ε / 4 :=
    hcenterSmall
  have hbase := hstrip N K hNpos hKN (aN N) c L hL F hF
  have hbound : |collisionEntrance N 0 K (aN N) (aN N) F| ≤
      L * (Creturn * (δ + 3 / (N : ℝ)) +
        Ccenter * ‖latticeRepresentative N (aN N) - c‖ *
          Real.log ((N : ℝ) + 2) + 4 * Cmoment * Real.sqrt δ) := by
    have hscale : (2 * Cmoment) * S ≤ 4 * Cmoment * Real.sqrt δ := by
      calc
        (2 * Cmoment) * S ≤ (2 * Cmoment) * (2 * Real.sqrt δ) :=
          mul_le_mul_of_nonneg_left hSbound (by positivity)
        _ = 4 * Cmoment * Real.sqrt δ := by ring
    calc
      _ ≤ L * (Creturn * (((K : ℝ) + 1) / N) +
          Ccenter * ‖latticeRepresentative N (aN N) - c‖ *
            Real.log ((N : ℝ) + 2) + 2 * Cmoment * S) := by
        simpa [K, S, mul_assoc, mul_left_comm, mul_comm] using hbase
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hL
        have h1 := mul_le_mul_of_nonneg_left hratio hCreturn.le
        have h3 := hscale
        nlinarith
  have hDδ : L * Creturn * δ ≤ ε / 8 := hfirst
  have hsum : L * (Creturn * (δ + 3 / (N : ℝ)) +
        Ccenter * ‖latticeRepresentative N (aN N) - c‖ *
          Real.log ((N : ℝ) + 2) + 4 * Cmoment * Real.sqrt δ) < ε := by
    have hcenterTerm : L * (Ccenter * ‖latticeRepresentative N (aN N) - c‖ *
          Real.log ((N : ℝ) + 2)) < ε / 4 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcenterSecond
    have htimeTerm : L * Creturn * (3 / (N : ℝ)) < ε / 4 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsecond
    have hsmall : L * (Creturn * δ) +
        L * (Creturn * (3 / (N : ℝ))) +
        L * (Ccenter * ‖latticeRepresentative N (aN N) - c‖ *
          Real.log ((N : ℝ) + 2)) +
        L * (4 * Cmoment * Real.sqrt δ) < ε := by
      nlinarith [hDδ, hthird, htimeTerm, hcenterTerm]
    convert hsmall using 1
    ring
  exact lt_of_le_of_lt hbound hsum

end Critical2DKPZ.SHF.Moments

end
