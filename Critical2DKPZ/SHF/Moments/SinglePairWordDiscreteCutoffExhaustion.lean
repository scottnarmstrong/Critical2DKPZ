/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordCutoffError
import Mathlib.Tactic

/-! # Uniform discrete cutoff exhaustion error for the two-particle entrance -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter DeltaBose
open scoped CompactlySupported Topology

/-- Along any horizon sequence converging to `T`, the discrete two-particle entrance changes by an
arbitrarily small amount when its full cutoff is replaced by the compact exhaustion cutoff. -/
theorem pairTwo_entrance_cutoff_exhaustion_error
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (η : ℕ → C_c(ℝ × Plane, ℝ))
    (hη : ∀ k p, η k p ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ (k : ℕ) (p : ℝ × Plane),
      T / ((k : ℝ) + 3) ≤ p.1 → p.1 ≤ T - T / ((k : ℝ) + 3) →
      ‖p.2‖ ≤ k → η k p = 1) :
    ∀ ε > 0, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      |pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (fun _ => 1) -
        pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (η k)| ≤ ε := by
  obtain ⟨C, D, R₀, hC, hD, hR₀, hCutoff⟩ :=
    eventually_pairTwoTestedEntranceWindow_cutoff_error ϑ (2 * T) (by positivity) φ
  intro ε hε
  have hSmallK :=
    (tendsto_const_div_atTop_nhds_zero_nat (3 * C * T + D)).eventually
      (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  have hKpos := eventually_gt_atTop 0
  have hNatCast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hKlarge : ∀ᶠ k : ℕ in atTop, R₀ ≤ (k : ℝ) :=
    hNatCast.eventually (eventually_ge_atTop R₀)
  filter_upwards [hSmallK, hKpos, hKlarge] with k hkSmall hkpos hkR₀
  let δ : ℝ := T / ((k : ℝ) + 3)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδT : δ ≤ T / 3 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left hT.le (by positivity)
    linarith
  have hTδ : 0 < T - δ := by linarith [hδT, hT]
  have hT2δ : 0 < T - 2 * δ := by linarith [hδT, hT]
  have hLclose : ∀ᶠ N : ℕ in atTop,
      T - δ < (L N : ℝ) / N ∧ (L N : ℝ) / N < T + δ := by
    have hIoo : Set.Ioo (T - δ) (T + δ) ∈ 𝓝 T :=
      Ioo_mem_nhds (by linarith [hδ]) (by linarith [hδ])
    filter_upwards [hL.eventually hIoo] with N hN
    exact ⟨hN.1, hN.2⟩
  have hNatN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hNδ : Tendsto (fun N : ℕ => (N : ℝ) * δ) atTop atTop := by
    simpa only [mul_comm] using
      hNatN.const_mul_atTop hδ
  have hNgap : Tendsto (fun N : ℕ => (N : ℝ) * (T - 2 * δ)) atTop atTop := by
    simpa only [mul_comm] using
      hNatN.const_mul_atTop hT2δ
  have hNpos := eventually_gt_atTop 0
  have hCdiv :=
    (tendsto_const_div_atTop_nhds_zero_nat C).eventually
      (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  have hCutoffN : ∀ᶠ N : ℕ in atTop, ∀ L lo A B hi : ℕ,
      lo ≤ A → A < B → B < hi → (L : ℝ) ≤ (2 * T) * N → (hi : ℝ) ≤ (2 * T) * N →
      ∀ R : ℝ, R₀ ≤ R → ∀ ξ : ℝ × Plane → ℝ,
        (∀ p, ξ p ∈ Set.Icc (0 : ℝ) 1) →
        (∀ r ∈ Finset.Icc (A + 1) B, ∀ z : Plane, ‖z‖ ≤ R →
          ξ ((r : ℝ) / N, z) = 1) →
        |pairTwoTestedEntranceWindow ϑ N L lo hi φ (fun _ => 1) -
          pairTwoTestedEntranceWindow ϑ N L lo hi φ ξ| ≤
            C * (((Finset.Icc lo A).card : ℝ) / N +
              ((Finset.Icc (B + 1) hi).card : ℝ) / N) + D / R := by
    simpa using hCutoff
  filter_upwards [hNpos, hLclose, hNδ.eventually_ge_atTop 2,
      hNgap.eventually_ge_atTop 2, hCutoffN,
      hCdiv] with N hNpos hLcloseN hNδlarge hNgaplarge hCutoffN hCdivN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  let A : ℕ := Nat.floor ((N : ℝ) * δ)
  let B : ℕ := Nat.floor ((N : ℝ) * (T - δ))
  have hAcast : (A : ℝ) ≤ (N : ℝ) * δ := by
    dsimp [A]
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) hδ.le)
  have hA2Nat : 2 ≤ A := by
    have hfloor := Nat.floor_mono hNδlarge
    have hfloor2 : Nat.floor (2 : ℝ) = 2 := by norm_num
    simpa [A, hfloor2] using hfloor
  have hA2 : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2Nat
  have hAplusB : A + 1 ≤ B := by
    have hreal : (A : ℝ) + 1 ≤ (N : ℝ) * (T - δ) := by
      have hgap : (N : ℝ) * δ + 2 ≤ (N : ℝ) * (T - δ) := by
        nlinarith [hNgaplarge]
      linarith [hAcast]
    have hfloor := Nat.floor_mono hreal
    have hfloorA : Nat.floor ((A : ℝ) + 1) = A + 1 := by
      have heq : (A : ℝ) + 1 = ((A + 1 : ℕ) : ℝ) := by norm_num
      rw [heq, Nat.floor_natCast]
    simpa only [hfloorA] using hfloor
  have hAB : A < B := Nat.lt_of_succ_le hAplusB
  have hBcast : (B : ℝ) ≤ (N : ℝ) * (T - δ) := by
    dsimp [B]
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) hTδ.le)
  have hlow : (N : ℝ) * (T - δ) < (L N : ℝ) := by
    have h := (lt_div_iff₀ hNr).mp hLcloseN.1
    nlinarith [h]
  have hBLreal : (B : ℝ) < (L N : ℝ) := hBcast.trans_lt hlow
  have hBL : B < L N := by exact_mod_cast hBLreal
  have hδupper : T + δ ≤ 2 * T := by linarith [hδT]
  have hLbound : (L N : ℝ) ≤ (2 * T) * N := by
    have h := (div_lt_iff₀ hNr).mp hLcloseN.2
    exact h.le.trans (mul_le_mul_of_nonneg_right hδupper hNr.le)
  have hApos : 1 ≤ A := by omega
  have hplateau : ∀ r ∈ Finset.Icc (A + 1) B, ∀ z : Plane,
      ‖z‖ ≤ (k : ℝ) → η k ((r : ℝ) / N, z) = 1 := by
    intro r hr z hz
    have hr' := Finset.mem_Icc.mp hr
    have htimeLo : δ ≤ (r : ℝ) / N := by
      apply (le_div_iff₀ hNr).2
      have hfloor : (N : ℝ) * δ < (A : ℝ) + 1 := by
        simpa only [A] using Nat.lt_floor_add_one ((N : ℝ) * δ)
      have hrcast : (A : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hr'.1
      simpa only [mul_comm] using hfloor.le.trans hrcast
    have htimeHi : (r : ℝ) / N ≤ T - δ := by
      apply (div_le_iff₀ hNr).2
      have hrcast : (r : ℝ) ≤ (B : ℝ) := by exact_mod_cast hr'.2
      simpa only [mul_comm] using hrcast.trans hBcast
    exact hone k ((r : ℝ) / N, z) htimeLo htimeHi hz
  have hηbounds : ∀ p : ℝ × Plane, η k p ∈ Set.Icc (0 : ℝ) 1 := hη k
  have hErr := hCutoffN (L N) 1 A B (L N) (by omega) hAB hBL hLbound hLbound
    (k : ℝ) (by exact_mod_cast hkR₀) (η k) hηbounds hplateau
  have hcardLeft : (Finset.Icc 1 A).card = A := by
    rw [Nat.card_Icc]
    omega
  have hcardRight : (Finset.Icc (B + 1) (L N)).card = L N - B := by
    rw [Nat.card_Icc]
    omega
  have hleftRatio : ((Finset.Icc 1 A).card : ℝ) / N ≤ δ := by
    rw [hcardLeft]
    apply (div_le_iff₀ hNr).2
    simpa only [mul_comm] using hAcast
  have hBfloor : (N : ℝ) * (T - δ) - 1 < (B : ℝ) := by
    dsimp [B]
    exact Nat.sub_one_lt_floor ((N : ℝ) * (T - δ))
  have hLupper : (L N : ℝ) < (T + δ) * N :=
    (div_lt_iff₀ hNr).mp hLcloseN.2
  have hrightRatio : ((Finset.Icc (B + 1) (L N)).card : ℝ) / N ≤
      2 * δ + 1 / N := by
    rw [hcardRight, Nat.cast_sub hBL.le]
    have hdiff : (L N : ℝ) - (B : ℝ) ≤ 2 * (N : ℝ) * δ + 1 := by
      nlinarith [hLupper, hBfloor]
    calc
      ((L N : ℝ) - B) / N ≤ (2 * (N : ℝ) * δ + 1) / N :=
        div_le_div_of_nonneg_right hdiff hNr.le
      _ = 2 * δ + 1 / N := by field_simp [hNr.ne']
  have hcardRatio :
      ((Finset.Icc 1 A).card : ℝ) / N +
          ((Finset.Icc (B + 1) (L N)).card : ℝ) / N ≤ 3 * δ + 1 / N := by
    calc
      _ ≤ δ + (2 * δ + 1 / N) := add_le_add hleftRatio hrightRatio
      _ = 3 * δ + 1 / N := by ring
  have hfirst : C * (3 * δ) ≤ (3 * C * T) / (k : ℝ) := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
    have hratio : (3 * T) / ((k : ℝ) + 3) ≤ (3 * T) / (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hkR (by linarith)
    calc
      C * (3 * δ) = C * ((3 * T) / ((k : ℝ) + 3)) := by dsimp [δ]; ring
      _ ≤ C * ((3 * T) / (k : ℝ)) := mul_le_mul_of_nonneg_left hratio hC
      _ = (3 * C * T) / (k : ℝ) := by ring
  have hq : (3 * C * T + D) / (k : ℝ) < ε / 2 := hkSmall
  have hstrict :
      |pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (fun _ => 1) -
        pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (η k)| < ε := by
    have hcut := hErr
    have hCdiv' : C / N < ε / 2 := hCdivN
    calc
      _ ≤ C * (((Finset.Icc 1 A).card : ℝ) / N +
            ((Finset.Icc (B + 1) (L N)).card : ℝ) / N) + D / (k : ℝ) := by
          simpa using hcut
      _ ≤ C * (3 * δ + 1 / N) + D / (k : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hcardRatio hC) le_rfl
      _ = C * (3 * δ) + D / (k : ℝ) + C / N := by ring
      _ ≤ (3 * C * T) / (k : ℝ) + D / (k : ℝ) + C / N :=
        add_le_add (add_le_add hfirst le_rfl) le_rfl
      _ = (3 * C * T + D) / (k : ℝ) + C / N := by rw [← add_div]
      _ < ε := by linarith
  exact hstrict.le

end Critical2DKPZ.SHF.Moments

end
