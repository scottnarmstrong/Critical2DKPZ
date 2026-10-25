/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockSpatialLocalLimit
public import Critical2DKPZ.SHF.Moments.PairBlockGaussianCompositionSplit
import Mathlib.Tactic

/-! # Mixed short-long composition spatial profiles -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

private theorem list_sum_filter_lt_add_ge (cut : ℕ) (ms : List ℕ) :
    (ms.filter (fun m => m < cut)).sum +
      (ms.filter (fun m => cut ≤ m)).sum = ms.sum := by
  have hperm := filter_short_append_long_perm cut ms
  have hsum : ((ms.filter (fun m => m < cut)) ++
      (ms.filter (fun m => cut ≤ m))).sum = ms.sum := hperm.sum_eq
  simpa only [List.sum_append] using hsum

private theorem abs_sum_weighted_error_le {ι : Type*} (A : Finset ι)
    (w f g : ι → ℝ) (ε : ℝ)
    (hw : ∀ i ∈ A, 0 ≤ w i)
    (hmass : ∑ i ∈ A, w i = 1)
    (herr : ∀ i ∈ A, |f i - g i| ≤ ε) :
    |(∑ i ∈ A, w i * f i) - (∑ i ∈ A, w i * g i)| ≤ ε := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ i ∈ A, |w i * (f i - g i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ A, w i * ε := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (herr i hi) (hw i hi)
    _ = ε := by rw [← Finset.sum_mul, hmass]; ring

private theorem abs_double_sum_weighted_error_le {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (wa : ι → ℝ) (wb : κ → ℝ)
    (f g : ι → κ → ℝ) (ε : ℝ)
    (hwa : ∀ a ∈ A, 0 ≤ wa a) (hwb : ∀ b ∈ B, 0 ≤ wb b)
    (hmassa : ∑ a ∈ A, wa a = 1) (hmassb : ∑ b ∈ B, wb b = 1)
    (herr : ∀ a ∈ A, ∀ b ∈ B, |f a b - g a b| ≤ ε) :
    |(∑ a ∈ A, wa a * (∑ b ∈ B, wb b * f a b)) -
      (∑ a ∈ A, wa a * (∑ b ∈ B, wb b * g a b))| ≤ ε := by
  have hinner (a : ι) (ha : a ∈ A) :
      |(∑ b ∈ B, wb b * f a b) - (∑ b ∈ B, wb b * g a b)| ≤ ε :=
    abs_sum_weighted_error_le B wb (fun b => f a b) (fun b => g a b) ε
      (fun b hb => hwb b hb) hmassb (fun b hb => herr a ha b hb)
  exact abs_sum_weighted_error_le A wa
    (fun a => ∑ b ∈ B, wb b * f a b)
    (fun a => ∑ b ∈ B, wb b * g a b) ε hwa hmassa hinner

private theorem largeBlockGaussianListPairLaw_eq_short_long_sum
    (mCut : ℕ) (ms : List ℕ) (j₁ j₂ : ℕ) :
    largeBlockGaussianListPairLaw mCut ms j₁ j₂ =
      ∑ b ∈ (Finset.range ((ms.filter (fun m => m < mCut)).sum + 1)).filter
            (fun b => b ≤ j₂ ∧ j₂ - b ≤ (ms.filter (fun m => mCut ≤ m)).sum),
        ∑ a ∈ (Finset.range ((ms.filter (fun m => m < mCut)).sum + 1)).filter
            (fun a => a ≤ j₁ ∧ j₁ - a ≤ (ms.filter (fun m => mCut ≤ m)).sum),
          largeBlockGaussianListLaw mCut (ms.filter (fun m => m < mCut)) a *
            largeBlockGaussianListLaw mCut (ms.filter (fun m => m < mCut)) b *
            (largeBlockGaussianListLaw mCut (ms.filter (fun m => mCut ≤ m)) (j₁ - a) *
              largeBlockGaussianListLaw mCut (ms.filter (fun m => mCut ≤ m)) (j₂ - b)) := by
  let short := ms.filter (fun m => m < mCut)
  let long := ms.filter (fun m => mCut ≤ m)
  let A := (Finset.range (short.sum + 1)).filter
    (fun a => a ≤ j₁ ∧ j₁ - a ≤ long.sum)
  let B := (Finset.range (short.sum + 1)).filter
    (fun b => b ≤ j₂ ∧ j₂ - b ≤ long.sum)
  have hcoord (j : ℕ) :
      largeBlockGaussianListLaw mCut ms j =
        ∑ i ∈ (Finset.range (short.sum + 1)).filter
            (fun i => i ≤ j ∧ j - i ≤ long.sum),
          largeBlockGaussianListLaw mCut short i *
            largeBlockGaussianListLaw mCut long (j - i) := by
    rw [largeBlockGaussianListLaw_eq_short_long_convolution]
    rw [finiteNaturalConvolution_eq_sum_left]
  change largeBlockGaussianListLaw mCut ms j₁ *
      largeBlockGaussianListLaw mCut ms j₂ = _
  rw [hcoord j₁, hcoord j₂]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := B) (t := A)]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem sqrtNat_le_nat (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    simpa using Real.sqrt_le_sqrt h
  have hsquare : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNreal.le
  have hmul := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (N : ℝ))
  have hmul' : Real.sqrt (N : ℝ) ≤ Real.sqrt (N : ℝ) ^ 2 := by
    simpa [pow_two] using hmul
  simpa [hsquare] using hmul'

/-- Both rotated integer coordinates are controlled by twice the Euclidean norm
of the embedded site. -/
theorem siteToPlane_sum_difference_norm_bound (z : Site) :
    |(z 0 : ℝ) + z 1| ≤ 2 * ‖siteToPlane z‖ ∧
    |(z 0 : ℝ) - z 1| ≤ 2 * ‖siteToPlane z‖ := by
  have h0Sq : (z 0 : ℝ) ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
    rw [Critical2DKPZ.norm_siteToPlane_sq]
    nlinarith
  have h1Sq : (z 1 : ℝ) ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
    rw [Critical2DKPZ.norm_siteToPlane_sq]
    nlinarith
  have h0 : |(z 0 : ℝ)| ≤ ‖siteToPlane z‖ :=
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 (by simpa [sq_abs] using h0Sq)
  have h1 : |(z 1 : ℝ)| ≤ ‖siteToPlane z‖ :=
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 (by simpa [sq_abs] using h1Sq)
  constructor
  · calc
      _ ≤ |(z 0 : ℝ)| + |(z 1 : ℝ)| := abs_add_le _ _
      _ ≤ 2 * ‖siteToPlane z‖ := by linarith
  · calc
      _ ≤ |(z 0 : ℝ)| + |(z 1 : ℝ)| := by
        have h := abs_add_le (z 0 : ℝ) (-z 1)
        calc
          _ = |(z 0 : ℝ) + (-z 1)| := by rw [sub_eq_add_neg]
          _ ≤ |(z 0 : ℝ)| + |(z 1 : ℝ)| := by simpa using h
      _ ≤ 2 * ‖siteToPlane z‖ := by linarith

private theorem intCast_natCast_list_sum (ms : List ℕ) :
    (List.map Int.cast (List.map Nat.cast ms)).sum = (ms.sum : ℝ) := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_natCast,
        Nat.cast_add, ih]

private theorem scaledIndex_lower_bound (δ N n x j : ℝ)
    (hq : 0 < δ * N) (hn : δ * N ≤ n)
    (hx : -((δ / 4) * N) < x) (hj : 2 * j = n + x) :
    (δ / 4) * N < j := by nlinarith

private theorem scaledIndex_upper_bound (δ N n x j : ℝ)
    (hq : 0 < δ * N) (hn : δ * N ≤ n)
    (hx : x < (δ / 4) * N) (hj : 2 * j = n + x) :
    j < n - (δ / 4) * N := by nlinarith

private theorem scaledIndex_gt_short (q S j : ℝ)
    (hq : 0 < q) (hS : S < q / 8) (hj : q / 4 < j) : S < j := by nlinarith

private theorem scaledIndex_le_remainder (δ N n S L j : ℝ)
    (hq : 0 < δ * N) (hs : S < (δ / 8) * N) (hls : L + S = n)
    (hj : j < n - (δ / 4) * N) : j ≤ L := by nlinarith

/-- Mixed short and long hybrid compositions have the spatial heat profile of their total duration. The short blocks contribute a deterministic shift bounded by their total duration. -/
theorem eventually_largeBlockGaussianListPairLaw_heat_error_mixedBlocks
    (δ R ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ms : List ℕ, ms ≠ [] →
      ms.length ≤ spatialLogCutoff N ^ 2 →
      (∀ m ∈ ms, 0 < m) → δ * (N : ℝ) ≤ (ms.sum : ℝ) →
      (ms.sum : ℝ) ≤ N → ∀ z : Site,
      ∀ j₁ j₂ : ℕ, j₁ ∈ Finset.range (ms.sum + 1) →
        j₂ ∈ Finset.range (ms.sum + 1) →
        2 * (j₁ : ℤ) = (ms.sum : ℤ) + z 0 + z 1 →
        2 * (j₂ : ℤ) = (ms.sum : ℤ) + z 0 - z 1 →
        ‖siteToPlane z‖ ≤ R * Real.sqrt N →
        |(N / 4 : ℝ) * largeBlockGaussianListPairLaw
            (spatialLogCutoff N ^ 10) ms j₁ j₂ -
          heatKernel ((ms.sum : ℝ) / (2 * N))
            ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| < ε := by
  have hlong := eventually_largeBlockGaussianListPairLaw_heat_error_longBlocks
    (δ / 2) (ε / 3) (by positivity) (by positivity)
  have hshift := eventually_heatKernel_short_shift_error δ R (ε / 3)
    hδ (by positivity)
  have hcut := eventually_spatialLogCutoff_pow12_div_sqrt_lt
    (by positivity : (0 : ℝ) < δ / 8)
  have hrootT := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hR := hrootT.eventually_gt_atTop (8 * |R| / δ)
  filter_upwards [hlong, hshift, hcut, hR, eventually_ge_atTop 1]
    with N hlongN hshiftN hcutN hRN hN
  intro ms hne hlen hpositive hnLower hnUpper z j₁ j₂ hj₁ hj₂ h₁ h₂ hz
  let mCut : ℕ := spatialLogCutoff N ^ 10
  let short : List ℕ := ms.filter (fun m => m < mCut)
  let long : List ℕ := ms.filter (fun m => mCut ≤ m)
  let S : ℕ := short.sum
  let L : ℕ := long.sum
  let wa : ℕ → ℝ := largeBlockGaussianListLaw mCut short
  let wb : ℕ → ℝ := largeBlockGaussianListLaw mCut short
  let la : ℕ → ℝ := largeBlockGaussianListLaw mCut long
  let lb : ℕ → ℝ := largeBlockGaussianListLaw mCut long
  let A := Finset.range (S + 1)
  let B := Finset.range (S + 1)
  have hNpos : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hrootle : Real.sqrt (N : ℝ) ≤ (N : ℝ) := sqrtNat_le_nat N (by omega)
  have hcutroot : (spatialLogCutoff N : ℝ) ^ 12 /
      Real.sqrt (N : ℝ) < δ / 8 := by
    simpa only [spatialLogCutoff] using hcutN
  have hSboundNat : S ≤ ms.length * mCut := by
    have hfilter := list_sum_filter_lt_le_length_mul ms mCut
    have hlenFilter : short.length ≤ ms.length := List.length_filter_le _ _
    dsimp [S, short] at hfilter ⊢
    exact hfilter.trans (Nat.mul_le_mul_right mCut hlenFilter)
  have hlenR : (ms.length : ℝ) ≤ (spatialLogCutoff N : ℝ) ^ 2 := by
    exact_mod_cast hlen
  have hSbound : (S : ℝ) ≤ (spatialLogCutoff N : ℝ) ^ 12 := by
    have hSboundR : (S : ℝ) ≤ (ms.length : ℝ) *
        (spatialLogCutoff N : ℝ) ^ 10 := by
      exact_mod_cast hSboundNat
    calc
      _ ≤ (ms.length : ℝ) * (spatialLogCutoff N : ℝ) ^ 10 := hSboundR
      _ ≤ (spatialLogCutoff N : ℝ) ^ 2 *
          (spatialLogCutoff N : ℝ) ^ 10 :=
        mul_le_mul_of_nonneg_right hlenR (by positivity)
      _ = (spatialLogCutoff N : ℝ) ^ 12 := by ring
  have hSdiv : (S : ℝ) / (N : ℝ) < δ / 8 := by
    calc
      _ ≤ (spatialLogCutoff N : ℝ) ^ 12 / (N : ℝ) :=
        div_le_div_of_nonneg_right hSbound hNreal.le
      _ ≤ (spatialLogCutoff N : ℝ) ^ 12 / Real.sqrt (N : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hsqrt hrootle
      _ < δ / 8 := hcutroot
  have hsumSplit : L + S = ms.sum := by
    dsimp [L, S, long, short, mCut]
    have h := list_sum_filter_lt_add_ge
      (spatialLogCutoff N ^ 10) ms
    omega
  have hsumSplitR : (L : ℝ) + (S : ℝ) = (ms.sum : ℝ) := by
    exact_mod_cast hsumSplit
  have hLlower : (δ / 2) * (N : ℝ) ≤ (L : ℝ) := by
    have hSsmall : (S : ℝ) < (δ / 8) * (N : ℝ) :=
      (div_lt_iff₀ hNreal).1 hSdiv
    nlinarith [hnLower]
  have hLupper : (L : ℝ) ≤ N := by
    have hLle : L ≤ ms.sum := by omega
    have hLleR : (L : ℝ) ≤ (ms.sum : ℝ) := by exact_mod_cast hLle
    exact hLleR.trans hnUpper
  have hsumLS : L + S = ms.sum := hsumSplit
  have hlongLen : long.length ≤ ms.length := List.length_filter_le _ _
  have hlongLength : long.length ≤ spatialLogCutoff N ^ 2 :=
    hlongLen.trans hlen
  have hshortMem : ∀ m ∈ short, m < mCut := by
    intro m hm
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hlongMem : ∀ m ∈ long, mCut ≤ m := by
    intro m hm
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hshortLaw : ∀ j, wa j = hypergeometricBlockListLaw short j := by
    intro j
    exact largeBlockGaussianListLaw_eq_hypergeometric_of_all_lt
      mCut short hshortMem j
  have hmassA : ∑ a ∈ A, wa a = 1 := by
    simpa [A, S, wa, hshortLaw] using hypergeometricBlockListLaw_sum_one short
  have hmassB : ∑ b ∈ B, wb b = 1 := by
    simpa [B, S, wb, wa, hshortLaw] using hypergeometricBlockListLaw_sum_one short
  have hwa : ∀ a ∈ A, 0 ≤ wa a := by
    intro a ha
    rw [hshortLaw]
    exact hypergeometricBlockListLaw_nonneg short a
  have hwb : ∀ b ∈ B, 0 ≤ wb b := by
    intro b hb
    change 0 ≤ wa b
    rw [hshortLaw]
    exact hypergeometricBlockListLaw_nonneg short b
  have hRnonneg : 0 ≤ R := by
    by_contra hR
    have hR' : R < 0 := lt_of_not_ge hR
    have h := hz
    have hnorm : 0 ≤ ‖siteToPlane z‖ := norm_nonneg _
    nlinarith [Real.sqrt_pos.mpr hNreal]
  have hRratio : |R| / Real.sqrt (N : ℝ) < δ / 8 := by
    rw [abs_of_nonneg hRnonneg]
    apply (div_lt_iff₀ hsqrt).2
    have hRN' : 8 * |R| < (Real.sqrt (N : ℝ)) * δ :=
      (div_lt_iff₀ hδ).1 hRN
    rw [abs_of_nonneg hRnonneg] at hRN'
    nlinarith [hRN']
  have hRscale : 2 * (R * Real.sqrt (N : ℝ)) < (δ / 4) * (N : ℝ) := by
    have hsquare : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by
      calc
        _ = Real.sqrt (N : ℝ) ^ 2 := by ring
        _ = (N : ℝ) := Real.sq_sqrt hNreal.le
    have hratio2 : 2 * (R / Real.sqrt (N : ℝ)) < δ / 4 := by
      rw [abs_of_nonneg hRnonneg] at hRratio
      nlinarith [hRratio]
    calc
      _ = 2 * (R / Real.sqrt (N : ℝ)) * (N : ℝ) := by
        calc
          _ = 2 * (R / Real.sqrt (N : ℝ)) *
              (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by
            field_simp [hsqrt.ne']
          _ = _ := by rw [hsquare]
      _ < (δ / 4) * (N : ℝ) := mul_lt_mul_of_pos_right hratio2 hNreal
  have hcoords := siteToPlane_sum_difference_norm_bound z
  have hcoordPlus : |(z 0 : ℝ) + z 1| < (δ / 4) * (N : ℝ) :=
    (hcoords.1.trans (mul_le_mul_of_nonneg_left hz
      (by norm_num : (0 : ℝ) ≤ 2))).trans_lt hRscale
  have hcoordMinus : |(z 0 : ℝ) - z 1| < (δ / 4) * (N : ℝ) :=
    (hcoords.2.trans (mul_le_mul_of_nonneg_left hz
      (by norm_num : (0 : ℝ) ≤ 2))).trans_lt hRscale
  have hj₁real : 2 * (j₁ : ℝ) = (ms.sum : ℝ) + z 0 + z 1 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) h₁
    push_cast at h
    rw [intCast_natCast_list_sum] at h
    exact h
  have hj₂real : 2 * (j₂ : ℝ) = (ms.sum : ℝ) + z 0 - z 1 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) h₂
    push_cast at h
    rw [intCast_natCast_list_sum] at h
    exact h
  have hidx₁lower : (δ / 4) * (N : ℝ) < (j₁ : ℝ) := by
    have hplusLower := (abs_lt.mp hcoordPlus).1
    have hj₁real' : 2 * (j₁ : ℝ) = (ms.sum : ℝ) +
        ((z 0 : ℝ) + z 1) := by linear_combination hj₁real
    exact scaledIndex_lower_bound δ (N : ℝ) (ms.sum : ℝ)
      ((z 0 : ℝ) + z 1) (j₁ : ℝ) (by positivity) hnLower hplusLower hj₁real'
  have hidx₂lower : (δ / 4) * (N : ℝ) < (j₂ : ℝ) := by
    have hminusLower := (abs_lt.mp hcoordMinus).1
    have hj₂real' : 2 * (j₂ : ℝ) = (ms.sum : ℝ) +
        ((z 0 : ℝ) - z 1) := by linear_combination hj₂real
    exact scaledIndex_lower_bound δ (N : ℝ) (ms.sum : ℝ)
      ((z 0 : ℝ) - z 1) (j₂ : ℝ) (by positivity) hnLower hminusLower hj₂real'
  have hidx₁upper : (j₁ : ℝ) < (ms.sum : ℝ) - (δ / 4) * (N : ℝ) := by
    have hplusUpper := (abs_lt.mp hcoordPlus).2
    have hj₁real' : 2 * (j₁ : ℝ) = (ms.sum : ℝ) +
        ((z 0 : ℝ) + z 1) := by linear_combination hj₁real
    exact scaledIndex_upper_bound δ (N : ℝ) (ms.sum : ℝ)
      ((z 0 : ℝ) + z 1) (j₁ : ℝ) (by positivity) hnLower hplusUpper hj₁real'
  have hidx₂upper : (j₂ : ℝ) < (ms.sum : ℝ) - (δ / 4) * (N : ℝ) := by
    have hminusUpper := (abs_lt.mp hcoordMinus).2
    have hj₂real' : 2 * (j₂ : ℝ) = (ms.sum : ℝ) +
        ((z 0 : ℝ) - z 1) := by linear_combination hj₂real
    exact scaledIndex_upper_bound δ (N : ℝ) (ms.sum : ℝ)
      ((z 0 : ℝ) - z 1) (j₂ : ℝ) (by positivity) hnLower hminusUpper hj₂real'
  have hSL : (S : ℝ) < (δ / 8) * (N : ℝ) := (div_lt_iff₀ hNreal).1 hSdiv
  have hSL' : (S : ℝ) < δ * (N : ℝ) / 8 := by
    convert hSL using 1
    ring
  have hidx₁lower' : δ * (N : ℝ) / 4 < (j₁ : ℝ) := by
    convert hidx₁lower using 1
    ring
  have hidx₂lower' : δ * (N : ℝ) / 4 < (j₂ : ℝ) := by
    convert hidx₂lower using 1
    ring
  have hJ₁S : S ≤ j₁ := by
    have hshort := scaledIndex_gt_short (δ * (N : ℝ))
      (S : ℝ) (j₁ : ℝ) (by positivity) hSL' hidx₁lower'
    exact_mod_cast le_of_lt hshort
  have hJ₂S : S ≤ j₂ := by
    have hshort := scaledIndex_gt_short (δ * (N : ℝ))
      (S : ℝ) (j₂ : ℝ) (by positivity) hSL' hidx₂lower'
    exact_mod_cast le_of_lt hshort
  have hJ₁L : j₁ ≤ L := by
    have h : (j₁ : ℝ) ≤ (L : ℝ) := scaledIndex_le_remainder δ
      (N : ℝ) (ms.sum : ℝ) (S : ℝ) (L : ℝ) (j₁ : ℝ)
      (by positivity) hSL hsumSplitR hidx₁upper
    exact_mod_cast h
  have hJ₂L : j₂ ≤ L := by
    have h : (j₂ : ℝ) ≤ (L : ℝ) := scaledIndex_le_remainder δ
      (N : ℝ) (ms.sum : ℝ) (S : ℝ) (L : ℝ) (j₂ : ℝ)
      (by positivity) hSL hsumSplitR hidx₂upper
    exact_mod_cast h
  have hAeq : (Finset.range (S + 1)).filter
      (fun a => a ≤ j₁ ∧ j₁ - a ≤ L) = A := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, A]
    constructor
    · rintro ⟨ha, _⟩
      exact ha
    · intro ha
      have haS : a ≤ S := Nat.le_of_lt_succ ha
      exact ⟨ha, ⟨by omega, by omega⟩⟩
  have hBeq : (Finset.range (S + 1)).filter
      (fun b => b ≤ j₂ ∧ j₂ - b ≤ L) = B := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, B]
    constructor
    · rintro ⟨hb, _⟩
      exact hb
    · intro hb
      have hbS : b ≤ S := Nat.le_of_lt_succ hb
      exact ⟨hb, ⟨by omega, by omega⟩⟩
  have hpairDecomp := largeBlockGaussianListPairLaw_eq_short_long_sum
    mCut ms j₁ j₂
  rw [show (ms.filter (fun m => m < mCut)).sum = S by rfl,
    show (ms.filter (fun m => mCut ≤ m)).sum = L by rfl,
    hAeq, hBeq] at hpairDecomp
  have hpairFactor : largeBlockGaussianListPairLaw mCut ms j₁ j₂ =
      ∑ b ∈ B, wb b * (∑ a ∈ A, wa a *
        (la (j₁ - a) * lb (j₂ - b))) := by
    rw [hpairDecomp]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [wa, wb, la, lb]
    ring
  have hscaledDecomp :
      (N / 4 : ℝ) * largeBlockGaussianListPairLaw mCut ms j₁ j₂ =
        ∑ b ∈ B, wb b * (∑ a ∈ A, wa a *
          ((N / 4 : ℝ) * (la (j₁ - a) * lb (j₂ - b)))) := by
    rw [hpairFactor]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      _ = wb b * ((N / 4 : ℝ) *
          (∑ a ∈ A, wa a * (la (j₁ - a) * lb (j₂ - b)))) := by ring
      _ = wb b * (∑ a ∈ A, (N / 4 : ℝ) *
          (wa a * (la (j₁ - a) * lb (j₂ - b)))) := by rw [Finset.mul_sum]
      _ = wb b * (∑ a ∈ A, wa a *
          ((N / 4 : ℝ) * (la (j₁ - a) * lb (j₂ - b)))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [wa, wb, la, lb]
        ring
  have hlongNonempty : long ≠ [] := by
    intro h
    simp [h, L] at hLlower
    nlinarith [hδ, hNreal]
  have hlongPositive : ∀ m ∈ long, 0 < m := by
    intro m hm
    exact hpositive m ((List.mem_filter.mp hm).1)
  have hlongCut : ∀ m ∈ long, spatialLogCutoff N ^ 10 ≤ m := by
    intro m hm
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hlongPoint (a : ℕ) (ha : a ∈ A) (b : ℕ) (hb : b ∈ B) :
      |(N / 4 : ℝ) * (la (j₁ - a) * lb (j₂ - b)) -
        heatKernel ((L : ℝ) / (2 * N))
          ((Real.sqrt (N / 2))⁻¹ • siteToPlane
            (shortShiftSite z S a b))| ≤ ε / 3 := by
    have haS : a ≤ S := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbS : b ≤ S := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have haJ : a ≤ j₁ := le_trans haS hJ₁S
    have hbJ : b ≤ j₂ := le_trans hbS hJ₂S
    have haL : j₁ - a ≤ L := by omega
    have hbL : j₂ - b ≤ L := by omega
    have h₁long : 2 * ((j₁ - a : ℕ) : ℤ) =
        (L : ℤ) + (shortShiftSite z S a b) 0 +
          (shortShiftSite z S a b) 1 := by
      have hsumZ : (ms.sum : ℤ) = (L : ℤ) + (S : ℤ) := by
        exact_mod_cast hsumSplit.symm
      have hsub : ((j₁ - a : ℕ) : ℤ) = (j₁ : ℤ) - a := by
        simp [Nat.cast_sub haJ]
      rw [hsub]
      simp [shortShiftSite]
      omega
    have h₂long : 2 * ((j₂ - b : ℕ) : ℤ) =
        (L : ℤ) + (shortShiftSite z S a b) 0 -
          (shortShiftSite z S a b) 1 := by
      have hsumZ : (ms.sum : ℤ) = (L : ℤ) + (S : ℤ) := by
        exact_mod_cast hsumSplit.symm
      have hsub : ((j₂ - b : ℕ) : ℤ) = (j₂ : ℤ) - b := by
        simp [Nat.cast_sub hbJ]
      rw [hsub]
      simp [shortShiftSite]
      omega
    have hlongHeat := hlongN long hlongNonempty hlongLength hlongPositive
      hlongCut hLlower hLupper (shortShiftSite z S a b)
      (j₁ - a) (j₂ - b)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le haL))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hbL)) h₁long h₂long
    simpa [largeBlockGaussianListPairLaw, la, lb, L] using hlongHeat.le
  have hshiftPoint (a : ℕ) (ha : a ∈ A) (b : ℕ) (hb : b ∈ B) :
      |heatKernel ((L : ℝ) / (2 * N))
          ((Real.sqrt (N / 2))⁻¹ • siteToPlane (shortShiftSite z S a b)) -
        heatKernel ((ms.sum : ℝ) / (2 * N))
          ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| ≤ ε / 3 := by
    have haS : a ≤ S := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbS : b ≤ S := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have h := hshiftN (ms.sum) L S (by exact_mod_cast hnLower)
      (by exact_mod_cast hnUpper) hsumLS hSbound z hz a b haS hbS
    exact h.le
  let f : ℕ → ℕ → ℝ := fun a b =>
    (N / 4 : ℝ) * (la (j₁ - a) * lb (j₂ - b))
  let g : ℕ → ℕ → ℝ := fun a b =>
    heatKernel ((L : ℝ) / (2 * N))
      ((Real.sqrt (N / 2))⁻¹ • siteToPlane (shortShiftSite z S a b))
  let H : ℝ := heatKernel ((ms.sum : ℝ) / (2 * N))
    ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)
  have hlongAverage := abs_double_sum_weighted_error_le B A wb wa
    (fun b a => f a b) (fun b a => g a b) (ε / 3)
    hwb hwa hmassB hmassA (by
      intro b hb a ha
      simpa [f, g] using hlongPoint a ha b hb)
  have hshiftAverage := abs_double_sum_weighted_error_le B A wb wa
    (fun b a => g a b) (fun _ _ => H) (ε / 3) hwb hwa hmassB hmassA (by
      intro b hb a ha
      simpa [g, H] using hshiftPoint a ha b hb)
  have hconst : ∑ b ∈ B, wb b * (∑ a ∈ A, wa a * H) = H := by
    have haconst (b : ℕ) : ∑ a ∈ A, wa a * H = H := by
      calc
        _ = (∑ a ∈ A, wa a) * H := by rw [← Finset.sum_mul]
        _ = H := by rw [hmassA]; ring
    calc
      _ = ∑ b ∈ B, wb b * H := by
        apply Finset.sum_congr rfl
        intro b hb
        exact congrArg (fun x : ℝ => wb b * x) (haconst b)
      _ = (∑ b ∈ B, wb b) * H := by rw [Finset.sum_mul]
      _ = H := by rw [hmassB]; ring
  have hscaledError :
      |(N / 4 : ℝ) * largeBlockGaussianListPairLaw mCut ms j₁ j₂ - H| ≤
        ε / 3 + ε / 3 := by
    calc
      _ ≤ |(N / 4 : ℝ) * largeBlockGaussianListPairLaw mCut ms j₁ j₂ -
            (∑ b ∈ B, wb b * (∑ a ∈ A, wa a * g a b))| +
          |(∑ b ∈ B, wb b * (∑ a ∈ A, wa a * g a b)) - H| := abs_sub_le _ _ _
      _ = |(∑ b ∈ B, wb b * (∑ a ∈ A, wa a * f a b)) -
            (∑ b ∈ B, wb b * (∑ a ∈ A, wa a * g a b))| +
          |(∑ b ∈ B, wb b * (∑ a ∈ A, wa a * g a b)) -
            (∑ b ∈ B, wb b * (∑ a ∈ A, wa a * H))| := by rw [hscaledDecomp, hconst]
      _ ≤ ε / 3 + ε / 3 := add_le_add hlongAverage hshiftAverage
  have hfinal :
      |(N / 4 : ℝ) * largeBlockGaussianListPairLaw mCut ms j₁ j₂ - H| < ε := by
    exact lt_of_le_of_lt hscaledError (by linarith)
  simpa [mCut, H] using hfinal

end Critical2DKPZ.SHF.Moments

end
