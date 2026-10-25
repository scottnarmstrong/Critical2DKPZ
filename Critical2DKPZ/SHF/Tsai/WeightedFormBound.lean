/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.SHF.DeltaBose.FormBounds
public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
import Mathlib.Tactic

/-! # Weighted positive bilinear kernel bounds -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The bound `⟨g, K f⟩ ≤ c ‖f e^{wY}‖_p ‖g e^{wX}‖_{p'}` for nonnegative `f, g`, with `p'` the exponent of the test `g`.
At `p = p' = 2` and zero weights this is `FormBound`. -/
def WeightedFormBound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (wX : X → ℝ) (wY : Y → ℝ) (p p' : ℝ)
    (K : X → Y → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  ∀ f : Y → ℝ≥0∞, ∀ g : X → ℝ≥0∞, Measurable f → Measurable g →
    (∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ) ≤
      c * (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p) *
        (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p')

/-- The unweighted `L²` form bound is the zero-weight case of
`WeightedFormBound`. -/
theorem WeightedFormBound.ofFormBound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : X → Y → ℝ≥0∞} {c : ℝ≥0∞}
    (h : FormBound μ ν K c) :
    WeightedFormBound μ ν (fun _ => 0) (fun _ => 0) 2 2 K c := by
  intro f g hf hg
  simpa only [WeightedFormBound, Real.exp_zero, ENNReal.ofReal_one, mul_one] using
    h f g hf hg

/-- Pointwise smaller positive kernels inherit weighted bilinear bounds. -/
theorem WeightedFormBound.mono {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ}
    {K L : X → Y → ℝ≥0∞} {c d : ℝ≥0∞}
    (h : WeightedFormBound μ ν wX wY p p' K c) (hLK : ∀ x y, L x y ≤ K x y) (hcd : c ≤ d) :
    WeightedFormBound μ ν wX wY p p' L d := by
  intro f g hf hg
  have hAction (x : X) :
      (∫⁻ y, L x y * f y ∂ν) ≤ ∫⁻ y, K x y * f y ∂ν := by
    apply lintegral_mono
    intro y
    exact mul_le_mul' (hLK x y) le_rfl
  calc
    (∫⁻ x, g x * (∫⁻ y, L x y * f y ∂ν) ∂μ) ≤
        ∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ := by
          apply lintegral_mono
          intro x
          exact mul_le_mul' le_rfl (hAction x)
    _ ≤ c * (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p) *
          (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') := h f g hf hg
    _ ≤ d * (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p) *
          (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') := by
          exact mul_le_mul' (mul_le_mul' hcd le_rfl) le_rfl

/-- Sums of measurable positive kernels inherit the sum of their weighted form bounds. -/
theorem WeightedFormBound.add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν] {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ}
    {K L : X → Y → ℝ≥0∞} {c d : ℝ≥0∞}
    (hKm : Measurable (Function.uncurry K)) (hLm : Measurable (Function.uncurry L))
    (hK : WeightedFormBound μ ν wX wY p p' K c)
    (hL : WeightedFormBound μ ν wX wY p p' L d) :
    WeightedFormBound μ ν wX wY p p' (fun x y => K x y + L x y) (c + d) := by
  intro f g hf hg
  let A : X → ℝ≥0∞ := fun x => ∫⁻ y, K x y * f y ∂ν
  let B : X → ℝ≥0∞ := fun x => ∫⁻ y, L x y * f y ∂ν
  have hA : Measurable A := measurable_kernelAction ν hKm hf
  have hB : Measurable B := measurable_kernelAction ν hLm hf
  have hInner (x : X) :
      (∫⁻ y, (K x y + L x y) * f y ∂ν) = A x + B x := by
    have hKx : Measurable (fun y : Y => K x y * f y) := by
      exact (hKm.comp (measurable_const.prodMk measurable_id)).mul hf
    calc
      _ = ∫⁻ y, K x y * f y + L x y * f y ∂ν := by
        apply lintegral_congr
        intro y
        simp only [add_mul]
      _ = A x + B x := by
        dsimp [A, B]
        rw [lintegral_add_left hKx]
  have hOuter :
      (∫⁻ x, g x * (A x + B x) ∂μ) =
        (∫⁻ x, g x * A x ∂μ) + (∫⁻ x, g x * B x ∂μ) := by
    have hterm : Measurable (fun x => g x * A x) := hg.mul hA
    calc
      _ = ∫⁻ x, g x * A x + g x * B x ∂μ := by
        apply lintegral_congr
        intro x
        rw [mul_add]
      _ = _ := by rw [lintegral_add_left hterm]
  let NF : ℝ≥0∞ := (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p : ℝ)
  let NG : ℝ≥0∞ := (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p' : ℝ)
  calc
    (∫⁻ x, g x * (∫⁻ y, (K x y + L x y) * f y ∂ν) ∂μ) =
        (∫⁻ x, g x * A x ∂μ) + (∫⁻ x, g x * B x ∂μ) := by
          rw [show (fun x => g x * (∫⁻ y, (K x y + L x y) * f y ∂ν)) =
            fun x => g x * (A x + B x) by
              funext x
              rw [hInner x], hOuter]
    _ ≤ c * NF * NG + d * NF * NG :=
          add_le_add (by simpa [A, NF, NG] using hK f g hf hg)
            (by simpa [B, NF, NG] using hL f g hf hg)
    _ = (c + d) * NF * NG := by ring

/-- Countable sums of measurable positive kernels inherit the sum of their weighted bounds. -/
theorem WeightedFormBound.tsum {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable ι] {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ} {K : ι → X → Y → ℝ≥0∞}
    {c : ι → ℝ≥0∞} (hm : ∀ i, Measurable (Function.uncurry (K i)))
    (h : ∀ i, WeightedFormBound μ ν wX wY p p' (K i) (c i)) :
    WeightedFormBound μ ν wX wY p p' (fun x y => ∑' i, K i x y) (∑' i, c i) := by
  intro f g hf hg
  let A : ι → X → ℝ≥0∞ := fun i x => ∫⁻ y, K i x y * f y ∂ν
  have hAmeas (i : ι) : Measurable (A i) := measurable_kernelAction ν (hm i) hf
  have hInner (x : X) :
      (∫⁻ y, (∑' i, K i x y) * f y ∂ν) = ∑' i, A i x := by
    calc
      _ = ∫⁻ y, ∑' i, K i x y * f y ∂ν := by
        apply lintegral_congr
        intro y
        rw [← ENNReal.tsum_mul_right]
      _ = ∑' i, ∫⁻ y, K i x y * f y ∂ν := by
        apply lintegral_tsum
        intro i
        have hx : Measurable (fun y : Y => (x, y)) := by fun_prop
        exact (((hm i).comp hx).mul hf).aemeasurable
      _ = ∑' i, A i x := rfl
  let NF : ℝ≥0∞ := (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p : ℝ)
  let NG : ℝ≥0∞ := (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p' : ℝ)
  calc
    (∫⁻ x, g x * (∫⁻ y, (∑' i, K i x y) * f y ∂ν) ∂μ) =
        ∑' i, (∫⁻ x, g x * A i x ∂μ) := by
          calc
            _ = ∫⁻ x, ∑' i, g x * A i x ∂μ := by
              apply lintegral_congr
              intro x
              rw [hInner x, ← ENNReal.tsum_mul_left]
            _ = ∑' i, (∫⁻ x, g x * A i x ∂μ) := by
              apply lintegral_tsum
              intro i
              exact (hg.mul (hAmeas i)).aemeasurable
    _ ≤ ∑' i, (c i * NF * NG) := by
          apply ENNReal.tsum_le_tsum
          intro i
          simpa [WeightedFormBound, A, NF, NG] using h i f g hf hg
    _ = (∑' i, c i) * NF * NG := by
          rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]

private theorem ennreal_half_rpow_mul_self_t (x : ℝ≥0∞) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
    (by norm_num) (by norm_num)]
  norm_num

private theorem iSup_min_nat_sq_t (x : ℝ≥0∞) :
    (⨆ k : ℕ, min x (k : ℝ≥0∞) ^ 2) = x ^ 2 := by
  apply le_antisymm
  · exact iSup_le fun k =>
      pow_le_pow_left₀ (by positivity) (min_le_left _ _) _
  · by_cases hx : x = ⊤
    · subst x
      have hnat : (⨆ k : ℕ, (k : ℝ≥0∞)) = ⊤ := ENNReal.iSup_natCast
      have hsq : (⨆ k : ℕ, (k : ℝ≥0∞) ^ 2) = ⊤ := by
        apply top_unique
        rw [← hnat]
        apply iSup_le
        intro k
        apply le_iSup_of_le (k + 1)
        have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
          push_cast
          nlinarith [sq_nonneg (k : ℝ)]
        exact_mod_cast hk
      simp [hsq]
    · have hx' : x < ⊤ := lt_top_iff_ne_top.mpr hx
      obtain ⟨r, rfl, _⟩ := ENNReal.lt_iff_exists_coe.mp hx'
      obtain ⟨k, hk⟩ := exists_nat_gt (r : ℝ)
      have hle : (r : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast (le_of_lt hk)
      exact le_iSup_of_le k (by simp [min_eq_left hle])

private theorem bilinear_sq_le_finite_trunc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {B : X → ℝ≥0∞} (hB : Measurable B) {C : ℝ≥0∞}
    (hpair : ∀ g : X → ℝ≥0∞, Measurable g →
      (∫⁻ x, g x * B x ∂μ) ≤ C * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ))
    (s : Set X) (hs : MeasurableSet s) (hsμ : μ s < ⊤) (k : ℕ) :
    (∫⁻ x, (s.indicator (fun x => min (B x) (k : ℝ≥0∞)) x) ^ 2 ∂μ) ≤ C ^ 2 := by
  let g : X → ℝ≥0∞ := s.indicator (fun x => min (B x) (k : ℝ≥0∞))
  have hg : Measurable g := by
    dsimp [g]
    exact (hB.min measurable_const).indicator hs
  let L : ℝ≥0∞ := ∫⁻ x, g x ^ (2 : ℝ) ∂μ
  have hL_eq : L = ∫⁻ x, g x ^ 2 ∂μ := by
    dsimp [L]
    congr 1
    funext x
    simp [pow_two]
  have hLboundNat : (∫⁻ x, g x ^ 2 ∂μ) ≤ (k : ℝ≥0∞) ^ 2 * μ s := by
    let b : X → ℝ≥0∞ := s.indicator (fun _ => (k : ℝ≥0∞) ^ 2)
    have hpoint : g ^ 2 ≤ b := by
      intro x
      by_cases hx : x ∈ s
      · have hm : min (B x) (k : ℝ≥0∞) ≤ (k : ℝ≥0∞) := min_le_right _ _
        simpa [g, b, hx] using pow_le_pow_left₀ (by positivity) hm (2 : ℕ)
      · simp [g, b, Set.indicator_of_notMem hx]
    calc
      _ ≤ ∫⁻ x, b x ∂μ := lintegral_mono hpoint
      _ = (k : ℝ≥0∞) ^ 2 * μ s := by
        rw [lintegral_indicator hs, setLIntegral_const]
  have hLbound : L ≤ (k : ℝ≥0∞) ^ 2 * μ s := hL_eq.trans_le hLboundNat
  have hLtop : L ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)) (ne_of_lt hsμ))
    exact hLbound
  have hLower : L ≤ ∫⁻ x, g x * B x ∂μ := by
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ s
    · simp only [ENNReal.rpow_two, g, Set.indicator_of_mem hx]
      simpa [pow_two] using mul_le_mul' (le_refl (min (B x) (k : ℝ≥0∞))) (min_le_left _ _)
    · simp [g, Set.indicator_of_notMem hx]
  have hEstimate : L ≤ C * L ^ (1 / 2 : ℝ) := by
    calc
      L ≤ ∫⁻ x, g x * B x ∂μ := hLower
      _ ≤ C * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hpair g hg
      _ = C * L ^ (1 / 2 : ℝ) := rfl
  by_cases hLzero : L = 0
  · calc
      (∫⁻ x, g x ^ 2 ∂μ) = L := hL_eq.symm
      _ = 0 := hLzero
      _ ≤ C ^ 2 := bot_le
  · let R : ℝ≥0∞ := L ^ (1 / 2 : ℝ)
    have hRsq : R * R = L := ennreal_half_rpow_mul_self_t L
    have hRzero : R ≠ 0 := by
      intro hR
      apply hLzero
      calc
        L = R * R := hRsq.symm
        _ = 0 := by simp [hR]
    have hRtop : R ≠ ⊤ := by
      intro hR
      apply hLtop
      calc
        L = R * R := hRsq.symm
        _ = ⊤ := by simp [hR]
    have hRoot : R ≤ C := by
      apply (ENNReal.mul_le_mul_iff_left hRzero hRtop).mp
      calc
        R * R = L := hRsq
        _ ≤ C * R := by simpa [R] using hEstimate
    have hSquared := mul_le_mul hRoot hRoot (by positivity) (by positivity)
    calc
      (∫⁻ x, g x ^ 2 ∂μ) = L := hL_eq.symm
      _ = R * R := hRsq.symm
      _ ≤ C ^ 2 := by simpa only [pow_two] using hSquared

private theorem bilinear_sq_le_sigmaFinite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] [SigmaFinite μ] {B : X → ℝ≥0∞} (hB : Measurable B)
    {C : ℝ≥0∞}
    (hpair : ∀ g : X → ℝ≥0∞, Measurable g →
      (∫⁻ x, g x * B x ∂μ) ≤ C * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) :
    (∫⁻ x, B x ^ (2 : ℝ) ∂μ) ≤ C ^ 2 := by
  let q : ℕ → X → ℝ≥0∞ := fun n x =>
    ((spanningSets μ n).indicator (fun x => min (B x) (n : ℝ≥0∞)) x) ^ 2
  have hqmeas (n : ℕ) : Measurable (q n) := by
    dsimp [q]
    exact ((hB.min measurable_const).indicator (measurableSet_spanningSets μ n)).pow_const _
  have hqmono : Monotone q := by
    intro n m hnm x
    dsimp [q]
    by_cases hx : x ∈ spanningSets μ n
    · have hxm : x ∈ spanningSets μ m := (monotone_spanningSets μ hnm) hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxm]
      exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ (by exact_mod_cast hnm)) _
    · simp [Set.indicator_of_notMem hx]
  have hqsup (x : X) : (⨆ n, q n x) = B x ^ (2 : ℝ) := by
    let Hx := B x
    have hcover : x ∈ ⋃ n : ℕ, spanningSets μ n := by
      rw [iUnion_spanningSets μ]
      exact mem_univ x
    obtain ⟨N, hN⟩ := mem_iUnion.mp hcover
    have hsupNat : (⨆ n, q n x) = Hx ^ 2 := by
      apply le_antisymm
      · apply iSup_le
        intro n
        dsimp [q]
        by_cases hx : x ∈ spanningSets μ n
        · simp only [Set.indicator_of_mem hx]
          exact pow_le_pow_left₀ (by positivity) (min_le_left _ _) _
        · simp [Set.indicator_of_notMem hx]
      · calc
          Hx ^ 2 = ⨆ k : ℕ, min Hx (k : ℝ≥0∞) ^ 2 := (iSup_min_nat_sq_t Hx).symm
          _ ≤ ⨆ n : ℕ, q n x := by
            apply iSup_le
            intro k
            let n := max N k
            have hNn : N ≤ n := le_max_left _ _
            have hkn : k ≤ n := le_max_right _ _
            have hxn : x ∈ spanningSets μ n := (monotone_spanningSets μ hNn) hN
            have hcut : (k : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hkn
            apply le_iSup_of_le n
            dsimp [q]
            rw [Set.indicator_of_mem hxn]
            exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hcut) _
    simpa only [ENNReal.rpow_two] using hsupNat
  calc
    (∫⁻ x, B x ^ (2 : ℝ) ∂μ) = ∫⁻ x, (⨆ n, q n x) ∂μ := by
      congr 1
      funext x
      exact (hqsup x).symm
    _ = ⨆ n, ∫⁻ x, q n x ∂μ := lintegral_iSup hqmeas hqmono
    _ ≤ C ^ 2 := by
      apply iSup_le
      intro n
      simpa [q] using bilinear_sq_le_finite_trunc μ hB hpair
        (spanningSets μ n) (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n) n

private theorem bilinear_l2_norm_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] [SigmaFinite μ] {B : X → ℝ≥0∞} (hB : Measurable B)
    {C : ℝ≥0∞}
    (hpair : ∀ g : X → ℝ≥0∞, Measurable g →
      (∫⁻ x, g x * B x ∂μ) ≤ C * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) :
    (∫⁻ x, B x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ C := by
  have hsq := bilinear_sq_le_sigmaFinite μ hB hpair
  calc
    (∫⁻ x, B x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ (C ^ 2 * 1) ^ (1 / 2 : ℝ) := by
      apply ENNReal.monotone_rpow_of_nonneg (by norm_num)
      simpa using hsq
    _ = C := by
      rw [mul_one]
      rw [← ENNReal.rpow_natCast_mul C 2 (1 / 2 : ℝ)]
      norm_num

private theorem iSup_min_nat_t (x : ℝ≥0∞) :
    (⨆ n : ℕ, min x (n : ℝ≥0∞)) = x := by
  apply le_antisymm
  · exact iSup_le fun n => min_le_left _ _
  · by_cases hx : x = ⊤
    · subst x
      simpa using (ENNReal.iSup_natCast : (⨆ n : ℕ, (n : ℝ≥0∞)) = ⊤)
    · obtain ⟨r, rfl, _⟩ := ENNReal.lt_iff_exists_coe.mp (lt_top_iff_ne_top.mpr hx)
      obtain ⟨n, hn⟩ := exists_nat_gt r
      apply le_iSup_of_le n
      rw [min_eq_left]
      exact_mod_cast (le_of_lt hn)

/-- A bilinear estimate against every measurable test function controls the
`Lᵖ` norm of its nonnegative density. This is the finite-truncation duality
argument for a SigmaFinite measure. -/
private theorem bilinear_lp_norm_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {p p' : ℝ} (hpq : p.HolderConjugate p')
    {B : X → ℝ≥0∞} {D : ℝ≥0∞} (hB : Measurable B)
    (hpair : ∀ g : X → ℝ≥0∞, Measurable g →
      (∫⁻ x, g x * B x ∂μ) ≤ D *
        (∫⁻ x, g x ^ p' ∂μ) ^ (1 / p' : ℝ)) :
    (∫⁻ x, B x ^ p ∂μ) ^ (1 / p : ℝ) ≤ D := by
  have hp : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp'0 : 0 < p' := hpq.symm.pos
  have hpInv : 0 < 1 / p := by positivity
  have hp'Inv : 0 < 1 / p' := by positivity
  have hrecip : 1 / p + 1 / p' = 1 := by
    simpa only [one_div] using (Real.holderConjugate_iff.mp hpq).2
  let A : ℕ → X → ℝ≥0∞ := fun n x =>
    (spanningSets μ n).indicator (fun x => min (B x ^ p) (n : ℝ≥0∞)) x
  have hAmeas (n : ℕ) : Measurable (A n) := by
    dsimp [A]
    exact (((ENNReal.continuous_rpow_const (y := p)).measurable.comp hB).min
      measurable_const).indicator
      (measurableSet_spanningSets μ n)
  have hAmono : Monotone A := by
    intro n m hnm x
    dsimp [A]
    by_cases hx : x ∈ spanningSets μ n
    · have hxm : x ∈ spanningSets μ m := (monotone_spanningSets μ hnm) hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxm]
      exact min_le_min_left _ (by exact_mod_cast hnm)
    · simp [Set.indicator_of_notMem hx]
  have hAsup (x : X) : (⨆ n, A n x) = B x ^ p := by
    have hcover : x ∈ ⋃ n : ℕ, spanningSets μ n := by
      rw [iUnion_spanningSets μ]
      exact mem_univ x
    obtain ⟨N, hN⟩ := mem_iUnion.mp hcover
    apply le_antisymm
    · apply iSup_le
      intro n
      dsimp [A]
      by_cases hx : x ∈ spanningSets μ n
      · simp only [Set.indicator_of_mem hx]
        exact min_le_left _ _
      · simp [Set.indicator_of_notMem hx]
    · calc
        B x ^ p = ⨆ k : ℕ, min (B x ^ p) (k : ℝ≥0∞) := (iSup_min_nat_t _).symm
        _ ≤ ⨆ n : ℕ, A n x := by
          apply iSup_le
          intro k
          let n := max N k
          have hNn : N ≤ n := le_max_left _ _
          have hkn : k ≤ n := le_max_right _ _
          have hxn : x ∈ spanningSets μ n := (monotone_spanningSets μ hNn) hN
          have hcut : (k : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hkn
          apply le_iSup_of_le n
          dsimp [A]
          rw [Set.indicator_of_mem hxn]
          exact min_le_min_left _ hcut
  let L (n : ℕ) : ℝ≥0∞ := ∫⁻ x, A n x ∂μ
  have hLtop (n : ℕ) : L n ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (lt_top_iff_ne_top.mp (measure_spanningSets_lt_top μ n)))
    calc
      L n ≤ ∫⁻ x, (spanningSets μ n).indicator (fun _ => (n : ℝ≥0∞)) x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ spanningSets μ n
        · simp only [A, Set.indicator_of_mem hx]
          exact min_le_right _ _
        · simp [A, Set.indicator_of_notMem hx]
      _ = (n : ℝ≥0∞) * μ (spanningSets μ n) := by
        rw [lintegral_indicator (measurableSet_spanningSets μ n), setLIntegral_const]
  have hLbound (n : ℕ) : L n ≤ D ^ p := by
    let q : X → ℝ≥0∞ := fun x =>
      (spanningSets μ n).indicator (fun x => (min (B x ^ p) (n : ℝ≥0∞)) ^ (1 / p' : ℝ)) x
    have hq : Measurable q := by
      dsimp [q]
      exact ((ENNReal.continuous_rpow_const (y := 1 / p')).measurable.comp
        (((ENNReal.continuous_rpow_const (y := p)).measurable.comp hB).min
          measurable_const)).indicator (measurableSet_spanningSets μ n)
    have hqpow (x : X) : q x ^ p' = A n x := by
      by_cases hx : x ∈ spanningSets μ n
      · simp only [q, A, Set.indicator_of_mem hx]
        rw [← ENNReal.rpow_mul]
        rw [show (1 / p' : ℝ) * p' = 1 by field_simp]
        exact ENNReal.rpow_one _
      · simp [q, A, Set.indicator_of_notMem hx, hp'0]
    have hpoint (x : X) : A n x ≤ q x * B x := by
      by_cases hx : x ∈ spanningSets μ n
      · let v := min (B x ^ p) (n : ℝ≥0∞)
        have hAv : A n x = v := by simp [A, hx, v]
        have hqv : q x = v ^ (1 / p' : ℝ) := by simp [q, hx, v]
        rw [hAv, hqv]
        have hvle : v ≤ B x ^ p := min_le_left _ _
        have hvroot : v ^ (1 / p : ℝ) ≤ B x := by
          calc
            _ ≤ (B x ^ p) ^ (1 / p : ℝ) := ENNReal.rpow_le_rpow hvle hpInv.le
            _ = B x := by
              rw [← ENNReal.rpow_mul]
              rw [show p * (1 / p : ℝ) = 1 by field_simp [ne_of_gt hp0]]
              exact ENNReal.rpow_one _
        have hfactor : v ^ (1 / p : ℝ) * v ^ (1 / p' : ℝ) = v := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ hpInv.le hp'Inv.le, hrecip,
            ENNReal.rpow_one]
        calc
          v = v ^ (1 / p : ℝ) * v ^ (1 / p' : ℝ) := hfactor.symm
          _ = v ^ (1 / p' : ℝ) * v ^ (1 / p : ℝ) := mul_comm _ _
          _ ≤ v ^ (1 / p' : ℝ) * B x := mul_le_mul' le_rfl hvroot
      · simp [A, q, Set.indicator_of_notMem hx]
    have hLpair : L n ≤ D * (L n) ^ (1 / p' : ℝ) := by
      calc
        L n ≤ ∫⁻ x, q x * B x ∂μ := by
          dsimp [L]
          exact lintegral_mono hpoint
        _ ≤ D * (∫⁻ x, q x ^ p' ∂μ) ^ (1 / p' : ℝ) := hpair q hq
        _ = D * (L n) ^ (1 / p' : ℝ) := by
          congr 1
          congr 1
          apply lintegral_congr
          intro x
          rw [hqpow]
    by_cases hLzero : L n = 0
    · simp [hLzero]
    · let R : ℝ≥0∞ := (L n) ^ (1 / p' : ℝ)
      let S : ℝ≥0∞ := (L n) ^ (1 / p : ℝ)
      have hprod : R * S = L n := by
        calc
          R * S = (L n) ^ (1 / p' + 1 / p : ℝ) := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ hp'Inv.le hpInv.le]
          _ = L n := by
            rw [show 1 / p' + 1 / p = 1 by linarith [hrecip], ENNReal.rpow_one]
      have hRzero : R ≠ 0 := by
        dsimp [R]
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hLzero) (hLtop n)).ne'
      have hRtop : R ≠ ⊤ := by
        dsimp [R]
        exact ENNReal.rpow_ne_top_of_nonneg hp'Inv.le (hLtop n)
      have hSle : S ≤ D := by
        apply (ENNReal.mul_le_mul_iff_left hRzero hRtop).mp
        calc
          S * R = L n := by rw [mul_comm S R, hprod]
          _ ≤ D * R := by simpa [R] using hLpair
      have hpPow : S ^ p = L n := by
        dsimp [S]
        rw [← ENNReal.rpow_mul]
        rw [show (1 / p : ℝ) * p = 1 by field_simp [ne_of_gt hp0]]
        exact ENNReal.rpow_one _
      calc
        L n = S ^ p := hpPow.symm
        _ ≤ D ^ p := ENNReal.rpow_le_rpow hSle hp0.le
  have htotal : (∫⁻ x, B x ^ p ∂μ) ≤ D ^ p := by
    calc
      (∫⁻ x, B x ^ p ∂μ) = ⨆ n : ℕ, L n := by
        rw [← lintegral_iSup hAmeas hAmono]
        congr 1
        funext x
        exact (hAsup x).symm
      _ ≤ D ^ p := iSup_le hLbound
  calc
    (∫⁻ x, B x ^ p ∂μ) ^ (1 / p : ℝ) ≤ (D ^ p) ^ (1 / p : ℝ) :=
      ENNReal.rpow_le_rpow htotal hpInv.le
    _ = D := by
      rw [← ENNReal.rpow_mul]
      rw [show p * (1 / p : ℝ) = 1 by field_simp [ne_of_gt hp0]]
      exact ENNReal.rpow_one _

/-- Composition of weighted positive-kernel bounds. The middle exponential
weights cancel; SigmaFinite duality on the middle space turns the second
bilinear estimate into the `Lᵖ` norm needed by the first. -/
theorem WeightedFormBound.comp {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {μ : Measure X} {ν : Measure Y} {ρ : Measure Z}
    [SFinite μ] [SigmaFinite ν] [SFinite ρ]
    {wX : X → ℝ} {wY : Y → ℝ} {wZ : Z → ℝ} {p p' : ℝ}
    {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞} {c d : ℝ≥0∞}
    (hpq : p.HolderConjugate p') (hwYm : Measurable wY)
    (hKm : Measurable (Function.uncurry K)) (hLm : Measurable (Function.uncurry L))
    (hK : WeightedFormBound μ ν wX wY p p' K c)
    (hL : WeightedFormBound ν ρ (fun y => -wY y) wZ p p' L d) :
    WeightedFormBound μ ρ wX wZ p p' (spatialKernelComp ν K L) (c * d) := by
  intro f g hf hg
  let B : Y → ℝ≥0∞ := fun y => ∫⁻ z, L y z * f z ∂ρ
  let E : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (wY y))
  let Eneg : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-wY y))
  let Bw : Y → ℝ≥0∞ := fun y => B y * E y
  have hB : Measurable B := measurable_kernelAction ρ hLm hf
  have hE : Measurable E := by
    dsimp [E]
    exact (Real.continuous_exp.measurable.comp hwYm).ennreal_ofReal
  have hEneg : Measurable Eneg := by
    dsimp [Eneg]
    exact (Real.continuous_exp.measurable.comp hwYm.neg).ennreal_ofReal
  have hBw : Measurable Bw := by dsimp [Bw]; exact hB.mul hE
  let NF : ℝ≥0∞ :=
    (∫⁻ z, (f z * ENNReal.ofReal (Real.exp (wZ z))) ^ p ∂ρ) ^ (1 / p : ℝ)
  have hpair : ∀ q : Y → ℝ≥0∞, Measurable q →
      (∫⁻ y, q y * Bw y ∂ν) ≤ d * NF *
        (∫⁻ y, q y ^ p' ∂ν) ^ (1 / p' : ℝ) := by
    intro q hq
    let Q : Y → ℝ≥0∞ := fun y => q y * E y
    have hQ : Measurable Q := hq.mul hE
    have hcancel (y : Y) : E y * Eneg y = 1 := by
      dsimp [E, Eneg]
      rw [← ENNReal.ofReal_mul (Real.exp_pos (wY y)).le]
      rw [show Real.exp (wY y) * Real.exp (-wY y) = 1 by
        rw [← Real.exp_add]
        simp]
      exact ENNReal.ofReal_one
    have hQcancel (y : Y) : Q y * Eneg y = q y := by
      dsimp [Q]
      calc
        q y * E y * Eneg y = q y * (E y * Eneg y) := by ac_rfl
        _ = q y := by rw [hcancel, mul_one]
    have hh := hL f Q hf hQ
    calc
      (∫⁻ y, q y * Bw y ∂ν) = ∫⁻ y, Q y * B y ∂ν := by
        apply lintegral_congr
        intro y
        dsimp [Bw, Q]
        ac_rfl
      _ ≤ d * NF *
          (∫⁻ y, (Q y * Eneg y) ^ p' ∂ν) ^ (1 / p' : ℝ) := by
            simpa [WeightedFormBound, B, NF, Eneg] using hh
      _ = d * NF * (∫⁻ y, q y ^ p' ∂ν) ^ (1 / p' : ℝ) := by
            congr 1
            congr 1
            apply lintegral_congr
            intro y
            rw [hQcancel]
  have hBwroot := bilinear_lp_norm_le ν hpq hBw hpair
  have hKaction := hK B g hB hg
  let NG : ℝ≥0∞ :=
    (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p' : ℝ)
  calc
    (∫⁻ x, g x * (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) ∂μ) =
        ∫⁻ x, g x * (∫⁻ y, K x y * B y ∂ν) ∂μ := by
          apply lintegral_congr
          intro x
          rw [spatialKernelComp_action_eq ν ρ hKm hLm hf x]
    _ ≤ c * (∫⁻ y, Bw y ^ p ∂ν) ^ (1 / p : ℝ) * NG := by
          simpa [WeightedFormBound, Bw, E, NG] using hKaction
    _ ≤ c * (d * NF) * NG := by
          exact mul_le_mul' (mul_le_mul' le_rfl hBwroot) le_rfl
    _ = c * d * NF * NG := by ac_rfl

/-- Composition through a SigmaFinite unweighted `L²` middle space. -/
theorem WeightedFormBound.comp_two {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {μ : Measure X} {ν : Measure Y} {ρ : Measure Z}
    [SFinite μ] [SigmaFinite ν] [SFinite ρ]
    {wX : X → ℝ} {wZ : Z → ℝ} {p p' : ℝ} {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞}
    {c d : ℝ≥0∞} (hKm : Measurable (Function.uncurry K)) (hLm : Measurable (Function.uncurry L))
    (hK : WeightedFormBound μ ν wX (fun _ => 0) 2 p' K c)
    (hL : WeightedFormBound ν ρ (fun _ => 0) wZ p 2 L d) :
    WeightedFormBound μ ρ wX wZ p p' (spatialKernelComp ν K L) (c * d) := by
  intro f g hf hg
  let B : Y → ℝ≥0∞ := fun y => ∫⁻ z, L y z * f z ∂ρ
  have hB : Measurable B := by
    exact measurable_kernelAction ρ hLm hf
  let N : ℝ≥0∞ := (∫⁻ z, (f z * ENNReal.ofReal (Real.exp (wZ z))) ^ p ∂ρ) ^ (1 / p : ℝ)
  have hpair : ∀ q : Y → ℝ≥0∞, Measurable q →
      (∫⁻ y, q y * B y ∂ν) ≤ d * N * (∫⁻ y, q y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
    intro q hq
    have hh := hL f q hf hq
    simpa [WeightedFormBound, B, N, Real.exp_zero, ENNReal.ofReal_one] using hh
  have hBroot := bilinear_l2_norm_le ν hB hpair
  have haction := hK B g hB hg
  calc
    (∫⁻ x, g x * (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) ∂μ) =
        ∫⁻ x, g x * (∫⁻ y, K x y * B y ∂ν) ∂μ := by
          apply lintegral_congr
          intro x
          rw [spatialKernelComp_action_eq ν ρ hKm hLm hf x]
    _ ≤ c * (∫⁻ y, (B y * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') := haction
    _ ≤ c * (d * N) * (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') := by
          apply mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl
          simpa [Real.exp_zero, ENNReal.ofReal_one] using hBroot
    _ = c * d * N * (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') := by
          ac_rfl

end Critical2DKPZ.SHF.Tsai

end
