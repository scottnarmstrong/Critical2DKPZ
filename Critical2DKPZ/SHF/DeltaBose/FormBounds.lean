/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic

/-! # Positive bilinear form bounds -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- A bound for the positive bilinear form of a kernel on `L²(μ) × L²(ν)`. -/
def FormBound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (K : X → Y → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  ∀ f : Y → ℝ≥0∞, ∀ g : X → ℝ≥0∞, Measurable f → Measurable g →
    (∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ) ≤
      c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
        (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)

/-- A pointwise smaller positive kernel inherits a bilinear form bound. -/
theorem FormBound.mono {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K K' : X → Y → ℝ≥0∞} {c c' : ℝ≥0∞}
    (h : FormBound μ ν K' c) (hK : ∀ x y, K x y ≤ K' x y) (hc : c ≤ c') :
    FormBound μ ν K c' := by
  intro f g hf hg
  have hAction (x : X) :
      (∫⁻ y, K x y * f y ∂ν) ≤ ∫⁻ y, K' x y * f y ∂ν := by
    apply lintegral_mono
    intro y
    exact mul_le_mul' (hK x y) le_rfl
  calc
    (∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ) ≤
        ∫⁻ x, g x * (∫⁻ y, K' x y * f y ∂ν) ∂μ := by
          apply lintegral_mono
          intro x
          exact mul_le_mul' le_rfl (hAction x)
    _ ≤ c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := h f g hf hg
    _ ≤ c' * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
          exact mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl

/-- Sums of measurable positive kernels inherit the sum of their bilinear
form bounds. Measurability is needed for additivity of the lower integrals. -/
theorem FormBound.add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {K L : X → Y → ℝ≥0∞} {c d : ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (h₁ : FormBound μ ν K c) (h₂ : FormBound μ ν L d) :
    FormBound μ ν (fun x y => K x y + L x y) (c + d) := by
  intro f g hf hg
  let A : X → ℝ≥0∞ := fun x => ∫⁻ y, K x y * f y ∂ν
  let B : X → ℝ≥0∞ := fun x => ∫⁻ y, L x y * f y ∂ν
  have hA : Measurable A := measurable_kernelAction ν hK hf
  have hB : Measurable B := measurable_kernelAction ν hL hf
  have hInner (x : X) :
      (∫⁻ y, (K x y + L x y) * f y ∂ν) = A x + B x := by
    have hp : Measurable (fun y : Y => (x, y)) := by fun_prop
    have hKx : Measurable (fun y : Y => K x y * f y) := (hK.comp hp).mul hf
    calc
      _ = ∫⁻ y, K x y * f y + L x y * f y ∂ν := by
        apply lintegral_congr
        intro y
        simp [add_mul]
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
      _ = _ := lintegral_add_left hterm _
  calc
    (∫⁻ x, g x * (∫⁻ y, (K x y + L x y) * f y ∂ν) ∂μ) =
        ∫⁻ x, g x * (A x + B x) ∂μ := by
          apply lintegral_congr
          intro x
          rw [hInner x]
    _ = (∫⁻ x, g x * A x ∂μ) + (∫⁻ x, g x * B x ∂μ) := hOuter
    _ ≤ c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) +
        d * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
            add_le_add (h₁ f g hf hg) (h₂ f g hf hg)
    _ = (c + d) * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
            rw [← add_mul]
            ring

/-- A countable sum of measurable positive kernels inherits the sum of their
bilinear form bounds. -/
theorem formBound_tsum {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable ι] {μ : Measure X} {ν : Measure Y} [SFinite ν]
    {K : ι → X → Y → ℝ≥0∞} {c : ι → ℝ≥0∞}
    (hK : ∀ i, Measurable (Function.uncurry (K i)))
    (h : ∀ i, FormBound μ ν (K i) (c i)) :
    FormBound μ ν (fun x y => ∑' i, K i x y) (∑' i, c i) := by
  intro f g hf hg
  let A : ι → X → ℝ≥0∞ := fun i x => ∫⁻ y, K i x y * f y ∂ν
  have hAmeas (i : ι) : Measurable (A i) := measurable_kernelAction ν (hK i) hf
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
        have hp : Measurable (fun y : Y => (x, y)) := by fun_prop
        exact (((hK i).comp hp).mul hf).aemeasurable
      _ = ∑' i, A i x := by rfl
  calc
    (∫⁻ x, g x * (∫⁻ y, (∑' i, K i x y) * f y ∂ν) ∂μ) =
        ∫⁻ x, ∑' i, g x * A i x ∂μ := by
          apply lintegral_congr
          intro x
          rw [hInner x, ← ENNReal.tsum_mul_left]
    _ = ∑' i, ∫⁻ x, g x * A i x ∂μ := by
          apply lintegral_tsum
          intro i
          exact (hg.mul (hAmeas i)).aemeasurable
    _ ≤ ∑' i, c i * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
          apply ENNReal.tsum_le_tsum
          intro i
          exact h i f g hf hg
    _ = (∑' i, c i) * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]


private theorem ennreal_half_rpow_mul_self (x : ℝ≥0∞) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
    (by norm_num) (by norm_num)]
  norm_num

private theorem iSup_min_nat_sq (x : ℝ≥0∞) :
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

private theorem formBound_sq_le_on_finite_trunc {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] {K : X → Y → ℝ≥0∞} {c : ℝ≥0∞}
    (hform : FormBound μ ν K c) {f : Y → ℝ≥0∞} (hf : Measurable f)
    (hH : Measurable (fun x => ∫⁻ y, K x y * f y ∂ν))
    (s : Set X) (hs : MeasurableSet s) (hsμ : μ s < ⊤) (k : ℕ) :
    (∫⁻ x, (s.indicator (fun x => min (∫⁻ y, K x y * f y ∂ν)
      (k : ℝ≥0∞)) x) ^ 2 ∂μ) ≤ c ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
  let H : X → ℝ≥0∞ := fun x => ∫⁻ y, K x y * f y ∂ν
  let g : X → ℝ≥0∞ := s.indicator (fun x => min (H x) (k : ℝ≥0∞))
  have hg : Measurable g := by
    dsimp [g]
    exact (hH.min measurable_const).indicator hs
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
      · have hm : min (H x) (k : ℝ≥0∞) ≤ (k : ℝ≥0∞) := min_le_right _ _
        simpa [g, b, hx] using
          pow_le_pow_left₀ (by positivity) hm (2 : ℕ)
      · simp [g, b, Set.indicator_of_notMem hx]
    calc
      _ ≤ ∫⁻ x, b x ∂μ := lintegral_mono hpoint
      _ = (k : ℝ≥0∞) ^ 2 * μ s := by
        rw [lintegral_indicator hs, setLIntegral_const]
  have hLbound : L ≤ (k : ℝ≥0∞) ^ 2 * μ s := hL_eq.trans_le hLboundNat
  have hLtop : L ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)) (ne_of_lt hsμ))
    exact hLbound
  have hLower : L ≤ ∫⁻ x, g x * H x ∂μ := by
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ s
    · simp only [ENNReal.rpow_two, g, Set.indicator_of_mem hx]
      simpa [pow_two] using mul_le_mul' (le_refl (min (H x) (k : ℝ≥0∞)))
        (min_le_left _ _)
    · simp [g, Set.indicator_of_notMem hx]
  have hBilinear := hform f g hf hg
  have hEstimate : L ≤ c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
      L ^ (1 / 2 : ℝ) := by
    exact hLower.trans (by simpa [L, H] using hBilinear)
  by_cases hLzero : L = 0
  · calc
      (∫⁻ x, g x ^ 2 ∂μ) = L := hL_eq.symm
      _ = 0 := hLzero
      _ ≤ c ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := bot_le
  · let R : ℝ≥0∞ := L ^ (1 / 2 : ℝ)
    have hRsq : R * R = L := ennreal_half_rpow_mul_self L
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
    have hRoot : R ≤ c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
      apply (ENNReal.mul_le_mul_iff_left hRzero hRtop).mp
      calc
        R * R = L := hRsq
        _ ≤ c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) * R := by
          simpa [R] using hEstimate
    have hSquared := mul_le_mul hRoot hRoot (by positivity) (by positivity)
    calc
      (∫⁻ x, g x ^ 2 ∂μ) = L := hL_eq.symm
      _ = R * R := hRsq.symm
      _ ≤ (c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) ^ 2 := by
        simpa only [pow_two] using hSquared
      _ = c ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
        calc
          _ = c ^ 2 *
              ((∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
                (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) := by
                  simp only [pow_two]
                  ac_rfl
          _ = _ := by rw [ennreal_half_rpow_mul_self]

/-- A positive bilinear form bound implies the squared `L²` action bound
when both measures are sigma-finite. The sigma-finite assumptions ensure that
bounded truncations on finite-measure spanning sets detect the full integral. -/
theorem formBound_iff_l2_sq_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SigmaFinite μ] [SigmaFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K)) (c : ℝ≥0∞) :
    FormBound μ ν K c ↔ ∀ f : Y → ℝ≥0∞, Measurable f →
      (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ) ≤
        c ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
  constructor
  · intro hform f hf
    have hH : Measurable (fun x => ∫⁻ y, K x y * f y ∂ν) :=
      measurable_kernelAction ν hK hf
    let q : ℕ → X → ℝ≥0∞ := fun n x =>
      ((spanningSets μ n).indicator (fun x => min (∫⁻ y, K x y * f y ∂ν)
        (n : ℝ≥0∞)) x) ^ 2
    have hqmeas (n : ℕ) : Measurable (q n) := by
      dsimp [q]
      exact ((hH.min measurable_const).indicator (measurableSet_spanningSets μ n)).pow_const _
    have hqmono : Monotone q := by
      intro n m hnm x
      dsimp [q]
      by_cases hx : x ∈ spanningSets μ n
      · have hxm : x ∈ spanningSets μ m :=
          (monotone_spanningSets μ hnm) hx
        simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxm]
        exact pow_le_pow_left₀ (by positivity)
          (min_le_min_left _ (by exact_mod_cast hnm)) _
      · simp [Set.indicator_of_notMem hx]
    have hqsup (x : X) : (⨆ n, q n x) =
        (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) := by
      let Hx := ∫⁻ y, K x y * f y ∂ν
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
            Hx ^ 2 = ⨆ k : ℕ, min Hx (k : ℝ≥0∞) ^ 2 :=
              (iSup_min_nat_sq Hx).symm
            _ ≤ ⨆ n : ℕ, q n x := by
              apply iSup_le
              intro k
              let n := max N k
              have hNn : N ≤ n := le_max_left _ _
              have hkn : k ≤ n := le_max_right _ _
              have hxn : x ∈ spanningSets μ n :=
                (monotone_spanningSets μ hNn) hN
              have hcut : (k : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hkn
              apply le_iSup_of_le n
              dsimp [q]
              rw [Set.indicator_of_mem hxn]
              exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hcut) _
      simpa only [ENNReal.rpow_two, pow_two] using hsupNat
    calc
      _ = ∫⁻ x, (⨆ n, q n x) ∂μ := by
        congr 1
        funext x
        exact (hqsup x).symm
      _ = ⨆ n, ∫⁻ x, q n x ∂μ := lintegral_iSup hqmeas hqmono
      _ ≤ c ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
        apply iSup_le
        intro n
        exact formBound_sq_le_on_finite_trunc μ ν hform hf hH (spanningSets μ n)
          (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n) n
  · intro h f g hf hg
    have hsq : ∀ {f : Y → ℝ≥0∞}, Measurable f →
        (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ) ≤
          c ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
      intro f hf
      exact h f hf
    simpa [mul_comm] using kernelAction_bilinear_l2_sq_le μ ν hK hsq hf hg

/-- Composition multiplies positive bilinear form bounds. The intermediate
and input measures are sigma-finite so the second bound controls the full
`L²` norm of its kernel action. -/
theorem FormBound.comp {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SigmaFinite ν] [SigmaFinite ρ]
    {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞} {c d : ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (h₁ : FormBound μ ν K c) (h₂ : FormBound ν ρ L d) :
    FormBound μ ρ (spatialKernelComp ν K L) (c * d) := by
  intro f g hf hg
  let B : Y → ℝ≥0∞ := fun y => ∫⁻ z, L y z * f z ∂ρ
  have hB : Measurable B := measurable_kernelAction ρ hL hf
  have hLsq := (formBound_iff_l2_sq_le ν ρ hL d).mp h₂
  have hBroot :
      (∫⁻ y, B y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ≤
        d * (∫⁻ z, f z ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ) := by
    calc
      (∫⁻ y, B y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ≤
          (d ^ 2 * ∫⁻ z, f z ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ) :=
            ENNReal.monotone_rpow_of_nonneg (by norm_num) (hLsq f hf)
      _ = d * (∫⁻ z, f z ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            rw [← ENNReal.rpow_natCast_mul]
            norm_num
  calc
    (∫⁻ x, g x * (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) ∂μ) =
        ∫⁻ x, g x * (∫⁻ y, K x y * B y ∂ν) ∂μ := by
          apply lintegral_congr
          intro x
          rw [spatialKernelComp_action_eq ν ρ hK hL hf x]
    _ ≤ c * (∫⁻ y, B y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := h₁ B g hB hg
    _ ≤ c * (d * (∫⁻ z, f z ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ)) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
            exact mul_le_mul' (mul_le_mul' le_rfl hBroot) le_rfl
    _ = c * d * (∫⁻ z, f z ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by ring



end Critical2DKPZ.DeltaBose
