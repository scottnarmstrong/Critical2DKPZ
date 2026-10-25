/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
public import Critical2DKPZ.SHF.Tsai.DenseChainTensorLimits
public import Critical2DKPZ.SHF.Tsai.HeatMollifier
import Mathlib.Tactic

/-! # Three-block Gaussian chain convergence at arbitrary nonnegative times -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped Topology ENNReal

namespace Critical2DKPZ.NonGaussian

/-- The Gaussian-smoothed product of three consecutive SHF increments converges in probability
to the SHF pairing over the full interval, for every pair of L² endpoint tests. -/
theorem tendstoInMeasure_threeBlock_heat_chain_of (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hdense : DenseSHFAt ϑ P Z)
    {r s t u : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (f g : Plane → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    TendstoInMeasure P (fun n ω => ∫ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then Z r s ω else if k = 1 then Z s t ω else Z t u ω)
        (fun _ => heatMollifier n) 2) atTop
      (fun ω => ∫ p, f p.1 * g p.2 ∂Z r u ω) := by
  let a : ℕ → ℝ
    | 0 => r
    | 1 => s
    | 2 => t
    | n + 3 => u + n
  have ha : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    rcases n with _ | _ | _ | n
    · exact hrs
    · exact hst
    · simpa only [a, Nat.cast_zero, add_zero] using htu
    · dsimp only [a]
      norm_num
  have ha0 : a 0 = r := rfl
  have hnonneg : ∀ z ∈ Set.range a, 0 ≤ z := by
    rintro z ⟨n, rfl⟩
    exact hr.trans (ha0 ▸ ha.monotone (Nat.zero_le n))
  have hD := hdense (Set.range a) (Set.countable_range a) hnonneg
  have hlim := hD.tendstoInMeasure_chain_tensor P Z 2 a ha
    (fun k _ => Set.mem_range_self k) (fun _ => heatMollifier)
    (fun _ => isL2ApplicableMollifier_heatMollifier) f g hf hg
  simpa [chainProduct, a] using hlim

/-- The Gaussian-smoothed product of two consecutive SHF increments converges in probability
to the SHF pairing over the full interval, for every pair of L² endpoint tests. -/
theorem tendstoInMeasure_twoBlock_heat_chain_of (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hdense : DenseSHFAt ϑ P Z)
    {r s t : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t)
    (f g : Plane → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    TendstoInMeasure P (fun n ω => ∫ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then Z r s ω else Z s t ω)
        (fun _ => heatMollifier n) 1) atTop
      (fun ω => ∫ p, f p.1 * g p.2 ∂Z r t ω) := by
  let a : ℕ → ℝ
    | 0 => r
    | 1 => s
    | n + 2 => t + n
  have ha : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    rcases n with _ | _ | n
    · exact hrs
    · simpa only [a, Nat.cast_zero, add_zero] using hst
    · dsimp only [a]
      norm_num
  have ha0 : a 0 = r := rfl
  have hnonneg : ∀ z ∈ Set.range a, 0 ≤ z := by
    rintro z ⟨n, rfl⟩
    exact hr.trans (ha0 ▸ ha.monotone (Nat.zero_le n))
  have hD := hdense (Set.range a) (Set.countable_range a) hnonneg
  have hlim := hD.tendstoInMeasure_chain_tensor P Z 1 a ha
    (fun k _ => Set.mem_range_self k) (fun _ => heatMollifier)
    (fun _ => isL2ApplicableMollifier_heatMollifier) f g hf hg
  simpa [chainProduct, a] using hlim

end Critical2DKPZ.NonGaussian

end
