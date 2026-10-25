/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainLpFour

/-! # Transitivity of convergence in fourth moment

The `L⁴` triangle inequality transfers an identified approximation limit to
any family whose fourth-moment difference from that approximation vanishes.
Every fourth power is proved integrable before its expectation is used.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Fourth-moment comparison and an identified fourth-moment limit give the same limit. -/
theorem tendsto_integral_sub_pow_four_trans {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : ℕ → Ω → ℝ) (h : Ω → ℝ)
    (hf : ∀ j, MemLp (f j) 4 P) (hg : ∀ j, MemLp (g j) 4 P) (hh : MemLp h 4 P)
    (hfg : Tendsto (fun j => ∫ ω, (f j ω - g j ω) ^ 4 ∂P) atTop (𝓝 0))
    (hgh : Tendsto (fun j => ∫ ω, (g j ω - h ω) ^ 4 ∂P) atTop (𝓝 0)) :
    (∀ j, Integrable (fun ω => (f j ω - h ω) ^ 4) P) ∧
    Tendsto (fun j => ∫ ω, (f j ω - h ω) ^ 4 ∂P) atTop (𝓝 0) := by
  have hI {a b : Ω → ℝ} (ha : MemLp a 4 P) (hb : MemLp b 4 P) :
      Integrable (fun ω => (a ω - b ω) ^ 4) P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Even.pow_abs (show Even 4 from ⟨2, rfl⟩)] using
      (ha.sub hb).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hfgNorm := tendsto_eLpNorm_four_of_integral_pow_four P (fun j ω => f j ω - g j ω)
    (fun j => ((hf j).sub (hg j)).aestronglyMeasurable) (fun j => hI (hf j) (hg j)) hfg
  have hghNorm := tendsto_eLpNorm_four_of_integral_pow_four P (fun j ω => g j ω - h ω)
    (fun j => ((hg j).sub hh).aestronglyMeasurable) (fun j => hI (hg j) hh) hgh
  have hbound (j) : eLpNorm (fun ω => f j ω - h ω) 4 P ≤
      eLpNorm (fun ω => f j ω - g j ω) 4 P + eLpNorm (fun ω => g j ω - h ω) 4 P := by
    have heq : (fun ω => f j ω - h ω) =
        (fun ω => f j ω - g j ω) + (fun ω => g j ω - h ω) := by
      funext ω
      exact (sub_add_sub_cancel _ _ _).symm
    rw [heq]
    exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hnorm : Tendsto (fun j => eLpNorm (fun ω => f j ω - h ω) 4 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hfgNorm.add hghNorm) (fun _ => zero_le) hbound
  exact ⟨fun j => hI (hf j) hh, tendsto_integral_pow_four_of_eLpNorm P
    (fun j ω => f j ω - h ω) (fun j => ((hf j).sub hh).aestronglyMeasurable)
    (fun j => hI (hf j) hh) hnorm⟩

end Critical2DKPZ.SHF.Tsai

end
