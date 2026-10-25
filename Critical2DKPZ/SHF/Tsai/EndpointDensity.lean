/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.SHF.Tsai.SecondMomentApproximation

/-! # Extension of probabilistic endpoint tests from compact functions to `L²`

Uniform second-moment continuity in the spatial endpoint gives the two
approximation errors in the convergence-in-measure argument. Compact
continuous density then extends the tested convergence to every `L²` function.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- A uniformly second-moment continuous tested family converges on every `L²` endpoint
if it converges on the compact continuous endpoints. The moment bounds include integrability. -/
theorem tendstoInMeasure_of_compact_endpoint
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : (Plane → ℝ) → ℕ → Ω → ℝ) (G : (Plane → ℝ) → Ω → ℝ)
    (C C' : ℝ)
    (hF : ∀ (f h : Plane → ℝ), MemLp f 2 → MemLp h 2 → ∀ n,
      Integrable (fun ω => (F f n ω - F h n ω) ^ 2) P ∧
      (∫ ω, (F f n ω - F h n ω) ^ 2 ∂P) ≤ C * (eLpNorm (f - h) 2).toReal ^ 2)
    (hG : ∀ (f h : Plane → ℝ), MemLp f 2 → MemLp h 2 →
      Integrable (fun ω => (G f ω - G h ω) ^ 2) P ∧
      (∫ ω, (G f ω - G h ω) ^ 2 ∂P) ≤ C' * (eLpNorm (f - h) 2).toReal ^ 2)
    (hconv : ∀ h : C_c(Plane, ℝ), TendstoInMeasure P (F h) atTop (G h))
    (g : Plane → ℝ) (hg : MemLp g 2) :
    TendstoInMeasure P (F g) atTop (G g) := by
  obtain ⟨a, ha, hlim⟩ := exists_compactTest_tendsto_eLpNorm_sub g hg
  have hreal := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hlim
  simp only [Function.comp_def, ENNReal.toReal_zero] at hreal
  let A (i : ℕ) := C * (eLpNorm (g - (a i : Plane → ℝ)) 2).toReal ^ 2
  let B (i : ℕ) := C' * (eLpNorm (g - (a i : Plane → ℝ)) 2).toReal ^ 2
  have hA : Tendsto A atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using (hreal.pow 2).const_mul C
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using (hreal.pow 2).const_mul C'
  exact tendstoInMeasure_of_uniform_sq_approximation P (F g) (G g)
    (fun i => F (a i)) (fun i => G (a i)) (fun i => hconv (a i)) A B hA hB
    (fun i n => hF g (a i) hg (ha i) n) (fun i => hG g (a i) hg (ha i))

end Critical2DKPZ.SHF.Tsai

end
