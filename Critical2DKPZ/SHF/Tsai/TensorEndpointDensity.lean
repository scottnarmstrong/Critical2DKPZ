/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.EndpointDensity

/-! # Extension in both spatial tensor endpoints

Apply compact continuous density first in the initial endpoint, keeping a
compact terminal endpoint fixed, and then in the terminal endpoint. Uniform
second-moment estimates justify both extensions.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Convergence on compact tensors extends to all `L²` endpoints under uniform
second-moment continuity in each endpoint. Every moment estimate includes integrability. -/
theorem tendstoInMeasure_of_compact_tensor_endpoints
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : (Plane → ℝ) → (Plane → ℝ) → ℕ → Ω → ℝ)
    (G : (Plane → ℝ) → (Plane → ℝ) → Ω → ℝ) (CL CR DL DR : ℝ)
    (hFL : ∀ (f h g' : Plane → ℝ), MemLp f 2 → MemLp h 2 → MemLp g' 2 → ∀ n,
      Integrable (fun ω => (F f g' n ω - F h g' n ω) ^ 2) P ∧
      (∫ ω, (F f g' n ω - F h g' n ω) ^ 2 ∂P) ≤
        CL * (eLpNorm (f - h) 2).toReal ^ 2 * (eLpNorm g' 2).toReal ^ 2)
    (hFR : ∀ (g f h : Plane → ℝ), MemLp g 2 → MemLp f 2 → MemLp h 2 → ∀ n,
      Integrable (fun ω => (F g f n ω - F g h n ω) ^ 2) P ∧
      (∫ ω, (F g f n ω - F g h n ω) ^ 2 ∂P) ≤
        CR * (eLpNorm g 2).toReal ^ 2 * (eLpNorm (f - h) 2).toReal ^ 2)
    (hGL : ∀ (f h g' : Plane → ℝ), MemLp f 2 → MemLp h 2 → MemLp g' 2 →
      Integrable (fun ω => (G f g' ω - G h g' ω) ^ 2) P ∧
      (∫ ω, (G f g' ω - G h g' ω) ^ 2 ∂P) ≤
        DL * (eLpNorm (f - h) 2).toReal ^ 2 * (eLpNorm g' 2).toReal ^ 2)
    (hGR : ∀ (g f h : Plane → ℝ), MemLp g 2 → MemLp f 2 → MemLp h 2 →
      Integrable (fun ω => (G g f ω - G g h ω) ^ 2) P ∧
      (∫ ω, (G g f ω - G g h ω) ^ 2 ∂P) ≤
        DR * (eLpNorm g 2).toReal ^ 2 * (eLpNorm (f - h) 2).toReal ^ 2)
    (hconv : ∀ f h : C_c(Plane, ℝ), TendstoInMeasure P (F f h) atTop (G f h))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    TendstoInMeasure P (F g g') atTop (G g g') := by
  have hleft (h : C_c(Plane, ℝ)) (f : Plane → ℝ) (hf : MemLp f 2) :
      TendstoInMeasure P (F f h) atTop (G f h) := by
    have hh : MemLp h 2 := h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport
    apply tendstoInMeasure_of_compact_endpoint P (fun v => F v h) (fun v => G v h)
      (CL * (eLpNorm h 2).toReal ^ 2) (DL * (eLpNorm h 2).toReal ^ 2) _ _
      (fun a => hconv a h) f hf
    · intro a b ha hb n
      have hbound := hFL a b h ha hb hh n
      refine ⟨hbound.1, hbound.2.trans_eq ?_⟩
      ring
    · intro a b ha hb
      have hbound := hGL a b h ha hb hh
      refine ⟨hbound.1, hbound.2.trans_eq ?_⟩
      ring
  refine tendstoInMeasure_of_compact_endpoint P
    (fun b n ω => F g b n ω) (fun b ω => G g b ω)
    (CR * (eLpNorm g 2).toReal ^ 2) (DR * (eLpNorm g 2).toReal ^ 2)
    ?_ ?_ ?_ g' hg'
  · intro f h hf hh n
    exact hFR g f h hg hf hh n
  · intro f h hf hh
    exact hGR g f h hg hf hh
  · intro h
    exact hleft h g hg

end Critical2DKPZ.SHF.Tsai

end
