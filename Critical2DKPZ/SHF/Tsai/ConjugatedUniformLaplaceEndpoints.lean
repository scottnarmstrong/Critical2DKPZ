/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedUniformEndpointBounds
public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceEndpoint
import Mathlib.Tactic

/-! # Uniform conjugated Laplace endpoint estimates -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Both endpoint Laplace powers use one rate shift, uniformly over collision
labels. Their exponents add to one in every finite `Lᵖ` space. -/
theorem exists_uniform_conjugated_laplace_endpoints (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (α : CollisionPair n) (rate : ℝ), c < rate →
      WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
        (fun x => a * configurationOneNorm x) p (p / (p - 1))
        (laplaceTimeKernel rate (fun q : ℝ × FusedConfiguration α × Configuration n =>
          ENNReal.ofReal (incomingKernel α q.1 q.2.1 q.2.2)))
        (ENNReal.ofReal (c * Real.Gamma (1 - 1 / p) * (1 / (rate - c)) ^ (1 - 1 / p))) ∧
      WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
        (fun y => a * fusedOneNorm α y) p (p / (p - 1))
        (laplaceTimeKernel rate (fun q : ℝ × Configuration n × FusedConfiguration α =>
          ENNReal.ofReal (incomingKernel α q.1 q.2.2 q.2.1)))
        (ENNReal.ofReal (c * Real.Gamma (1 / p) * (1 / (rate - c)) ^ (1 / p))) := by
  obtain ⟨c, hc, hbound⟩ := exists_uniform_conjugated_endpoint_bounds n hp ha
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hinv : 1 / p < 1 := (div_lt_iff₀ hp0).mpr (by simpa only [one_mul] using hp)
  have hbIn : -1 < -1 / p := by simpa only [neg_div] using neg_lt_neg hinv
  have heOut : -(p - 1) / p + 1 = 1 / p := by field_simp; ring
  have hbOut : -1 < -(p - 1) / p := by
    have hpos : 0 < 1 / p := by positivity
    linarith only [heOut, hpos]
  refine ⟨c, hc, ?_⟩
  intro α rate hrate
  constructor
  · have h := WeightedFormBound.laplace_of_power_bound
      (K := fun q : ℝ × FusedConfiguration α × Configuration n =>
        ENNReal.ofReal (incomingKernel α q.1 q.2.1 q.2.2))
      (measurable_incomingKernel α).ennreal_ofReal (zero_le_one.trans hc) hbIn hrate
      (fun t ht => (hbound α t ht).1)
    simpa only [show -1 / p + 1 = 1 - 1 / p by ring] using h
  · have hKm : Measurable (fun q : ℝ × Configuration n × FusedConfiguration α =>
        ENNReal.ofReal (incomingKernel α q.1 q.2.2 q.2.1)) :=
      ((measurable_incomingKernel α).comp
        (measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst))).ennreal_ofReal
    have h := WeightedFormBound.laplace_of_power_bound hKm (zero_le_one.trans hc) hbOut hrate
      (fun t ht => (hbound α t ht).2)
    simpa only [heOut] using h

end Critical2DKPZ.SHF.Tsai

end
