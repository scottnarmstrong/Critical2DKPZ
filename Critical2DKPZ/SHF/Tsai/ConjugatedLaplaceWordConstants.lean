/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedUniformLaplaceEndpoints
public import Critical2DKPZ.SHF.Tsai.ConjugatedUniformSwapping
public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceCollision
import Mathlib.Tactic

/-! # Uniform scalar constants for conjugated Laplace word bounds -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- One endpoint rate shift, chosen uniformly over all collision labels. -/
def conjugatedEndpointShift (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) : ℝ :=
  Classical.choose (exists_uniform_conjugated_laplace_endpoints n hp ha)

/-- The scalar endpoint Laplace factor, with its precise inverse-rate power. -/
def conjugatedEndpointLaplaceFactor (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a)
    (rate b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (conjugatedEndpointShift n hp ha * Real.Gamma b *
    (1 / (rate - conjugatedEndpointShift n hp ha)) ^ b)

/-- The chosen common endpoint shift is at least one. -/
theorem conjugatedEndpointShift_ge_one (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    1 ≤ conjugatedEndpointShift n hp ha :=
  (Classical.choose_spec (exists_uniform_conjugated_laplace_endpoints n hp ha)).1

/-- The terminal free strand has the precise incoming Laplace endpoint
power, with the common shift and its canonical kernel orientation. -/
theorem weightedFormBound_laplace_free_incoming_conj_uniform {n : ℕ} {p a rate : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) (α : CollisionPair n)
    (hrate : conjugatedEndpointShift n hp ha < rate) :
    WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
      (fun x => a * configurationOneNorm x) p (p / (p - 1))
      (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id))
      (conjugatedEndpointLaplaceFactor n hp ha rate (1 - 1 / p)) := by
  have h := (Classical.choose_spec (exists_uniform_conjugated_laplace_endpoints n hp ha)).2 α rate hrate
  have hKernel : freeTimeKernel (collisionEmbedding α) id =
      (fun q : ℝ × FusedConfiguration α × Configuration n =>
        ENNReal.ofReal (incomingKernel α q.1 q.2.1 q.2.2)) := by
    funext q
    exact congrArg ENNReal.ofReal (freeKernel_symm n q.1 (collisionEmbedding α q.2.1) q.2.2)
  rw [hKernel]
  exact h.1

/-- The initial free strand has the complementary outgoing Laplace endpoint
power, with the same rate shift as the terminal strand. -/
theorem weightedFormBound_laplace_free_outgoing_conj_uniform {n : ℕ} {p a rate : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) (α : CollisionPair n)
    (hrate : conjugatedEndpointShift n hp ha < rate) :
    WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
      (fun y => a * fusedOneNorm α y) p (p / (p - 1))
      (laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)))
      (conjugatedEndpointLaplaceFactor n hp ha rate (1 / p)) :=
  ((Classical.choose_spec (exists_uniform_conjugated_laplace_endpoints n hp ha)).2 α rate hrate).2

/-- The scalar collision resolvent factor after Gaussian conjugation. -/
def conjugatedCollisionLaplaceFactor (n : ℕ) (θ a rate : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ n * (4 * Real.pi *
    (Real.log (rate - 2 * n * a ^ 2) - θ)⁻¹))

end Critical2DKPZ.SHF.Tsai

end
