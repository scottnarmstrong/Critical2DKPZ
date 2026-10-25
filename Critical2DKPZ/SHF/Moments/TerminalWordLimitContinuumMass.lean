/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTimeAction
public import Critical2DKPZ.SHF.DeltaBose.PathKernel
public import Critical2DKPZ.SHF.DeltaBose.PathDominating
public import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
public import Critical2DKPZ.SHF.DeltaBose.PotentialIntegratedSchur
public import Critical2DKPZ.SHF.DeltaBose.ScalarEnvelope
public import Critical2DKPZ.SHF.DeltaBose.IncomingMass
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Continuum row bounds for the first letter of a collision path -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

private theorem heatKernel_center_product {t : ℝ} (ht : 0 < t)
    (a b z : Plane) :
    heatKernel t (z - a) * heatKernel t (z - b) =
      heatKernel (2 * t) (b - a) * heatKernel (t / 2) (z - (1 / 2 : ℝ) • (a + b)) := by
  have h := Critical2DKPZ.heatKernel_mul_sub ht ht (b - a) (z - a)
  rw [show (b - a) - (z - a) = -(z - b) by abel, heatKernel_neg] at h
  have ht1 : t + t = 2 * t := by ring
  have ht2 : t * t / (2 * t) = t / 2 := by field_simp
  have ht3 : t / (2 * t) = (1 / 2 : ℝ) := by field_simp
  have hv : z - a - (t / (2 * t)) • (b - a) =
      z - (1 / 2 : ℝ) • (a + b) := by rw [ht3]; module
  rw [ht1, ht2, hv] at h
  exact h


private theorem integral_heatKernel_shifted_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (a b : Plane) :
    (∫ z : Plane, heatKernel s (z - a) * heatKernel t (b - z)) =
      heatKernel (s + t) (b - a) := by
  let F : Plane → ℝ := fun u => heatKernel s u * heatKernel t ((b - a) - u)
  have hfun : (fun z : Plane => heatKernel s (z - a) * heatKernel t (b - z)) =
      fun z => F (z - a) := by
    funext z
    dsimp [F]
    congr 2
    abel
  rw [hfun, integral_sub_right_eq_self]
  exact Critical2DKPZ.integral_heatKernel_mul_sub hs ht (b - a)

private theorem integral_heatKernel_center_composition {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) (a b z' : Plane) :
    (∫ z : Plane,
      (heatKernel r (z - a) * heatKernel r (z - b)) *
        heatKernel (q / 2) (z' - z)) =
      heatKernel (2 * r) (b - a) *
        heatKernel ((r + q) / 2) (z' - (1 / 2 : ℝ) • (a + b)) := by
  have hpoint (z : Plane) := heatKernel_center_product hr a b z
  calc
    (∫ z : Plane,
      (heatKernel r (z - a) * heatKernel r (z - b)) *
        heatKernel (q / 2) (z' - z))
        = ∫ z : Plane,
          (heatKernel (2 * r) (b - a) *
            heatKernel (r / 2) (z - (1 / 2 : ℝ) • (a + b))) *
            heatKernel (q / 2) (z' - z) := by
              apply integral_congr_ae
              filter_upwards [] with z
              rw [hpoint z]
    _ = ∫ z : Plane, heatKernel (2 * r) (b - a) *
          (heatKernel (r / 2) (z - (1 / 2 : ℝ) • (a + b)) *
            heatKernel (q / 2) (z' - z)) := by
              apply integral_congr_ae
              filter_upwards [] with z
              ring
    _ = heatKernel (2 * r) (b - a) *
          ∫ z : Plane, heatKernel (r / 2) (z - (1 / 2 : ℝ) • (a + b)) *
            heatKernel (q / 2) (z' - z) :=
              integral_const_mul (heatKernel (2 * r) (b - a)) _
    _ = heatKernel (2 * r) (b - a) *
          heatKernel (r / 2 + q / 2) (z' - (1 / 2 : ℝ) • (a + b)) := by
            rw [integral_heatKernel_shifted_sub (by positivity) (by positivity)]
    _ = _ := by rw [show r / 2 + q / 2 = (r + q) / 2 by ring]


private theorem integral_incoming_mul_collisionKernel {n : ℕ}
    (α : CollisionPair n) {r q θ : ℝ} (hr : 0 < r) (hq : 0 < q)
    (x : Configuration n) (z' : FusedConfiguration α) :
    (∫ z : FusedConfiguration α,
      incomingKernel α r z x * collisionKernel α θ q z z') =
      (4 * Real.pi * scalarDensity θ q) *
        (heatKernel (2 * r) (x α.1.2 - x α.1.1) *
          (heatKernel ((r + q) / 2)
            (z'.1 - (1 / 2 : ℝ) • (x α.1.1 + x α.1.2)) *
            ∏ i : Spectator α, heatKernel (r + q) (z'.2 i - x i.1))) := by
  classical
  let A : Plane → ℝ := fun c =>
    heatKernel r (c - x α.1.1) * heatKernel r (c - x α.1.2) *
      heatKernel (q / 2) (z'.1 - c)
  let B : (Spectator α → Plane) → ℝ := fun v =>
    ∏ i : Spectator α, heatKernel r (v i - x i.1) *
      heatKernel q (z'.2 i - v i)
  have hpoint (z : FusedConfiguration α) :
      incomingKernel α r z x * collisionKernel α θ q z z' =
        (4 * Real.pi * scalarDensity θ q) * (A z.1 * B z.2) := by
    rw [incomingKernel_eq_prod]
    unfold A B collisionKernel
    calc
      _ = (4 * Real.pi * scalarDensity θ q) *
          ((heatKernel r (z.1 - x α.1.1) * heatKernel r (z.1 - x α.1.2) *
            heatKernel (q / 2) (z'.1 - z.1)) *
            ((∏ i : Spectator α, heatKernel r (z.2 i - x i.1)) *
              ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i))) := by ring
      _ = (4 * Real.pi * scalarDensity θ q) *
          ((heatKernel r (z.1 - x α.1.1) * heatKernel r (z.1 - x α.1.2) *
            heatKernel (q / 2) (z'.1 - z.1)) *
            ∏ i : Spectator α,
              (heatKernel r (z.2 i - x i.1) * heatKernel q (z'.2 i - z.2 i))) := by
                rw [← Finset.prod_mul_distrib]
  calc
    _ = ∫ z : FusedConfiguration α,
          (4 * Real.pi * scalarDensity θ q) * (A z.1 * B z.2) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = (4 * Real.pi * scalarDensity θ q) *
          ∫ z : FusedConfiguration α, A z.1 * B z.2 := by
            rw [integral_const_mul]
    _ = (4 * Real.pi * scalarDensity θ q) *
          ((∫ c : Plane, A c) * ∫ v : Spectator α → Plane, B v) := by
            rw [Measure.volume_eq_prod, integral_prod_mul]
    _ = (4 * Real.pi * scalarDensity θ q) *
          (heatKernel (2 * r) (x α.1.2 - x α.1.1) *
            (heatKernel ((r + q) / 2)
              (z'.1 - (1 / 2 : ℝ) • (x α.1.1 + x α.1.2)) *
              ∏ i : Spectator α, heatKernel (r + q) (z'.2 i - x i.1))) := by
            rw [show (∫ c : Plane, A c) =
              heatKernel (2 * r) (x α.1.2 - x α.1.1) *
                heatKernel ((r + q) / 2)
                  (z'.1 - (1 / 2 : ℝ) • (x α.1.1 + x α.1.2)) by
                    dsimp [A]
                    exact integral_heatKernel_center_composition hr hq
                      (x α.1.1) (x α.1.2) z'.1]
            rw [show (∫ v : Spectator α → Plane, B v) =
              ∏ i : Spectator α, heatKernel (r + q) (z'.2 i - x i.1) by
                  dsimp [B]
                  rw [integral_fintype_prod_volume_eq_prod
                    (fun i : Spectator α => fun v : Plane =>
                      heatKernel r (v - x i.1) * heatKernel q (z'.2 i - v))]
                  apply Finset.prod_congr rfl
                  intro i hi
                  exact integral_heatKernel_shifted_sub hr hq (x i.1) (z'.2 i)]
            ring

private theorem lintegral_fusedTensor_weight_le {n : ℕ} (α : CollisionPair n)
    {a b : ℝ} (ha : 0 < a) (c₀ : Plane)
    (x : Spectator α → Plane) (W : Plane → (Spectator α → Plane) → ℝ≥0∞)
    (hW : Measurable (Function.uncurry W))
    (R : ℝ≥0∞)
    (hrow : ∀ c : Plane, (∫⁻ v : Spectator α → Plane,
      (∏ i : Spectator α, ENNReal.ofReal (heatKernel b (v i - x i))) * W c v) ≤ R) :
    (∫⁻ z : FusedConfiguration α,
      (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
        ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i - x i))) *
        W z.1 z.2) ≤ R := by
  classical
  let C : Plane → ℝ≥0∞ := fun c => ENNReal.ofReal (heatKernel a (c - c₀))
  let S : (Spectator α → Plane) → ℝ≥0∞ := fun v =>
    ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (v i - x i))
  have hC : Measurable C := by
    dsimp [C]
    unfold heatKernel
    fun_prop
  have hS : Measurable S := by
    dsimp [S]
    apply Finset.measurable_fun_prod
    intro i hi
    unfold heatKernel
    fun_prop
  have hF : Measurable (fun z : FusedConfiguration α =>
      (C z.1 * S z.2) * W z.1 z.2) :=
    ((hC.comp measurable_fst).mul (hS.comp measurable_snd)).mul
      (hW.comp measurable_id)
  calc
    _ = ∫⁻ c : Plane, ∫⁻ v : Spectator α → Plane,
          (C c * S v) * W c v := by
            rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
    _ ≤ ∫⁻ c : Plane, C c * R := by
          apply lintegral_mono
          intro c
          have hSv : Measurable (fun v : Spectator α → Plane => S v * W c v) :=
            hS.mul (hW.comp (measurable_const.prodMk measurable_id))
          calc (∫⁻ v : Spectator α → Plane, (C c * S v) * W c v)
              = C c * (∫⁻ v : Spectator α → Plane, S v * W c v) := by
                  calc
                    _ = ∫⁻ v : Spectator α → Plane, C c * (S v * W c v) := by
                          apply lintegral_congr
                          intro v
                          ac_rfl
                    _ = _ := lintegral_const_mul (C c) hSv
            _ ≤ C c * R := mul_le_mul_right (hrow c) (C c)
    _ = R := by
          rw [lintegral_mul_const _ hC, lintegral_heatKernel_sub ha c₀, one_mul]

private theorem pair_eq_of_endpoint_mem {n : ℕ} {α β : CollisionPair n}
    (h₁ : β.1.1 = α.1.1 ∨ β.1.1 = α.1.2)
    (h₂ : β.1.2 = α.1.1 ∨ β.1.2 = α.1.2) : β = α := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · have hβ := β.2
    have hα := α.2
    exfalso
    omega
  · apply Subtype.ext
    exact Prod.ext h₁ h₂
  · have hβ := β.2
    have hα := α.2
    exfalso
    omega
  · have hβ := β.2
    have hα := α.2
    exfalso
    omega

private theorem lintegral_fusedPairPotential_separated_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c₀ : Plane) (x : Spectator α → Plane) :
    (∫⁻ z : FusedConfiguration α,
      (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
        ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i - x i))) *
        heatPotential ((collisionEmbedding α z) β.1.1 -
          (collisionEmbedding α z) β.1.2)) ≤ heatPotentialRowBound b := by
  classical
  by_cases h₁ : β.1.1 = α.1.1 ∨ β.1.1 = α.1.2
  · by_cases h₂ : β.1.2 = α.1.1 ∨ β.1.2 = α.1.2
    · exact False.elim (hne.symm (pair_eq_of_endpoint_mem (α := α) (β := β) h₁ h₂))
    · have hout : β.1.2 ≠ α.1.1 ∧ β.1.2 ≠ α.1.2 := by
        simpa only [not_or] using h₂
      let j : Spectator α := ⟨β.1.2, hout⟩
      let W : Plane → (Spectator α → Plane) → ℝ≥0∞ := fun c v =>
        heatPotential (c - v j)
      have hW : Measurable (Function.uncurry W) := by
        dsimp [W]
        exact measurable_heatPotential.comp
          (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))
      have hweight : ∀ c : Plane, ∀ v : Spectator α → Plane,
          heatPotential ((collisionEmbedding α (c, v)) β.1.1 -
            (collisionEmbedding α (c, v)) β.1.2) = W c v := by
        intro c v
        rcases h₁ with hleft | hright
        · simp [W, collisionEmbedding, hleft, hout, j]
        · simp [W, collisionEmbedding, hright, hout, j]
      calc
        _ = ∫⁻ z : FusedConfiguration α,
            (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
              ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i - x i))) *
              W z.1 z.2 := by
                apply lintegral_congr
                intro z
                rw [hweight z.1 z.2]
        _ ≤ heatPotentialRowBound b := by
              apply lintegral_fusedTensor_weight_le α ha c₀ x W hW
              intro c
              simpa [W, heatPotential_sub_swap] using
                (lintegral_tensorHeatKernel_mul_shiftedPotential_le hb j x c)
  · by_cases h₂ : β.1.2 = α.1.1 ∨ β.1.2 = α.1.2
    · have hout : β.1.1 ≠ α.1.1 ∧ β.1.1 ≠ α.1.2 := by
        simpa only [not_or] using h₁
      let i : Spectator α := ⟨β.1.1, hout⟩
      let W : Plane → (Spectator α → Plane) → ℝ≥0∞ := fun c v =>
        heatPotential (v i - c)
      have hW : Measurable (Function.uncurry W) := by
        dsimp [W]
        exact measurable_heatPotential.comp
          (((measurable_pi_apply i).comp measurable_snd).sub measurable_fst)
      have hweight : ∀ c : Plane, ∀ v : Spectator α → Plane,
          heatPotential ((collisionEmbedding α (c, v)) β.1.1 -
            (collisionEmbedding α (c, v)) β.1.2) = W c v := by
        intro c v
        rcases h₂ with hleft | hright
        · simp [W, collisionEmbedding, hleft, hout, i]
        · simp [W, collisionEmbedding, hright, hout, i]
      calc
        _ = ∫⁻ z : FusedConfiguration α,
            (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
              ∏ i' : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i' - x i'))) *
              W z.1 z.2 := by
                apply lintegral_congr
                intro z
                rw [hweight z.1 z.2]
        _ ≤ heatPotentialRowBound b := by
              apply lintegral_fusedTensor_weight_le α ha c₀ x W hW
              intro c
              exact lintegral_tensorHeatKernel_mul_shiftedPotential_le hb i x c
    · have hout₁ : β.1.1 ≠ α.1.1 ∧ β.1.1 ≠ α.1.2 := by
        simpa only [not_or] using h₁
      have hout₂ : β.1.2 ≠ α.1.1 ∧ β.1.2 ≠ α.1.2 := by
        simpa only [not_or] using h₂
      let i : Spectator α := ⟨β.1.1, hout₁⟩
      let j : Spectator α := ⟨β.1.2, hout₂⟩
      have hij : i ≠ j := by
        intro he
        have := congrArg Subtype.val he
        exact (ne_of_lt β.2) this
      let W : Plane → (Spectator α → Plane) → ℝ≥0∞ := fun _ v =>
        heatPotential (v i - v j)
      have hW : Measurable (Function.uncurry W) := by
        dsimp [W]
        exact measurable_heatPotential.comp
          (((measurable_pi_apply i).comp measurable_snd).sub
            ((measurable_pi_apply j).comp measurable_snd))
      have hweight : ∀ c : Plane, ∀ v : Spectator α → Plane,
          heatPotential ((collisionEmbedding α (c, v)) β.1.1 -
            (collisionEmbedding α (c, v)) β.1.2) = W c v := by
        intro c v
        simp [W, collisionEmbedding, hout₁, hout₂, i, j]
      calc
        _ = ∫⁻ z : FusedConfiguration α,
            (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
              ∏ i' : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i' - x i'))) *
              W z.1 z.2 := by
                apply lintegral_congr
                intro z
                rw [hweight z.1 z.2]
        _ ≤ heatPotentialRowBound b := by
              apply lintegral_fusedTensor_weight_le α ha c₀ x W hW
              intro c
              exact lintegral_tensorHeatKernel_mul_pairPotential_le hb i j hij x

private theorem collisionKernel_bdd_of_time {n : ℕ} (α : CollisionPair n)
    (θ : ℝ) {q : ℝ} (hq : 0 < q) (z' : FusedConfiguration α) :
    ∃ M : ℝ, ∀ z : FusedConfiguration α, |collisionKernel α θ q z z'| ≤ M := by
  classical
  let M : ℝ := (4 * Real.pi * scalarDensity θ q) *
    ((2 * Real.pi * (q / 2))⁻¹ *
      ∏ i : Spectator α, (2 * Real.pi * q)⁻¹)
  refine ⟨M, ?_⟩
  intro z
  have hc : 0 < 4 * Real.pi * scalarDensity θ q := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (scalarDensity_pos θ hq)
  have htcenter : 0 ≤ q / 2 := by positivity
  have hcenter : heatKernel (q / 2) (z'.1 - z.1) ≤
      (2 * Real.pi * (q / 2))⁻¹ := heatKernel_le_at_zero htcenter _
  have hspec : ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i) ≤
      ∏ i : Spectator α, (2 * Real.pi * q)⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (Critical2DKPZ.heatKernel_pos hq _).le
    · intro i hi
      exact heatKernel_le_at_zero hq.le _
  have hnonneg : 0 ≤ collisionKernel α θ q z z' :=
    (collisionKernel_pos α θ hq z z').le
  rw [abs_of_nonneg hnonneg]
  unfold collisionKernel
  dsimp [M]
  have hspec0 : 0 ≤ ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i) :=
    Finset.prod_nonneg fun i hi => (Critical2DKPZ.heatKernel_pos hq _).le
  have hcenterBound0 : 0 ≤ (2 * Real.pi * (q / 2))⁻¹ := inv_nonneg.mpr (by positivity)
  have hprod :
      heatKernel (q / 2) (z'.1 - z.1) *
          ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i) ≤
        (2 * Real.pi * (q / 2))⁻¹ *
          ∏ i : Spectator α, (2 * Real.pi * q)⁻¹ := by
    calc
      _ ≤ (2 * Real.pi * (q / 2))⁻¹ *
            ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i) :=
          mul_le_mul_of_nonneg_right hcenter hspec0
      _ ≤ (2 * Real.pi * (q / 2))⁻¹ *
            ∏ i : Spectator α, (2 * Real.pi * q)⁻¹ :=
          mul_le_mul_of_nonneg_left hspec hcenterBound0
  calc
    (4 * Real.pi * scalarDensity θ q) *
        heatKernel (q / 2) (z'.1 - z.1) *
          ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i)
      = (4 * Real.pi * scalarDensity θ q) *
          (heatKernel (q / 2) (z'.1 - z.1) *
            ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i)) := by ring
    _ ≤ (4 * Real.pi * scalarDensity θ q) *
        ((2 * Real.pi * (q / 2))⁻¹ *
          ∏ i : Spectator α, (2 * Real.pi * q)⁻¹) :=
          mul_le_mul_of_nonneg_left hprod hc.le
    _ = M := rfl

private theorem integrable_incoming_mul_collisionKernel {n : ℕ}
    (α : CollisionPair n) (θ : ℝ) {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (x : Configuration n) (z' : FusedConfiguration α) :
    Integrable (fun z : FusedConfiguration α =>
      incomingKernel α r z x * collisionKernel α θ q z z') := by
  obtain ⟨M, hM⟩ := collisionKernel_bdd_of_time α θ hq z'
  have hcont : Continuous (fun z : FusedConfiguration α =>
      collisionKernel α θ q z z') := by
    unfold collisionKernel
    have hc : Continuous (fun z : FusedConfiguration α =>
        heatKernel (q / 2) (z'.1 - z.1)) :=
      (continuous_heatKernel (q / 2)).comp (continuous_const.sub continuous_fst)
    have hs : Continuous (fun z : FusedConfiguration α =>
        ∏ i : Spectator α, heatKernel q (z'.2 i - z.2 i)) := by
      apply continuous_finsetProd
      intro i hi
      exact (continuous_heatKernel q).comp
        (continuous_const.sub ((continuous_apply i).comp continuous_snd))
    exact (continuous_const.mul hc).mul hs
  apply (integrable_incomingKernel_fused α hr x).mul_bdd hcont.aestronglyMeasurable
  filter_upwards [] with z
  change ‖collisionKernel α θ q z z'‖ ≤ M
  rw [Real.norm_eq_abs]
  exact hM z

private theorem lintegral_incoming_mul_collisionKernel {n : ℕ}
    (α : CollisionPair n) (θ : ℝ) {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (x : Configuration n) (z' : FusedConfiguration α) :
    (∫⁻ z : FusedConfiguration α,
      ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ q z z')) =
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
        (ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
          (ENNReal.ofReal (heatKernel ((r + q) / 2)
            (z'.1 - (1 / 2 : ℝ) • (x α.1.1 + x α.1.2))) *
            ∏ i : Spectator α, ENNReal.ofReal
              (heatKernel (r + q) (z'.2 i - x i.1)))) := by
  have hi := integrable_incoming_mul_collisionKernel α θ hr hq x z'
  have hnonneg : ∀ᵐ z : FusedConfiguration α ∂volume,
      0 ≤ incomingKernel α r z x * collisionKernel α θ q z z' := by
    filter_upwards [] with z
    exact mul_nonneg (incomingKernel_pos α hr z x).le
      (collisionKernel_pos α θ hq z z').le
  calc
    _ = ∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x * collisionKernel α θ q z z') := by
            apply lintegral_congr
            intro z
            rw [← ENNReal.ofReal_mul (incomingKernel_pos α hr z x).le]
    _ = ENNReal.ofReal (∫ z : FusedConfiguration α,
          incomingKernel α r z x * collisionKernel α θ q z z') :=
            (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
    _ = _ := by
          rw [integral_incoming_mul_collisionKernel α hr hq x z']
          rw [ENNReal.ofReal_mul (mul_nonneg
              (mul_nonneg (by norm_num) Real.pi_pos.le)
              (scalarDensity_pos θ hq).le),
            ENNReal.ofReal_mul (Critical2DKPZ.heatKernel_pos (mul_pos (by norm_num) hr) _).le,
            ENNReal.ofReal_mul (Critical2DKPZ.heatKernel_pos
              (div_pos (add_pos hr hq) (by norm_num)) _).le,
            ENNReal.ofReal_prod_of_nonneg (fun i hi =>
              (Critical2DKPZ.heatKernel_pos (by positivity) _).le)]

private theorem lintegral_incoming_collision_potential_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) (θ : ℝ)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (x : Configuration n) :
    (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
      (ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ q z z')) *
        heatPotential ((collisionEmbedding α z') β.1.1 -
          (collisionEmbedding α z') β.1.2)) ≤
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
        (ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
          heatPotentialRowBound (r + q)) := by
  let K : FusedConfiguration α × FusedConfiguration α → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (incomingKernel α r p.1 x) *
      ENNReal.ofReal (collisionKernel α θ q p.1 p.2)
  let V : FusedConfiguration α → ℝ≥0∞ := fun z' =>
    heatPotential ((collisionEmbedding α z') β.1.1 -
      (collisionEmbedding α z') β.1.2)
  let H : FusedConfiguration α → ℝ≥0∞ := fun z' =>
    ENNReal.ofReal (heatKernel ((r + q) / 2)
      (z'.1 - (1 / 2 : ℝ) • (x α.1.1 + x α.1.2))) *
      ∏ i : Spectator α, ENNReal.ofReal (heatKernel (r + q) (z'.2 i - x i.1))
  have hKI : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α r p.1 x)) := by
    have hArgs : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        (r, (p.1, x))) := by fun_prop
    exact (measurable_incomingKernel α).comp hArgs |>.ennreal_ofReal
  have hKC : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      ENNReal.ofReal (collisionKernel α θ q p.1 p.2)) := by
    have hArgs : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ((θ, q), p)) := by fun_prop
    exact (measurable_collisionKernel α).comp hArgs |>.ennreal_ofReal
  have hK : Measurable K := by dsimp [K]; exact hKI.mul hKC
  have hV : Measurable V := by
    dsimp [V]
    exact measurable_heatPotential.comp
      (((measurable_pi_apply β.1.1).comp
          ((measurable_collisionEmbedding α).comp measurable_id)).sub
        ((measurable_pi_apply β.1.2).comp
          ((measurable_collisionEmbedding α).comp measurable_id)))
  have hH : Measurable H := by
    dsimp [H]
    have hc : Measurable (fun z' : FusedConfiguration α =>
        heatKernel ((r + q) / 2)
          (z'.1 - (1 / 2 : ℝ) • (x α.1.1 + x α.1.2))) := by
      unfold heatKernel
      fun_prop
    have hs : Measurable (fun z' : FusedConfiguration α =>
        ∏ i : Spectator α, ENNReal.ofReal
          (heatKernel (r + q) (z'.2 i - x i.1))) := by
      apply Finset.measurable_fun_prod
      intro i hi
      have hm : Measurable (fun z' : FusedConfiguration α =>
          heatKernel (r + q) (z'.2 i - x i.1)) := by
        unfold heatKernel
        fun_prop
      exact hm.ennreal_ofReal
    exact hc.ennreal_ofReal.mul hs
  have hW : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      K p * V p.2) := hK.mul (hV.comp measurable_snd)
  have hKernelSlice (z' : FusedConfiguration α) :
      Measurable (fun z : FusedConfiguration α => K (z, z')) :=
    hK.comp (measurable_id.prodMk measurable_const)
  calc
    _ = ∫⁻ z' : FusedConfiguration α, ∫⁻ z : FusedConfiguration α,
          K (z, z') * V z' :=
          lintegral_lintegral_swap hW.aemeasurable
    _ = ∫⁻ z' : FusedConfiguration α,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
            (ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
              (H z' * V z')) := by
            apply lintegral_congr
            intro z'
            calc
              _ = (∫⁻ z : FusedConfiguration α, K (z, z')) * V z' := by
                    rw [lintegral_mul_const _ (hKernelSlice z')]
              _ = _ := by
                    rw [lintegral_incoming_mul_collisionKernel α θ hr hq x z']
                    simp only [V, H]
                    ac_rfl
    _ ≤ ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
          (ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
            heatPotentialRowBound (r + q)) := by
            have hrow := lintegral_fusedPairPotential_separated_le α β hne
              (by positivity : 0 < (r + q) / 2) (by linarith : 0 < r + q)
              ((1 / 2 : ℝ) • (x α.1.1 + x α.1.2)) (fun i => x i.1)
            calc
              _ = (ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                    ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1))) *
                    ∫⁻ z' : FusedConfiguration α, H z' * V z' := by
                      calc
                        _ = ∫⁻ z' : FusedConfiguration α,
                              (ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                                ENNReal.ofReal (heatKernel (2 * r)
                                  (x α.1.2 - x α.1.1))) * (H z' * V z') := by
                                apply lintegral_congr
                                intro z'
                                ac_rfl
                        _ = _ := lintegral_const_mul _ (hH.mul (hV.comp measurable_id))
              _ ≤ (ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                    ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1))) *
                    heatPotentialRowBound (r + q) := by
                      calc
                        _ = (∫⁻ z' : FusedConfiguration α, H z' * V z') *
                              (ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                                ENNReal.ofReal (heatKernel (2 * r)
                                  (x α.1.2 - x α.1.1))) := by ac_rfl
                        _ ≤ heatPotentialRowBound (r + q) *
                              (ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                                ENNReal.ofReal (heatKernel (2 * r)
                                  (x α.1.2 - x α.1.1))) := mul_le_mul_left hrow _
                        _ = _ := by ac_rfl
              _ = _ := by ac_rfl

private noncomputable def pathRow {n : ℕ} (θ : ℝ) (w : List (CollisionPair n))
    (t : ℝ) (x : Configuration n) : ℝ≥0∞ :=
  ∫⁻ y : Configuration n, pathTimeKernel θ w id id (t, x, y)

private theorem pathTimeKernel_compose_left {n : ℕ} (θ : ℝ)
    (w : List (CollisionPair n)) {X : Type} (eX : X → Configuration n)
    (t : ℝ) (x : X) (y : Configuration n) :
    pathTimeKernel (X := X) (Y := Configuration n) θ w eX id (t, x, y) =
      pathTimeKernel (X := Configuration n) (Y := Configuration n) θ w id id
        (t, eX x, y) := by
  cases w <;> rfl

private theorem pathRow_compose_left {n : ℕ} (θ : ℝ)
    (w : List (CollisionPair n)) {X : Type} (eX : X → Configuration n)
    (t : ℝ) (x : X) :
    (∫⁻ y : Configuration n, pathTimeKernel θ w eX id (t, x, y)) =
      pathRow θ w t (eX x) := by
  apply lintegral_congr
  intro y
  exact pathTimeKernel_compose_left θ w eX t x y

private theorem pathRow_cons_comp {n : ℕ} (θ : ℝ) (α : CollisionPair n)
    (w : List (CollisionPair n)) (t : ℝ) (x : Configuration n) :
    pathRow θ (α :: w) t x =
      timeKernelComp volume (causalKernel (freeTimeKernel id (collisionEmbedding α)))
        (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
          (fun p : ℝ × FusedConfiguration α × PUnit =>
            pathRow θ w p.1 (collisionEmbedding α p.2.1))) (t, x, ()) := by
  rw [pathRow]
  calc
    _ = ∫⁻ q : ℝ × FusedConfiguration α,
        causalKernel (freeTimeKernel id (collisionEmbedding α))
            (q.1, x, q.2) *
          ∫⁻ p : ℝ × FusedConfiguration α,
            causalKernel (collisionTimeKernel α θ) (p.1, q.2, p.2) *
              pathRow θ w (t - q.1 - p.1) (collisionEmbedding α p.2) := by
          have h := lintegral_pathTimeKernel_cons_mul θ t α w
            (f := fun _ : Configuration n => (1 : ℝ≥0∞)) (by fun_prop) x
          have h' : pathRow θ (α :: w) t x =
              ∫⁻ q : ℝ × FusedConfiguration α,
                causalKernel (freeTimeKernel id (collisionEmbedding α))
                    (q.1, x, q.2) *
                  ∫⁻ p : ℝ × FusedConfiguration α,
                    causalKernel (collisionTimeKernel α θ) (p.1, q.2, p.2) *
                      ∫⁻ y : Configuration n,
                        pathTimeKernel θ w (collisionEmbedding α) id
                          (t - q.1 - p.1, p.2, y) := by
                simpa only [pathRow, mul_one] using h
          calc
            pathRow θ (α :: w) t x = _ := h'
            _ = ∫⁻ q : ℝ × FusedConfiguration α,
                  causalKernel (freeTimeKernel id (collisionEmbedding α))
                      (q.1, x, q.2) *
                    ∫⁻ p : ℝ × FusedConfiguration α,
                      causalKernel (collisionTimeKernel α θ) (p.1, q.2, p.2) *
                        pathRow θ w (t - q.1 - p.1) (collisionEmbedding α p.2) := by
                  apply lintegral_congr
                  intro q
                  apply congrArg (fun z =>
                    causalKernel (freeTimeKernel id (collisionEmbedding α))
                      (q.1, x, q.2) * z)
                  apply lintegral_congr
                  intro p
                  apply congrArg (fun z =>
                    causalKernel (collisionTimeKernel α θ) (p.1, q.2, p.2) * z)
                  exact pathRow_compose_left θ w (collisionEmbedding α)
                    (t - q.1 - p.1) p.2
    _ = timeKernelComp volume (causalKernel (freeTimeKernel id (collisionEmbedding α)))
          (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
            (fun p : ℝ × FusedConfiguration α × PUnit =>
              pathRow θ w p.1 (collisionEmbedding α p.2.1))) (t, x, ()) := rfl

private theorem pathRow_cons_interval {n : ℕ} (θ : ℝ) (α : CollisionPair n)
    (w : List (CollisionPair n)) {t : ℝ} (_ht : 0 < t) (x : Configuration n) :
    pathRow θ (α :: w) t x =
      ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ z : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α r z x) *
          ∫⁻ q in Ioo (0 : ℝ) (t - r), ∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (collisionKernel α θ q z z') *
              pathRow θ w (t - r - q) (collisionEmbedding α z') := by
  classical
  let I : TimeKernel (Configuration n) (FusedConfiguration α) :=
    freeTimeKernel id (collisionEmbedding α)
  let J : TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
    collisionTimeKernel α θ
  let T : TimeKernel (FusedConfiguration α) PUnit := fun p =>
    pathRow θ w p.1 (collisionEmbedding α p.2.1)
  have hI : Measurable I := measurable_freeTimeKernel measurable_id
    (measurable_collisionEmbedding α)
  have hJ : Measurable J := measurable_collisionTimeKernel α θ
  have hT : Measurable T := by
    have hpath := measurable_pathTimeKernel θ w measurable_id measurable_id
    have hpath' : Measurable (fun p : (ℝ × Configuration n) × Configuration n =>
        pathTimeKernel θ w id id (p.1.1, p.1.2, p.2)) := hpath.comp (by fun_prop)
    have hrow := hpath'.lintegral_prod_right' (ν := volume)
    have hmap : Measurable (fun p : ℝ × FusedConfiguration α × PUnit =>
        (p.1, collisionEmbedding α p.2.1)) :=
      measurable_fst.prodMk
        ((measurable_collisionEmbedding α).comp measurable_snd.fst)
    exact hrow.comp hmap
  have hTcausal : causalKernel T = T := by
    funext p
    by_cases hp : 0 < p.1
    · simp [causalKernel, hp]
    · have htail := pathTimeKernel_causal θ w (collisionEmbedding α) id
      have hzero : ∀ y : Configuration n,
          pathTimeKernel θ w (collisionEmbedding α) id (p.1, p.2.1, y) = 0 := by
        intro y
        rw [← htail]
        simp [causalKernel, hp]
      have hzero' : ∀ y : Configuration n,
          pathTimeKernel θ w id id (p.1, collisionEmbedding α p.2.1, y) = 0 := by
        intro y
        rw [← pathTimeKernel_compose_left θ w (collisionEmbedding α)
          p.1 p.2.1 y]
        exact hzero y
      simp [causalKernel, hp, T, pathRow, hzero']
  have hQ : Measurable (timeKernelComp volume (causalKernel J) T) :=
    measurable_timeKernelComp volume (measurable_causalKernel hJ) hT
  have hQcausal : causalKernel (timeKernelComp volume (causalKernel J) T) =
      timeKernelComp volume (causalKernel J) T :=
    by simpa only [hTcausal] using timeKernelComp_causal volume J T
  rw [pathRow_cons_comp]
  change timeKernelComp volume (causalKernel I)
    (timeKernelComp volume (causalKernel J) T) (t, x, ()) = _
  rw [← hQcausal]
  rw [timeKernelComp_causal_eq volume hI hQ t x ()]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  apply lintegral_congr
  intro z
  have hinner := timeKernelComp_causal_eq volume hJ hT (t - r) z ()
  rw [hTcausal] at hinner
  calc
    I (r, x, z) * timeKernelComp volume (causalKernel J) T (t - r, z, ()) =
        ENNReal.ofReal (incomingKernel α r z x) *
          timeKernelComp volume (causalKernel J) T (t - r, z, ()) := by
            rfl
    _ = ENNReal.ofReal (incomingKernel α r z x) *
          ∫⁻ q in Ioo (0 : ℝ) (t - r), ∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (collisionKernel α θ q z z') *
              pathRow θ w (t - r - q) (collisionEmbedding α z') := by
            rw [hinner]
            rfl

private theorem pathRow_cons_interval_swapped {n : ℕ} (θ : ℝ)
    (α : CollisionPair n) (w : List (CollisionPair n)) {t : ℝ}
    (ht : 0 < t) (x : Configuration n) :
    pathRow θ (α :: w) t x =
      ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
        ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
          (ENNReal.ofReal (incomingKernel α r z x) *
            ENNReal.ofReal (collisionKernel α θ q z z')) *
            pathRow θ w (t - r - q) (collisionEmbedding α z') := by
  rw [pathRow_cons_interval θ α w ht x]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  let I : TimeKernel (Configuration n) (FusedConfiguration α) :=
    freeTimeKernel id (collisionEmbedding α)
  let J : TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
    collisionTimeKernel α θ
  let T : TimeKernel (FusedConfiguration α) PUnit := fun p =>
    pathRow θ w p.1 (collisionEmbedding α p.2.1)
  have hI : Measurable I := measurable_freeTimeKernel measurable_id
    (measurable_collisionEmbedding α)
  have hJ : Measurable J := measurable_collisionTimeKernel α θ
  have hpath := measurable_pathTimeKernel θ w measurable_id measurable_id
  have hpath' : Measurable (fun p : (ℝ × Configuration n) × Configuration n =>
      pathTimeKernel θ w id id (p.1.1, p.1.2, p.2)) := hpath.comp (by fun_prop)
  have hrow := hpath'.lintegral_prod_right' (ν := volume)
  have hmap : Measurable (fun p : ℝ × FusedConfiguration α × PUnit =>
      (p.1, collisionEmbedding α p.2.1)) :=
    measurable_fst.prodMk
      ((measurable_collisionEmbedding α).comp measurable_snd.fst)
  have hT : Measurable T := hrow.comp hmap
  have hG : Measurable
      (fun p : (FusedConfiguration α × ℝ) × FusedConfiguration α =>
        J (p.1.2, p.1.1, p.2) * T (t - r - p.1.2, p.2, ())) := by
    have hK := hJ.comp (by fun_prop : Measurable
      (fun p : (FusedConfiguration α × ℝ) × FusedConfiguration α =>
        (p.1.2, p.1.1, p.2)))
    have htail := hT.comp (by fun_prop : Measurable
      (fun p : (FusedConfiguration α × ℝ) × FusedConfiguration α =>
        (t - r - p.1.2, p.2, ())))
    exact hK.mul htail
  have hGint : Measurable (fun p : FusedConfiguration α × ℝ =>
      ∫⁻ z' : FusedConfiguration α,
        J (p.2, p.1, z') * T (t - r - p.2, z', ())) :=
    hG.lintegral_prod_right' (ν := volume)
  have hA : Measurable (Function.uncurry (fun z : FusedConfiguration α =>
      fun q : ℝ => I (r, x, z) * ∫⁻ z' : FusedConfiguration α,
        J (q, z, z') * T (t - r - q, z', ()))) := by
    have hI' : Measurable (fun z : FusedConfiguration α => I (r, x, z)) :=
      hI.comp (by fun_prop)
    exact (hI'.comp measurable_fst).mul hGint
  have hswap := lintegral_lintegral_swap
    (μ := volume) (ν := volume.restrict (Ioo (0 : ℝ) (t - r))) hA.aemeasurable
  have hIfinite (z : FusedConfiguration α) : I (r, x, z) ≠ ⊤ := by
    change ENNReal.ofReal (freeKernel n r x (collisionEmbedding α z)) ≠ ⊤
    exact ENNReal.ofReal_ne_top
  calc
    (∫⁻ z : FusedConfiguration α,
        I (r, x, z) * ∫⁻ q in Ioo (0 : ℝ) (t - r),
          ∫⁻ z' : FusedConfiguration α,
            J (q, z, z') * T (t - r - q, z', ())) =
      ∫⁻ z : FusedConfiguration α, ∫⁻ q in Ioo (0 : ℝ) (t - r),
        I (r, x, z) * ∫⁻ z' : FusedConfiguration α,
          J (q, z, z') * T (t - r - q, z', ()) := by
            apply lintegral_congr
            intro z
            exact (lintegral_const_mul' (I (r, x, z)) _ (hIfinite z)).symm
    _ = ∫⁻ q in Ioo (0 : ℝ) (t - r), ∫⁻ z : FusedConfiguration α,
          I (r, x, z) * ∫⁻ z' : FusedConfiguration α,
            J (q, z, z') * T (t - r - q, z', ()) := hswap
    _ = ∫⁻ q in Ioo (0 : ℝ) (t - r), ∫⁻ z : FusedConfiguration α,
          ∫⁻ z' : FusedConfiguration α,
            (I (r, x, z) * J (q, z, z')) * T (t - r - q, z', ()) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
            apply lintegral_congr
            intro z
            rw [← lintegral_const_mul' (I (r, x, z)) _ (hIfinite z)]
            apply lintegral_congr
            intro z'
            ac_rfl
    _ = ∫⁻ q in Ioo (0 : ℝ) (t - r), ∫⁻ z : FusedConfiguration α,
          ∫⁻ z' : FusedConfiguration α,
            (ENNReal.ofReal (incomingKernel α r z x) *
              ENNReal.ofReal (collisionKernel α θ q z z')) *
              pathRow θ w (t - r - q) (collisionEmbedding α z') := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
            apply lintegral_congr
            intro z
            apply lintegral_congr
            intro z'
            rfl

private theorem heatPotentialRowBound_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    heatPotentialRowBound b ≤ heatPotentialRowBound a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpow := Real.rpow_le_rpow_of_nonpos ha hab
    (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  have hcoef : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  unfold heatPotentialRowBound
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hcoef)

private theorem lintegral_scalarDensity_subinterval_le {θ τ t r : ℝ}
    (htτ : t ≤ τ) (hr : 0 < r) :
    (∫⁻ q in Ioo (0 : ℝ) (t - r), ENNReal.ofReal (scalarDensity θ q)) ≤
      ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * τ)) := by
  have hsubset : Ioo (0 : ℝ) (t - r) ⊆ Ioo (0 : ℝ) τ := by
    intro q hq
    exact ⟨hq.1, lt_of_lt_of_le hq.2 (by linarith)⟩
  calc
    _ ≤ ∫⁻ q in Ioo (0 : ℝ) τ, ENNReal.ofReal (scalarDensity θ q) :=
      lintegral_mono_set hsubset
    _ ≤ ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * τ)) :=
      lintegral_scalarDensity_Ioo_le

private theorem lintegral_time_heatPotentialRowBound_le {θ τ t : ℝ}
    (htτ : t ≤ τ) (x : Plane) :
    (∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
        (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound (r + q))) ≤
      (ENNReal.ofReal (4 * Real.pi) *
        ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * τ))) *
        integratedPotentialRowConstant * heatPotential x := by
  let B : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi) *
    ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * τ))
  have hBtop : B ≠ ⊤ := by
    dsimp [B]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hDensityMass (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) t) :
      (∫⁻ q in Ioo (0 : ℝ) (t - r),
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ q)) ≤ B := by
    have hscalar := lintegral_scalarDensity_subinterval_le (θ := θ) htτ hr.1
    calc
      _ = ENNReal.ofReal (4 * Real.pi) *
            ∫⁻ q in Ioo (0 : ℝ) (t - r), ENNReal.ofReal (scalarDensity θ q) := by
              calc
                _ = ∫⁻ q in Ioo (0 : ℝ) (t - r),
                      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (scalarDensity θ q) := by
                        apply lintegral_congr_ae
                        filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
                        calc
                          ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) =
                              ENNReal.ofReal (scalarDensity θ q * (4 * Real.pi)) := by
                                congr 1
                                ring
                          _ = ENNReal.ofReal (scalarDensity θ q) * ENNReal.ofReal (4 * Real.pi) :=
                                ENNReal.ofReal_mul (scalarDensity_pos θ hq.1).le
                          _ = _ := by ac_rfl
                _ = _ := by
                      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ B := by
            exact mul_le_mul' le_rfl hscalar
  calc
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) t,
          B * (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound r) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            have hGtop :
                (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound r) ≠ ⊤ := by
              exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (heatPotentialRowBound_ne_top r)
            have hqpoint {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) (t - r)) :
                ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                  (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound (r + q)) ≤
                  ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                    (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound r) := by
              apply mul_le_mul' le_rfl
              apply mul_le_mul' le_rfl
              exact heatPotentialRowBound_antitone hr.1 (by linarith [hq.1])
            calc
              _ ≤ ∫⁻ q in Ioo (0 : ℝ) (t - r),
                    ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                      (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound r) := by
                    apply lintegral_mono_ae
                    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
                    exact hqpoint hq
              _ = (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound r) *
                    ∫⁻ q in Ioo (0 : ℝ) (t - r),
                      ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) := by
                    calc
                      _ = ∫⁻ q in Ioo (0 : ℝ) (t - r),
                            (ENNReal.ofReal (heatKernel (2 * r) x) *
                              heatPotentialRowBound r) *
                              ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) := by
                                apply lintegral_congr_ae
                                filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
                                ac_rfl
                      _ = _ := lintegral_const_mul' _ _ hGtop
              _ ≤ B * (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound r) := by
                    calc
                      _ ≤ (ENNReal.ofReal (heatKernel (2 * r) x) * heatPotentialRowBound r) * B :=
                            mul_le_mul' le_rfl (hDensityMass r hr)
                      _ = _ := by ac_rfl
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) t,
          B * (heatPotentialRowBound r * ENNReal.ofReal (heatKernel (2 * r) x)) := by
            apply lintegral_mono
            intro r
            exact le_of_eq (by ac_rfl)
    _ = B * ∫⁻ r in Ioo (0 : ℝ) t,
          heatPotentialRowBound r * ENNReal.ofReal (heatKernel (2 * r) x) := by
            rw [← lintegral_const_mul' _ _ hBtop]
    _ ≤ B * ∫⁻ r in Ioi (0 : ℝ),
          heatPotentialRowBound r * ENNReal.ofReal (heatKernel (2 * r) x) := by
            exact mul_le_mul' le_rfl (lintegral_mono_set Ioo_subset_Ioi_self)
    _ = B * (integratedPotentialRowConstant * heatPotential x) := by
            rw [lintegral_heatPotentialRowBound_mul_heatKernel_eq_constant]
    _ = _ := by dsimp [B]; ac_rfl

private theorem lintegral_incoming_collision_eq {n : ℕ} (α : CollisionPair n)
    (θ : ℝ) {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (x : Configuration n) :
    (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
      ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ q z z')) =
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
        ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) := by
  calc
    _ = ∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x) *
            (∫⁻ z' : FusedConfiguration α,
              ENNReal.ofReal (collisionKernel α θ q z z')) := by
            apply lintegral_congr
            intro z
            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x) *
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) := by
            apply lintegral_congr
            intro z
            rw [lintegral_collisionKernel_right α θ hq z]
    _ = (∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x)) *
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) :=
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [lintegral_incomingKernel_fused α hr x]; ac_rfl

private theorem pathRow_nil_eq_one {n : ℕ} (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (x : Configuration n) : pathRow θ [] t x = 1 := by
  simp [pathRow, pathTimeKernel, causalKernel, ht, freeTimeKernel,
    lintegral_freeKernel_right n ht x]

private noncomputable def continuumTimeFactor (θ τ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (4 * Real.pi) *
    ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * τ))) *
      integratedPotentialRowConstant

private theorem continuumTimeFactor_pos (θ τ : ℝ) : 0 < continuumTimeFactor θ τ := by
  unfold continuumTimeFactor
  apply ENNReal.mul_pos
  · exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne').ne'
  · exact integratedPotentialRowConstant_pos.ne'

private theorem continuumTimeFactor_ne_top (θ τ : ℝ) :
    continuumTimeFactor θ τ ≠ ⊤ := by
  unfold continuumTimeFactor
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · exact integratedPotentialRowConstant_ne_top

private theorem heatPotentialRowBound_pos {t : ℝ} (ht : 0 < t) :
    0 < heatPotentialRowBound t := by
  unfold heatPotentialRowBound
  apply ENNReal.mul_pos
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · exact halfTimeResolventConstant_pos.ne'

private theorem exists_pathRow_heatPotential_bound {n : ℕ} (θ : ℝ) :
    ∀ (α : CollisionPair n) (w : List (CollisionPair n)),
      (α :: w).IsChain (· ≠ ·) → ∀ {τ : ℝ}, 0 < τ →
        ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, 0 < t → t ≤ τ → ∀ x : Configuration n,
          pathRow θ (α :: w) t x ≤
            ENNReal.ofReal C * heatPotential (x α.1.2 - x α.1.1) := by
  intro α w
  induction w generalizing α with
  | nil =>
      intro hw τ hτ
      let D : ℝ≥0∞ := (heatPotentialRowBound τ)⁻¹
      let E : ℝ≥0∞ := continuumTimeFactor θ τ
      let C : ℝ := (D * E).toReal
      have hrowτpos : 0 < heatPotentialRowBound τ := heatPotentialRowBound_pos hτ
      have hrowτtop : heatPotentialRowBound τ ≠ ⊤ := heatPotentialRowBound_ne_top τ
      have hDpos : 0 < D := ENNReal.inv_pos.mpr hrowτtop
      have hDtop : D ≠ ⊤ := ENNReal.inv_ne_top.mpr hrowτpos.ne'
      have hEpos : 0 < E := continuumTimeFactor_pos θ τ
      have hEtop : E ≠ ⊤ := continuumTimeFactor_ne_top θ τ
      have hCENNpos : 0 < D * E := ENNReal.mul_pos hDpos.ne' hEpos.ne'
      have hCENNtop : D * E ≠ ⊤ := ENNReal.mul_ne_top hDtop hEtop
      have hCpos : 0 < C := by
        dsimp [C]
        exact ENNReal.toReal_pos hCENNpos.ne' hCENNtop
      have hC : ENNReal.ofReal C = D * E := by
        dsimp [C]
        exact ENNReal.ofReal_toReal hCENNtop
      have hcancel : D * heatPotentialRowBound τ = 1 :=
        ENNReal.inv_mul_cancel hrowτpos.ne' hrowτtop
      refine ⟨C, hCpos, ?_⟩
      intro t ht htτ x
      have hbase : pathRow θ [α] t x =
          ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
              ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) := by
        rw [pathRow_cons_interval_swapped θ α [] ht x]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
        have hs : 0 < t - r - q := sub_pos.mpr hq.2
        simp_rw [pathRow_nil_eq_one θ hs, mul_one]
        exact lintegral_incoming_collision_eq α θ hr.1 hq.1 x
      have htime := lintegral_time_heatPotentialRowBound_le
        (θ := θ) (τ := τ) (t := t) htτ
        (x α.1.2 - x α.1.1)
      calc
        pathRow θ [α] t x =
            ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
              ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) := hbase
        _ ≤ ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
              D * (ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                (ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
                  heatPotentialRowBound (r + q))) := by
                apply lintegral_mono_ae
                filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
                apply lintegral_mono_ae
                filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
                have hrq : 0 < r + q := by linarith [hr.1, hq.1]
                have hrqτ : r + q ≤ τ := by linarith [hr.2, hq.2, htτ]
                have hrow := heatPotentialRowBound_antitone hrq hrqτ
                have hone : 1 ≤ D * heatPotentialRowBound (r + q) := by
                  calc
                    1 = D * heatPotentialRowBound τ := hcancel.symm
                    _ ≤ D * heatPotentialRowBound (r + q) :=
                      mul_le_mul' le_rfl hrow
                calc
                  _ = ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                        ENNReal.ofReal (heatKernel (2 * r)
                          (x α.1.2 - x α.1.1)) * 1 := by simp
                  _ ≤ ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                        ENNReal.ofReal (heatKernel (2 * r)
                          (x α.1.2 - x α.1.1)) *
                          (D * heatPotentialRowBound (r + q)) :=
                            mul_le_mul' le_rfl hone
                  _ = _ := by ac_rfl
        _ = D * ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
              ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                (ENNReal.ofReal (heatKernel (2 * r)
                  (x α.1.2 - x α.1.1)) * heatPotentialRowBound (r + q)) := by
                simp_rw [lintegral_const_mul' D _ hDtop]
        _ ≤ D * (E * heatPotential (x α.1.2 - x α.1.1)) := by
                apply mul_le_mul' le_rfl
                simpa only [E, continuumTimeFactor] using htime
        _ = ENNReal.ofReal C * heatPotential (x α.1.2 - x α.1.1) := by
                rw [hC]
                ac_rfl
  | cons β w ih =>
      intro hw τ hτ
      have hparts := List.isChain_cons_cons.mp hw
      obtain ⟨Ctail, hCtail, htail⟩ := ih β hparts.2 hτ
      let E : ℝ≥0∞ := continuumTimeFactor θ τ
      let C : ℝ := Ctail * E.toReal
      have hEpos : 0 < E := continuumTimeFactor_pos θ τ
      have hEtop : E ≠ ⊤ := continuumTimeFactor_ne_top θ τ
      have hCpos : 0 < C := by
        dsimp [C]
        exact mul_pos hCtail (ENNReal.toReal_pos hEpos.ne' hEtop)
      have hCENN : ENNReal.ofReal C = ENNReal.ofReal Ctail * E := by
        dsimp [C]
        rw [ENNReal.ofReal_mul (le_of_lt hCtail), ENNReal.ofReal_toReal hEtop]
      refine ⟨C, hCpos, ?_⟩
      intro t ht htτ x
      have hrowPotential :
          pathRow θ (α :: β :: w) t x ≤
            ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
              ENNReal.ofReal Ctail *
                (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
                  (ENNReal.ofReal (incomingKernel α r z x) *
                    ENNReal.ofReal (collisionKernel α θ q z z')) *
                    heatPotential ((collisionEmbedding α z') β.1.1 -
                      (collisionEmbedding α z') β.1.2)) := by
        rw [pathRow_cons_interval_swapped θ α (β :: w) ht x]
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
        have htailPotential :
            (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
              (ENNReal.ofReal (incomingKernel α r z x) *
                ENNReal.ofReal (collisionKernel α θ q z z')) *
                pathRow θ (β :: w) (t - r - q) (collisionEmbedding α z')) ≤
              ENNReal.ofReal Ctail *
                (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
                  (ENNReal.ofReal (incomingKernel α r z x) *
                    ENNReal.ofReal (collisionKernel α θ q z z')) *
                    heatPotential ((collisionEmbedding α z') β.1.1 -
                      (collisionEmbedding α z') β.1.2)) := by
          have hs : 0 < t - r - q := sub_pos.mpr hq.2
          have hsτ : t - r - q ≤ τ := by
            have hle : t - r - q ≤ t := by nlinarith [hr.1, hq.1]
            exact hle.trans htτ
          calc
            _ ≤ ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
                  (ENNReal.ofReal (incomingKernel α r z x) *
                    ENNReal.ofReal (collisionKernel α θ q z z')) *
                    (ENNReal.ofReal Ctail *
                      heatPotential ((collisionEmbedding α z') β.1.1 -
                        (collisionEmbedding α z') β.1.2)) := by
                  apply lintegral_mono
                  intro z
                  apply lintegral_mono
                  intro z'
                  have htailBound := htail hs hsτ (collisionEmbedding α z')
                  have hpotential := heatPotential_sub_swap
                    ((collisionEmbedding α z') β.1.2)
                    ((collisionEmbedding α z') β.1.1)
                  rw [hpotential] at htailBound
                  exact mul_le_mul' le_rfl htailBound
            _ = ENNReal.ofReal Ctail *
                  (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
                    (ENNReal.ofReal (incomingKernel α r z x) *
                      ENNReal.ofReal (collisionKernel α θ q z z')) *
                      heatPotential ((collisionEmbedding α z') β.1.1 -
                        (collisionEmbedding α z') β.1.2)) := by
                  calc
                    _ = ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
                          ENNReal.ofReal Ctail *
                            ((ENNReal.ofReal (incomingKernel α r z x) *
                              ENNReal.ofReal (collisionKernel α θ q z z')) *
                              heatPotential ((collisionEmbedding α z') β.1.1 -
                                (collisionEmbedding α z') β.1.2)) := by
                            apply lintegral_congr
                            intro z
                            apply lintegral_congr
                            intro z'
                            ac_rfl
                    _ = ∫⁻ z : FusedConfiguration α,
                          ENNReal.ofReal Ctail *
                            (∫⁻ z' : FusedConfiguration α,
                              (ENNReal.ofReal (incomingKernel α r z x) *
                                ENNReal.ofReal (collisionKernel α θ q z z')) *
                                heatPotential ((collisionEmbedding α z') β.1.1 -
                                  (collisionEmbedding α z') β.1.2)) := by
                            apply lintegral_congr
                            intro z
                            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
                    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        exact htailPotential
      have hspatialBound (r q : ℝ) (hr : 0 < r) (hq : 0 < q) :
          (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
            (ENNReal.ofReal (incomingKernel α r z x) *
              ENNReal.ofReal (collisionKernel α θ q z z')) *
              heatPotential ((collisionEmbedding α z') β.1.1 -
                (collisionEmbedding α z') β.1.2)) ≤
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
              (ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
                heatPotentialRowBound (r + q)) := by
        exact lintegral_incoming_collision_potential_le α β hparts.1 θ hr hq x
      have htime := lintegral_time_heatPotentialRowBound_le
        (θ := θ) (τ := τ) (t := t) htτ
        (x α.1.2 - x α.1.1)
      calc
        pathRow θ (α :: β :: w) t x ≤
            ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
              ENNReal.ofReal Ctail *
                (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
                  (ENNReal.ofReal (incomingKernel α r z x) *
                    ENNReal.ofReal (collisionKernel α θ q z z')) *
                    heatPotential ((collisionEmbedding α z') β.1.1 -
                      (collisionEmbedding α z') β.1.2)) := hrowPotential
        _ ≤ ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
              ENNReal.ofReal Ctail *
                (ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                  (ENNReal.ofReal (heatKernel (2 * r)
                    (x α.1.2 - x α.1.1)) * heatPotentialRowBound (r + q))) := by
                apply lintegral_mono_ae
                filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
                apply lintegral_mono_ae
                filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
                exact mul_le_mul' le_rfl (hspatialBound r q hr.1 hq.1)
        _ = ENNReal.ofReal Ctail *
              ∫⁻ r in Ioo (0 : ℝ) t, ∫⁻ q in Ioo (0 : ℝ) (t - r),
                ENNReal.ofReal (4 * Real.pi * scalarDensity θ q) *
                  (ENNReal.ofReal (heatKernel (2 * r)
                    (x α.1.2 - x α.1.1)) * heatPotentialRowBound (r + q)) := by
                simp_rw [lintegral_const_mul' (ENNReal.ofReal Ctail) _
                  ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Ctail *
              (E * heatPotential (x α.1.2 - x α.1.1)) := by
                apply mul_le_mul' le_rfl
                simpa only [E, continuumTimeFactor] using htime
        _ = ENNReal.ofReal C * heatPotential (x α.1.2 - x α.1.1) := by
                rw [hCENN]
                ac_rfl

theorem exists_lintegral_diagramKernel_row_le_heatPotential
    (θ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Configuration h,
      (∫⁻ y : Configuration h, diagramKernel θ (α :: w) τ x y) ≤
        ENNReal.ofReal C * heatPotential (x α.1.2 - x α.1.1) := by
  obtain ⟨C, hC, hrow⟩ := exists_pathRow_heatPotential_bound θ α w hw hτ
  refine ⟨C, hC, fun x => ?_⟩
  have hpath := lintegral_diagramKernel_eq_pathTimeKernel θ τ hτ (α :: w)
    (fun _ : Configuration h => (1 : ℝ≥0∞)) x
  have hbound := hrow hτ le_rfl x
  calc
    _ = ∫⁻ y : Configuration h,
          pathTimeKernel θ (α :: w) id id (τ, x, y) * 1 := by simpa using hpath
    _ = pathRow θ (α :: w) τ x := by simp [pathRow]
    _ ≤ ENNReal.ofReal C * heatPotential (x α.1.2 - x α.1.1) := hbound

end Critical2DKPZ.SHF.Moments
