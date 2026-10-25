/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Critical2DKPZ.SHF.DeltaBose.LaplaceEndpointL2
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! The majorants associated with Tsai’s and Surendranath–Tsai’s collision-chain estimates are summable after counting words at a sufficiently large damping rate. -/

@[expose] public section

namespace Critical2DKPZ.DeltaBose

open MeasureTheory Set
open scoped ENNReal

/-- A length-`k` collision word is a subtype of all `k`-tuples of pairs. -/
theorem collisionWord_card_le_pow (n k : ℕ) :
    Fintype.card (CollisionWord n k) ≤ Fintype.card (CollisionPair n) ^ k := by
  classical
  calc Fintype.card (CollisionWord n k) ≤ Fintype.card (Fin k → CollisionPair n) :=
        Fintype.card_le_of_injective Subtype.val (fun _ _ h => Subtype.ext h)
    _ = Fintype.card (CollisionPair n) ^ k := Fintype.card_pi_const _ _

/-- The number of available pair labels, viewed as a real chain constant. -/
noncomputable def collisionPairCount (n : ℕ) : ℝ :=
  (Fintype.card (CollisionPair n) : ℕ)

/-- At least one collision pair exists as soon as there are two particles. -/
theorem collisionPairCount_pos {n : ℕ} (hn : 2 ≤ n) : 0 < collisionPairCount n := by
  classical
  have hpair : Nonempty (CollisionPair n) := by
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    refine ⟨⟨(i, j), ?_⟩⟩
    exact Fin.mk_lt_mk.mpr (by omega)
  unfold collisionPairCount
  exact_mod_cast (Fintype.card_pos_iff.mpr hpair)

/-- The scalar majorant for `m+1` collision blocks has cubic length growth. -/
noncomputable def correctedChainMajorant (C c₀ lam t : ℝ) (m : ℕ) : ℝ :=
  2 * C ^ (m + 1) * c₀ ^ (2 * (m + 1) + 1) * (m + 1) ^ 3 *
    Real.exp (lam * t) / Real.log (lam - c₀ - 1) ^ m

/-- Counting `N^(m+1)` collision words multiplies the scalar chain majorant by that factor. -/
noncomputable def correctedWordChainMajorant (N C c₀ lam t : ℝ) (m : ℕ) : ℝ :=
  N ^ (m + 1) * correctedChainMajorant C c₀ lam t m

/-- The word-counted chain majorant factors into a constant and a polynomial times a geometric power. -/
theorem correctedWordChainMajorant_eq (N C c₀ lam t : ℝ) (m : ℕ) :
    correctedWordChainMajorant N C c₀ lam t m =
      (2 * N * C * c₀ ^ 3 * Real.exp (lam * t)) *
        ((m + 1 : ℝ) ^ 3 *
          (N * C * c₀ ^ 2 / Real.log (lam - c₀ - 1)) ^ m) := by
  unfold correctedWordChainMajorant correctedChainMajorant
  have hN : N ^ (m + 1) = N * N ^ m := by rw [pow_succ]; ac_rfl
  have hC : C ^ (m + 1) = C * C ^ m := by rw [pow_succ]; ac_rfl
  have hc₀ : c₀ ^ (2 * (m + 1) + 1) = c₀ ^ 3 * (c₀ ^ 2) ^ m := by
    have he : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    rw [he, show 2 * m + 3 = 2 * m + 3 by rfl, pow_add, pow_mul]
    ac_rfl
  rw [hN, hC, hc₀]
  rw [div_pow, mul_pow, mul_pow]
  ring

/-- A cubic polynomial times a geometric sequence is summable when its ratio
is less than one. -/
theorem summable_natSucc_cube_mul_pow {q : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    Summable (fun m : ℕ => (m + 1 : ℝ) ^ 3 * q ^ m) := by
  have hqabs : |q| < 1 := by rw [abs_of_pos hq0]; exact hq
  have hbase : Summable (fun m : ℕ => (m : ℝ) ^ 3 * q ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hqabs
  have hshift' : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 3 * q ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hshift : Summable (fun m : ℕ => (m + 1 : ℝ) ^ 3 * q ^ (m + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshift'
  have hscaled : Summable (fun m : ℕ => q⁻¹ * ((m + 1 : ℝ) ^ 3 * q ^ (m + 1))) :=
    hshift.mul_left q⁻¹
  apply hscaled.congr
  intro m
  simp only [pow_succ]
  field_simp [ne_of_gt hq0]

/-- The word-counted chain majorants are summable when their positive geometric ratio is less than one. -/
theorem summable_correctedWordChainMajorant {N C c₀ lam t : ℝ}
    (hN : 0 < N) (hC : 0 < C) (hc₀ : 0 < c₀)
    (hlog : 0 < Real.log (lam - c₀ - 1))
    (hq : N * C * c₀ ^ 2 / Real.log (lam - c₀ - 1) < 1) :
    Summable (fun m : ℕ => correctedWordChainMajorant N C c₀ lam t m) := by
  rw [show (fun m : ℕ => correctedWordChainMajorant N C c₀ lam t m) =
      fun m : ℕ => (2 * N * C * c₀ ^ 3 * Real.exp (lam * t)) *
        ((m + 1 : ℝ) ^ 3 *
          (N * C * c₀ ^ 2 / Real.log (lam - c₀ - 1)) ^ m) by
        funext m
        exact correctedWordChainMajorant_eq N C c₀ lam t m]
  have hq0 : 0 < N * C * c₀ ^ 2 / Real.log (lam - c₀ - 1) := by positivity
  exact (summable_natSucc_cube_mul_pow hq0 hq).mul_left _

/-- For positive parameters, this damping rate makes the geometric ratio of the word-counted chain majorant equal to `1/2`. -/
noncomputable def correctedChainRate (N C c₀ : ℝ) : ℝ :=
  Real.exp (2 * N * C * c₀ ^ 2) + c₀ + 1

/-- The logarithm of the excess chain rate is `2 * N * C * c₀ ^ 2`. -/
theorem correctedChainRate_log (N C c₀ : ℝ) :
    Real.log (correctedChainRate N C c₀ - c₀ - 1) = 2 * N * C * c₀ ^ 2 := by
  unfold correctedChainRate
  rw [show Real.exp (2 * N * C * c₀ ^ 2) + c₀ + 1 - c₀ - 1 =
    Real.exp (2 * N * C * c₀ ^ 2) by ring, Real.log_exp]


/-- The collision-word chain majorants are summable at this damping rate. -/
theorem summable_correctedWordChainMajorant_at_rate {N C c₀ t : ℝ}
    (hN : 0 < N) (hC : 0 < C) (hc₀ : 0 < c₀) :
    Summable (fun m : ℕ =>
      correctedWordChainMajorant N C c₀ (correctedChainRate N C c₀) t m) := by
  apply summable_correctedWordChainMajorant hN hC hc₀
  · rw [correctedChainRate_log]
    positivity
  · rw [correctedChainRate_log]
    have hden : 0 < 2 * N * C * c₀ ^ 2 := by positivity
    rw [show N * C * c₀ ^ 2 / (2 * N * C * c₀ ^ 2) = 1 / 2 by
      field_simp [ne_of_gt hden]]
    norm_num

/-- The chain majorants are summable with the number of collision pairs for every particle count at least two. -/
theorem summable_correctedCollisionWordMajorant_at_rate {n : ℕ} {C c₀ t : ℝ}
    (hn : 2 ≤ n) (hC : 0 < C) (hc₀ : 0 < c₀) :
    Summable (fun m : ℕ => correctedWordChainMajorant (collisionPairCount n) C c₀
      (correctedChainRate (collisionPairCount n) C c₀) t m) := by
  exact summable_correctedWordChainMajorant_at_rate (collisionPairCount_pos hn) hC hc₀

/-- A collision list with no adjacent repeat, as required after resumming
consecutive collisions of the same pair. -/
def collisionListNoAdjacentRepeat {n : ℕ} : List (CollisionPair n) → Prop
  | [] => True
  | [_] => True
  | α :: β :: w => α ≠ β ∧ collisionListNoAdjacentRepeat (β :: w)

/-- The resummed-word condition is the usual adjacent relation on lists. -/
theorem collisionListNoAdjacentRepeat_iff_isChain {n : ℕ}
    (w : List (CollisionPair n)) :
    collisionListNoAdjacentRepeat w ↔ w.IsChain (fun α β => α ≠ β) := by
  induction w with
  | nil => simp [collisionListNoAdjacentRepeat]
  | cons α w ih =>
      cases w with
      | nil => simp [collisionListNoAdjacentRepeat]
      | cons β w =>
          simp only [collisionListNoAdjacentRepeat, List.isChain_cons_cons]
          exact and_congr_right fun _ => ih

/-- Every finite collision word has no adjacent repeat, in list form. -/
theorem collisionListNoAdjacentRepeat_of_collisionWord {n k : ℕ}
    (w : CollisionWord n k) :
    collisionListNoAdjacentRepeat (List.ofFn w.1) := by
  rw [collisionListNoAdjacentRepeat_iff_isChain, List.isChain_ofFn]
  intro i hi
  exact w.2 ⟨i, by omega⟩ ⟨i + 1, by omega⟩ rfl

/-- The finite endpoint-trace constant in a Laplace-damped word estimate. -/
noncomputable def laplaceEndpointTraceConstant (rate : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), laplaceIncomingTimeMajorant rate t

/-- The finite repeated-collision resolvent constant in a Laplace-damped
word estimate. -/
noncomputable def laplaceCollisionResolventConstant (θ rate : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)


/-- The integrated potential row constant is nonzero. -/
theorem integratedPotentialRowConstant_pos : 0 < integratedPotentialRowConstant := by
  unfold integratedPotentialRowConstant
  apply ENNReal.mul_pos
  · apply ne_of_gt
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    · exact halfTimeResolventConstant_pos.ne'
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'












/-- The Laplace transform of a collision path from a fused collision space to the full configuration space is bounded by the product of the integrated swapping constants and damped collision resolvent constants, followed by an endpoint trace constant. -/
theorem laplacePathSuffix_l2_sq_le {n : ℕ} {θ rate : ℝ}
    (hrate : 0 < rate) (hθ : θ < Real.log rate) (w : List (CollisionPair n)) :
    ∀ (α : CollisionPair n), collisionListNoAdjacentRepeat (α :: w) →
      ∀ {f : Configuration n → ℝ≥0∞}, Measurable f →
      (∫⁻ z : FusedConfiguration α,
        (∫⁻ x : Configuration n,
          laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) id) z x * f x) ^ 2) ≤
        ((integratedPotentialRowConstant ^ w.length) *
          (laplaceCollisionResolventConstant θ rate ^ w.length) *
          laplaceEndpointTraceConstant rate) ^ 2 *
          ∫⁻ x : Configuration n, f x ^ 2 := by
  induction w with
  | nil =>
      intro α _ f hf
      simpa [pathTimeKernel, laplaceTimeKernel_causalKernel,
        laplaceEndpointTraceConstant, laplaceIncomingTimeMajorant] using
        (laplaceTimeKernel_incoming_l2_sq_le α rate hf)
  | cons β w ih =>
      intro α hword f hf
      change α ≠ β ∧ collisionListNoAdjacentRepeat (β :: w) at hword
      let Kswap : FusedConfiguration α → FusedConfiguration β → ℝ≥0∞ :=
        laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β))
      let Kcollision : FusedConfiguration β → FusedConfiguration β → ℝ≥0∞ :=
        collisionResolvent β θ rate
      let Ktail : FusedConfiguration β → Configuration n → ℝ≥0∞ :=
        laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding β) id)
      have hKswap : Measurable (Function.uncurry Kswap) :=
        measurable_laplaceTimeKernel rate
          (measurable_freeTimeKernel (measurable_collisionEmbedding α)
            (measurable_collisionEmbedding β))
      have hKcollision : Measurable (Function.uncurry Kcollision) :=
        measurable_collisionResolvent β θ rate
      have hPathTail : Measurable (pathTimeKernel θ w (collisionEmbedding β) id) :=
        measurable_pathTimeKernel θ w (measurable_collisionEmbedding β) measurable_id
      have hKtail : Measurable (Function.uncurry Ktail) :=
        measurable_laplaceTimeKernel rate hPathTail
      have hKswapBound : ∀ {g : FusedConfiguration β → ℝ≥0∞}, Measurable g →
          (∫⁻ z : FusedConfiguration α,
            (∫⁻ y : FusedConfiguration β, Kswap z y * g y) ^ 2) ≤
            integratedPotentialRowConstant ^ 2 * ∫⁻ y : FusedConfiguration β, g y ^ 2 := by
        intro g hg
        exact laplaceTimeKernel_swapping_l2_sq_le α β hword.1 hrate.le hg
      have hKcollisionBound : ∀ {g : FusedConfiguration β → ℝ≥0∞}, Measurable g →
          (∫⁻ z : FusedConfiguration β,
            (∫⁻ y : FusedConfiguration β, Kcollision z y * g y) ^ 2) ≤
            laplaceCollisionResolventConstant θ rate ^ 2 *
              ∫⁻ y : FusedConfiguration β, g y ^ 2 := by
        intro g hg
        exact collisionResolvent_l2_sq_le β hrate hθ hg
      have hKtailBound : ∀ {g : Configuration n → ℝ≥0∞}, Measurable g →
          (∫⁻ z : FusedConfiguration β,
            (∫⁻ x : Configuration n, Ktail z x * g x) ^ 2) ≤
            ((integratedPotentialRowConstant ^ w.length) *
              (laplaceCollisionResolventConstant θ rate ^ w.length) *
              laplaceEndpointTraceConstant rate) ^ 2 *
              ∫⁻ x : Configuration n, g x ^ 2 := by
        intro g hg
        exact ih β hword.2 hg
      have hInnerMeas :
          Measurable (Function.uncurry (spatialKernelComp volume Kcollision Ktail)) :=
        measurable_spatialKernelComp volume hKcollision hKtail
      have hInnerBound : ∀ {g : Configuration n → ℝ≥0∞}, Measurable g →
          (∫⁻ z : FusedConfiguration β,
            (∫⁻ x : Configuration n,
              spatialKernelComp volume Kcollision Ktail z x * g x) ^ 2) ≤
            (laplaceCollisionResolventConstant θ rate *
              (integratedPotentialRowConstant ^ w.length *
                (laplaceCollisionResolventConstant θ rate ^ w.length) *
                laplaceEndpointTraceConstant rate)) ^ 2 *
              ∫⁻ x : Configuration n, g x ^ 2 := by
        intro g hg
        exact spatialKernelComp_l2_sq_le volume volume volume hKcollision hKtail
          hKcollisionBound hKtailBound hg
      have hComp := spatialKernelComp_l2_sq_le volume volume volume hKswap hInnerMeas
        hKswapBound hInnerBound hf
      have hfactor (z : FusedConfiguration α) (x : Configuration n) :
          laplaceTimeKernel rate (pathTimeKernel θ (β :: w) (collisionEmbedding α) id) z x =
            spatialKernelComp volume Kswap (spatialKernelComp volume Kcollision Ktail) z x := by
        have h := laplaceTimeKernel_pathTimeKernel_cons θ rate β w
          (measurable_collisionEmbedding α) measurable_id z x
        have hc : laplaceTimeKernel rate (collisionTimeKernel β θ) = Kcollision := by
          funext u v
          exact laplaceTimeKernel_collisionTimeKernel β θ rate u v
        rw [hc] at h
        simpa [Kswap, Ktail] using h
      have hAction (z : FusedConfiguration α) :
          (∫⁻ x : Configuration n,
            laplaceTimeKernel rate (pathTimeKernel θ (β :: w) (collisionEmbedding α) id) z x * f x) =
          ∫⁻ x : Configuration n,
            spatialKernelComp volume Kswap (spatialKernelComp volume Kcollision Ktail) z x * f x := by
        apply lintegral_congr
        intro x
        rw [hfactor z x]
      have hconst :
          (integratedPotentialRowConstant *
            (laplaceCollisionResolventConstant θ rate *
              (integratedPotentialRowConstant ^ w.length *
                (laplaceCollisionResolventConstant θ rate ^ w.length) *
                laplaceEndpointTraceConstant rate))) ^ 2 =
          ((integratedPotentialRowConstant ^ (w.length + 1)) *
            (laplaceCollisionResolventConstant θ rate ^ (w.length + 1)) *
            laplaceEndpointTraceConstant rate) ^ 2 := by
        congr 1
        rw [pow_succ, pow_succ]
        ac_rfl
      calc
        (∫⁻ z : FusedConfiguration α,
          (∫⁻ x : Configuration n,
            laplaceTimeKernel rate (pathTimeKernel θ (β :: w) (collisionEmbedding α) id)
              z x * f x) ^ 2) =
          ∫⁻ z : FusedConfiguration α,
            (∫⁻ x : Configuration n,
              spatialKernelComp volume Kswap (spatialKernelComp volume Kcollision Ktail)
                z x * f x) ^ 2 := by
                  apply lintegral_congr
                  intro z
                  rw [hAction z]
        _ ≤ (integratedPotentialRowConstant *
              (laplaceCollisionResolventConstant θ rate *
                (integratedPotentialRowConstant ^ w.length *
                  (laplaceCollisionResolventConstant θ rate ^ w.length) *
                  laplaceEndpointTraceConstant rate))) ^ 2 *
                ∫⁻ x : Configuration n, f x ^ 2 := hComp
        _ = _ := by rw [hconst, List.length_cons]




/-! The path composition identity and positive-time Laplace integration transfer the chain estimate to the ordered diagram integral. -/



end Critical2DKPZ.DeltaBose
