/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PathDominating
import Mathlib.Tactic

/-!
# Form bounds for path-dominating kernels

Uniform bilinear form bounds for the recursively split supremum/Laplace
majorant, including the initial incoming block and its fused collision tail.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

private noncomputable def pathLaplaceFactor (A rate : ℝ) : ℝ :=
  max integratedPotentialRowConstant.toReal 1 * (4 * Real.pi) *
    (Real.log rate - A)⁻¹

private theorem pathLaplaceFactor_pos {A rate : ℝ}
    (hA : Real.exp (A + 1) ≤ rate) : 0 < pathLaplaceFactor A rate := by
  have hrate : 0 < rate := (Real.exp_pos _).trans_le hA
  have hlog : A + 1 ≤ Real.log rate := by
    calc
      A + 1 = Real.log (Real.exp (A + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _) hA
  have hgap : 0 < Real.log rate - A := by linarith
  unfold pathLaplaceFactor
  exact mul_pos (mul_pos
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (mul_pos (by norm_num) Real.pi_pos)) (inv_pos.mpr hgap)

private theorem laplaceCollision_le_pathLaplaceFactor {A θ rate : ℝ}
    (hθ : θ ≤ A) (hExp : Real.exp (A + 1) ≤ rate) :
    ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) ≤
      ENNReal.ofReal (pathLaplaceFactor A rate) := by
  have hlog : A + 1 ≤ Real.log rate := by
    calc
      A + 1 = Real.log (Real.exp (A + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _) hExp
  have hdenA : 0 < Real.log rate - A := by linarith
  have hdenθ : 0 < Real.log rate - θ := by linarith
  have hdenle : Real.log rate - A ≤ Real.log rate - θ := by linarith
  have hinv : (Real.log rate - θ)⁻¹ ≤ (Real.log rate - A)⁻¹ :=
    (inv_le_inv₀ hdenθ hdenA).mpr hdenle
  apply ENNReal.ofReal_le_ofReal
  unfold pathLaplaceFactor
  have hM : 1 ≤ max integratedPotentialRowConstant.toReal 1 := le_max_right _ _
  calc
    4 * Real.pi * (Real.log rate - θ)⁻¹ =
        (1 : ℝ) * (4 * Real.pi) * (Real.log rate - θ)⁻¹ := by ring
    _ ≤ max integratedPotentialRowConstant.toReal 1 *
          (4 * Real.pi) * (Real.log rate - θ)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hM (by positivity)) (by positivity)
    _ ≤ max integratedPotentialRowConstant.toReal 1 *
          (4 * Real.pi) * (Real.log rate - A)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)

private theorem formBound_laplace_pathTimeKernel_coarse {n : ℕ}
    (A θ rate : ℝ) (hθ : θ ≤ A)
    (hExp : Real.exp (A + 1) ≤ rate) (hrateOne : 1 ≤ rate)
    (α₀ : CollisionPair n)
    (w : List (CollisionPair n))
    (hchain : (α₀ :: w).IsChain (· ≠ ·)) :
    FormBound volume volume
      (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α₀) id))
      (ENNReal.ofReal (pathLaplaceFactor A rate ^ w.length)) := by
  have hrate : 0 < rate := (Real.exp_pos _).trans_le hExp
  have hlog : A + 1 ≤ Real.log rate := by
    calc
      A + 1 = Real.log (Real.exp (A + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _) hExp
  have hdenA : 0 < Real.log rate - A := by linarith
  have hdenθ : 0 < Real.log rate - θ := by linarith
  have hdenle : Real.log rate - A ≤ Real.log rate - θ := by linarith
  have hinv : (Real.log rate - θ)⁻¹ ≤ (Real.log rate - A)⁻¹ :=
    (inv_le_inv₀ hdenθ hdenA).mpr hdenle
  have hPtop : integratedPotentialRowConstant ≠ ⊤ :=
    integratedPotentialRowConstant_ne_top
  have hP : integratedPotentialRowConstant =
      ENNReal.ofReal integratedPotentialRowConstant.toReal := by
    exact (ENNReal.ofReal_toReal hPtop).symm
  have hbase : integratedPotentialRowConstant *
      ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) ≤
      ENNReal.ofReal (pathLaplaceFactor A rate) := by
    rw [hP, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    apply ENNReal.ofReal_le_ofReal
    unfold pathLaplaceFactor
    have hPM : integratedPotentialRowConstant.toReal ≤
        max integratedPotentialRowConstant.toReal 1 := le_max_left _ _
    have hcoeff : integratedPotentialRowConstant.toReal * (4 * Real.pi) ≤
        max integratedPotentialRowConstant.toReal 1 * (4 * Real.pi) :=
      mul_le_mul_of_nonneg_right hPM (by positivity)
    calc
      integratedPotentialRowConstant.toReal *
          (4 * Real.pi * (Real.log rate - θ)⁻¹) =
        (integratedPotentialRowConstant.toReal * (4 * Real.pi)) *
          (Real.log rate - θ)⁻¹ := by ring
      _ ≤ (max integratedPotentialRowConstant.toReal 1 * (4 * Real.pi)) *
          (Real.log rate - θ)⁻¹ :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ (max integratedPotentialRowConstant.toReal 1 * (4 * Real.pi)) *
          (Real.log rate - A)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = max integratedPotentialRowConstant.toReal 1 * (4 * Real.pi) *
          (Real.log rate - A)⁻¹ := by ring
  have hsqrt : 1 ≤ Real.sqrt rate := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hrateOne
  have hinvsqrt : (Real.sqrt rate)⁻¹ ≤ 1 :=
    (inv_le_one₀ (Real.sqrt_pos.2 hrate)).2 hsqrt
  have hendpoint : ENNReal.ofReal ((Real.sqrt rate)⁻¹) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact hinvsqrt
  have hbasepow :
      (integratedPotentialRowConstant *
        ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) ^ w.length ≤
      ENNReal.ofReal (pathLaplaceFactor A rate) ^ w.length :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hfactor :
      (integratedPotentialRowConstant *
        ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) ^ w.length *
          ENNReal.ofReal ((Real.sqrt rate)⁻¹) ≤
        ENNReal.ofReal (pathLaplaceFactor A rate ^ w.length) := by
    calc
      _ ≤ ENNReal.ofReal (pathLaplaceFactor A rate) ^ w.length * 1 :=
        mul_le_mul' hbasepow hendpoint
      _ = ENNReal.ofReal (pathLaplaceFactor A rate ^ w.length) := by
        rw [← ENNReal.ofReal_pow (pathLaplaceFactor_pos hExp).le]
        simp
  have hD1 := formBound_laplace_pathTimeKernel (rate := rate) θ hrateOne
    (by linarith) α₀ w hchain
  exact hD1.mono (fun _ _ => le_rfl) hfactor

private theorem rpow_div_nat_neg {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (n : ℕ) :
    (τ / a) ^ (-(n : ℝ)) = a ^ n * τ ^ (-(n : ℝ)) := by
  rw [Real.div_rpow hτ.le ha.le, Real.rpow_neg hτ.le, Real.rpow_neg ha.le,
    Real.rpow_natCast, Real.rpow_natCast]
  field_simp

private theorem exists_formBound_fusedPathDominatingKernel (n : ℕ) (A : ℝ) :
    ∃ C c rate₀ : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (A + 1) ≤ rate₀ ∧
      ∀ θ : ℝ, θ ≤ A → ∀ rate : ℝ, rate₀ ≤ rate →
        ∀ β : CollisionPair n, ∀ w : List (CollisionPair n),
          (β :: w).IsChain (· ≠ ·) →
          ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ 1 →
            FormBound volume volume
              (pathDominatingKernel θ rate w (collisionEmbedding β) τ₀)
              (ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ)) *
                (c / (Real.log rate - A)) ^ (w.length - 1))) := by
  obtain ⟨Cfree, hCfree, hFree⟩ := exists_formBound_sup_free n
  obtain ⟨Ccollision, rateCollision, hCcollision, hCollision⟩ :=
    exists_formBound_sup_collision n A
  let P : ℝ := integratedPotentialRowConstant.toReal
  let M : ℝ := max P 1
  let q : ℝ := M * (4 * Real.pi)
  let K : ℝ := 3 * M * q * (4 : ℝ) ^ n
  let c : ℝ := K + q + 1
  let C : ℝ := 3 * (Cfree * (2 : ℝ) ^ n +
    M * Ccollision * (4 : ℝ) ^ n + 1)
  let rate₀ : ℝ := max rateCollision (max 1 (Real.exp (A + K + 1)))
  have hPnonneg : 0 ≤ P := by dsimp [P]; exact ENNReal.toReal_nonneg
  have hPpos : 0 < P := by
    dsimp [P]
    exact ENNReal.toReal_pos integratedPotentialRowConstant_pos.ne'
      integratedPotentialRowConstant_ne_top
  have hPtop : integratedPotentialRowConstant ≠ ⊤ :=
    integratedPotentialRowConstant_ne_top
  have hPENN : integratedPotentialRowConstant = ENNReal.ofReal P := by
    dsimp [P]
    exact (ENNReal.ofReal_toReal hPtop).symm
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMone : 1 ≤ M := le_max_right _ _
  have hPM : P ≤ M := le_max_left _ _
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hcpos : 0 < c := by dsimp [c]; linarith
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hcq : q ≤ c := by dsimp [c]; linarith
  have hcTail : 3 * M * q * (4 : ℝ) ^ n ≤ c := by
    dsimp [c, K]
    linarith
  have hRate₀exp : Real.exp (A + 1) ≤ rate₀ := by
    dsimp [rate₀]
    apply le_trans ?_ (le_max_of_le_right (le_max_of_le_right le_rfl))
    exact Real.exp_le_exp.mpr (by linarith [hKpos])
  refine ⟨C, c, rate₀, hCpos, hcpos, hRate₀exp, ?_⟩
  intro θ hθ rate hrate β w
  have hrate₀one : 1 ≤ rate₀ := by
    dsimp [rate₀]
    exact le_max_of_le_right (le_max_of_le_left le_rfl)
  have hrateOne : 1 ≤ rate := hrate₀one.trans hrate
  have hRate₀ExpStrong : Real.exp (A + K + 1) ≤ rate₀ := by
    dsimp [rate₀]
    exact le_max_of_le_right (le_max_of_le_right le_rfl)
  have hRateExpStrong : Real.exp (A + K + 1) ≤ rate :=
    hRate₀ExpStrong.trans hrate
  have hExp : Real.exp (A + 1) ≤ rate := hRate₀exp.trans hrate
  have hlog : A + 1 ≤ Real.log rate := by
    calc
      A + 1 = Real.log (Real.exp (A + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _)
        hExp
  have hlogStrong : A + K + 1 ≤ Real.log rate := by
    calc
      A + K + 1 = Real.log (Real.exp (A + K + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _) hRateExpStrong
  have hgap : 0 < Real.log rate - A := by linarith
  have hgapStrong : K + 1 ≤ Real.log rate - A := by linarith
  have hδpos : 0 < pathLaplaceFactor A rate :=
    pathLaplaceFactor_pos hExp
  have hδsmall : pathLaplaceFactor A rate ≤
      1 / (3 * M * (4 : ℝ) ^ n) := by
    rw [show pathLaplaceFactor A rate = q / (Real.log rate - A) by
      simp [pathLaplaceFactor, q, M, P]
      ring]
    rw [div_le_div_iff₀ hgap (by positivity)]
    calc
      q * (3 * M * (4 : ℝ) ^ n) = K := by dsimp [K]; ring
      _ ≤ K + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ 1 * (Real.log rate - A) := by simpa only [one_mul] using hgapStrong
  have hδleOne : pathLaplaceFactor A rate ≤ 1 := by
    have hden : 1 ≤ 3 * M * (4 : ℝ) ^ n := by
      have hpow4 : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hMone) hpow4
    calc
      pathLaplaceFactor A rate ≤ 1 / (3 * M * (4 : ℝ) ^ n) := hδsmall
      _ ≤ 1 := (div_le_one (by positivity)).2 hden
  have htargetPos : 0 < c / (Real.log rate - A) := div_pos hcpos hgap
  have hδleTarget : pathLaplaceFactor A rate ≤ c / (Real.log rate - A) := by
    change q * (Real.log rate - A)⁻¹ ≤ c * (Real.log rate - A)⁻¹
    exact mul_le_mul_of_nonneg_right hcq (inv_nonneg.mpr hgap.le)
  have hδPow (k : ℕ) :
      pathLaplaceFactor A rate ^ k ≤
        (c / (Real.log rate - A)) ^ k :=
    pow_le_pow_left₀ hδpos.le hδleTarget k
  have hδStepPow (k : ℕ) :
      pathLaplaceFactor A rate ^ (k + 1) ≤
        (c / (Real.log rate - A)) ^ k := by
    rw [pow_succ]
    calc
      pathLaplaceFactor A rate ^ k * pathLaplaceFactor A rate ≤
          (c / (Real.log rate - A)) ^ k * 1 :=
        mul_le_mul (hδPow k) hδleOne (by positivity) (by positivity)
      _ = _ := by rw [mul_one]
  have hscale2 {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
      (τ₀ / 2) ^ (-(n : ℝ)) =
        (2 : ℝ) ^ n * τ₀ ^ (-(n : ℝ)) :=
    rpow_div_nat_neg (by norm_num) hτ₀ n
  have hscale4 {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
      (τ₀ / 4) ^ (-(n : ℝ)) =
        (4 : ℝ) ^ n * τ₀ ^ (-(n : ℝ)) :=
    rpow_div_nat_neg (by norm_num) hτ₀ n
  have hCabsorb :
      Cfree * (2 : ℝ) ^ n + M * Ccollision * (4 : ℝ) ^ n ≤ C / 3 := by
    dsimp [C]
    linarith only []
  have hCsPart : Cfree * (2 : ℝ) ^ n ≤ C / 3 := by
    have hnonneg : 0 ≤ M * Ccollision * (4 : ℝ) ^ n := by positivity
    linarith
  have hCcPart : M * Ccollision * (4 : ℝ) ^ n ≤ C / 3 := by
    have hnonneg : 0 ≤ Cfree * (2 : ℝ) ^ n := by positivity
    linarith
  induction w generalizing β with
  | nil =>
      intro hchain τ₀ hτ₀ hτ₀le
      have hbase := (hFree rate hrateOne τ₀ hτ₀ hτ₀le).2.1 β
      have hpow2 : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hCfreeC : Cfree ≤ C := by
        calc
          Cfree = Cfree * 1 := (mul_one _).symm
          _ ≤ Cfree * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left hpow2 hCfree.le
          _ ≤ C / 3 := hCsPart
          _ ≤ C := div_le_self hCpos.le (by norm_num)
      have hconst :
          ENNReal.ofReal (Cfree * τ₀ ^ (-(n : ℝ))) ≤
            ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hCfreeC (by positivity)
      have hbound := hbase.mono (fun _ _ => le_rfl) hconst
      simpa [pathDominatingKernel] using hbound
  | cons γ v ih =>
      intro hchain τ₀ hτ₀ hτ₀le
      rw [List.isChain_cons_cons] at hchain
      rcases hchain with ⟨hne, hrest⟩
      let I : TimeKernel (FusedConfiguration β) (FusedConfiguration γ) :=
        freeTimeKernel (collisionEmbedding β) (collisionEmbedding γ)
      let J : TimeKernel (FusedConfiguration γ) (FusedConfiguration γ) :=
        collisionTimeKernel γ θ
      let T : TimeKernel (FusedConfiguration γ) (Configuration n) :=
        pathTimeKernel θ v (collisionEmbedding γ) id
      let Q : TimeKernel (FusedConfiguration γ) (Configuration n) :=
        timeKernelComp volume (causalKernel J) T
      let Tail : FusedConfiguration γ → Configuration n → ℝ≥0∞ :=
        pathDominatingKernel θ rate v (collisionEmbedding γ) (τ₀ / 4)
      let Inner : FusedConfiguration γ → Configuration n → ℝ≥0∞ := fun z y =>
        spatialKernelComp volume (supTimeKernel rate (τ₀ / 4) J)
          (laplaceTimeKernel rate T) z y +
        spatialKernelComp volume (laplaceTimeKernel rate J) Tail z y
      let factor : ℝ := pathLaplaceFactor A rate
      let targetFactor : ℝ := c / (Real.log rate - A)
      let tauPow : ℝ := τ₀ ^ (-(n : ℝ))
      let d : ℝ≥0∞ := ENNReal.ofReal factor
      have hfactorPos : 0 < factor := by exact hδpos
      have htargetFactorPos : 0 < targetFactor := htargetPos
      have hfactorle : factor ≤ targetFactor := hδleTarget
      have hfactorpow (k : ℕ) :
          factor ^ k ≤ targetFactor ^ k := by
        exact pow_le_pow_left₀ hfactorPos.le hfactorle k
      have hfactorstep (k : ℕ) :
          factor ^ (k + 1) ≤ targetFactor ^ k := by
        simpa [factor, targetFactor] using hδStepPow k
      have hfactorone : factor ≤ 1 := by simpa [factor] using hδleOne
      have hDpow (k : ℕ) : d ^ k = ENNReal.ofReal (factor ^ k) := by
        exact (ENNReal.ofReal_pow hfactorPos.le k).symm
      have hI : Measurable I :=
        measurable_freeTimeKernel (measurable_collisionEmbedding β)
          (measurable_collisionEmbedding γ)
      have hJ : Measurable J := measurable_collisionTimeKernel γ θ
      have hT : Measurable T :=
        measurable_pathTimeKernel θ v (measurable_collisionEmbedding γ) measurable_id
      have hQ : Measurable Q :=
        measurable_timeKernelComp volume (measurable_causalKernel hJ) hT
      have hSupI : Measurable (Function.uncurry
          (supTimeKernel rate (τ₀ / 2) I)) :=
        measurable_supTimeKernel (K := I) hI
          (fun (x : FusedConfiguration β) (y : FusedConfiguration γ) => by
            simpa only [I] using
              continuousOn_freeTimeKernel_time
                (eX := collisionEmbedding β) (eY := collisionEmbedding γ) x y)
          rate (by positivity)
      have hSupJ : Measurable (Function.uncurry
          (supTimeKernel rate (τ₀ / 4) J)) :=
        measurable_supTimeKernel (K := J) hJ
          (fun x y => by
            simpa only [J] using continuousOn_collisionTimeKernel_time γ θ x y)
          rate (by positivity)
      have hLapI : Measurable (Function.uncurry (laplaceTimeKernel rate I)) :=
        measurable_laplaceTimeKernel rate hI
      have hLapJ : Measurable (Function.uncurry (laplaceTimeKernel rate J)) :=
        measurable_laplaceTimeKernel rate hJ
      have hLapT : Measurable (Function.uncurry (laplaceTimeKernel rate T)) :=
        measurable_laplaceTimeKernel rate hT
      have hLapQ : Measurable (Function.uncurry (laplaceTimeKernel rate Q)) :=
        measurable_laplaceTimeKernel rate hQ
      have hTail : Measurable (Function.uncurry Tail) :=
        measurable_pathDominatingKernel θ rate v
          (measurable_collisionEmbedding γ) (by positivity)
      have hSupJComp : Measurable (Function.uncurry
          (spatialKernelComp volume (supTimeKernel rate (τ₀ / 4) J)
            (laplaceTimeKernel rate T))) :=
        measurable_spatialKernelComp volume hSupJ hLapT
      have hLapJComp : Measurable (Function.uncurry
          (spatialKernelComp volume (laplaceTimeKernel rate J) Tail)) :=
        measurable_spatialKernelComp volume hLapJ hTail
      have hInner : Measurable (Function.uncurry Inner) :=
        hSupJComp.add hLapJComp
      have hFirstComp : Measurable (Function.uncurry
          (spatialKernelComp volume (supTimeKernel rate (τ₀ / 2) I)
            (laplaceTimeKernel rate Q))) :=
        measurable_spatialKernelComp volume hSupI hLapQ
      have hSecondComp : Measurable (Function.uncurry
          (spatialKernelComp volume (laplaceTimeKernel rate I) Inner)) :=
        measurable_spatialKernelComp volume hLapI hInner

      have hPathLapRaw := formBound_laplace_pathTimeKernel_coarse A θ rate hθ
        hExp hrateOne γ v hrest
      have hPathLap : FormBound volume volume (laplaceTimeKernel rate T)
          (ENNReal.ofReal (factor ^ v.length)) := by
        simpa [T, factor] using hPathLapRaw
      have hθlog : θ < Real.log rate := by linarith
      have hLapCollisionRaw := formBound_laplace_collision γ
        (rate := rate) (by linarith) hθlog
      have hLapCollisionLe := laplaceCollision_le_pathLaplaceFactor hθ hExp
      have hLapCollision : FormBound volume volume (laplaceTimeKernel rate J) d := by
        have h := hLapCollisionRaw.mono (fun _ _ => le_rfl) hLapCollisionLe
        simpa [J, d, factor] using h
      have hTcausal : causalKernel T = T :=
        pathTimeKernel_causal θ v (collisionEmbedding γ) id
      have hQeq : ∀ x y, laplaceTimeKernel rate Q x y =
          spatialKernelComp volume (laplaceTimeKernel rate J)
            (laplaceTimeKernel rate T) x y := by
        intro x y
        simpa [Q, hTcausal] using
          laplaceTimeKernel_timeKernelComp_causal volume hJ hT rate x y
      have hQraw := FormBound.comp volume volume volume hLapJ hLapT
        hLapCollision hPathLap
      have hQconst :
          d * ENNReal.ofReal (factor ^ v.length) =
            ENNReal.ofReal (factor ^ (v.length + 1)) := by
        calc
          d * ENNReal.ofReal (factor ^ v.length) =
              ENNReal.ofReal (factor * factor ^ v.length) := by
                simpa [d] using
                  (ENNReal.ofReal_mul hfactorPos.le).symm
          _ = ENNReal.ofReal (factor ^ (v.length + 1)) := by
                congr 1
                rw [pow_succ]
                ring
      have hQbound : FormBound volume volume (laplaceTimeKernel rate Q)
          (ENNReal.ofReal (factor ^ (v.length + 1))) :=
        hQraw.mono (fun x y => (hQeq x y).le) hQconst.le

      have hSupIForm : FormBound volume volume
          (supTimeKernel rate (τ₀ / 2) I)
          (ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ)))) :=
        (hFree rate hrateOne (τ₀ / 2) (by positivity) (by linarith)).2.2 β γ
      have hSupJForm : FormBound volume volume
          (supTimeKernel rate (τ₀ / 4) J)
          (ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)))) :=
        hCollision θ hθ rate (le_trans (le_max_left _ _) hrate)
          (τ₀ / 4) (by positivity) (by linarith) γ
      have hLapIForm : FormBound volume volume (laplaceTimeKernel rate I)
          integratedPotentialRowConstant :=
        formBound_laplace_swapping β γ hne (by linarith)

      have hFirstRaw := FormBound.comp volume volume volume hSupI hLapQ
        hSupIForm hQbound
      have hTermSupRaw := FormBound.comp volume volume volume hSupJ hLapT
        hSupJForm hPathLap
      have hTailForm := ih γ hrest (τ₀ / 4) (by positivity) (by linarith)
      have hTermTailRaw := FormBound.comp volume volume volume hLapJ hTail
        hLapCollision hTailForm
      have hInnerForm := FormBound.add hSupJComp hLapJComp hTermSupRaw hTermTailRaw
      have hSecondRaw := FormBound.comp volume volume volume hLapI hInner
        hLapIForm hInnerForm
      have hTotalRaw := FormBound.add hFirstComp hSecondComp hFirstRaw hSecondRaw

      have hFirstConst :
          ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
            ENNReal.ofReal (factor ^ (v.length + 1)) =
          ENNReal.ofReal
            (Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have hTermSupConst :
          ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
            ENNReal.ofReal (factor ^ v.length) =
          ENNReal.ofReal
            (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have hTermTailConst :
          d * ENNReal.ofReal
              (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1)) =
            ENNReal.ofReal
              (factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1))) := by
        simpa [d] using
          (ENNReal.ofReal_mul hfactorPos.le).symm
      have hInnerConst :
          (ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ v.length)) +
            d * ENNReal.ofReal
              (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1)) =
          ENNReal.ofReal
            (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
              factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1))) := by
        rw [hTermSupConst, hTermTailConst,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hTotalConstEq :
          (ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ (v.length + 1))) +
            integratedPotentialRowConstant *
              ((ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
                  ENNReal.ofReal (factor ^ v.length)) +
                d * ENNReal.ofReal
                  (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                    targetFactor ^ (v.length - 1))) =
          ENNReal.ofReal
            (Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) +
              P * (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
                factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                  targetFactor ^ (v.length - 1)))) := by
        rw [hPENN, hFirstConst, hInnerConst,
          ← ENNReal.ofReal_mul hPnonneg,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

      have hTauNonneg : 0 ≤ tauPow := by positivity
      have hTargetPowNonneg (k : ℕ) : 0 ≤ targetFactor ^ k :=
        pow_nonneg (le_of_lt htargetFactorPos) k
      have hFirstRealLe :
          Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) ≤
            (C / 3) * tauPow * targetFactor ^ v.length := by
        rw [hscale2 hτ₀]
        calc
          Cfree * ((2 : ℝ) ^ n * tauPow) * factor ^ (v.length + 1) =
              Cfree * (2 : ℝ) ^ n * tauPow * factor ^ (v.length + 1) := by ring
          _ ≤ Cfree * (2 : ℝ) ^ n * tauPow * targetFactor ^ v.length :=
                mul_le_mul_of_nonneg_left (hfactorstep v.length) (by positivity)
          _ ≤ (C / 3) * tauPow * targetFactor ^ v.length := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hCsPart hTauNonneg)
                  (hTargetPowNonneg _)
      have hInnerSupRealLe :
          P * (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length) ≤
            (C / 3) *
              tauPow * targetFactor ^ v.length := by
        rw [hscale4 hτ₀]
        have hPcoll : P * Ccollision ≤ M * Ccollision :=
          mul_le_mul_of_nonneg_right hPM hCcollision.le
        have hPcoll4 : P * Ccollision * (4 : ℝ) ^ n ≤
            M * Ccollision * (4 : ℝ) ^ n := by
          calc
            P * Ccollision * (4 : ℝ) ^ n = (P * Ccollision) * (4 : ℝ) ^ n := by ring
            _ ≤ (M * Ccollision) * (4 : ℝ) ^ n :=
              mul_le_mul_of_nonneg_right hPcoll (by positivity)
            _ = M * Ccollision * (4 : ℝ) ^ n := by ring
        have hPcoll4τ : P * Ccollision * (4 : ℝ) ^ n * tauPow ≤
            M * Ccollision * (4 : ℝ) ^ n * tauPow :=
          mul_le_mul_of_nonneg_right hPcoll4 hTauNonneg
        calc
          P * (Ccollision * ((4 : ℝ) ^ n * tauPow) * factor ^ v.length) =
              (P * Ccollision * (4 : ℝ) ^ n * tauPow) * factor ^ v.length := by ring
          _ ≤ (M * Ccollision * (4 : ℝ) ^ n * tauPow) * factor ^ v.length :=
            mul_le_mul_of_nonneg_right hPcoll4τ (pow_nonneg hfactorPos.le _)
          _ ≤ (M * Ccollision * (4 : ℝ) ^ n * tauPow) * targetFactor ^ v.length :=
            mul_le_mul_of_nonneg_left (hfactorpow v.length) (by positivity)
          _ = M * Ccollision * (4 : ℝ) ^ n * tauPow * targetFactor ^ v.length := by ring
          _ ≤ (C / 3) * tauPow * targetFactor ^ v.length :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCcPart hTauNonneg)
              (hTargetPowNonneg _)
      have hTailRealLe :
          P * factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
            targetFactor ^ (v.length - 1)) ≤
            (C / 3) * tauPow * targetFactor ^ v.length := by
        rw [hscale4 hτ₀]
        by_cases hk : v.length = 0
        · have hv : v = [] := List.length_eq_zero_iff.mp hk
          subst v
          simp only [List.length_nil, Nat.zero_sub, pow_zero, mul_one]
          have hsmall : P * factor * (4 : ℝ) ^ n ≤ 1 / 3 := by
            calc
              P * factor * (4 : ℝ) ^ n ≤ M * factor * (4 : ℝ) ^ n :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hPM hfactorPos.le) (by positivity)
              _ = factor * (M * (4 : ℝ) ^ n) := by ring
              _ ≤ (1 / (3 * M * (4 : ℝ) ^ n)) * (M * (4 : ℝ) ^ n) :=
                mul_le_mul_of_nonneg_right hδsmall (by positivity)
              _ = 1 / 3 := by
                have hM4 : M * (4 : ℝ) ^ n ≠ 0 :=
                  ne_of_gt (mul_pos hMpos (by positivity))
                field_simp [hM4]
          calc
            P * factor * (C * ((4 : ℝ) ^ n * tauPow)) =
                (P * factor * (4 : ℝ) ^ n) * C * tauPow := by ring
            _ ≤
                (1 / 3) * C * tauPow :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hsmall (by positivity))
                hTauNonneg
            _ = (C / 3) * tauPow := by ring
        · have hkpos : 0 < v.length := Nat.pos_of_ne_zero hk
          have hratio : P * factor * (4 : ℝ) ^ n ≤ targetFactor / 3 := by
            have hcoeff : P * q * (4 : ℝ) ^ n ≤ c / 3 := by
              calc
                P * q * (4 : ℝ) ^ n ≤ M * q * (4 : ℝ) ^ n :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hPM hqpos.le) (by positivity)
                _ ≤ c / 3 := by
                  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
                  calc
                    M * q * (4 : ℝ) ^ n * 3 = 3 * M * q * (4 : ℝ) ^ n := by ring
                    _ ≤ c := hcTail
            calc
              P * factor * (4 : ℝ) ^ n =
                  (P * q * (4 : ℝ) ^ n) * (Real.log rate - A)⁻¹ := by
                    simp [factor, pathLaplaceFactor, q]
                    ring
              _ ≤ (c / 3) * (Real.log rate - A)⁻¹ :=
                mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr hgap.le)
              _ = targetFactor / 3 := by
                dsimp [targetFactor]
                ring
          have hpow : targetFactor ^ (v.length - 1) * targetFactor =
              targetFactor ^ v.length := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
          calc
            P * factor * (C * ((4 : ℝ) ^ n * tauPow) *
                targetFactor ^ (v.length - 1)) =
              C * tauPow * (P * factor * (4 : ℝ) ^ n * targetFactor ^ (v.length - 1)) := by ring
            _ =
                C * tauPow *
                  (P * factor * (4 : ℝ) ^ n * targetFactor ^ (v.length - 1)) := rfl
            _ ≤ C * tauPow *
                ((targetFactor / 3) * targetFactor ^ (v.length - 1)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hratio
                  (pow_nonneg (le_of_lt htargetFactorPos) _))
                (by positivity)
            _ = (C / 3) * tauPow * targetFactor ^ v.length := by
              calc
                C * tauPow * ((targetFactor / 3) * targetFactor ^ (v.length - 1)) =
                    (C / 3) * tauPow *
                      (targetFactor ^ (v.length - 1) * targetFactor) := by ring
                _ = (C / 3) * tauPow * targetFactor ^ v.length := by rw [hpow]
      have hTotalRealLe :
          Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) +
            P * (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
              factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1))) ≤
            C * tauPow * targetFactor ^ v.length := by
        have hsup := hInnerSupRealLe
        have htail := hTailRealLe
        have hcoeff : C / 3 + C / 3 + C / 3 ≤ C := by
          calc
            C / 3 + C / 3 + C / 3 = C := by ring
            _ ≤ C := le_rfl
        have hX : 0 ≤ tauPow * targetFactor ^ v.length :=
          mul_nonneg hTauNonneg (hTargetPowNonneg _)
        have hsumBound :
            (C / 3) * tauPow * targetFactor ^ v.length +
              (C / 3) * tauPow * targetFactor ^ v.length +
              (C / 3) * tauPow * targetFactor ^ v.length ≤
                C * tauPow * targetFactor ^ v.length := by
          calc
            _ = (C / 3 + C / 3 + C / 3) *
                (tauPow * targetFactor ^ v.length) := by ring
            _ ≤ C * (tauPow * targetFactor ^ v.length) :=
              mul_le_mul_of_nonneg_right hcoeff hX
            _ = C * tauPow * targetFactor ^ v.length := by ring
        calc
          Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) +
              P * (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
                factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                  targetFactor ^ (v.length - 1))) ≤
              (C / 3) * tauPow * targetFactor ^ v.length +
                ((C / 3) * tauPow * targetFactor ^ v.length +
                  (C / 3) * tauPow * targetFactor ^ v.length) := by
            apply add_le_add hFirstRealLe
            rw [mul_add]
            apply add_le_add hsup
            calc
              P * (factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                  targetFactor ^ (v.length - 1))) =
                  P * factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                    targetFactor ^ (v.length - 1)) := by ring
              _ ≤ _ := htail
          _ =
              (C / 3) * tauPow * targetFactor ^ v.length +
                (C / 3) * tauPow * targetFactor ^ v.length +
                (C / 3) * tauPow * targetFactor ^ v.length := by ring
          _ ≤ C * tauPow * targetFactor ^ v.length := hsumBound
      have hTotalConst :
          (ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ (v.length + 1))) +
            integratedPotentialRowConstant *
              ((ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
                  ENNReal.ofReal (factor ^ v.length)) +
                d * ENNReal.ofReal
                  (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                    targetFactor ^ (v.length - 1))) ≤
          ENNReal.ofReal (C * tauPow * targetFactor ^ v.length) := by
        rw [hTotalConstEq]
        exact ENNReal.ofReal_le_ofReal hTotalRealLe
      have hTotalForm := FormBound.add hFirstComp hSecondComp hFirstRaw hSecondRaw
      have hTotal := hTotalForm.mono (fun _ _ => le_rfl) hTotalConst
      simpa [pathDominatingKernel, I, J, T, Q, Tail, Inner, factor,
        targetFactor, tauPow, hscale2 hτ₀, hscale4 hτ₀] using hTotal

/-! The form bound on the full configuration space includes the initial incoming block and the remaining path on the fused collision space. -/
/-- For bounded interaction parameters and large Laplace rates, path-dominating kernels obey geometric form bounds. -/
theorem exists_formBound_pathDominatingKernel (n : ℕ) (A : ℝ) :
    ∃ C c rate₀ : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (A + 1) ≤ rate₀ ∧
      ∀ θ : ℝ, θ ≤ A → ∀ rate : ℝ, rate₀ ≤ rate →
        ∀ w : List (CollisionPair n), w ≠ [] → w.IsChain (· ≠ ·) →
          ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ 1 →
            FormBound volume volume (pathDominatingKernel θ rate w id τ₀)
              (ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ)) *
                (c / (Real.log rate - A)) ^ (w.length - 1))) := by
  obtain ⟨Ctail, ctail, rateTail, hCtail, hctail, hRateTailExp, hFused⟩ :=
    exists_formBound_fusedPathDominatingKernel n A
  obtain ⟨Cfree, hCfree, hFree⟩ := exists_formBound_sup_free n
  obtain ⟨Ccollision, rateCollision, hCcollision, hCollision⟩ :=
    exists_formBound_sup_collision n A
  let P : ℝ := integratedPotentialRowConstant.toReal
  let M : ℝ := max P 1
  let q : ℝ := M * (4 * Real.pi)
  let K : ℝ := 3 * M * q * (4 : ℝ) ^ n
  let C : ℝ := Ctail + 3 *
    (Cfree * (2 : ℝ) ^ n + Ccollision * (4 : ℝ) ^ n + 1)
  let c : ℝ := ctail + 3 * q * (4 : ℝ) ^ n + 1
  let rate₀ : ℝ := max (max rateTail rateCollision)
    (max 1 (Real.exp (A + K + 1)))
  have hPnonneg : 0 ≤ P := by dsimp [P]; exact ENNReal.toReal_nonneg
  have hPpos : 0 < P := by
    dsimp [P]
    exact ENNReal.toReal_pos integratedPotentialRowConstant_pos.ne'
      integratedPotentialRowConstant_ne_top
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMone : 1 ≤ M := le_max_right _ _
  have hPM : P ≤ M := le_max_left _ _
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hRateTail : rateTail ≤ rate₀ := by
    dsimp [rate₀]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hRateCollision : rateCollision ≤ rate₀ := by
    dsimp [rate₀]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hRateOne : 1 ≤ rate₀ := by
    dsimp [rate₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hRateStrong : Real.exp (A + K + 1) ≤ rate₀ := by
    dsimp [rate₀]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hRate₀exp : Real.exp (A + 1) ≤ rate₀ :=
    le_trans hRateTailExp hRateTail
  have hCabsorb :
      Cfree * (2 : ℝ) ^ n + Ccollision * (4 : ℝ) ^ n ≤ C / 3 := by
    dsimp [C]
    linarith only [hCtail]
  have hCsPart : Cfree * (2 : ℝ) ^ n ≤ C / 3 := by
    have hnonneg : 0 ≤ Ccollision * (4 : ℝ) ^ n := by positivity
    linarith
  have hCcPart : Ccollision * (4 : ℝ) ^ n ≤ C / 3 := by
    have hnonneg : 0 ≤ Cfree * (2 : ℝ) ^ n := by positivity
    linarith
  have hCtailLe : Ctail ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  have hcTailMass : 3 * q * (4 : ℝ) ^ n ≤ c := by
    dsimp [c]
    have hExtra : 0 ≤ ctail + 1 := by positivity
    linarith
  have hqleC : q ≤ c := by
    have hpow4 : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hnonneg : 0 ≤ ctail := hctail.le
    dsimp [c]
    have hqterm : q ≤ 3 * q * (4 : ℝ) ^ n := by
      calc
        q = q * 1 := (mul_one _).symm
        _ ≤ q * (3 * (4 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left
            (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hpow4) hqpos.le
        _ = _ := by ring
    have hExtra : 0 ≤ ctail + 1 := by positivity
    exact le_trans hqterm (by linarith)
  refine ⟨C, c, rate₀, hCpos, hcpos, hRate₀exp, ?_⟩
  intro θ hθ rate hrate w hwne hwchain τ₀ hτ₀ hτ₀le
  have hrateTail : rateTail ≤ rate := le_trans hRateTail hrate
  have hrateCollision : rateCollision ≤ rate := le_trans hRateCollision hrate
  have hrateOne : 1 ≤ rate := le_trans hRateOne hrate
  have hRateExpStrong : Real.exp (A + K + 1) ≤ rate := le_trans hRateStrong hrate
  have hExp : Real.exp (A + 1) ≤ rate :=
    le_trans hRate₀exp hrate
  have hlogStrong : A + K + 1 ≤ Real.log rate := by
    calc
      A + K + 1 = Real.log (Real.exp (A + K + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _) hRateExpStrong
  have hlog : A + 1 ≤ Real.log rate := by
    calc
      A + 1 = Real.log (Real.exp (A + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _) hExp
  have hgap : 0 < Real.log rate - A := by linarith
  have hgapStrong : K + 1 ≤ Real.log rate - A := by linarith
  have hfactorPos : 0 < pathLaplaceFactor A rate := pathLaplaceFactor_pos hExp
  have hδsmall : pathLaplaceFactor A rate ≤
      1 / (3 * M * (4 : ℝ) ^ n) := by
    rw [show pathLaplaceFactor A rate = q / (Real.log rate - A) by
      simp [pathLaplaceFactor, q, M, P]
      ring]
    rw [div_le_div_iff₀ hgap (by positivity)]
    calc
      q * (3 * M * (4 : ℝ) ^ n) = K := by dsimp [K]; ring
      _ ≤ K + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ 1 * (Real.log rate - A) := by simpa only [one_mul] using hgapStrong
  have hden : 1 ≤ 3 * M * (4 : ℝ) ^ n := by
    have hpow4 : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hMone) hpow4
  have hδleOne : pathLaplaceFactor A rate ≤ 1 := by
    calc
      pathLaplaceFactor A rate ≤ 1 / (3 * M * (4 : ℝ) ^ n) := hδsmall
      _ ≤ 1 := (div_le_one (by positivity)).2 hden
  have htargetPos : 0 < c / (Real.log rate - A) := div_pos hcpos hgap
  have hδleTarget : pathLaplaceFactor A rate ≤ c / (Real.log rate - A) := by
    change q * (Real.log rate - A)⁻¹ ≤ c * (Real.log rate - A)⁻¹
    exact mul_le_mul_of_nonneg_right hqleC (inv_nonneg.mpr hgap.le)
  have hδPow (k : ℕ) :
      pathLaplaceFactor A rate ^ k ≤ (c / (Real.log rate - A)) ^ k :=
    pow_le_pow_left₀ hfactorPos.le hδleTarget k
  have hδStepPow (k : ℕ) :
      pathLaplaceFactor A rate ^ (k + 1) ≤ (c / (Real.log rate - A)) ^ k := by
    rw [pow_succ]
    calc
      pathLaplaceFactor A rate ^ k * pathLaplaceFactor A rate ≤
          (c / (Real.log rate - A)) ^ k * 1 :=
        mul_le_mul (hδPow k) hδleOne (by positivity) (by positivity)
      _ = _ := by rw [mul_one]
  cases w with
  | nil => simp at hwne
  | cons α v =>
      let I : TimeKernel (Configuration n) (FusedConfiguration α) :=
        freeTimeKernel id (collisionEmbedding α)
      let J : TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
        collisionTimeKernel α θ
      let T : TimeKernel (FusedConfiguration α) (Configuration n) :=
        pathTimeKernel θ v (collisionEmbedding α) id
      let Q : TimeKernel (FusedConfiguration α) (Configuration n) :=
        timeKernelComp volume (causalKernel J) T
      let Tail : FusedConfiguration α → Configuration n → ℝ≥0∞ :=
        pathDominatingKernel θ rate v (collisionEmbedding α) (τ₀ / 4)
      let Inner : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z y =>
        spatialKernelComp volume (supTimeKernel rate (τ₀ / 4) J)
          (laplaceTimeKernel rate T) z y +
        spatialKernelComp volume (laplaceTimeKernel rate J) Tail z y
      let factor : ℝ := pathLaplaceFactor A rate
      let targetFactor : ℝ := c / (Real.log rate - A)
      let tauPow : ℝ := τ₀ ^ (-(n : ℝ))
      let d : ℝ≥0∞ := ENNReal.ofReal factor
      have hfactorle : factor ≤ targetFactor := hδleTarget
      have hfactorpow (k : ℕ) : factor ^ k ≤ targetFactor ^ k :=
        pow_le_pow_left₀ hfactorPos.le hfactorle k
      have hfactorstep (k : ℕ) : factor ^ (k + 1) ≤ targetFactor ^ k := by
        simpa [factor, targetFactor] using hδStepPow k
      have hI : Measurable I :=
        measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α)
      have hJ : Measurable J := measurable_collisionTimeKernel α θ
      have hT : Measurable T :=
        measurable_pathTimeKernel θ v (measurable_collisionEmbedding α) measurable_id
      have hQ : Measurable Q :=
        measurable_timeKernelComp volume (measurable_causalKernel hJ) hT
      have hSupI : Measurable (Function.uncurry
          (supTimeKernel rate (τ₀ / 2) I)) :=
        measurable_supTimeKernel (K := I) hI
          (fun (x : Configuration n) (y : FusedConfiguration α) => by
            simpa only [I] using
              continuousOn_freeTimeKernel_time
                (eX := id) (eY := collisionEmbedding α) x y)
          rate (by positivity)
      have hSupJ : Measurable (Function.uncurry
          (supTimeKernel rate (τ₀ / 4) J)) :=
        measurable_supTimeKernel (K := J) hJ
          (fun x y => by
            simpa only [J] using continuousOn_collisionTimeKernel_time α θ x y)
          rate (by positivity)
      have hLapI : Measurable (Function.uncurry (laplaceTimeKernel rate I)) :=
        measurable_laplaceTimeKernel rate hI
      have hLapJ : Measurable (Function.uncurry (laplaceTimeKernel rate J)) :=
        measurable_laplaceTimeKernel rate hJ
      have hLapT : Measurable (Function.uncurry (laplaceTimeKernel rate T)) :=
        measurable_laplaceTimeKernel rate hT
      have hLapQ : Measurable (Function.uncurry (laplaceTimeKernel rate Q)) :=
        measurable_laplaceTimeKernel rate hQ
      have hTail : Measurable (Function.uncurry Tail) :=
        measurable_pathDominatingKernel θ rate v
          (measurable_collisionEmbedding α) (by positivity)
      have hSupJComp : Measurable (Function.uncurry
          (spatialKernelComp volume (supTimeKernel rate (τ₀ / 4) J)
            (laplaceTimeKernel rate T))) :=
        measurable_spatialKernelComp volume hSupJ hLapT
      have hLapJComp : Measurable (Function.uncurry
          (spatialKernelComp volume (laplaceTimeKernel rate J) Tail)) :=
        measurable_spatialKernelComp volume hLapJ hTail
      have hInnerMeas : Measurable (Function.uncurry Inner) := hSupJComp.add hLapJComp
      have hFirstComp : Measurable (Function.uncurry
          (spatialKernelComp volume (supTimeKernel rate (τ₀ / 2) I)
            (laplaceTimeKernel rate Q))) :=
        measurable_spatialKernelComp volume hSupI hLapQ
      have hSecondComp : Measurable (Function.uncurry
          (spatialKernelComp volume (laplaceTimeKernel rate I) Inner)) :=
        measurable_spatialKernelComp volume hLapI hInnerMeas
      have hPathLapRaw := formBound_laplace_pathTimeKernel_coarse A θ rate hθ
        hExp hrateOne α v hwchain
      have hPathLap : FormBound volume volume (laplaceTimeKernel rate T)
          (ENNReal.ofReal (factor ^ v.length)) := by
        simpa [T, factor] using hPathLapRaw
      have hθlog : θ < Real.log rate := by linarith
      have hLapJRaw := formBound_laplace_collision α
        (rate := rate) (by linarith) hθlog
      have hLapJLe := laplaceCollision_le_pathLaplaceFactor hθ hExp
      have hLapJForm : FormBound volume volume (laplaceTimeKernel rate J) d := by
        have h := hLapJRaw.mono (fun _ _ => le_rfl) hLapJLe
        simpa [J, d, factor] using h
      have hLapIRaw := formBound_laplace_incoming (rate := rate) α (by linarith)
      have hsqrt : 1 ≤ Real.sqrt rate := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hrateOne
      have hinvsqrt : (Real.sqrt rate)⁻¹ ≤ 1 :=
        (inv_le_one₀ (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hrateOne))).2 hsqrt
      have hLapIConst : ENNReal.ofReal ((Real.sqrt rate)⁻¹) ≤ 1 := by
        rw [ENNReal.ofReal_le_one]
        exact hinvsqrt
      have hLapIForm : FormBound volume volume (laplaceTimeKernel rate I) 1 :=
        hLapIRaw.mono (fun _ _ => le_rfl) hLapIConst
      have hSupIForm : FormBound volume volume
          (supTimeKernel rate (τ₀ / 2) I)
          (ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ)))) :=
        (hFree rate hrateOne (τ₀ / 2) (by positivity) (by linarith)).1 α
      have hSupJForm : FormBound volume volume
          (supTimeKernel rate (τ₀ / 4) J)
          (ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)))) :=
        hCollision θ hθ rate hrateCollision (τ₀ / 4)
          (by positivity) (by linarith) α
      have hTailRaw := hFused θ hθ rate hrateTail α v hwchain
        (τ₀ / 4) (by positivity) (by linarith)
      have hCtailScale : Ctail * (τ₀ / 4) ^ (-(n : ℝ)) ≤
          C * (τ₀ / 4) ^ (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_right hCtailLe (by positivity)
      have hcTailLe : ctail ≤ c := by
        dsimp [c]
        have hExtra : 0 ≤ 3 * q * (4 : ℝ) ^ n + 1 := by positivity
        linarith
      have htargetTailLe : ctail / (Real.log rate - A) ≤ targetFactor := by
        exact div_le_div_of_nonneg_right hcTailLe hgap.le
      have htargetTailPos : 0 < ctail / (Real.log rate - A) :=
        div_pos hctail hgap
      have hTailConst : ENNReal.ofReal
          (Ctail * (τ₀ / 4) ^ (-(n : ℝ)) *
            (ctail / (Real.log rate - A)) ^ (v.length - 1)) ≤
          ENNReal.ofReal
            (C * (τ₀ / 4) ^ (-(n : ℝ)) * targetFactor ^ (v.length - 1)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          Ctail * (τ₀ / 4) ^ (-(n : ℝ)) *
              (ctail / (Real.log rate - A)) ^ (v.length - 1) ≤
              C * (τ₀ / 4) ^ (-(n : ℝ)) *
                (ctail / (Real.log rate - A)) ^ (v.length - 1) :=
            mul_le_mul_of_nonneg_right hCtailScale
              (pow_nonneg (le_of_lt htargetTailPos) _)
          _ ≤ C * (τ₀ / 4) ^ (-(n : ℝ)) * targetFactor ^ (v.length - 1) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ htargetTailPos.le htargetTailLe _)
              (by positivity)
      have hTailForm : FormBound volume volume Tail
          (ENNReal.ofReal (C * (τ₀ / 4) ^ (-(n : ℝ)) *
            targetFactor ^ (v.length - 1))) := by
        exact hTailRaw.mono (fun _ _ => le_rfl) hTailConst
      let factorENN : ℝ≥0∞ := ENNReal.ofReal factor
      have hQeq : ∀ x y, laplaceTimeKernel rate Q x y =
          spatialKernelComp volume (laplaceTimeKernel rate J)
            (laplaceTimeKernel rate T) x y := by
        have hTcausal : causalKernel T = T :=
          pathTimeKernel_causal θ v (collisionEmbedding α) id
        intro x y
        simpa [Q, hTcausal] using
          laplaceTimeKernel_timeKernelComp_causal volume hJ hT rate x y
      have hQraw := FormBound.comp volume volume volume hLapJ hLapT
        hLapJForm hPathLap
      have hQconst :
          factorENN * ENNReal.ofReal (factor ^ v.length) =
            ENNReal.ofReal (factor ^ (v.length + 1)) := by
        calc
          factorENN * ENNReal.ofReal (factor ^ v.length) =
              ENNReal.ofReal (factor * factor ^ v.length) := by
                simpa [factorENN] using
                  (ENNReal.ofReal_mul hfactorPos.le).symm
          _ = ENNReal.ofReal (factor ^ (v.length + 1)) := by
                congr 1
                rw [pow_succ]
                ring
      have hQbound : FormBound volume volume (laplaceTimeKernel rate Q)
          (ENNReal.ofReal (factor ^ (v.length + 1))) :=
        hQraw.mono (fun x y => (hQeq x y).le) hQconst.le
      have hLapQeq : ∀ x y, laplaceTimeKernel rate Q x y =
          spatialKernelComp volume (laplaceTimeKernel rate J)
            (laplaceTimeKernel rate T) x y := hQeq
      have hFirstRaw := FormBound.comp volume volume volume hSupI hLapQ
        hSupIForm hQbound
      have hTermSupRaw := FormBound.comp volume volume volume hSupJ hLapT
        hSupJForm hPathLap
      have hTermTailRaw := FormBound.comp volume volume volume hLapJ hTail
        hLapJForm hTailForm
      have hInnerForm := FormBound.add hSupJComp hLapJComp hTermSupRaw hTermTailRaw
      have hSecondRaw := FormBound.comp volume volume volume hLapI hInnerMeas
        hLapIForm hInnerForm
      have hTotalRaw := FormBound.add hFirstComp hSecondComp hFirstRaw hSecondRaw
      have hFirstConst :
          ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
            ENNReal.ofReal (factor ^ (v.length + 1)) =
          ENNReal.ofReal
            (Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have hTermSupConst :
          ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
            ENNReal.ofReal (factor ^ v.length) =
          ENNReal.ofReal
            (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have hTermTailConst :
          factorENN * ENNReal.ofReal
            (C * (τ₀ / 4) ^ (-(n : ℝ)) * targetFactor ^ (v.length - 1)) =
          ENNReal.ofReal
            (factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
              targetFactor ^ (v.length - 1))) := by
        simpa [factorENN] using
          (ENNReal.ofReal_mul hfactorPos.le).symm
      have hInnerConst :
          (ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ v.length)) +
            factorENN * ENNReal.ofReal
              (C * (τ₀ / 4) ^ (-(n : ℝ)) * targetFactor ^ (v.length - 1)) =
          ENNReal.ofReal
            (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
              factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1))) := by
        rw [hTermSupConst, hTermTailConst,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hTotalConstEq :
          (ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ (v.length + 1))) +
            1 * ((ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
                  ENNReal.ofReal (factor ^ v.length)) +
                factorENN * ENNReal.ofReal
                  (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                    targetFactor ^ (v.length - 1))) =
          ENNReal.ofReal
            (Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) +
              (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
                factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                  targetFactor ^ (v.length - 1)))) := by
        rw [hFirstConst, one_mul, hInnerConst,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hTauNonneg : 0 ≤ tauPow := by positivity
      have hTargetPowNonneg (k : ℕ) : 0 ≤ targetFactor ^ k :=
        pow_nonneg (le_of_lt htargetPos) k
      have hFirstRealLe :
          Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) ≤
            (C / 3) * tauPow * targetFactor ^ v.length := by
        rw [rpow_div_nat_neg (by norm_num) hτ₀ n]
        calc
          Cfree * ((2 : ℝ) ^ n * tauPow) * factor ^ (v.length + 1) =
              Cfree * (2 : ℝ) ^ n * tauPow * factor ^ (v.length + 1) := by ring
          _ ≤ Cfree * (2 : ℝ) ^ n * tauPow * targetFactor ^ v.length :=
            mul_le_mul_of_nonneg_left (hfactorstep v.length) (by positivity)
          _ ≤ (C / 3) * tauPow * targetFactor ^ v.length :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCsPart hTauNonneg)
              (hTargetPowNonneg _)
      have hInnerSupRealLe :
          Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length ≤
            (C / 3) * tauPow * targetFactor ^ v.length := by
        rw [rpow_div_nat_neg (by norm_num) hτ₀ n]
        calc
          Ccollision * ((4 : ℝ) ^ n * tauPow) * factor ^ v.length =
              Ccollision * (4 : ℝ) ^ n * tauPow * factor ^ v.length := by ring
          _ ≤ Ccollision * (4 : ℝ) ^ n * tauPow * targetFactor ^ v.length :=
            mul_le_mul_of_nonneg_left (hfactorpow v.length) (by positivity)
          _ ≤ (C / 3) * tauPow * targetFactor ^ v.length :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCcPart hTauNonneg)
              (hTargetPowNonneg _)
      have hTailRealLe :
          factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
            targetFactor ^ (v.length - 1)) ≤
            (C / 3) * tauPow * targetFactor ^ v.length := by
        rw [rpow_div_nat_neg (by norm_num) hτ₀ n]
        by_cases hk : v.length = 0
        · have hv : v = [] := List.length_eq_zero_iff.mp hk
          subst v
          simp only [List.length_nil, Nat.zero_sub, pow_zero, mul_one]
          have hsmall : factor * (4 : ℝ) ^ n ≤ 1 / 3 := by
            calc
              factor * (4 : ℝ) ^ n ≤
                  (1 / (3 * M * (4 : ℝ) ^ n)) * (4 : ℝ) ^ n :=
                mul_le_mul_of_nonneg_right hδsmall (by positivity)
              _ = 1 / (3 * M) := by
                have hpow4 : (4 : ℝ) ^ n ≠ 0 := ne_of_gt (by positivity)
                field_simp [hpow4, ne_of_gt hMpos]
              _ ≤ 1 / 3 := by
                have hdenM : 3 ≤ 3 * M := by
                  calc
                    3 = 3 * 1 := by ring
                    _ ≤ 3 * M := mul_le_mul_of_nonneg_left hMone (by norm_num)
                exact one_div_le_one_div_of_le (by norm_num) hdenM
          calc
            factor * (C * ((4 : ℝ) ^ n * tauPow)) =
                (factor * (4 : ℝ) ^ n) * C * tauPow := by ring
            _ ≤ (1 / 3) * C * tauPow :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hsmall (by positivity)) hTauNonneg
            _ = (C / 3) * tauPow := by ring
        · have hkpos : 0 < v.length := Nat.pos_of_ne_zero hk
          have hcoeff : q * (4 : ℝ) ^ n ≤ c / 3 := by
            have hcoeff' : 3 * (q * (4 : ℝ) ^ n) ≤ c := by
              calc
                3 * (q * (4 : ℝ) ^ n) = 3 * q * (4 : ℝ) ^ n := by ring
                _ ≤ c := hcTailMass
            calc
              q * (4 : ℝ) ^ n = (3 * (q * (4 : ℝ) ^ n)) / 3 := by ring
              _ ≤ c / 3 := div_le_div_of_nonneg_right hcoeff' (by norm_num)
          have hratio : factor * (4 : ℝ) ^ n ≤ targetFactor / 3 := by
            calc
              factor * (4 : ℝ) ^ n =
                  (q * (4 : ℝ) ^ n) * (Real.log rate - A)⁻¹ := by
                    simp [factor, pathLaplaceFactor, q]
                    ring
              _ ≤ (c / 3) * (Real.log rate - A)⁻¹ :=
                mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr hgap.le)
              _ = targetFactor / 3 := by
                dsimp [targetFactor]
                ring
          have hpow : targetFactor ^ (v.length - 1) * targetFactor =
              targetFactor ^ v.length := by
            calc
              targetFactor ^ (v.length - 1) * targetFactor =
                  targetFactor ^ ((v.length - 1) + 1) := by rw [pow_succ]
              _ = targetFactor ^ v.length := by
                rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
          calc
            factor * (C * ((4 : ℝ) ^ n * tauPow) *
                targetFactor ^ (v.length - 1)) =
              C * tauPow * (factor * (4 : ℝ) ^ n *
                targetFactor ^ (v.length - 1)) := by ring
            _ ≤ C * tauPow * ((targetFactor / 3) *
                targetFactor ^ (v.length - 1)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hratio
                  (pow_nonneg (le_of_lt htargetPos) _))
                (by positivity)
            _ = (C / 3) * tauPow * targetFactor ^ v.length := by
              calc
                C * tauPow * ((targetFactor / 3) * targetFactor ^ (v.length - 1)) =
                    (C / 3) * tauPow *
                      (targetFactor ^ (v.length - 1) * targetFactor) := by ring
                _ = (C / 3) * tauPow * targetFactor ^ v.length := by rw [hpow]
      have hTotalRealLe :
          Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) +
            (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
              factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1))) ≤
            C * tauPow * targetFactor ^ v.length := by
        have hcoeff : C / 3 + C / 3 + C / 3 ≤ C := by
          calc
            C / 3 + C / 3 + C / 3 = C := by ring
            _ ≤ C := le_rfl
        have hX : 0 ≤ tauPow * targetFactor ^ v.length :=
          mul_nonneg hTauNonneg (hTargetPowNonneg _)
        have hsum :
            (C / 3) * tauPow * targetFactor ^ v.length +
              (C / 3) * tauPow * targetFactor ^ v.length +
              (C / 3) * tauPow * targetFactor ^ v.length ≤
                C * tauPow * targetFactor ^ v.length := by
          calc
            _ = (C / 3 + C / 3 + C / 3) *
                (tauPow * targetFactor ^ v.length) := by ring
            _ ≤ C * (tauPow * targetFactor ^ v.length) :=
              mul_le_mul_of_nonneg_right hcoeff hX
            _ = C * tauPow * targetFactor ^ v.length := by ring
        calc
          Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) +
              (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
                factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                  targetFactor ^ (v.length - 1))) ≤
              (C / 3) * tauPow * targetFactor ^ v.length +
                ((C / 3) * tauPow * targetFactor ^ v.length +
                  (C / 3) * tauPow * targetFactor ^ v.length) := by
            apply add_le_add hFirstRealLe
            apply add_le_add hInnerSupRealLe hTailRealLe
          _ =
              (C / 3) * tauPow * targetFactor ^ v.length +
                (C / 3) * tauPow * targetFactor ^ v.length +
                (C / 3) * tauPow * targetFactor ^ v.length := by ring
          _ ≤ C * tauPow * targetFactor ^ v.length := hsum
      have hFirstConst :
          ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
            ENNReal.ofReal (factor ^ (v.length + 1)) =
          ENNReal.ofReal
            (Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have hTermSupConst :
          ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
            ENNReal.ofReal (factor ^ v.length) =
          ENNReal.ofReal
            (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have hTermTailConst :
          factorENN * ENNReal.ofReal
            (C * (τ₀ / 4) ^ (-(n : ℝ)) * targetFactor ^ (v.length - 1)) =
          ENNReal.ofReal
            (factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
              targetFactor ^ (v.length - 1))) := by
        simpa [factorENN] using (ENNReal.ofReal_mul hfactorPos.le).symm
      have hInnerConst :
          (ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ v.length)) +
            factorENN * ENNReal.ofReal
              (C * (τ₀ / 4) ^ (-(n : ℝ)) * targetFactor ^ (v.length - 1)) =
          ENNReal.ofReal
            (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
              factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                targetFactor ^ (v.length - 1))) := by
        rw [hTermSupConst, hTermTailConst,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hTotalConstEq :
          (ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ (v.length + 1))) +
            1 * ((ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
                  ENNReal.ofReal (factor ^ v.length)) +
                factorENN * ENNReal.ofReal
                  (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                    targetFactor ^ (v.length - 1))) =
          ENNReal.ofReal
            (Cfree * (τ₀ / 2) ^ (-(n : ℝ)) * factor ^ (v.length + 1) +
              (Ccollision * (τ₀ / 4) ^ (-(n : ℝ)) * factor ^ v.length +
                factor * (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                  targetFactor ^ (v.length - 1)))) := by
        rw [hFirstConst, one_mul, hInnerConst,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hTotalConst :
          (ENNReal.ofReal (Cfree * (τ₀ / 2) ^ (-(n : ℝ))) *
              ENNReal.ofReal (factor ^ (v.length + 1))) +
            1 * ((ENNReal.ofReal (Ccollision * (τ₀ / 4) ^ (-(n : ℝ))) *
                  ENNReal.ofReal (factor ^ v.length)) +
                factorENN * ENNReal.ofReal
                  (C * (τ₀ / 4) ^ (-(n : ℝ)) *
                    targetFactor ^ (v.length - 1))) ≤
          ENNReal.ofReal (C * tauPow * targetFactor ^ v.length) := by
        rw [hTotalConstEq]
        exact ENNReal.ofReal_le_ofReal hTotalRealLe
      have hTcausal : causalKernel T = T :=
        pathTimeKernel_causal θ v (collisionEmbedding α) id
      have hQeq : ∀ x y, laplaceTimeKernel rate Q x y =
          spatialKernelComp volume (laplaceTimeKernel rate J)
            (laplaceTimeKernel rate T) x y := by
        intro x y
        simpa [Q, hTcausal] using
          laplaceTimeKernel_timeKernelComp_causal volume hJ hT rate x y
      have hQraw := FormBound.comp volume volume volume hLapJ hLapT
        hLapJForm hPathLap
      have hQconst :
          factorENN * ENNReal.ofReal (factor ^ v.length) =
            ENNReal.ofReal (factor ^ (v.length + 1)) := by
        calc
          factorENN * ENNReal.ofReal (factor ^ v.length) =
              ENNReal.ofReal (factor * factor ^ v.length) := by
                simpa [factorENN] using (ENNReal.ofReal_mul hfactorPos.le).symm
          _ = ENNReal.ofReal (factor ^ (v.length + 1)) := by
                congr 1
                rw [pow_succ]
                ring
      have hQbound : FormBound volume volume (laplaceTimeKernel rate Q)
          (ENNReal.ofReal (factor ^ (v.length + 1))) :=
        hQraw.mono (fun x y => (hQeq x y).le) hQconst.le
      have hFirstRaw := FormBound.comp volume volume volume hSupI hLapQ
        hSupIForm hQbound
      have hTermSupRaw := FormBound.comp volume volume volume hSupJ hLapT
        hSupJForm hPathLap
      have hTermTailRaw := FormBound.comp volume volume volume hLapJ hTail
        hLapJForm hTailForm
      have hInnerForm := FormBound.add hSupJComp hLapJComp hTermSupRaw hTermTailRaw
      have hSecondRaw := FormBound.comp volume volume volume hLapI hInnerMeas
        hLapIForm hInnerForm
      have hTotalRaw := FormBound.add hFirstComp hSecondComp hFirstRaw hSecondRaw
      have hTotal := hTotalRaw.mono (fun _ _ => le_rfl) hTotalConst
      simpa [pathDominatingKernel, I, J, T, Q, Tail, Inner, factor,
        targetFactor, tauPow, factorENN, List.length_cons, Nat.add_sub_cancel] using hTotal

end Critical2DKPZ.DeltaBose
