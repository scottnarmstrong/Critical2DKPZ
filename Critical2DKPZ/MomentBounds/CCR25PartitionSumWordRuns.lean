/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25WordRunAssembly
import Mathlib.Tactic

/-! # Full-support partition sums grouped by CCR25 words -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem list_prod_eq_of_map_eq {α β : Type*}
    {xs ys : List (α × β)}
    (hfst : xs.map Prod.fst = ys.map Prod.fst)
    (hsnd : xs.map Prod.snd = ys.map Prod.snd) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hfst
  | cons x xs ih =>
      cases ys with
      | nil => simp at hfst
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at hfst hsnd
          rcases hfst with ⟨hfstHead, hfstTail⟩
          rcases hsnd with ⟨hsndHead, hsndTail⟩
          have hxy : x = y := Prod.ext hfstHead hsndHead
          subst y
          simp [ih hfstTail hsndTail]

/-- The damped kernel word of a timed code is the parameter-choice kernel word of its labels. -/
theorem ccr25GapRunTimedCodeDampedKernelWord_eq_parameterChoiceKernelWord
    {h L : ℕ} (lam β : ℝ)
    (code : List (CCR25OperatorLabel h × CCR25RunDurationParam)) :
    ccr25GapRunTimedCodeDampedKernelWord lam β code =
      ccr25ParameterChoiceKernelWord
        ((code.map Prod.fst).map (ccr25RunOperatorParameterFamily L lam β))
        (code.map Prod.snd) := by
  induction code with
  | nil => rfl
  | cons entry code ih =>
      simp only [ccr25GapRunTimedCodeDampedKernelWord, List.map_cons,
        ccr25GapRunTimedCodeDampedKernel,
        ccr25ParameterChoiceKernelWord]
      rw [ccr25RunOperatorParameterFamily_kernel_eq]
      apply congrArg (fun kernels =>
        ccr25RunDurationKernel lam β entry.1 entry.2 :: kernels)
      exact ih

/-- Keys with equal label lists, equal timed parameters and positive later entry gaps are equal. -/
theorem ccr25GapRunKey_eq_of_labels_eq_params {h : ℕ}
    {key key' : CCR25GapRunKey h}
    (hlabels : ccr25GapRunKeyLabels key = ccr25GapRunKeyLabels key')
    (hparams : (ccr25GapRunKeyTimedCode key).map Prod.snd =
      (ccr25GapRunKeyTimedCode key').map Prod.snd)
    (hpos : ∀ run ∈ key.laterRuns, 1 ≤ run.firstGap)
    (hpos' : ∀ run ∈ key'.laterRuns, 1 ≤ run.firstGap) : key = key' := by
  have hops : (ccr25GapRunKeyTimedCode key).map Prod.fst =
      (ccr25GapRunKeyTimedCode key').map Prod.fst := by
    rw [ccr25GapRunKeyTimedCode_fst, ccr25GapRunKeyTimedCode_fst]
    unfold ccr25GapRunOperatorWord
    have hnormalize (key : CCR25GapRunKey h) :
        (ccr25GapRunKeyNormalize key).map CCR25GapRun.label =
          ccr25GapRunKeyLabels key := by
      simp [ccr25GapRunKeyNormalize, ccr25GapRunKeyRestore,
        ccr25GapRunKeyLabels]
    rw [hnormalize key, hnormalize key', hlabels]
  have hcode := list_prod_eq_of_map_eq hops hparams
  exact ccr25GapRunKeyTimedCode_injective hpos hpos' hcode

/-- Gap-run path weights are nonnegative. -/
theorem ccr25GapRunPathWeight_nonneg {h : ℕ} (β : ℝ)
    (previous : ReplicaPartition h) :
    ∀ (runs : List (CCR25GapRun h)) (z : LatticeConfiguration h),
      0 ≤ ccr25GapRunPathWeight β previous runs z := by
  intro runs
  induction runs generalizing previous with
  | nil => intro z; simp [ccr25GapRunPathWeight]
  | cons run runs ih =>
      intro z
      simp only [ccr25GapRunPathWeight]
      apply mul_nonneg (abs_nonneg _)
      apply tsum_nonneg
      intro x
      apply mul_nonneg (freeReplicaKernel_nonneg _ _ _ _ _)
      apply tsum_nonneg
      intro y
      exact mul_nonneg
        (ccr25TimedInteractionRunAbs_nonneg β run.label
          run.internalGapsRev x y)
        (ih run.label y)

/-- The product of the absolute disorder moments of the labels of the normalized key runs. -/
def ccr25GapRunKeyMomentCoefficient {h : ℕ} (β : ℝ)
    (key : CCR25GapRunKey h) : ℝ :=
  ccr25GapRunMomentProduct β (ccr25GapRunKeyNormalize key)

/-- The word kernel on the key's damped timed code, applied to the last-label indicator. -/
def ccr25GapRunKeyDampedTail {h : ℕ} (L : ℕ) (lam β : ℝ)
    (A : Finset Site) (key : CCR25GapRunKey h)
    (x : LatticeConfiguration h) : ℝ :=
  finiteKernelWordApply (configBox h A L)
    (ccr25GapRunTimedCodeDampedKernelWord lam β
      (ccr25GapRunKeyTimedCode key))
    (collisionIndicator (ccr25GapRunKeyLastLabel key)) x

private theorem ccr25GapRunKeyInteractionCost_le_remainingCost {h : ℕ}
    (key : CCR25GapRunKey h) :
    ccr25GapRunTimedCodeInteractionCost (ccr25GapRunKeyTimedCode key) ≤
      key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run =>
          run.firstGap + run.internalGapsRev.sum).sum := by
  rw [ccr25GapRunKeyTimedCodeInteractionCost_eq]
  have htail :
      (key.laterRuns.map fun run => run.internalGapsRev.sum).sum ≤
        (key.laterRuns.map fun run =>
          run.firstGap + run.internalGapsRev.sum).sum := by
    induction key.laterRuns with
    | nil => simp
    | cons run runs ih =>
        simp only [List.map_cons, List.sum_cons]
        omega
  omega

/-- A valid subset of first-gap choices for one normalized run key is bounded
by its finite-box damped CCR25 word. -/
theorem ccr25GapRunKey_validGapProfileSum_le_of_gapFacts {h L : ℕ}
    (β lam : ℝ) (hlam : 0 ≤ lam)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (key : CCR25GapRunKey h)
    (hkeyFacts : (∀ run ∈ key.laterRuns, 1 ≤ run.firstGap) ∧
      (∀ run ∈ key.laterRuns, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
      (∀ d ∈ key.firstInternalGapsRev, 1 ≤ d) ∧
      key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L)
    (N : Finset ℕ) (hN : N ⊆ Finset.range L)
    (hbudget : ∀ n ∈ N,
      n + 1 + key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run =>
          run.firstGap + run.internalGapsRev.sum).sum ≤ L) :
    (∑ n ∈ N,
      ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ccr25GapRunPathWeight β ⊥
            (ccr25GapRunKeyRestore key (n + 1)) w) ≤
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x := by
  classical
  let B : Finset (LatticeConfiguration h) := configBox h A L
  let tail := ccr25GapRunKeyDampedTail L lam β A key
  let coeff := ccr25GapRunKeyMomentCoefficient β key
  have hcostLe : ccr25GapRunTimedCodeInteractionCost
        (ccr25GapRunKeyTimedCode key) ≤ L :=
    le_trans (ccr25GapRunKeyInteractionCost_le_remainingCost key)
      hkeyFacts.2.2.2
  have hcoeff : 0 ≤ coeff := by
    unfold coeff ccr25GapRunKeyMomentCoefficient ccr25GapRunMomentProduct
    exact List.prod_nonneg (by
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨run, _, rfl⟩ := hr
      exact abs_nonneg _)
  have hkernel :
      ∀ K ∈ ccr25GapRunTimedCodeDampedKernelWord lam β
          (ccr25GapRunKeyTimedCode key),
        ∀ x y, 0 ≤ K x y := by
    intro K hK x y
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hK
    exact ccr25RunDurationKernel_nonneg lam β entry.1 entry.2 x y
  have hterminal : ∀ x, 0 ≤ collisionIndicator
      (ccr25GapRunKeyLastLabel key) x := by
    intro x
    by_cases hx : IsCollisionConfiguration (ccr25GapRunKeyLastLabel key) x <;>
      simp [collisionIndicator, hx]
  have htailNonneg : ∀ x, 0 ≤ tail x := by
    intro x
    exact finiteKernelWordApply_nonneg B
      (ccr25GapRunTimedCodeDampedKernelWord lam β
        (ccr25GapRunKeyTimedCode key))
      (collisionIndicator (ccr25GapRunKeyLastLabel key))
      hkernel hterminal x
  have hboundaryNonneg (n : ℕ) (x : LatticeConfiguration h) :
      0 ≤ replicaBoundaryVector (n + 1) key.firstLabel A φ x :=
    replicaBoundaryVector_nonneg (n + 1) key.firstLabel A φ
      (fun z hz => hφ z) x
  have hhattedNonneg (x : LatticeConfiguration h) :
      0 ≤ hattedReplicaBoundaryVector L key.firstLabel A φ x :=
    hattedReplicaBoundaryVector_nonneg L key.firstLabel A φ
      (fun z hz => hφ z) x
  have hmomentEq (n : ℕ) :
      ccr25GapRunMomentProduct β
          (ccr25GapRunKeyRestore key (n + 1)) = coeff := by
    simp [coeff, ccr25GapRunKeyMomentCoefficient,
      ccr25GapRunMomentProduct, ccr25GapRunKeyRestore,
      ccr25GapRunKeyNormalize]
  have hsingle (n : ℕ) (hn : n ∈ N) :
      (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ccr25GapRunPathWeight β ⊥
            (ccr25GapRunKeyRestore key (n + 1)) w) ≤
      Real.exp (lam * L) * coeff *
        ∑ x ∈ B,
          replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by
    have hgapPos : ∀ run ∈ key.laterRuns, 1 ≤ run.firstGap :=
      hkeyFacts.1
    have hprof := ccr25GapRunKey_profilePairing_eq_finiteBox_word
      β A φ key n hgapPos (hbudget n hn)
    have hwordExp := finiteKernelWordApply_undampedTimedCode_eq_exp_mul_damped
      B lam β (ccr25GapRunKeyTimedCode key) (fun _ => 1)
    have hsumCode :
        (∑ x ∈ B,
          replicaBoundaryVector (n + 1) key.firstLabel A φ x *
            finiteKernelWordApply B
              (ccr25GapRunTimedCodeKernelWord β
                (ccr25GapRunKeyTimedCode key)) (fun _ => 1) x) =
        Real.exp (lam *
            (ccr25GapRunTimedCodeInteractionCost
              (ccr25GapRunKeyTimedCode key) : ℝ)) *
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hwordExp x,
        ccr25GapRunKeyDampedKernelWord_terminal_eq B lam β key x]
      simpa [tail, ccr25GapRunKeyDampedTail] using (by ring)
    have hcostCast :
        (ccr25GapRunTimedCodeInteractionCost
          (ccr25GapRunKeyTimedCode key) : ℝ) ≤ L := by
      exact_mod_cast hcostLe
    have hexp : Real.exp
        (lam * (ccr25GapRunTimedCodeInteractionCost
          (ccr25GapRunKeyTimedCode key) : ℝ)) ≤ Real.exp (lam * L) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hcostCast hlam
    have hpairNonneg : 0 ≤ ∑ x ∈ B,
        replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by
      apply Finset.sum_nonneg
      intro x hx
      exact mul_nonneg (hboundaryNonneg n x) (htailNonneg x)
    have hmomentEq' := hmomentEq n
    rw [hprof, hmomentEq', hsumCode]
    calc
      coeff * (Real.exp
          (lam * (ccr25GapRunTimedCodeInteractionCost
            (ccr25GapRunKeyTimedCode key) : ℝ)) *
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x) =
        (coeff * Real.exp
          (lam * (ccr25GapRunTimedCodeInteractionCost
            (ccr25GapRunKeyTimedCode key) : ℝ))) *
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by ring
      _ ≤ (Real.exp (lam * L) * coeff) *
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x :=
        calc
          (coeff * Real.exp
              (lam * (ccr25GapRunTimedCodeInteractionCost
                (ccr25GapRunKeyTimedCode key) : ℝ))) *
              ∑ x ∈ B,
                replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x
              = (Real.exp
                  (lam * (ccr25GapRunTimedCodeInteractionCost
                    (ccr25GapRunKeyTimedCode key) : ℝ)) * coeff) *
                  ∑ x ∈ B,
                    replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by ring
          _ ≤ (Real.exp (lam * L) * coeff) *
                ∑ x ∈ B,
                  replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hexp hcoeff) hpairNonneg
          _ = Real.exp (lam * L) * coeff *
                ∑ x ∈ B,
                  replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by ring
      _ = Real.exp (lam * L) * coeff *
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by ring
  have hsingleNonneg (n : ℕ) :
      0 ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ccr25GapRunPathWeight β ⊥
            (ccr25GapRunKeyRestore key (n + 1)) w := by
    apply Finset.sum_nonneg
    intro w hw
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      exact hφ (w i)
    · exact ccr25GapRunPathWeight_nonneg β ⊥
        (ccr25GapRunKeyRestore key (n + 1)) w
  calc
    _ ≤ ∑ n ∈ N,
        Real.exp (lam * L) * coeff *
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x :=
      Finset.sum_le_sum fun n hn => hsingle n hn
    _ ≤ ∑ n ∈ Finset.range L,
        Real.exp (lam * L) * coeff *
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (by
        intro n hn hnot
        exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) hcoeff)
          (Finset.sum_nonneg fun x hx =>
            mul_nonneg (hboundaryNonneg n x) (htailNonneg x)))
    _ = (Real.exp (lam * L) * coeff) *
        ∑ n ∈ Finset.range L,
          ∑ x ∈ B,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by
      rw [← Finset.mul_sum]
    _ = (Real.exp (lam * L) * coeff) *
        ∑ x ∈ B,
          (∑ n ∈ Finset.range L,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x) * tail x := by
      apply congrArg (fun v : ℝ => (Real.exp (lam * L) * coeff) * v)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_mul]
    _ = Real.exp (lam * L) * coeff *
        ∑ x ∈ B,
          hattedReplicaBoundaryVector L key.firstLabel A φ x * tail x := by
      apply congrArg (fun v : ℝ => (Real.exp (lam * L) * coeff) * v)
      apply Finset.sum_congr rfl
      intro x hx
      simp [hattedReplicaBoundaryVector]

/-- Specialization of the timing-only first-gap estimate to full-support keys. -/
theorem ccr25GapRunKey_validGapProfileSum_le {h L : ℕ}
    (hh : 0 < h) (β lam : ℝ) (hlam : 0 ≤ lam)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (key : CCR25GapRunKey h)
    (hkey : key ∈ ccr25FullSupportGapRunKeys h L)
    (N : Finset ℕ) (hN : N ⊆ Finset.range L)
    (hbudget : ∀ n ∈ N,
      n + 1 + key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run =>
          run.firstGap + run.internalGapsRev.sum).sum ≤ L) :
    (∑ n ∈ N,
      ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ccr25GapRunPathWeight β ⊥
            (ccr25GapRunKeyRestore key (n + 1)) w) ≤
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x := by
  exact ccr25GapRunKey_validGapProfileSum_le_of_gapFacts β lam hlam A φ hφ key
    (ccr25FullSupportGapRunKey_gapFacts hh hkey) N hN hbudget

/-- Code retaining the run key and its omitted first free gap. -/
def ccr25GapRunStreamCode {h : ℕ}
    (runs : List (CCR25GapRun h)) : CCR25GapRunKey h × ℕ :=
  match runs with
  | [] => (ccr25GapRunKeyOfD runs, 0)
  | run :: _ => (ccr25GapRunKeyOfD runs, run.firstGap - 1)

/-- Start-profile score of one exact timed run stream. -/
def ccr25GapRunStreamProfileScore {h : ℕ} (β : ℝ)
    (A : Finset Site) (φ : Site → ℝ) (runs : List (CCR25GapRun h)) : ℝ :=
  ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
    (∏ i : Fin h, φ (w i)) * ccr25GapRunPathWeight β ⊥ runs w

/-- Start-profile score after restoring a key at a chosen first gap. -/
def ccr25GapRunKeyGapProfileScore {h : ℕ} (β : ℝ)
    (A : Finset Site) (φ : Site → ℝ) (p : CCR25GapRunKey h × ℕ) : ℝ :=
  ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
    (∏ i : Fin h, φ (w i)) *
      ccr25GapRunPathWeight β ⊥
        (ccr25GapRunKeyRestore p.1 (p.2 + 1)) w

/-- The restored key fits inside the microscopic time horizon. -/
def ccr25GapRunKeyGapBudget {h : ℕ} (L : ℕ)
    (p : CCR25GapRunKey h × ℕ) : Prop :=
  p.2 + 1 + p.1.firstInternalGapsRev.sum +
    (p.1.laterRuns.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L

/-- Restored key score restricted to the total duration budget. -/
def ccr25GapRunKeyGapProfileScoreWithBudget {h : ℕ} (L : ℕ)
    (β : ℝ) (A : Finset Site) (φ : Site → ℝ)
    (p : CCR25GapRunKey h × ℕ) : ℝ :=
  if ccr25GapRunKeyGapBudget L p then
    ccr25GapRunKeyGapProfileScore β A φ p else 0

/-- Positive nonempty run streams are recovered from their codes. -/
theorem ccr25GapRunStreamCode_injective_of_positive {h : ℕ}
    {runs runs' : List (CCR25GapRun h)}
    (hnil : runs ≠ []) (hnil' : runs' ≠ [])
    (hpos : ∀ run ∈ runs, 1 ≤ run.firstGap)
    (hpos' : ∀ run ∈ runs', 1 ≤ run.firstGap)
    (hcode : ccr25GapRunStreamCode runs =
      ccr25GapRunStreamCode runs') : runs = runs' := by
  cases runs with
  | nil => exact (hnil rfl).elim
  | cons run tail =>
    cases runs' with
    | nil => exact (hnil' rfl).elim
    | cons run' tail' =>
      have hp : 1 ≤ run.firstGap := hpos run (by simp)
      have hp' : 1 ≤ run'.firstGap := hpos' run' (by simp)
      cases run with
      | mk label gap gaps =>
        cases run' with
        | mk label' gap' gaps' =>
          have hkey :
              (⟨label, gaps, tail⟩ : CCR25GapRunKey h) =
                ⟨label', gaps', tail'⟩ := by
            have := congrArg Prod.fst hcode
            simpa [ccr25GapRunStreamCode, ccr25GapRunKeyOfD] using this
          have hfirst : gap - 1 = gap' - 1 := by
            have := congrArg Prod.snd hcode
            simpa [ccr25GapRunStreamCode] using this
          simp only [CCR25GapRunKey.mk.injEq] at hkey
          rcases hkey with ⟨rfl, rfl, rfl⟩
          change 1 ≤ gap at hp
          change 1 ≤ gap' at hp'
          have hgap : gap = gap' := by omega
          subst gap'
          rfl

private theorem ccr25FullSupportGapRunStream_ne_nil {h L : ℕ}
    (hh : 0 < h) {runs : List (CCR25GapRun h)}
    (hruns : runs ∈ ccr25FullSupportGapRunStreams h L) : runs ≠ [] := by
  simp only [ccr25FullSupportGapRunStreams, Finset.mem_image] at hruns
  obtain ⟨I, hI, rfl⟩ := hruns
  exact ccr25FullSupportGapRunEncode_ne_nil hh hI

private theorem ccr25FullSupportGapRunStreamCode_mem {h L : ℕ}
    (hh : 0 < h) {runs : List (CCR25GapRun h)}
    (hruns : runs ∈ ccr25FullSupportGapRunStreams h L) :
    ccr25GapRunStreamCode runs ∈
      ccr25FullSupportGapRunKeys h L ×ˢ Finset.range L ∧
      ccr25GapRunKeyGapBudget L (ccr25GapRunStreamCode runs) := by
  classical
  have hne := ccr25FullSupportGapRunStream_ne_nil hh hruns
  cases runs with
  | nil => exact (hne rfl).elim
  | cons first later =>
      have hfacts := ccr25FullSupportGapRunStream_gapFacts hruns
      simp only [List.map_cons, List.sum_cons] at hfacts
      have hfirstPos := hfacts.1 first (by simp)
      have htailCost := hfacts.2.2
      have hkeyMem : ccr25GapRunKeyOfD (first :: later) ∈
          ccr25FullSupportGapRunKeys h L := by
        exact Finset.mem_image.mpr ⟨first :: later, hruns, rfl⟩
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · exact hkeyMem
        · simp only [ccr25GapRunStreamCode, Finset.mem_range]
          omega
      · simp only [ccr25GapRunStreamCode, ccr25GapRunKeyOfD,
          ccr25GapRunKeyGapBudget]
        omega

/-- Nonnegative profiles give nonnegative restored-key scores. -/
theorem ccr25GapRunKeyGapProfileScore_nonneg {h : ℕ}
    (β : ℝ) (A : Finset Site) (φ : Site → ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (p : CCR25GapRunKey h × ℕ) :
    0 ≤ ccr25GapRunKeyGapProfileScore β A φ p := by
  apply Finset.sum_nonneg
  intro w hw
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i hi
    exact hφ (w i)
  · exact ccr25GapRunPathWeight_nonneg β ⊥
      (ccr25GapRunKeyRestore p.1 (p.2 + 1)) w

/-- The duration-budget restriction preserves nonnegativity. -/
theorem ccr25GapRunKeyGapProfileScoreWithBudget_nonneg {h L : ℕ}
    (β : ℝ) (A : Finset Site) (φ : Site → ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (p : CCR25GapRunKey h × ℕ) :
    0 ≤ ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p := by
  simp only [ccr25GapRunKeyGapProfileScoreWithBudget]
  split_ifs
  · exact ccr25GapRunKeyGapProfileScore_nonneg β A φ hφ p
  · norm_num

private theorem ccr25FullSupportGapRunStreamSum_le_keyGapProfileSum
    {h L : ℕ} (hh : 0 < h) (β lam : ℝ) (hlam : 0 ≤ lam)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ runs ∈ ccr25FullSupportGapRunStreams h L,
      ccr25GapRunStreamProfileScore β A φ runs) ≤
      ∑ key ∈ ccr25FullSupportGapRunKeys h L,
        Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
          ∑ x ∈ configBox h A L,
            hattedReplicaBoundaryVector L key.firstLabel A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x := by
  classical
  let streams := ccr25FullSupportGapRunStreams h L
  let keys := ccr25FullSupportGapRunKeys h L
  let pairs := streams.image ccr25GapRunStreamCode
  have hcodeInj : Set.InjOn ccr25GapRunStreamCode
      (↑streams : Set (List (CCR25GapRun h))) := by
    intro runs hruns runs' hruns' hcode
    apply ccr25GapRunStreamCode_injective_of_positive
      (ccr25FullSupportGapRunStream_ne_nil hh hruns)
      (ccr25FullSupportGapRunStream_ne_nil hh hruns')
      (ccr25FullSupportGapRunStream_gapFacts hruns).1
      (ccr25FullSupportGapRunStream_gapFacts hruns').1 hcode
  have hsumImage :
      (∑ runs ∈ streams, ccr25GapRunStreamProfileScore β A φ runs) =
        ∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p := by
    calc
      _ = ∑ runs ∈ streams,
          ccr25GapRunKeyGapProfileScore β A φ
            (ccr25GapRunStreamCode runs) := by
        apply Finset.sum_congr rfl
        intro runs hruns
        have hne := ccr25FullSupportGapRunStream_ne_nil hh hruns
        have hfacts := ccr25FullSupportGapRunStream_gapFacts hruns
        cases runs with
        | nil => exact (hne rfl).elim
        | cons first later =>
            have hpos := hfacts.1 first (by simp)
            simp [ccr25GapRunStreamProfileScore,
              ccr25GapRunKeyGapProfileScore, ccr25GapRunStreamCode,
              ccr25GapRunKeyOfD, ccr25GapRunKeyRestore,
              Nat.sub_add_cancel hpos]
      _ = ∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p := by
        dsimp [pairs]
        symm
        exact Finset.sum_image hcodeInj
  have hpairsSubset : pairs ⊆ keys ×ˢ Finset.range L := by
    intro p hp
    obtain ⟨runs, hruns, rfl⟩ := Finset.mem_image.mp hp
    exact (ccr25FullSupportGapRunStreamCode_mem hh hruns).1
  have hpairsBudget : ∀ p ∈ pairs,
      ccr25GapRunKeyGapBudget L p := by
    intro p hp
    obtain ⟨runs, hruns, rfl⟩ := Finset.mem_image.mp hp
    exact (ccr25FullSupportGapRunStreamCode_mem hh hruns).2
  have hsumBudget :
      (∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p) ≤
        ∑ p ∈ keys ×ˢ Finset.range L,
          ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p := by
    calc
      _ = ∑ p ∈ pairs,
          ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [ccr25GapRunKeyGapProfileScoreWithBudget,
          hpairsBudget p hp]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hpairsSubset (by
        intro p hp hnot
        exact ccr25GapRunKeyGapProfileScoreWithBudget_nonneg
          β A φ hφ p)
  have hsumProduct :
      (∑ p ∈ keys ×ˢ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p) =
      ∑ key ∈ keys, ∑ n ∈ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ (key, n) := by
    rw [Finset.sum_product]
  have hkeyBound (key : CCR25GapRunKey h) (hkey : key ∈ keys) :
      (∑ n ∈ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ (key, n)) ≤
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x := by
    let N := (Finset.range L).filter
      (fun n => ccr25GapRunKeyGapBudget L (key, n))
    have hN : N ⊆ Finset.range L := Finset.filter_subset _ _
    have hbudget : ∀ n ∈ N,
        n + 1 + key.firstInternalGapsRev.sum +
          (key.laterRuns.map fun run =>
            run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
      intro n hn
      exact (Finset.mem_filter.mp hn).2
    calc
      _ = ∑ n ∈ N,
          ccr25GapRunKeyGapProfileScore β A φ (key, n) := by
        change (∑ n ∈ Finset.range L,
          if ccr25GapRunKeyGapBudget L (key, n) then
            ccr25GapRunKeyGapProfileScore β A φ (key, n) else 0) = _
        dsimp [N]
        rw [← Finset.sum_filter]
      _ ≤ _ := ccr25GapRunKey_validGapProfileSum_le hh β lam hlam
        A φ hφ key hkey N hN hbudget
  calc
    _ = ∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p := hsumImage
    _ ≤ ∑ p ∈ keys ×ˢ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p := hsumBudget
    _ = ∑ key ∈ keys, ∑ n ∈ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ (key, n) := hsumProduct
    _ ≤ ∑ key ∈ keys,
        Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
          ∑ x ∈ configBox h A L,
            hattedReplicaBoundaryVector L key.firstLabel A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x :=
      Finset.sum_le_sum fun key hkey => hkeyBound key hkey

/-- Index type of partition words: a length `n + 1` together with a word of that length. -/
abbrev CCR25PartitionWordIndex (h : ℕ) :=
  Σ n : ℕ, (Fin (n + 1) → ReplicaPartition h)

/-- Pairs `(n, w)` with `n < L` and `w` an admissible word of length `n + 1`. -/
noncomputable def ccr25AdmissibleWordIndices (h L : ℕ) :
    Finset (CCR25PartitionWordIndex h) :=
  (Finset.range L).sigma fun n => ccr25AdmissibleWords h n

/-- The word index of a gap-run key: its number of later runs and its word. -/
def ccr25GapRunKeyWordIndex {h : ℕ} (key : CCR25GapRunKey h) :
    CCR25PartitionWordIndex h :=
  ⟨key.laterRuns.length, ccr25GapRunKeyWord key⟩

/-- Moment-weighted operator contribution of one length-indexed word. -/
def ccr25WordIndexContribution {h L : ℕ} (lam β : ℝ)
    (A : Finset Site) (φ : Site → ℝ)
    (idx : CCR25PartitionWordIndex h) : ℝ :=
  (∏ j : Fin (idx.1 + 1),
      |replicaPartitionDisorderMoment β (idx.2 j)|) *
    ccr25FiniteWordPairing (configBox h A L) L lam β idx.2
      (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator

private theorem ccr25GapRunKeyLabels_getLast {h : ℕ}
    (key : CCR25GapRunKey h) :
    (ccr25GapRunKeyLabels key).getLast (by simp [ccr25GapRunKeyLabels]) =
      ccr25GapRunKeyLastLabel key := by
  cases key with
  | mk firstLabel firstInternalGapsRev laterRuns =>
      induction laterRuns generalizing firstLabel with
      | nil => simp [ccr25GapRunKeyLabels, ccr25GapRunKeyLastLabel]
      | cons run laterRuns ih =>
          cases laterRuns with
          | nil => simp [ccr25GapRunKeyLabels, ccr25GapRunKeyLastLabel]
          | cons run' laterRuns' =>
              simp only [ccr25GapRunKeyLabels, List.map_cons,
                List.getLast_cons_cons, ccr25GapRunKeyLastLabel,
                List.foldl_cons]
              exact ih run.label

private theorem ccr25GapRunKeyWord_lastLabel {h : ℕ}
    (key : CCR25GapRunKey h) :
    ccr25GapRunKeyWord key (Fin.last key.laterRuns.length) =
      ccr25GapRunKeyLastLabel key := by
  have hlast := List.getLast_ofFn_succ (ccr25GapRunKeyWord key)
  calc
    ccr25GapRunKeyWord key (Fin.last key.laterRuns.length) =
        (ccr25GapRunKeyLabels key).getLast (by simp [ccr25GapRunKeyLabels]) := by
      simpa only [ccr25GapRunKeyWord_ofFn] using hlast.symm
    _ = ccr25GapRunKeyLastLabel key := ccr25GapRunKeyLabels_getLast key

private theorem ccr25GapRunKeyMomentCoefficient_eq_word
    {h n : ℕ} (β : ℝ) (key : CCR25GapRunKey h)
    (J : Fin (n + 1) → ReplicaPartition h)
    (hindex : ccr25GapRunKeyWordIndex key = ⟨n, J⟩) :
    ccr25GapRunKeyMomentCoefficient β key =
      ∏ j : Fin (n + 1), |replicaPartitionDisorderMoment β (J j)| := by
  cases hindex
  unfold ccr25GapRunKeyMomentCoefficient ccr25GapRunMomentProduct
  have hmap :
      (ccr25GapRunKeyLabels key).map
          (fun I => |replicaPartitionDisorderMoment β I|) =
        (ccr25GapRunKeyNormalize key).map
          (fun run => |replicaPartitionDisorderMoment β run.label|) := by
    simp [ccr25GapRunKeyLabels, ccr25GapRunKeyNormalize,
      ccr25GapRunKeyRestore]
  rw [← hmap, ← ccr25GapRunKeyWord_ofFn key]
  simp only [List.map_ofFn, Function.comp_def, List.prod_ofFn]

private theorem ccr25GapRunKeyWordIndex_components {h n : ℕ}
    (key : CCR25GapRunKey h) (J : Fin (n + 1) → ReplicaPartition h)
    (hindex : ccr25GapRunKeyWordIndex key = ⟨n, J⟩) :
    key.laterRuns.length = n ∧
      List.ofFn (ccr25GapRunKeyWord key) = List.ofFn J := by
  cases hindex
  exact ⟨rfl, rfl⟩

private theorem ccr25FullSupportGapRunKeyWordIndex_mem {h L : ℕ}
    (hh : 0 < h) {key : CCR25GapRunKey h}
    (hkey : key ∈ ccr25FullSupportGapRunKeys h L) :
    ccr25GapRunKeyWordIndex key ∈ ccr25AdmissibleWordIndices h L := by
  obtain ⟨hadm, hlen⟩ :=
    ccr25FullSupportGapRunKey_admissible_and_length_lt hh hkey
  simp only [ccr25AdmissibleWordIndices, Finset.mem_sigma]
  constructor
  · simpa only [Finset.mem_range, ccr25GapRunKeyWordIndex] using hlen
  · change ccr25GapRunKeyWord key ∈
        Finset.univ.filter ccr25AdmissibleWord
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadm⟩

/-- Resumming a fiber of timed keys uses only their positive bounded gaps. -/
theorem ccr25GapRunKeyFiber_timedTail_le_of_gapFacts
    {h L : ℕ} (lam β : ℝ)
    (A : Finset Site)
    (idx : CCR25PartitionWordIndex h)
    (F : Finset (CCR25GapRunKey h))
    (hFfacts : ∀ key ∈ F,
      (∀ run ∈ key.laterRuns, 1 ≤ run.firstGap) ∧
        (∀ run ∈ key.laterRuns, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
        (∀ d ∈ key.firstInternalGapsRev, 1 ≤ d) ∧
        key.firstInternalGapsRev.sum +
          (key.laterRuns.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L)
    (hFidx : ∀ key ∈ F, ccr25GapRunKeyWordIndex key = idx)
    (x : LatticeConfiguration h) :
    (∑ key ∈ F,
      ccr25GapRunKeyDampedTail L lam β A key x) ≤
      finiteKernelWordApply (configBox h A L)
        ((ccr25PartitionWordLabels idx.1 idx.2).map
          (ccr25LabelKernel L lam β))
        (collisionIndicator (idx.2 (Fin.last idx.1))) x := by
  classical
  let ops := ccr25PartitionWordLabels idx.1 idx.2
  let paramCode (key : CCR25GapRunKey h) :=
    (ccr25GapRunKeyTimedCode key).map Prod.snd
  let paramSet := F.image paramCode
  have hlabelsJ (key : CCR25GapRunKey h) (hk : key ∈ F) :
      List.ofFn idx.2 =
        (ccr25GapRunKeyNormalize key).map CCR25GapRun.label := by
    have hparts := ccr25GapRunKeyWordIndex_components key idx.2
      (hFidx key hk)
    calc
      List.ofFn idx.2 = List.ofFn (ccr25GapRunKeyWord key) := hparts.2.symm
      _ = ccr25GapRunKeyLabels key := ccr25GapRunKeyWord_ofFn key
      _ = (ccr25GapRunKeyNormalize key).map CCR25GapRun.label := by
        simp [ccr25GapRunKeyLabels, ccr25GapRunKeyNormalize,
          ccr25GapRunKeyRestore]
  have hcodeLabels (key : CCR25GapRunKey h) (hk : key ∈ F) :
      (ccr25GapRunKeyTimedCode key).map Prod.fst = ops := by
    calc
      (ccr25GapRunKeyTimedCode key).map Prod.fst =
          ccr25GapRunOperatorWord (ccr25GapRunKeyNormalize key) :=
        ccr25GapRunKeyTimedCode_fst key
      _ = ccr25PartitionWordLabels idx.1 idx.2 :=
        ccr25GapRunOperatorWord_eq_partitionWordLabels
          (ccr25GapRunKeyNormalize key) idx.2 (hlabelsJ key hk)
  have hparamMem (key : CCR25GapRunKey h) (hk : key ∈ F) :
      paramCode key ∈ ccr25ParameterChoices
        (ops.map (ccr25RunOperatorParameterFamily L lam β)) := by
    have h := ccr25GapRunKey_parameters_mem_of_gapFacts lam β key
      (hFfacts key hk)
    change (ccr25GapRunKeyTimedCode key).map Prod.snd ∈
      ccr25ParameterChoices
        (((ccr25GapRunKeyTimedCode key).map Prod.fst).map
          (ccr25RunOperatorParameterFamily L lam β)) at h
    rw [hcodeLabels key hk] at h
    exact h
  have hparamInj : Set.InjOn paramCode (↑F : Set (CCR25GapRunKey h)) := by
    intro key hk key' hk' hparam
    have hlabels : ccr25GapRunKeyLabels key =
        ccr25GapRunKeyLabels key' := by
      calc
        ccr25GapRunKeyLabels key = List.ofFn (ccr25GapRunKeyWord key) :=
          (ccr25GapRunKeyWord_ofFn key).symm
        _ = List.ofFn idx.2 := (ccr25GapRunKeyWordIndex_components
          key idx.2 (hFidx key hk)).2
        _ = List.ofFn (ccr25GapRunKeyWord key') :=
          (ccr25GapRunKeyWordIndex_components
            key' idx.2 (hFidx key' hk')).2.symm
        _ = ccr25GapRunKeyLabels key' := ccr25GapRunKeyWord_ofFn key'
    exact ccr25GapRunKey_eq_of_labels_eq_params hlabels hparam
      (hFfacts key hk).1
      (hFfacts key' hk').1
  have htailEq (key : CCR25GapRunKey h) (hk : key ∈ F) :
      ccr25GapRunKeyDampedTail L lam β A key x =
        finiteKernelWordApply (configBox h A L)
          (ccr25ParameterChoiceKernelWord
            (ops.map (ccr25RunOperatorParameterFamily L lam β))
            (paramCode key))
          (collisionIndicator (idx.2 (Fin.last idx.1))) x := by
    have hlast : ccr25GapRunKeyLastLabel key =
        idx.2 (Fin.last idx.1) := by
      have hparts := ccr25GapRunKeyWordIndex_components key idx.2
        (hFidx key hk)
      have hwordLast :
          ccr25GapRunKeyWord key (Fin.last key.laterRuns.length) =
            idx.2 (Fin.last idx.1) := by
        have hlastList := congrArg List.getLast? hparts.2
        rw [List.getLast?_eq_getLast_of_ne_nil (by simp),
          List.getLast?_eq_getLast_of_ne_nil (by simp),
          List.getLast_ofFn_succ, List.getLast_ofFn_succ] at hlastList
        exact Option.some.inj hlastList
      calc
        ccr25GapRunKeyLastLabel key =
            ccr25GapRunKeyWord key (Fin.last key.laterRuns.length) :=
          (ccr25GapRunKeyWord_lastLabel key).symm
        _ = idx.2 (Fin.last idx.1) := hwordLast
    unfold ccr25GapRunKeyDampedTail
    rw [ccr25GapRunTimedCodeDampedKernelWord_eq_parameterChoiceKernelWord,
      hcodeLabels key hk, hlast]
  have hsumImage :
      (∑ key ∈ F, ccr25GapRunKeyDampedTail L lam β A key x) =
        ∑ params ∈ paramSet,
          finiteKernelWordApply (configBox h A L)
            (ccr25ParameterChoiceKernelWord
              (ops.map (ccr25RunOperatorParameterFamily L lam β)) params)
            (collisionIndicator (idx.2 (Fin.last idx.1))) x := by
    calc
      _ = ∑ key ∈ F,
          finiteKernelWordApply (configBox h A L)
            (ccr25ParameterChoiceKernelWord
              (ops.map (ccr25RunOperatorParameterFamily L lam β))
              (paramCode key))
            (collisionIndicator (idx.2 (Fin.last idx.1))) x := by
        apply Finset.sum_congr rfl
        intro key hk
        exact htailEq key hk
      _ = _ := by
        dsimp [paramSet]
        symm
        exact Finset.sum_image hparamInj
  have hparamSubset : paramSet ⊆
      ccr25ParameterChoices (ops.map (ccr25RunOperatorParameterFamily L lam β)) := by
    intro params hparams
    obtain ⟨key, hk, rfl⟩ := Finset.mem_image.mp hparams
    exact hparamMem key hk
  have hterminal : ∀ z, 0 ≤
      collisionIndicator (idx.2 (Fin.last idx.1)) z := by
    intro z
    by_cases hz : IsCollisionConfiguration (idx.2 (Fin.last idx.1)) z <;>
      simp [collisionIndicator, hz]
  rw [hsumImage]
  exact ccr25RunParameterChoices_subset_sum_le_hattedWord
    (configBox h A L) L lam β ops paramSet hparamSubset
    (collisionIndicator (idx.2 (Fin.last idx.1))) hterminal x

/-- Positive profile contributions in a key fiber obey the same timing-only bound. -/
theorem ccr25GapRunKeyFiber_contribution_le_wordIndex_of_gapFacts
    {h L : ℕ} (lam β : ℝ)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (idx : CCR25PartitionWordIndex h)
    (F : Finset (CCR25GapRunKey h))
    (hFfacts : ∀ key ∈ F,
      (∀ run ∈ key.laterRuns, 1 ≤ run.firstGap) ∧
        (∀ run ∈ key.laterRuns, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
        (∀ d ∈ key.firstInternalGapsRev, 1 ≤ d) ∧
        key.firstInternalGapsRev.sum +
          (key.laterRuns.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L)
    (hFidx : ∀ key ∈ F, ccr25GapRunKeyWordIndex key = idx) :
    (∑ key ∈ F,
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x) ≤
      Real.exp (lam * L) *
        ccr25WordIndexContribution (L := L) lam β A φ idx := by
  classical
  let B := configBox h A L
  let M := ∏ j : Fin (idx.1 + 1),
    |replicaPartitionDisorderMoment β (idx.2 j)|
  let C := Real.exp (lam * L)
  have hM : 0 ≤ M := by
    apply Finset.prod_nonneg
    intro j hj
    exact abs_nonneg _
  have hC : 0 ≤ C := Real.exp_nonneg _
  have hconst : 0 ≤ C * M := mul_nonneg hC hM
  have hfirstLabel (key : CCR25GapRunKey h) (hk : key ∈ F) :
      key.firstLabel = idx.2 0 := by
    have hparts := ccr25GapRunKeyWordIndex_components key idx.2
      (hFidx key hk)
    have hhead := congrArg List.head? hparts.2
    simpa [ccr25GapRunKeyWord] using hhead
  have hcoeff (key : CCR25GapRunKey h) (hk : key ∈ F) :
      ccr25GapRunKeyMomentCoefficient β key = M := by
    exact ccr25GapRunKeyMomentCoefficient_eq_word β key idx.2
      (hFidx key hk)
  have hboundaryNonneg (x : LatticeConfiguration h) :
      0 ≤ hattedReplicaBoundaryVector L (idx.2 0) A φ x :=
    hattedReplicaBoundaryVector_nonneg L (idx.2 0) A φ
      (fun y hy => hφ y) x
  have htailBound (x : LatticeConfiguration h) :
      (∑ key ∈ F, ccr25GapRunKeyDampedTail L lam β A key x) ≤
        finiteKernelWordApply B
          ((ccr25PartitionWordLabels idx.1 idx.2).map
            (ccr25LabelKernel L lam β))
          (collisionIndicator (idx.2 (Fin.last idx.1))) x :=
    ccr25GapRunKeyFiber_timedTail_le_of_gapFacts lam β A idx F
      hFfacts hFidx x
  have hsumCommon :
      (∑ key ∈ F,
        ∑ x ∈ B,
          hattedReplicaBoundaryVector L (idx.2 0) A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x) =
      ∑ x ∈ B,
        hattedReplicaBoundaryVector L (idx.2 0) A φ x *
          ∑ key ∈ F, ccr25GapRunKeyDampedTail L lam β A key x := by
    calc
      _ = ∑ x ∈ B,
          ∑ key ∈ F,
            hattedReplicaBoundaryVector L (idx.2 0) A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ B,
          hattedReplicaBoundaryVector L (idx.2 0) A φ x *
            ∑ key ∈ F, ccr25GapRunKeyDampedTail L lam β A key x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.mul_sum]
  have hpairBound :
      (∑ x ∈ B,
        hattedReplicaBoundaryVector L (idx.2 0) A φ x *
          ∑ key ∈ F, ccr25GapRunKeyDampedTail L lam β A key x) ≤
      ∑ x ∈ B,
        hattedReplicaBoundaryVector L (idx.2 0) A φ x *
          finiteKernelWordApply B
            ((ccr25PartitionWordLabels idx.1 idx.2).map
              (ccr25LabelKernel L lam β))
            (collisionIndicator (idx.2 (Fin.last idx.1))) x := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (htailBound x) (hboundaryNonneg x)
  have hpairEq :
      (∑ x ∈ B,
        hattedReplicaBoundaryVector L (idx.2 0) A φ x *
          finiteKernelWordApply B
            ((ccr25PartitionWordLabels idx.1 idx.2).map
              (ccr25LabelKernel L lam β))
            (collisionIndicator (idx.2 (Fin.last idx.1))) x) =
        ccr25FiniteWordPairing B L lam β idx.2
          (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator := by
    simp [ccr25FiniteWordPairing]
  calc
    _ = ∑ key ∈ F,
        C * M *
          ∑ x ∈ B,
            hattedReplicaBoundaryVector L (idx.2 0) A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x := by
      apply Finset.sum_congr rfl
      intro key hk
      rw [hcoeff key hk, hfirstLabel key hk]
    _ = C * M *
        ∑ key ∈ F,
          ∑ x ∈ B,
            hattedReplicaBoundaryVector L (idx.2 0) A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x := by
      rw [Finset.mul_sum]
    _ = C * M *
        ∑ x ∈ B,
          hattedReplicaBoundaryVector L (idx.2 0) A φ x *
            ∑ key ∈ F, ccr25GapRunKeyDampedTail L lam β A key x := by
      rw [hsumCommon]
    _ ≤ C * M *
        ∑ x ∈ B,
          hattedReplicaBoundaryVector L (idx.2 0) A φ x *
            finiteKernelWordApply B
              ((ccr25PartitionWordLabels idx.1 idx.2).map
                (ccr25LabelKernel L lam β))
              (collisionIndicator (idx.2 (Fin.last idx.1))) x :=
      mul_le_mul_of_nonneg_left hpairBound hconst
    _ = Real.exp (lam * L) *
        ccr25WordIndexContribution (L := L) lam β A φ idx := by
      simp only [C, M, B, ccr25WordIndexContribution]
      rw [hpairEq]
      ring

private theorem ccr25GapRunKeyFiber_contribution_le_wordIndex
    {h L : ℕ} (hh : 0 < h) (lam β : ℝ)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (idx : CCR25PartitionWordIndex h)
    (F : Finset (CCR25GapRunKey h))
    (hFkeys : F ⊆ ccr25FullSupportGapRunKeys h L)
    (hFidx : ∀ key ∈ F, ccr25GapRunKeyWordIndex key = idx) :
    (∑ key ∈ F,
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x) ≤
      Real.exp (lam * L) *
        ccr25WordIndexContribution (L := L) lam β A φ idx := by
  exact ccr25GapRunKeyFiber_contribution_le_wordIndex_of_gapFacts lam β A φ hφ idx F
    (fun key hk => ccr25FullSupportGapRunKey_gapFacts hh (hFkeys hk)) hFidx

private theorem ccr25GapRunKeySum_le_wordIndexSum
    {h L : ℕ} (hh : 0 < h) (lam β : ℝ)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ key ∈ ccr25FullSupportGapRunKeys h L,
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x) ≤
      Real.exp (lam * L) *
        ∑ idx ∈ ccr25AdmissibleWordIndices h L,
          ccr25WordIndexContribution (L := L) lam β A φ idx := by
  classical
  let keys := ccr25FullSupportGapRunKeys h L
  let indices := ccr25AdmissibleWordIndices h L
  let keyIndex : CCR25GapRunKey h → CCR25PartitionWordIndex h :=
    ccr25GapRunKeyWordIndex
  let keyContribution (key : CCR25GapRunKey h) :=
    Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
      ∑ x ∈ configBox h A L,
        hattedReplicaBoundaryVector L key.firstLabel A φ x *
          ccr25GapRunKeyDampedTail L lam β A key x
  have hmap : ∀ key ∈ keys, keyIndex key ∈ indices := by
    intro key hkey
    exact ccr25FullSupportGapRunKeyWordIndex_mem hh hkey
  have hfiberwise :
      (∑ key ∈ keys, keyContribution key) =
        ∑ idx ∈ indices,
          ∑ key ∈ keys.filter (fun key => keyIndex key = idx),
            keyContribution key := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfiber (idx : CCR25PartitionWordIndex h) (hidx : idx ∈ indices) :
      (∑ key ∈ keys.filter (fun key => keyIndex key = idx),
        keyContribution key) ≤
        Real.exp (lam * L) *
          ccr25WordIndexContribution (L := L) lam β A φ idx := by
    exact ccr25GapRunKeyFiber_contribution_le_wordIndex hh lam β A φ hφ
      idx (keys.filter fun key => keyIndex key = idx)
      (Finset.filter_subset _ _) (by
        intro key hk
        exact (Finset.mem_filter.mp hk).2)
  calc
    _ = ∑ idx ∈ indices,
        ∑ key ∈ keys.filter (fun key => keyIndex key = idx),
          keyContribution key := hfiberwise
    _ ≤ ∑ idx ∈ indices,
        Real.exp (lam * L) *
          ccr25WordIndexContribution (L := L) lam β A φ idx :=
      Finset.sum_le_sum fun idx hidx => hfiber idx hidx
    _ = Real.exp (lam * L) *
        ∑ idx ∈ indices,
          ccr25WordIndexContribution (L := L) lam β A φ idx := by
      rw [← Finset.mul_sum]

private theorem ccr25WordIndexSum_eq_admissibleWordSum
    {h L : ℕ} (lam β : ℝ) (A : Finset Site) (φ : Site → ℝ) :
    (∑ idx ∈ ccr25AdmissibleWordIndices h L,
      ccr25WordIndexContribution (L := L) lam β A φ idx) =
      ∑ n ∈ Finset.range L,
        ∑ J ∈ ccr25AdmissibleWords h n,
          (∏ j : Fin (n + 1),
            |replicaPartitionDisorderMoment β (J j)|) *
            ccr25FiniteWordPairing (configBox h A L) L lam β J
              (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator := by
  rw [ccr25AdmissibleWordIndices, Finset.sum_sigma]
  rfl

/-- Bound the full-support partition expansion by the finite CCR25 word sum,
grouping maximal collision runs by their labels and retained timing parameters. -/
theorem partitionSum_le_wordRuns {h : ℕ} (hh : 1 ≤ h)
    (β lam : ℝ) (hlam : 0 ≤ lam) (L : ℕ)
    (φ : Site → ℝ) (A : Finset Site) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ a : Fin h, φ (w a)) *
        ∑ I ∈ fullSupportSequences h L,
          (∏ n : Fin L, |replicaPartitionDisorderMoment β (I n)|) *
            replicaPathWeight (List.ofFn I) w) ≤
      Real.exp (lam * L) *
        ∑ n ∈ Finset.range L,
          ∑ J ∈ ccr25AdmissibleWords h n,
            (∏ j : Fin (n + 1),
              |replicaPartitionDisorderMoment β (J j)|) *
              ccr25FiniteWordPairing (configBox h A L) L lam β J
                (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator := by
  classical
  let W := Fintype.piFinset (fun _ : Fin h => A)
  let F := fullSupportSequences h L
  have hFubini :
      (∑ w ∈ W,
        (∏ a : Fin h, φ (w a)) *
          ∑ I ∈ F,
            (∏ n : Fin L, |replicaPartitionDisorderMoment β (I n)|) *
              replicaPathWeight (List.ofFn I) w) =
        ∑ I ∈ F,
          ∑ w ∈ W,
            (∏ a : Fin h, φ (w a)) *
              ((∏ n : Fin L,
                |replicaPartitionDisorderMoment β (I n)|) *
                replicaPathWeight (List.ofFn I) w) := by
    calc
      _ = ∑ w ∈ W,
          ∑ I ∈ F,
            (∏ a : Fin h, φ (w a)) *
              ((∏ n : Fin L,
                |replicaPartitionDisorderMoment β (I n)|) *
                replicaPathWeight (List.ofFn I) w) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mul_sum]
      _ = _ := Finset.sum_comm
  have hrunReindex :=
    fullSupport_startProfile_momentSum_eq_sum_gapRunPathImage
      (h := h) (L := L) β A φ
  calc
    _ = ∑ runs ∈ ccr25FullSupportGapRunStreams h L,
        ccr25GapRunStreamProfileScore β A φ runs := by
      calc
        _ = ∑ I ∈ fullSupportSequences h L,
            ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
              (∏ i : Fin h, φ (w i)) *
                ((∏ k : Fin L,
                  |replicaPartitionDisorderMoment β (I k)|) *
                  replicaPathWeight (List.ofFn I) w) := by
          simpa [W, F] using hFubini
        _ = ∑ runs ∈ ccr25FullSupportGapRunStreams h L,
            ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
              (∏ i : Fin h, φ (w i)) *
                ccr25GapRunPathWeight β ⊥ runs w := hrunReindex
        _ = _ := by rfl
    _ ≤ ∑ key ∈ ccr25FullSupportGapRunKeys h L,
        Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
          ∑ x ∈ configBox h A L,
            hattedReplicaBoundaryVector L key.firstLabel A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x :=
      ccr25FullSupportGapRunStreamSum_le_keyGapProfileSum
        (by omega) β lam hlam A φ hφ
    _ ≤ Real.exp (lam * L) *
        ∑ idx ∈ ccr25AdmissibleWordIndices h L,
          ccr25WordIndexContribution (L := L) lam β A φ idx :=
      ccr25GapRunKeySum_le_wordIndexSum (by omega) lam β A φ hφ
    _ = _ := by
      rw [ccr25WordIndexSum_eq_admissibleWordSum]

/-- Bound the absolute centered moment by the finite CCR25 word sum, using
the full-support active-moment expansion followed by `partitionSum_le_wordRuns`. -/
theorem abs_centeredMoment_profileP2Fun_le_wordRuns {h : ℕ}
    (hh : 1 ≤ h) (β lam : ℝ) (hlam : 0 ≤ lam)
    (L : ℕ) (φ : Site → ℝ) (A : Finset Site)
    (hφ : ∀ z, 0 ≤ φ z) (hA : ∀ z ∉ A, φ z = 0) :
    |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
      Real.exp (lam * L) *
        ∑ n ∈ Finset.range L,
          ∑ J ∈ ccr25AdmissibleWords h n,
            (∏ j : Fin (n + 1),
              |replicaPartitionDisorderMoment β (J j)|) *
              ccr25FiniteWordPairing (configBox h A L) L lam β J
                (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator := by
  classical
  have hactive := abs_centeredMoment_profileP2Fun_le_activeMomentSum
    (h := h) (L := L) β φ A hφ hA
  have hactiveEq :
      (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ∑ I ∈ fullSupportSequences h L,
            ccr25ActiveMomentKernelPathWeight β ⊥
              (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) w) =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ∑ I ∈ fullSupportSequences h L,
            (∏ k : Fin L,
              |replicaPartitionDisorderMoment β (I k)|) *
              replicaPathWeight (List.ofFn I) w := by
    apply Finset.sum_congr rfl
    intro w hw
    apply congrArg (fun x : ℝ => (∏ i : Fin h, φ (w i)) * x)
    apply Finset.sum_congr rfl
    intro I hI
    exact (absMoment_mul_replicaPathWeight_eq_activeMomentKernelPathWeight
      β I w).symm
  calc
    _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ∑ I ∈ fullSupportSequences h L,
            ccr25ActiveMomentKernelPathWeight β ⊥
              (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) w := hactive
    _ ≤ Real.exp (lam * L) *
        ∑ n ∈ Finset.range L,
          ∑ J ∈ ccr25AdmissibleWords h n,
            (∏ j : Fin (n + 1),
              |replicaPartitionDisorderMoment β (J j)|) *
              ccr25FiniteWordPairing (configBox h A L) L lam β J
                (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator := by
      rw [hactiveEq]
      exact partitionSum_le_wordRuns hh β lam hlam L φ A hφ

end

end Critical2DKPZ.MomentBounds

end
