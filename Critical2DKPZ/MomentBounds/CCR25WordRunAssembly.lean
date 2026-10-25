/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25ActiveMomentExpansion
public import Critical2DKPZ.MomentBounds.CCR25RunDurationFamilies
public import Critical2DKPZ.MomentBounds.CCR25RunBoxSupport
public import Critical2DKPZ.MomentBounds.CCR25GapCompositions
public import Critical2DKPZ.MomentBounds.CCR25RunBoxSupport
public import Mathlib.Tactic
public import Critical2DKPZ.MomentBounds.CCR25GaussianWordOperator
import Mathlib.Tactic

/-! # Grouping the first collision gap before the CCR25 word sum -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- A maximal-run record with its initial free gap removed. The initial gap
is summed into the left boundary vector; the interaction gaps and every later
free gap remain in the word parameter. -/
structure CCR25GapRunKey (h : ℕ) where
  firstLabel : ReplicaPartition h
  firstInternalGapsRev : List ℕ
  laterRuns : List (CCR25GapRun h)

/-- A total key map; the empty-list case will be excluded on full-support
paths with positive replica count. -/
def ccr25GapRunKeyOfD {h : ℕ} (runs : List (CCR25GapRun h)) :
    CCR25GapRunKey h :=
  match runs with
  | [] => ⟨⊥, [], []⟩
  | run :: rest => ⟨run.label, run.internalGapsRev, rest⟩

/-- Full-support run keys, with the initial free gap forgotten. -/
noncomputable def ccr25FullSupportGapRunKeys (h L : ℕ) :
    Finset (CCR25GapRunKey h) := by
  classical
  exact (ccr25FullSupportGapRunStreams h L).image ccr25GapRunKeyOfD

/-- A full-support partition sequence has a nonempty encoded gap-run list. -/
theorem ccr25FullSupportGapRunEncode_ne_nil {h L : ℕ} (hh : 0 < h)
    {I : Fin L → ReplicaPartition h}
    (hI : I ∈ fullSupportSequences h L) :
    ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) ≠ [] := by
  obtain ⟨r, J, hJ, hlabels⟩ := ccr25ActiveGapRun_admissibleWord hh hI
  intro hruns
  have hlen := congrArg List.length hlabels
  simp [hruns] at hlen

/-- Total list of run labels, including the distinguished first run. -/
def ccr25GapRunKeyLabels {h : ℕ} (key : CCR25GapRunKey h) :
    List (ReplicaPartition h) :=
  key.firstLabel :: key.laterRuns.map CCR25GapRun.label

/-- The key labels are the run labels of the list, when the list is nonempty. -/
theorem ccr25GapRunKeyLabels_eq_runLabels_ofD {h : ℕ}
    {runs : List (CCR25GapRun h)} (hruns : runs ≠ []) :
    ccr25GapRunKeyLabels (ccr25GapRunKeyOfD runs) =
      runs.map CCR25GapRun.label := by
  cases runs with
  | nil => exact (hruns rfl).elim
  | cons run rest => rfl

/-- The indexed word read from the normalized key's label list. -/
@[instance_reducible] def ccr25GapRunKeyWord {h : ℕ} (key : CCR25GapRunKey h) :
    Fin (key.laterRuns.length + 1) → ReplicaPartition h :=
  Fin.cases key.firstLabel (fun i => (key.laterRuns.get i).label)

private theorem ccr25ListOfFn_cons {α : Type*} {n : ℕ}
    (f : Fin (n + 1) → α) :
    List.ofFn f = f 0 :: List.ofFn (fun j : Fin n => f j.succ) := by
  let tail : Fin n → α := fun j => f j.succ
  have hcons : f = Fin.cons (f 0) tail := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  rw [hcons, List.ofFn_cons]
  simp [tail, Fin.cons_zero]

/-- The word of a key, as a list, is the list of its labels. -/
theorem ccr25GapRunKeyWord_ofFn {h : ℕ} (key : CCR25GapRunKey h) :
    List.ofFn (ccr25GapRunKeyWord key) = ccr25GapRunKeyLabels key := by
  rw [ccr25ListOfFn_cons]
  simp [ccr25GapRunKeyWord, ccr25GapRunKeyLabels]

/-- The key label list has one more entry than there are later runs. -/
theorem ccr25GapRunKeyLabels_length {h : ℕ} (key : CCR25GapRunKey h) :
    (ccr25GapRunKeyLabels key).length = key.laterRuns.length + 1 := by
  simp [ccr25GapRunKeyLabels]



/-- Restore a chosen first free gap to an initial-gap key. -/
def ccr25GapRunKeyRestore {h : ℕ} (key : CCR25GapRunKey h)
    (firstGap : ℕ) : List (CCR25GapRun h) :=
  ⟨key.firstLabel, firstGap, key.firstInternalGapsRev⟩ :: key.laterRuns

/-- The normalized run list attached to an initial-gap key. -/
def ccr25GapRunKeyNormalize {h : ℕ} (key : CCR25GapRunKey h) :
    List (CCR25GapRun h) := ccr25GapRunKeyRestore key 0

/-- Pair the free/interacting factors of a tail run list with their timed
parameters. -/
def ccr25GapRunTimedCodeFrom {h : ℕ} (previous : ReplicaPartition h) :
    List (CCR25GapRun h) → List (CCR25OperatorLabel h × CCR25RunDurationParam)
  | [] => []
  | run :: runs =>
      (.free previous run.label, .free (run.firstGap - 1)) ::
        (.interacting run.label,
          .interacting run.internalGapsRev.sum run.internalGapsRev) ::
        ccr25GapRunTimedCodeFrom run.label runs

private theorem ccr25GapRunTimedCodeFrom_fst {h : ℕ}
    (previous : ReplicaPartition h) (runs : List (CCR25GapRun h)) :
    (ccr25GapRunTimedCodeFrom previous runs).map Prod.fst =
      ccr25LabelListOperatorWordFrom previous (runs.map CCR25GapRun.label) := by
  induction runs generalizing previous with
  | nil => simp [ccr25GapRunTimedCodeFrom, ccr25LabelListOperatorWordFrom]
  | cons run runs ih =>
      simp [ccr25GapRunTimedCodeFrom, ccr25LabelListOperatorWordFrom, ih]

private theorem ccr25GapRunTimedCodeFrom_snd {h : ℕ}
    (previous : ReplicaPartition h) (runs : List (CCR25GapRun h)) :
    (ccr25GapRunTimedCodeFrom previous runs).map Prod.snd =
      ccr25GapRunParameterWordFrom runs := by
  induction runs generalizing previous with
  | nil => simp [ccr25GapRunTimedCodeFrom, ccr25GapRunParameterWordFrom]
  | cons run runs ih =>
      simp [ccr25GapRunTimedCodeFrom, ccr25GapRunParameterWordFrom, ih]

private theorem ccr25GapRunTimedCodeFrom_injective {h : ℕ} :
    ∀ (previous : ReplicaPartition h) (runs runs' : List (CCR25GapRun h)),
      (∀ run ∈ runs, 1 ≤ run.firstGap) →
      (∀ run ∈ runs', 1 ≤ run.firstGap) →
      ccr25GapRunTimedCodeFrom previous runs =
        ccr25GapRunTimedCodeFrom previous runs' →
      runs = runs' := by
  intro previous runs
  induction runs generalizing previous with
  | nil =>
      intro runs' _ _ hcode
      cases runs' with
      | nil => rfl
      | cons run rest => simp [ccr25GapRunTimedCodeFrom] at hcode
  | cons run runs ih =>
      intro runs' hpos hpos' hcode
      cases runs' with
      | nil => simp [ccr25GapRunTimedCodeFrom] at hcode
      | cons run' runs' =>
          simp only [ccr25GapRunTimedCodeFrom] at hcode
          rcases List.cons.inj hcode with ⟨hfree, hrest⟩
          rcases List.cons.inj hrest with ⟨hinter, htail⟩
          have hlabel : run.label = run'.label := by
            exact (CCR25OperatorLabel.free.inj
              (congrArg Prod.fst hfree)).2
          have hgapSub : run.firstGap - 1 = run'.firstGap - 1 := by
            exact CCR25RunDurationParam.free.inj (congrArg Prod.snd hfree)
          have hgap : run.firstGap = run'.firstGap := by
            have hp := hpos run (by simp)
            have hp' := hpos' run' (by simp)
            omega
          have hgaps : run.internalGapsRev = run'.internalGapsRev := by
            exact (CCR25RunDurationParam.interacting.inj
              (congrArg Prod.snd hinter)).2
          have hrun : run = run' := by
            cases run with
            | mk label gap gaps =>
                cases run' with
                | mk label' gap' gaps' =>
                    simp_all
          have hposTail : ∀ r ∈ runs, 1 ≤ r.firstGap := by
            intro r hr
            exact hpos r (List.mem_cons_of_mem _ hr)
          have hpos'Tail : ∀ r ∈ runs', 1 ≤ r.firstGap := by
            intro r hr
            exact hpos' r (List.mem_cons_of_mem _ hr)
          have htail' :
              ccr25GapRunTimedCodeFrom run.label runs =
                ccr25GapRunTimedCodeFrom run.label runs' := by
            simpa [hlabel] using htail
          have htailEq := ih run.label runs' hposTail hpos'Tail htail'
          simp [hrun, htailEq]

/-- Pair every operator in a normalized gap-run word with its exact timed
parameter. The pair list remembers all run labels and all noninitial gaps. -/
def ccr25GapRunKeyTimedCode {h : ℕ} (key : CCR25GapRunKey h) :
    List (CCR25OperatorLabel h × CCR25RunDurationParam) :=
  (.interacting key.firstLabel,
    .interacting key.firstInternalGapsRev.sum key.firstInternalGapsRev) ::
    ccr25GapRunTimedCodeFrom key.firstLabel key.laterRuns

/-- The final collision label in a normalized key. -/
@[instance_reducible] def ccr25GapRunKeyLastLabel {h : ℕ} (key : CCR25GapRunKey h) :
    ReplicaPartition h :=
  key.laterRuns.foldl (fun _ run => run.label) key.firstLabel

/-- The paired label/parameter code determines a normalized gap-run key
whenever every later run has a positive entry gap. -/
theorem ccr25GapRunKeyTimedCode_injective {h : ℕ}
    {key key' : CCR25GapRunKey h}
    (hpos : ∀ run ∈ key.laterRuns, 1 ≤ run.firstGap)
    (hpos' : ∀ run ∈ key'.laterRuns, 1 ≤ run.firstGap)
    (hcode : ccr25GapRunKeyTimedCode key = ccr25GapRunKeyTimedCode key') :
    key = key' := by
  cases key with
  | mk firstLabel firstGaps laterRuns =>
      cases key' with
      | mk firstLabel' firstGaps' laterRuns' =>
          simp only [ccr25GapRunKeyTimedCode] at hcode
          rcases List.cons.inj hcode with ⟨hfirst, htail⟩
          have hlabel : firstLabel = firstLabel' := by
            exact CCR25OperatorLabel.interacting.inj (congrArg Prod.fst hfirst)
          have hgaps : firstGaps = firstGaps' := by
            exact (CCR25RunDurationParam.interacting.inj
              (congrArg Prod.snd hfirst)).2
          have htail' :
              ccr25GapRunTimedCodeFrom firstLabel laterRuns =
                ccr25GapRunTimedCodeFrom firstLabel laterRuns' := by
            simpa [hlabel] using htail
          have hlater := ccr25GapRunTimedCodeFrom_injective
            firstLabel laterRuns laterRuns' hpos hpos' htail'
          simp [hlabel, hgaps, hlater]

/-- The operator labels of the key's timed code form the operator word of its normalization. -/
theorem ccr25GapRunKeyTimedCode_fst {h : ℕ} (key : CCR25GapRunKey h) :
    (ccr25GapRunKeyTimedCode key).map Prod.fst =
      ccr25GapRunOperatorWord (ccr25GapRunKeyNormalize key) := by
  cases key with
  | mk firstLabel firstGaps laterRuns =>
      simp [ccr25GapRunKeyTimedCode, ccr25GapRunKeyNormalize,
        ccr25GapRunKeyRestore, ccr25GapRunOperatorWord,
        ccr25LabelListOperatorWord, ccr25GapRunTimedCodeFrom_fst]







/-- A full-support gap-run key has an admissible word and fewer than `L` later runs. -/
theorem ccr25FullSupportGapRunKey_admissible_and_length_lt
    {h L : ℕ} (hh : 0 < h) {key : CCR25GapRunKey h}
    (hkey : key ∈ ccr25FullSupportGapRunKeys h L) :
    ccr25AdmissibleWord (ccr25GapRunKeyWord key) ∧
      key.laterRuns.length < L := by
  classical
  obtain ⟨runs, hruns, hkeyEq⟩ := Finset.mem_image.mp hkey
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hruns
  obtain ⟨r, J, hrL, hJ, hJlabels⟩ :=
    ccr25PositionedCollisionRuns_admissibleWord_length_le hh hI
  have hrunLabels :
      List.ofFn J =
        (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
          CCR25GapRun.label := by
    calc
      List.ofFn J = (ccr25PositionedCollisionRuns I).map Prod.fst := hJlabels
      _ = (ccr25GapRunEncode
          (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map CCR25GapRun.label :=
        (ccr25ActiveGapRun_labels_eq_positioned I).symm
  have hrunNonempty :
      ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) ≠ [] := by
    intro he
    have hnil : List.ofFn J = [] := by rw [hrunLabels, he]; rfl
    have hlen := congrArg List.length hnil
    simp at hlen
  have hkeyLabels := ccr25GapRunKeyLabels_eq_runLabels_ofD hrunNonempty
  have hlabelsKey : List.ofFn J = ccr25GapRunKeyLabels key := by
    calc
      List.ofFn J =
          (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
            CCR25GapRun.label := hrunLabels
      _ = ccr25GapRunKeyLabels
          (ccr25GapRunKeyOfD
            (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)))) :=
        hkeyLabels.symm
      _ = ccr25GapRunKeyLabels key := by rw [hkeyEq]
  have hnum : r = key.laterRuns.length := by
    have hlength : r + 1 = key.laterRuns.length + 1 := by
      calc
        r + 1 = (List.ofFn J).length := by simp
        _ = (ccr25GapRunKeyLabels key).length := by rw [hlabelsKey]
        _ = key.laterRuns.length + 1 := ccr25GapRunKeyLabels_length key
    omega
  subst r
  have hJ' : List.ofFn J = List.ofFn (ccr25GapRunKeyWord key) := by
    rw [ccr25GapRunKeyWord_ofFn]
    exact hlabelsKey
  have hword : J = ccr25GapRunKeyWord key := List.ofFn_inj.mp hJ'
  exact ⟨hword ▸ hJ, by omega⟩

/-- Run streams inherited from a horizon-length partition sequence have
positive event gaps and total gap duration at most the horizon. -/
theorem ccr25FullSupportGapRunStream_gapFacts {h L : ℕ}
    {runs : List (CCR25GapRun h)}
    (hruns : runs ∈ ccr25FullSupportGapRunStreams h L) :
    (∀ run ∈ runs, 1 ≤ run.firstGap) ∧
      (∀ run ∈ runs, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
      (runs.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
  classical
  simp only [ccr25FullSupportGapRunStreams, Finset.mem_image] at hruns
  obtain ⟨I, hI, rfl⟩ := hruns
  have hpos : ∀ e ∈ ccr25ActiveGapEncodeFrom 0 (List.ofFn I),
      1 ≤ e.1 := by
    intro e he
    exact ccr25ActiveGapEncodeFrom_gap_pos 0 (List.ofFn I) (e := e) he
  have hrunPos : ∀ run ∈ ccr25GapRunEncode
      (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)),
      ∀ d ∈ run.firstGap :: run.internalGapsRev, 1 ≤ d :=
    ccr25GapRunEncode_gap_pos _ hpos
  have hfirst : ∀ run ∈ ccr25GapRunEncode
      (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)), 1 ≤ run.firstGap := by
    intro run hr
    exact hrunPos run hr run.firstGap (by simp)
  have hinner : ∀ run ∈ ccr25GapRunEncode
      (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)),
      ∀ d ∈ run.internalGapsRev, 1 ≤ d := by
    intro run hr d hd
    exact hrunPos run hr d (by simp [hd])
  have hsum :
      ((ccr25GapRunEncode
        (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
          fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
    rw [← ccr25GapRunExpand_gapSum, ccr25GapRunExpand_encode]
    simpa using
      (ccr25ActiveGapEncodeFrom_sum_le (gap := 0) (List.ofFn I))
  exact ⟨hfirst, hinner, hsum⟩

private theorem ccr25NatLeSumMapOfMem {α : Type*} (f : α → ℕ) :
    ∀ (xs : List α) {a : α}, a ∈ xs → f a ≤ (xs.map f).sum := by
  intro xs
  induction xs with
  | nil => intro a ha; simp at ha
  | cons b xs ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp
      · have htail := ih ha
        simp only [List.map_cons, List.sum_cons]
        omega

/-- The key of a full-support run stream retains positive internal gaps and
all positive later free intervals, with their total duration bounded by L. -/
theorem ccr25FullSupportGapRunKey_gapFacts {h L : ℕ}
    (hh : 0 < h) {key : CCR25GapRunKey h}
    (hkey : key ∈ ccr25FullSupportGapRunKeys h L) :
    (∀ run ∈ key.laterRuns, 1 ≤ run.firstGap) ∧
      (∀ run ∈ key.laterRuns, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
      (∀ d ∈ key.firstInternalGapsRev, 1 ≤ d) ∧
      key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run =>
          run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
  classical
  obtain ⟨runs, hruns, hkeyEq⟩ := Finset.mem_image.mp hkey
  have hnonempty : runs ≠ [] := by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hruns
    exact ccr25FullSupportGapRunEncode_ne_nil hh hI
  obtain ⟨first, later, rfl⟩ := List.exists_cons_of_ne_nil hnonempty
  have hfacts := ccr25FullSupportGapRunStream_gapFacts hruns
  have hsumKey : first.internalGapsRev.sum +
      (later.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
    have hsum := hfacts.2.2
    simp only [List.map_cons, List.sum_cons] at hsum
    omega
  simp only [ccr25GapRunKeyOfD] at hkeyEq
  rcases hkeyEq with ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro run hr
    exact hfacts.1 run (by simp [hr])
  · intro run hr d hd
    exact hfacts.2.1 run (by simp [hr]) d hd
  · intro d hd
    exact hfacts.2.1 first (by simp) d (by simp [hd])
  · simpa [ccr25GapRunKeyOfD] using hsumKey

private theorem ccr25GapRunParameterWordFrom_mem_for_key {h : ℕ}
    (L : ℕ) (lam β : ℝ) :
    ∀ (previous : ReplicaPartition h) (runs : List (CCR25GapRun h)),
      (∀ run ∈ runs, 1 ≤ run.firstGap) →
      (∀ run ∈ runs, run.firstGap ≤ L) →
      (∀ run ∈ runs, ∀ d ∈ run.internalGapsRev, 1 ≤ d) →
      (∀ run ∈ runs, run.internalGapsRev.sum ≤ L) →
      ccr25GapRunParameterWordFrom runs ∈
        ccr25ParameterChoices
          ((ccr25GapRunOperatorWordFrom previous runs).map
            (ccr25RunOperatorParameterFamily L lam β)) := by
  intro previous runs
  induction runs generalizing previous with
  | nil => intro _ _ _ _; simp [ccr25GapRunParameterWordFrom,
      ccr25GapRunOperatorWordFrom, ccr25LabelListOperatorWordFrom,
      ccr25ParameterChoices]
  | cons run runs ih =>
      intro hfirst hfirstL hinner hinnerL
      have hfirst' := hfirst run (by simp)
      have hfirstL' := hfirstL run (by simp)
      have hinner' : ∀ d ∈ run.internalGapsRev, 1 ≤ d :=
        fun d hd => hinner run (by simp) d hd
      have hinnerL' := hinnerL run (by simp)
      have htail := ih run.label
        (fun r hr => hfirst r (by simp [hr]))
        (fun r hr => hfirstL r (by simp [hr]))
        (fun r hr d hd => hinner r (by simp [hr]) d hd)
        (fun r hr => hinnerL r (by simp [hr]))
      have hfree : CCR25RunDurationParam.free (run.firstGap - 1) ∈
          (ccr25RunOperatorParameterFamily L lam β
            (.free previous run.label)).parameters := by
        change CCR25RunDurationParam.free (run.firstGap - 1) ∈
          (Finset.range L).image CCR25RunDurationParam.free
        apply Finset.mem_image.mpr
        refine ⟨run.firstGap - 1, ?_, rfl⟩
        simp only [Finset.mem_range]
        omega
      have hinter : CCR25RunDurationParam.interacting
          run.internalGapsRev.sum run.internalGapsRev ∈
          ccr25InteractingRunParameters L :=
        ccr25InteractingRunParameter_mem L run.internalGapsRev
          hinner' hinnerL'
      simp only [ccr25GapRunOperatorWordFrom,
        ccr25LabelListOperatorWordFrom, ccr25GapRunParameterWordFrom,
        List.map_cons]
      rw [ccr25ParameterChoices]
      apply Finset.mem_biUnion.mpr
      refine ⟨CCR25RunDurationParam.free (run.firstGap - 1), hfree, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨CCR25RunDurationParam.interacting run.internalGapsRev.sum
        run.internalGapsRev :: ccr25GapRunParameterWordFrom runs, ?_, rfl⟩
      rw [ccr25ParameterChoices]
      apply Finset.mem_biUnion.mpr
      refine ⟨CCR25RunDurationParam.interacting run.internalGapsRev.sum
        run.internalGapsRev, hinter, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨ccr25GapRunParameterWordFrom runs, htail, rfl⟩

/-- The operator and duration projections of a key with positive bounded gaps
form one member of the exact finite CCR25 parameter-choice family. -/
theorem ccr25GapRunKey_parameters_mem_of_gapFacts {h L : ℕ}
    (lam β : ℝ) (key : CCR25GapRunKey h)
    (hfacts : (∀ run ∈ key.laterRuns, 1 ≤ run.firstGap) ∧
      (∀ run ∈ key.laterRuns, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
      (∀ d ∈ key.firstInternalGapsRev, 1 ≤ d) ∧
      key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L) :
    (ccr25GapRunKeyTimedCode key).map Prod.snd ∈
      ccr25ParameterChoices
        (((ccr25GapRunKeyTimedCode key).map Prod.fst).map
          (ccr25RunOperatorParameterFamily L lam β)) := by
  have htail := ccr25GapRunParameterWordFrom_mem_for_key L lam β
    key.firstLabel key.laterRuns hfacts.1
    (fun run hr => by
      have h := ccr25NatLeSumMapOfMem
        (fun r : CCR25GapRun h => r.firstGap + r.internalGapsRev.sum)
        key.laterRuns hr
      omega)
    hfacts.2.1
    (fun run hr => by
      have h := ccr25NatLeSumMapOfMem
        (fun r : CCR25GapRun h => r.firstGap + r.internalGapsRev.sum)
        key.laterRuns hr
      omega)
  have hfirst : CCR25RunDurationParam.interacting
      key.firstInternalGapsRev.sum key.firstInternalGapsRev ∈
      ccr25InteractingRunParameters L :=
    ccr25InteractingRunParameter_mem L key.firstInternalGapsRev
      hfacts.2.2.1 (by omega)
  simp only [ccr25GapRunKeyTimedCode, List.map_cons,
    ccr25GapRunTimedCodeFrom_fst, ccr25GapRunTimedCodeFrom_snd]
  rw [ccr25ParameterChoices]
  apply Finset.mem_biUnion.mpr
  refine ⟨CCR25RunDurationParam.interacting
      key.firstInternalGapsRev.sum key.firstInternalGapsRev, hfirst, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨ccr25GapRunParameterWordFrom key.laterRuns, htail, rfl⟩


/-- The undamped operator kernel attached to an explicitly timed run-code
entry. -/
def ccr25GapRunTimedCodeKernel {h : ℕ} (β : ℝ)
    (entry : CCR25OperatorLabel h × CCR25RunDurationParam) :
    LatticeConfiguration h → LatticeConfiguration h → ℝ :=
  ccr25RunDurationKernel 0 β entry.1 entry.2

/-- The undamped finite kernel word of a timed run code. -/
def ccr25GapRunTimedCodeKernelWord {h : ℕ} (β : ℝ)
    (code : List (CCR25OperatorLabel h × CCR25RunDurationParam)) :
    List (LatticeConfiguration h → LatticeConfiguration h → ℝ) :=
  code.map (ccr25GapRunTimedCodeKernel β)

/-- The multiplicative disorder-moment coefficient of a run list. -/
def ccr25GapRunMomentProduct {h : ℕ} (β : ℝ)
    (runs : List (CCR25GapRun h)) : ℝ :=
  (runs.map fun run => |replicaPartitionDisorderMoment β run.label|).prod

/-- Total interaction duration remembered by one explicit timed operator
parameter. -/
def ccr25RunDurationParamInteractionCost : CCR25RunDurationParam → ℕ
  | .free _ => 0
  | .interacting d _ => d

/-- Total Laplace cost carried by a paired operator/parameter code. -/
def ccr25GapRunTimedCodeInteractionCost {h : ℕ}
    (code : List (CCR25OperatorLabel h × CCR25RunDurationParam)) : ℕ :=
  (code.map fun entry => ccr25RunDurationParamInteractionCost entry.2).sum

/-- The interaction cost of the timed code of a run tail is the total of its internal gaps. -/
theorem ccr25GapRunTimedCodeInteractionCostFrom_eq {h : ℕ}
    (previous : ReplicaPartition h) (runs : List (CCR25GapRun h)) :
    ccr25GapRunTimedCodeInteractionCost
        (ccr25GapRunTimedCodeFrom previous runs) =
      (runs.map fun run => run.internalGapsRev.sum).sum := by
  induction runs generalizing previous with
  | nil => rfl
  | cons run runs ih =>
      simp only [ccr25GapRunTimedCodeFrom,
        ccr25GapRunTimedCodeInteractionCost, List.map_cons,
        ccr25RunDurationParamInteractionCost, List.sum_cons,
        zero_add]
      change run.internalGapsRev.sum +
          ccr25GapRunTimedCodeInteractionCost
            (ccr25GapRunTimedCodeFrom run.label runs) = _
      rw [ih run.label]

/-- The interaction cost of a key's timed code is the sum of its internal gaps, first and later. -/
theorem ccr25GapRunKeyTimedCodeInteractionCost_eq {h : ℕ}
    (key : CCR25GapRunKey h) :
    ccr25GapRunTimedCodeInteractionCost (ccr25GapRunKeyTimedCode key) =
      key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run => run.internalGapsRev.sum).sum := by
  simp only [ccr25GapRunKeyTimedCode,
    ccr25GapRunTimedCodeInteractionCost,
    ccr25RunDurationParamInteractionCost, List.map_cons, List.sum_cons]
  change key.firstInternalGapsRev.sum +
      ccr25GapRunTimedCodeInteractionCost
        (ccr25GapRunTimedCodeFrom key.firstLabel key.laterRuns) = _
  rw [ccr25GapRunTimedCodeInteractionCostFrom_eq]

/-- The damped kernel of a timed code entry, using the same Laplace parameter
as the finite CCR25 operator family. -/
def ccr25GapRunTimedCodeDampedKernel {h : ℕ} (lam β : ℝ)
    (entry : CCR25OperatorLabel h × CCR25RunDurationParam) :
    LatticeConfiguration h → LatticeConfiguration h → ℝ :=
  ccr25RunDurationKernel lam β entry.1 entry.2

/-- The damped finite word carried by an explicit timed code. -/
def ccr25GapRunTimedCodeDampedKernelWord {h : ℕ} (lam β : ℝ)
    (code : List (CCR25OperatorLabel h × CCR25RunDurationParam)) :
    List (LatticeConfiguration h → LatticeConfiguration h → ℝ) :=
  code.map (ccr25GapRunTimedCodeDampedKernel lam β)

/-- At `lam = 0` the run-duration kernel is `exp (lam * cost)` times the kernel at `lam`. -/
theorem ccr25RunDurationKernel_zero_eq_exp_cost_mul_damped {h : ℕ}
    (lam β : ℝ) (op : CCR25OperatorLabel h) (p : CCR25RunDurationParam)
    (z x : LatticeConfiguration h) :
    ccr25RunDurationKernel 0 β op p z x =
      Real.exp (lam * (ccr25RunDurationParamInteractionCost p : ℝ)) *
        ccr25RunDurationKernel lam β op p z x := by
  cases op with
  | free I J =>
      cases p <;>
        simp [ccr25RunDurationKernel,
          ccr25RunDurationParamInteractionCost]
  | interacting I =>
      cases p with
      | free d => simp [ccr25RunDurationKernel]
      | interacting d gaps =>
          simp only [ccr25RunDurationKernel,
            ccr25RunDurationParamInteractionCost]
          simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
          have hexp : Real.exp (lam * (d : ℝ)) *
              Real.exp (-(lam * (d : ℝ))) = 1 := by
            rw [← Real.exp_add]
            rw [add_neg_cancel, Real.exp_zero]
          calc
            _ = (Real.exp (lam * (d : ℝ)) *
                  Real.exp (-(lam * (d : ℝ)))) *
                    ccr25TimedInteractionRunAbs β I gaps z x := by
                      rw [hexp]
                      simp
            _ = _ := by ring

/-- Undamped application of a timed code equals its damped application times
the exponential of the total interaction duration. -/
theorem finiteKernelWordApply_undampedTimedCode_eq_exp_mul_damped
    {h : ℕ} (s : Finset (LatticeConfiguration h)) (lam β : ℝ)
    (code : List (CCR25OperatorLabel h × CCR25RunDurationParam))
    (f : LatticeConfiguration h → ℝ) (z : LatticeConfiguration h) :
    finiteKernelWordApply s
        (ccr25GapRunTimedCodeKernelWord β code) f z =
      Real.exp (lam * (ccr25GapRunTimedCodeInteractionCost code : ℝ)) *
        finiteKernelWordApply s
          (ccr25GapRunTimedCodeDampedKernelWord lam β code) f z := by
  induction code generalizing f z with
  | nil => simp [ccr25GapRunTimedCodeKernelWord,
      ccr25GapRunTimedCodeDampedKernelWord,
      ccr25GapRunTimedCodeInteractionCost]
  | cons entry code ih =>
      simp only [ccr25GapRunTimedCodeKernelWord,
        ccr25GapRunTimedCodeDampedKernelWord,
        ccr25GapRunTimedCodeInteractionCost, List.map_cons,
        ccr25GapRunTimedCodeInteractionCost]
      simp only [finiteKernelWordApply]
      calc
        (∑ y ∈ s,
            ccr25GapRunTimedCodeKernel β entry z y *
              finiteKernelWordApply s
                (ccr25GapRunTimedCodeKernelWord β code) f y) =
          ∑ y ∈ s,
            (Real.exp
                (lam * (ccr25RunDurationParamInteractionCost entry.2 : ℝ)) *
              ccr25RunDurationKernel lam β entry.1 entry.2 z y) *
              (Real.exp (lam *
                (ccr25GapRunTimedCodeInteractionCost code : ℝ)) *
                finiteKernelWordApply s
                  (ccr25GapRunTimedCodeDampedKernelWord lam β code) f y) := by
                apply Finset.sum_congr rfl
                intro y hy
                change ccr25RunDurationKernel 0 β entry.1 entry.2 z y *
                    finiteKernelWordApply s
                      (ccr25GapRunTimedCodeKernelWord β code) f y = _
                rw [ccr25RunDurationKernel_zero_eq_exp_cost_mul_damped,
                  ih]
        _ = Real.exp (lam *
              ((ccr25RunDurationParamInteractionCost entry.2 : ℝ) +
                (ccr25GapRunTimedCodeInteractionCost code : ℝ))) *
              ∑ y ∈ s,
                ccr25RunDurationKernel lam β entry.1 entry.2 z y *
                  finiteKernelWordApply s
                    (ccr25GapRunTimedCodeDampedKernelWord lam β code) f y := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y hy
                calc
                  _ = (Real.exp (lam *
                        (ccr25RunDurationParamInteractionCost entry.2 : ℝ)) *
                      Real.exp (lam *
                        (ccr25GapRunTimedCodeInteractionCost code : ℝ))) *
                        (ccr25RunDurationKernel lam β entry.1 entry.2 z y *
                          finiteKernelWordApply s
                            (ccr25GapRunTimedCodeDampedKernelWord lam β code)
                            f y) := by ring
                  _ = _ := by
                    rw [← Real.exp_add]
                    congr 1
                    ring
        _ = Real.exp (lam *
              (ccr25GapRunTimedCodeInteractionCost (entry :: code) : ℝ)) *
              finiteKernelWordApply s
                (ccr25GapRunTimedCodeDampedKernelWord lam β (entry :: code))
                f z := by
                simp [ccr25GapRunTimedCodeInteractionCost,
                  ccr25GapRunTimedCodeDampedKernelWord,
                  ccr25GapRunTimedCodeDampedKernel,
                  finiteKernelWordApply, List.map_cons, List.sum_cons]

/-- Every timed interaction run ends on its label's collision stratum. -/
theorem ccr25TimedInteractionRunAbs_zero_of_not_collision_right {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) :
    ∀ (gaps : List ℕ) (z x : LatticeConfiguration h),
      ¬ IsCollisionConfiguration I x →
        ccr25TimedInteractionRunAbs β I gaps z x = 0 := by
  intro gaps
  induction gaps with
  | nil =>
      intro z x hx
      simp [ccr25TimedInteractionRunAbs, hx]
  | cons d gaps ih =>
      intro z x hx
      simp [ccr25TimedInteractionRunAbs, freeReplicaKernel, hx]

/-- A finite kernel word whose last kernel is supported on a collision
stratum is unchanged when its terminal one-vector is replaced by that
stratum's indicator. -/
theorem finiteKernelWordApply_append_terminal_collisionIndicator
    {h : ℕ} (s : Finset (LatticeConfiguration h))
    (Ks : List (LatticeConfiguration h → LatticeConfiguration h → ℝ))
    (K : LatticeConfiguration h → LatticeConfiguration h → ℝ)
    (I : ReplicaPartition h)
    (hK : ∀ x y, ¬ IsCollisionConfiguration I y → K x y = 0) :
    ∀ x,
      finiteKernelWordApply s (Ks ++ [K]) (fun _ => 1) x =
        finiteKernelWordApply s (Ks ++ [K]) (collisionIndicator I) x := by
  induction Ks with
  | nil =>
      intro x
      simp only [List.nil_append, finiteKernelWordApply]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hc : IsCollisionConfiguration I y
      · simp [collisionIndicator, hc]
      · simp [collisionIndicator, hc, hK x y hc]
  | cons head tail ih =>
      intro x
      simp only [List.cons_append, finiteKernelWordApply]
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      exact ih y

private theorem ccr25TsumFreeReplicaKernel_eq_sum_configBox_of_le
    {h L r d : ℕ} {A : Finset Site} {z : LatticeConfiguration h}
    (hz : z ∈ configBox h A r) (hbound : r + d ≤ L)
    (I J : ReplicaPartition h) (f : LatticeConfiguration h → ℝ) :
    (∑' x, freeReplicaKernel d I J z x * f x) =
      ∑ x ∈ configBox h A L, freeReplicaKernel d I J z x * f x := by
  apply tsum_eq_sum
  intro x hx
  have hxsmall : x ∉ configBox h A (r + d) := by
    intro hxsmall
    exact hx (ccr25ConfigBox_mono hbound hxsmall)
  rw [freeReplicaKernel_zero_of_not_configBox hz hxsmall I J]
  simp

private theorem ccr25TsumTimedInteractionRunAbs_eq_sum_configBox_of_le
    {h L r : ℕ} {A : Finset Site} (β : ℝ) (I : ReplicaPartition h)
    (gaps : List ℕ) {z : LatticeConfiguration h}
    (hz : z ∈ configBox h A r)
    (hbound : r + gaps.sum ≤ L) (f : LatticeConfiguration h → ℝ) :
    (∑' x, ccr25TimedInteractionRunAbs β I gaps z x * f x) =
      ∑ x ∈ configBox h A L,
        ccr25TimedInteractionRunAbs β I gaps z x * f x := by
  apply tsum_eq_sum
  intro x hx
  have hxsmall : x ∉ configBox h A (r + gaps.sum) := by
    intro hxsmall
    exact hx (ccr25ConfigBox_mono hbound hxsmall)
  rw [ccr25TimedInteractionRunAbs_zero_of_not_configBox β I gaps hz hxsmall]
  simp

/-- A timed maximal-run path whose total remaining duration fits in the
spatial horizon equals its finite-box timed CCR25 word. The box restriction
is retained at every intermediate configuration. -/
theorem ccr25GapRunPathWeight_eq_finiteBox_timedCode {h L : ℕ}
    (β : ℝ) (A : Finset Site) :
    ∀ (previous : ReplicaPartition h) (runs : List (CCR25GapRun h))
      (r : ℕ) (z : LatticeConfiguration h),
      (∀ run ∈ runs, 1 ≤ run.firstGap) →
      z ∈ configBox h A r →
      r + (runs.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L →
      ccr25GapRunPathWeight β previous runs z =
        ccr25GapRunMomentProduct β runs *
          finiteKernelWordApply (configBox h A L)
            (ccr25GapRunTimedCodeKernelWord β
              (ccr25GapRunTimedCodeFrom previous runs))
            (fun _ => 1) z := by
  intro previous runs
  induction runs generalizing previous with
  | nil =>
      intro r z _ _ _
      simp [ccr25GapRunPathWeight, ccr25GapRunMomentProduct,
        ccr25GapRunTimedCodeKernelWord, ccr25GapRunTimedCodeFrom,
        finiteKernelWordApply]
  | cons run runs ih =>
      intro r z hgap hz hbudget
      have hrunpos : 1 ≤ run.firstGap := hgap run (by simp)
      have hgapTail : ∀ tail ∈ runs, 1 ≤ tail.firstGap := by
        intro tail htail
        exact hgap tail (List.mem_cons_of_mem _ htail)
      have hbudget' : r + (run.firstGap + run.internalGapsRev.sum) +
          (runs.map fun tail => tail.firstGap + tail.internalGapsRev.sum).sum ≤ L := by
        simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hbudget
      have hfreeBound : r + run.firstGap ≤ L := by omega
      have hinterBound : r + run.firstGap + run.internalGapsRev.sum ≤ L := by omega
      let r' := r + run.firstGap + run.internalGapsRev.sum
      have htailBudget : r' +
          (runs.map fun tail => tail.firstGap + tail.internalGapsRev.sum).sum ≤ L := by
        dsimp [r']
        omega
      have htailEq : ∀ y ∈ configBox h A r',
          ccr25GapRunPathWeight β run.label runs y =
            ccr25GapRunMomentProduct β runs *
              finiteKernelWordApply (configBox h A L)
                (ccr25GapRunTimedCodeKernelWord β
                  (ccr25GapRunTimedCodeFrom run.label runs))
                (fun _ => 1) y := by
        intro y hy
        exact ih run.label r' y hgapTail hy htailBudget
      have hinner (x : LatticeConfiguration h) :
          freeReplicaKernel run.firstGap previous run.label z x *
            (∑' y, ccr25TimedInteractionRunAbs β run.label
                run.internalGapsRev x y *
              ccr25GapRunPathWeight β run.label runs y) =
          ccr25GapRunMomentProduct β runs *
            (freeReplicaKernel run.firstGap previous run.label z x *
              ∑ y ∈ configBox h A L,
                ccr25TimedInteractionRunAbs β run.label
                    run.internalGapsRev x y *
                  finiteKernelWordApply (configBox h A L)
                    (ccr25GapRunTimedCodeKernelWord β
                      (ccr25GapRunTimedCodeFrom run.label runs))
                    (fun _ => 1) y) := by
        by_cases hx : x ∈ configBox h A (r + run.firstGap)
        · have hrunTsum := ccr25TsumTimedInteractionRunAbs_eq_sum_configBox_of_le
            β run.label run.internalGapsRev hx (by omega)
            (ccr25GapRunPathWeight β run.label runs)
          rw [hrunTsum]
          have hsum :
              (∑ y ∈ configBox h A L,
                ccr25TimedInteractionRunAbs β run.label
                    run.internalGapsRev x y *
                  ccr25GapRunPathWeight β run.label runs y) =
                ccr25GapRunMomentProduct β runs *
                  ∑ y ∈ configBox h A L,
                    ccr25TimedInteractionRunAbs β run.label
                        run.internalGapsRev x y *
                      finiteKernelWordApply (configBox h A L)
                        (ccr25GapRunTimedCodeKernelWord β
                          (ccr25GapRunTimedCodeFrom run.label runs))
                        (fun _ => 1) y := by
            calc
              _ = ∑ y ∈ configBox h A L,
                    ccr25TimedInteractionRunAbs β run.label
                        run.internalGapsRev x y *
                      (ccr25GapRunMomentProduct β runs *
                        finiteKernelWordApply (configBox h A L)
                          (ccr25GapRunTimedCodeKernelWord β
                            (ccr25GapRunTimedCodeFrom run.label runs))
                          (fun _ => 1) y) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    by_cases hy' : y ∈ configBox h A r'
                    · rw [htailEq y hy']
                    · have hzero := ccr25TimedInteractionRunAbs_zero_of_not_configBox
                        β run.label run.internalGapsRev hx hy'
                      rw [hzero]
                      simp
              _ = ccr25GapRunMomentProduct β runs *
                    ∑ y ∈ configBox h A L,
                      ccr25TimedInteractionRunAbs β run.label
                          run.internalGapsRev x y *
                        finiteKernelWordApply (configBox h A L)
                          (ccr25GapRunTimedCodeKernelWord β
                            (ccr25GapRunTimedCodeFrom run.label runs))
                          (fun _ => 1) y := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
          rw [hsum]
          ring
        · have hzero := freeReplicaKernel_zero_of_not_configBox hz hx
            previous run.label
          rw [hzero]
          simp
      have houter := ccr25TsumFreeReplicaKernel_eq_sum_configBox_of_le
        hz hfreeBound previous run.label
        (fun x => ∑' y, ccr25TimedInteractionRunAbs β run.label
            run.internalGapsRev x y * ccr25GapRunPathWeight β run.label runs y)
      calc
        ccr25GapRunPathWeight β previous (run :: runs) z =
            |replicaPartitionDisorderMoment β run.label| *
              ∑' x, freeReplicaKernel run.firstGap previous run.label z x *
                (∑' y, ccr25TimedInteractionRunAbs β run.label
                    run.internalGapsRev x y *
                  ccr25GapRunPathWeight β run.label runs y) := by
                    simp [ccr25GapRunPathWeight]
        _ = |replicaPartitionDisorderMoment β run.label| *
              ∑ x ∈ configBox h A L,
                freeReplicaKernel run.firstGap previous run.label z x *
                  (∑' y, ccr25TimedInteractionRunAbs β run.label
                      run.internalGapsRev x y *
                    ccr25GapRunPathWeight β run.label runs y) := by
                    rw [houter]
        _ = |replicaPartitionDisorderMoment β run.label| *
              ∑ x ∈ configBox h A L,
                ccr25GapRunMomentProduct β runs *
                  (freeReplicaKernel run.firstGap previous run.label z x *
                    ∑ y ∈ configBox h A L,
                      ccr25TimedInteractionRunAbs β run.label
                          run.internalGapsRev x y *
                        finiteKernelWordApply (configBox h A L)
                          (ccr25GapRunTimedCodeKernelWord β
                            (ccr25GapRunTimedCodeFrom run.label runs))
                          (fun _ => 1) y) := by
                    apply congrArg (fun v : ℝ =>
                      |replicaPartitionDisorderMoment β run.label| * v)
                    apply Finset.sum_congr rfl
                    intro x hx
                    exact hinner x
        _ = (|replicaPartitionDisorderMoment β run.label| *
              ccr25GapRunMomentProduct β runs) *
              ∑ x ∈ configBox h A L,
                freeReplicaKernel run.firstGap previous run.label z x *
                  ∑ y ∈ configBox h A L,
                    ccr25TimedInteractionRunAbs β run.label
                        run.internalGapsRev x y *
                      finiteKernelWordApply (configBox h A L)
                        (ccr25GapRunTimedCodeKernelWord β
                          (ccr25GapRunTimedCodeFrom run.label runs))
                        (fun _ => 1) y := by
                    calc
                      _ = |replicaPartitionDisorderMoment β run.label| *
                          (ccr25GapRunMomentProduct β runs *
                            ∑ x ∈ configBox h A L,
                              freeReplicaKernel run.firstGap previous run.label z x *
                                ∑ y ∈ configBox h A L,
                                  ccr25TimedInteractionRunAbs β run.label
                                      run.internalGapsRev x y *
                                    finiteKernelWordApply (configBox h A L)
                                      (ccr25GapRunTimedCodeKernelWord β
                                        (ccr25GapRunTimedCodeFrom run.label runs))
                                      (fun _ => 1) y) := by
                            congr 1
                            rw [Finset.mul_sum]
                      _ = _ := by ring
        _ = ccr25GapRunMomentProduct β (run :: runs) *
              finiteKernelWordApply (configBox h A L)
                (ccr25GapRunTimedCodeKernelWord β
                  (ccr25GapRunTimedCodeFrom previous (run :: runs)))
                (fun _ => 1) z := by
                    have hprod : ccr25GapRunMomentProduct β (run :: runs) =
                        |replicaPartitionDisorderMoment β run.label| *
                          ccr25GapRunMomentProduct β runs := by
                      simp [ccr25GapRunMomentProduct]
                    have hcode : ccr25GapRunTimedCodeKernelWord β
                        (ccr25GapRunTimedCodeFrom previous (run :: runs)) =
                        freeReplicaKernel run.firstGap previous run.label ::
                          ccr25TimedInteractionRunAbs β run.label
                            run.internalGapsRev ::
                          ccr25GapRunTimedCodeKernelWord β
                            (ccr25GapRunTimedCodeFrom run.label runs) := by
                      have hfreeCode :
                          ccr25RunDurationKernel 0 β
                              (.free previous run.label)
                              (.free (run.firstGap - 1)) =
                            freeReplicaKernel run.firstGap previous run.label := by
                        change freeReplicaKernel ((run.firstGap - 1) + 1)
                            previous run.label =
                          freeReplicaKernel run.firstGap previous run.label
                        congr 1
                        omega
                      have hinterCode :
                          ccr25RunDurationKernel 0 β
                              (.interacting run.label)
                              (.interacting run.internalGapsRev.sum
                                run.internalGapsRev) =
                            ccr25TimedInteractionRunAbs β run.label
                              run.internalGapsRev := by
                        change (fun z x =>
                            Real.exp (-0 * (run.internalGapsRev.sum : ℝ)) *
                              ccr25TimedInteractionRunAbs β run.label
                                run.internalGapsRev z x) = _
                        funext z x
                        simp
                      simp [ccr25GapRunTimedCodeKernelWord,
                        ccr25GapRunTimedCodeKernel,
                        ccr25GapRunTimedCodeFrom, hfreeCode, hinterCode]
                    rw [hprod, hcode]
                    simp only [finiteKernelWordApply]

/-- Summing a finitely supported start profile against a full-support run
path turns its initial free run into the boundary vector. The remaining
timed code is evaluated with every intermediate state in the horizon box. -/
theorem ccr25GapRunKey_profilePairing_eq_finiteBox_word {h L : ℕ}
    (β : ℝ) (A : Finset Site) (φ : Site → ℝ)
    (key : CCR25GapRunKey h) (n : ℕ)
    (hpos : ∀ run ∈ key.laterRuns, 1 ≤ run.firstGap)
    (hbudget : n + 1 + key.firstInternalGapsRev.sum +
      (key.laterRuns.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L) :
    (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (w i)) *
        ccr25GapRunPathWeight β ⊥
          (ccr25GapRunKeyRestore key (n + 1)) w) =
      ccr25GapRunMomentProduct β (ccr25GapRunKeyRestore key (n + 1)) *
        ∑ x ∈ configBox h A L,
          replicaBoundaryVector (n + 1) key.firstLabel A φ x *
            finiteKernelWordApply (configBox h A L)
              (ccr25GapRunTimedCodeKernelWord β
                (ccr25GapRunKeyTimedCode key)) (fun _ => 1) x := by
  classical
  let S := configBox h A L
  let tail : LatticeConfiguration h → ℝ := fun x =>
    finiteKernelWordApply S
      (ccr25GapRunTimedCodeKernelWord β (ccr25GapRunKeyTimedCode key))
      (fun _ => 1) x
  have hstart (w : LatticeConfiguration h)
      (hw : w ∈ Fintype.piFinset (fun _ : Fin h => A)) :
      w ∈ configBox h A 0 := by
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi : w i ∈ A := Fintype.mem_piFinset.mp hw i
    refine Finset.mem_biUnion.mpr ⟨w i, hi, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    simp
  have hcode (d : ℕ) (hd : 1 ≤ d) :
      ccr25GapRunTimedCodeKernelWord β
          (ccr25GapRunTimedCodeFrom ⊥
            (ccr25GapRunKeyRestore key d)) =
        (fun z x => freeReplicaKernel d ⊥ key.firstLabel z x) ::
          ccr25GapRunTimedCodeKernelWord β (ccr25GapRunKeyTimedCode key) := by
    cases key with
    | mk firstLabel firstInternalGapsRev laterRuns =>
      simp only [ccr25GapRunTimedCodeFrom, ccr25GapRunKeyRestore,
        ccr25GapRunKeyTimedCode, ccr25GapRunTimedCodeKernelWord,
        List.map_cons, ccr25GapRunTimedCodeKernel]
      apply congrArg (fun K : LatticeConfiguration h →
          LatticeConfiguration h → ℝ =>
        K :: ccr25RunDurationKernel 0 β (.interacting firstLabel)
          (.interacting firstInternalGapsRev.sum firstInternalGapsRev) ::
          List.map (ccr25GapRunTimedCodeKernel β)
            (ccr25GapRunTimedCodeFrom firstLabel laterRuns))
      funext z x
      change freeReplicaKernel (d - 1 + 1) ⊥ firstLabel z x =
        freeReplicaKernel d ⊥ firstLabel z x
      rw [Nat.sub_add_cancel hd]
  have hpath (w : LatticeConfiguration h)
      (hw : w ∈ Fintype.piFinset (fun _ : Fin h => A)) :
      ccr25GapRunPathWeight β ⊥
          (ccr25GapRunKeyRestore key (n + 1)) w =
        ccr25GapRunMomentProduct β
            (ccr25GapRunKeyRestore key (n + 1)) *
          (∑ x ∈ S, freeReplicaKernel (n + 1) ⊥ key.firstLabel w x * tail x) := by
    have hposAll : ∀ run ∈ ccr25GapRunKeyRestore key (n + 1),
        1 ≤ run.firstGap := by
      intro run hr
      simp only [ccr25GapRunKeyRestore, List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp
      · exact hpos run hr
    have hboxBudget : 0 +
        ((ccr25GapRunKeyRestore key (n + 1)).map
          (fun run => run.firstGap + run.internalGapsRev.sum)).sum ≤ L := by
      simp only [ccr25GapRunKeyRestore, List.map_cons, List.sum_cons]
      simpa [Nat.add_assoc] using hbudget
    have hfinite := ccr25GapRunPathWeight_eq_finiteBox_timedCode
      (h := h) (L := L) β A ⊥
      (ccr25GapRunKeyRestore key (n + 1)) 0 w hposAll (hstart w hw) hboxBudget
    rw [hfinite]
    have hcode' := hcode (n + 1) (by omega)
    rw [hcode']
    simp only [finiteKernelWordApply, S, tail]
  have hfreeSum (w : LatticeConfiguration h)
      (hw : w ∈ Fintype.piFinset (fun _ : Fin h => A)) :
      (∑ x ∈ S, freeReplicaKernel (n + 1) ⊥ key.firstLabel w x * tail x) =
        ∑' x : LatticeConfiguration h,
          freeReplicaKernel (n + 1) ⊥ key.firstLabel w x * tail x := by
    symm
    exact ccr25TsumFreeReplicaKernel_eq_sum_configBox_of_le
      (A := A) (r := 0) (d := n + 1) (hstart w hw)
      (by omega) ⊥ key.firstLabel tail
  have hboundarySupport (x : LatticeConfiguration h)
      (hx : x ∉ S) : replicaBoundaryVector (n + 1) key.firstLabel A φ x = 0 := by
    exact replicaBoundaryVector_zero_of_not_configBox
      (n + 1) key.firstLabel A φ (fun hxsmall =>
        hx (ccr25ConfigBox_mono (by omega) hxsmall))
  calc
    _ = ccr25GapRunMomentProduct β
          (ccr25GapRunKeyRestore key (n + 1)) *
        ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (w i)) *
            (∑' x : LatticeConfiguration h,
              freeReplicaKernel (n + 1) ⊥ key.firstLabel w x * tail x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [hpath w hw, hfreeSum w hw]
      ring
    _ = ccr25GapRunMomentProduct β
          (ccr25GapRunKeyRestore key (n + 1)) *
        ∑' x : LatticeConfiguration h,
          replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by
      congr 1
      exact finite_sum_startProfile_freeReplicaKernel_pairing_eq_boundaryVector
        (n + 1) key.firstLabel A φ tail
    _ = ccr25GapRunMomentProduct β
          (ccr25GapRunKeyRestore key (n + 1)) *
        ∑ x ∈ S,
          replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x := by
      apply congrArg (fun f : ℝ =>
        ccr25GapRunMomentProduct β
          (ccr25GapRunKeyRestore key (n + 1)) * f)
      have htsum :
          (∑' x : LatticeConfiguration h,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x) =
          ∑ x ∈ S,
            replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x :=
        tsum_eq_sum (s := S) (f := fun x =>
          replicaBoundaryVector (n + 1) key.firstLabel A φ x * tail x)
          (fun x hx => by rw [hboundarySupport x hx]; simp)
      exact htsum

/-- The last timed kernel in a key code is an interaction ending on the
collision stratum of the final label, so its terminal one-vector can be
replaced by that collision indicator. -/
theorem ccr25GapRunKeyDampedKernelWord_terminal_eq {h : ℕ}
    (s : Finset (LatticeConfiguration h)) (lam β : ℝ)
    (key : CCR25GapRunKey h) :
    ∀ x,
      finiteKernelWordApply s
        (ccr25GapRunTimedCodeDampedKernelWord lam β
          (ccr25GapRunKeyTimedCode key)) (fun _ => 1) x =
      finiteKernelWordApply s
        (ccr25GapRunTimedCodeDampedKernelWord lam β
          (ccr25GapRunKeyTimedCode key))
        (collisionIndicator (ccr25GapRunKeyLastLabel key)) x := by
  cases key with
  | mk firstLabel firstInternalGapsRev laterRuns =>
      induction laterRuns generalizing firstLabel firstInternalGapsRev with
      | nil =>
          intro x
          let K : LatticeConfiguration h → LatticeConfiguration h → ℝ :=
            ccr25RunDurationKernel lam β (.interacting firstLabel)
              (.interacting firstInternalGapsRev.sum firstInternalGapsRev)
          have hK : ∀ x y,
              ¬ IsCollisionConfiguration firstLabel y → K x y = 0 := by
            intro x y hy
            simp [K, ccr25RunDurationKernel,
              ccr25TimedInteractionRunAbs_zero_of_not_collision_right
                β firstLabel firstInternalGapsRev x y hy]
          simpa [K, ccr25GapRunKeyTimedCode,
            ccr25GapRunTimedCodeFrom,
            ccr25GapRunTimedCodeDampedKernelWord,
            ccr25GapRunTimedCodeDampedKernel,
            ccr25GapRunKeyLastLabel] using
            (finiteKernelWordApply_append_terminal_collisionIndicator
              s [] K firstLabel hK x)
      | cons run laterRuns ih =>
          intro x
          let tailKey : CCR25GapRunKey h :=
            ⟨run.label, run.internalGapsRev, laterRuns⟩
          have hcode :
              ccr25GapRunTimedCodeDampedKernelWord lam β
                (ccr25GapRunKeyTimedCode
                  ⟨firstLabel, firstInternalGapsRev, run :: laterRuns⟩) =
                ccr25RunDurationKernel lam β (.interacting firstLabel)
                    (.interacting firstInternalGapsRev.sum
                      firstInternalGapsRev) ::
                  ccr25RunDurationKernel lam β (.free firstLabel run.label)
                    (.free (run.firstGap - 1)) ::
                  ccr25GapRunTimedCodeDampedKernelWord lam β
                    (ccr25GapRunKeyTimedCode tailKey) := by
            simp [ccr25GapRunKeyTimedCode,
              ccr25GapRunTimedCodeFrom,
              ccr25GapRunTimedCodeDampedKernelWord,
              ccr25GapRunTimedCodeDampedKernel, tailKey]
          have hlast : ccr25GapRunKeyLastLabel
                ⟨firstLabel, firstInternalGapsRev, run :: laterRuns⟩ =
              ccr25GapRunKeyLastLabel tailKey := by
            simp [ccr25GapRunKeyLastLabel, tailKey]
          rw [hcode, hlast]
          simp only [finiteKernelWordApply]
          apply Finset.sum_congr rfl
          intro y hy
          congr 1
          apply Finset.sum_congr rfl
          intro z hz
          congr 1
          exact ih run.label run.internalGapsRev z

end

end Critical2DKPZ.MomentBounds
