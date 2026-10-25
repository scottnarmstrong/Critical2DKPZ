/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25IndependentParameterSubset
public import Critical2DKPZ.MomentBounds.CCR25PartitionWords
public import Critical2DKPZ.MomentBounds.CCR25GapCompositions
public import Critical2DKPZ.MomentBounds.CCR25GapRunEncoding
public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
import Mathlib.Tactic

/-! # Exact internal-gap parameter families for CCR25 words -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- Parameters for one factor in a timed CCR25 run word. -/
inductive CCR25RunDurationParam
  | free (duration : ℕ)
  | interacting (duration : ℕ) (gapsRev : List ℕ)
  deriving DecidableEq

/-- The discounted kernel for one explicitly timed CCR25 free or interaction
factor. -/
noncomputable def ccr25RunDurationKernel {h : ℕ} (lam β : ℝ)
    (op : CCR25OperatorLabel h) (p : CCR25RunDurationParam)
    (z x : LatticeConfiguration h) : ℝ := by
  classical
  exact match op, p with
  | .free I J, .free d => freeReplicaKernel (d + 1) I J z x
  | .interacting I, .interacting d gapsRev =>
      Real.exp (-lam * (d : ℝ)) *
        ccr25TimedInteractionRunAbs β I gapsRev z x
  | _, _ => 0

/-- The full finite set of internal-gap choices for one hatted interacting
operator through cutoff `L`. -/
noncomputable def ccr25InteractingRunParameters (L : ℕ) :
    Finset CCR25RunDurationParam :=
  (Finset.range (L + 1)).biUnion fun d =>
    (ccr25PositiveGapCompositionsRev d).image fun gaps =>
      CCR25RunDurationParam.interacting d gaps

/-- The parameter family corresponding to a CCR25 operator label. -/
noncomputable def ccr25RunOperatorParameterFamily {h : ℕ}
    (L : ℕ) (lam β : ℝ) (op : CCR25OperatorLabel h) :
    CCR25KernelParameterFamily CCR25RunDurationParam (LatticeConfiguration h) :=
  match op with
  | .interacting _ =>
      ⟨ccr25InteractingRunParameters L, ccr25RunDurationKernel lam β op⟩
  | .free _ _ =>
      ⟨(Finset.range L).image CCR25RunDurationParam.free,
        ccr25RunDurationKernel lam β op⟩

/-- Projection from an operator parameter family recovers its explicit timed
kernel. -/
theorem ccr25RunOperatorParameterFamily_kernel_eq {h : ℕ}
    (L : ℕ) (lam β : ℝ) (op : CCR25OperatorLabel h)
    (p : CCR25RunDurationParam) :
    (ccr25RunOperatorParameterFamily L lam β op).kernel p =
      ccr25RunDurationKernel lam β op p := by
  cases op <;> rfl

/-- The interacting run parameters split disjointly by their total duration. -/
private theorem ccr25InteractingRunParameters_pairwiseDisjoint (L : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (L + 1)))
      (fun d => (ccr25PositiveGapCompositionsRev d).image fun gaps =>
        CCR25RunDurationParam.interacting d gaps) := by
  intro d hd d' hd' hne
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨gaps, hgaps, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨gaps', hgaps', heq⟩ := Finset.mem_image.mp hp'
  have hdEq : d' = d := (CCR25RunDurationParam.interacting.inj heq).1
  exact hne hdEq.symm

/-- Summing an interacting run parameter family gives exactly the hatted
interacting kernel. -/
theorem ccr25RunOperatorParameterFamily_interacting_sum_eq_hatted
    {h : ℕ} (L : ℕ) (lam β : ℝ) (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) :
    (∑ p ∈ (ccr25RunOperatorParameterFamily L lam β (.interacting I)).parameters,
      (ccr25RunOperatorParameterFamily L lam β (.interacting I)).kernel p z x) =
        hattedInteractingReplicaKernelAbs L lam β I z x := by
  classical
  rw [show (ccr25RunOperatorParameterFamily L lam β (.interacting I)).parameters =
      ccr25InteractingRunParameters L by rfl,
    ccr25InteractingRunParameters, Finset.sum_biUnion
      (ccr25InteractingRunParameters_pairwiseDisjoint L)]
  calc
    (∑ d ∈ Finset.range (L + 1),
        ∑ p ∈ (ccr25PositiveGapCompositionsRev d).image
            (fun gaps => CCR25RunDurationParam.interacting d gaps),
          ccr25RunDurationKernel lam β (.interacting I) p z x) =
      ∑ d ∈ Finset.range (L + 1),
        ∑ gaps ∈ ccr25PositiveGapCompositionsRev d,
          Real.exp (-lam * (d : ℝ)) *
            ccr25TimedInteractionRunAbs β I gaps z x := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_image (fun gaps hgaps gaps' hgaps' heq =>
            (CCR25RunDurationParam.interacting.inj heq).2)]
          rfl
    _ = ∑ d ∈ Finset.range (L + 1),
          Real.exp (-lam * (d : ℝ)) *
            ∑ gaps ∈ ccr25PositiveGapCompositionsRev d,
              ccr25TimedInteractionRunAbs β I gaps z x := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Finset.mul_sum]
    _ = hattedInteractingReplicaKernelAbs L lam β I z x :=
      ccr25TimedInteractionRunAbs_damped_gapCompositionSum_eq_hatted
        L lam β I z x

/-- Summing a free run parameter family gives exactly the hatted free kernel. -/
theorem ccr25RunOperatorParameterFamily_free_sum_eq_hatted
    {h : ℕ} (L : ℕ) (lam β : ℝ) (I J : ReplicaPartition h)
    (z x : LatticeConfiguration h) :
    (∑ p ∈ (ccr25RunOperatorParameterFamily L lam β (.free I J)).parameters,
      (ccr25RunOperatorParameterFamily L lam β (.free I J)).kernel p z x) =
        hattedFreeReplicaKernel L I J z x := by
  classical
  rw [show (ccr25RunOperatorParameterFamily L lam β (.free I J)).parameters =
      (Finset.range L).image CCR25RunDurationParam.free by rfl]
  rw [Finset.sum_image (fun d hd d' hd' heq =>
    CCR25RunDurationParam.free.inj heq)]
  simp [ccr25RunOperatorParameterFamily, ccr25RunDurationKernel,
    hattedFreeReplicaKernel]

/-- The sum of every operator's explicit timed parameter family is its hatted
CCR25 kernel. -/
theorem ccr25RunOperatorParameterFamily_sum_eq_labelKernel {h : ℕ}
    (L : ℕ) (lam β : ℝ) (op : CCR25OperatorLabel h)
    (z x : LatticeConfiguration h) :
    (∑ p ∈ (ccr25RunOperatorParameterFamily L lam β op).parameters,
      (ccr25RunOperatorParameterFamily L lam β op).kernel p z x) =
        ccr25LabelKernel L lam β op z x := by
  cases op with
  | interacting I =>
      exact ccr25RunOperatorParameterFamily_interacting_sum_eq_hatted
        L lam β I z x
  | free I J =>
      rw [ccr25RunOperatorParameterFamily_free_sum_eq_hatted]
      rfl

/-- Every explicit timed factor is nonnegative. -/
theorem ccr25RunDurationKernel_nonneg {h : ℕ}
    (lam β : ℝ) (op : CCR25OperatorLabel h)
    (p : CCR25RunDurationParam) (z x : LatticeConfiguration h) :
    0 ≤ ccr25RunDurationKernel lam β op p z x := by
  cases op with
  | interacting I =>
      cases p with
      | free d => simp [ccr25RunDurationKernel]
      | interacting d gapsRev =>
          exact mul_nonneg (Real.exp_nonneg _)
            (ccr25TimedInteractionRunAbs_nonneg β I gapsRev z x)
  | free I J =>
      cases p with
      | free d => exact freeReplicaKernel_nonneg (d + 1) I J z x
      | interacting d gapsRev => simp [ccr25RunDurationKernel]

/-- The parameter-family word action equals the corresponding hatted kernel
word action. -/
theorem ccr25RunOperatorParameterFamilyWordApply_eq_finiteKernelWordApply
    {h : ℕ} (s : Finset (LatticeConfiguration h))
    (L : ℕ) (lam β : ℝ) :
    ∀ (ops : List (CCR25OperatorLabel h)) (f : LatticeConfiguration h → ℝ)
      (x : LatticeConfiguration h),
      finiteKernelParameterFamilyWordApply s
        (ops.map (ccr25RunOperatorParameterFamily L lam β)) f x =
      finiteKernelWordApply s
        (ops.map (ccr25LabelKernel L lam β)) f x := by
  intro ops
  induction ops with
  | nil => intro f x; rfl
  | cons op ops ih =>
      intro f x
      simp only [List.map_cons, finiteKernelParameterFamilyWordApply,
        finiteKernelWordApply]
      calc
        (∑ p ∈ (ccr25RunOperatorParameterFamily L lam β op).parameters,
            ∑ y ∈ s,
              (ccr25RunOperatorParameterFamily L lam β op).kernel p x y *
                finiteKernelParameterFamilyWordApply s
                  (ops.map (ccr25RunOperatorParameterFamily L lam β)) f y) =
          ∑ y ∈ s,
            (∑ p ∈ (ccr25RunOperatorParameterFamily L lam β op).parameters,
              (ccr25RunOperatorParameterFamily L lam β op).kernel p x y) *
              finiteKernelParameterFamilyWordApply s
                (ops.map (ccr25RunOperatorParameterFamily L lam β)) f y := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.sum_mul]
        _ = ∑ y ∈ s,
            ccr25LabelKernel L lam β op x y *
              finiteKernelWordApply s
                (ops.map (ccr25LabelKernel L lam β)) f y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [ccr25RunOperatorParameterFamily_sum_eq_labelKernel,
            ih f y]

/-- A nonnegative terminal profile gives nonnegative actions for all valid
timed parameter words of a CCR25 operator list. -/
private theorem ccr25RunParameterChoices_wordApply_nonneg
    {h : ℕ} (s : Finset (LatticeConfiguration h))
    (L : ℕ) (lam β : ℝ) :
    ∀ (ops : List (CCR25OperatorLabel h))
      (f : LatticeConfiguration h → ℝ) (_hf : ∀ x, 0 ≤ f x),
      ∀ params ∈ ccr25ParameterChoices
        (ops.map (ccr25RunOperatorParameterFamily L lam β)),
        ∀ x, 0 ≤ finiteKernelWordApply s
          (ccr25ParameterChoiceKernelWord
            (ops.map (ccr25RunOperatorParameterFamily L lam β)) params) f x := by
  intro ops
  induction ops with
  | nil =>
      intro f hf params hparams x
      simp only [List.map_nil, ccr25ParameterChoices,
        Finset.mem_singleton] at hparams
      subst params
      change 0 ≤ f x
      exact hf x
  | cons op ops ih =>
      intro f _hf params hparams x
      classical
      simp only [List.map_cons, ccr25ParameterChoices] at hparams
      obtain ⟨p, hp, himage⟩ := Finset.mem_biUnion.mp hparams
      obtain ⟨tail, htail, heq⟩ := Finset.mem_image.mp himage
      subst params
      simp only [List.map_cons, ccr25ParameterChoiceKernelWord,
        finiteKernelWordApply]
      apply Finset.sum_nonneg
      intro y hy
      apply mul_nonneg
      · rw [ccr25RunOperatorParameterFamily_kernel_eq]
        exact ccr25RunDurationKernel_nonneg lam β op p x y
      · exact ih f _hf tail htail y

/-- A sum over any constrained subset of explicit internal-gap choices is
bounded by the corresponding hatted operator word. -/
theorem ccr25RunParameterChoices_subset_sum_le_hattedWord
    {h : ℕ} (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (ops : List (CCR25OperatorLabel h)) (S : Finset (List CCR25RunDurationParam))
    (hS : S ⊆ ccr25ParameterChoices
      (ops.map (ccr25RunOperatorParameterFamily L lam β)))
    (f : LatticeConfiguration h → ℝ) (hf : ∀ x, 0 ≤ f x)
    (x : LatticeConfiguration h) :
    (∑ params ∈ S,
      finiteKernelWordApply s
        (ccr25ParameterChoiceKernelWord
          (ops.map (ccr25RunOperatorParameterFamily L lam β)) params) f x) ≤
      finiteKernelWordApply s (ops.map (ccr25LabelKernel L lam β)) f x := by
  calc
    (∑ params ∈ S,
      finiteKernelWordApply s
        (ccr25ParameterChoiceKernelWord
          (ops.map (ccr25RunOperatorParameterFamily L lam β)) params) f x) ≤
      finiteKernelParameterFamilyWordApply s
        (ops.map (ccr25RunOperatorParameterFamily L lam β)) f x :=
      ccr25ParameterChoices_subset_sum_kernelWord_le_familyApply s _ S hS f x
        (fun params hparams =>
          ccr25RunParameterChoices_wordApply_nonneg s L lam β ops f hf
            params hparams x)
    _ = finiteKernelWordApply s
        (ops.map (ccr25LabelKernel L lam β)) f x :=
      ccr25RunOperatorParameterFamilyWordApply_eq_finiteKernelWordApply
        s L lam β ops f x

/-- Build the alternating operator tail from a list of collision labels. -/
def ccr25LabelListOperatorWordFrom {h : ℕ} (previous : ReplicaPartition h) :
    List (ReplicaPartition h) → List (CCR25OperatorLabel h)
  | [] => []
  | label :: labels => .free previous label :: .interacting label ::
      ccr25LabelListOperatorWordFrom label labels
termination_by labels => labels.length
decreasing_by all_goals simp_wf

/-- Build the alternating interacting/free operator word from collision
labels. -/
def ccr25LabelListOperatorWord {h : ℕ} :
    List (ReplicaPartition h) → List (CCR25OperatorLabel h)
  | [] => []
  | label :: labels => .interacting label ::
      ccr25LabelListOperatorWordFrom label labels

/-- A run list becomes the alternating interacting/free operator word. -/
def ccr25GapRunOperatorWordFrom {h : ℕ} (previous : ReplicaPartition h)
    (runs : List (CCR25GapRun h)) : List (CCR25OperatorLabel h) :=
  ccr25LabelListOperatorWordFrom previous (runs.map CCR25GapRun.label)

/-- The operator word of a run list is the label-list operator word of its run labels. -/
def ccr25GapRunOperatorWord {h : ℕ} (runs : List (CCR25GapRun h)) :
    List (CCR25OperatorLabel h) :=
  ccr25LabelListOperatorWord (runs.map CCR25GapRun.label)

/-- The label-list operator word agrees with the canonical CCR25 word
expansion of a finite partition sequence. -/
private theorem ccr25ListOfFn_cons {α : Type*} {n : ℕ}
    (f : Fin (n + 1) → α) :
    List.ofFn f = f 0 :: List.ofFn (fun j : Fin n => f j.succ) := by
  let tail : Fin n → α := fun j => f j.succ
  have hcons : f = Fin.cons (f 0) tail := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  rw [hcons, List.ofFn_cons]
  simp [tail, Fin.cons_zero]

/-- On a nonempty list, the label-list operator word is the canonical partition-word labels. -/
theorem ccr25LabelListOperatorWord_ofFn {h n : ℕ}
    (I : Fin (n + 1) → ReplicaPartition h) :
    ccr25LabelListOperatorWord (List.ofFn I) =
      ccr25PartitionWordLabels n I := by
  induction n with
  | zero =>
      let tail : Fin 0 → ReplicaPartition h := fun j => I j.succ
      have hlist : List.ofFn I = I 0 :: List.ofFn tail := by
        exact ccr25ListOfFn_cons I
      rw [hlist]
      simp [ccr25LabelListOperatorWord, ccr25LabelListOperatorWordFrom,
        ccr25PartitionWordLabels, tail]
  | succ n ih =>
      let tail : Fin (n + 1) → ReplicaPartition h := fun j => I j.succ
      have hlist : List.ofFn I = I 0 :: List.ofFn tail := by
        exact ccr25ListOfFn_cons I
      have htail : List.ofFn tail = tail 0 ::
          List.ofFn (fun j : Fin n => tail j.succ) :=
        ccr25ListOfFn_cons tail
      rw [hlist, htail]
      simp only [ccr25LabelListOperatorWord,
        ccr25LabelListOperatorWordFrom, ccr25PartitionWordLabels, tail]
      have hih := ih tail
      rw [htail] at hih
      simp only [ccr25LabelListOperatorWord, tail] at hih
      rw [← hih]
      have h01 : (1 : Fin (n + 1 + 1)) =
          Fin.succ (0 : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      rw [← h01]

/-- The alternating word of a gap-run list is the canonical partition word
when the run labels are its indexed partition sequence. -/
theorem ccr25GapRunOperatorWord_eq_partitionWordLabels {h n : ℕ}
    (runs : List (CCR25GapRun h)) (I : Fin (n + 1) → ReplicaPartition h)
    (hruns : List.ofFn I = runs.map CCR25GapRun.label) :
    ccr25GapRunOperatorWord runs = ccr25PartitionWordLabels n I := by
  unfold ccr25GapRunOperatorWord
  rw [← hruns, ccr25LabelListOperatorWord_ofFn]

/-- The run durations associated with the operator word. Each interacting
parameter retains the full reverse internal-gap list; a free parameter is
the one-based gap between consecutive distinct-label runs, shifted to the
zero-based index used by `hattedFreeReplicaKernel`. -/
def ccr25GapRunParameterWordFrom {h : ℕ} :
    List (CCR25GapRun h) → List CCR25RunDurationParam
  | [] => []
  | run :: runs =>
      CCR25RunDurationParam.free (run.firstGap - 1) ::
        CCR25RunDurationParam.interacting run.internalGapsRev.sum
          run.internalGapsRev ::
        ccr25GapRunParameterWordFrom runs
termination_by runs => runs.length
decreasing_by all_goals simp_wf


/-- Every list of positive gaps is a member of the reverse composition
family for its total duration. -/
theorem ccr25PositiveGapCompositionsRev_mem_of_pos_sum :
    ∀ (gaps : List ℕ), (∀ d ∈ gaps, 1 ≤ d) →
      gaps ∈ ccr25PositiveGapCompositionsRev gaps.sum := by
  intro gaps
  induction gaps with
  | nil => intro _; simp [ccr25PositiveGapCompositionsRev]
  | cons d gaps ih =>
      intro hpos
      have hd : 1 ≤ d := hpos d (by simp)
      have htail : ∀ e ∈ gaps, 1 ≤ e := by
        intro e he
        exact hpos e (by simp [he])
      have hrec := ih htail
      let m := d - 1 + gaps.sum
      have hmem : d - 1 ∈ Finset.range (m + 1) := by
        simp only [Finset.mem_range]
        dsimp [m]
        omega
      have hrest : gaps ∈
          ccr25PositiveGapCompositionsRev (m - (d - 1)) := by
        have hEq : m - (d - 1) = gaps.sum := by dsimp [m]; omega
        rw [hEq]
        exact hrec
      have hcons : d :: gaps ∈
          (ccr25PositiveGapCompositionsRev (m - (d - 1))).image
            (fun ds => (d - 1 + 1) :: ds) := by
        apply Finset.mem_image.mpr
        refine ⟨gaps, hrest, ?_⟩
        simp [Nat.sub_add_cancel hd]
      rw [show (d :: gaps).sum = m + 1 by
        simp only [List.sum_cons]
        dsimp [m]
        omega, ccr25PositiveGapCompositionsRev]
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
      refine ⟨d - 1, ?_, gaps, hrest, ?_⟩
      · dsimp [m]
        omega
      · simp [Nat.sub_add_cancel hd]

/-- An exact interacting run parameter belongs to the corresponding finite
duration family whenever its internal gaps are positive and their total is
at most the cutoff. -/
theorem ccr25InteractingRunParameter_mem (L : ℕ)
    (gaps : List ℕ) (hpos : ∀ d ∈ gaps, 1 ≤ d) (hL : gaps.sum ≤ L) :
    CCR25RunDurationParam.interacting gaps.sum gaps ∈
      ccr25InteractingRunParameters L := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨gaps.sum, Finset.mem_range.mpr ?_, ?_⟩
  · omega
  · apply Finset.mem_image.mpr
    exact ⟨gaps, ccr25PositiveGapCompositionsRev_mem_of_pos_sum gaps hpos, rfl⟩



/-- The event-gap sum contributed by one maximal run is its entry gap plus
the sum of its internal gaps. -/
private theorem map_pair_fst_eq {α β : Type*} (xs : List α) (b : β) :
    (xs.map fun x => (x, b)).map Prod.fst = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The gap sum of one expanded run is its first gap plus its internal gaps. -/
theorem ccr25GapRunExpandOne_gapSum {h : ℕ} (run : CCR25GapRun h) :
    ((ccr25GapRunExpandOne run).map Prod.fst).sum =
      run.firstGap + run.internalGapsRev.sum := by
  simp only [ccr25GapRunExpandOne, List.map_cons, List.sum_cons]
  rw [map_pair_fst_eq run.internalGapsRev.reverse run.label]
  simp [List.sum_reverse]

/-- Expanding a run list preserves total event-gap duration. -/
theorem ccr25GapRunExpand_gapSum {h : ℕ} (runs : List (CCR25GapRun h)) :
    ((ccr25GapRunExpand runs).map Prod.fst).sum =
      (runs.map fun run => run.firstGap + run.internalGapsRev.sum).sum := by
  induction runs with
  | nil => simp [ccr25GapRunExpand]
  | cons run runs ih =>
      simp [ccr25GapRunExpand, ccr25GapRunExpandOne_gapSum,
        List.map_append, List.sum_append, ih]

/-- Every gap stored by a run occurs in that run's expanded event list. -/
theorem ccr25GapRunExpandOne_gap_mem {h : ℕ} (run : CCR25GapRun h)
    {d : ℕ} (hd : d ∈ run.firstGap :: run.internalGapsRev) :
    (d, run.label) ∈ ccr25GapRunExpandOne run := by
  simp only [List.mem_cons] at hd
  rcases hd with rfl | hd
  · simp [ccr25GapRunExpandOne]
  · apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    exact ⟨d, List.mem_reverse.mpr hd, rfl⟩

/-- A run's expanded event list is included in the expansion of any list
which contains that run. -/
theorem ccr25GapRunExpandOne_subset_expand {h : ℕ} {run : CCR25GapRun h}
    {runs : List (CCR25GapRun h)} (hrun : run ∈ runs) :
    ∀ e ∈ ccr25GapRunExpandOne run, e ∈ ccr25GapRunExpand runs := by
  induction runs with
  | nil => simp at hrun
  | cons head tail ih =>
      simp only [List.mem_cons] at hrun
      rcases hrun with rfl | hrun
      · intro e he
        apply List.mem_append_left
        exact he
      · intro e he
        apply List.mem_append_right
        exact ih hrun e he

/-- The gap positivity of an active stream passes to every entry and internal
gap of its maximal run encoding. -/
theorem ccr25GapRunEncode_gap_pos {h : ℕ}
    (events : List (ℕ × ReplicaPartition h))
    (hpos : ∀ e ∈ events, 1 ≤ e.1) :
    ∀ run ∈ ccr25GapRunEncode events,
      ∀ d ∈ run.firstGap :: run.internalGapsRev, 1 ≤ d := by
  intro run hrun d hd
  have he := ccr25GapRunExpandOne_gap_mem run hd
  have he' := ccr25GapRunExpandOne_subset_expand hrun _ he
  rw [ccr25GapRunExpand_encode] at he'
  exact hpos (d, run.label) he'




end Critical2DKPZ.MomentBounds

end
