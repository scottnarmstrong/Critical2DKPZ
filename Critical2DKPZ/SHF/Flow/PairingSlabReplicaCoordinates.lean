/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabTensorTests
public import Critical2DKPZ.SHF.Tsai.FinsetCoordinateSplit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Tactic.FinCases

/-! # Four-replica rearrangement for the slab comparison -/

@[expose] public section

open MeasureTheory
open Filter
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- Reorder four coordinates into two pairs of replica paths. -/
def slabReplicaArrayEquiv (X : Type*) :
    (Fin 4 → X) ≃ (Fin 2 → X × X) where
  toFun q := ![(q (0 : Fin 4), q (2 : Fin 4)), (q (1 : Fin 4), q (3 : Fin 4))]
  invFun r := ![(r (0 : Fin 2)).1, (r (1 : Fin 2)).1,
    (r (0 : Fin 2)).2, (r (1 : Fin 2)).2]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv r := by
    funext i
    fin_cases i <;> ext <;> rfl

/-- The replica coordinate reordering as a measurable equivalence. -/
def slabReplicaArrayMeasurableEquiv (X : Type*) [MeasurableSpace X] :
    (Fin 4 → X) ≃ᵐ (Fin 2 → X × X) where
  toEquiv := slabReplicaArrayEquiv X
  measurable_toFun := by
    apply measurable_pi_iff.2
    intro i
    fin_cases i
    · exact (measurable_pi_apply 0).prodMk (measurable_pi_apply 2)
    · exact (measurable_pi_apply 1).prodMk (measurable_pi_apply 3)
  measurable_invFun := by
    apply measurable_pi_iff.2
    intro i
    fin_cases i
    · exact measurable_fst.comp (measurable_pi_apply 0)
    · exact measurable_fst.comp (measurable_pi_apply 1)
    · exact measurable_snd.comp (measurable_pi_apply 0)
    · exact measurable_snd.comp (measurable_pi_apply 1)

/-- The replica coordinate reordering as a homeomorphism. -/
def slabReplicaArrayHomeomorph (X : Type*) [TopologicalSpace X] :
    (Fin 4 → X) ≃ₜ (Fin 2 → X × X) where
  toEquiv := slabReplicaArrayEquiv X
  continuous_toFun := by
    apply continuous_pi_iff.2
    intro i
    fin_cases i <;> fun_prop
  continuous_invFun := by
    apply continuous_pi_iff.2
    intro i
    fin_cases i <;> fun_prop

private theorem measurePreserving_slabReplicaArrayEquiv
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] :
    MeasurePreserving (slabReplicaArrayMeasurableEquiv X)
      (Measure.pi fun i : Fin 4 => if i.val < 2 then μ else ν)
      (Measure.pi fun _ : Fin 2 => μ.prod ν) := by
  classical
  let S : Finset (Fin 4) := {0, 1}
  let μsource : Fin 4 → Measure X := fun i => if i ∈ S then μ else ν
  have hsourceSigma : ∀ i : Fin 4, SigmaFinite (μsource i) := by
    intro i
    dsimp [μsource]
    split_ifs <;> infer_instance
  have hsplit := @measurePreserving_splitFinsetCoordinates 4 S X inferInstance
    μsource hsourceSigma
  have hSmono : StrictMono (fun i : Fin 2 => i.castAdd 2) := Fin.strictMono_castAdd 2
  have hSmem : ∀ i : Fin 2, i.castAdd 2 ∈ S := by
    intro i
    fin_cases i <;> simp [S]
  have hScard : S.card = 2 := by simp [S]
  have hSidx (i : Fin S.card) : S.orderEmbOfFin rfl i =
      (Fin.cast hScard i).castAdd 2 := by
    have h := Finset.orderEmbOfFin_unique (s := S) rfl hSmem hSmono
    exact (congrFun h (Fin.cast hScard i)).symm.trans (by simp)
  have hCset : Sᶜ = ({2, 3} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [S]
  have hCmono : StrictMono (fun i : Fin 2 => i.natAdd 2) := Fin.strictMono_natAdd 2
  have hCmem : ∀ i : Fin 2, i.natAdd 2 ∈ Sᶜ := by
    intro i
    fin_cases i <;> simp [S]
  have hCcard : Sᶜ.card = 2 := by rw [hCset]; norm_num
  have hCidx (i : Fin Sᶜ.card) : Sᶜ.orderEmbOfFin rfl i =
      (Fin.cast hCcard i).natAdd 2 := by
    have h := Finset.orderEmbOfFin_unique (s := Sᶜ) (by rw [hCset]; norm_num)
      hCmem hCmono
    exact (congrFun h (Fin.cast hCcard i)).symm.trans (by simp)
  have hsourceMeasure : μsource = fun i : Fin 4 => if i.val < 2 then μ else ν := by
    funext i
    fin_cases i <;> simp [μsource, S]
  have hsplitRaw : MeasurePreserving (splitFinsetCoordinates S X)
      (Measure.pi fun i : Fin 4 => if i.val < 2 then μ else ν)
      ((Measure.pi fun _ : Fin S.card => μ).prod
        (Measure.pi fun _ : Fin Sᶜ.card => ν)) := by
    rw [← hsourceMeasure]
    have hfirst : ∀ i : Fin S.card, μsource (S.orderEmbOfFin rfl i) = μ := by
      intro i
      simp [μsource]
    have hsecond : ∀ i : Fin Sᶜ.card, μsource (Sᶜ.orderEmbOfFin rfl i) = ν := by
      intro i
      have hi : Sᶜ.orderEmbOfFin rfl i ∉ S :=
        Finset.mem_compl.mp (Finset.orderEmbOfFin_mem Sᶜ rfl i)
      simp [μsource, hi]
    simpa [μsource, hfirst, hsecond] using hsplit
  let eS : Fin S.card ≃ Fin 2 := finCongr hScard
  let eC : Fin Sᶜ.card ≃ Fin 2 := finCongr hCcard
  let eSMeas := MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => X) eS
  let eCMeas := MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => X) eC
  have hSMeasure := measurePreserving_piCongrLeft (fun _ : Fin 2 => μ) eS
  have hCMeasure := measurePreserving_piCongrLeft (fun _ : Fin 2 => ν) eC
  have hsplitCast := (hSMeasure.prod hCMeasure).comp hsplitRaw
  have hfst (q : Fin 4 → X) : eSMeas ((splitFinsetCoordinates S X q).1) =
      fun i : Fin 2 => q (i.castAdd 2) := by
    funext i
    change (splitFinsetCoordinates S X q).1 (Fin.cast hScard.symm i) =
      q (i.castAdd 2)
    rw [splitFinsetCoordinates_fst]
    change q (S.orderEmbOfFin rfl (Fin.cast hScard.symm i)) = q (i.castAdd 2)
    rw [hSidx, Fin.rightInverse_cast hScard i]
  have hsnd (q : Fin 4 → X) : eCMeas ((splitFinsetCoordinates S X q).2) =
      fun i : Fin 2 => q (i.natAdd 2) := by
    funext i
    change (splitFinsetCoordinates S X q).2 (Fin.cast hCcard.symm i) =
      q (i.natAdd 2)
    rw [splitFinsetCoordinates_snd]
    change q (Sᶜ.orderEmbOfFin rfl (Fin.cast hCcard.symm i)) = q (i.natAdd 2)
    rw [hCidx, Fin.rightInverse_cast hCcard i]
  have hArrow := measurePreserving_arrowProdEquivProdArrow X X (Fin 2)
    (fun _ => μ) (fun _ => ν)
  have hcomp := hArrow.symm.comp hsplitCast
  let eSplit := (splitFinsetCoordinates S X).trans (eSMeas.prodCongr eCMeas)
  have heq : slabReplicaArrayMeasurableEquiv X =
      eSplit.trans (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin 2)).symm := by
    ext q i
    · fin_cases i
      · change q (0 : Fin 4) = eSMeas ((splitFinsetCoordinates S X q).1) 0
        exact (congrFun (hfst q) 0).symm
      · change q (1 : Fin 4) = eSMeas ((splitFinsetCoordinates S X q).1) 1
        exact (congrFun (hfst q) 1).symm
    · fin_cases i
      · change q (2 : Fin 4) = eCMeas ((splitFinsetCoordinates S X q).2) 0
        exact (congrFun (hsnd q) 0).symm
      · change q (3 : Fin 4) = eCMeas ((splitFinsetCoordinates S X q).2) 1
        exact (congrFun (hsnd q) 1).symm
  rw [heq]
  exact hcomp

/-- The product of one compact connector test over two replicas. -/
def slabReplicaTensorTest {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : C_c(X × X, ℝ)) : C_c((Fin 2 → X × X), ℝ) := by
  let f : (Fin 2 → X × X) → ℝ := fun r => ∏ i : Fin 2, g (r i)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  refine ⟨⟨f, hf⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi fun _ : Fin 2 => g.hasCompactSupport)
  intro r hr
  apply Set.mem_univ_pi.mpr
  intro i
  by_contra hi
  have hz : g (r i) = 0 := image_eq_zero_of_notMem_tsupport hi
  have hprod : f r = 0 := by
    simpa [f] using (Finset.prod_eq_zero (s := Finset.univ) (f := fun j : Fin 2 => g (r j))
      (Finset.mem_univ i) hz)
  exact hr hprod

/-- Pull the two-replica compact connector test back to four source coordinates. -/
def slabReplicaSourceTest {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : C_c(X × X, ℝ)) : C_c((Fin 4 → X), ℝ) := by
  let f := slabReplicaTensorTest g
  let h := slabReplicaArrayHomeomorph X
  refine ⟨⟨fun q => f (h q), f.continuous.comp h.continuous⟩, ?_⟩
  exact f.hasCompactSupport.comp_homeomorph h


/-- The four-replica product identity for an arbitrary measurable connector integrand. This
version does not require continuity or compact support; those conditions are supplied separately
when integrability is needed. -/
theorem integral_slabReplicaFunction_sq {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [SigmaFinite μ] [SigmaFinite ν] (f : X × X → ℝ) :
    (∫ q : Fin 4 → X, f (q 0, q 2) * f (q 1, q 3) ∂
      Measure.pi (fun i : Fin 4 => if i.val < 2 then μ else ν)) =
      (∫ p, f p ∂(μ.prod ν)) ^ 2 := by
  let e := slabReplicaArrayMeasurableEquiv X
  have hmp := measurePreserving_slabReplicaArrayEquiv (X := X) μ ν
  have hsource :
      (∫ q : Fin 4 → X, f (q 0, q 2) * f (q 1, q 3) ∂
        Measure.pi (fun i : Fin 4 => if i.val < 2 then μ else ν)) =
      ∫ r : Fin 2 → X × X, ∏ i : Fin 2, f (r i) ∂
        Measure.pi (fun _ : Fin 2 => μ.prod ν) := by
    simpa [e, slabReplicaArrayMeasurableEquiv, slabReplicaArrayEquiv,
      Equiv.arrowProdEquivProdArrow] using
        hmp.integral_comp' (fun r : Fin 2 → X × X => ∏ i : Fin 2, f (r i))
  rw [hsource, integral_fintype_prod_eq_prod]
  simp [pow_two]


end Critical2DKPZ.SHF.Flow

end
