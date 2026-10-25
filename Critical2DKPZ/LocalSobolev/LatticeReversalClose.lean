/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeReversalAssembly
public import Critical2DKPZ.LocalSobolev.LatticeReversalClockError
import Critical2DKPZ.LocalSobolev.LatticeReversalForwardClock
import Critical2DKPZ.LocalSobolev.LatticeReversalTestedExactError
import Critical2DKPZ.LocalSobolev.LatticeReversalClosing
import Critical2DKPZ.LocalSobolev.LatticeReversalLawTransfer
import Critical2DKPZ.Provider.PropVD
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-! # Equality of limiting forward and reversed lattice laws -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.LocalSobolev

private theorem measurable_kpzLatticeReversed_section (ϑ : ℝ) (N : ℕ) (t T : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) :
    Measurable (fun x : Plane => kpzLatticeReversed ϑ N t T h₀ x ω) := by
  let g : Site → ℝ := fun z =>
    Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t)) (evenCeil (N * T))
      (fun w => if w = z then 1 else 0) (cellAverage N fun y => Real.exp (h₀ y)) ω) -
    ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t))
      (evenCeil (N * T)) (fun w => if w = z then 1 else 0)
        (fun _ => 1) ω') ∂disorderLaw
  have hg : Measurable g := measurable_of_countable g
  have hfactor : (fun x : Plane => kpzLatticeReversed ϑ N t T h₀ x ω) =
      g ∘ latticePoint N := by
    funext x
    simp [g, kpzLatticeReversed]
  rw [hfactor]
  exact hg.comp (measurable_latticePoint N)

private theorem kpzLatticeReversed_bounded_on_compact (ϑ : ℝ) (N : ℕ) (t T : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) (K : Set Plane) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖kpzLatticeReversed ϑ N t T h₀ x ω‖ ≤ B := by
  classical
  let g : Site → ℝ := fun z =>
    Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t)) (evenCeil (N * T))
      (fun w => if w = z then 1 else 0) (cellAverage N fun y => Real.exp (h₀ y)) ω) -
    ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t))
      (evenCeil (N * T)) (fun w => if w = z then 1 else 0)
        (fun _ => 1) ω') ∂disorderLaw
  have hfactor : (fun x : Plane => kpzLatticeReversed ϑ N t T h₀ x ω) =
      g ∘ latticePoint N := by
    funext x
    simp [g, kpzLatticeReversed]
  have hfinite := Critical2DKPZ.SHF.Limit.finite_latticePoint_image_of_bounded
    (N := N) hK.isBounded
  let values : Set ℝ := g '' (latticePoint N '' K)
  have hvfinite : values.Finite := hfinite.image g
  obtain ⟨M, hM⟩ := hvfinite.bddAbove
  obtain ⟨m, hm⟩ := hvfinite.bddBelow
  let B : ℝ := max |M| |m|
  refine ⟨B, ?_, fun x hx => ?_⟩
  · dsimp [B]
    positivity
  have hvalue : kpzLatticeReversed ϑ N t T h₀ x ω ∈ values := by
    rw [congrFun hfactor x]
    exact ⟨latticePoint N x, ⟨x, hx, rfl⟩, rfl⟩
  have hupper : kpzLatticeReversed ϑ N t T h₀ x ω ≤ M := hM hvalue
  have hlower : m ≤ kpzLatticeReversed ϑ N t T h₀ x ω := hm hvalue
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · dsimp [B]
    exact (neg_le_neg (le_max_right |M| |m|)).trans ((neg_abs_le m).trans hlower)
  · dsimp [B]
    exact hupper.trans (le_abs_self M |>.trans (le_max_left |M| |m|))

private theorem kpzLatticeReversed_locallyIntegrable (ϑ : ℝ) (N : ℕ) (t T : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) :
    LocallyIntegrable (fun x : Plane => kpzLatticeReversed ϑ N t T h₀ x ω) volume := by
  have hmeas := measurable_kpzLatticeReversed_section ϑ N t T h₀ ω
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨B, _, hB⟩ := kpzLatticeReversed_bounded_on_compact ϑ N t T h₀ ω K hK
  exact Measure.integrableOn_of_bounded (ne_of_lt hK.measure_lt_top)
    hmeas.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact hB x hx)

private theorem integral_testFn_mul_sub_eq (φ : TestFn) (f g : Plane → ℝ)
    (hf : LocallyIntegrableOn f Set.univ volume)
    (hg : LocallyIntegrableOn g Set.univ volume) :
    (∫ x, φ x * (f x - g x)) =
      (∫ x, φ x * f x) - ∫ x, φ x * g x := by
  have hfi : Integrable (fun x => φ x * f x) := by
    simpa only [smul_eq_mul] using φ.integrable_smul hf
  have hgi : Integrable (fun x => φ x * g x) := by
    simpa only [smul_eq_mul] using φ.integrable_smul hg
  rw [← integral_sub hfi hgi]
  congr 1
  funext x
  ring

/-- The complementary horizon and reverse-start clocks induce a forward time shift of zero or
minus two lattice steps. The rounded shifted time is exactly the complementary forward clock. -/
theorem eventually_kpzLattice_reverse_complementClockShift_eq (t T : ℝ)
    (ht : 0 < t) (htT : t ≤ T) :
    ∀ᶠ N : ℕ in atTop,
      evenCeil ((N : ℝ) * (t +
        ((((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * (T - t)) : ℕ) : ℤ) -
          (evenCeil ((N : ℝ) * t) : ℤ) : ℤ) : ℝ) / (N : ℝ))) =
        evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * (T - t)) := by
  filter_upwards [eventually_ge_atTop ⌈4 / t⌉₊, eventually_gt_atTop 0]
    with N hN hNpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlarge : 4 / t ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
  have hNt : 4 ≤ (N : ℝ) * t := by
    simpa only [mul_comm] using (div_le_iff₀ ht).mp hlarge
  let m : ℕ := evenCeil ((N : ℝ) * t)
  let L : ℕ := evenCeil ((N : ℝ) * T)
  let r : ℕ := evenCeil ((N : ℝ) * (T - t))
  let m' : ℕ := L - r
  let d : ℤ := (m' : ℤ) - (m : ℤ)
  have hshift : d = -2 ∨ d = 0 := by
    have h := kpzLattice_reverseClockShift_spec N T ht htT
    dsimp only [m, L, r, m'] at h
    dsimp [d]
    rcases h with h | h
    · left
      exact h
    · right
      exact h
  have hexpand : (N : ℝ) * (t + (d : ℝ) / (N : ℝ)) =
      (N : ℝ) * t + d := by
    field_simp
  have hgoal : evenCeil ((N : ℝ) * (t + (d : ℝ) / (N : ℝ))) = m' := by
    rw [hexpand]
    rcases hshift with hd | hd
    · rw [hd]
      have hc := Critical2DKPZ.evenCeil_add_two_mul
        (t := (N : ℝ) * t - 2) (by linarith) 1
      have he : (N : ℝ) * t - 2 + 2 * (1 : ℕ) = (N : ℝ) * t := by norm_num
      rw [he] at hc
      have hclock : evenCeil ((N : ℝ) * t - 2) + 2 = m := by
        dsimp [m]
        exact hc.symm
      have hdiff : (m' : ℤ) - (m : ℤ) = -2 := by simpa [d] using hd
      have hclockInt : (m : ℤ) = (evenCeil ((N : ℝ) * t - 2) : ℤ) + 2 := by
        exact_mod_cast hclock.symm
      have hceilInt : (evenCeil ((N : ℝ) * t - 2) : ℤ) = (m' : ℤ) := by omega
      have hnat : evenCeil ((N : ℝ) * t - 2) = m' := by exact_mod_cast hceilInt
      simpa only [hd, Int.cast_neg, Int.cast_ofNat, sub_eq_add_neg] using hnat
    · have hdiff : (m' : ℤ) = (m : ℤ) := by
        have hh : (m' : ℤ) - (m : ℤ) = 0 := by simpa [d] using hd
        omega
      have hnat : m' = m := by exact_mod_cast hdiff
      simpa only [hd, Int.cast_zero, add_zero] using hnat.symm
  simpa only [m, L, r, d] using hgoal

private theorem kpzLattice_eq_of_evenClock_eq (ϑ : ℝ) (N : ℕ) {s u : ℝ}
    (hclock : evenCeil ((N : ℝ) * s) = evenCeil ((N : ℝ) * u))
    (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    kpzLattice ϑ N s h₀ x ω = kpzLattice ϑ N u h₀ x ω := by
  simp [kpzLattice, kpzLatticeCentring, rescaledP2P, hclock]

private def testedExactReverseClockError (ϑ : ℝ) (N : ℕ) (t T : ℝ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) : Disorder → ℝ := fun ω =>
  ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
    kpzLatticeReversed ϑ N
      (((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) / (N : ℝ))
      (((evenCeil ((N : ℝ) * T) : ℕ) : ℝ) / (N : ℝ)) h₀ x
      (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω))

private def testedForwardClockPerturbation (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (d : ℤ) : Disorder → ℝ := fun ω =>
  ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
    kpzLattice ϑ N (t + (d : ℝ) / (N : ℝ)) h₀ x ω)

/-- The tested fields in one coordinate are close in `L¹`. We compare first at the
fixed exact reflected clock, then change the forward clock by the complementary two-step
rounding defect, and finally use the exact reversal estimate at that complementary clock. -/
private theorem tendsto_eLpNorm_tested_kpzLattice_reverse_coordinate_of_helpers
    (ϑ T t : ℝ) (ht : 0 < t) (htT : t ≤ T)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (hExact : Tendsto (fun N : ℕ =>
      eLpNorm (testedExactReverseClockError ϑ N t T h₀ φ) 1 disorderLaw)
      atTop (𝓝 0))
    (hPerturb : Tendsto (fun N : ℕ => eLpNorm
      (testedForwardClockPerturbation ϑ N t h₀ φ
        ((((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * (T - t)) : ℕ) : ℤ) -
          (evenCeil ((N : ℝ) * t) : ℤ))))
      2 disorderLaw) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => eLpNorm (fun ω : Disorder =>
      ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
        kpzLatticeReversed ϑ N (T - t) T h₀ x
          (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)))
      1 disorderLaw) atTop (𝓝 0) := by
  let m : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  let L : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * T)
  let r : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * (T - t))
  let m' : ℕ → ℕ := fun N => L N - r N
  let d : ℕ → ℤ := fun N => (m' N : ℤ) - (m N : ℤ)
  have hshiftClock : ∀ᶠ N : ℕ in atTop,
      evenCeil ((N : ℝ) * (t + (d N : ℝ) / (N : ℝ))) = m' N := by
    simpa [m, L, r, m', d] using
      eventually_kpzLattice_reverse_complementClockShift_eq t T ht htT
  have hd : ∀ N, d N = -2 ∨ d N = 0 ∨ d N = 2 := by
    intro N
    have hh := kpzLattice_reverseClockShift_spec N T ht htT
    dsimp [d, m', L, r, m] at hh ⊢
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  have hEvenM (N : ℕ) : Even (m N) := by
    dsimp [m]
    exact evenCeil_even _
  have hEvenL (N : ℕ) : Even (L N) := by
    dsimp [L]
    exact evenCeil_even _
  have hEvenR (N : ℕ) : Even (r N) := by
    dsimp [r]
    exact evenCeil_even _
  have hrL (N : ℕ) : r N ≤ L N := by
    dsimp [r, L]
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left (sub_le_self T ht.le) (Nat.cast_nonneg N)
  have hmL (N : ℕ) : m N ≤ L N := by
    dsimp [m, L]
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg N)
  have hmPos : ∀ᶠ N : ℕ in atTop, 1 ≤ m N := by
    filter_upwards [eventually_ge_atTop ⌈4 / t⌉₊, eventually_gt_atTop 0]
      with N hN hNpos
    have hlarge : 4 / t ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
    have hNt : 4 ≤ (N : ℝ) * t := by
      simpa only [mul_comm] using (div_le_iff₀ ht).mp hlarge
    have hcast : (4 : ℝ) ≤ (m N : ℝ) := by
      have hc := le_evenCeil ((N : ℝ) * t)
      simpa [m] using hNt.trans hc
    have hm4 : 4 ≤ m N := by exact_mod_cast hcast
    omega
  have hm'Even (N : ℕ) : Even (m' N) := by
    exact (Nat.even_sub (hrL N)).2 ⟨fun _ => hEvenR N, fun _ => hEvenL N⟩
  have hm'Pos : ∀ᶠ N : ℕ in atTop, 1 ≤ m' N := by
    filter_upwards [eventually_ge_atTop ⌈4 / t⌉₊] with N hN
    have hlarge : 4 / t ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
    have hNt : 4 ≤ (N : ℝ) * t := by
      simpa only [mul_comm] using (div_le_iff₀ ht).mp hlarge
    have hcast : (4 : ℝ) ≤ (m N : ℝ) := by
      have hc := le_evenCeil ((N : ℝ) * t)
      simpa [m] using hNt.trans hc
    have hm4 : 4 ≤ m N := by exact_mod_cast hcast
    rcases hd N with h | h | h
    · dsimp [d] at h
      omega
    · dsimp [d] at h
      omega
    · dsimp [d] at h
      omega
  have hmPrimeL : ∀ N, m' N ≤ L N := fun N => Nat.sub_le _ _
  have hMoveM := tendsto_eLpNorm_tested_exactReverseField_error_of_movingClock
    ϑ m L h₀ φ hmPos hEvenM hEvenL (Filter.Eventually.of_forall hmL)
  have hMoveM' := tendsto_eLpNorm_tested_exactReverseField_error_of_movingClock
    ϑ m' L h₀ φ hm'Pos hm'Even hEvenL (Filter.Eventually.of_forall hmPrimeL)
  have hA : Tendsto (fun N : ℕ => eLpNorm (fun ω : Disorder =>
      ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
        kpzLatticeReversed ϑ N (((L N - m N : ℕ) : ℝ) / N)
          ((L N : ℝ) / N) h₀ x (PolymerCalculus.reversedDisorder (L N) ω)))
      1 disorderLaw) atTop (𝓝 0) := by
    change Tendsto (fun N : ℕ => eLpNorm (fun ω : Disorder =>
      ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
        kpzLatticeReversed ϑ N
          (((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) / (N : ℝ))
          (((evenCeil ((N : ℝ) * T) : ℕ) : ℝ) / (N : ℝ)) h₀ x
          (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)))
      1 disorderLaw) atTop (𝓝 0) at hExact
    simpa [m, L] using hExact
  let A : ℕ → Disorder → ℝ := fun N ω =>
    ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
      kpzLatticeReversed ϑ N (((L N - m N : ℕ) : ℝ) / N)
        ((L N : ℝ) / N) h₀ x (PolymerCalculus.reversedDisorder (L N) ω))
  let B : ℕ → Disorder → ℝ := fun N ω =>
    ∫ x, φ x * (kpzLattice ϑ N ((m N : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N (((L N - m N : ℕ) : ℝ) / N)
        ((L N : ℝ) / N) h₀ x (PolymerCalculus.reversedDisorder (L N) ω))
  let C : ℕ → Disorder → ℝ := fun N =>
    testedForwardClockPerturbation ϑ N t h₀ φ (d N)
  let D : ℕ → Disorder → ℝ := fun N ω =>
    ∫ x, φ x * (kpzLattice ϑ N ((m' N : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N (((r N : ℕ) : ℝ) / N)
        ((L N : ℝ) / N) h₀ x (PolymerCalculus.reversedDisorder (L N) ω))
  have hB : Tendsto (fun N : ℕ => eLpNorm (B N) 1 disorderLaw) atTop (𝓝 0) := by
    simpa [B, m, L] using hMoveM
  have hD : Tendsto (fun N : ℕ => eLpNorm (D N) 1 disorderLaw) atTop (𝓝 0) := by
    have hsub (N : ℕ) : L N - m' N = r N := by
      dsimp [m']
      exact Nat.sub_sub_self (hrL N)
    simpa only [D, hsub] using hMoveM'
  have hCtwo : Tendsto (fun N : ℕ => eLpNorm (C N) 2 disorderLaw) atTop (𝓝 0) := by
    change Tendsto (fun N : ℕ => eLpNorm
      (testedForwardClockPerturbation ϑ N t h₀ φ (d N)) 2 disorderLaw)
      atTop (𝓝 0) at hPerturb
    simpa only [C] using hPerturb
  have hCmeas (N : ℕ) : Measurable (C N) := by
    have hPair (ω : Disorder) : C N ω =
        (∫ x, φ x * kpzLattice ϑ N t h₀ x ω) -
          ∫ x, φ x * kpzLattice ϑ N (t + (d N : ℝ) / (N : ℝ)) h₀ x ω := by
      dsimp [C, testedForwardClockPerturbation]
      exact integral_testFn_mul_sub_eq φ _ _
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N t h₀ ω) Set.univ)
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N (t + (d N : ℝ) / (N : ℝ)) h₀ ω) Set.univ)
    have hleft := measurable_integral_kpzLattice_testPairing ϑ N t h₀ φ
    have hright := measurable_integral_kpzLattice_testPairing
      ϑ N (t + (d N : ℝ) / (N : ℝ)) h₀ φ
    have hfun : (fun ω : Disorder => C N ω) = fun ω =>
        (∫ x, φ x * kpzLattice ϑ N t h₀ x ω) -
          ∫ x, φ x * kpzLattice ϑ N (t + (d N : ℝ) / (N : ℝ)) h₀ x ω := by
      funext ω
      exact hPair ω
    change Measurable (fun ω : Disorder => C N ω)
    rw [hfun]
    exact hleft.sub hright
  have hCone (N : ℕ) : eLpNorm (C N) 1 disorderLaw ≤ eLpNorm (C N) 2 disorderLaw :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ENNReal) ≤ 2)
  have hConeven : ∀ N : ℕ,
      eLpNorm (C N) 1 disorderLaw ≤ eLpNorm (C N) 2 disorderLaw := hCone
  have hConeTendsto : Tendsto (fun N : ℕ => eLpNorm (C N) 1 disorderLaw)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCtwo
      (Filter.Eventually.of_forall fun _ => bot_le)
    exact Filter.Eventually.of_forall hConeven
  let Ft : ℕ → Disorder → Plane → ℝ := fun N ω x => kpzLattice ϑ N t h₀ x ω
  let Fm : ℕ → Disorder → Plane → ℝ := fun N ω x =>
    kpzLattice ϑ N ((m N : ℝ) / N) h₀ x ω
  let Fshift : ℕ → Disorder → Plane → ℝ := fun N ω x =>
    kpzLattice ϑ N (t + (d N : ℝ) / (N : ℝ)) h₀ x ω
  let Fprime : ℕ → Disorder → Plane → ℝ := fun N ω x =>
    kpzLattice ϑ N ((m' N : ℝ) / N) h₀ x ω
  let Rtarget : ℕ → Disorder → Plane → ℝ := fun N ω x =>
    kpzLatticeReversed ϑ N (T - t) T h₀ x (PolymerCalculus.reversedDisorder (L N) ω)
  let Rr : ℕ → Disorder → Plane → ℝ := fun N ω x =>
    kpzLatticeReversed ϑ N (((r N : ℕ) : ℝ) / N) ((L N : ℝ) / N)
      h₀ x (PolymerCalculus.reversedDisorder (L N) ω)
  let Rq : ℕ → Disorder → Plane → ℝ := fun N ω x =>
    kpzLatticeReversed ϑ N (((L N - m N : ℕ) : ℝ) / N) ((L N : ℝ) / N)
      h₀ x (PolymerCalculus.reversedDisorder (L N) ω)
  let PT : ℕ → Disorder → ℝ := fun N ω => ∫ x, φ x * Ft N ω x
  let Pm : ℕ → Disorder → ℝ := fun N ω => ∫ x, φ x * Fm N ω x
  let Pshift : ℕ → Disorder → ℝ := fun N ω => ∫ x, φ x * Fshift N ω x
  let Pprime : ℕ → Disorder → ℝ := fun N ω => ∫ x, φ x * Fprime N ω x
  let Ptarget : ℕ → Disorder → ℝ := fun N ω => ∫ x, φ x * Rtarget N ω x
  let Pr : ℕ → Disorder → ℝ := fun N ω => ∫ x, φ x * Rr N ω x
  let Pq : ℕ → Disorder → ℝ := fun N ω => ∫ x, φ x * Rq N ω x
  let Target : ℕ → Disorder → ℝ := fun N ω =>
    ∫ x, φ x * (Ft N ω x - Rtarget N ω x)
  have hdecomp : ∀ᶠ N : ℕ in atTop, ∀ ω : Disorder,
      Target N ω = A N ω - B N ω + C N ω + D N ω := by
    filter_upwards [eventually_gt_atTop 0, hshiftClock] with N hN hclock
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hmScaled : evenCeil ((N : ℝ) * ((m N : ℝ) / (N : ℝ))) = m N :=
      Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN (hEvenM N)
    have hLScaled : evenCeil ((N : ℝ) * ((L N : ℝ) / (N : ℝ))) = L N :=
      Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN (hEvenL N)
    have hrScaled : evenCeil ((N : ℝ) * ((r N : ℝ) / (N : ℝ))) = r N :=
      Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN (hEvenR N)
    have hm'Scaled : evenCeil ((N : ℝ) * ((m' N : ℝ) / (N : ℝ))) = m' N :=
      Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN (hm'Even N)
    have hmTime : evenCeil ((N : ℝ) * t) = m N := rfl
    have hshiftEq := hclock.trans hm'Scaled.symm
    have hfieldTime (x : Plane) (ω : Disorder) : Ft N ω x = Fm N ω x := by
      exact kpzLattice_eq_of_evenClock_eq ϑ N (hmTime.trans hmScaled.symm) h₀ x ω
    have hfieldShift (x : Plane) (ω : Disorder) : Fshift N ω x = Fprime N ω x := by
      exact kpzLattice_eq_of_evenClock_eq ϑ N hshiftEq h₀ x ω
    have hrevTime : evenCeil ((N : ℝ) * (T - t)) = r N := rfl
    have hLTime : evenCeil ((N : ℝ) * T) = L N := rfl
    have hrevField (x : Plane) (ω : Disorder) : Rtarget N ω x = Rr N ω x := by
      dsimp [Rtarget, Rr]
      simp only [kpzLatticeReversed, hrevTime, hLTime, hrScaled, hLScaled]
    intro ω
    have htargetPair : Target N ω = PT N ω - Ptarget N ω := by
      exact integral_testFn_mul_sub_eq φ _ _
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N t h₀ ω) Set.univ)
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLatticeReversed_locallyIntegrable ϑ N (T - t) T h₀
            (PolymerCalculus.reversedDisorder (L N) ω)) Set.univ)
    have hAeq : A N ω = PT N ω - Pq N ω := by
      exact integral_testFn_mul_sub_eq φ _ _
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N t h₀ ω) Set.univ)
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLatticeReversed_locallyIntegrable ϑ N (((L N - m N : ℕ) : ℝ) / N)
            ((L N : ℝ) / N) h₀ (PolymerCalculus.reversedDisorder (L N) ω)) Set.univ)
    have hBeq : B N ω = Pm N ω - Pq N ω := by
      exact integral_testFn_mul_sub_eq φ _ _
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N ((m N : ℝ) / N) h₀ ω) Set.univ)
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLatticeReversed_locallyIntegrable ϑ N (((L N - m N : ℕ) : ℝ) / N)
            ((L N : ℝ) / N) h₀ (PolymerCalculus.reversedDisorder (L N) ω)) Set.univ)
    have hCeq : C N ω = Pm N ω - Pshift N ω := by
      have h := integral_testFn_mul_sub_eq φ _ _
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N t h₀ ω) Set.univ)
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N (t + (d N : ℝ) / (N : ℝ)) h₀ ω) Set.univ)
      have hPTm : (∫ x, φ x * kpzLattice ϑ N t h₀ x ω) = Pm N ω := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact congrArg (fun z : ℝ => φ x * z) (hfieldTime x ω)
      dsimp [C, Pshift] at h ⊢
      rw [hPTm] at h
      exact h
    have hDeq : D N ω = Pprime N ω - Pr N ω := by
      exact integral_testFn_mul_sub_eq φ _ _
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N ((m' N : ℝ) / N) h₀ ω) Set.univ)
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLatticeReversed_locallyIntegrable ϑ N (((r N : ℕ) : ℝ) / N)
            ((L N : ℝ) / N) h₀ (PolymerCalculus.reversedDisorder (L N) ω)) Set.univ)
    have hPTm : PT N ω = Pm N ω := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg (fun z : ℝ => φ x * z) (hfieldTime x ω)
    have hPshift : Pshift N ω = Pprime N ω := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg (fun z : ℝ => φ x * z) (hfieldShift x ω)
    have hPtarget : Ptarget N ω = Pr N ω := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg (fun z : ℝ => φ x * z) (hrevField x ω)
    rw [htargetPair, hAeq, hBeq, hCeq, hDeq, hPTm, hPshift, hPtarget]
    ring
  have hsum : Tendsto (fun N : ℕ =>
      ((eLpNorm (A N) 1 disorderLaw + eLpNorm (B N) 1 disorderLaw) +
        eLpNorm (C N) 1 disorderLaw) + eLpNorm (D N) 1 disorderLaw)
      atTop (𝓝 0) := by
    simpa using (((hA.add hB).add hConeTendsto).add hD)
  have htriangle : ∀ᶠ N : ℕ in atTop,
      eLpNorm (Target N) 1 disorderLaw ≤
        ((eLpNorm (A N) 1 disorderLaw + eLpNorm (B N) 1 disorderLaw) +
          eLpNorm (C N) 1 disorderLaw) + eLpNorm (D N) 1 disorderLaw := by
    filter_upwards [hdecomp] with N hN
    have hfun : Target N = fun ω => A N ω - B N ω + C N ω + D N ω := by
      funext ω
      exact hN ω
    rw [hfun]
    calc
      _ ≤ eLpNorm (A N - B N + C N) 1 disorderLaw + eLpNorm (D N) 1 disorderLaw :=
        eLpNorm_add_le (f := A N - B N + C N) (g := D N)
          (by norm_num : (1 : ENNReal) ≤ 1)
      _ ≤ (eLpNorm (A N - B N) 1 disorderLaw + eLpNorm (C N) 1 disorderLaw) +
          eLpNorm (D N) 1 disorderLaw := by
        exact add_le_add_left
          (eLpNorm_add_le (f := A N - B N) (g := C N)
            (by norm_num : (1 : ENNReal) ≤ 1)) _
      _ ≤ ((eLpNorm (A N) 1 disorderLaw + eLpNorm (B N) 1 disorderLaw) +
          eLpNorm (C N) 1 disorderLaw) + eLpNorm (D N) 1 disorderLaw := by
        have hsub : eLpNorm (A N - B N) 1 disorderLaw ≤
            eLpNorm (A N) 1 disorderLaw + eLpNorm (B N) 1 disorderLaw :=
          eLpNorm_sub_le (f := A N) (g := B N)
            (by norm_num : (1 : ENNReal) ≤ 1)
        exact add_le_add_left (add_le_add_left hsub (eLpNorm (C N) 1 disorderLaw))
          (eLpNorm (D N) 1 disorderLaw)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => bot_le)
  exact htriangle

/-- The finite vector of tested forward fields is close in `L¹` to the reversed vector under the reversal coupling. -/
theorem tendsto_eLpNorm_tested_kpzLattice_reverse_vector
    (ϑ T : ℝ) (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ))
    (φ : Fin k → TestFn) (ht : ∀ i, 0 < t i ∧ t i ≤ T) :
    Tendsto (fun N : ℕ => eLpNorm (fun ω : Disorder =>
      ‖(fun i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω) -
        (fun i => ∫ x, φ i x * kpzLatticeReversed ϑ N (T - t i) T (h₀ i) x
          (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω))‖)
      1 disorderLaw) atTop (𝓝 0) := by
  classical
  let X : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω
  let Y : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * kpzLatticeReversed ϑ N (T - t i) T (h₀ i) x ω
  let Yrev : ℕ → Disorder → Fin k → ℝ := fun N ω =>
    Y N (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)
  have hXcoord (N : ℕ) (i : Fin k) : Measurable (fun ω : Disorder => X N ω i) := by
    simpa [X] using measurable_integral_kpzLattice_testPairing
      ϑ N (t i) (h₀ i) (φ i)
  have hX (N : ℕ) : AEMeasurable (X N) disorderLaw := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact (hXcoord N i).aemeasurable
  have hY (N : ℕ) : AEMeasurable (Y N) disorderLaw := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact JointConvergence.aemeasurable_integral_kpzLatticeReversed
      ϑ N (T - t i) T (h₀ i) (φ i)
  have hYrev (N : ℕ) : AEMeasurable (Yrev N) disorderLaw := by
    let L : ℕ := evenCeil ((N : ℝ) * T)
    have hmp := PolymerCalculus.measurePreserving_reversedDisorder L
    have h := (hY N).aestronglyMeasurable.comp_measurePreserving hmp
    exact h.aemeasurable
  have hDmeas (N : ℕ) : AEStronglyMeasurable (fun ω : Disorder => X N ω - Yrev N ω)
      disorderLaw := (hX N).aestronglyMeasurable.sub (hYrev N).aestronglyMeasurable
  have hDcoord (N : ℕ) (i : Fin k) : AEStronglyMeasurable
      (fun ω : Disorder => X N ω i - Yrev N ω i) disorderLaw :=
    ((hX N).eval i).aestronglyMeasurable.sub ((hYrev N).eval i).aestronglyMeasurable
  have hcoord (i : Fin k) : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω : Disorder => X N ω i - Yrev N ω i) 1 disorderLaw)
      atTop (𝓝 0) := by
    let d : ℕ → ℤ := fun N =>
      (((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * (T - t i)) : ℕ) : ℤ) -
        (evenCeil ((N : ℝ) * (t i) : ℝ) : ℤ))
    have hd (N : ℕ) : d N = -2 ∨ d N = 0 ∨ d N = 2 := by
      have h := kpzLattice_reverseClockShift_spec N T (ht i).1 (ht i).2
      dsimp [d] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hExact := tendsto_eLpNorm_tested_exactReverseField_error
      ϑ (t i) T (ht i).1 (ht i).2 (h₀ i) (φ i)
    have hPerturb := tendsto_eLpNorm_tested_kpzLattice_evenClockPerturb
      ϑ (t i) (ht i).1 (h₀ i) (φ i) d hd
    have hPerturb' : Tendsto (fun N : ℕ => eLpNorm
        (testedForwardClockPerturbation ϑ N (t i) (h₀ i) (φ i)
          ((((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * (T - t i)) : ℕ) : ℤ) -
            (evenCeil ((N : ℝ) * (t i) : ℝ) : ℤ))))
        2 disorderLaw) atTop (𝓝 0) := by
      change Tendsto (fun N : ℕ => eLpNorm
        (testedForwardClockPerturbation ϑ N (t i) (h₀ i) (φ i) (d N))
        2 disorderLaw) atTop (𝓝 0) at hPerturb
      exact hPerturb
    have hcoordinate := tendsto_eLpNorm_tested_kpzLattice_reverse_coordinate_of_helpers
      ϑ T (t i) (ht i).1 (ht i).2 (h₀ i) (φ i) hExact hPerturb'
    have hpair (N : ℕ) (ω : Disorder) : X N ω i - Yrev N ω i =
        ∫ x, φ i x * (kpzLattice ϑ N (t i) (h₀ i) x ω -
          kpzLatticeReversed ϑ N (T - t i) T (h₀ i) x
            (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)) := by
      dsimp [X, Yrev, Y]
      symm
      exact integral_testFn_mul_sub_eq (φ i) _ _
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLattice_locallyIntegrable ϑ N (t i) (h₀ i) ω) Set.univ)
        (LocallyIntegrable.locallyIntegrableOn
          (kpzLatticeReversed_locallyIntegrable ϑ N (T - t i) T (h₀ i)
            (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)) Set.univ)
    have hfun : (fun N : ℕ => eLpNorm (fun ω : Disorder => X N ω i - Yrev N ω i)
        1 disorderLaw) = (fun N => eLpNorm (fun ω : Disorder =>
          ∫ x, φ i x * (kpzLattice ϑ N (t i) (h₀ i) x ω -
            kpzLatticeReversed ϑ N (T - t i) T (h₀ i) x
              (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)))
          1 disorderLaw) := by
      funext N
      congr 2
      funext ω
      exact hpair N ω
    rw [hfun]
    exact hcoordinate
  have hcoordNormTendsto (i : Fin k) : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω : Disorder => ‖X N ω i - Yrev N ω i‖) 1 disorderLaw)
      atTop (𝓝 0) := by
    have hnormEq : (fun N : ℕ =>
        eLpNorm (fun ω : Disorder => ‖X N ω i - Yrev N ω i‖) 1 disorderLaw) =
        fun N => eLpNorm (fun ω : Disorder => X N ω i - Yrev N ω i)
          1 disorderLaw := by
      funext N
      exact eLpNorm_norm _ (hDcoord N i)
    rw [hnormEq]
    exact hcoord i
  have hsumTendsto : Tendsto (fun N : ℕ => ∑ i : Fin k,
      eLpNorm (fun ω : Disorder => ‖X N ω i - Yrev N ω i‖) 1 disorderLaw)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hcoordNormTendsto i)
  have hvectorBound (N : ℕ) (ω : Disorder) :
      ‖X N ω - Yrev N ω‖ ≤ ∑ i : Fin k, ‖X N ω i - Yrev N ω i‖ := by
    rw [pi_norm_le_iff_of_nonneg (r := ∑ i : Fin k, ‖X N ω i - Yrev N ω i‖)
      (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    intro i
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have hLpBound (N : ℕ) : eLpNorm (fun ω : Disorder => ‖X N ω - Yrev N ω‖)
      1 disorderLaw ≤ ∑ i : Fin k,
        eLpNorm (fun ω : Disorder => ‖X N ω i - Yrev N ω i‖) 1 disorderLaw := by
    have hsumFun : (fun ω : Disorder => ∑ i : Fin k,
        ‖X N ω i - Yrev N ω i‖) =
        ∑ i : Fin k, (fun ω : Disorder => ‖X N ω i - Yrev N ω i‖) := by
      funext ω
      simp
    calc
      _ = eLpNorm (fun ω : Disorder => X N ω - Yrev N ω) 1 disorderLaw :=
        eLpNorm_norm _ (hDmeas N)
      _ ≤ eLpNorm (fun ω : Disorder => ∑ i : Fin k,
          ‖X N ω i - Yrev N ω i‖) 1 disorderLaw :=
        eLpNorm_mono_real (hDmeas N) (fun ω => hvectorBound N ω)
      _ = eLpNorm (∑ i : Fin k, (fun ω : Disorder =>
          ‖X N ω i - Yrev N ω i‖)) 1 disorderLaw := by rw [hsumFun]
      _ ≤ ∑ i : Fin k, eLpNorm (fun ω : Disorder =>
          ‖X N ω i - Yrev N ω i‖) 1 disorderLaw := by
        simpa using eLpNorm_sum_le (p := (1 : ENNReal))
          (μ := disorderLaw) (s := Finset.univ)
          (f := fun i ω => ‖X N ω i - Yrev N ω i‖) (by norm_num)
  have hvectorTendsto : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω : Disorder => ‖X N ω - Yrev N ω‖) 1 disorderLaw)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumTendsto
      (Filter.Eventually.of_forall fun _ => bot_le)
    exact Filter.Eventually.of_forall hLpBound
  simpa [X, Yrev, Y] using hvectorTendsto

/-- The forward and reversed fields have asymptotically equal bounded-continuous test laws. -/
theorem kpzLattice_reverse_law_close (ϑ T : ℝ) (k : ℕ) (t : Fin k → ℝ)
    (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn)
    (ht : ∀ i, 0 < t i ∧ t i ≤ T) (g : (Fin k → ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ =>
        (∫ ω, g (fun i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω) ∂disorderLaw) -
          ∫ ω, g (fun i => ∫ x, φ i x * kpzLatticeReversed ϑ N (T - t i) T
            (h₀ i) x ω) ∂disorderLaw)
      atTop (𝓝 0) := by
  have hVD : Smoothing.PropVDBound := fun A => Critical2DKPZ.Provider.prop_VD A
  have hsecond := kpzLattice_testFnTuple_second_moment_le_of hVD ϑ t
    (fun i => (ht i).1) h₀ φ
  have hclose := tendsto_eLpNorm_tested_kpzLattice_reverse_vector
    ϑ T k t h₀ φ ht
  exact tendsto_integral_kpzLattice_reverse_sub_of_tested_L1
    ϑ T k t h₀ φ ht g
    tendsto_integral_bddContinuous_sub_of_L2_tightness hsecond hclose

end Critical2DKPZ.LocalSobolev

end
