/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichJetNets
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichConvolutionJets
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichMollificationClosed
public import Critical2DKPZ.Analysis.Sobolev.Rellich.Additivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite Sobolev nets for mollified functions and compact Sobolev embeddings.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- The mollified Sobolev unit ball has finite Sobolev nets with mollified centres. -/
theorem exists_finite_convReal_sobolev_net {d : ℕ} {D : Set (Space d)}
    (hD : Bornology.IsBounded D) {ρ : Space d → ℝ}
    (hρsm : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ)
    (s s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ T : Set (Space d → ℝ),
      T ⊆ (fun φ => convReal φ ρ) '' {φ | IsTestFn D φ ∧ sobolevNormSq d s φ ≤ 1} ∧
      T.Finite ∧ ∀ φ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
        ∃ g ∈ T, sobolevNormSq d s₀ (fun x => convReal φ ρ x - g x)
          ≤ ENNReal.ofReal η := by
  let S := {φ : Space d → ℝ | IsTestFn D φ ∧ sobolevNormSq d s φ ≤ 1}
  let U := (fun φ => convReal φ ρ) '' S
  let K := tsupport ρ + closure D
  have hK : IsCompact K := hρcs.isCompact.add hD.isCompact_closure
  have hsm : ∀ f ∈ U, ContDiff ℝ (⊤ : ℕ∞) f := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact contDiff_convReal hφ.1.integrable.locallyIntegrable hρsm hρcs
  have hsupp : ∀ f ∈ U, tsupport f ⊆ K := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact tsupport_convReal_subset_sum hD hφ.1 hρcs
  have hjets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f ∈ U, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
    intro m
    obtain ⟨C, hC, hbound⟩ := exists_convReal_uniform_jets hD hρsm hρcs s m
    refine ⟨C, hC.le, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩ k hk x
    exact hbound φ hφ.1 hφ.2 k hk x
  obtain ⟨T, hTU, hTfin, hnet⟩ :=
    exists_finite_sobolev_net_of_uniform_jets hK U hsm hsupp hjets s₀ hη
  refine ⟨T, hTU, hTfin, ?_⟩
  intro φ hφ hunit
  exact hnet (convReal φ ρ) ⟨φ, ⟨hφ, hunit⟩, rfl⟩

private theorem sobolevNormSq_reverse_sub {d : ℕ} (s : ℝ) (f g : Space d → ℝ) :
    sobolevNormSq d s (fun x => f x - g x) =
      sobolevNormSq d s (fun x => g x - f x) := by
  have he : (fun x => f x - g x) = fun x => (-1 : ℝ) * (g x - f x) := by
    funext x
    ring
  rw [he, sobolevNormSq_const_mul]
  norm_num

private theorem sobolev_three_error_transfer {d : ℕ} (s : ℝ)
    (f a b g : Space d → ℝ)
    (hf : Integrable f) (ha : Integrable a) (hb : Integrable b) (hg : Integrable g)
    {q : ℝ} (_hq : 0 ≤ q)
    (hfa : sobolevNormSq d s (fun x => f x - a x) ≤ ENNReal.ofReal q)
    (hab : sobolevNormSq d s (fun x => a x - b x) ≤ ENNReal.ofReal q)
    (hbg : sobolevNormSq d s (fun x => b x - g x) ≤ ENNReal.ofReal q) :
    sobolevNormSq d s (fun x => f x - g x) ≤ ENNReal.ofReal (10 * q) := by
  have h1 : Integrable (fun x => ((f x - a x : ℝ) : ℂ)) := by
    exact (hf.sub ha).ofReal (𝕜 := ℂ)
  have h2 : Integrable (fun x => ((a x - b x : ℝ) : ℂ)) := by
    exact (ha.sub hb).ofReal (𝕜 := ℂ)
  have h3 : Integrable (fun x => ((b x - g x : ℝ) : ℂ)) := by
    exact (hb.sub hg).ofReal (𝕜 := ℂ)
  have h2' : Integrable (fun x => ((a x - g x : ℝ) : ℂ)) := by
    exact (ha.sub hg).ofReal (𝕜 := ℂ)
  have hin := sobolevNormSq_add_le d s
    (fun x => a x - b x) (fun x => b x - g x) h2 h3
  have hout := sobolevNormSq_add_le d s
    (fun x => f x - a x) (fun x => a x - g x) h1 h2'
  rw [show (fun x => (a x - b x) + (b x - g x)) = fun x => a x - g x by
    funext x; ring] at hin
  rw [show (fun x => (f x - a x) + (a x - g x)) = fun x => f x - g x by
    funext x; ring] at hout
  have hmid : sobolevNormSq d s (fun x => a x - g x) ≤
      2 * ENNReal.ofReal q + 2 * ENNReal.ofReal q :=
    hin.trans (add_le_add (mul_le_mul_right hab 2) (mul_le_mul_right hbg 2))
  calc sobolevNormSq d s (fun x => f x - g x)
      ≤ 2 * ENNReal.ofReal q + 2 * (2 * ENNReal.ofReal q + 2 * ENNReal.ofReal q) :=
        hout.trans (add_le_add (mul_le_mul_right hfa 2) (mul_le_mul_right hmid 2))
    _ = 10 * ENNReal.ofReal q := by ring
    _ = ENNReal.ofReal (10 * q) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num

/-- The Rellich finite-net theorem, with its centers retained in the stronger Sobolev unit ball.
The extra conclusion makes uniform coordinate bounds immediate from a stronger negative-norm
bound. -/
theorem rellichKondrachovNegSobolev_holds_with_unit_centers :
    ∀ (d : ℕ) (D : Set (Critical2DKPZ.Analysis.Sobolev.Rellich.Space d)),
    Critical2DKPZ.Analysis.Sobolev.Rellich.IsDomain D →
    ∀ (s₀ s : ℝ), s₀ < s → ∀ η : ℝ, 0 < η →
      ∃ (N : ℕ) (ψ : Fin N → Critical2DKPZ.Analysis.Sobolev.Rellich.Space d → ℝ),
        (∀ i, Critical2DKPZ.Analysis.Sobolev.Rellich.IsTestFn D (ψ i) ∧
          Critical2DKPZ.Analysis.Sobolev.Rellich.sobolevNormSq d s (ψ i) ≤ 1) ∧
        ∀ φ : Critical2DKPZ.Analysis.Sobolev.Rellich.Space d → ℝ, Critical2DKPZ.Analysis.Sobolev.Rellich.IsTestFn D φ →
          Critical2DKPZ.Analysis.Sobolev.Rellich.sobolevNormSq d s φ ≤ 1 →
            ∃ i, Critical2DKPZ.Analysis.Sobolev.Rellich.sobolevNormSq d s₀ (fun x => φ x - ψ i x)
              ≤ ENNReal.ofReal (η ^ 2) := by
  classical
  intro d D hD s₀ s hlt η hη
  let q := η ^ 2 / 16
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨ρ, hρsm, hρcs, hρmass, hρnonneg, hmoll⟩ :=
    exists_uniform_testFn_mollifier (d := d) hlt q hq
  have hρint : Integrable ρ := hρsm.continuous.integrable_of_hasCompactSupport hρcs
  obtain ⟨T, hTsub, hTfin, hTnet⟩ :=
    exists_finite_convReal_sobolev_net hD.2.1 hρsm hρcs s s₀ hq
  let S := {φ : Space d → ℝ | IsTestFn D φ ∧ sobolevNormSq d s φ ≤ 1}
  let : Fintype T := hTfin.fintype
  have hpre : ∀ g : T, ∃ φ : Space d → ℝ, φ ∈ S ∧ convReal φ ρ = g.val :=
    fun g => hTsub g.property
  choose pick hpickS hpick using hpre
  let e := Fintype.equivFin T
  let ψ (i : Fin (Fintype.card T)) := pick (e.symm i)
  refine ⟨Fintype.card T, ψ, ?_, ?_⟩
  · intro i
    exact ⟨(hpickS (e.symm i)).1, (hpickS (e.symm i)).2⟩
  · intro φ hφ hunit
    obtain ⟨g, hg, hfg⟩ := hTnet φ hφ hunit
    let u : T := ⟨g, hg⟩
    refine ⟨e u, ?_⟩
    have hψS : ψ (e u) ∈ S := by simpa [ψ] using hpickS u
    have heq : convReal (ψ (e u)) ρ = g := by simpa [ψ] using hpick u
    have hcentre : sobolevNormSq d s₀
        (fun x => convReal (ψ (e u)) ρ x - ψ (e u) x) ≤ ENNReal.ofReal q := by
      rw [sobolevNormSq_reverse_sub]
      exact hmoll (ψ (e u)) hψS.1.1 hψS.1.2.1 hψS.2
    have hφerror : sobolevNormSq d s₀ (fun x => φ x - convReal φ ρ x)
        ≤ ENNReal.ofReal q := hmoll φ hφ.1 hφ.2.1 hunit
    have hmiddle : sobolevNormSq d s₀
        (fun x => convReal φ ρ x - convReal (ψ (e u)) ρ x)
        ≤ ENNReal.ofReal q := by simpa [heq] using hfg
    have hφconv : Integrable (convReal φ ρ) :=
      Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hφ.integrable hρint
    have hψconv : Integrable (convReal (ψ (e u)) ρ) :=
      Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
        hψS.1.integrable hρint
    exact (sobolev_three_error_transfer s₀ φ (convReal φ ρ)
      (convReal (ψ (e u)) ρ) (ψ (e u)) hφ.integrable hφconv hψconv hψS.1.integrable
      hq.le hφerror hmiddle hcentre).trans
      (ENNReal.ofReal_le_ofReal (by dsimp [q]; nlinarith [sq_nonneg η]))

/-- The stronger test-function Sobolev unit ball has finite nets in the weaker Sobolev energy. -/
theorem rellichKondrachovNegSobolev_holds :
    ∀ (d : ℕ) (D : Set (Critical2DKPZ.Analysis.Sobolev.Rellich.Space d)),
    Critical2DKPZ.Analysis.Sobolev.Rellich.IsDomain D →
    ∀ (s₀ s : ℝ), s₀ < s → ∀ η : ℝ, 0 < η →
      ∃ (N : ℕ) (ψ : Fin N → Critical2DKPZ.Analysis.Sobolev.Rellich.Space d → ℝ),
        (∀ i, Critical2DKPZ.Analysis.Sobolev.Rellich.IsTestFn D (ψ i)) ∧
        ∀ φ : Critical2DKPZ.Analysis.Sobolev.Rellich.Space d → ℝ,
          Critical2DKPZ.Analysis.Sobolev.Rellich.IsTestFn D φ →
          Critical2DKPZ.Analysis.Sobolev.Rellich.sobolevNormSq d s φ ≤ 1 →
            ∃ i, Critical2DKPZ.Analysis.Sobolev.Rellich.sobolevNormSq d s₀
              (fun x => φ x - ψ i x) ≤ ENNReal.ofReal (η ^ 2) := by
  intro d D hD s₀ s hlt η hη
  obtain ⟨N, ψ, hψ, hnet⟩ :=
    rellichKondrachovNegSobolev_holds_with_unit_centers d D hD s₀ s hlt η hη
  exact ⟨N, ψ, fun i => (hψ i).1, hnet⟩

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
