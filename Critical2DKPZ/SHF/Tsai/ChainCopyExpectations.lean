/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainCoordinateCopies
public import Critical2DKPZ.SHF.Tsai.ChainPairingMeasurability
public import Critical2DKPZ.SHF.Tsai.SplitCopyBlocks
import Mathlib.Probability.IdentDistrib

/-! # Nonlinear chain expectations on a split product space

Independent coordinate copies preserve joint laws of tensor pairings, so separating one
probability coordinate preserves expectations of measurable functions of their finite sums.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Nonlinear tensor-sum expectations agree between independent blocks and their split copies. -/
theorem integral_comp_chain_eq_splitCopies {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k)) {m r : ℕ}
    (g g' : Fin m → Fin r → Plane → ℝ)
    (hgm : ∀ a b, Measurable (g a b)) (hg'm : ∀ a b, Measurable (g' a b))
    (H : (Fin m → ℝ) → ℝ) (hH : Measurable H) :
    (∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) w K) ∂P) =
      ∫ q : (Fin K → Ω) × Ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B q.1) j (B j q.2)) w K)
          ∂(Measure.pi (fun _ : Fin K => P)).prod P := by
  let R := Measure.pi (fun _ : Fin (K + 1) => P)
  let T (i : Fin m × Fin r) (p : Plane × Plane) := g i.1 i.2 p.1 * g' i.1 i.2 p.2
  have hT (i) : Measurable (T i) :=
    ((hgm i.1 i.2).comp measurable_fst).mul ((hg'm i.1 i.2).comp measurable_snd)
  let F (ω : Ω) (i : Fin m × Fin r) := ∫ p, T i p ∂chainProduct (fun k => B k ω) w K
  let G (ω : Fin (K + 1) → Ω) (i : Fin m × Fin r) :=
    ∫ p, T i p ∂chainProduct (coordinateCopyBlock K B ω) w K
  have hFm : Measurable F := Measurable.of_eval fun i =>
    measurable_integral_chainProduct K B hB (fun ω k hk => hlf k hk ω) w hw _ (hT i)
  have hGlf (ω : Fin (K + 1) → Ω) (k) (hk : k ≤ K) :
      IsLocallyFiniteMeasure (coordinateCopyBlock K B ω k) := by
    simp only [coordinateCopyBlock, dite_eq_left hk]
    exact hlf k hk _
  have hGm : Measurable G := Measurable.of_eval fun i =>
    measurable_integral_chainProduct K (fun k ω => coordinateCopyBlock K B ω k)
      (measurable_coordinateCopyBlock K B hB) hGlf w hw _ (hT i)
  have hLaw := map_chainReadouts_eq_coordinateCopies P K B hB
    (fun k hk => Filter.Eventually.of_forall (hlf k hk)) hind w hw T hT
  have hID : IdentDistrib F G P R := ⟨hFm.aemeasurable, hGm.aemeasurable, hLaw⟩
  let Φ (z : (Fin m × Fin r) → ℝ) := H (fun a => ∑ b, z (a, b))
  have hΦ : Measurable Φ := hH.comp (Measurable.of_eval fun a =>
    Finset.measurable_sum _ fun b _ => measurable_pi_apply (a, b))
  have hEq := (hID.comp hΦ).integral_eq
  have hφ := measurePreserving_insertCopyCoordinate P K j
  have hIntMeas : AEStronglyMeasurable (fun ω => Φ (G ω))
      (Measure.map (fun q : (Fin K → Ω) × Ω =>
        Fin.insertNth (α := fun _ : Fin (K + 1) => Ω) j q.2 q.1)
          ((Measure.pi (fun _ : Fin K => P)).prod P)) := by
    rw [hφ.map_eq]
    exact (hΦ.comp hGm).aestronglyMeasurable
  have hSplit := integral_map hφ.measurable.aemeasurable hIntMeas
  rw [hφ.map_eq] at hSplit
  exact hEq.trans (by
    simpa only [Φ, G, T, R, Function.comp_def, coordinateCopyBlock_insertNth_eq_update_outer] using hSplit)

end Critical2DKPZ.SHF.Tsai

end
