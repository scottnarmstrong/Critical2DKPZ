/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceWindowsHorizon
import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceFullL1
import Mathlib.Tactic

/-! # Full-clock convergence with an interior compact entrance cutoff -/

@[expose] public noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter DeltaBose
open scoped CompactlySupported Topology

/-- A compact collision cutoff has a closed time support strictly inside the
positive horizon. The extra midpoint handles an identically zero cutoff. -/
theorem pairTwo_cutoff_time_bounds {T : ℝ} (hT : 0 < T)
    (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < T ∧
      ∀ p : ℝ × Plane, η p ≠ 0 → a ≤ p.1 ∧ p.1 ≤ b := by
  let K : Set ℝ := Prod.fst '' tsupport η ∪ {T / 2}
  have hK : IsCompact K :=
    (η.hasCompactSupport.isCompact.image continuous_fst).union (isCompact_singleton : IsCompact ({T / 2} : Set ℝ))
  have hne : K.Nonempty := ⟨T / 2, Or.inr (Set.mem_singleton _)⟩
  have hKT : ∀ u ∈ K, 0 < u ∧ u < T := by
    intro u hu
    rcases hu with ⟨p, hp, rfl⟩ | hu
    · exact hη p hp
    · rw [Set.mem_singleton_iff] at hu
      subst u
      constructor <;> linarith only [hT]
  obtain ⟨a, ha⟩ := hK.exists_isLeast hne
  obtain ⟨b, hb⟩ := hK.exists_isGreatest hne
  refine ⟨a, b, (hKT a ha.1).1, ha.2 hb.1, (hKT b hb.1).2, ?_⟩
  intro p hp
  have hpK : p.1 ∈ K := Or.inl ⟨p, subset_closure hp, rfl⟩
  exact ⟨ha.2 hpK, hb.2 hpK⟩

/-- Once the compact cutoff is enclosed in an interior clock slab, its
full-clock entrance sum agrees exactly with the restricted entrance sum. -/
theorem eventually_pairTwoTestedEntranceWindow_eq_interior_cutoff
    (ϑ T : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {a b s t : ℝ} (hs : 0 < s) (hst : s < t) (hsa : s < a) (hbt : b < t) (htT : t < T)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p : ℝ × Plane, η p ≠ 0 → a ≤ p.1 ∧ p.1 ≤ b) :
    ∀ᶠ N : ℕ in atTop,
      pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ η =
        pairTwoTestedEntranceWindow ϑ N (L N)
          (evenCeil (N * s) + 1) (evenCeil (N * t)) φ η := by
  have ht : 0 < t := hs.trans hst
  have hlo := (tendsto_evenCeil_div s hs.le).eventually (Iio_mem_nhds hsa)
  have hhi := (tendsto_evenCeil_div t ht.le).eventually
    (Iio_mem_nhds (show t < (t + T) / 2 by linarith only [htT]))
  have hLL := hL.eventually (Ioi_mem_nhds
    (show (t + T) / 2 < T by linarith only [htT]))
  filter_upwards [hlo, hhi, hLL, eventually_gt_atTop 0] with N hloN hhiN hLLN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hupper : evenCeil (N * t) ≤ L N := by
    have hh : (evenCeil (N * t) : ℝ) / N < (L N : ℝ) / N := hhiN.trans hLLN
    exact_mod_cast ((div_lt_div_iff_of_pos_right hNr).mp hh).le
  have hsub : Finset.Icc (evenCeil (N * s) + 1) (evenCeil (N * t)) ⊆
      Finset.Icc 1 (L N) := by
    intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    exact ⟨by omega, hr.2.trans hupper⟩
  unfold pairTwoTestedEntranceWindow
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  symm
  unfold collisionEntrance
  apply Finset.sum_subset hsub
  intro r _hr hrout
  have hz (z : Site) : η ((r : ℝ) / N, latticeRepresentative N z) = 0 := by
    by_contra hzero
    obtain ⟨hra, hrb⟩ := hη _ hzero
    have hrlo : evenCeil (N * s) + 1 ≤ r := by
      have hh := (div_lt_div_iff_of_pos_right hNr).mp (hloN.trans_le hra)
      have hh' : evenCeil (N * s) < r := by exact_mod_cast hh
      omega
    have htceil : t ≤ (evenCeil (N * t) : ℝ) / N := by
      apply (le_div_iff₀ hNr).mpr
      simpa only [mul_comm] using Critical2DKPZ.le_evenCeil (N * t)
    have hrhi : r ≤ evenCeil (N * t) := by
      have hh := (div_le_div_iff_of_pos_right hNr).mp (hrb.trans (hbt.le.trans htceil))
      exact_mod_cast hh
    exact hrout (Finset.mem_Icc.mpr ⟨hrlo, hrhi⟩)
  unfold collisionSlice
  apply Finset.sum_eq_zero
  intro z _hz
  change srwKernel r (z - x 0) * srwKernel r (z - x 1) *
    (η ((r : ℝ) / N, latticeRepresentative N z) *
      pairTwoFutureSampleProfile ϑ N (L N) φ x ((r : ℝ) / N, latticeRepresentative N z)) = 0
  rw [hz, zero_mul, mul_zero]


private theorem integral_pairTwo_entrance_reorder (α : Measure ℝ) [SFinite α]
    (F : ℝ × (Plane × (Plane × Plane)) → ℝ)
    (hF : Integrable F (α.prod ((volume : Measure Plane).prod
      ((volume : Measure Plane).prod volume)))) :
    (∫ q, F q ∂α.prod ((volume : Measure Plane).prod
      ((volume : Measure Plane).prod volume))) =
      ∫ p : Plane × Plane, ∫ u : ℝ, ∫ z : Plane,
        F (u, p.1, z, p.2) ∂volume ∂α := by
  let ν : Measure Plane := volume
  let e₁ : Plane × (Plane × Plane) ≃ᵐ Plane × (Plane × Plane) :=
    MeasurableEquiv.prodAssoc.symm |>.trans
      ((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl Plane)) |>.trans
      MeasurableEquiv.prodAssoc
  let e : (Plane × Plane) × (ℝ × Plane) ≃ᵐ ℝ × (Plane × (Plane × Plane)) :=
    MeasurableEquiv.prodComm.trans (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl ℝ).prodCongr e₁))
  have h₁ : MeasurePreserving e₁ (ν.prod (ν.prod ν)) (ν.prod (ν.prod ν)) := by
    exact (measurePreserving_prodAssoc ν ν ν).comp
      ((Measure.measurePreserving_swap.prod (MeasurePreserving.id ν)).comp
        (measurePreserving_prodAssoc ν ν ν).symm)
  have he : MeasurePreserving e ((ν.prod ν).prod (α.prod ν))
      (α.prod (ν.prod (ν.prod ν))) := by
    exact ((MeasurePreserving.id α).prod h₁).comp
      ((measurePreserving_prodAssoc α ν (ν.prod ν)).comp Measure.measurePreserving_swap)
  have hi : Integrable (fun q => F (e q)) ((ν.prod ν).prod (α.prod ν)) :=
    he.integrable_comp_of_integrable hF
  have hirows := hi.prod_right_ae
  calc
    _ = ∫ q, F (e q) ∂(ν.prod ν).prod (α.prod ν) := (he.integral_comp' F).symm
    _ = ∫ p : Plane × Plane, ∫ q : ℝ × Plane, F (e (p, q)) ∂α.prod ν :=
      integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hirows] with p hp
      exact integral_prod _ hp

/-- The interior cutoff entrance has exactly four times the full joint
continuum integral. Absolute integrability justifies the change of order. -/
theorem pairTwo_cutoff_continuum_integral_eq_full
    (θ T : ℝ) (hT : 0 < T) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (htT : t < T)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p : ℝ × Plane, η p ≠ 0 → s < p.1 ∧ p.1 < t) :
    (∫ p : Plane × Plane, pairTwoContinuumCutoffEntrance θ T s t φ η p) =
      4 * (∫ p : ℝ × (Plane × (Plane × Plane)),
        η (p.1, p.2.2.1) *
          ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
            pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1)
        ∂(volume.restrict (Set.Ioo 0 T)).prod
          ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))) := by
  let F := fun p : ℝ × (Plane × (Plane × Plane)) =>
    η (p.1, p.2.2.1) *
      ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
        pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1)
  have hi : Integrable F ((volume.restrict (Set.Ioo 0 T)).prod
      ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))) := by
    apply (integrable_pairTwo_continuum_entrance θ T hT φ).bdd_mul
    · exact (η.continuous.comp (continuous_fst.prodMk continuous_snd.snd.fst)).aestronglyMeasurable
    · exact Eventually.of_forall fun p => η.toBoundedContinuousFunction.norm_coe_le_norm _
  have he := integral_pairTwo_entrance_reorder (volume.restrict (Set.Ioo 0 T)) F hi
  rw [he]
  simp only [pairTwoContinuumCutoffEntrance, integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    let g : ℝ → ℝ := fun u => ∫ z : Plane, F (u, p.1, z, p.2)
    have hz (u : ℝ) (hu : u ∉ Set.Ioc s t) : g u = 0 := by
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun z => by
        have hηzero : η (u, z) = 0 := by
          by_contra hn
          obtain ⟨hlo, hhi⟩ := hη (u, z) hn
          exact hu ⟨hlo, hhi.le⟩
        change η (u, z) * _ = 0
        rw [hηzero, zero_mul]
    have hzfull (u : ℝ) (hu : u ∉ Set.Ioo 0 T) : g u = 0 := by
      apply hz
      intro hst'
      exact hu ⟨hs.trans hst'.1, hst'.2.trans_lt htT⟩
    have hg : (∫ u in s..t, g u) = ∫ u in Set.Ioo 0 T, g u := by
      rw [intervalIntegral.integral_of_le hst.le,
        setIntegral_eq_integral_of_forall_compl_eq_zero hz,
        setIntegral_eq_integral_of_forall_compl_eq_zero hzfull]
    convert hg using 1
    apply intervalIntegral.integral_congr
    intro u _hu
    unfold heatKernelPairProfileIntegral
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only [g, F]
      have hk : heatKernel u (z - p.2) = heatKernel u (p.2 - z) := by
        rw [← heatKernel_neg u (z - p.2), neg_sub]
      rw [hk]
      ring

/-- A compact cutoff inside the positive horizon permits full-clock entrance
convergence. The exact coefficient is one quarter after the incoming average. -/
theorem tendsto_pairTwoTestedEntranceWindow_full_cutoff
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) :
    Tendsto (fun N => pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ η) atTop
      (𝓝 ((1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
        η (p.1, p.2.2.1) *
          ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
            pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1)
              φ ![p.2.1, p.2.2.2] p.2.2.1)
        ∂(volume.restrict (Set.Ioo 0 T)).prod
          ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))))) := by
  obtain ⟨a, b, ha, hab, hbT, hbounds⟩ := pairTwo_cutoff_time_bounds hT η hη
  let s := a / 2
  let t := (b + T) / 2
  have hs : 0 < s := by dsimp only [s]; linarith only [ha]
  have hsa : s < a := by dsimp only [s]; linarith only [ha]
  have hbt : b < t := by dsimp only [t]; linarith only [hbT]
  have htT : t < T := by dsimp only [t]; linarith only [hbT]
  have hst : s < t := hsa.trans (hab.trans_lt hbt)
  have hinside : ∀ p : ℝ × Plane, η p ≠ 0 → s < p.1 ∧ p.1 < t := by
    intro p hp
    exact ⟨hsa.trans_le (hbounds p hp).1, (hbounds p hp).2.trans_lt hbt⟩
  have heq := eventually_pairTwoTestedEntranceWindow_eq_interior_cutoff
    ϑ T L hL hs hst hsa hbt htT φ η hbounds
  have hlim := tendsto_pairTwoTestedEntranceWindow_cutoff_horizon
    ϑ T hT L hL hs hst φ η hη
  have hvalue := pairTwo_cutoff_continuum_integral_eq_full
    (ϑ - Real.eulerMascheroniConstant) T hT hs hst htT φ η hinside
  rw [hvalue] at hlim
  have hc : (1 / 16 : ℝ) * (4 * (∫ p : ℝ × (Plane × (Plane × Plane)),
      η (p.1, p.2.2.1) *
        ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
          pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1)
            φ ![p.2.1, p.2.2.2] p.2.2.1)
      ∂(volume.restrict (Set.Ioo 0 T)).prod
        ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)))) =
      (1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
      η (p.1, p.2.2.1) *
        ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
          pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1)
            φ ![p.2.1, p.2.2.2] p.2.2.1)
      ∂(volume.restrict (Set.Ioo 0 T)).prod
        ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))) := by ring
  rw [hc] at hlim
  apply hlim.congr'
  filter_upwards [heq] with N hN
  exact hN.symm

end Critical2DKPZ.SHF.Moments
