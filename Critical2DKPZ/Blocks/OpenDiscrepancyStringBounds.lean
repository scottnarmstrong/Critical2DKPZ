/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.DiscrepancyStringBounds
import Mathlib.Tactic

/-! # Open discrepancy-string moment bound -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal

namespace Critical2DKPZ.Blocks

private theorem openOccupiedRenewalTerm_le_of_backwardChain
    (N : ℕ) (ρ ϑ : ℝ) (u v : ℕ) (S : Finset ℕ)
    (C₅ Cchain Graw G D L : ℝ) (d : ℕ)
    (hC₅ : 0 < C₅) (hCchain : 0 < Cchain) (hDprod : C₅ * Cchain ≤ D)
    (hGrawpos : 0 < Graw) (hGrawleG : Graw ≤ G) (hG : 1 ≤ G) (hDone : 1 ≤ D)
    (hρone : 1 < ρ) (hLdef : L = Real.log ρ)
    (hLpos : 0 < L) (hLone : 1 ≤ L) (hLleρ : L ≤ ρ)
    (hN : 1 ≤ N) (hu : 1 ≤ u) (huv : u < v)
    (hvK : v + 1 ≤ blockCount N ρ) (hd : d = v - u)
    (hgridLocal : ∀ i, 1 ≤ i → i < blockCount N ρ →
      4 * ((blockTime N ρ (i - 1) : ℝ) + 1 / 2) ≤
        (blockTime N ρ i : ℝ) + 1 / 2)
    (hgridRatio : ∀ i j, 1 ≤ i → i ≤ j → j < blockCount N ρ →
      (blockTime N ρ i : ℝ) + 1 / 2 ≤
        (Graw / ρ) ^ (j - i) * ((blockTime N ρ j : ℝ) + 1 / 2))
    (hgridLogCell : ∀ i, 1 ≤ i → i < blockCount N ρ →
      ((blockCount N ρ : ℝ) - i) * L ≤
        Graw * -Real.log (((blockTime N ρ i : ℝ) + 1 / 2) / N))
    (hgridLogFirst : ∀ i, 1 ≤ i → i < blockCount N ρ →
      Real.log (((blockTime N ρ i : ℝ) + 1 / 2) /
        ((blockTime N ρ (i - 1) : ℝ) + 1 / 2)) ≤ Graw * L)
    (htvN : blockTime N ρ v ≤ N)
    (hupdateMono : MonotoneOn (Function.update (blockTime N ρ) v N) (Set.Iic v))
    (hrenewal : ∀ (m : ℕ) (lo hi : Fin (m + 2) → ℕ),
      (∀ j, lo j < hi j) →
      (∀ j : Fin (m + 1), hi j.castSucc ≤ lo j.succ) →
      hi (Fin.last (m + 1)) ≤ N →
      let Sgrid : Fin (m + 2) → ℝ := fun j => ((lo j : ℝ) + 1 / 2) / N
      let Tgrid : Fin (m + 2) → ℝ := fun j => ((hi j : ℝ) + 1 / 2) / N
      0 < Sgrid 0 → 2 * Sgrid 0 ≤ Tgrid 0 →
      (∀ j : Fin (m + 1), 4 * Sgrid j.succ ≤ Tgrid j.succ) →
      (∀ j : Fin (m + 1), Tgrid j.castSucc ≤ Sgrid j.succ) →
      (∀ j : Fin (m + 1), Tgrid j.castSucc < 1) →
      Tgrid (Fin.last (m + 1)) ≤ 2 →
      ENNReal.ofReal (renewalStringSum ϑ N (m + 1) lo hi) ≤
        ENNReal.ofReal ((Cchain ^ (m + 2) * Real.log (Tgrid 0 / Sgrid 0) *
          (∏ j : Fin (m + 1), Tgrid j.castSucc / Sgrid j.succ)) *
          ∏ j : Fin (m + 1), (-Real.log (Tgrid j.castSucc))⁻¹))
    (hSsubset : S ⊆ Finset.Ioo u v) :
    C₅ ^ (S.card + 2) * renewalStringSum ϑ N (S.card + 1)
      (occupiedLo (Function.update (blockTime N ρ) v N) u v S)
      (occupiedHi (Function.update (blockTime N ρ) v N) u v S) ≤
      (D ^ (d + 3) * G ^ 2 * (G / L) ^ (d - 1)) /
        ((blockCount N ρ : ℝ) - u) := by
  classical
  let t : ℕ → ℕ := Function.update (blockTime N ρ) v N
  let M : ℕ := S.card
  let idx : Fin (M + 2) → ℕ := occupiedIndex u v S
  let lo : Fin (M + 2) → ℕ := occupiedLo t u v S
  let hi : Fin (M + 2) → ℕ := occupiedHi t u v S
  let sh : ℕ → ℝ := fun i => (t i : ℝ) + 1 / 2
  let sgrid : Fin (M + 2) → ℝ := fun j => ((lo j : ℝ) + 1 / 2) / N
  let tgrid : Fin (M + 2) → ℝ := fun j => ((hi j : ℝ) + 1 / 2) / N
  have hidx0 : idx 0 = u := by simp [idx, occupiedIndex_zero]
  have hidxlast : idx (Fin.last (M + 1)) = v := by
    simpa [idx, M] using occupiedIndex_last u v S
  have hidxmono : StrictMono idx := by
    simpa [idx] using occupiedIndex_strictMono huv hSsubset
  have hidxle : ∀ j, idx j ≤ v := by
    intro j
    have hjval : (j : ℕ) ≤ M + 1 := by
      have hjlt := j.isLt
      omega
    have hjle : j ≤ Fin.last (M + 1) :=
      Fin.le_iff_val_le_val.mpr (by simpa using hjval)
    have h := hidxmono.monotone hjle
    simpa only [hidxlast] using h
  have hidxlo : ∀ j, 1 ≤ idx j := by
    intro j
    have h := hidxmono.monotone (Fin.zero_le j)
    rw [hidx0] at h
    exact le_trans (by exact_mod_cast hu) h
  have hidxltK : ∀ j, idx j < blockCount N ρ := by
    intro j
    have hj := hidxle j
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hDenu : 0 < (blockCount N ρ : ℝ) - u := by
    have huK : u < blockCount N ρ := by omega
    exact sub_pos.mpr (by exact_mod_cast huK)
  have htimev : (blockTime N ρ v : ℝ) ≤ N := by exact_mod_cast htvN
  have hgridUpdated (i : ℕ) (hi : 1 ≤ i) (hiK : i < blockCount N ρ)
      (hiv : i ≤ v) :
      4 * ((t (i - 1) : ℝ) + 1 / 2) ≤ (t i : ℝ) + 1 / 2 := by
    by_cases hieq : i = v
    · subst i
      have hlocal := hgridLocal v hi hiK
      have hprev : v - 1 ≠ v := by omega
      change 4 * ((Function.update (blockTime N ρ) v N (v - 1) : ℝ) + 1 / 2) ≤
        (Function.update (blockTime N ρ) v N v : ℝ) + 1 / 2
      rw [Function.update_of_ne hprev, Function.update_self]
      linarith [hlocal, htimev]
    · have hlocal := hgridLocal i hi hiK
      have hprev : i - 1 ≠ v := by omega
      change 4 * ((Function.update (blockTime N ρ) v N (i - 1) : ℝ) + 1 / 2) ≤
        (Function.update (blockTime N ρ) v N i : ℝ) + 1 / 2
      rw [Function.update_of_ne hprev, Function.update_of_ne hieq]
      exact hlocal
  have hlo : ∀ j, lo j < hi j := by
    intro j
    have hg := hgridUpdated (idx j) (hidxlo j) (hidxltK j) (hidxle j)
    have hcast : (t (idx j - 1) : ℝ) < (t (idx j) : ℝ) := by
      have hprev : 0 ≤ (t (idx j - 1) : ℝ) := Nat.cast_nonneg _
      nlinarith [hg, hprev]
    dsimp [lo, hi, occupiedLo, occupiedHi]
    exact_mod_cast hcast
  have hsep : ∀ j : Fin (M + 1), hi j.castSucc ≤ lo j.succ := by
    intro j
    have hidx : idx j.castSucc ≤ idx j.succ - 1 := by
      have hstrict := hidxmono (Fin.castSucc_lt_succ : j.castSucc < j.succ)
      omega
    apply hupdateMono
    · exact Set.mem_Iic.mpr (hidxle j.castSucc)
    · have htop := hidxle j.succ
      exact Set.mem_Iic.mpr (by dsimp [idx] at htop ⊢; omega)
    · exact hidx
  have hlast : hi (Fin.last (M + 1)) ≤ N := by
    change t (idx (Fin.last (M + 1))) ≤ N
    rw [hidxlast]
    simp [t]
  have hspos : ∀ j, 0 < sgrid j := by
    intro j
    dsimp [sgrid, lo, occupiedLo]
    positivity
  have htpos : ∀ j, 0 < tgrid j := by
    intro j
    dsimp [tgrid, hi, occupiedHi]
    positivity
  have hfirst : 2 * sgrid 0 ≤ tgrid 0 := by
    have h := hgridUpdated u hu (by omega) (by omega)
    change 2 * (sh (idx 0 - 1) / N) ≤ sh (idx 0) / N
    rw [hidx0]
    dsimp [sh]
    have hprev : u - 1 ≠ v := by omega
    have hu_ne : u ≠ v := by omega
    simp only [t, Function.update_of_ne hprev, Function.update_of_ne hu_ne] at h
    have htimeprev : 0 ≤ (blockTime N ρ (u - 1) : ℝ) := Nat.cast_nonneg _
    have hhalf : 2 * ((blockTime N ρ (u - 1) : ℝ) + 1 / 2) ≤
        (blockTime N ρ u : ℝ) + 1 / 2 := by nlinarith [h, htimeprev]
    simp only [t, Function.update_of_ne hprev, Function.update_of_ne hu_ne]
    calc
      2 * (((blockTime N ρ (u - 1) : ℝ) + 1 / 2) / N) =
          (2 * ((blockTime N ρ (u - 1) : ℝ) + 1 / 2)) / N := by ring
      _ ≤ ((blockTime N ρ u : ℝ) + 1 / 2) / N :=
        div_le_div_of_nonneg_right hhalf hNpos.le
  have hblock : ∀ j : Fin (M + 1), 4 * sgrid j.succ ≤ tgrid j.succ := by
    intro j
    have h := hgridUpdated (idx j.succ) (hidxlo j.succ) (hidxltK j.succ)
      (hidxle j.succ)
    change 4 * (sh (idx j.succ - 1) / N) ≤ sh (idx j.succ) / N
    dsimp [sh]
    calc
      4 * (((t (idx j.succ - 1) : ℝ) + 1 / 2) / N) =
          (4 * ((t (idx j.succ - 1) : ℝ) + 1 / 2)) / N := by ring
      _ ≤ ((t (idx j.succ) : ℝ) + 1 / 2) / N :=
        div_le_div_of_nonneg_right h hNpos.le
  have hchain : ∀ j : Fin (M + 1), tgrid j.castSucc ≤ sgrid j.succ := by
    intro j
    have hidx : idx j.castSucc ≤ idx j.succ - 1 := by
      have hstrict := hidxmono (Fin.castSucc_lt_succ : j.castSucc < j.succ)
      omega
    have htop := hidxle j.succ
    have hmono := hupdateMono
      (Set.mem_Iic.mpr (hidxle j.castSucc))
      (Set.mem_Iic.mpr (by dsimp [idx] at htop ⊢; omega)) hidx
    change sh (idx j.castSucc) / N ≤ sh (idx j.succ - 1) / N
    have hshift : sh (idx j.castSucc) ≤ sh (idx j.succ - 1) := by
      dsimp [sh]
      have hmonoReal : (t (idx j.castSucc) : ℝ) ≤ t (idx j.succ - 1) := by
        exact_mod_cast hmono
      linarith
    exact div_le_div_of_nonneg_right hshift hNpos.le
  have hTlt : ∀ j : Fin (M + 1), tgrid j.castSucc < 1 := by
    intro j
    have hjlt : j.castSucc < Fin.last (M + 1) := by
      apply Fin.lt_def.mpr
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
    have hidxlt : idx j.castSucc < v := by
      simpa only [hidxlast] using hidxmono hjlt
    have hlogCell := hgridLogCell (idx j.castSucc) (hidxlo j.castSucc)
      (hidxltK j.castSucc)
    have hleft : 0 < ((blockCount N ρ : ℝ) - idx j.castSucc) * L :=
      mul_pos (sub_pos.mpr (by exact_mod_cast hidxltK j.castSucc)) hLpos
    have hneq : idx j.castSucc ≠ v := ne_of_lt hidxlt
    have hgridEq : tgrid j.castSucc =
        ((blockTime N ρ (idx j.castSucc) : ℝ) + 1 / 2) / N := by
      simp only [tgrid, hi, occupiedHi, idx, t, Function.update_of_ne hneq]
    have hraw : ((blockCount N ρ : ℝ) - idx j.castSucc) * L ≤
        Graw * (-Real.log (tgrid j.castSucc)) := by
      rw [hgridEq]
      exact hlogCell
    have hlogneg : Real.log (tgrid j.castSucc) < 0 := by
      have hneglog : 0 < -Real.log (tgrid j.castSucc) := by
        by_contra hnot
        have hnonpos : -Real.log (tgrid j.castSucc) ≤ 0 := le_of_not_gt hnot
        have hprod : Graw * (-Real.log (tgrid j.castSucc)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hGrawpos.le hnonpos
        linarith only [hleft, hraw, hprod]
      exact neg_pos.mp hneglog
    exact (Real.log_neg_iff (htpos _)).1 hlogneg
  have hTlast : tgrid (Fin.last (M + 1)) ≤ 2 := by
    rw [show tgrid (Fin.last (M + 1)) = ((N : ℝ) + 1 / 2) / N by
      simp [tgrid, hi, occupiedHi, idx, t, hidxlast]]
    rw [div_le_iff₀ hNpos]
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hlogfirst : Real.log (tgrid 0 / sgrid 0) ≤ G * L := by
    have h := hgridLogFirst u hu (by omega)
    have hratio : tgrid 0 / sgrid 0 =
        ((blockTime N ρ u : ℝ) + 1 / 2) /
          ((blockTime N ρ (u - 1) : ℝ) + 1 / 2) := by
      have hu_ne : u ≠ v := by omega
      have huprev_ne : u - 1 ≠ v := by omega
      simp only [tgrid, sgrid, hi, lo, occupiedHi, occupiedLo,
        occupiedIndex_zero, t]
      rw [Function.update_of_ne hu_ne, Function.update_of_ne huprev_ne]
      field_simp [ne_of_gt hNpos]
    have hraw : Real.log (tgrid 0 / sgrid 0) ≤ Graw * L := by
      rw [hratio]
      simpa [hLdef] using h
    exact hraw.trans (mul_le_mul_of_nonneg_right hGrawleG hLpos.le)
  have hlogcell : ∀ j : Fin (M + 1),
      ((blockCount N ρ : ℝ) - idx j.castSucc) * L ≤
        G * (-Real.log (tgrid j.castSucc)) := by
    intro j
    have h := hgridLogCell (idx j.castSucc) (hidxlo j.castSucc)
      (hidxltK j.castSucc)
    have hjval : (j.castSucc : ℕ) < M + 1 := by
      simp only [Fin.val_castSucc]
      omega
    have hjlt : j.castSucc < Fin.last (M + 1) :=
      Fin.lt_def.mpr (by simpa using hjval)
    have hidxlt : idx j.castSucc < v := by
      simpa only [hidxlast] using hidxmono hjlt
    have hneq : idx j.castSucc ≠ v := ne_of_lt hidxlt
    have hgridEq : tgrid j.castSucc =
        ((blockTime N ρ (idx j.castSucc) : ℝ) + 1 / 2) / N := by
      simp only [tgrid, hi, occupiedHi, idx, t, Function.update_of_ne hneq]
    have hraw : ((blockCount N ρ : ℝ) - idx j.castSucc) * L ≤
        Graw * (-Real.log (tgrid j.castSucc)) := by
      rw [hgridEq]
      exact h
    exact hraw.trans (mul_le_mul_of_nonneg_right hGrawleG
      (by have h := Real.log_neg (htpos _) (hTlt j); linarith))
  have hstep : ∀ j : Fin (M + 1),
      tgrid j.castSucc / sgrid j.succ ≤
        (G / ρ) ^ (idx j.succ - idx j.castSucc - 1) := by
    intro j
    let a := idx j.castSucc
    let b := idx j.succ - 1
    have ha : 1 ≤ a := by dsimp [a]; exact hidxlo j.castSucc
    have hstrict := hidxmono (Fin.castSucc_lt_succ : j.castSucc < j.succ)
    have hab : a ≤ b := by dsimp [a, b]; omega
    have hbK : b < blockCount N ρ := by
      dsimp [b]
      have := hidxltK j.succ
      omega
    have hgridratio := hgridRatio a b ha hab hbK
    have hbase : Graw / ρ ≤ G / ρ :=
      div_le_div_of_nonneg_right hGrawleG (by linarith : 0 ≤ ρ)
    have hshpos : 0 < sh b := by dsimp [sh, t]; positivity
    have hjlt : j.castSucc < Fin.last (M + 1) := by
      apply Fin.lt_def.mpr
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
    have hlt := hidxmono hjlt
    have hltv : a < v := by simpa [a, hidxlast] using hlt
    have ha_ne : a ≠ v := ne_of_lt hltv
    have hb_ne : b ≠ v := by
      dsimp [b]
      have htop := hidxle j.succ
      omega
    have hgridratio' : sh a ≤ (Graw / ρ) ^ (b - a) * sh b := by
      dsimp [sh, t]
      rw [Function.update_of_ne ha_ne, Function.update_of_ne hb_ne]
      exact hgridratio
    have hratioRaw : sh a / sh b ≤ (Graw / ρ) ^ (b - a) :=
      (div_le_iff₀ hshpos).2 hgridratio'
    have hratio : sh a / sh b ≤ (G / ρ) ^ (b - a) :=
      hratioRaw.trans (pow_le_pow_left₀
        (div_nonneg hGrawpos.le (by linarith : 0 ≤ ρ)) hbase _)
    have heq : tgrid j.castSucc / sgrid j.succ = sh a / sh b := by
      have hT : tgrid j.castSucc = ((t a : ℝ) + 1 / 2) / N := by
        simp [tgrid, hi, occupiedHi, idx, a]
      have hS : sgrid j.succ = ((t b : ℝ) + 1 / 2) / N := by
        simp [sgrid, lo, occupiedLo, idx, b]
      rw [hT, hS]
      dsimp [sh]
      field_simp [ne_of_gt hNpos]
    have hexp : b - a = idx j.succ - idx j.castSucc - 1 := by
      dsimp [a, b]
      omega
    rw [heq, ← hexp]
    exact hratio
  have hsumDelta : ∑ j : Fin (M + 1), (idx j.succ - idx j.castSucc) = v - u := by
    simpa [idx, M] using occupiedIndex_step_sum huv hSsubset
  have hSleT : sgrid 0 ≤ tgrid 0 := by nlinarith [hfirst, hspos 0]
  have hfactor := openBackwardFactor_le_occupiedRate idx sgrid tgrid
    (by linarith [hG]) hLone hLleρ huv hvK hidx0 hidxlast hidxle hidxmono
    hspos htpos hTlt hSleT hlogfirst hlogcell hstep hsumDelta
  have hsposRaw : ∀ j, 0 < ((lo j : ℝ) + 1 / 2) / N := by
    simpa only [sgrid] using hspos
  have hfirstRaw : 2 * (((lo 0 : ℝ) + 1 / 2) / N) ≤
      ((hi 0 : ℝ) + 1 / 2) / N := by simpa only [sgrid, tgrid] using hfirst
  have hblockRaw : ∀ j : Fin (M + 1),
      4 * (((lo j.succ : ℝ) + 1 / 2) / N) ≤ ((hi j.succ : ℝ) + 1 / 2) / N := by
    simpa only [sgrid, tgrid] using hblock
  have hchainRaw : ∀ j : Fin (M + 1),
      ((hi j.castSucc : ℝ) + 1 / 2) / N ≤ ((lo j.succ : ℝ) + 1 / 2) / N := by
    simpa only [sgrid, tgrid] using hchain
  have hTraw : ∀ j : Fin (M + 1), ((hi j.castSucc : ℝ) + 1 / 2) / N < 1 := by
    simpa only [tgrid] using hTlt
  have hTlastRaw : ((hi (Fin.last (M + 1)) : ℝ) + 1 / 2) / N ≤ 2 := by
    simpa only [tgrid] using hTlast
  have hchainBound := hrenewal M lo hi hlo hsep hlast (hsposRaw 0)
    hfirstRaw hblockRaw hchainRaw hTraw hTlastRaw
  have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hfactorPos : 0 < G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1) := by
    exact mul_pos (div_pos (sq_pos_of_pos hGpos) hDenu)
      (pow_pos (div_pos hGpos hLpos) _)
  have hrenewalTargetPos : 0 < Cchain ^ (M + 2) *
      (G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1)) :=
    mul_pos (pow_pos hCchain _) hfactorPos
  have hrealRenewal : renewalStringSum ϑ N (M + 1) lo hi ≤
      Cchain ^ (M + 2) *
        (G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1)) := by
    apply (ENNReal.ofReal_le_ofReal_iff hrenewalTargetPos.le).mp
    calc
      ENNReal.ofReal (renewalStringSum ϑ N (M + 1) lo hi) ≤
          ENNReal.ofReal (Cchain ^ (M + 2) *
            (Real.log (tgrid 0 / sgrid 0) *
              (∏ j : Fin (M + 1), tgrid j.castSucc / sgrid j.succ) *
              ∏ j : Fin (M + 1), (-Real.log (tgrid j.castSucc))⁻¹)) := by
        simpa only [sgrid, tgrid, M, mul_assoc] using hchainBound
      _ ≤ ENNReal.ofReal (Cchain ^ (M + 2) *
          (G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1))) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow : 0 ≤ Cchain ^ (M + 2) := pow_nonneg hCchain.le _
        have hfactor' :
            Real.log (tgrid 0 / sgrid 0) *
              (∏ j : Fin (M + 1), tgrid j.castSucc / sgrid j.succ) *
              ∏ j : Fin (M + 1), (-Real.log (tgrid j.castSucc))⁻¹ ≤
            G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1) := by
          simpa [hLdef, hd] using hfactor
        exact mul_le_mul_of_nonneg_left hfactor' hpow
  have hprodPow : C₅ ^ (S.card + 2) * Cchain ^ (M + 2) ≤ D ^ (d + 3) := by
    have heq : C₅ ^ (S.card + 2) * Cchain ^ (M + 2) =
        (C₅ * Cchain) ^ (S.card + 2) := by simp [M, ← mul_pow]
    rw [heq]
    have hcard : S.card + 2 ≤ d + 3 := by
      have hsub : S.card ≤ v - u + 1 := by
        calc
          S.card ≤ (Finset.Icc u v).card := Finset.card_le_card (by
            intro x hx
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioo.mp (hSsubset hx)).1.le,
              (Finset.mem_Ioo.mp (hSsubset hx)).2.le⟩)
          _ = v - u + 1 := by simp; omega
      rw [hd]
      omega
    calc
      (C₅ * Cchain) ^ (S.card + 2) ≤ D ^ (S.card + 2) :=
        pow_le_pow_left₀ (by positivity) hDprod _
      _ ≤ D ^ (d + 3) := pow_le_pow_right₀ hDone hcard
  have hfactorNonneg : 0 ≤ G ^ 2 / ((blockCount N ρ : ℝ) - u) *
      (G / L) ^ (d - 1) := hfactorPos.le
  calc
    _ ≤ C₅ ^ (S.card + 2) *
        (Cchain ^ (M + 2) *
          (G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1))) :=
      mul_le_mul_of_nonneg_left hrealRenewal (pow_nonneg hC₅.le _)
    _ ≤ D ^ (d + 3) *
        (G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1)) := by
      calc
        _ = (C₅ ^ (S.card + 2) * Cchain ^ (M + 2)) *
            (G ^ 2 / ((blockCount N ρ : ℝ) - u) * (G / L) ^ (d - 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hprodPow hfactorNonneg
    _ = (D ^ (d + 3) * G ^ 2 * (G / L) ^ (d - 1)) /
        ((blockCount N ρ : ℝ) - u) := by
      field_simp [ne_of_gt hDenu]

private theorem open_powerset_rate_algebra (d : ℕ) (hd : 1 ≤ d) (D G L : ℝ) :
    2 ^ (d + 1) * (D ^ (d + 3) * G ^ 2 * (G / L) ^ (d - 1)) =
      (2 * D ^ 2 * G) ^ 2 * (2 * D * G) ^ (d - 1) / L ^ (d - 1) := by
  have hpow : (2 * D * G) ^ (d - 1) = 2 ^ (d - 1) * D ^ (d - 1) * G ^ (d - 1) := by
    rw [mul_pow, mul_pow]
  let e := d - 1
  have hd1 : d + 1 = e + 2 := by dsimp [e]; omega
  have hd3 : d + 3 = e + 4 := by dsimp [e]; omega
  rw [hd1, hd3, div_pow, hpow, pow_add, pow_add]
  ring

/-- The open discrepancy has a geometric second-moment bound with one inverse endpoint-distance factor.
Integrability follows from `memLp_closedDiscrepancy` and
`openDiscrepancyMass_eq_closedDiscrepancy_update`. -/
theorem openDiscrepancyMass_sq_integral_le (A : ℝ) :
    ∃ C C₀ : ℝ, 0 < C₀ ∧ ∀ ρ : ℝ, Real.exp (C₀ ^ 2) < ρ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ u v : ℕ, 1 ≤ u → u < v → v + 1 ≤ blockCount N ρ →
        ∫ ω, openDiscrepancyMass (criticalBeta ϑ N) (blockTime N ρ) N u v ω ^ 2 ∂disorderLaw ≤
          (C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u - 1)) ^ 2 /
            ((blockCount N ρ : ℝ) - u) := by
  obtain ⟨C₅, hC₅, hstring⟩ := closedStringSum_le_renewalStringSum A
  obtain ⟨Graw, ρ₀, hGraw, hρ₀, hgridRaw⟩ := halfShiftedGrid_bounds
  let G : ℝ := max 1 Graw
  have hG : 1 ≤ G := by dsimp [G]; exact le_max_left _ _
  have hGrawleG : Graw ≤ G := by dsimp [G]; exact le_max_right _ _
  have hGrawpos : 0 < Graw := hGraw
  obtain ⟨Cchain, hCchain, hrenewal⟩ := renewalStringSum_backwardChain_open_le A
  let D : ℝ := max 2 (max (C₅ * Cchain) G)
  let C : ℝ := 2 * D ^ 2 * G
  let C₀ : ℝ := 2 * D * G + Real.sqrt (Real.log ρ₀) + 1
  have hDtwo : 2 ≤ D := by dsimp [D]; exact le_max_left _ _
  have hDprod : C₅ * Cchain ≤ D := by
    dsimp [D]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hDpos : 0 < D := by linarith
  have hDone : 1 ≤ D := by linarith
  have hC₀pos : 0 < C₀ := by
    dsimp [C₀]
    have hlog₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
    positivity
  have hC₀base : 2 * D * G ≤ C₀ := by
    dsimp [C₀]
    have hsqrt : 0 ≤ Real.sqrt (Real.log ρ₀) := Real.sqrt_nonneg _
    linarith
  have hρ₀exp : ρ₀ ≤ Real.exp (C₀ ^ 2) := by
    have hlog₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
    have hsqrtSq : (Real.sqrt (Real.log ρ₀)) ^ 2 = Real.log ρ₀ :=
      Real.sq_sqrt hlog₀.le
    have hsqrtle : Real.sqrt (Real.log ρ₀) ≤ C₀ := by
      dsimp [C₀]
      nlinarith [Real.sqrt_nonneg (Real.log ρ₀), hDpos]
    have hsqle : Real.log ρ₀ ≤ C₀ ^ 2 := by nlinarith [Real.sqrt_nonneg (Real.log ρ₀)]
    calc
      ρ₀ = Real.exp (Real.log ρ₀) := (Real.exp_log (by linarith : 0 < ρ₀)).symm
      _ ≤ Real.exp (C₀ ^ 2) := Real.exp_le_exp.mpr hsqle
  refine ⟨C, C₀, hC₀pos, ?_⟩
  intro ρ hρ
  have hlogρ : C₀ ^ 2 < Real.log ρ := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hρ
  have hρlarge : ρ₀ ≤ ρ := (lt_of_le_of_lt hρ₀exp hρ).le
  have hρone : 1 < ρ := by
    have hC₀sq : 0 < C₀ ^ 2 := sq_pos_of_pos hC₀pos
    have hexp : 1 < Real.exp (C₀ ^ 2) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hC₀sq
    exact lt_trans hexp hρ
  have hLpos : 0 < Real.log ρ := Real.log_pos hρone
  have hLone : 1 ≤ Real.log ρ := by
    have hDGe : 1 ≤ 2 * D * G := by nlinarith [hDtwo, hG]
    have hC₀ge : 1 ≤ C₀ := by
      dsimp [C₀]
      nlinarith [Real.sqrt_nonneg (Real.log ρ₀), hDpos]
    have hsq : 1 ≤ C₀ ^ 2 := by nlinarith
    linarith
  have hLleρ : Real.log ρ ≤ ρ := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ρ by linarith)
    linarith
  filter_upwards [hstring, hgridRaw ρ hρlarge, blockTime_monotone hρone] with
    N hstringN hgridN htimeMono
  intro ϑ hϑ u v hu huv hvK
  have hK : 1 ≤ blockCount N ρ := by omega
  have hKne : blockCount N ρ ≠ 0 := by omega
  have hN : 1 ≤ N := by
    by_contra hn
    have hNzero : N = 0 := by omega
    subst N
    have hsepU := hgridN.1 u hu (by omega : u < blockCount 0 ρ)
    have htimeU : blockTime 0 ρ u = 0 := by simp [blockTime]
    have htimePrev : blockTime 0 ρ (u - 1) = 0 := by simp [blockTime]
    rw [htimeU, htimePrev] at hsepU
    norm_num at hsepU
  have hKtime : blockTime N ρ (blockCount N ρ) = N := by
    simp [blockTime, hKne]
  have htvN : blockTime N ρ v ≤ N := by
    have hle := htimeMono (show v ≤ blockCount N ρ by omega)
    simpa [hKtime] using hle
  let t : ℕ → ℕ := Function.update (blockTime N ρ) v N
  have hupdateMono : MonotoneOn t (Set.Iic v) := by
    intro i hi j hj hij
    by_cases hjv : j = v
    · subst j
      by_cases hiv : i = v
      · subst i
        simp [t]
      · have hiK : i ≤ blockCount N ρ := by omega
        have hle := htimeMono hiK
        simpa [t, Function.update_of_ne hiv, hKtime] using hle
    · have hiv : i ≠ v := by
        intro hiV
        apply hjv
        exact Nat.le_antisymm hj (hiV ▸ hij)
      simpa [t, Function.update_of_ne hiv, Function.update_of_ne hjv] using
        htimeMono hij
  have hmonoOn : MonotoneOn t (Set.Iic v) := hupdateMono
  have hsum := hstringN ϑ hϑ t u v hmonoOn (by simp [t]) hu huv
  have hupdateId (ω : Disorder) :
      openDiscrepancyMass (criticalBeta ϑ N) (blockTime N ρ) N u v ω =
        closedDiscrepancy (criticalBeta ϑ N) t u v ω := by
    exact openDiscrepancyMass_eq_closedDiscrepancy_update
      (criticalBeta ϑ N) (blockTime N ρ) N hu huv.le ω
  have hsqEq : ∫ ω, openDiscrepancyMass (criticalBeta ϑ N)
      (blockTime N ρ) N u v ω ^ 2 ∂disorderLaw =
      closedStringSum (Polymer.sigmaSq (criticalBeta ϑ N)) t u v := by
    calc
      _ = ∫ ω, closedDiscrepancy (criticalBeta ϑ N) t u v ω ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [hupdateId]
      _ = _ := closedDiscrepancy_sq_integral_eq (criticalBeta ϑ N)
        (t := t) (u := u) (v := v) hmonoOn hu huv
  rw [hsqEq]
  have hsumN := hsum
  have hKreal : (v : ℝ) + 1 ≤ (blockCount N ρ : ℝ) := by exact_mod_cast hvK
  let L : ℝ := Real.log ρ
  let d : ℕ := v - u
  let K : ℝ := blockCount N ρ
  have hDenu : 0 < K - u := by
    have huKnat : u < blockCount N ρ := by omega
    have huKreal : (u : ℝ) < K := by
      change (u : ℝ) < (blockCount N ρ : ℝ)
      exact_mod_cast huKnat
    exact sub_pos.mpr huKreal
  have hterm : ∀ S ∈ (Finset.Ioo u v).powerset,
      C₅ ^ (S.card + 2) * renewalStringSum ϑ N (S.card + 1)
        (occupiedLo t u v S) (occupiedHi t u v S) ≤
        (D ^ (d + 3) * G ^ 2 * (G / L) ^ (d - 1)) / (K - u) := by
    intro S hSmem
    exact openOccupiedRenewalTerm_le_of_backwardChain
      N ρ ϑ u v S C₅ Cchain Graw G D L d hC₅ hCchain hDprod
      hGrawpos hGrawleG hG hDone hρone rfl hLpos hLone hLleρ hN hu huv hvK rfl
      hgridN.1 hgridN.2.1 hgridN.2.2.1 hgridN.2.2.2 htvN
      hupdateMono (hrenewal N hN ϑ hϑ) (Finset.mem_powerset.mp hSmem)
  have htermUniform := Finset.sum_le_sum hterm
  have hcardPower : ((Finset.Ioo u v).powerset.card : ℝ) ≤ 2 ^ (d + 1 : ℕ) := by
    have h := occupied_powerset_card_le huv
    simpa [d] using h
  have hsumCoarse :
      ∑ S ∈ (Finset.Ioo u v).powerset,
        C₅ ^ (S.card + 2) * renewalStringSum ϑ N (S.card + 1)
          (occupiedLo t u v S) (occupiedHi t u v S) ≤
        (4 * D ^ 4 * G ^ 2 * (2 * D * G) ^ (d - 1)) /
          ((K - u) * L ^ (d - 1)) := by
    calc
      _ ≤ ∑ S ∈ (Finset.Ioo u v).powerset,
          (D ^ (d + 3) * G ^ 2 * (G / L) ^ (d - 1)) / (K - u) := htermUniform
      _ = ((Finset.Ioo u v).powerset.card : ℝ) *
          ((D ^ (d + 3) * G ^ 2 * (G / L) ^ (d - 1)) / (K - u)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ (d + 1) *
          ((D ^ (d + 3) * G ^ 2 * (G / L) ^ (d - 1)) / (K - u)) :=
        mul_le_mul_of_nonneg_right hcardPower (by positivity)
      _ = _ := by
        rw [← mul_div_assoc,
          open_powerset_rate_algebra d (by dsimp [d]; omega) D G L]
        field_simp [ne_of_gt hDenu, ne_of_gt hLpos]
        ring
  have hsumResult := hsumN.trans hsumCoarse
  have he : 1 ≤ d := by dsimp [d]; omega
  have hepos : 0 ≤ d - 1 := by omega
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hrootPow : (Real.sqrt L) ^ (2 * (d - 1)) = L ^ (d - 1) := by
    rw [pow_mul, Real.sq_sqrt hLpos.le]
  have hC₀geOne : 1 ≤ C₀ := by
    dsimp [C₀]
    have hsqrt : 0 ≤ Real.sqrt (Real.log ρ₀) := Real.sqrt_nonneg _
    have hD : 2 ≤ D := hDtwo
    have hG' : 1 ≤ G := hG
    nlinarith
  have hbaseSq : 2 * D * G ≤ C₀ ^ 2 := by
    have hbase : 2 * D * G ≤ C₀ := hC₀base
    calc
      2 * D * G ≤ C₀ := hbase
      _ ≤ C₀ * C₀ := by
        calc
          C₀ = 1 * C₀ := by ring
          _ ≤ C₀ * C₀ := mul_le_mul_of_nonneg_right hC₀geOne hC₀pos.le
      _ = C₀ ^ 2 := by ring
  have hbasepow : (2 * D * G) ^ (d - 1) ≤ C₀ ^ (2 * (d - 1)) := by
    calc
      _ ≤ (C₀ ^ 2) ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) hbaseSq _
      _ = _ := by rw [← pow_mul]
  have hconst : 4 * D ^ 4 * G ^ 2 ≤ C ^ 2 := by
    calc
      4 * D ^ 4 * G ^ 2 = C ^ 2 := by dsimp [C]; ring
      _ ≤ C ^ 2 := le_rfl
  have htargetNumerator :
      4 * D ^ 4 * G ^ 2 * (2 * D * G) ^ (d - 1) ≤
        C ^ 2 * C₀ ^ (2 * (d - 1)) := by
    calc
      _ ≤ C ^ 2 * (2 * D * G) ^ (d - 1) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbasepow (by positivity)
  have htargetEq : (C * (C₀ / Real.sqrt L) ^ (d - 1)) ^ 2 =
      C ^ 2 * C₀ ^ (2 * (d - 1)) / L ^ (d - 1) := by
    have hnum : (C₀ ^ (d - 1)) ^ 2 = C₀ ^ (2 * (d - 1)) := by
      rw [← pow_mul, Nat.mul_comm]
    have hden : ((Real.sqrt L) ^ (d - 1)) ^ 2 = L ^ (d - 1) := by
      rw [← pow_mul, Nat.mul_comm, hrootPow]
    rw [mul_pow, div_pow, div_pow, hnum, hden]
    ring
  have hfinal :
      (4 * D ^ 4 * G ^ 2 * (2 * D * G) ^ (d - 1)) /
          ((K - u) * L ^ (d - 1)) ≤
        (C * (C₀ / Real.sqrt L) ^ (d - 1)) ^ 2 / (K - u) := by
    rw [htargetEq]
    have hdiv : (C ^ 2 * C₀ ^ (2 * (d - 1)) / L ^ (d - 1)) / (K - u) =
        (C ^ 2 * C₀ ^ (2 * (d - 1))) / ((K - u) * L ^ (d - 1)) := by
      calc
        _ = _ / (L ^ (d - 1) * (K - u)) := by rw [div_div]
        _ = _ := by congr 1; ring
    rw [hdiv]
    have hDenL : 0 < (K - u) * L ^ (d - 1) := mul_pos hDenu (pow_pos hLpos _)
    apply (div_le_div_iff₀ hDenL hDenL).2
    exact mul_le_mul_of_nonneg_right htargetNumerator hDenL.le
  exact hsumResult.trans hfinal
