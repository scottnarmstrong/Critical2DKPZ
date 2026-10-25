/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioExpansion
import Mathlib.Tactic

/-! # Combinatorial component bounds -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem pairBond_index_bounds {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s) {i : ℕ}
    (hi : PairBond F G i) : r ≤ i ∧ i < s := by
  rcases hi with ⟨I, hI, hleft, hright⟩
  rcases Finset.mem_union.mp hI with hIF | hIG
  · have hb := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hIF
    exact ⟨by omega, by omega⟩
  · have hb := (intervalFamilies_mem_iff r s G).mp hG |>.1 I hIG
    exact ⟨by omega, by omega⟩

/-- Every interval in either family is contained in a maximal bonded component. -/
theorem interval_exists_pairComponent {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    (hr : 1 ≤ r) (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) {I : ℕ × ℕ} (hI : I ∈ F ∪ G) :
    ∃ c ∈ pairComponents r s F G, c.1 ≤ I.1 ∧ I.2 ≤ c.2 := by
  classical
  have hbounds := (Finset.mem_union.mp hI).elim
    (fun h => (intervalFamilies_mem_iff r s F).mp hF |>.1 I h)
    (fun h => (intervalFamilies_mem_iff r s G).mp hG |>.1 I h)
  have huv : I.1 < I.2 := hbounds.2.2.2.2
  let Starts : Finset ℕ := (Finset.Icc r I.1).filter fun a =>
    ∀ i ∈ Finset.Ico a I.2, PairBond F G i
  have hStarts : Starts.Nonempty := by
    refine ⟨I.1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbounds.1, le_rfl⟩, ?_⟩⟩
    intro i hi
    exact ⟨I, hI, (Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2⟩
  let a := Starts.min' hStarts
  have ha_mem : a ∈ Starts := Finset.min'_mem Starts hStarts
  have ha_bounds := Finset.mem_Icc.mp (Finset.mem_filter.mp ha_mem).1
  have ha_bonds := (Finset.mem_filter.mp ha_mem).2
  let Ends : Finset ℕ := (Finset.Icc I.2 s).filter fun b =>
    ∀ i ∈ Finset.Ico a b, PairBond F G i
  have hEnds : Ends.Nonempty := by
    refine ⟨I.2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hbounds.2.2.2.1⟩, ?_⟩⟩
    exact ha_bonds
  let b := Ends.max' hEnds
  have hb_mem : b ∈ Ends := Finset.max'_mem Ends hEnds
  have hb_bounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hb_mem).1
  have hb_bonds := (Finset.mem_filter.mp hb_mem).2
  have hleftBoundary : ¬ PairBond F G (a - 1) := by
    intro hleft
    by_cases har : a = r
    · have hi := pairBond_index_bounds hF hG hleft
      rw [har] at hi
      omega
    · have hAr : r ≤ a - 1 := by omega
      have hAu : a - 1 ≤ I.1 := by omega
      have hnew : a - 1 ∈ Starts := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hAr, hAu⟩, ?_⟩
        intro i hi
        rcases Finset.mem_Ico.mp hi with ⟨hai, hiv⟩
        by_cases hia : i = a - 1
        · simpa [hia] using hleft
        · have hia' : a ≤ i := by omega
          exact ha_bonds i (Finset.mem_Ico.mpr ⟨hia', hiv⟩)
      have hmin := Finset.min'_le Starts (a - 1) hnew
      dsimp [a] at hmin
      omega
  have hrightBoundary : ¬ PairBond F G b := by
    intro hright
    by_cases hbs : b = s
    · have hi := pairBond_index_bounds hF hG hright
      rw [hbs] at hi
      omega
    · have hbs' : b + 1 ≤ s := by omega
      have hnew : b + 1 ∈ Ends := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨by omega, hbs'⟩, ?_⟩
        intro i hi
        rcases Finset.mem_Ico.mp hi with ⟨hai, hib⟩
        by_cases hib' : i = b
        · simpa [hib'] using hright
        · exact hb_bonds i (Finset.mem_Ico.mpr ⟨hai, by omega⟩)
      have hmax := Finset.le_max' Ends (b + 1) hnew
      dsimp [b] at hmax
      omega
  refine ⟨(a, b), ?_, ?_, ?_⟩
  · simp only [pairComponents, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨ha_bounds.1, le_trans ha_bounds.2 hbounds.2.1⟩,
        ⟨le_trans hbounds.2.2.1 hb_bounds.1, hb_bounds.2⟩⟩,
      ⟨lt_of_le_of_lt ha_bounds.2 (lt_of_lt_of_le huv hb_bounds.1), hb_bonds,
        hleftBoundary, hrightBoundary⟩⟩
  · exact ha_bounds.2
  · exact hb_bounds.1

/-- Restrict one interval family to the intervals carried by a component span. -/
def restrictIntervalFamily (F : Finset (ℕ × ℕ)) (c : ℕ × ℕ) :
    Finset (ℕ × ℕ) := F.filter fun I => c.1 ≤ I.1 ∧ I.2 ≤ c.2

/-- Restricting a family to a component preserves its interval-family property. -/
theorem restrictIntervalFamily_mem {r s : ℕ} {F : Finset (ℕ × ℕ)}
    (hF : F ∈ intervalFamilies r s) {c : ℕ × ℕ} :
    restrictIntervalFamily F c ∈ intervalFamilies c.1 c.2 := by
  classical
  rw [intervalFamilies_mem_iff]
  constructor
  · intro I hI
    have hIf := Finset.mem_filter.mp hI
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hIf.1
    rcases hIf.2 with ⟨hc1, hc2⟩
    exact ⟨hc1, le_trans (Nat.le_of_lt hbounds.2.2.2.2) hc2,
      le_trans hc1 (Nat.le_of_lt hbounds.2.2.2.2), hc2, hbounds.2.2.2.2⟩
  · intro I hI J hJ hne
    have hIf := Finset.mem_filter.mp hI
    have hJf := Finset.mem_filter.mp hJ
    exact ((intervalFamilies_mem_iff r s F).mp hF).2 I hIf.1 J hJf.1 hne

private theorem restrict_isolated_iff (F G : Finset (ℕ × ℕ)) (c : ℕ × ℕ) :
    IsIsolatedComponent F G c ↔
      (restrictIntervalFamily F c).card + (restrictIntervalFamily G c).card = 1 := Iff.rfl

/-- The left family is the disjoint union of its restrictions to all pair components. -/
theorem intervalFamily_reconstruct (r s : ℕ) (hr : 1 ≤ r) (F G : Finset (ℕ × ℕ))
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s) :
    F = (pairComponents r s F G).biUnion (restrictIntervalFamily F) := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨c, hc, hc1, hc2⟩ :=
      interval_exists_pairComponent hr hF hG (Finset.mem_union.mpr (Or.inl hI))
    exact Finset.mem_biUnion.mpr ⟨c, hc,
      Finset.mem_filter.mpr ⟨hI, ⟨hc1, hc2⟩⟩⟩
  · intro hI
    rcases Finset.mem_biUnion.mp hI with ⟨c, hc, hIc⟩
    exact (Finset.mem_filter.mp hIc).1

/-- The right family is the disjoint union of its restrictions to all pair components. -/
theorem intervalFamily_reconstruct_right (r s : ℕ) (hr : 1 ≤ r) (F G : Finset (ℕ × ℕ))
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s) :
    G = (pairComponents r s F G).biUnion (restrictIntervalFamily G) := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨c, hc, hc1, hc2⟩ :=
      interval_exists_pairComponent hr hF hG (Finset.mem_union.mpr (Or.inr hI))
    exact Finset.mem_biUnion.mpr ⟨c, hc,
      Finset.mem_filter.mpr ⟨hI, ⟨hc1, hc2⟩⟩⟩
  · intro hI
    rcases Finset.mem_biUnion.mp hI with ⟨c, hc, hIc⟩
    exact (Finset.mem_filter.mp hIc).1

private theorem sum_range_pow_four_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (4 : ℕ) ^ k ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      (∑ k ∈ Finset.range n, (4 : ℕ) ^ k) + 4 ^ n ≤ 4 ^ n + 4 ^ n :=
        Nat.add_le_add_right ih _
      _ ≤ 4 ^ (n + 1) := by rw [pow_succ]; omega

private theorem sum_interval_pow_four_le (r s : ℕ) (hrs : r ≤ s) :
    ∑ u ∈ Finset.Icc r s, (4 : ℕ) ^ (u - r) ≤ 4 ^ (s - r + 1) := by
  have hreindex :
      ∑ u ∈ Finset.Icc r s, (4 : ℕ) ^ (u - r) =
        ∑ k ∈ Finset.range (s - r + 1), (4 : ℕ) ^ k := by
    symm
    apply Finset.sum_bij (fun k _ => r + k)
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      exact Finset.mem_Icc.mpr ⟨Nat.le_add_right r k, by omega⟩
    · intro k hk l hl hEq
      exact Nat.add_left_cancel hEq
    · intro u hu
      refine ⟨u - r, Finset.mem_range.mpr ?_, ?_⟩
      · have hu' := Finset.mem_Icc.mp hu
        exact Nat.lt_succ_of_le (Nat.sub_le_sub_right hu'.2 r)
      · exact Nat.add_sub_of_le (Finset.mem_Icc.mp hu).1
    · intro k hk
      simp
  rw [hreindex]
  exact sum_range_pow_four_le (s - r + 1)

private theorem intervalFamilies_card_le_four_pow {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    (intervalFamilies r s).card ≤ 4 ^ (s - r + 1) := by
  revert r
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro r hr hrs
    by_cases hrsEq : r = s
    · subst r
      simp [intervalFamilies_self]
    · have hrs' : r ≤ s - 1 := by omega
      let hasLast : Finset (ℕ × ℕ) → Prop := fun F => ∃ I ∈ F, I.2 = s
      let L := (intervalFamilies r s).filter hasLast
      let T := (Finset.Icc r (s - 1)).sigma (fun u => intervalFamilies r (u - 1))
      have hprefix :
          (intervalFamilies r s).filter (fun F => ¬ hasLast F) =
            intervalFamilies r (s - 1) := by
        ext F
        simp only [Finset.mem_filter]
        exact (intervalFamilies_prefix_iff r s F).symm
      have hlast : T.card = L.card := by
        apply Finset.card_bij (fun p _ => insert (p.1, s) p.2)
        · intro p hp
          rcases Finset.mem_sigma.mp hp with ⟨hu, hG⟩
          have hu' := Finset.mem_Icc.mp hu
          have hvalid : insert (p.1, s) p.2 ∈ intervalFamilies r s :=
            intervalFamilies_insert_last hu'.1 (by omega) p.2 hG
          apply Finset.mem_filter.mpr
          exact ⟨hvalid, ⟨(p.1, s), Finset.mem_insert_self .., rfl⟩⟩
        · intro p hp q hq hpq
          rcases Finset.mem_sigma.mp hp with ⟨hpu, hpg⟩
          rcases Finset.mem_sigma.mp hq with ⟨hqu, hqg⟩
          have hpu' := Finset.mem_Icc.mp hpu
          have hpf : insert (p.1, s) p.2 ∈ intervalFamilies r s :=
            intervalFamilies_insert_last hpu'.1 (by omega) p.2 hpg
          have hpPair : (p.1, s) ∈ insert (p.1, s) p.2 := Finset.mem_insert_self ..
          have hqPair' : (q.1, s) ∈ insert (p.1, s) p.2 := by simp [hpq]
          have huEq := intervalFamilies_rightEndpoint_unique hpf hpPair hqPair' rfl rfl
          have hfirst : p.1 = q.1 := congrArg Prod.fst huEq
          cases p with
          | mk u G =>
            cases q with
            | mk v H =>
              dsimp at hfirst hpq ⊢
              subst v
              have hnotG : (u, s) ∉ G := by
                intro hmem
                have hbound := (intervalFamilies_mem_iff r (u - 1) G).mp hpg |>.1 (u, s) hmem
                have hrange := Finset.mem_Icc.mp hpu
                omega
              have hnotH : (u, s) ∉ H := by
                intro hmem
                have hbound := (intervalFamilies_mem_iff r (u - 1) H).mp hqg |>.1 (u, s) hmem
                have hrange := Finset.mem_Icc.mp hqu
                omega
              have hGH : G = H := by
                apply Finset.ext
                intro I
                have hmemEq := congrArg (fun K : Finset (ℕ × ℕ) => I ∈ K) hpq
                by_cases hI : I = (u, s)
                · subst I
                  exact iff_of_false hnotG hnotH
                · simpa [Finset.mem_insert, hI] using hmemEq
              subst H
              rfl
        · intro F hF
          have hF' := (Finset.mem_filter.mp hF).1
          have hhas := (Finset.mem_filter.mp hF).2
          obtain ⟨u, hu, G, hG, hdecomp⟩ :=
            intervalFamilies_decompose_last F hF' hhas
          exact ⟨⟨u, G⟩, Finset.mem_sigma.mpr ⟨hu, hG⟩, hdecomp.symm⟩
      have hcardSigma : T.card =
          ∑ u ∈ Finset.Icc r (s - 1), (intervalFamilies r (u - 1)).card := by
        simp [T, Finset.sigma]
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := intervalFamilies r s) hasLast
      rw [← hlast, hcardSigma, hprefix] at hsplit
      have hterms : ∀ u ∈ Finset.Icc r (s - 1),
          (intervalFamilies r (u - 1)).card ≤ 4 ^ (u - r) := by
        intro u hu
        have hu' := Finset.mem_Icc.mp hu
        by_cases hur : u = r
        · subst u
          rw [intervalFamilies_empty r hr]
          simp
        · have hru : r ≤ u - 1 := by omega
          have hbound := ih (u - 1) (by omega) (r := r) hr hru
          have hexp : (u - 1) - r + 1 = u - r := by omega
          simpa [hexp] using hbound
      have hsum :
          (∑ u ∈ Finset.Icc r (s - 1), (intervalFamilies r (u - 1)).card) ≤
            4 ^ (s - r) := by
        calc
          _ ≤ ∑ u ∈ Finset.Icc r (s - 1), 4 ^ (u - r) :=
            Finset.sum_le_sum fun u hu => hterms u hu
          _ = ∑ u ∈ Finset.Icc r (s - 1), 4 ^ (u - r) := rfl
          _ ≤ 4 ^ ((s - 1) - r + 1) := sum_interval_pow_four_le r (s - 1) hrs'
          _ = 4 ^ (s - r) := by congr 1; omega
      have hpre := ih (s - 1) (by omega) (r := r) hr hrs'
      have hpre' : (intervalFamilies r (s - 1)).card ≤ 4 ^ (s - r) := by
        have hexp : (s - 1) - r + 1 = s - r := by omega
        simpa [hexp] using hpre
      have hrecEq : (intervalFamilies r s).card =
          (intervalFamilies r (s - 1)).card +
            ∑ u ∈ Finset.Icc r (s - 1), (intervalFamilies r (u - 1)).card := by
        omega
      rw [hrecEq]
      have hpow : 4 ^ (s - r) + 4 ^ (s - r) ≤ 4 ^ (s - r + 1) := by
        rw [show s - r + 1 = (s - r) + 1 by omega, pow_succ]
        omega
      calc
        (intervalFamilies r (s - 1)).card +
            ∑ u ∈ Finset.Icc r (s - 1), (intervalFamilies r (u - 1)).card ≤
            4 ^ (s - r) + 4 ^ (s - r) := Nat.add_le_add hpre' hsum
        _ ≤ 4 ^ (s - r + 1) := hpow

private def candidateComponentSpans (r s : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc r s ×ˢ Finset.Icc r s).filter fun c => c.1 < c.2

private def componentChoiceUniverse (r s : ℕ) :
    Finset (Σ _c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) :=
  (candidateComponentSpans r s).sigma fun _c =>
    intervalFamilies _c.1 _c.2 ×ˢ intervalFamilies _c.1 _c.2

private noncomputable def componentEncoding (r s : ℕ) (F G : Finset (ℕ × ℕ)) :
    Finset (Σ _c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) :=
  (pairComponents r s F G).image fun c =>
    ⟨c, (restrictIntervalFamily F c, restrictIntervalFamily G c)⟩

private noncomputable def componentDatumWeight (ε : ℝ) (K : ℕ)
    (d : Σ _c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) : ℝ := by
  classical
  exact ε ^ (d.1.2 - d.1.1) * ((K : ℝ) - d.1.2) ^
    (-(if d.2.1.card + d.2.2.card = 1 then (3 / 2 : ℝ) else 2))

private theorem componentEncoding_prod_weight_eq {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    (ε : ℝ) (K : ℕ) :
    ∏ d ∈ componentEncoding r s F G, componentDatumWeight ε K d =
      ∏ c ∈ pairComponents r s F G, componentWeight ε K F G c := by
  classical
  have hInj : Set.InjOn
      (fun c => (⟨c, (restrictIntervalFamily F c, restrictIntervalFamily G c)⟩ :
        Σ c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)))
      (pairComponents r s F G) := by
    intro c hc d hd hEq
    exact congrArg Sigma.fst hEq
  change ∏ d ∈ (pairComponents r s F G).image
      (fun c => (⟨c, (restrictIntervalFamily F c, restrictIntervalFamily G c)⟩ :
        Σ c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ))), componentDatumWeight ε K d = _
  rw [Finset.prod_image hInj]
  apply Finset.prod_congr rfl
  intro c hc
  simp only [componentDatumWeight, componentWeight]
  rw [if_congr (restrict_isolated_iff F G c).symm rfl rfl]

private theorem componentEncoding_recover_left {r s : ℕ} (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) :
    (componentEncoding r s F G).biUnion (fun d => d.2.1) = F := by
  classical
  change ((pairComponents r s F G).image
      (fun c => (⟨c, (restrictIntervalFamily F c, restrictIntervalFamily G c)⟩ :
        Σ c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)))).biUnion
      (fun d => d.2.1) = F
  rw [Finset.image_biUnion]
  simpa using (intervalFamily_reconstruct r s hr F G hF hG).symm

private theorem componentEncoding_recover_right {r s : ℕ} (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) :
    (componentEncoding r s F G).biUnion (fun d => d.2.2) = G := by
  classical
  change ((pairComponents r s F G).image
      (fun c => (⟨c, (restrictIntervalFamily F c, restrictIntervalFamily G c)⟩ :
        Σ c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)))).biUnion
      (fun d => d.2.2) = G
  rw [Finset.image_biUnion]
  simpa using (intervalFamily_reconstruct_right r s hr F G hF hG).symm

private theorem componentEncoding_injective {r s : ℕ} (hr : 1 ≤ r)
    {F G F' G' : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) (hF' : F' ∈ intervalFamilies r s)
    (hG' : G' ∈ intervalFamilies r s)
    (h : componentEncoding r s F G = componentEncoding r s F' G') :
    F = F' ∧ G = G' := by
  have hleft := congrArg (fun D => D.biUnion fun d => d.2.1) h
  have hright := congrArg (fun D => D.biUnion fun d => d.2.2) h
  rw [componentEncoding_recover_left hr hF hG,
    componentEncoding_recover_left hr hF' hG'] at hleft
  rw [componentEncoding_recover_right hr hF hG,
    componentEncoding_recover_right hr hF' hG'] at hright
  exact ⟨hleft, hright⟩

private theorem pairComponent_mem_candidate {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G) :
    c ∈ candidateComponentSpans r s := by
  simp only [pairComponents, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc] at hc
  simp [candidateComponentSpans, hc.1, hc.2.1]

private theorem componentEncoding_subset_universe {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s) :
    componentEncoding r s F G ⊆ componentChoiceUniverse r s := by
  classical
  rw [componentEncoding, Finset.image_subset_iff]
  intro c hc
  rw [componentChoiceUniverse, Finset.mem_sigma]
  refine ⟨pairComponent_mem_candidate hc, ?_⟩
  simp only [Finset.mem_product]
  exact ⟨restrictIntervalFamily_mem hF, restrictIntervalFamily_mem hG⟩

private theorem componentEncoding_nonempty {r s : ℕ} (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) (hFne : F.Nonempty) :
    (componentEncoding r s F G).Nonempty := by
  classical
  obtain ⟨I, hI⟩ := hFne
  obtain ⟨c, hc, -, -⟩ := interval_exists_pairComponent hr hF hG
    (Finset.mem_union.mpr (Or.inl hI))
  refine ⟨⟨c, (restrictIntervalFamily F c, restrictIntervalFamily G c)⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨c, hc, rfl⟩

private theorem componentChoices_card_le {r s : ℕ} {c : ℕ × ℕ}
    (hr : 1 ≤ r) (hc : c ∈ candidateComponentSpans r s) :
    (intervalFamilies c.1 c.2 ×ˢ intervalFamilies c.1 c.2).card ≤
      16 ^ (c.2 - c.1 + 1) := by
  have hc' : c.1 < c.2 ∧ r ≤ c.1 ∧ c.2 ≤ s := by
    simp [candidateComponentSpans, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hc
    omega
  have hfamily := intervalFamilies_card_le_four_pow
    (r := c.1) (s := c.2) (by omega) (by omega)
  rw [Finset.card_product]
  calc
    (intervalFamilies c.1 c.2).card * (intervalFamilies c.1 c.2).card ≤
        (4 ^ (c.2 - c.1 + 1)) * (4 ^ (c.2 - c.1 + 1)) :=
      Nat.mul_le_mul hfamily hfamily
    _ = 16 ^ (c.2 - c.1 + 1) := by
      rw [← mul_pow]
      norm_num

private theorem componentDatumWeight_le_envelope {r s : ℕ}
    (ε : ℝ) (hε : 0 ≤ ε) {K : ℕ} (hK : s < K)
    {d : Σ _c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)}
    (hd : d ∈ componentChoiceUniverse r s) :
    componentDatumWeight ε K d ≤
      ε ^ (d.1.2 - d.1.1) * ((K : ℝ) - d.1.2) ^ (-(3 / 2 : ℝ)) := by
  classical
  rcases Finset.mem_sigma.mp hd with ⟨hc, hp⟩
  have hspan : d.1.1 < d.1.2 ∧ r ≤ d.1.1 ∧ d.1.2 ≤ s := by
    simp [candidateComponentSpans, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hc
    omega
  have hnat : 1 ≤ K - d.1.2 := by omega
  have hbase : (1 : ℝ) ≤ (K : ℝ) - d.1.2 := by
    have hcast : ((K - d.1.2 : ℕ) : ℝ) = (K : ℝ) - d.1.2 := by
      exact_mod_cast Nat.cast_sub (Nat.le_of_lt (lt_of_le_of_lt hspan.2.2 hK))
    rw [← hcast]
    exact_mod_cast hnat
  have hexp : -(if d.2.1.card + d.2.2.card = 1 then (3 / 2 : ℝ) else 2) ≤
      -(3 / 2 : ℝ) := by
    split_ifs <;> norm_num
  unfold componentDatumWeight
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε _)
  exact Real.rpow_le_rpow_of_exponent_le hbase hexp

private theorem componentDatumWeight_nonneg {r s : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    {K : ℕ} (hK : s < K)
    {d : Σ _c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)}
    (hd : d ∈ componentChoiceUniverse r s) : 0 ≤ componentDatumWeight ε K d := by
  classical
  rcases Finset.mem_sigma.mp hd with ⟨hc, -⟩
  have hspan : r ≤ d.1.2 ∧ d.1.2 ≤ s := by
    simp [candidateComponentSpans, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hc
    omega
  have hbase : 0 ≤ (K : ℝ) - d.1.2 := by
    have hcast : ((K - d.1.2 : ℕ) : ℝ) = (K : ℝ) - d.1.2 := by
      exact_mod_cast Nat.cast_sub (Nat.le_of_lt (lt_of_le_of_lt hspan.2 hK))
    rw [← hcast]
    exact_mod_cast (Nat.zero_le (K - d.1.2))
  unfold componentDatumWeight
  exact mul_nonneg (pow_nonneg hε _) (Real.rpow_nonneg hbase _)


private theorem componentChoiceUniverse_envelope_sum_le_spans {r s K : ℕ}
    (hr : 1 ≤ r) (hK : s < K) (ε : ℝ) (hε : 0 ≤ ε) :
    ∑ d ∈ componentChoiceUniverse r s,
        ε ^ (d.1.2 - d.1.1) * ((K : ℝ) - d.1.2) ^ (-(3 / 2 : ℝ)) ≤
      ∑ c ∈ candidateComponentSpans r s,
        (16 : ℝ) ^ (c.2 - c.1 + 1) * ε ^ (c.2 - c.1) *
          ((K : ℝ) - c.2) ^ (-(3 / 2 : ℝ)) := by
  classical
  rw [componentChoiceUniverse, Finset.sum_sigma]
  apply Finset.sum_le_sum
  intro c hc
  let choices := intervalFamilies c.1 c.2 ×ˢ intervalFamilies c.1 c.2
  have hcard : (choices.card : ℝ) ≤ (16 : ℝ) ^ (c.2 - c.1 + 1) := by
    exact_mod_cast componentChoices_card_le hr (by simpa [choices] using hc)
  have hcp := Finset.mem_filter.mp hc
  have hsp := Finset.mem_product.mp hcp.1
  have hcs := Finset.mem_Icc.mp hsp.2
  have hnat : 1 ≤ K - c.2 := by omega
  have hbase : (1 : ℝ) ≤ (K : ℝ) - c.2 := by
    have hcast : ((K - c.2 : ℕ) : ℝ) = (K : ℝ) - c.2 := by
      exact_mod_cast Nat.cast_sub (Nat.le_of_lt (lt_of_le_of_lt hcs.2 hK))
    rw [← hcast]
    exact_mod_cast hnat
  have hfactor : 0 ≤ ε ^ (c.2 - c.1) *
      ((K : ℝ) - c.2) ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg (pow_nonneg hε _) (Real.rpow_nonneg (by positivity) _)
  calc
    (∑ p ∈ choices,
        ε ^ (c.2 - c.1) * ((K : ℝ) - c.2) ^ (-(3 / 2 : ℝ))) =
      (choices.card : ℝ) *
        (ε ^ (c.2 - c.1) * ((K : ℝ) - c.2) ^ (-(3 / 2 : ℝ))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (16 : ℝ) ^ (c.2 - c.1 + 1) *
        (ε ^ (c.2 - c.1) * ((K : ℝ) - c.2) ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = (16 : ℝ) ^ (c.2 - c.1 + 1) * ε ^ (c.2 - c.1) *
        ((K : ℝ) - c.2) ^ (-(3 / 2 : ℝ)) := by ring

private theorem sum_pow_gap_le {r b : ℕ} (hrb : r < b) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    ∑ a ∈ Finset.Icc r (b - 1), q ^ (b - a) ≤ 2 * q := by
  have hterm : ∀ a ∈ Finset.Icc r (b - 1),
      q ^ (b - a) ≤ q * (1 / 2 : ℝ) ^ (b - a - 1) := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    have hlen : 1 ≤ b - a := by omega
    calc
      q ^ (b - a) = q ^ ((b - a - 1) + 1) := by congr 1; omega
      _ = q ^ (b - a - 1) * q := by rw [pow_succ]
      _ = q * q ^ (b - a - 1) := by ring
      _ ≤ q * (1 / 2 : ℝ) ^ (b - a - 1) := by
        gcongr
  have hreindex :
      ∑ a ∈ Finset.Icc r (b - 1), (1 / 2 : ℝ) ^ (b - a - 1) =
        ∑ k ∈ Finset.range (b - r), (1 / 2 : ℝ) ^ k := by
    symm
    apply Finset.sum_bij (fun k _ => b - 1 - k)
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      have hkr : r + k < b := by omega
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k hk l hl hEq
      have hk' := Finset.mem_range.mp hk
      have hl' := Finset.mem_range.mp hl
      have hkr : r + k < b := by omega
      have hlr : r + l < b := by omega
      omega
    · intro a ha
      have ha' := Finset.mem_Icc.mp ha
      refine ⟨b - a - 1, Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · omega
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      have hkr : r + k < b := by omega
      congr 1
      omega
  calc
    ∑ a ∈ Finset.Icc r (b - 1), q ^ (b - a) ≤
        ∑ a ∈ Finset.Icc r (b - 1), q * (1 / 2 : ℝ) ^ (b - a - 1) :=
      Finset.sum_le_sum fun a ha => hterm a ha
    _ = q * ∑ a ∈ Finset.Icc r (b - 1), (1 / 2 : ℝ) ^ (b - a - 1) := by
      rw [Finset.mul_sum]
    _ = q * ∑ k ∈ Finset.range (b - r), (1 / 2 : ℝ) ^ k := by rw [hreindex]
    _ ≤ q * 2 := by
      exact mul_le_mul_of_nonneg_left (sum_geometric_two_le (b - r)) hq0
    _ = 2 * q := by ring

private theorem candidateSpan_sum_eq {r s : ℕ} (f : ℕ × ℕ → ℝ) :
    ∑ c ∈ candidateComponentSpans r s, f c =
      ∑ b ∈ Finset.Icc (r + 1) s, ∑ a ∈ Finset.Icc r (b - 1), f (a, b) := by
  classical
  symm
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => (p.2, p.1))
  · intro p hp
    rcases Finset.mem_sigma.mp hp with ⟨hb, ha⟩
    have hb' := Finset.mem_Icc.mp hb
    have ha' := Finset.mem_Icc.mp ha
    rcases hb' with ⟨hrb, hbs⟩
    rcases ha' with ⟨hra, habound⟩
    simp only [candidateComponentSpans, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    exact ⟨⟨⟨hra, le_trans habound (le_trans (Nat.sub_le _ _) hbs)⟩,
      ⟨by omega, hbs⟩⟩, by omega⟩
  · intro p hp q hq hEq
    cases p with
    | mk b a =>
      cases q with
      | mk b' a' =>
        simp only [Prod.mk.injEq] at hEq
        simp_all
  · intro c hc
    rcases c with ⟨a, b⟩
    simp only [candidateComponentSpans, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hc
    rcases hc with ⟨⟨⟨hra, has⟩, ⟨hrb, hbs⟩⟩, hab⟩
    have hrb' : r + 1 ≤ b := by omega
    refine ⟨⟨b, a⟩, Finset.mem_sigma.mpr ?_, ?_⟩
    · refine ⟨Finset.mem_Icc.mpr ⟨hrb', hbs⟩,
        Finset.mem_Icc.mpr ⟨hra, ?_⟩⟩
      exact Nat.le_pred_of_lt hab
    · rfl
  · intro p hp
    rfl

private theorem sum_inv_succ_diff_eq {D T : ℕ} (hDT : D ≤ T) :
    ∑ n ∈ Finset.Icc D T,
        ( (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) =
      (D : ℝ)⁻¹ - ((T + 1 : ℕ) : ℝ)⁻¹ := by
  revert D
  induction T with
  | zero =>
    intro D hD
    have hD0 : D = 0 := by omega
    subst D
    simp
  | succ T ih =>
    intro D hD
    by_cases hDT : D ≤ T
    · rw [Finset.sum_Icc_succ_top hD]
      rw [ih hDT]
      ring
    · have hEq : D = T + 1 := by omega
      subst D
      simp

private theorem sum_sqrt_inv_succ_diff_eq {D T : ℕ} (hDT : D ≤ T) :
    ∑ n ∈ Finset.Icc D T,
        ((n : ℝ) ^ (-(1 / 2 : ℝ)) - ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (D : ℝ) ^ (-(1 / 2 : ℝ)) - ((T + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  revert D
  induction T with
  | zero =>
    intro D hD
    have hD0 : D = 0 := by omega
    subst D
    simp
  | succ T ih =>
    intro D hD
    by_cases hDT : D ≤ T
    · rw [Finset.sum_Icc_succ_top hD]
      rw [ih hDT]
      ring
    · have hEq : D = T + 1 := by omega
      subst D
      simp

private theorem nat_inv_sq_le_succ_diff {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-2 : ℝ) ≤
      2 * ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hncast : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hplus : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by exact_mod_cast Nat.cast_add n 1
  have hpow : (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ := by
    calc
      (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hnpos)]
      _ = ((n : ℝ) ^ 2)⁻¹ := congrArg Inv.inv (Real.rpow_natCast (n : ℝ) 2)
  rw [hpow, hcast]
  field_simp [hnpos.ne', hplus.ne']
  nlinarith

private theorem nat_inv_sqrt_eq_sqrt_inv {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) = (√(n : ℝ))⁻¹ := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (n : ℝ) ^ (-(1 / 2 : ℝ)) = ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hnpos)]
    _ = (√(n : ℝ))⁻¹ := by rw [← Real.sqrt_eq_rpow]

private theorem nat_inv_three_halves_eq {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((n : ℝ) * √(n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (n : ℝ) ^ (-(3 / 2 : ℝ)) =
        (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(3 / 2 : ℝ)) = (-1 : ℝ) + (-(1 / 2 : ℝ)) by norm_num,
        Real.rpow_add hnpos]
    _ = 1 / ((n : ℝ) * √(n : ℝ)) := by
      rw [Real.rpow_neg_one, nat_inv_sqrt_eq_sqrt_inv hn]
      field_simp

private theorem nat_inv_three_halves_le_sqrt_diff {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      8 * ((n : ℝ) ^ (-(1 / 2 : ℝ)) -
        ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hn0 : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp1 : 0 < n + 1 := by omega
  have hnp1real : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hnp1
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    exact_mod_cast Nat.cast_add n 1
  have hx : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnreal
  have hy : 0 < √((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hnp1real
  have hx2 : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnreal.le
  have hy2 : (√((n + 1 : ℕ) : ℝ)) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hnp1real.le
  have hyle : √((n + 1 : ℕ) : ℝ) ≤ 2 * √(n : ℝ) := by
    rw [Real.sqrt_le_left (by positivity), hcast]
    have hfour : (2 * √(n : ℝ)) ^ 2 = 4 * (n : ℝ) := by
      calc
        _ = 4 * (√(n : ℝ)) ^ 2 := by ring
        _ = 4 * (n : ℝ) := by rw [hx2]
    nlinarith [hfour, hncast]
  have hsumle : √(n : ℝ) + √((n + 1 : ℕ) : ℝ) ≤ 3 * √(n : ℝ) := by linarith
  have hden : √(n : ℝ) * √((n + 1 : ℕ) : ℝ) *
      (√(n : ℝ) + √((n + 1 : ℕ) : ℝ)) ≤
        8 * ((n : ℝ) * √(n : ℝ)) := by
    calc
      _ ≤ √(n : ℝ) * (2 * √(n : ℝ)) * (3 * √(n : ℝ)) := by
        gcongr
      _ = 6 * ((n : ℝ) * √(n : ℝ)) := by
        calc
          _ = 6 * ((√(n : ℝ)) ^ 2 * √(n : ℝ)) := by ring
          _ = 6 * ((n : ℝ) * √(n : ℝ)) := by rw [hx2]
      _ ≤ 8 * ((n : ℝ) * √(n : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 8)
          (mul_nonneg hnreal.le hx.le)
  have hrootdiff : √((n + 1 : ℕ) : ℝ) ^ 2 - √(n : ℝ) ^ 2 = 1 := by
    rw [hy2, hx2, hcast]
    ring
  have hinvroot :
      (√(n : ℝ))⁻¹ - (√((n + 1 : ℕ) : ℝ))⁻¹ =
        1 / (√(n : ℝ) * √((n + 1 : ℕ) : ℝ) *
          (√(n : ℝ) + √((n + 1 : ℕ) : ℝ))) := by
    field_simp [hx.ne', hy.ne', (show √(n : ℝ) + √((n + 1 : ℕ) : ℝ) ≠ 0 by positivity)]
    nlinarith [hrootdiff]
  have hdenpos : 0 < √(n : ℝ) * √((n + 1 : ℕ) : ℝ) *
      (√(n : ℝ) + √((n + 1 : ℕ) : ℝ)) := by positivity
  have hrhspos : 0 < 8 * ((n : ℝ) * √(n : ℝ)) := by positivity
  have hrecip :
      1 / ((n : ℝ) * √(n : ℝ)) ≤
        8 / (√(n : ℝ) * √((n + 1 : ℕ) : ℝ) *
          (√(n : ℝ) + √((n + 1 : ℕ) : ℝ))) := by
    rw [div_le_div_iff₀ (mul_pos hnreal hx) hdenpos]
    nlinarith [hden]
  rw [nat_inv_three_halves_eq hn0, nat_inv_sqrt_eq_sqrt_inv hn0,
    nat_inv_sqrt_eq_sqrt_inv hnp1]
  rw [hinvroot]
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hrecip

private theorem sum_nat_inv_three_halves_le {D T : ℕ} (hD : 1 ≤ D) (hDT : D ≤ T) :
    ∑ n ∈ Finset.Icc D T, (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      8 / √(D : ℝ) := by
  have hsum :
      ∑ n ∈ Finset.Icc D T, (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        ∑ n ∈ Finset.Icc D T,
          8 * ((n : ℝ) ^ (-(1 / 2 : ℝ)) -
            ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    apply Finset.sum_le_sum
    intro n hn
    exact nat_inv_three_halves_le_sqrt_diff (le_trans hD (Finset.mem_Icc.mp hn).1)
  have htel :
      ∑ n ∈ Finset.Icc D T,
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) -
            ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        (D : ℝ) ^ (-(1 / 2 : ℝ)) - ((T + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sum_sqrt_inv_succ_diff_eq hDT
  calc
    _ ≤ 8 * ((D : ℝ) ^ (-(1 / 2 : ℝ)) -
          ((T + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
      calc
        _ ≤ ∑ n ∈ Finset.Icc D T,
            8 * ((n : ℝ) ^ (-(1 / 2 : ℝ)) -
              ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := hsum
        _ = 8 * ((D : ℝ) ^ (-(1 / 2 : ℝ)) -
              ((T + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by rw [← Finset.mul_sum, htel]
    _ ≤ 8 / √(D : ℝ) := by
      rw [nat_inv_sqrt_eq_sqrt_inv hD]
      have htail : 0 ≤ ((T + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have hdiff : (D : ℝ) ^ (-(1 / 2 : ℝ)) -
          ((T + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (D : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
      have hDpos : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
      have hpow : (D : ℝ) ^ (-(1 / 2 : ℝ)) = (√(D : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hDpos), ← Real.sqrt_eq_rpow]
      calc
        _ ≤ 8 * (D : ℝ) ^ (-(1 / 2 : ℝ)) := by nlinarith [hdiff]
        _ = 8 / √(D : ℝ) := by rw [hpow, div_eq_mul_inv]

private theorem span_envelope_sum_le {r s K : ℕ} (hKs : s < K)
    {ε q p T : ℝ} (hq : q = 16 * ε) (hq0 : 0 ≤ q)
    (hsmall : q ≤ 1 / 2)
    (hendpoint : ∑ b ∈ Finset.Icc r s, ((K : ℝ) - b) ^ p ≤ T) :
    ∑ c ∈ candidateComponentSpans r s,
        (16 : ℝ) ^ (c.2 - c.1 + 1) * ε ^ (c.2 - c.1) *
          ((K : ℝ) - c.2) ^ p ≤ 32 * q * T := by
  classical
  rw [candidateSpan_sum_eq]
  have hterms : ∀ b ∈ Finset.Icc (r + 1) s,
      ∑ a ∈ Finset.Icc r (b - 1),
          (16 : ℝ) ^ (b - a + 1) * ε ^ (b - a) * ((K : ℝ) - b) ^ p ≤
        32 * q * ((K : ℝ) - b) ^ p := by
    intro b hb
    have hb' := Finset.mem_Icc.mp hb
    have hrb : r < b := by omega
    have hbK : b ≤ K := le_trans hb'.2 (Nat.le_of_lt hKs)
    have hbKreal : (b : ℝ) ≤ (K : ℝ) := by exact_mod_cast hbK
    have hbase : 0 ≤ (K : ℝ) - b := by linarith
    have hg : 0 ≤ ((K : ℝ) - b) ^ p := Real.rpow_nonneg hbase _
    have hfactor : 0 ≤ 16 * ((K : ℝ) - b) ^ p := mul_nonneg (by norm_num) hg
    have hsum := sum_pow_gap_le hrb hq0 hsmall
    calc
      _ = 16 * ((K : ℝ) - b) ^ p *
          ∑ a ∈ Finset.Icc r (b - 1), q ^ (b - a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        have hpow : (16 : ℝ) ^ (b - a + 1) * ε ^ (b - a) =
            16 * q ^ (b - a) := by
          rw [hq]
          calc
            _ = ((16 : ℝ) ^ (b - a) * 16) * ε ^ (b - a) := by rw [pow_succ]
            _ = 16 * ((16 * ε) ^ (b - a)) := by rw [mul_pow]; ring
        rw [hpow]
        ring
      _ ≤ 16 * ((K : ℝ) - b) ^ p * (2 * q) :=
        mul_le_mul_of_nonneg_left hsum hfactor
      _ = 32 * q * ((K : ℝ) - b) ^ p := by ring
  calc
    _ = ∑ b ∈ Finset.Icc (r + 1) s,
        ∑ a ∈ Finset.Icc r (b - 1),
          (16 : ℝ) ^ (b - a + 1) * ε ^ (b - a) * ((K : ℝ) - b) ^ p := rfl
    _ ≤ ∑ b ∈ Finset.Icc (r + 1) s, 32 * q * ((K : ℝ) - b) ^ p :=
      Finset.sum_le_sum hterms
    _ ≤ ∑ b ∈ Finset.Icc r s, 32 * q * ((K : ℝ) - b) ^ p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        rcases Finset.mem_Icc.mp hb with ⟨hlo, hhi⟩
        exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
      · intro b hb hnot
        have hb' := Finset.mem_Icc.mp hb
        have hbK : b ≤ K := le_trans hb'.2 (Nat.le_of_lt hKs)
        have hbKreal : (b : ℝ) ≤ (K : ℝ) := by exact_mod_cast hbK
        have hbase : 0 ≤ (K : ℝ) - b := by linarith
        exact mul_nonneg (mul_nonneg (by norm_num) hq0) (Real.rpow_nonneg hbase _)
    _ = 32 * q * ∑ b ∈ Finset.Icc r s, ((K : ℝ) - b) ^ p := by
      rw [Finset.mul_sum]
    _ ≤ 32 * q * T := by
      exact mul_le_mul_of_nonneg_left hendpoint (mul_nonneg (by norm_num) hq0)

/-- The inverse-square sum from a positive lower endpoint is at most two divided by that endpoint. -/
theorem sum_nat_inv_sq_le {D T : ℕ} (hD : 1 ≤ D) (hDT : D ≤ T) :
    ∑ n ∈ Finset.Icc D T, (n : ℝ) ^ (-2 : ℝ) ≤ 2 / (D : ℝ) := by
  have hsum :
      ∑ n ∈ Finset.Icc D T, (n : ℝ) ^ (-2 : ℝ) ≤
        ∑ n ∈ Finset.Icc D T,
          2 * ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact nat_inv_sq_le_succ_diff (le_trans hD hn'.1)
  calc
    ∑ n ∈ Finset.Icc D T, (n : ℝ) ^ (-2 : ℝ) ≤
        2 * ∑ n ∈ Finset.Icc D T,
          ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
      simpa only [Finset.mul_sum] using hsum
    _ = 2 * ((D : ℝ)⁻¹ - ((T + 1 : ℕ) : ℝ)⁻¹) := by
      rw [sum_inv_succ_diff_eq hDT]
    _ ≤ 2 / (D : ℝ) := by
      have hTpos : 0 ≤ ((T + 1 : ℕ) : ℝ)⁻¹ := by positivity
      have hdiff : (D : ℝ)⁻¹ - ((T + 1 : ℕ) : ℝ)⁻¹ ≤ (D : ℝ)⁻¹ := by linarith
      calc
        2 * ((D : ℝ)⁻¹ - ((T + 1 : ℕ) : ℝ)⁻¹) ≤ 2 * (D : ℝ)⁻¹ := by nlinarith
        _ = 2 / (D : ℝ) := by rw [div_eq_mul_inv]

/-- Subtraction from a fixed natural number reverses the indicated finite sum. -/
theorem sum_nat_sub_reindex {r s K : ℕ} (hrs : r ≤ s) (hKs : s < K)
    (f : ℕ → ℝ) :
    ∑ b ∈ Finset.Icc r s, f (K - b) =
      ∑ n ∈ Finset.Icc (K - s) (K - r), f n := by
  classical
  apply Finset.sum_bij (fun b _ => K - b)
  · intro b hb
    rcases Finset.mem_Icc.mp hb with ⟨hrb, hbs⟩
    exact Finset.mem_Icc.mpr ⟨Nat.sub_le_sub_left hbs K, Nat.sub_le_sub_left hrb K⟩
  · intro b hb c hc heq
    have hb' := Finset.mem_Icc.mp hb
    have hc' := Finset.mem_Icc.mp hc
    have hbK : b ≤ K := le_trans hb'.2 (Nat.le_of_lt hKs)
    have hcK : c ≤ K := le_trans hc'.2 (Nat.le_of_lt hKs)
    omega
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
    have hleft : r ≤ K - n := by
      calc
        r = K - (K - r) := (Nat.sub_sub_self (by omega)).symm
        _ ≤ K - n := Nat.sub_le_sub_left hhi K
    have hright : K - n ≤ s := by
      calc
        K - n ≤ K - (K - s) := Nat.sub_le_sub_left hlo K
        _ = s := Nat.sub_sub_self (by omega)
    refine ⟨K - n, Finset.mem_Icc.mpr ⟨hleft, hright⟩, ?_⟩
    exact Nat.sub_sub_self (le_trans hhi (Nat.sub_le K r))
  · intro b hb
    rfl

private theorem sum_endpoint_inv_sq_le {r s K : ℕ} (hrs : r ≤ s) (hKs : s < K) :
    ∑ b ∈ Finset.Icc r s, ((K : ℝ) - b) ^ (-2 : ℝ) ≤
      2 / ((K : ℝ) - s) := by
  have hD : 1 ≤ K - s := by omega
  have hDT : K - s ≤ K - r := Nat.sub_le_sub_left hrs K
  have hcast : ((K - s : ℕ) : ℝ) = (K : ℝ) - s := by
    exact_mod_cast Nat.cast_sub (by omega : s ≤ K)
  calc
    _ = ∑ b ∈ Finset.Icc r s, ((K - b : ℕ) : ℝ) ^ (-2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := Finset.mem_Icc.mp hb
      have hbK : b ≤ K := le_trans hb'.2 (Nat.le_of_lt hKs)
      rw [show (K : ℝ) - b = ((K - b : ℕ) : ℝ) by
        exact (Nat.cast_sub hbK).symm]
    _ = ∑ n ∈ Finset.Icc (K - s) (K - r), (n : ℝ) ^ (-2 : ℝ) :=
      sum_nat_sub_reindex hrs hKs (fun n => (n : ℝ) ^ (-2 : ℝ))
    _ ≤ 2 / ((K - s : ℕ) : ℝ) := sum_nat_inv_sq_le hD hDT
    _ = 2 / ((K : ℝ) - s) := by rw [hcast]

/-- A shifted inverse three-halves tail is bounded by the inverse square root of the gap
to the right endpoint. -/
theorem sum_endpoint_inv_three_halves_le {r s K : ℕ}
    (hrs : r ≤ s) (hKs : s < K) :
    ∑ b ∈ Finset.Icc r s, ((K : ℝ) - b) ^ (-(3 / 2 : ℝ)) ≤
      8 / √((K : ℝ) - s) := by
  have hD : 1 ≤ K - s := by omega
  have hDT : K - s ≤ K - r := Nat.sub_le_sub_left hrs K
  have hcast : ((K - s : ℕ) : ℝ) = (K : ℝ) - s := by
    exact_mod_cast Nat.cast_sub (by omega : s ≤ K)
  calc
    _ = ∑ b ∈ Finset.Icc r s, ((K - b : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := Finset.mem_Icc.mp hb
      have hbK : b ≤ K := le_trans hb'.2 (Nat.le_of_lt hKs)
      rw [show (K : ℝ) - b = ((K - b : ℕ) : ℝ) by
        exact (Nat.cast_sub hbK).symm]
    _ = ∑ n ∈ Finset.Icc (K - s) (K - r), (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
      sum_nat_sub_reindex hrs hKs (fun n => (n : ℝ) ^ (-(3 / 2 : ℝ)))
    _ ≤ 8 / √((K - s : ℕ) : ℝ) := sum_nat_inv_three_halves_le hD hDT
    _ = 8 / √((K : ℝ) - s) := by rw [hcast]

private theorem prod_one_sub_ge_one_sub_sum {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (hw : ∀ x ∈ U, 0 ≤ w x)
    (hA : ∑ x ∈ U, w x ≤ 1 / 2) :
    1 - ∑ x ∈ U, w x ≤ ∏ x ∈ U, (1 - w x) := by
  classical
  revert hw hA
  induction U using Finset.induction_on with
  | empty => intro hw hA; simp
  | @insert a U ha ih =>
    intro hw hA
    have ha0 : 0 ≤ w a := hw a (Finset.mem_insert_self ..)
    have hU0 : 0 ≤ ∑ x ∈ U, w x := Finset.sum_nonneg fun x hx =>
      hw x (Finset.mem_insert_of_mem hx)
    have hsum : (∑ x ∈ insert a U, w x) = w a + ∑ x ∈ U, w x :=
      Finset.sum_insert ha
    rw [hsum] at hA
    have hUle : ∑ x ∈ U, w x ≤ 1 / 2 := by linarith
    have ih' := ih (fun x hx => hw x (Finset.mem_insert_of_mem hx)) hUle
    have hfactor : 0 ≤ 1 - w a := by linarith
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    calc
      1 - (w a + ∑ x ∈ U, w x) ≤
          (1 - w a) * (1 - ∑ x ∈ U, w x) := by
        nlinarith [mul_nonneg ha0 hU0]
      _ ≤ (1 - w a) * ∏ x ∈ U, (1 - w x) :=
        mul_le_mul_of_nonneg_left ih' hfactor

private theorem prod_one_add_le_inv_one_sub_sum {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (hw : ∀ x ∈ U, 0 ≤ w x)
    (hA : ∑ x ∈ U, w x ≤ 1 / 2) :
    ∏ x ∈ U, (1 + w x) ≤ 1 / (1 - ∑ x ∈ U, w x) := by
  classical
  have hwle : ∀ x ∈ U, w x ≤ 1 / 2 := by
    intro x hx
    exact (Finset.single_le_sum (fun y hy => hw y hy) hx).trans hA
  have hprod : ∏ x ∈ U, (1 + w x) ≤ ∏ x ∈ U, (1 - w x)⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro x hx
      exact add_nonneg (by norm_num) (hw x hx)
    · intro x hx
      have hden : 0 < 1 - w x := by linarith [hwle x hx]
      rw [inv_eq_one_div, le_div_iff₀ hden]
      nlinarith [sq_nonneg (w x)]
  rw [Finset.prod_inv_distrib] at hprod
  have hlower := prod_one_sub_ge_one_sub_sum U w hw hA
  have hprodpos : 0 < ∏ x ∈ U, (1 - w x) := by
    apply Finset.prod_pos
    intro x hx
    linarith [hwle x hx]
  have hdenpos : 0 < 1 - ∑ x ∈ U, w x := by
    have hnonneg := Finset.sum_nonneg hw
    linarith
  calc
    ∏ x ∈ U, (1 + w x) ≤ (∏ x ∈ U, (1 - w x))⁻¹ := hprod
    _ ≤ 1 / (1 - ∑ x ∈ U, w x) := by
      rw [div_eq_mul_inv, one_mul]
      exact (inv_le_inv₀ hprodpos hdenpos).2 hlower

private theorem sum_powerset_card_ge_two_le_two_sq {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (hw : ∀ x ∈ U, 0 ≤ w x)
    (hA : ∑ x ∈ U, w x ≤ 1 / 2) :
    ∑ S ∈ U.powerset.filter (fun S => 2 ≤ S.card), ∏ x ∈ S, w x ≤
      2 * (∑ x ∈ U, w x) ^ 2 := by
  classical
  let A := ∑ x ∈ U, w x
  let multi := ∑ S ∈ U.powerset.filter (fun S => 2 ≤ S.card), ∏ x ∈ S, w x
  have htotal :
      ∏ x ∈ U, (1 + w x) = 1 + A + multi := by
    dsimp [A, multi]
    rw [Finset.prod_one_add]
    rw [← Finset.sum_filter_add_sum_filter_not U.powerset (fun S => 2 ≤ S.card)]
    simp_rw [not_le, Nat.lt_succ_iff, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff,
      Finset.filter_or, ← Finset.powersetCard_eq_filter,
      Finset.sum_union (Finset.disjoint_powersetCard_of_ne zero_ne_one _ _),
      Finset.powersetCard_zero, Finset.powersetCard_one, Finset.sum_singleton,
      Finset.sum_map, Function.Embedding.coeFn_mk]
    simp [Finset.prod_empty, Finset.prod_singleton]
    ring
  have hA0 : 0 ≤ A := Finset.sum_nonneg hw
  have hAhalf : A ≤ 1 / 2 := hA
  have hprodBound : ∏ x ∈ U, (1 + w x) ≤ 1 / (1 - A) := by
    simpa [A] using prod_one_add_le_inv_one_sub_sum U w hw hA
  have hden : 0 < 1 - A := by linarith
  have hnum : 1 / (1 - A) ≤ 1 + A + 2 * A ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (sq_nonneg A) (by linarith : 0 ≤ 1 - 2 * A)]
  rw [htotal] at hprodBound
  dsimp [multi] at hprodBound ⊢
  linarith


private theorem componentChoiceUniverse_nonisolated_bound {r s K : ℕ}
    (hr : 1 ≤ r) (hrs : r ≤ s) (hKs : s < K) (ε q : ℝ)
    (hε : 0 ≤ ε) (hq : q = 16 * ε) (hq0 : 0 ≤ q) (hsmall : q ≤ 1 / 2) :
    ∑ d ∈ (componentChoiceUniverse r s).filter
        (fun d => d.2.1.card + d.2.2.card ≠ 1), componentDatumWeight ε K d ≤
      64 * q / ((K : ℝ) - s) := by
  classical
  rw [componentChoiceUniverse, Finset.filter_sigma, Finset.sum_sigma]
  have hterms : ∀ c ∈ candidateComponentSpans r s,
      ∑ p ∈ (intervalFamilies c.1 c.2 ×ˢ intervalFamilies c.1 c.2).filter
          (fun p => p.1.card + p.2.card ≠ 1), componentDatumWeight ε K ⟨c, p⟩ ≤
        (16 : ℝ) ^ (c.2 - c.1 + 1) * ε ^ (c.2 - c.1) *
          ((K : ℝ) - c.2) ^ (-2 : ℝ) := by
    intro c hc
    let choices := intervalFamilies c.1 c.2 ×ˢ intervalFamilies c.1 c.2
    let allowed := choices.filter (fun p => p.1.card + p.2.card ≠ 1)
    have hspan : c.1 < c.2 ∧ r ≤ c.1 ∧ c.2 ≤ s := by
      simp [candidateComponentSpans, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hc
      omega
    have hnat : 1 ≤ K - c.2 := by omega
    have hbase : (1 : ℝ) ≤ (K : ℝ) - c.2 := by
      have hcast : ((K - c.2 : ℕ) : ℝ) = (K : ℝ) - c.2 := by
        exact_mod_cast Nat.cast_sub (Nat.le_of_lt (lt_of_le_of_lt hspan.2.2 hKs))
      rw [← hcast]
      exact_mod_cast hnat
    have hheq : ∀ p ∈ allowed,
        componentDatumWeight ε K ⟨c, p⟩ =
          ε ^ (c.2 - c.1) * ((K : ℝ) - c.2) ^ (-2 : ℝ) := by
      intro p hp
      have hnot := (Finset.mem_filter.mp hp).2
      simp [componentDatumWeight, hnot]
    have hsum :
        (∑ p ∈ allowed, componentDatumWeight ε K ⟨c, p⟩) =
          (allowed.card : ℝ) *
            (ε ^ (c.2 - c.1) * ((K : ℝ) - c.2) ^ (-2 : ℝ)) := by
      rw [Finset.sum_congr rfl hheq]
      simp [Finset.sum_const, nsmul_eq_mul]
    have hcard : (allowed.card : ℝ) ≤ (16 : ℝ) ^ (c.2 - c.1 + 1) := by
      have hNatCard := Finset.card_filter_le choices (fun p => p.1.card + p.2.card ≠ 1)
      have hAllCard := componentChoices_card_le hr hc
      exact_mod_cast (le_trans hNatCard hAllCard)
    have hfactor : 0 ≤ ε ^ (c.2 - c.1) *
        ((K : ℝ) - c.2) ^ (-2 : ℝ) :=
      mul_nonneg (pow_nonneg hε _) (Real.rpow_nonneg (by positivity) _)
    rw [hsum]
    calc
      (allowed.card : ℝ) *
          (ε ^ (c.2 - c.1) * ((K : ℝ) - c.2) ^ (-2 : ℝ)) ≤
        (16 : ℝ) ^ (c.2 - c.1 + 1) *
          (ε ^ (c.2 - c.1) * ((K : ℝ) - c.2) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hfactor
      _ = (16 : ℝ) ^ (c.2 - c.1 + 1) * ε ^ (c.2 - c.1) *
          ((K : ℝ) - c.2) ^ (-2 : ℝ) := by ring
  calc
    _ ≤ ∑ c ∈ candidateComponentSpans r s,
        (16 : ℝ) ^ (c.2 - c.1 + 1) * ε ^ (c.2 - c.1) *
          ((K : ℝ) - c.2) ^ (-2 : ℝ) := Finset.sum_le_sum hterms
    _ ≤ 32 * q * (2 / ((K : ℝ) - s)) :=
      span_envelope_sum_le hKs hq hq0 hsmall (sum_endpoint_inv_sq_le hrs hKs)
    _ = 64 * q / ((K : ℝ) - s) := by ring

/-- The component-weight sum is bounded by a constant times `ε / (K - s)`, as used after equation (7.27). -/
theorem sum_prod_componentWeight_le :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∀ K r s : ℕ,
      1 ≤ r → r ≤ s → s < K →
      ∑ F ∈ (intervalFamilies r s).erase ∅, ∑ G ∈ (intervalFamilies r s).erase ∅,
          ∏ c ∈ pairComponents r s F G, componentWeight ε K F G c ≤
        C * ε / ((K : ℝ) - s) := by
  classical
  refine ⟨1 / 8192, 6000, by norm_num, by norm_num, ?_⟩
  intro ε hε hεsmall K r s hr hrs hKs
  let Fam := (intervalFamilies r s).erase ∅
  let Pair := Fam ×ˢ Fam
  let Datum := Σ _c : ℕ × ℕ, Finset (ℕ × ℕ) × Finset (ℕ × ℕ)
  let U : Finset Datum := componentChoiceUniverse r s
  let encode : (Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) → Finset Datum :=
    fun p => componentEncoding r s p.1 p.2
  let Image := Pair.image encode
  let q : ℝ := 16 * ε
  have hq : q = 16 * ε := rfl
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hsmall : q ≤ 1 / 2 := by dsimp [q]; nlinarith [hεsmall]
  have hDnat : 1 ≤ K - s := by omega
  have hD : (1 : ℝ) ≤ (K : ℝ) - s := by
    have hcast : ((K - s : ℕ) : ℝ) = (K : ℝ) - s := by
      exact_mod_cast Nat.cast_sub (by omega : s ≤ K)
    rw [← hcast]
    exact_mod_cast hDnat
  have hDpos : 0 < (K : ℝ) - s := lt_of_lt_of_le (by norm_num) hD
  let w : Datum → ℝ := fun d =>
    ε ^ (d.1.2 - d.1.1) * ((K : ℝ) - d.1.2) ^ (-(3 / 2 : ℝ))
  let actualWeight : Finset Datum → ℝ := fun D =>
    ∏ d ∈ D, componentDatumWeight ε K d
  let envelopeWeight : Finset Datum → ℝ := fun D => ∏ d ∈ D, w d
  let Allowed := U.filter (fun d => d.2.1.card + d.2.2.card ≠ 1)
  let singletonImage := Allowed.image (fun d => ({d} : Finset Datum))
  have hWnonneg : ∀ d ∈ U, 0 ≤ w d := by
    intro d hd
    have hcomp := componentDatumWeight_nonneg ε hε hKs hd
    have hupper := componentDatumWeight_le_envelope ε hε hKs hd
    exact hcomp.trans (by simpa [w] using hupper)
  let A : ℝ := ∑ d ∈ U, w d
  have hA0 : 0 ≤ A := Finset.sum_nonneg hWnonneg
  have hA_bound : A ≤ 256 * q / √((K : ℝ) - s) := by
    calc
      _ ≤ ∑ c ∈ candidateComponentSpans r s,
          (16 : ℝ) ^ (c.2 - c.1 + 1) * ε ^ (c.2 - c.1) *
            ((K : ℝ) - c.2) ^ (-(3 / 2 : ℝ)) := by
        simpa [A, U, w] using
          componentChoiceUniverse_envelope_sum_le_spans hr hKs ε hε
      _ ≤ 32 * q * (8 / √((K : ℝ) - s)) :=
        span_envelope_sum_le hKs hq hq0 hsmall
          (sum_endpoint_inv_three_halves_le hrs hKs)
      _ = 256 * q / √((K : ℝ) - s) := by ring
  have hsqrtD : 1 ≤ √((K : ℝ) - s) := Real.one_le_sqrt.mpr hD
  have hAhalf : A ≤ 1 / 2 := by
    have hcoef : 256 * q ≤ 1 / 2 := by dsimp [q]; nlinarith [hεsmall]
    have hdiv : (256 * q) / √((K : ℝ) - s) ≤ 256 * q := by
      rw [div_le_iff₀ (Real.sqrt_pos.2 hDpos)]
      nlinarith [hsqrtD, mul_nonneg (by positivity : 0 ≤ 256 * q)
        (sub_nonneg.mpr hsqrtD)]
    exact le_trans (hA_bound.trans hdiv) hcoef
  have hmulti :
      ∑ D ∈ U.powerset.filter (fun D => 2 ≤ D.card), envelopeWeight D ≤ 2 * A ^ 2 := by
    simpa [U, envelopeWeight, A] using
      sum_powerset_card_ge_two_le_two_sq U w hWnonneg (by simpa [A] using hAhalf)
  have hsumPair :
      (∑ F ∈ Fam, ∑ G ∈ Fam,
        ∏ c ∈ pairComponents r s F G, componentWeight ε K F G c) =
      ∑ p ∈ Pair,
        ∏ c ∈ pairComponents r s p.1 p.2, componentWeight ε K p.1 p.2 c := by
    dsimp [Pair]
    rw [← Finset.sum_product']
  have hencode_inj : Set.InjOn encode Pair := by
    intro p hp p' hp' heq
    rcases Finset.mem_product.mp hp with ⟨hpF, hpG⟩
    rcases Finset.mem_product.mp hp' with ⟨hpF', hpG'⟩
    have hF := (Finset.mem_erase.mp hpF).2
    have hG := (Finset.mem_erase.mp hpG).2
    have hF' := (Finset.mem_erase.mp hpF').2
    have hG' := (Finset.mem_erase.mp hpG').2
    rcases componentEncoding_injective hr hF hG hF' hG' heq with ⟨hleft, hright⟩
    exact Prod.ext hleft hright
  have hsumImage :
      (∑ p ∈ Pair,
        ∏ c ∈ pairComponents r s p.1 p.2, componentWeight ε K p.1 p.2 c) =
      ∑ D ∈ Image, actualWeight D := by
    calc
      _ = ∑ p ∈ Pair, actualWeight (encode p) := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa [actualWeight, encode] using
          (componentEncoding_prod_weight_eq ε K :
            ∏ d ∈ componentEncoding r s p.1 p.2, componentDatumWeight ε K d =
              ∏ c ∈ pairComponents r s p.1 p.2, componentWeight ε K p.1 p.2 c).symm
      _ = ∑ D ∈ Image, actualWeight D := (Finset.sum_image hencode_inj).symm
  have hImage_sub : Image ⊆ U.powerset := by
    intro D hDmem
    rcases Finset.mem_image.mp hDmem with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hpF, hpG⟩
    exact Finset.mem_powerset.mpr
      (componentEncoding_subset_universe (Finset.mem_erase.mp hpF).2
        (Finset.mem_erase.mp hpG).2)
  have hImage_card_pos : ∀ D ∈ Image, 1 ≤ D.card := by
    intro D hDmem
    rcases Finset.mem_image.mp hDmem with ⟨p, hp, hDenc⟩
    rcases Finset.mem_product.mp hp with ⟨hpF, hpG⟩
    have hF := (Finset.mem_erase.mp hpF).2
    have hG := (Finset.mem_erase.mp hpG).2
    have hFne : p.1.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hpF).1
    have hencne := componentEncoding_nonempty hr hF hG hFne
    have hpos : 0 < (encode p).card := by simpa [encode] using hencne.card_pos
    rw [hDenc] at hpos
    omega
  have hactual_le_envelope : ∀ D ∈ Image, actualWeight D ≤ envelopeWeight D := by
    intro D hDmem
    apply Finset.prod_le_prod₀
    · intro d hd
      exact componentDatumWeight_nonneg ε hε hKs
        ((Finset.mem_powerset.mp (hImage_sub hDmem)) hd)
    · intro d hd
      have hdU := (Finset.mem_powerset.mp (hImage_sub hDmem)) hd
      simpa [w] using componentDatumWeight_le_envelope ε hε hKs hdU
  have hhigh_bound :
      ∑ D ∈ Image.filter (fun D => 2 ≤ D.card), actualWeight D ≤ 2 * A ^ 2 := by
    have hsubset : Image.filter (fun D => 2 ≤ D.card) ⊆
        U.powerset.filter (fun D => 2 ≤ D.card) := by
      intro D hDmem
      rcases Finset.mem_filter.mp hDmem with ⟨hDin, hcard⟩
      exact Finset.mem_filter.mpr ⟨hImage_sub hDin, hcard⟩
    calc
      _ ≤ ∑ D ∈ Image.filter (fun D => 2 ≤ D.card), envelopeWeight D :=
        Finset.sum_le_sum fun D hDmem => hactual_le_envelope D
          (Finset.mem_filter.mp hDmem).1
      _ ≤ ∑ D ∈ U.powerset.filter (fun D => 2 ≤ D.card), envelopeWeight D :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro D hDmem hDnot
          have hsubD := Finset.mem_powerset.mp (Finset.mem_filter.mp hDmem).1
          exact Finset.prod_nonneg fun d hd => hWnonneg d (hsubD hd))
      _ ≤ 2 * A ^ 2 := hmulti
  have hlow_subset : Image.filter (fun D => ¬ 2 ≤ D.card) ⊆ singletonImage := by
    intro D hDmem
    rcases Finset.mem_filter.mp hDmem with ⟨hDin, hnotHigh⟩
    rcases Finset.mem_image.mp hDin with ⟨p, hp, hDenc⟩
    rcases Finset.mem_product.mp hp with ⟨hpF, hpG⟩
    have hF := (Finset.mem_erase.mp hpF).2
    have hG := (Finset.mem_erase.mp hpG).2
    have hFne : p.1.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hpF).1
    have hGne : p.2.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hpG).1
    have hEncne := componentEncoding_nonempty hr hF hG hFne
    have hcardD : D.card = 1 := by
      have hpos : 0 < (encode p).card := by simpa [encode] using hEncne.card_pos
      rw [hDenc] at hpos
      omega
    obtain ⟨d, hDsingle⟩ := Finset.card_eq_one.mp hcardD
    have hdD : d ∈ D := by rw [hDsingle]; simp
    have hdU : d ∈ U := Finset.mem_powerset.mp (hImage_sub hDin) hdD
    have hDenc' : componentEncoding r s p.1 p.2 = D := by simpa [encode] using hDenc
    have hleft : p.1 = d.2.1 := by
      calc
        p.1 = (componentEncoding r s p.1 p.2).biUnion (fun e => e.2.1) :=
          (componentEncoding_recover_left hr hF hG).symm
        _ = d.2.1 := by rw [hDenc', hDsingle]; simp
    have hright : p.2 = d.2.2 := by
      calc
        p.2 = (componentEncoding r s p.1 p.2).biUnion (fun e => e.2.2) :=
          (componentEncoding_recover_right hr hF hG).symm
        _ = d.2.2 := by rw [hDenc', hDsingle]; simp
    have hFlocal : d.2.1.Nonempty := hleft ▸ hFne
    have hGlocal : d.2.2.Nonempty := hright ▸ hGne
    have hnotOne : d.2.1.card + d.2.2.card ≠ 1 := by
      have hcardF : 1 ≤ d.2.1.card := Finset.one_le_card.mpr hFlocal
      have hcardG : 1 ≤ d.2.2.card := Finset.one_le_card.mpr hGlocal
      omega
    have hdAllowed : d ∈ Allowed := Finset.mem_filter.mpr ⟨hdU, hnotOne⟩
    exact Finset.mem_image.mpr ⟨d, hdAllowed, hDsingle.symm⟩
  have hsingleton_image_eq :
      ∑ D ∈ singletonImage, actualWeight D =
        ∑ d ∈ Allowed, componentDatumWeight ε K d := by
    symm
    calc
      ∑ d ∈ Allowed, componentDatumWeight ε K d =
          ∑ d ∈ Allowed, actualWeight ({d} : Finset Datum) := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [actualWeight]
      _ = ∑ D ∈ singletonImage, actualWeight D := by
        apply (Finset.sum_image ?_).symm
        intro d hd d' hd' heq
        exact Finset.singleton_injective heq
  have hlow_bound :
      ∑ D ∈ Image.filter (fun D => ¬ 2 ≤ D.card), actualWeight D ≤
        64 * q / ((K : ℝ) - s) := by
    calc
      _ ≤ ∑ D ∈ singletonImage, actualWeight D :=
        Finset.sum_le_sum_of_subset_of_nonneg hlow_subset (by
          intro D hDmem hDnot
          rcases Finset.mem_image.mp hDmem with ⟨d, hdAllowed, rfl⟩
          have hdU := (Finset.mem_filter.mp hdAllowed).1
          simp [actualWeight]
          exact componentDatumWeight_nonneg ε hε hKs hdU)
      _ = ∑ d ∈ Allowed, componentDatumWeight ε K d := hsingleton_image_eq
      _ ≤ 64 * q / ((K : ℝ) - s) := by
        simpa [Allowed, U] using
          componentChoiceUniverse_nonisolated_bound hr hrs hKs ε q hε hq hq0 hsmall
  have hImageBound :
      ∑ D ∈ Image, actualWeight D ≤ 2 * A ^ 2 + 64 * q / ((K : ℝ) - s) := by
    rw [← Finset.sum_filter_add_sum_filter_not Image (fun D => 2 ≤ D.card)]
    exact add_le_add hhigh_bound hlow_bound
  have hAlinear : A ≤ 4096 * ε / √((K : ℝ) - s) := by
    calc
      A ≤ 256 * q / √((K : ℝ) - s) := hA_bound
      _ = 4096 * ε / √((K : ℝ) - s) := by rw [hq]; ring
  have hA2 : 2 * A ^ 2 ≤ 4096 * ε / ((K : ℝ) - s) := by
    have hsquare := (sq_le_sq₀ hA0 (by positivity)).2 hAlinear
    have hroot : (√((K : ℝ) - s)) ^ 2 = (K : ℝ) - s := Real.sq_sqrt hDpos.le
    have hεsq : ε ^ 2 ≤ ε / 8192 := by
      calc
        ε ^ 2 = ε * ε := pow_two ε
        _ ≤ ε * (1 / 8192) := mul_le_mul_of_nonneg_left hεsmall hε
        _ = ε / 8192 := by ring
    calc
      2 * A ^ 2 ≤ 2 * (4096 * ε / √((K : ℝ) - s)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by norm_num)
      _ = (2 * 4096 ^ 2 * ε ^ 2) / ((K : ℝ) - s) := by
        rw [div_pow, hroot]
        ring
      _ ≤ 4096 * ε / ((K : ℝ) - s) := by
        apply div_le_div_of_nonneg_right _ hDpos.le
        linarith only [hεsq]
  have htotal : 2 * A ^ 2 + 64 * q / ((K : ℝ) - s) ≤
      6000 * ε / ((K : ℝ) - s) := by
    calc
      _ ≤ 4096 * ε / ((K : ℝ) - s) + 64 * q / ((K : ℝ) - s) :=
        by simpa [add_comm] using add_le_add_right hA2 (64 * q / ((K : ℝ) - s))
      _ = 5120 * ε / ((K : ℝ) - s) := by rw [hq]; ring
      _ ≤ 6000 * ε / ((K : ℝ) - s) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (5120 : ℝ) ≤ 6000) hε) hDpos.le
  calc
    _ = ∑ F ∈ Fam, ∑ G ∈ Fam,
        ∏ c ∈ pairComponents r s F G, componentWeight ε K F G c := rfl
    _ = ∑ D ∈ Image, actualWeight D := by
      rw [hsumPair]
      exact hsumImage
    _ ≤ 2 * A ^ 2 + 64 * q / ((K : ℝ) - s) := hImageBound
    _ ≤ 6000 * ε / ((K : ℝ) - s) := htotal

end Critical2DKPZ.OnePoint

end
