/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.InvUSCSuperlevelExact
import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler
/-! Actual global SAME-P canonical finite phases erase a compact INITIAL full
upper cut, allowing noncompact whole cosupport. No analytic threshold, desired
phase, stage compactness or count certificate is an input. General BM13.4 OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalCompactUpperCutGlobalPhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq ResolutionInvariantDriver ResolutionInvariantOrder
  ResolutionDriver CanonicalCentres StepOneLowerDomain
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
variable {n k : ℕ} {X Y : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- Literal SAME original full-invariant upper cut at a fixed old threshold. -/
def actualUpperCut (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ) : Set Y :=
  {z | z ∈ (geoTransformAlong m T).cosupp ∧ b ≤ R.inv m T z}

/-- Genuine original step drop composes along the actual canonical history. -/
theorem canonical_value_le_initial
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsCanonical m (R.inv m) T →
      ∀ z ∈ (geoTransformAlong m T).cosupp,
        R.inv m T z ≤ R.inv m (.refl : BlowupTower X X) (T.proj z)
  | _, .refl, _, _, _ => le_rfl
  | _, .step T C π hπ, hc, z, hz => by
    have hd := stepDrop_of_isInvValue R.isInvValue h T C π hπ hc z hz
    have hle : R.inv m (.step T C π hπ) z ≤ R.inv m T (π z) := by
      by_cases hp : π z ∈ C
      · exact (hd.2.1 hp).le
      · exact (hd.2.2 hp).le
    exact hle.trans (canonical_value_le_initial R m h T hc.1 (π z) hd.1)

/-- True closed current upper cuts lie in the genuine proper preimage of the
SAME compact INITIAL cut; the whole cosupport can remain noncompact. -/
theorem current_upper_cut_compact
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (b : Λ)
    (hK : IsCompact (actualUpperCut R m (.refl : BlowupTower X X) b))
    (T : BlowupTower X Y) (hc : IsCanonical m (R.inv m) T) :
    IsCompact (actualUpperCut R m T b) ∧
      actualUpperCut R m T b ⊆ T.proj ⁻¹' actualUpperCut R m (.refl : BlowupTower X X) b := by
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hw := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht).isWellFormed
  have hclosed := (R.isInvValue.usc m h T hc).isClosed_superlevel
    (GiraudAlong.isClosed_cosupport_along hw.isCoherent hw.isClosedSubmanifold_N _) b
  have hsub : actualUpperCut R m T b ⊆ T.proj ⁻¹' actualUpperCut R m (.refl : BlowupTower X X) b := by
    intro z hz
    exact ⟨proj_mem_cosupp_of_mem_cosupp h.isWellFormed.isClosedSubmanifold_N
      h.isWellFormed.isCoherent T ht hz.1,hz.2.trans (canonical_value_le_initial R m h T hc z hz.1)⟩
  exact ⟨((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hclosed hsub,hsub⟩

/-- Compactness of the real upper cut internally gives a REAL global maximum
and ENTIRE global maximum-locus containment in that cut. -/
theorem global_maximum_of_compact_upper_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (b : Λ)
    (hK : IsCompact (actualUpperCut R m (.refl : BlowupTower X X) b))
    (T : BlowupTower X Y) (hc : IsCanonical m (R.inv m) T)
    (hne : (actualUpperCut R m T b).Nonempty) :
    (maxLocus (R.inv m T) (geoTransformAlong m T).cosupp).Nonempty ∧
      maxLocus (R.inv m T) (geoTransformAlong m T).cosupp ⊆ actualUpperCut R m T b := by
  have hcompact := (current_upper_cut_compact R m h b hK T hc).1
  obtain ⟨x,hx,hmax⟩ := ((R.isInvValue.usc m h T hc).mono (fun _ hz => hz.1)).exists_isMaxOn hcompact hne
  have hglobal : ∀ y ∈ (geoTransformAlong m T).cosupp,R.inv m T y ≤ R.inv m T x := by
    intro y hy
    by_cases hb : b ≤ R.inv m T y
    · exact hmax y ⟨hy,hb⟩
    · exact (lt_of_not_ge hb).le.trans hx.2
  refine ⟨⟨x,hx.1,hglobal⟩,?_⟩
  intro y hy
  exact ⟨hy.1,hx.2.trans (hy.2 x hx.1)⟩

/-- Real global canonical maps are constructed before a SAME compact initial
upper-cut global centre count proves erasure at an actual finite prefix. -/
theorem exists_actual_compact_upper_cut_global_phase
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (b : Λ)
    (hK : IsCompact (actualUpperCut R m (.refl : BlowupTower X X) b)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsCanonical m (R.inv m) T ∧
      actualUpperCut R m T b=∅ ∧ ∀ z ∈ (geoTransformAlong m T).cosupp,R.inv m T z < b := by
  let A := {p : Σ Y : CMfd.{u} n,BlowupTower X Y // IsCanonical m (R.inv m) p.2}
  have hext : ∀ p : A,∃ q : A,∃ (C : Set p.1.1) (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n C π),q.1.2=.step p.1.2 C π hπ ∧
      C ⊆ actualUpperCut R m p.1.2 b ∧ ((actualUpperCut R m p.1.2 b).Nonempty → C.Nonempty) := by
    intro p
    have ht := R.isInvValue.isGeoTestTower_of_isCanonical h p.1.2 p.2
    by_cases hne : (actualUpperCut R m p.1.2 b).Nonempty
    · obtain ⟨hCne,hCsub⟩ := global_maximum_of_compact_upper_cut R m h b hK p.1.2 p.2 hne
      let C := maxLocus (R.inv m p.1.2) (geoTransformAlong m p.1.2).cosupp
      have hadm := R.isInvValue.isAdmissibleCentre_maxLocus h p.1.2 p.2 ht
      obtain ⟨Z,π,hπ⟩ := exists_blowup C hadm.1 (interior_maxLocus_eq_empty h p.1.2 ht _)
      exact ⟨⟨⟨Z,.step p.1.2 C π hπ⟩,p.2,Or.inr rfl⟩,C,π,hπ,rfl,hCsub,fun _ => hCne⟩
    · obtain ⟨Z,π,hπ⟩ := exists_blowup (∅ : Set p.1.1) (isAdmissibleCentre_empty (geoTransformAlong m p.1.2)).1
        interior_empty
      exact ⟨⟨⟨Z,.step p.1.2 ∅ π hπ⟩,p.2,Or.inl rfl⟩,∅,π,hπ,rfl,empty_subset _,fun hh => (hne hh).elim⟩
  choose next hnext using hext
  let a0 : A := ⟨⟨X,.refl⟩,trivial⟩
  let s : GrowingSeq X := GrowingSeq.ofIterate (fun p : A => p.1) next a0 rfl (fun p => by
    obtain ⟨C,π,hπ,he,_hsub,_hne⟩ := hnext p
    exact ⟨C,π,hπ,he⟩)
  have hcan : ∀ i,IsCanonical m (R.inv m) (s.stage i).2 := fun i => (next^[i] a0).2
  have hclear : ∃ i,actualUpperCut R m (s.stage i).2 b=∅ := by
    by_contra hno
    have hne : ∀ i,(actualUpperCut R m (s.stage i).2 b).Nonempty :=
      fun i => Set.nonempty_iff_ne_empty.mpr (fun he => hno ⟨i,he⟩)
    obtain ⟨bound,hbound⟩ := R.seqLocallyFinite m h (actualUpperCut R m (.refl : BlowupTower X X) b) hK s hcan
    have hcount : ∀ i,countCentresMeeting (actualUpperCut R m (.refl : BlowupTower X X) b) (s.stage i).2=i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        obtain ⟨C,π,hπ,he,hCsub,hCne⟩ := hnext (next^[i] a0)
        obtain ⟨x,hx⟩ := hCne (hne i)
        have hhit : (C ∩ (s.stage i).2.proj ⁻¹' actualUpperCut R m (.refl : BlowupTower X X) b).Nonempty :=
          ⟨x,hx,(current_upper_cut_compact R m h b hK (s.stage i).2 (hcan i)).2 (hCsub hx)⟩
        change countCentresMeeting _ (next^[i+1] a0).1.2=i+1
        rw [Function.iterate_succ_apply',he]
        have hhiti : (C ∩ (next^[i] a0).1.2.proj ⁻¹' actualUpperCut R m (.refl : BlowupTower X X) b).Nonempty := hhit
        have ihi : countCentresMeeting (actualUpperCut R m (.refl : BlowupTower X X) b) (next^[i] a0).1.2=i := ih
        simp only [countCentresMeeting,if_pos hhiti,ihi]
    have hh := hbound (bound+1)
    rw [hcount] at hh
    omega
  obtain ⟨i,hi⟩ := hclear
  refine ⟨(s.stage i).1,(s.stage i).2,hcan i,hi,?_⟩
  intro z hz
  apply lt_of_not_ge
  intro hb
  have hh : z ∈ actualUpperCut R m (s.stage i).2 b := ⟨hz,hb⟩
  rw [hi] at hh
  exact hh

/-- ONLY original all-depth marked data, a fixed actual threshold and compact
INITIAL literal cut supply a true GLOBAL canonical phase and whole strict bound. -/
theorem exists_original_compact_upper_cut_global_phase (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (b : ValTy d)
    (hK : IsCompact (actualUpperCut (invFamily hn d) m (.refl : BlowupTower X X) b)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical m ((invFamily hn d).inv m) T ∧ IsGeoTestTower m T ∧
      actualUpperCut (invFamily hn d) m T b=∅ ∧
      ∀ z ∈ (geoTransformAlong m T).cosupp,(invFamily hn d).inv m T z < b := by
  obtain ⟨Y,T,hc,hcut,hstrict⟩ := exists_actual_compact_upper_cut_global_phase (invFamily hn d) m h b hK
  exact ⟨Y,T,hc,(invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hc,hcut,hstrict⟩

end
end Hironaka.HironakaOriginalCompactUpperCutGlobalPhase
