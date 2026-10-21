/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCompactUpperCutGlobalPhase
import Hironaka.Resolution.HironakaOriginalGlobalSequencePrefixSplice
/-! Genuine global compact-CURRENT-cut phases after ANY actual original canonical
prefix. Entire original history/invariant retained; actual prefix splicing applies
ORIGINAL sequence finiteness, without rebasing or caller phase/bound certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalCurrentCompactCutGlobalTailPhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq ResolutionInvariantDriver ResolutionInvariantOrder
  ResolutionDriver CanonicalCentres StepOneLowerDomain
  HironakaOriginalCompactUpperCutGlobalPhase HironakaOriginalGlobalSequencePrefixSplice
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
variable {n k : ℕ} {X Y Z : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- Genuine original whole-value nonincrease relative to the retained ACTUAL
prefix; the invariant is not replaced by that of its current marked record. -/
theorem canonical_value_le_prefix
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),IsCanonical m (R.inv m) (T.append S) →
      ∀ z ∈ (geoTransformAlong m (T.append S)).cosupp,
        R.inv m (T.append S) z ≤ R.inv m T (S.proj z)
  | _, .refl, _, _, _ => le_rfl
  | _, .step S C π hπ, hc, z, hz => by
    have hd := stepDrop_of_isInvValue R.isInvValue h (T.append S) C π hπ hc z hz
    have hle : R.inv m (T.append (.step S C π hπ)) z ≤ R.inv m (T.append S) (π z) := by
      by_cases hp : π z ∈ C
      · exact (hd.2.1 hp).le
      · exact (hd.2.2 hp).le
    exact hle.trans (canonical_value_le_prefix R m h T S hc.1 (π z) hd.1)

/-- True closed later cuts lie in the actual proper TAIL preimage of the
CURRENT compact cut, not an assumed compact initial original set. -/
theorem current_tail_cut_compact
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y)
    (hcT : IsCanonical m (R.inv m) T) (b : Λ) (hK : IsCompact (actualUpperCut R m T b))
    (S : BlowupTower Y Z) (hc : IsCanonical m (R.inv m) (T.append S)) :
    IsCompact (actualUpperCut R m (T.append S) b) ∧
      actualUpperCut R m (T.append S) b ⊆ S.proj ⁻¹' actualUpperCut R m T b := by
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical h T hcT
  have htApp := R.isInvValue.isGeoTestTower_of_isCanonical h (T.append S) hc
  have htS := ((isGeoTestTower_append_iff m T S).mp htApp).2
  have hwT := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht).isWellFormed
  have hw := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h (T.append S) htApp).isWellFormed
  have hclosed := (R.isInvValue.usc m h (T.append S) hc).isClosed_superlevel
    (GiraudAlong.isClosed_cosupport_along hw.isCoherent hw.isClosedSubmanifold_N _) b
  have hsub : actualUpperCut R m (T.append S) b ⊆ S.proj ⁻¹' actualUpperCut R m T b := by
    intro z hz
    have hzS : z ∈ (geoTransformAlong (geoTransformAlong m T) S).cosupp := by
      simpa only [geoTransformAlong_append] using hz.1
    exact ⟨proj_mem_cosupp_of_mem_cosupp hwT.isClosedSubmanifold_N hwT.isCoherent S htS hzS,
      hz.2.trans (canonical_value_le_prefix R m h T S hc z hz.1)⟩
  exact ⟨((HironakaLocalPrincipalization.isProperMap_proj S).isCompact_preimage hK).of_isClosed_subset
    hclosed hsub,hsub⟩

private theorem actual_global_maximum_of_tail_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y)
    (hcT : IsCanonical m (R.inv m) T) (b : Λ) (hK : IsCompact (actualUpperCut R m T b))
    (S : BlowupTower Y Z) (hc : IsCanonical m (R.inv m) (T.append S))
    (hne : (actualUpperCut R m (T.append S) b).Nonempty) :
    (maxLocus (R.inv m (T.append S)) (geoTransformAlong m (T.append S)).cosupp).Nonempty ∧
      maxLocus (R.inv m (T.append S)) (geoTransformAlong m (T.append S)).cosupp ⊆
        actualUpperCut R m (T.append S) b := by
  have hcompact := (current_tail_cut_compact R m h T hcT b hK S hc).1
  obtain ⟨x,hx,hmax⟩ := ((R.isInvValue.usc m h (T.append S) hc).mono (fun _ hz => hz.1)).exists_isMaxOn hcompact hne
  have hglobal : ∀ y ∈ (geoTransformAlong m (T.append S)).cosupp,
      R.inv m (T.append S) y ≤ R.inv m (T.append S) x := by
    intro y hy
    by_cases hb : b ≤ R.inv m (T.append S) y
    · exact hmax y ⟨hy,hb⟩
    · exact (lt_of_not_ge hb).le.trans hx.2
  exact ⟨⟨x,hx.1,hglobal⟩,fun _ hy => ⟨hy.1,hx.2.trans (hy.2 x hx.1)⟩⟩

/-- Actual GLOBAL continuation after the real original prefix: SAME original
invariant, compact CURRENT cut, genuine spliced sequence, real count increment. -/
theorem exists_actual_current_compact_cut_global_tail_phase
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y)
    (hcT : IsCanonical m (R.inv m) T) (b : Λ) (hK : IsCompact (actualUpperCut R m T b)) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),IsCanonical m (R.inv m) (T.append S) ∧
      actualUpperCut R m (T.append S) b=∅ ∧
      ∀ z ∈ (geoTransformAlong m (T.append S)).cosupp,R.inv m (T.append S) z < b := by
  let A := {p : Σ Z : CMfd.{u} n,BlowupTower Y Z // IsCanonical m (R.inv m) (T.append p.2)}
  have hext : ∀ p : A,∃ q : A,∃ (C : Set p.1.1) (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n C π),q.1.2=.step p.1.2 C π hπ ∧
      C ⊆ actualUpperCut R m (T.append p.1.2) b ∧
        ((actualUpperCut R m (T.append p.1.2) b).Nonempty → C.Nonempty) := by
    intro p
    have ht := R.isInvValue.isGeoTestTower_of_isCanonical h (T.append p.1.2) p.2
    by_cases hne : (actualUpperCut R m (T.append p.1.2) b).Nonempty
    · obtain ⟨hCne,hCsub⟩ := actual_global_maximum_of_tail_cut R m h T hcT b hK p.1.2 p.2 hne
      let C := maxLocus (R.inv m (T.append p.1.2)) (geoTransformAlong m (T.append p.1.2)).cosupp
      have hadm := R.isInvValue.isAdmissibleCentre_maxLocus h (T.append p.1.2) p.2 ht
      obtain ⟨Z,π,hπ⟩ := exists_blowup C hadm.1 (interior_maxLocus_eq_empty h (T.append p.1.2) ht _)
      exact ⟨⟨⟨Z,.step p.1.2 C π hπ⟩,p.2,Or.inr rfl⟩,C,π,hπ,rfl,hCsub,fun _ => hCne⟩
    · obtain ⟨Z,π,hπ⟩ := exists_blowup (∅ : Set p.1.1)
        (isAdmissibleCentre_empty (geoTransformAlong m (T.append p.1.2))).1 interior_empty
      exact ⟨⟨⟨Z,.step p.1.2 ∅ π hπ⟩,p.2,Or.inl rfl⟩,∅,π,hπ,rfl,empty_subset _,fun hh => (hne hh).elim⟩
  choose next hnext using hext
  let a0 : A := ⟨⟨Y,.refl⟩,hcT⟩
  let s : GrowingSeq Y := GrowingSeq.ofIterate (fun p : A => p.1) next a0 rfl (fun p => by
    obtain ⟨C,π,hπ,he,_hsub,_hne⟩ := hnext p
    exact ⟨C,π,hπ,he⟩)
  have hcan : ∀ i,IsCanonical m (R.inv m) (T.append (s.stage i).2) := fun i => (next^[i] a0).2
  let full := prependTower T s
  have hfull : ∀ i,IsCanonical m (R.inv m) (full.stage i).2 := prependTower_canonical m (R.inv m) T s hcT hcan
  let L : Set X := T.proj '' actualUpperCut R m T b
  have hL : IsCompact L := hK.image T.contMDiff_proj.continuous
  have hclear : ∃ i,actualUpperCut R m (T.append (s.stage i).2) b=∅ := by
    by_contra hno
    have hne : ∀ i,(actualUpperCut R m (T.append (s.stage i).2) b).Nonempty :=
      fun i => Set.nonempty_iff_ne_empty.mpr (fun he => hno ⟨i,he⟩)
    obtain ⟨bound,hbound⟩ := R.seqLocallyFinite m h L hL full hfull
    have hcount : ∀ i,countCentresMeeting L (T.append (s.stage i).2)=countCentresMeeting L T+i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        obtain ⟨C,π,hπ,he,hCsub,hCne⟩ := hnext (next^[i] a0)
        obtain ⟨x,hx⟩ := hCne (hne i)
        have hxK := (current_tail_cut_compact R m h T hcT b hK (s.stage i).2 (hcan i)).2 (hCsub hx)
        have hhit : (C ∩ (T.append (next^[i] a0).1.2).proj ⁻¹' L).Nonempty := by
          refine ⟨x,hx,?_⟩
          change (T.append (s.stage i).2).proj x ∈ T.proj '' actualUpperCut R m T b
          rw [BlowupTower.proj_append]
          exact ⟨(s.stage i).2.proj x,hxK,rfl⟩
        have ihi : countCentresMeeting L (T.append (next^[i] a0).1.2)=countCentresMeeting L T+i := ih
        change countCentresMeeting L (T.append (next^[i+1] a0).1.2)=countCentresMeeting L T+(i+1)
        rw [Function.iterate_succ_apply',he,BlowupTower.append_step]
        simp only [countCentresMeeting,if_pos hhit,ihi]
        omega
    have hh := hbound (T.length+(bound+1))
    have hstage : countCentresMeeting L (full.stage (T.length+(bound+1))).2=
        countCentresMeeting L (T.append (s.stage (bound+1)).2) :=
      congrArg (fun p : Σ Z : CMfd.{u} n,BlowupTower X Z => countCentresMeeting L p.2)
        (prependTower_stage_length_add T s (bound+1))
    rw [hstage,hcount] at hh
    omega
  obtain ⟨i,hi⟩ := hclear
  refine ⟨(s.stage i).1,(s.stage i).2,hcan i,hi,?_⟩
  intro z hz
  apply lt_of_not_ge
  intro hb
  have hh : z ∈ actualUpperCut R m (T.append (s.stage i).2) b := ⟨hz,hb⟩
  rw [hi] at hh
  exact hh

/-- ONLY original all-depth data, actual original canonical prefix and true
compact CURRENT cut internally construct a genuine GLOBAL SAME-P continuation. -/
theorem exists_original_current_compact_cut_global_tail_phase (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hcT : IsCanonical m ((invFamily hn d).inv m) T) (b : ValTy d)
    (hK : IsCompact (actualUpperCut (invFamily hn d) m T b)) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
      IsCanonical m ((invFamily hn d).inv m) (T.append S) ∧ IsGeoTestTower m (T.append S) ∧
      actualUpperCut (invFamily hn d) m (T.append S) b=∅ ∧
      ∀ z ∈ (geoTransformAlong m (T.append S)).cosupp,(invFamily hn d).inv m (T.append S) z < b := by
  obtain ⟨Z,S,hc,hcut,hstrict⟩ := exists_actual_current_compact_cut_global_tail_phase (invFamily hn d) m h T hcT b hK
  exact ⟨Z,S,hc,(invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h (T.append S) hc,hcut,hstrict⟩

end
end Hironaka.HironakaOriginalCurrentCompactCutGlobalTailPhase
