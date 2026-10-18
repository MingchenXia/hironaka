/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaLocalPrincipalization
/-! Actual global canonical sequences/terminal histories from original domain
and compact INITIAL cosupport, allowing noncompact ambient and carrier.
General noncompact-cosupport scheduling/arbitrary thresholds remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalCompactCosupportGlobalScheduler
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq ResolutionInvariantDriver ResolutionInvariantOrder
  ResolutionDriver CanonicalCentres StepOneLowerDomain
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
variable {n k : ℕ} {X Y : CMfd.{u} n}

/-- Actual closed current cosupport inside the true proper preimage of the
SAME compact INITIAL cosupport; no stage compactness is supplied. -/
theorem current_cosupport_compact (m : MarkedIdeal n X) (h : IsInvDomain k m)
    (hK : IsCompact m.cosupp) (T : BlowupTower X Y) (hT : IsGeoTestTower m T) :
    IsCompact (geoTransformAlong m T).cosupp ∧
      (geoTransformAlong m T).cosupp ⊆ T.proj ⁻¹' m.cosupp := by
  have hw := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
  have hclosed := GiraudAlong.isClosed_cosupport_along hw.isCoherent hw.isClosedSubmanifold_N
    (geoTransformAlong m T).d
  have hsub : (geoTransformAlong m T).cosupp ⊆ T.proj ⁻¹' m.cosupp :=
    fun _ hz => proj_mem_cosupp_of_mem_cosupp h.isWellFormed.isClosedSubmanifold_N
      h.isWellFormed.isCoherent T hT hz
  exact ⟨((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hclosed hsub,hsub⟩

variable {Λ : Type v} [LinearOrder Λ]

/-- Actual global centres/maps are selected and iterated BEFORE any terminal
history or numerical bound is known. -/
theorem exists_actual_global_canonical_sequence
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (hK : IsCompact m.cosupp) :
    ∃ s : GrowingSeq X,
      (∀ i,IsCanonical m (R.inv m) (s.stage i).2) ∧
      (∀ i,∃ (C : Set (s.stage i).1) (π : (s.stage (i+1)).1 → (s.stage i).1)
        (hπ : IsBlowupAlong n C π),
        (s.stage (i+1)).2=.step (s.stage i).2 C π hπ ∧
        C=maxLocus (R.inv m (s.stage i).2) (geoTransformAlong m (s.stage i).2).cosupp) ∧
      ∃ N,∀ i,N ≤ i → IsGeoResolution m (s.stage i).2 := by
  let A := {p : Σ Y : CMfd.{u} n,BlowupTower X Y // IsCanonical m (R.inv m) p.2}
  have hext : ∀ p : A,∃ q : A,∃ (C : Set p.1.1) (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n C π),q.1.2=.step p.1.2 C π hπ ∧
      C=maxLocus (R.inv m p.1.2) (geoTransformAlong m p.1.2).cosupp := by
    intro p
    have ht := R.isInvValue.isGeoTestTower_of_isCanonical h p.1.2 p.2
    let C := maxLocus (R.inv m p.1.2) (geoTransformAlong m p.1.2).cosupp
    have hadm := R.isInvValue.isAdmissibleCentre_maxLocus h p.1.2 p.2 ht
    obtain ⟨Z,π,hπ⟩ := exists_blowup C hadm.1 (interior_maxLocus_eq_empty h p.1.2 ht _)
    exact ⟨⟨⟨Z,.step p.1.2 C π hπ⟩,p.2,Or.inr rfl⟩,C,π,hπ,rfl,rfl⟩
  choose next hnext using hext
  let a0 : A := ⟨⟨X,.refl⟩,trivial⟩
  let s : GrowingSeq X := GrowingSeq.ofIterate (fun p : A => p.1) next a0 rfl (fun p => by
    obtain ⟨C,π,hπ,he,_hC⟩ := hnext p
    exact ⟨C,π,hπ,he⟩)
  have hcan : ∀ i,IsCanonical m (R.inv m) (s.stage i).2 := fun i => (next^[i] a0).2
  have hmaps : ∀ i,∃ (C : Set (s.stage i).1) (π : (s.stage (i+1)).1 → (s.stage i).1)
      (hπ : IsBlowupAlong n C π),(s.stage (i+1)).2=.step (s.stage i).2 C π hπ ∧
      C=maxLocus (R.inv m (s.stage i).2) (geoTransformAlong m (s.stage i).2).cosupp := by
    intro i
    change ∃ (C : Set (next^[i] a0).1.1) (π : (next^[i+1] a0).1.1 → (next^[i] a0).1.1)
      (hπ : IsBlowupAlong n C π),(next^[i+1] a0).1.2=.step (next^[i] a0).1.2 C π hπ ∧ _
    rw [Function.iterate_succ_apply']
    exact hnext (next^[i] a0)
  have hterminal : ∃ N,(geoTransformAlong m (s.stage N).2).cosupp=∅ := by
    by_contra hno
    have hne : ∀ i,(geoTransformAlong m (s.stage i).2).cosupp.Nonempty := by
      intro i
      exact Set.nonempty_iff_ne_empty.mpr (fun he => hno ⟨i,he⟩)
    obtain ⟨bound,hbound⟩ := R.seqLocallyFinite m h m.cosupp hK s hcan
    have hcount : ∀ i,countCentresMeeting m.cosupp (s.stage i).2=i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        obtain ⟨C,π,hπ,he,hC⟩ := hmaps i
        have ht := R.isInvValue.isGeoTestTower_of_isCanonical h (s.stage i).2 (hcan i)
        obtain ⟨hcompact,hsub⟩ := current_cosupport_compact m h hK (s.stage i).2 ht
        obtain ⟨x,hx,hmax⟩ := (R.isInvValue.usc m h _ (hcan i)).exists_isMaxOn hcompact (hne i)
        have hhit : (C ∩ (s.stage i).2.proj ⁻¹' m.cosupp).Nonempty :=
          ⟨x,hC.symm ▸ ⟨hx,hmax⟩,hsub hx⟩
        rw [he]
        simp only [countCentresMeeting,if_pos hhit,ih]
    have hh := hbound (bound+1)
    rw [hcount] at hh
    omega
  obtain ⟨N,hN⟩ := hterminal
  have htail : ∀ j,(geoTransformAlong m (s.stage (N+j)).2).cosupp=∅ := by
    intro j
    induction j with
    | zero => exact hN
    | succ j ih =>
      rw [← Nat.add_assoc]
      obtain ⟨C,π,hπ,he,_hC⟩ := hmaps (N+j)
      have ht := R.isInvValue.isGeoTestTower_of_isCanonical h (s.stage (N+j)).2 (hcan (N+j))
      have hnxt := R.isInvValue.isGeoTestTower_of_isCanonical h (s.stage (N+j+1)).2 (hcan (N+j+1))
      rw [he] at hnxt
      have hadm := ((isGeoTestTower_step_iff m (s.stage (N+j)).2 C π hπ).mp hnxt).2
      have hw := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h (s.stage (N+j)).2 ht).isWellFormed
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz' : z ∈ (geoTransformAlong (geoTransformAlong m (s.stage (N+j)).2)
          (.step .refl C π hπ)).cosupp := by
        change z ∈ (geoTransform (geoTransformAlong m (s.stage (N+j)).2) C π).cosupp
        simpa only [he,geoTransformAlong_step] using hz
      have hh := proj_mem_cosupp_of_mem_cosupp hw.isClosedSubmanifold_N hw.isCoherent
        (.step .refl C π hπ) ⟨trivial,hadm⟩ hz'
      rw [ih] at hh
      exact hh
  refine ⟨s,hcan,hmaps,N,?_⟩
  intro i hi
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
  exact ⟨R.isInvValue.isGeoTestTower_of_isCanonical h _ (hcan _),htail j⟩

/-- ONLY original all-depth inputs supply all actual global stages, maximum
centres/maps and eventual terminal histories on the original ambient. -/
theorem exists_original_compact_cosupport_global_sequence (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (hK : IsCompact m.cosupp) :
    ∃ s : GrowingSeq X,
      (∀ i,IsCanonical m ((invFamily hn d).inv m) (s.stage i).2) ∧
      (∀ i,∃ (C : Set (s.stage i).1) (π : (s.stage (i+1)).1 → (s.stage i).1)
        (hπ : IsBlowupAlong n C π),(s.stage (i+1)).2=.step (s.stage i).2 C π hπ ∧
        C=maxLocus ((invFamily hn d).inv m (s.stage i).2) (geoTransformAlong m (s.stage i).2).cosupp) ∧
      ∃ N,∀ i,N ≤ i → IsGeoResolution m (s.stage i).2 :=
  exists_actual_global_canonical_sequence (invFamily hn d) m h hK

/-- A genuine finite GLOBAL SAME-P terminal tower, without CompactSpace X/N. -/
theorem exists_original_compact_cosupport_terminal_tower (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (hK : IsCompact m.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical m ((invFamily hn d).inv m) T ∧ IsGeoResolution m T := by
  obtain ⟨s,hcan,_hmaps,N,hres⟩ := exists_original_compact_cosupport_global_sequence hn d m h hK
  exact ⟨(s.stage N).1,(s.stage N).2,hcan N,hres N le_rfl⟩

end
end Hironaka.HironakaOriginalCompactCosupportGlobalScheduler
