/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsInitialFullMaximum

/-! # The actual canonicalInvariant n initial NC step

Whole-record transport is proved for any genuine resolution invariant with
its natural dimension bound. The specialization uses canonicalInvariant n
itself; no stability or equality between family depths n and n+1 is assumed.
Only the empty original history and its actual first blowup are constructed.
Blueprint: `hironaka-normal-crossings-canonical-initial-step-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaNormalCrossingsCanonicalInitialStep

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundarySeparation
  HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsTotalIdeal HironakaNormalCrossingsMarkedAdmissibility
  HironakaNormalCrossingsBiholomorphicMultiplicity HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsActualResidual BlowupFlatCoordinates BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres ResolutionInvariantSpec
  BlowupTowerIsomorphism MarkedIdealBiholomorphism HironakaNormalCrossingsInitialFullMaximum

noncomputable section
variable {n : ℕ} {A B : CMfd.{u} n}

private theorem original_domain {k : ℕ} (hnk : n ≤ k) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) : IsInvDomain k (originalMarkedIdeal H) := by
  have h := isInvDomain_originalMarkedIdeal hH
  refine ⟨h.isWellFormed,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨d,hd,hreg⟩ := h.dimLE x hx
  exact ⟨d,hd.trans hnk,hreg⟩

private theorem original_pullback_open {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (U : TopologicalSpace.Opens A) :
    MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H) =
      originalMarkedIdeal (A := CMfd.of (n := n) U) ((Subtype.val : U → A) ⁻¹' H) := by
  have hp := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U (boundaryAdapted_nil hH))
  have hc : (vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' H)).IsCoherent :=
    (isInvDomain_originalMarkedIdeal (A := CMfd.of (n := n) U) hp).isWellFormed.isCoherent
  have hi := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) H
  rw [BlowupControlledTransform.pullback_id hc] at hi
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H))
    (𝔫 := originalMarkedIdeal (A := CMfd.of (n := n) U) ((Subtype.val : U → A) ⁻¹' H)) rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) (Subtype.val : U → A) (vanishingIdeal (n := n) H) =
    vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' H)
  simpa only [Function.comp_id] using hi.symm

private theorem original_pullback_diffeomorph
    (χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    MarkedIdeal.pullback χ (originalMarkedIdeal H) = originalMarkedIdeal (χ ⁻¹' H) := by
  have hp := isNormalCrossingsCarrier_preimage χ.contMDiff
    (notMem_exceptionalLocus_of_inverse χ.contMDiff χ.symm.contMDiff
      χ.apply_symm_apply χ.symm_apply_apply) hH
  have hc : (vanishingIdeal (n := n) (χ ⁻¹' H)).IsCoherent :=
    (isInvDomain_originalMarkedIdeal hp).isWellFormed.isCoherent
  have hi := pullback_vanishingIdeal_preimage χ.contMDiff χ.symm.contMDiff
    χ.apply_symm_apply χ.symm_apply_apply (g := (id : B → B)) contMDiff_id H
  rw [BlowupControlledTransform.pullback_id hc] at hi
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := MarkedIdeal.pullback χ (originalMarkedIdeal H))
    (𝔫 := originalMarkedIdeal (χ ⁻¹' H)) rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) χ (vanishingIdeal (n := n) H) = vanishingIdeal (n := n) (χ ⁻¹' H)
  simpa only [Function.comp_id] using hi.symm

section Generic
variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- The entire original reflexive value of any proved invariant. -/
def initialValue (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (H : Set A) (x : A) : Λ := R.inv (originalMarkedIdeal H) .refl x

private theorem initialValue_open (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ) (hnk : n ≤ k) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (U : TopologicalSpace.Opens A)
    (x : U) (hx : (x : A) ∈ H) :
    initialValue (A := CMfd.of (n := n) U) R ((Subtype.val : U → A) ⁻¹' H) x =
      initialValue R H (x : A) := by
  have hcos : (originalMarkedIdeal H).cosupp = H :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
  have hv := R.isInvValue.restrictOpen
    (originalMarkedIdeal H) (original_domain hnk hH) U .refl trivial x
    (by simpa only [geoTransformAlong_refl,hcos] using hx)
  rw [original_pullback_open hH U] at hv
  exact hv

private theorem initialValue_diffeomorph (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ) (hnk : n ≤ k)
    (χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (x : B) (hx : χ x ∈ H) :
    initialValue R (χ ⁻¹' H) x = initialValue R H (χ x) := by
  have hcos : (originalMarkedIdeal H).cosupp = H :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
  have hv := R.isInvValue.towerIso χ
    (originalMarkedIdeal H) (original_domain hnk hH) .refl .refl χ .refl trivial x
    (by simpa only [geoTransformAlong_refl,hcos] using hx)
  rw [original_pullback_diffeomorph χ hH] at hv
  exact hv

/-- An actual centred NC flattening transports the ENTIRE value of the original
empty-history invariant to the genuine whole coordinate model at zero. -/
theorem initialValue_eq_coordinate_model (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ) (hnk : n ≤ k) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {x : A} (hx : x ∈ H)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (S : Finset (Fin n))
    (hflat : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) :
    initialValue R H x =
      initialValue (A := CMfd.of (n := n) (LiftedModel.{u} n)) R
        (coordinateCarrier S) (ULift.up (0 : ComplexModel n)) := by
  let U : TopologicalSpace.Opens A := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let T : TopologicalSpace.Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let χ := flatDomainDiffeomorph Φ hsrc
  let px : U := ⟨x,mem_flatDomain_self Φ⟩
  have hzT : (0 : ComplexModel n) ∈ T := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  let pz : LiftedOpen.{u} T := LiftedOpen.mk T 0 hzT
  have hχ : χ px = pz := by
    apply Subtype.ext
    apply ULift.ext
    exact h0
  have hpre : χ ⁻¹' ((Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' coordinateCarrier S) =
      (Subtype.val : U → A) ⁻¹' H := by
    ext p
    change (∃ i ∈ S, flatCoord Φ i (p : A) = 0) ↔ (p : A) ∈ H
    exact (hflat p p.2).symm
  have hmodel := coordinateCarrier_isNormalCrossings.{u} S
  have htrace := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_open (A := CMfd.of (n := n) (LiftedModel.{u} n))
      (liftedOpens T) (boundaryAdapted_nil hmodel))
  have hχmem : χ px ∈ (Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' coordinateCarrier S := by
    change px ∈ χ ⁻¹' ((Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' coordinateCarrier S)
    rw [hpre]
    exact hx
  have hvalue := initialValue_diffeomorph
    (A := CMfd.of (n := n) (LiftedOpen.{u} T)) (B := CMfd.of (n := n) U) R hnk χ htrace px hχmem
  rw [hpre,hχ] at hvalue
  have hmodelmem : (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n) ∈ coordinateCarrier S := by
    have hh := hχmem
    rw [hχ] at hh
    exact hh
  exact (initialValue_open R hnk hH U px hx).symm.trans
    (hvalue.trans (initialValue_open (A := CMfd.of (n := n) (LiftedModel.{u} n))
      R hnk hmodel (liftedOpens T) pz hmodelmem))

/-- At the actual highest original count, genuine normalized charts compare
the WHOLE initial values through one identical last-coordinate NC model. -/
theorem initialValue_eq_of_highest_branch_count (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ) (hnk : n ≤ k) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ z : A, branchMultiplicity hH z ≤ r) {x y : A}
    (hx : r ≤ branchMultiplicity hH x) (hy : r ≤ branchMultiplicity hH y) :
    initialValue R H x = initialValue R H y := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => n-r ≤ i.val)
  obtain ⟨Φ,hsrc,h0,_,hflat⟩ := exists_highest_stratum_branch_adapted_coordinates hH hbound hx
  obtain ⟨Ψ,hsrc',h0',_,hflat'⟩ := exists_highest_stratum_branch_adapted_coordinates hH hbound hy
  have hxH := (branchMultiplicity_pos_iff hH x).mp (hr.trans_le hx)
  have hyH := (branchMultiplicity_pos_iff hH y).mp (hr.trans_le hy)
  have hΦ : ∀ z ∈ flatDomain Φ, z ∈ H ↔ ∃ i ∈ S, flatCoord Φ i z = 0 := by
    intro z hz
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hflat z hz
  have hΨ : ∀ z ∈ flatDomain Ψ, z ∈ H ↔ ∃ i ∈ S, flatCoord Ψ i z = 0 := by
    intro z hz
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hflat' z hz
  exact (initialValue_eq_coordinate_model R hnk hH hxH Φ hsrc h0 S hΦ).trans
    (initialValue_eq_coordinate_model R hnk hH hyH Ψ hsrc' h0' S hΨ).symm

end Generic

/-- The actual ambient-dimensional invariant at the original reflexive history. -/
def canonicalInitialValue (H : Set A) (x : A) : ValTy n :=
  (canonicalInvariant n).inv (originalMarkedIdeal H) .refl x

private theorem branchMultiplicity_congr {H K : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hK : IsNormalCrossingsCarrier (n := n) K)
    (heq : H = K) (x : A) : branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

private theorem initial_nmOrd (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (x : A) :
    NonmonomialOrderLocal.nmOrd (originalMarkedIdeal H) x = branchMultiplicity hH x := by
  have hp := isNormalCrossingsCarrier_of_boundaryAdapted
    (HironakaNormalCrossingsOriginalExponents.higherSeparationCentres_pair hH
      (.refl : BlowupTower A A) trivial)
  have hs : strictTransform n (id : A → A) H = H := by
    simp [strictTransform,exceptionalLocus_id,hH.1.closure_eq]
  have hv := higherSeparationCentres_nmOrd hn hH (.refl : BlowupTower A A) trivial x
  change NonmonomialOrderLocal.nmOrd (originalMarkedIdeal H) x = branchMultiplicity hp x at hv
  exact hv.trans (branchMultiplicity_congr hp hH hs x)

/-- The first entry of canonicalInvariant n itself strictly orders distinct
original branch counts in positive ambient dimension. -/
theorem canonicalInitialValue_lt_of_branch_count_lt (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {x y : A}
    (hlt : branchMultiplicity hH x < branchMultiplicity hH y) :
    canonicalInitialValue H x < canonicalInitialValue H y := by
  cases n with
  | zero => omega
  | succ m =>
    have hfirst (z : A) : (ofLex (canonicalInitialValue H z)).1 = branchMultiplicity hH z := by
      change NonmonomialOrderLocal.nmOrd (geoTransformAlong (originalMarkedIdeal H) .refl) z = _
      exact initial_nmOrd (Nat.succ_pos m) hH z
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl (((hfirst x).trans_lt hlt).trans_eq (hfirst y).symm)

/-- Whole actual ambient-dimensional canonical maximum, at the initial original
history. It is not an identification at later prefixes. -/
theorem canonicalInitialMaximum_eq_highest_stratum (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ x : A, branchMultiplicity hH x ≤ r)
    (hatt : {x | r ≤ branchMultiplicity hH x}.Nonempty) :
    ResolutionDriver.maxLocus (canonicalInitialValue H) (originalMarkedIdeal H).cosupp =
      {x | r ≤ branchMultiplicity hH x} := by
  have hcos : (originalMarkedIdeal H).cosupp = H :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
  obtain ⟨a,ha⟩ := hatt
  have haH := (branchMultiplicity_pos_iff hH a).mp (hr.trans_le ha)
  rw [hcos]
  ext x
  change (x ∈ H ∧ ∀ y ∈ H, canonicalInitialValue H y ≤ canonicalInitialValue H x) ↔
    r ≤ branchMultiplicity hH x
  constructor
  · rintro ⟨_,hmax⟩
    by_contra hx
    have hlt := canonicalInitialValue_lt_of_branch_count_lt hn hH
      ((Nat.lt_of_not_ge hx).trans_le ha)
    exact (not_lt_of_ge (hmax a haH)) hlt
  · intro hx
    refine ⟨(branchMultiplicity_pos_iff hH x).mp (hr.trans_le hx),fun y _hy => ?_⟩
    by_cases hy : r ≤ branchMultiplicity hH y
    · exact le_of_eq (initialValue_eq_of_highest_branch_count (canonicalInvariant n)
        (Nat.le_refl n) hH hr hbound hy hx)
    · exact (canonicalInitialValue_lt_of_branch_count_lt hn hH
        ((Nat.lt_of_not_ge hy).trans_le hx)).le

/-- ONLY the nonempty original NC carrier produces an actual first test blowup
canonical for canonicalInvariant n itself, with no maximum/history certificate. -/
theorem exists_canonicalInvariant_initial_blowup (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hne : H.Nonempty) :
    ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ (∀ x : A, branchMultiplicity hH x ≤ r) ∧
      {x | r ≤ branchMultiplicity hH x}.Nonempty ∧
      {x | r ≤ branchMultiplicity hH x} =
        ResolutionDriver.maxLocus (canonicalInitialValue H) (originalMarkedIdeal H).cosupp ∧
      ∃ D : CMfd.{u} n, ∃ π : D → A,
        ∃ hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π,
          IsGeoTestTower (originalMarkedIdeal H) (.step .refl _ π hπ) ∧
          IsCanonical (originalMarkedIdeal H) ((canonicalInvariant n).inv (originalMarkedIdeal H))
            (.step .refl _ π hπ) := by
  obtain ⟨r,hr,hrn,hbound,hatt,_,_,_⟩ := exists_highest_multiplicity_stratum hH hne
  have hatt' : {x | r ≤ branchMultiplicity hH x}.Nonempty := by
    obtain ⟨x,hx⟩ := hatt
    exact ⟨x,hx.ge⟩
  have hmax := (canonicalInitialMaximum_eq_highest_stratum hn hH hr hbound hatt').symm
  obtain ⟨D,hDtop,hDchart,hDcm,π,hπ⟩ := exists_highest_stratum_blowup hH hr hbound
  let := hDtop
  let := hDchart
  let := hDcm
  have hadm : (originalMarkedIdeal H).IsAdmissibleCentre {x | r ≤ branchMultiplicity hH x} := by
    rw [hmax]
    exact (canonicalInvariant n).isInvValue.isAdmissibleCentre_maxLocus
      (original_domain (Nat.le_refl n) hH) .refl trivial trivial
  exact ⟨r,hr,hrn,hbound,hatt',hmax,CMfd.of (n := n) D,π,hπ,
    ⟨trivial,hadm⟩,⟨trivial,Or.inr hmax⟩⟩

end
end Hironaka.HironakaNormalCrossingsCanonicalInitialStep
