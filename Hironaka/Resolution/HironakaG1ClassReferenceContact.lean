import Hironaka.Resolution.HironakaG8MemberLocalRelation
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.InvDomainTowerAlong

/-! A genuine contact of an actual class reference gives full local
coefficient equivalence. No literal tangent-ideal transfer is asserted.
Blueprint FIRST: hironaka-g1-class-reference-contact.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ClassReferenceContact
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealEquivalence.MarkedIdeal
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  HironakaG8MemberLocalRelation HironakaG8ContactMax HironakaG8LocalHistory HironakaG8LocalStable
  ResolutionInvariantSpec TangentDirectionAlong ContactEquivalenceAlong
open HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open scoped ProductComplexManifold

/-- Internal coinduction data. The actual reference retains its own genuine
contact; the source retains its entire member/coefficient family. -/
def ReferenceContactRel {m : ℕ} {Y : CMfd.{0} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ (R : MarkedIdeal m Y) (F : ℕ → MarkedIdeal m Y) (S : Set Y),
    LocWPEquiv P R ∧ IsClosedSubmanifold m R.N ∧ R.ideal.IsCoherent ∧ 1 ≤ R.d ∧
      P.N = R.N ∧ MaxContact R S ∧ MemberRel P Q F S

private theorem reference_cosupp_eq {m : ℕ} {Y : CMfd.{0} m} {P Q : MarkedIdeal m Y}
    (h : ReferenceContactRel P Q) : P.cosupp = Q.cosupp := by
  obtain ⟨R, F, S, hL, _hN, hI, hd, _hNR, hContact, hM⟩ := h
  have hSub : P.cosupp ⊆ S := fun x hx => hContact.cosupp_subset hI hd (hL.cosupp_eq_base ▸ hx)
  rw [← hM.cosupp_eq]
  exact (Set.inter_eq_left.mpr hSub).symm

/-- The actual class-reference contact relation survives every action of
the full original local weak projection test class. -/
theorem isLocStable_referenceContact :
    IsLocStable.{0} Kinds.wp (fun {m} {Y} P Q => ReferenceContactRel (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨R, F, S, _hL, _hN, _hI, _hd, _hNR, _hContact, hM⟩
    exact hM.E_eq
  cosupp_eq := by
    intro m Y P Q h
    exact reference_cosupp_eq h
  controlled := by
    rintro m Y P Q ⟨R, F, S, hL, hN, hI, hd, hNR, hContact, hM⟩ C Z π hπ hC
    have hCR : R.IsAdmissibleCentre C :=
      (HironakaG8MixedEquiv.isAdmissibleCentre_congr hL.E_eq.symm hL.cosupp_eq_base C).mp hC
    have hCS : C ⊆ S := fun x hx => hContact.cosupp_subset hI hd (hL.cosupp_eq_base ▸ hC.2.1 hx)
    have hSR : S ⊆ R.N := by rw [← hNR]; exact hM.SN
    refine ⟨R.geoTransform C π, fun i => (F i).geoTransform C π,
      BlowupStrictSubmanifold.geoStrictTransform π C S,
      (isLocStable_locEquiv Kinds.wp).controlled hL C π hπ hC,
      isClosedSubmanifold_geoTransform_N hN hCR hπ,
      HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hI hCR hπ,
      hd, ?_, maxContact_geoTransform hN hI hd hSR hContact hπ hCR,
      hM.geoTransform hπ hC hCS⟩
    simp only [geoTransform_N, hNR]
  projection := by
    rintro hp m Y P Q ⟨R, F, S, hL, hN, hI, hd, hNR, hContact, hM⟩
    have hf := HironakaAuxiliaryGraphGeometry.isSubmersion_fst
      (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)
    refine ⟨projectionTest R, fun i => projectionTest (F i),
      (Prod.fst : projectionAmbient Y → Y) ⁻¹' S,
      (isLocStable_locEquiv Kinds.wp).projection hp hL,
      HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hN,
      GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hI,
      hd, ?_, maxContact_pullback_submersion hf rfl rfl rfl hN hI hContact, ?_⟩
    · change (Prod.fst : projectionAmbient Y → Y) ⁻¹' P.N = Prod.fst ⁻¹' R.N
      rw [hNR]
    · exact hM.pullback hf rfl rfl rfl (fun _ => rfl)
        (fun i hi => by simp only [projectionTest, hM.fE i hi]) (fun _ => rfl) (fun _ => rfl)
        rfl (by simp only [projectionTest, hM.E_eq]) rfl rfl
  restrict := by
    rintro m Y P Q ⟨R, F, S, hL, hN, hI, hd, hNR, hContact, hM⟩ U
    have hf := HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val (n := m) U
    refine ⟨MarkedIdeal.pullback (Subtype.val : U → Y) R,
      fun i => MarkedIdeal.pullback (Subtype.val : U → Y) (F i),
      (Subtype.val : U → Y) ⁻¹' S,
      (isLocStable_locEquiv Kinds.wp).restrict hL U,
      HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hN,
      GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hI,
      hd, ?_, maxContact_pullback_submersion hf rfl rfl rfl hN hI hContact, ?_⟩
    · change (Subtype.val : U → Y) ⁻¹' P.N = (Subtype.val : U → Y) ⁻¹' R.N
      rw [hNR]
    · exact hM.pullback (r := 0) (Y' := CMfd.of (n := m) U) hf rfl rfl rfl (fun _ => rfl)
        (fun i hi => by simp only [MarkedIdeal.pullback, hM.fE i hi]) (fun _ => rfl) (fun _ => rfl)
        rfl (by simp only [MarkedIdeal.pullback, hM.E_eq]) rfl rfl

/-- The actual reference's genuine contact suffices. The source is never
asserted to have literal tangent membership or MaxContact on this carrier. -/
theorem locWPEquiv_of_reference_maxContact {n : ℕ} {X : CMfd.{0} n}
    (P R : MarkedIdeal n X)
    (hPN : IsClosedSubmanifold n P.N) (hPI : P.ideal.IsCoherent) (hdP : 1 ≤ P.d)
    (hRN : IsClosedSubmanifold n R.N) (hRI : R.ideal.IsCoherent) (hdR : 1 ≤ R.d)
    (hN : P.N = R.N) (hL : LocWPEquiv P R)
    (S : Set X) (hS : IsClosedSubmanifold n S) (hSP : S ⊆ P.N) (hRef : MaxContact R S) :
    LocWPEquiv P (withN (coeffMarkedAlong P) S) :=
  LocEquiv.of_isLocStable isLocStable_referenceContact rfl
    ⟨R, fun i => derivMarkedAlong P i, S, hL, hRN, hRI, hdR, hN, hRef,
      memberRel_base P hPN hPI hdP hS hSP⟩

/-- Ordinary native source/reference data and a genuine reference tangent
produce the actual whole open coefficient restriction at its native mark. -/
theorem locWPEquiv_contact_of_reference_tangent {n k l : ℕ} {X : CMfd.{0} n}
    (P R : MarkedIdeal n X) (hP : IsInvDomain k P) (hR : IsInvDomain l R)
    (hN : P.N = R.N) (hL : LocWPEquiv P R)
    (U : Opens X) (u : X → ℂ) (hu : IsTangentDirectionAlong R.N R.ideal R.d U u) :
    LocWPEquiv (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) P)
      (MarkedIdeal.pullback (Subtype.val : U → X) (withN (coeffMarkedAlong P) (P.N ∩ {x | u x = 0}))) := by
  let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P
  let R' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) R
  let S : Set U := (Subtype.val : U → X) ⁻¹' (P.N ∩ {x | u x = 0})
  have hP' := InvDomainTowerAlong.isInvDomain_pullback_val U hP
  have hR' := InvDomainTowerAlong.isInvDomain_pullback_val U hR
  have hu' := isTangentDirectionAlong_pullback_val U
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hR.isWellFormed.isCoherent hg) hu
  have hS : S = R'.N ∩ {x : U | (u ∘ Subtype.val) x = 0} ∩ Set.univ := by
    ext x
    simp only [S, R', MarkedIdeal.pullback, hN, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Function.comp_apply, Set.mem_univ, and_true]
  have hSC : IsClosedSubmanifold n S := by
    rw [hS]
    exact isClosedSubmanifold_contact_along hR'.isWellFormed.isClosedSubmanifold_N
      hR'.isWellFormed.isCoherent hu'
  have hRef : MaxContact R' S := by
    rw [hS]
    exact maxContact_base R' hR'.isWellFormed.isCoherent hu'
  have hSP : S ⊆ P'.N := fun _ hx => hx.1
  have hN' : P'.N = R'.N := by
    change (Subtype.val : U → X) ⁻¹' P.N = (Subtype.val : U → X) ⁻¹' R.N
    rw [hN]
  have hCore := locWPEquiv_of_reference_maxContact (X := CMfd.of (n := n) U) P' R'
    hP'.isWellFormed.isClosedSubmanifold_N hP'.isWellFormed.isCoherent hP'.one_le_d
    hR'.isWellFormed.isClosedSubmanifold_N hR'.isWellFormed.isCoherent hR'.one_le_d
    hN' (hL.restrict U) S hSC hSP hRef
  rw [ContactCanonicalAlong.pullback_val_restrictedCoeff U P hP.isWellFormed.isCoherent
    hP.isWellFormed.isClosedSubmanifold_N hP.one_le_d]
  exact hCore

end
end Hironaka.HironakaG1ClassReferenceContact
