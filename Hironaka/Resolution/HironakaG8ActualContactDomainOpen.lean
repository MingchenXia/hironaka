import Hironaka.Resolution.HironakaG8PairDomainOpen
import Hironaka.Resolution.HironakaG8CaseTContactPair
import Hironaka.Resolution.HironakaG11ActualContactTailTest
/-! # Common domain open for an actual contact history -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ActualContactDomainOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  TangentDirectionAlong StepOneValue ResolutionInvariantSpec DivisorExponentAlong
  HironakaG11InvBMLower HironakaG8LocalHistory HironakaG8PairDomainOpen
  HironakaG8CaseTActualAmbient HironakaG8CaseTContactPair NormalCrossings NormalCrossingsInvariance
open HironakaG11InvBMClass (SameCarrierDim)

/-- A common original test history and nonzero actual contact transforms
produce a common native-domain source open with the full old prefix, local
equivalence, equal carrier dimensions, and the literal restricted suffix. -/
theorem actual_contact_common_domain_open
    {n : ℕ} {X Y Z : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B) (hAB : LocWPEquiv A B)
    (hd : A.d = B.d) (hdim : SameCarrierDim A B)
    (U : Opens X) {f g : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (hg : IsTangentDirectionAlong B.N B.ideal B.d U g)
    (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked A) (P.append Q)) :
    let V := openPreimage P U
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
    let D := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B g P)
    let F := (A.E.map (strictAlong P)).map ((Subtype.val : V → Y) ⁻¹' ·)
    let T := restrict V Q
    ∀ (z : openPreimage Q V),
      z ∈ (geoTransformAlong C T).N → z ∈ (geoTransformAlong D T).N →
      IsNonzeroAlongAt (geoTransformAlong C T).N (geoTransformAlong C T).ideal z →
      IsNonzeroAlongAt (geoTransformAlong D T).N (geoTransformAlong D T).ideal z →
      ∃ G : Opens V, T.proj z ∈ G ∧
        let CG := MarkedIdeal.pullback (Subtype.val : G → V) C
        let DG := MarkedIdeal.pullback (Subtype.val : G → V) D
        let FG := F.map ((Subtype.val : G → V) ⁻¹' ·)
        IsInvDomain n CG ∧ IsInvDomain n DG ∧
        LocWPEquiv (X := CMfd.of (n := n) G) {CG with E := FG ++ CG.E} {DG with E := FG ++ CG.E} ∧
        SameCarrierDim (X := CMfd.of (n := n) G) CG DG ∧ DG.d = CG.d ∧
        IsSNCDivisor n (FG ++ CG.E) ∧
        IsGeoTestTower CG (restrict G T) ∧ IsGeoTestTower DG (restrict G T) ∧
        IsGeoTestTower {CG with E := FG ++ CG.E} (restrict G T) := by
  let V := openPreimage P U
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
  let D := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B g P)
  let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A P)
  let F := (A.E.map (strictAlong P)).map ((Subtype.val : V → Y) ⁻¹' ·)
  let T := restrict V Q
  have hTA : IsGeoTestTower A (P.append Q) := ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hT
  have ⟨hPA,hQA⟩ := (isGeoTestTower_append_iff A P Q).mp hTA
  have hTB : IsGeoTestTower B P := (hAB.wEquiv.2 P).1.mp hPA
  have hc := actual_contact_ambient A hA.isWellFormed hA.one_le_d U hf P hPA
  have hd' := actual_contact_ambient B hB.isWellFormed hB.one_le_d U hg P hTB
  have hCR : LocWPEquiv (X := CMfd.of (n := n) V) {C with E := F ++ C.E} R :=
    actual_contact_prefix A hA.isWellFormed hA.one_le_d U hf P hPA
  have hp := actual_contact_pair A B hA.isWellFormed hB.isWellFormed hA.one_le_d hB.one_le_d
    hAB hdim U hf hg P hPA
  have hE : D.E = C.E := List.append_cancel_left hp.1.E_eq
  have hrel : LocWPEquiv (X := CMfd.of (n := n) V) {C with E := F ++ C.E} {D with E := F ++ C.E} := by
    have hp' : LocWPEquiv (X := CMfd.of (n := n) V) {C with E := F ++ C.E} {D with E := F ++ D.E} := hp.1
    rw [hE] at hp'
    exact hp'
  have hdC : 1 ≤ C.d := by
    change 1 ≤ (contactCoeffBM A f P).d
    rw [contactCoeffBM_d]
    exact HironakaG8ClassStepCut.one_le_coeffEmptyBM_d A
  have hdd : D.d = C.d := by
    change (contactCoeffBM B g P).d = (contactCoeffBM A f P).d
    rw [contactCoeffBM_d, contactCoeffBM_d, coeffEmptyBM_d, coeffEmptyBM_d, hd]
  have hdD : 1 ≤ D.d := hdd ▸ hdC
  have hRN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA.isWellFormed P hPA)
  have hRT : IsGeoTestTower (X := CMfd.of (n := n) V) R T :=
    isGeoTestTower_restrict V hRN.isClosedSubmanifold_N hRN.isCoherent Q hQA
  have hTF : IsGeoTestTower (X := CMfd.of (n := n) V) {C with E := F ++ C.E} T :=
    (hCR.wEquiv.2 T).1.mpr hRT
  have hsnc : IsSNCDivisor n (F ++ C.E) := by
    have he : R.E = F ++ C.E := hCR.E_eq
    rw [← he]
    exact hc.2.1.isSNCDivisor
  change ∀ (z : openPreimage Q V), z ∈ (geoTransformAlong C T).N → z ∈ (geoTransformAlong D T).N →
    IsNonzeroAlongAt (geoTransformAlong C T).N (geoTransformAlong C T).ideal z →
    IsNonzeroAlongAt (geoTransformAlong D T).N (geoTransformAlong D T).ideal z → _
  intro z hzC hzD hnC hnD
  obtain ⟨G,hzG,hCG,hDG,hrelG,hTC,hTD,hTFG⟩ :=
    exists_common_domain_open_of_prefixed_test C D F hc.1 hd'.1 hdC hdD hE hrel T hTF hzC hzD hnC hnD
  let CG := MarkedIdeal.pullback (Subtype.val : G → V) C
  let DG := MarkedIdeal.pullback (Subtype.val : G → V) D
  let FG := F.map ((Subtype.val : G → V) ⁻¹' ·)
  have hdimG : SameCarrierDim (X := CMfd.of (n := n) G) CG DG :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hc.1.isCoherent) hp.2 G
  have hsncG : IsSNCDivisor n (FG ++ CG.E) := by
    have hh := isSNCDivisor_map_preimage (pullsBackCoordinates_val G) continuous_subtype_val hsnc
    dsimp [FG,CG]
    simpa only [MarkedIdeal.pullback, List.map_append] using hh
  exact ⟨G,hzG,hCG,hDG,hrelG,hdimG,hdd,hsncG,hTC,hTD,hTFG⟩

end
end Hironaka.HironakaG8ActualContactDomainOpen
