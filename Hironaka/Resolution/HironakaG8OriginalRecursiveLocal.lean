import Hironaka.Resolution.HironakaActualOriginalLowerLocalTests
import Hironaka.Resolution.HironakaG1CoeffBarLocal
import Hironaka.Resolution.HironakaG8MemberCutStable
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG8OriginalRecursiveLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdealBiholomorphism HomogenizedIdealAlong CoefficientIdeal CoefficientIdealRestriction ResolutionInvariantSpec
  InvDomainTowerAlong MarkedIdealRestrictOpen HironakaActualOriginalHistoricalBarWeightedThreshold
  HironakaActualOriginalTrueMarkMaskCompanions HironakaActualOriginalLowerLocalTests
  HironakaG1CoeffBarLocal HironakaG8LocalHistory HironakaG8MemberCutStable
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactStageKept
  CoefficientIdealAlongRestrictionFull HironakaEmbeddedAnalytic NonmonomialOrderLocal
  NonmonomialOrderTail CompanionRebase

/-- The literal kept-boundary common-contact records inherit the full local relation. -/
theorem contact_lower_locally_equivalent {n kA kB : ℕ} {X Y : CMfd.{0} n}
    (J K : MarkedIdeal n X) (hJ : IsInvDomain kA J) (hK : IsInvDomain kB K)
    (hN : J.N=K.N) (hLocal : LocWPEquiv J K) (H : BlowupTower X Y)
    (hHJ : IsGeoTestTower J H) (hHK : IsGeoTestTower K H) (O : Opens Y) (w : X→ℂ)
    (hS : IsClosedSubmanifold n (contactMarkedKept J w H O).N) :
    LocWPEquiv (X := CMfd.of (n := n) O) (contactMarkedKept J w H O) (contactMarkedKept K w H O) := by
  have hBarJ := (original_bar_weighted_history J hJ H hHJ).2.1
  have hBarK := (original_bar_weighted_history K hK H hHK).2.1
  let A := MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong (barMarked J) H)
  let B := MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong (barMarked K) H)
  let S := (Subtype.val : O→Y) ⁻¹' strictAlong H (J.N∩{x | w x=0})
  have hA := isInvDomain_pullback_val O hBarJ
  have hB := isInvDomain_pullback_val O hBarK
  have hSA : S⊆A.N := by
    intro x hx
    exact MaximalContactAlongTower.strictAlong_subset_N (barMarked J) (fun _ hz=>hz.1) H hx
  have hSB : S⊆B.N := by
    intro x hx
    have hxK : x.val∈strictAlong H (K.N∩{x | w x=0}) := by rw [←hN]; exact hx
    exact MaximalContactAlongTower.strictAlong_subset_N (barMarked K) (fun _ hz=>hz.1) H hxK
  have hLJ : contactMarkedKept J w H O=withN (coeffMarkedAlong A) S :=
    ContactCanonicalAlong.pullback_val_restrictedCoeff O _ hBarJ.isWellFormed.isCoherent
      hBarJ.isWellFormed.isClosedSubmanifold_N hBarJ.one_le_d _
  have hLK : contactMarkedKept K w H O=withN (coeffMarkedAlong B) S := by
    change MarkedIdeal.pullback (Subtype.val : O→Y)
      (withN (coeffMarkedAlong (geoTransformAlong (barMarked K) H)) (strictAlong H (K.N∩{x | w x=0})))=_
    rw [ContactCanonicalAlong.pullback_val_restrictedCoeff O _ hBarK.isWellFormed.isCoherent
      hBarK.isWellFormed.isClosedSubmanifold_N hBarK.one_le_d]
    change withN (coeffMarkedAlong B) ((Subtype.val : O→Y) ⁻¹' strictAlong H (K.N∩{x | w x=0}))=
      withN (coeffMarkedAlong B) ((Subtype.val : O→Y) ⁻¹' strictAlong H (J.N∩{x | w x=0}))
    rw [hN]
  have hBT : IsGeoTestTower (barMarked J) H :=
    (((HironakaG8HomStable.bar_local_any_boundary J hJ).wEquiv).2 H).1.mp hHJ
  have hUpper : LocWPEquiv (X := CMfd.of (n := n) O) A B := ((bar_local_of_local J K hJ hK hLocal).geoTransformAlong H hBT).restrict O
  have hCommon := memberLocal_of_split (κ := Kinds.wp) (X := CMfd.of (n := n) O)
    (A := A) (B := B) (F := []) (G := A.E) (S := S) rfl hA.isWellFormed hB.isWellFormed
    hA.one_le_d hB.one_le_d hUpper (by simp) hS hSA hSB (by simp)
  rw [hLJ,hLK]
  simpa [withN, coeffMarkedAlong, HomogenizedIdealAlong.derivMarkedAlong,
    CoefficientIdeal.msum, hUpper.E_eq] using hCommon
/-- Original given-Q companion histories yield locally equivalent literal lower records. -/
theorem original_recursive_lower_local {n k : ℕ} (hn : 0<n) {A : CMfd.{0} n}
    (Q : MarkedIdeal n A) (hQ : IsInvDomain k Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d) (Z : Set A)
    (hZ : IsComplexAnalyticSubset (n:=n) Z) (hSing : Q.cosupp⊆singularSet (n:=n) Z)
    (a : A) (ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      x∈U ∧ IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧
      ∀{Y : CMfd.{0} n}(H : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J H→
        IsGeoTestTower K H ∧
        ∀y∈(geoTransformAlong (barMarked K) H).cosupp,
          y∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked K) H).N
            (geoTransformAlong (barMarked K) H).ideal (geoTransformAlong (barMarked K) H).d→
          y∈maskB K H y ∧
          let O:=maskB K H y
          let LJ:=contactMarkedKept J (tangentChoice K (H.proj y)).2 H O
          let LK:=contactMarkedKept K (tangentChoice K (H.proj y)).2 H O
          IsInvDomain ((k-1)-1) LJ ∧ IsInvDomain ((k-1)-1) LK ∧
          LK=lowerMarkedB K H y ∧ LJ.N=LK.N ∧ LJ.E=LK.E ∧ LocWPEquiv (X := CMfd.of (n := n) O) LJ LK := by
  obtain ⟨hm,hxU,hJ,hK,_hJE,_hKE,_hJd,_hKd,hStage⟩ :=
    original_lower_local_tests hn Q hQ hN hE hMax Z hZ hSing a ha
  obtain ⟨_hmC,_hxC,hLocal⟩ :=
    HironakaG1CoeffCompanionLocal.original_coefficient_companions_local hn Q hQ hN hE hMax Z hZ hSing a ha
  refine ⟨hm,hxU,hJ,hK,?_⟩
  intro Y H hHJ
  obtain ⟨hHK,hStage⟩ := hStage H hHJ
  refine ⟨hHK,?_⟩
  intro y hy hOut
  obtain ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,_hLJd,_hLKd,_hLenJ,_hLenK,_hRest⟩ := hStage y hy hOut
  refine ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,?_⟩
  apply contact_lower_locally_equivalent _ _ hJ hK ?_ hLocal H hHJ hHK _ _ hLJ.isWellFormed.isClosedSubmanifold_N
  simp only [CompanionRebase.companionOf, CompanionReductionAlong.companionAlong_N]
  rfl
end
end Hironaka.HironakaG8OriginalRecursiveLocal
