import Hironaka.Resolution.HironakaG3StoppedStructuralOverlap
import Hironaka.Resolution.HironakaDisjointNativeOpenLift
import Hironaka.Resolution.HironakaG11AdmissibleCentreEmptyInterior
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CoupledNativeNormalization
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport HironakaActualNativeSectionFiniteHistory
  MarkedIdealTowerTransport ResolutionInvariantSpec InvDomainTowerAlong

/-- Normalize a coupled history to native contact manifolds while retaining
its exact ambient blowup tower. -/
theorem exists_native_normalization
    {d t : ℕ} {X : CMfd.{0} (d+t)} {N : Set X}
    (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    {P : CMfd.{0} d} :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (Φ : P ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ N)
      {B : List (Set X)} {J : GermIdeal (d+t) X} {ι : P → X} {M : MarkedIdeal d P}
      (_hι : ∀ p, ι p = (Φ p).val) (_hM : IsInvDomain d M)
      {Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)} {T : BlowupTower P Q}
      {U : BlowupTower X Y} {η : Q → Y},
      IsGeoTestTower M T → IsGeoTestTower (fullMarked B J) U →
      CoupledHistory N B J ι M T U η →
      ∃ (hSc : IsClosed (contactAlong N U))
        (hS : ∀ y ∈ contactAlong N U, RegularAtDim (n := d+t) (contactAlong N U) y d)
        (R : BlowupTower (nativeManifold (Nat.le_add_right d t) N hN)
          (nativeManifold (Nat.le_add_right d t) (contactAlong N U) hS))
        (F : Q ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
          nativeManifold (Nat.le_add_right d t) (contactAlong N U) hS),
        Lift (Nat.le_add_right d t) N hNc hN B U (contactAlong N U) hSc hS R ∧
        IsTowerIso Φ T R F ∧ ∀ q, (F q).val = η q := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro Φ B J ι M hι hM Q Y T U η hT hU h
  induction h with
  | refl hEnd =>
    exact ⟨hNc,hN,.refl,Φ,Lift.refl,IsTowerIso.refl,fun q => (hι q).symm⟩
  | @step Q R Y Z T U η η' C C' ρ π hρ hπ hprev hcentre hsquare hEnd ih =>
    obtain ⟨hSc,hS,R₀,F,hLift,hIso,hF⟩ := ih hT.1 hU.1
    obtain ⟨hSc',hS',_hJ',_hNorm',_hB',_hTrans',F',hF',_hSq',_hIdeal',_hBoundary'⟩ := hEnd
    let D : Set (nativeManifold (Nat.le_add_right d t) (contactAlong N U) hS) := F.symm ⁻¹' C
    have hD : IsClosedSubmanifold d D :=
      (isClosedSubmanifold_preimage_iff F.symm).mpr hT.2.1
    have hCthin : interior C = ∅ :=
      HironakaG11AdmissibleCentreEmptyInterior.interior_eq_empty_of_invDomain_test_tower_centre hM T hT.1 hT.2
    have hDthin : interior D = ∅ := by
      simpa only [D, Diffeomorph.coe_toHomeomorph, hCthin, preimage_empty] using
        (F.symm.toHomeomorph.preimage_interior C).symm
    have hDimage : (Subtype.val : contactAlong N U → Y) '' D = C' := by
      rw [hcentre]
      ext y
      constructor
      · rintro ⟨p,hp,rfl⟩
        refine ⟨F.symm p,hp,?_⟩
        rw [← hF]
        exact congrArg Subtype.val (F.apply_symm_apply p)
      · rintro ⟨q,hq,rfl⟩
        refine ⟨F q,?_,hF q⟩
        change F.symm (F q) ∈ C
        rwa [F.symm_apply_apply]
    clear hcentre
    subst C'
    have hπD : IsBlowupAlong (d+t) ((Subtype.val : contactAlong N U → Y) '' D) π := hπ
    have hNC : HasNormalCrossings (d+t) ((Subtype.val : contactAlong N U → Y) '' D) (boundary B U) := by
      have he := MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
        (𝔪 := fullMarked B J)
        (𝔫 := (⟨univ,B,IdealWeightPowers.unitIdeal (d+t) X,1⟩ : MarkedIdeal (d+t) X)) rfl U
      change HasNormalCrossings (d+t) _ ((geoTransformAlong
        (⟨univ,B,IdealWeightPowers.unitIdeal (d+t) X,1⟩ : MarkedIdeal (d+t) X) U).E)
      rw [← he]
      exact hU.2.2.2
    let ρD := nativeProjection (Nat.le_add_right d t) hSc hS D π hπD
    let hρD := nativeProjection_genuine (Nat.le_add_right d t) hSc hS D hD hDthin π hπD
    have hcomm : ∀ z, ρD (F' z) = F (ρ z) := by
      intro z
      apply Subtype.ext
      change π ((F' z).val) = (F (ρ z)).val
      have hz := congrFun hsquare z
      change π (η' z) = η (ρ z) at hz
      rw [hF, congrFun hF']
      exact hz
    have hpre : F ⁻¹' D = C := by
      ext q
      change F.symm (F q) ∈ C ↔ q ∈ C
      rw [F.symm_apply_apply]
    have hStep := Lift.step hLift D hD hDthin π hπD hNC
    refine ⟨hSc',hS',.step R₀ D ρD hρD,F',hStep,?_,fun q => congrFun hF' q⟩
    exact IsTowerIso.step hIso hρ hρD F' hcomm hpre

end
end Hironaka.HironakaG3CoupledNativeNormalization
