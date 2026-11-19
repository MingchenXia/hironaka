import Hironaka.Resolution.HironakaG1ClassReferenceContact
import Hironaka.Resolution.HironakaG1OriginalStepSkeleton
import Hironaka.Resolution.HironakaG1CoeffBarLocal
import Hironaka.Resolution.HironakaActualOriginalHistoricalBarWeightedThreshold
import Hironaka.Invariant.ContactEquivalenceStage

/-! Class-reference contact on the SAME original tested prefix, then the
independent actual own/reference lower contact class on the common mask.
Blueprint FIRST: hironaka-g1-original-contact-class-at-stage.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalContactClassAtStage
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSpec
  HironakaG1ClassReferenceContact HironakaG8ContactMax HironakaG8LocalHistory
  HironakaG1OriginalStepSkeleton HironakaG1CoeffBarLocal HironakaG8HomStable
  HironakaActualOriginalHistoricalBarWeightedThreshold InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower ContactEquivalenceAlong ContactEquivalenceStage
  TangentDirectionAlong ContactStageKept ContactStageInvDomain GiraudAlong CoefficientIdealRestriction
  StepOneValue StepOneValueMasked StepOneLowerDomain
open HomogenizedGlueingTower (strictAlong)

/-- The actual ORIGINAL reference contact has MaxContact at the SAME tested
prefix and every genuine subwindow of the original tangent preimage. -/
theorem maxContact_stage_on_open {n k : ℕ} {X Y : CMfd.{0} n}
    (R : MarkedIdeal n X) (hR : IsInvDomain k R)
    (U : Opens X) (u : X → ℂ) (hu : IsTangentDirectionAlong R.N R.ideal R.d U u)
    (T : BlowupTower X Y) (hT : IsGeoTestTower R T)
    (O : Opens Y) (hOU : (O : Set Y) ⊆ openPreimage T U) :
    MaxContact (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
      (geoTransformAlong R T)) ((Subtype.val : O → Y) ⁻¹' strictAlong T (R.N ∩ {x | u x = 0})) := by
  let R' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (geoTransformAlong R T)
  have hRT := isInvDomain_geoTransformAlong hR T hT
  have hR' := isInvDomain_pullback_val O hRT
  have hHol : ∀ x f, (geoTransformAlong R T).ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hRT.isWellFormed.isCoherent hg
  have hHol' : ∀ x f, R'.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hR'.isWellFormed.isCoherent hg
  intro z hz
  obtain ⟨W, hzW, _hWU, w, hw, hWS⟩ := exists_isTangentDirectionAlong_stage R
    hR.isWellFormed.isClosedSubmanifold_N hR.isWellFormed.isCoherent hR.one_le_d U hu T hT hz (hOU z.2)
  have hwO : IsTangentDirectionAlong R'.N R'.ideal R'.d
      ((Subtype.val : O → Y) ⁻¹' (W : Set Y)) (w ∘ Subtype.val) :=
    isTangentDirectionAlong_pullback
      (fun y => ⟨DerivativeIdealAlongEtale.openInv O y, DerivativeIdealAlongEtale.isLocalInverseAt_val O y⟩) hHol hw
  refine ⟨(Subtype.val : O → Y) ⁻¹' (W : Set Y), w ∘ Subtype.val, hzW, hwO.isOpen,
    (fun x hx => holomorphicAt_of_mem_iterDerivIdealAlong hHol' _ x _ (hwO.mem x hx)), ?_,
    (fun x hx _ h0 => hwO.multiplicity_one x hx h0), ?_⟩
  · intro x hx _hxN
    exact ⟨1, fun _ => w ∘ Subtype.val, fun _ _ => 1, fun _ => hwO.mem x hx,
      fun _ => holomorphicAt_const 1, Eventually.of_forall fun _ _ => by simp⟩
  · intro x hx hxN
    constructor
    · intro h0
      have h : (x : Y) ∈ (geoTransformAlong R T).N ∩ {x | w x = 0} ∩ (W : Set Y) := ⟨⟨hxN, h0⟩, hx⟩
      rw [hWS] at h
      exact h.1
    · intro hS
      have h : (x : Y) ∈ strictAlong T (R.N ∩ {x | u x = 0}) ∩ (W : Set Y) := ⟨hS, hx⟩
      rw [← hWS] at h
      exact h.1.2

/-- The transformed INITIAL original bar is locally equivalent to its
literal kept coefficient restriction on the actual reference's contact.
No tangent membership of the source J is assumed or asserted. -/
theorem original_bar_local_to_reference_contact {n kJ kK : ℕ} {X Y : CMfd.{0} n}
    (J K : MarkedIdeal n X) (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hN : J.N = K.N) (hL : LocWPEquiv J K)
    (U : Opens X) (u : X → ℂ) (hu : IsTangentDirectionAlong K.N K.ideal K.d U u)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (O : Opens Y) (hOU : (O : Set Y) ⊆ openPreimage T U) :
    LocWPEquiv (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong (barMarked J) T))
      (contactMarkedKept J u T O) := by
  have hTK : IsGeoTestTower K T := (hL.wEquiv.2 T).1.mp hT
  have hTBar : IsGeoTestTower (barMarked J) T := (((bar_local_any_boundary J hJ).wEquiv).2 T).1.mp hT
  have hBarT := (original_bar_weighted_history J hJ T hT).2.1
  have hKT := isInvDomain_geoTransformAlong hK T hTK
  let P := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (geoTransformAlong (barMarked J) T)
  let R := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (geoTransformAlong K T)
  let S : Set O := (Subtype.val : O → Y) ⁻¹' strictAlong T (J.N ∩ {x | u x = 0})
  have hP := isInvDomain_pullback_val O hBarT
  have hR := isInvDomain_pullback_val O hKT
  have hBase : LocWPEquiv (barMarked J) K := (bar_local_any_boundary J hJ).symm.trans hL
  have hPR : LocWPEquiv (X := CMfd.of (n := n) O) P R := (hBase.geoTransformAlong T hTBar).restrict O
  have hNT : (geoTransformAlong (barMarked J) T).N = (geoTransformAlong K T).N :=
    HironakaCoherentTransformExtension.geoTransformAlong_N_eq_of_N_eq (𝔍 := barMarked J) (𝔪 := K) hN T
  have hPNR : P.N = R.N := by
    change (Subtype.val : O → Y) ⁻¹' (geoTransformAlong (barMarked J) T).N =
      (Subtype.val : O → Y) ⁻¹' (geoTransformAlong K T).N
    rw [hNT]
  have hSC : IsClosedSubmanifold n S := by
    change IsClosedSubmanifold n ((Subtype.val : O → Y) ⁻¹' strictAlong T (J.N ∩ {x | u x = 0}))
    rw [hN]
    exact isClosedSubmanifold_strictAlong_stage_of_le K hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hK.one_le_d U hu T hTK O hOU
  have hSP : S ⊆ P.N := fun x hx =>
    MaximalContactAlongTower.strictAlong_subset_N (barMarked J) (fun _ hz => hz.1) T hx
  have hRef : MaxContact R S := by
    have h := maxContact_stage_on_open K hK U u hu T hTK O hOU
    simpa only [S, hN] using h
  have hCore := locWPEquiv_of_reference_maxContact (X := CMfd.of (n := n) O) P R
    hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hP.one_le_d
    hR.isWellFormed.isClosedSubmanifold_N hR.isWellFormed.isCoherent hR.one_le_d hPNR hPR S hSC hSP hRef
  change LocWPEquiv (X := CMfd.of (n := n) O) P
    (MarkedIdeal.pullback (Subtype.val : O → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (barMarked J) T)) (strictAlong T (J.N ∩ {x | u x = 0}))))
  rw [ContactCanonicalAlong.pullback_val_restrictedCoeff O _ hBarT.isWellFormed.isCoherent
    hBarT.isWellFormed.isClosedSubmanifold_N hBarT.one_le_d]
  exact hCore

/-- The independent existing J and K choices give the SAME full original
lower local class on their genuine nonempty common mask. The source J's
native double mark and every old/born/empty slot remain literal. -/
theorem own_contact_locally_equivalent_on_intersection {n kJ kK : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hN : J.N = K.N) (hL : LocWPEquiv J K)
    (hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d) (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked J) T).cosupp) (hReg : stepRegime J 0 T y) :
    ∃ _hyJ : y ∈ maskB J T y, ∃ _hyK : y ∈ maskB K T y,
      let O := maskB J T y ⊓ maskB K T y
      LocWPEquiv (X := CMfd.of (n := n) O)
        (contactMarkedKept J (tangentChoice J (T.proj y)).2 T O)
        (contactMarkedKept J (tangentChoice K (T.proj y)).2 T O) := by
  have hTK : IsGeoTestTower K T := (hL.wEquiv.2 T).1.mp hT
  have hTBarJ : IsGeoTestTower (barMarked J) T := (((bar_local_any_boundary J hJ).wEquiv).2 T).1.mp hT
  have hTBarK : IsGeoTestTower (barMarked K) T := (((bar_local_any_boundary K hK).wEquiv).2 T).1.mp hTK
  have hyK : y ∈ (geoTransformAlong (barMarked K) T).cosupp :=
    ((bar_local_of_local J K hJ hK hL).geoTransformAlong T hTBarJ).cosupp_eq_base ▸ hy
  have hSkel := original_step_skeleton_of_wEquiv hn J K hJ hK hN hL.wEquiv T hT y
  have hRegK : stepRegime K 0 T y := (hSkel.2.2 0).mp hReg
  have hOutJ : y ∉ CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked J) T).N
      (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d :=
    fun h => hReg.2 (Or.inl ⟨hReg.1, h⟩)
  have hOutK : y ∉ CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked K) T).N
      (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d :=
    fun h => hRegK.2 (Or.inl ⟨hRegK.1, h⟩)
  have hyJMask := StepOneLowerDomain.mem_maskB J hJ.isWellFormed hJ.one_le_d hMaxJ T hTBarJ hy hReg.1 hOutJ
  have hyKMask := StepOneLowerDomain.mem_maskB K hK.isWellFormed hK.one_le_d hMaxK T hTBarK hyK hRegK.1 hOutK
  obtain ⟨_hxJ, huJ⟩ := tangentChoice_spec J
    (exists_tangent_of_mem_cosupp J hJ.isWellFormed hJ.one_le_d hMaxJ T hTBarJ hy)
  obtain ⟨_hxK, huK⟩ := tangentChoice_spec K
    (exists_tangent_of_mem_cosupp K hK.isWellFormed hK.one_le_d hMaxK T hTBarK hyK)
  let UJ : Opens X := ⟨(tangentChoice J (T.proj y)).1, huJ.isOpen⟩
  let UK : Opens X := ⟨(tangentChoice K (T.proj y)).1, huK.isOpen⟩
  let O := maskB J T y ⊓ maskB K T y
  have hOUJ : (O : Set Y) ⊆ openPreimage T UJ := fun _ hz => (interior_subset hz.1).1
  have hOUK : (O : Set Y) ⊆ openPreimage T UK := fun _ hz => (interior_subset hz.2).1
  have hOwn := original_bar_local_to_reference_contact J J hJ hJ rfl (LocEquiv.refl Kinds.wp J)
    UJ (tangentChoice J (T.proj y)).2 huJ T hT O hOUJ
  have hOther := original_bar_local_to_reference_contact J K hJ hK hN hL
    UK (tangentChoice K (T.proj y)).2 huK T hT O hOUK
  exact ⟨hyJMask, hyKMask, hOwn.symm.trans hOther⟩

end
end Hironaka.HironakaG1OriginalContactClassAtStage
