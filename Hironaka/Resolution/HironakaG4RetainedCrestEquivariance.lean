import Hironaka.Resolution.HironakaG4RetainedDefectTraceEquivariance
import Hironaka.Resolution.HironakaSupportedTowerPhysicalExtension
import Hironaka.Resolution.HironakaG34JointMaskEquivariance
import Hironaka.Resolution.HironakaG34MaskFoldEquivariance
import Hironaka.Resolution.HironakaActualProcessedAllMasksDrop

set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff Topology BigOperators
universe u

namespace Hironaka.HironakaG4RetainedCrestEquivariance

noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MaxLocusLocal
  HironakaG4RetainedDefectRelativeDecrease HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedCurrentStamp HironakaG4OrderedDefectStamp HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalDistinctDefect HironakaActualRetainedBoundaryJointStep
  HironakaG34JointMaskEquivariance HironakaG34CanonicalLocalEquivariance
  HironakaG34MaskFoldEquivariance HironakaSupportedTowerPhysicalExtension
  HironakaSharpActualCurveComparisonRestriction HironakaG3CentresOverGenericFactor
  HironakaG4RetainedDefectTraceEquivariance
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem footprint_preserved (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born) {T : BlowupTower X Y}
    (P : RetainedDefectCrestPhase hn N old born T) {U V : Opens X}
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
    (hN : ∀ p : U, ((φ p : V) : X) ∈ N ↔ (p : X) ∈ N)
    (hE : ∀ H ∈ old ++ born, ∀ p : U, ((φ p : V) : X) ∈ H ↔ (p : X) ∈ H) :
    ∀ p : U, ((φ p : V) : X) ∈ P.footprint ↔ (p : X) ∈ P.footprint := by
  let a := (Subtype.val : U → X)
  let b := (Subtype.val : V → X)
  have hN' : φ ⁻¹' (b ⁻¹' N) = a ⁻¹' N := Set.ext hN
  have hList (L : List (Set X)) (hL : ∀ H ∈ L, H ∈ old ++ born) :
      (L.map (b ⁻¹' ·)).map (φ ⁻¹' ·) = L.map (a ⁻¹' ·) := by
    rw [List.map_map]
    exact List.map_congr_left fun H hH => Set.ext (hE H (hL H hH))
  have hOld := hList old (fun _ h => List.mem_append_left _ h)
  have hBorn := hList born (fun _ h => List.mem_append_right _ h)
  have gV := g.restrict V
  have hTransport := actual_retained_defect_and_rank_biholomorph hn
    gV.carrier gV.full gV.born_transverse gV.dense φ
  dsimp only at hTransport
  rw [hN',hOld,hBorn] at hTransport
  have hU := actual_retained_defect_and_rank_open hn g.carrier g.full g.born_transverse g.dense U
  have hV := actual_retained_defect_and_rank_open hn g.carrier g.full g.born_transverse g.dense V
  dsimp only at hU hV
  intro p
  have hDef := hTransport.1
  rw [hU.1,hV.1] at hDef
  have hDefp := Set.ext_iff.mp hDef p
  have hRank := hTransport.2 p
  rw [hU.2 p,hV.2 (φ p)] at hRank
  rw [P.footprint_iff,P.footprint_iff,←hRank]
  exact and_congr hDefp.symm Iff.rfl

private theorem mem_image_subtype_iff {A : Opens X} (B : Set A) (p : A) :
    p.val ∈ (Subtype.val : A → X) '' B ↔ p ∈ B := by
  rw [← Set.mem_preimage, Set.preimage_image_eq _ Subtype.val_injective]

set_option maxHeartbeats 1200000 in
/-- One certified crest history is invariant under local symmetries of
its exact carrier and ordered boundary, with every empty stage retained. -/
theorem retained_crest_isEquivariant (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born) {T : BlowupTower X Y}
    (P : RetainedDefectCrestPhase hn N old born T) :
    IsEquivariant N (old ++ born) T := by
  intro U U' φ hN hE
  let A := P.active
  let a : Opens U := ⟨{p | p.val ∈ A ∧ (φ p).val ∈ A},
    (A.isOpen.preimage continuous_subtype_val).inter
      (A.isOpen.preimage (continuous_subtype_val.comp φ.continuous))⟩
  let a' := preimageOpen φ.symm a
  let V : Opens X := ⟨(Subtype.val : U → X) '' (a : Set U),
    U.isOpen.isOpenMap_subtype_val _ a.isOpen⟩
  let V' : Opens X := ⟨(Subtype.val : U' → X) '' (a' : Set U'),
    U'.isOpen.isOpenMap_subtype_val _ a'.isOpen⟩
  have hVU : V ≤ U := fun _ ⟨p,_,hp⟩ => hp ▸ p.property
  have hV'U' : V' ≤ U' := fun _ ⟨p,_,hp⟩ => hp ▸ p.property
  have hVA : V ≤ A := fun _ ⟨p,hp,he⟩ => he ▸ hp.1
  have hV'A : V' ≤ A := by
    rintro x ⟨p,hp,rfl⟩
    have h := (show φ.symm p ∈ a from hp).2
    change (φ (φ.symm p)).val ∈ A at h
    rwa [φ.apply_symm_apply] at h
  let sourceWindow := nestedOpens U V
  let targetWindow := nestedOpens U' V'
  let left := nestedOpens A V
  let right := nestedOpens A V'
  have hMatch : (sourceWindow : Set U) = φ ⁻¹' (targetWindow : Set U') := by
    ext p
    change p.val ∈ (Subtype.val : U → X) '' (a : Set U) ↔
      (φ p).val ∈ (Subtype.val : U' → X) '' (a' : Set U')
    rw [mem_image_subtype_iff (a : Set U) p, mem_image_subtype_iff (a' : Set U') (φ p)]
    change p ∈ a ↔ φ.symm (φ p) ∈ a
    rw [φ.symm_apply_apply]
  let φ' := openRestriction φ sourceWindow targetWindow hMatch
  let γ := nestedOpensDiffeo (n := n) hVA
  let γ' := nestedOpensDiffeo (n := n) hV'A
  let u := (nestedOpensDiffeo (n := n) hVU).trans γ.symm
  let u' := (nestedOpensDiffeo (n := n) hV'U').trans γ'.symm
  let δ := u.symm.trans (φ'.trans u')
  let ξ := (Subtype.val : A → X)
  let i := (Subtype.val : left → A)
  let i' := (Subtype.val : right → A)
  let f : left → X := ξ ∘ i
  let f' : left → X := fun q => ξ (i' (δ q))
  let μ := ∑ j,P.profile j
  let M := jointProfileMarked N old born μ P.inactive
  let J := MarkedIdeal.pullback ξ M
  have hMCoh : M.ideal.IsCoherent :=
    isCoherent_jointProfileMarked hn g.carrier g.full g.born_transverse g.dense μ P.inactive
  have hf : HironakaBaseChange.IsOpenHoloEmbedding n f := ⟨V,γ,fun _ => rfl⟩
  have hf' : HironakaBaseChange.IsOpenHoloEmbedding n f' := ⟨V',δ.trans γ',fun _ => rfl⟩
  have hN' : f' ⁻¹' N = f ⁻¹' N := Set.ext fun q => hN (u.symm q).val
  have hE' : ∀ H ∈ old ++ born, f' ⁻¹' H = f ⁻¹' H :=
    fun H hH => Set.ext fun q => hE H hH (u.symm q).val
  have hRaw : MarkedIdeal.pullback f' M = MarkedIdeal.pullback f M :=
    pullback_jointProfileMarked_eq_of_preimage_eq (Y := CMfd.of (n := n) left)
      hn g.carrier g.full g.born_transverse g.dense μ P.inactive (f₁ := f') (f₂ := f)
      hf' hf hN' hE'
  have hJ : IsInvDomain (n+1) J := P.active_record.2.1
  have hCC : IsCanonical J ((CanonicalCentres.invFamily hn (n+1)).inv J) (restrict A T) :=
    P.active_record.2.2.1
  have hComp : MarkedIdeal.pullback δ (MarkedIdeal.pullback i' J) = MarkedIdeal.pullback i J := by
    have hLeft : MarkedIdeal.pullback i J = MarkedIdeal.pullback f M :=
      StepOneTangentChange.pullback_pullback_of_comp hMCoh contMDiff_subtype_val
        contMDiff_subtype_val (fun _ => rfl)
    have hRight : MarkedIdeal.pullback δ (MarkedIdeal.pullback i' J) =
        MarkedIdeal.pullback (fun q => i' (δ q)) J :=
      StepOneTangentChange.pullback_pullback_of_comp hJ.isWellFormed.isCoherent
        contMDiff_subtype_val δ.contMDiff (fun _ => rfl)
    rw [hLeft,hRight]
    have hRight' : MarkedIdeal.pullback (fun q => i' (δ q)) J = MarkedIdeal.pullback f' M :=
      StepOneTangentChange.pullback_pullback_of_comp hMCoh contMDiff_subtype_val
        (contMDiff_subtype_val.comp δ.contMDiff) (fun _ => rfl)
    exact hRight'.trans hRaw
  obtain ⟨_, hLocal⟩ := exists_isTowerIso_restrict_of_isCanonical
    (CanonicalCentres.invFamily hn (n+1)) hJ δ hComp (restrict A T) hCC
  have hFrom := (isTowerIso_restrict_nestedOpens hVU T).trans
    (isTowerIso_restrict_nestedOpens hVA T).symm
  have hTo := (isTowerIso_restrict_nestedOpens hV'U' T).trans
    (isTowerIso_restrict_nestedOpens hV'A T).symm
  have hWindow := hFrom.trans (hLocal.trans hTo.symm)
  have hBase : u.trans (δ.trans u'.symm) = φ' := by
    apply Diffeomorph.ext
    intro p
    change u'.symm (u' (φ' (u.symm (u p)))) = φ' p
    rw [u.symm_apply_apply,u'.symm_apply_apply]
  change IsTowerIso (u.trans (δ.trans u'.symm))
    (restrict sourceWindow (restrict U T)) (restrict targetWindow (restrict U' T)) _ at hWindow
  rw [hBase] at hWindow
  have hFoot := footprint_preserved hn g P φ hN hE
  have hSub : (Subtype.val : U → X) ⁻¹' P.footprint ⊆ (sourceWindow : Set U) := by
    intro p hp
    exact ⟨p,⟨P.footprint_subset hp,P.footprint_subset ((hFoot p).mpr hp)⟩,rfl⟩
  have hSub' : (Subtype.val : U' → X) ⁻¹' P.footprint ⊆ (targetWindow : Set U') := by
    intro p hp
    change p.val ∈ P.footprint at hp
    have hTarget : p.val ∈ A := P.footprint_subset hp
    have hMapped : (φ (φ.symm p)).val ∈ P.footprint := by
      rw [φ.apply_symm_apply]
      exact hp
    have hSource := (hFoot (φ.symm p)).mp hMapped
    refine ⟨p,⟨P.footprint_subset hSource,?_⟩,rfl⟩
    change (φ (φ.symm p)).val ∈ A
    rw [φ.apply_symm_apply]
    exact hTarget
  exact isTowerIso_extends_of_supported_windows φ sourceWindow targetWindow hMatch (restrict U T) (restrict U' T)
    (HironakaActualProcessedAllMasksDrop.centresOver_mono_local hSub _
      (centresOver_restrict U P.footprint T P.centresOver))
    (HironakaActualProcessedAllMasksDrop.centresOver_mono_local hSub' _
      (centresOver_restrict U' P.footprint T P.centresOver)) hWindow

/-- Every actual ordered retained-defect history is strictly locally
equivariant for its source geometry. -/
theorem retained_defect_trace_isEquivariant (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} {μ : WithTop RetainedStampRank} {T : BlowupTower X Y}
    (g : NativeRetainedGeometry N old born) (trace : OrderedRetainedDefectTrace hn N old born μ T) :
    IsEquivariant N (old ++ born) T :=
  orderedRetainedDefectTrace_isEquivariant
    (fun geometry crest => retained_crest_isEquivariant hn geometry crest) trace g

end
end Hironaka.HironakaG4RetainedCrestEquivariance
