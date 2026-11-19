import Hironaka.Resolution.HironakaActualRetainedBoundaryProfileExit
import Hironaka.Resolution.HironakaActualRetainedBornResidualOpen
import Hironaka.Resolution.HironakaActualDefectProfileWindows
import Hironaka.Resolution.HironakaCompactFootprintSharpExtension
import Hironaka.Resolution.HironakaSharpActualEmptyChronologicalDefect
import Hironaka.Resolution.HironakaActualRawRecordPullbacks
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Resolution.HironakaSharpActualDistinctCountOpenNaturality
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix
import Hironaka.Resolution.HironakaG34ExtensionEquivariance

/-!
# The profile-window block and the global profile blocks with an equivariance conclusion (sixth brick of EQ_d)

Lane G34 (run 0080, round 9).  Blueprint: `hironaka-g34-resume-profile-block-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (rows "carrier, blocks" and "carrier, extension"), §2(c)(ii).

The held theorem `HironakaActualGlobalDefectProfileBlock.exists_actual_global_original_profile_blocks` is existential and
its window block (`exists_current_profile_window_block`) is PRIVATE.  This module re-derives the held file verbatim (the
private helpers below are copies; the held file is not edited), with two changes in the window block: the profile-`q` exit
on the window `U` is the equivariant one (`HironakaG34MaskFoldEquivariance.exists_actual_retained_boundary_profile_q_exit_equivariant`),
and the compact-footprint extension `Q` of it is equivariant for the data together with the window
(`HironakaG34ExtensionEquivariance.isEquivariant_of_extension`).  The global profile blocks inherit the clause for the
CURRENT data along the prefix `T` and the profile window.

## Main result

* **`exists_actual_global_original_profile_blocks_equivariant`**: the held conclusions together with, for each realized
  profile, `IsEquivariant A.N (profileWindow W E T q r :: (E.map (strictAlong T) ++ A.E)) Q`, where `A` is the transform
  of the geometric template `(W, [])` along `T`.

New file; no existing statement changed; no named input.  Sorry-free.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34ProfileBlockEquivariance
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBornResidualHistory HironakaActualRetainedBornResidualOpen
  HironakaActualRetainedBoundaryMaskBlock HironakaActualRetainedBoundaryProfileExit
  HironakaActualDefectProfileWindows HironakaG4PreparedCentreCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualEmptyChronologicalDefect
  HironakaSharpActualEquimultipleResidualHistory HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpOriginalProductTraceOrder HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus MonomialPartAlong MonomialPartEtale
  GermIdealOrder DivisorExponentAlong MemberInterLocusAlong IdealWeightPowers
  BlowupTowerIsomorphism BlowupTowerSplitIso MarkedIdealRestrictOpen
  DerivativeIdealAlongEtale HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X Y Z V : CMfd.{u} n}

private theorem vanishing_pullback_biholo
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {H : Set X} (hH : IsClosedSubmanifold n H) :
    GermIdeal.pullback (m := n) e (vanishingIdeal (n := n) H)=
      vanishingIdeal (n := n) (e ⁻¹' H) := by
  have hPre := MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
    e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply hH
  have h := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
    e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply
    (g := (id : Y → Y)) contMDiff_id H
  rw [BlowupControlledTransform.pullback_id (VanishingIdealCoherent.isCoherent_vanishingIdeal hPre)] at h
  exact h.symm

/-- Zero-credit intrinsic whole-record naturality.  The actual geometry
derives all coherence inputs; every retained born position and mark0 stay. -/
private theorem retained_seed_pullback_biholo (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (i : Fin old.length) :
    let oldY := old.map (e ⁻¹' ·)
    let iY : Fin oldY.length := ⟨i.val,by simpa only [oldY,List.length_map] using i.isLt⟩
    MarkedIdeal.pullback e (retainedResidualMarked N old born i)=
      retainedResidualMarked (e ⁻¹' N) oldY (born.map (e ⁻¹' ·)) iY := by
  let oldY := old.map (e ⁻¹' ·)
  let iY : Fin oldY.length := ⟨i.val,by simpa only [oldY,List.length_map] using i.isLt⟩
  have hGet : oldY.get iY=e ⁻¹' old.get i := by simp [oldY,iY]
  have hH := MonomialPart.isClosedSubmanifold_get hn
    (isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)) i
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
  have hTrace : GermIdeal.pullback (m := n) e (oldTraceIdeal N old i)=
      oldTraceIdeal (e ⁻¹' N) oldY iY := by
    change GermIdeal.pullback (m := n) e (restrictOn n N (vanishingIdeal (n := n) (old.get i)))=
      restrictOn n (e ⁻¹' N) (vanishingIdeal (n := n) (oldY.get iY))
    rw [restrictOn_pullback_biholo e hN hcH,vanishing_pullback_biholo e hH,hGet]
  have hJ := MonomialPartEtale.pullback_nonmonomialPartAlong
    (φ := e) (N := N) (𝔞 := oldTraceIdeal N old i) (E := born)
    (fun y => ⟨e.symm,CompanionRebase.isLocalInverseAt_diffeo e y⟩)
    hParts.1 hParts.2.2.2.2.1 hParts.2.2.1
  rw [hTrace] at hJ
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  exact hJ

private theorem canonical_family_biholo (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    canonicalResidualFamily (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·))=
      (canonicalResidualFamily N old born).map (GermIdeal.pullback (m := n) e) := by
  simp only [canonicalResidualFamily,List.map_map]
  apply List.map_congr_left
  intro H hH
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
  have h := congrArg (fun M : MarkedIdeal n Y => M.ideal)
    (retained_seed_pullback_biholo hn hN hE hTr hdense e i)
  simpa [MarkedIdealBiholomorphism.MarkedIdeal.pullback,retainedResidualMarked,oldResidualPart,oldTraceIdeal] using h.symm

/-- Normalization is retained at EVERY finite-product multiplication. -/
private theorem canonical_product_pullback_biholo (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (q : ℕ) (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    MarkedIdeal.pullback e (canonicalProductMarked N old born q)=
      canonicalProductMarked (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·)) q := by
  have hCoh : ∀ I ∈ canonicalResidualFamily N old born,I.IsCoherent := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.1
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) e (relativeIdealListProduct N (canonicalResidualFamily N old born))=
    relativeIdealListProduct (e ⁻¹' N)
      (canonicalResidualFamily (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·)))
  rw [relativeIdealListProduct_pullback_biholo e hN _ hCoh,canonical_family_biholo hn hN hE hTr hdense e]

private theorem open_full_density {N : Set X} {E : List (Set X)}
    (hdense : N ⊆ closure (N \ ⋃ H ∈ E,H)) (U : Opens X) :
    (Subtype.val : U → X) ⁻¹' N ⊆ closure ((Subtype.val : U → X) ⁻¹' N \
      ⋃ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
  intro y hy
  have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (N \ ⋃ H ∈ E,H) := hdense hy
  erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (N \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

private theorem open_geometry {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (U : Opens X) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    IsClosedSubmanifold n NU ∧ IsSNCDivisor n (OU ++ BU) ∧ IsTransverse n NU BU ∧
      NU ⊆ closure (NU \ ⋃ H ∈ OU ++ BU,H) := by
  refine ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U,?_,
    isTransverse_preimage (pullsBackCoordinates_val U) hTr,?_⟩
  · simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  · simpa only [List.map_append] using open_full_density hdense U

private theorem template_pullback (f : Y → X) (N : Set X) (B : List (Set X)) :
    MarkedIdeal.pullback f (geometricTemplate N B)=geometricTemplate (f ⁻¹' N) (B.map (f ⁻¹' ·)) := by
  simp [MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal]

/-- The entire actual born ledger, carrier and each original strict member
are transported by the ACTUAL extension tower isomorphism. -/
private theorem tuple_open_iso {N : Set X} (hN : IsClosedSubmanifold n N)
    (born : List (Set X)) (U : Opens X) (S : BlowupTower X Y)
    (hS : IsGeoTestTower (geometricTemplate N born) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e) :
    let f : Z → Y := (Subtype.val : openPreimage S U → Y) ∘ e
    let NU := (Subtype.val : U → X) ⁻¹' N
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate N born) S
    let AR := geoTransformAlong (geometricTemplate NU BU) R
    AR.N=f ⁻¹' A.N ∧ AR.E=A.E.map (f ⁻¹' ·) ∧
      ∀ H : Set X,strictAlong R ((Subtype.val : U → X) ⁻¹' H)=f ⁻¹' strictAlong S H := by
  let M := geometricTemplate N born
  let NU := (Subtype.val : U → X) ⁻¹' N
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let MU := geometricTemplate (X := CMfd.of (n := n) U) NU BU
  let f : Z → Y := (Subtype.val : openPreimage S U → Y) ∘ e
  have hcM : M.ideal.IsCoherent := IdealWeightPowers.isCoherent_unitIdeal
  have hhol : ∀ x g,M.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcM hg
  have hPull : MarkedIdeal.pullback (Subtype.val : U → X) M=MU :=
    template_pullback (Y := CMfd.of (n := n) U) (Subtype.val : U → X) N born
  have hSU := isGeoTestTower_restrict U hN hcM S hS
  rw [hPull] at hSU
  have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hIso := IsTowerIso.geoTransformAlong_eq
    (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) U)
    (Y := CMfd.of (n := n) (openPreimage S U)) (Y' := Z)
    (T := restrict U S) (T' := R) (χ := e) (𝔪 := MU)
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) hNU IdealWeightPowers.isCoherent_unitIdeal he hSU
  have hId : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) MU=MU := by
    simp [MU,MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal]
  have hRestrict := HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol M hhol U S
  rw [hPull] at hRestrict
  rw [hId,hRestrict] at hIso
  have hComp := HironakaActualRawRecordPullbacks.marked_pullback_comp_hhol
    (J := geoTransformAlong M S)
    (HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong M hhol S)
    (a := (Subtype.val : openPreimage S U → Y)) (b := e) (d := f)
    contMDiff_subtype_val e.contMDiff (fun _ => rfl)
  have hMarked := hIso.trans hComp
  refine ⟨?_,?_,?_⟩
  · simpa only [MarkedIdeal.pullback] using congrArg (fun K : MarkedIdeal n Z => K.N) hMarked
  · simpa only [MarkedIdeal.pullback] using congrArg (fun K : MarkedIdeal n Z => K.E) hMarked
  · intro H
    have h := he.strictAlong_eq ((Subtype.val : U → X) ⁻¹' H)
    change strictAlong R ((Subtype.val : U → X) ⁻¹' H)=
      e ⁻¹' strictAlong (restrict U S) ((Subtype.val : U → X) ⁻¹' H) at h
    rw [strictAlong_restrict] at h
    exact h

private theorem current_member_record (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (i : Fin old.length) :
    let A := geoTransformAlong (geometricTemplate N born) S
    chronologicalMarked (retainedResidualMarked N old born i) S=
      (⟨A.N,A.E,nonmonomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong S (old.get i)))) A.E,0⟩ : MarkedIdeal n Y) := by
  let j : Fin (old.map (strictAlong S)).length := ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
  have hIndex : Fin.cast (List.length_map (f := strictAlong S) (as := old)).symm i=j := by
    apply Fin.ext
    rfl
  have h := retained_seed_eq_chronological_current hn hN hE hTr hdense S hS hFull i
  rw [hIndex] at h
  have hGet : (old.map (strictAlong S)).get j=strictAlong S (old.get i) := by simp [j]
  simpa only [retainedResidualMarked,oldResidualPart,oldTraceIdeal,hGet] using h.symm

private theorem coherent_relative_product {N : Set X} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X)) (hc : ∀ I ∈ L,I.IsCoherent) :
    (relativeIdealListProduct N L).IsCoherent := by
  induction L with
  | nil => exact IdealWeightPowers.isCoherent_unitIdeal
  | cons I L ih =>
    exact isCoherent_restrictOn (isCoherent_mul (hc I (by simp))
      (ih (fun J hJ => hc J (List.mem_cons_of_mem I hJ))))
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)

private theorem canonical_product_coherent (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ) :
    (canonicalProductMarked N old born q).ideal.IsCoherent := by
  apply coherent_relative_product hN
  intro I hI
  obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
  exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.1

private theorem open_iso_local_inverse (U : Opens X)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (z : Y) :
    ∃ ψ : X → Y,IsLocalInverseAt n ((Subtype.val : U → X) ∘ e) ψ z := by
  let ψ := e.symm ∘ openInv U (e z)
  have hInv := isLocalInverseAt_val (n := n) U (e z)
  refine ⟨ψ,⟨?_,?_,?_,?_⟩⟩
  · exact Eventually.of_forall fun w =>
      ((contMDiff_subtype_val.comp e.contMDiff) w).mdifferentiableAt (by simp)
  · filter_upwards [hInv.mdiff_inv] with x hx
    exact ((e.symm.contMDiff _).mdifferentiableAt (by simp)).comp x hx
  · filter_upwards [e.contMDiff.continuous.continuousAt.eventually hInv.left_inv] with w hw
    change e.symm (openInv U (e z) ((e w).val))=w
    rw [hw,e.symm_apply_apply]
  · filter_upwards [hInv.right_inv] with x hx
    change (e (e.symm (openInv U (e z) x))).val=x
    rw [e.apply_symm_apply]
    exact hx

private theorem ordinary_order_pullback_open_iso (hn : 0 < n) {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x) (U : Opens X)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (z : Y) :
    ordinaryTraceOrder (((Subtype.val : U → X) ∘ e) ⁻¹' N)
      (GermIdeal.pullback (m := n) ((Subtype.val : U → X) ∘ e) I) z=
      ordinaryTraceOrder N I (e z).val := by
  exact NonmonomialOrderLocal.nmOrd_pullback_of_local hn
    (fun y => open_iso_local_inverse U e y) (ordinaryTraceMarked_isWellFormed hN hI) hnz z

private theorem count_pullback_open_iso {m : ℕ} (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent) (U : Opens X)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (z : Y) :
    actualDistinctProperCount (fun i => GermIdeal.pullback (m := n) ((Subtype.val : U → X) ∘ e) (F i)) z=
      actualDistinctProperCount F (e z).val := by
  let FV := fun i => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F i)
  have hFam : (fun i => GermIdeal.pullback (m := n) ((Subtype.val : U → X) ∘ e) (F i))=
      (fun i => GermIdeal.pullback (m := n) e (FV i)) := by
    funext i
    exact GermIdealTotalTransform.pullback_comp contMDiff_subtype_val e.contMDiff (hc i)
  rw [hFam]
  exact (actual_distinct_proper_count_biholo (X := CMfd.of (n := n) U) e FV
    (fun i => GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (hc i)) z).trans
      (HironakaSharpActualDistinctCountOpenNaturality.actual_distinct_proper_count_open F hc U (e z))

private theorem family_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S) :
    let A := geoTransformAlong (geometricTemplate N born) S
    ∀ i : Fin old.length,
      let J := (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
      J.IsCoherent ∧ (∀ x ∈ A.N,IsNonzeroAlongAt A.N J x) ∧
        ∀ x ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f x ∧ ∀ g,J.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) A.N (·=f) x g := by
  dsimp only
  intro i
  have hSeed := retainedResidualMarked_geometry hn hN hE hTr hdense i
  obtain ⟨hw,hnz,hpr⟩ := chronologicalMarked_actual_geometry hn
    (retainedResidualMarked N old born i) hSeed.1 rfl hSeed.2.1 hSeed.2.2 S hS
  have hCurrentN := (chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) S).1
  rw [hCurrentN] at hnz hpr
  exact ⟨hw.isCoherent,hnz,hpr⟩

private theorem product_ideal (N : Set X) (old born : List (Set X))
    (q : ℕ) (S : BlowupTower X Y) :
    (retainedProductMarked N old born q S).ideal=
      relativeIdealListProduct (geoTransformAlong (geometricTemplate N born) S).N
        (List.ofFn fun i : Fin old.length =>
          (chronologicalMarked (retainedResidualMarked N old born i) S).ideal) := by
  unfold retainedProductMarked
  dsimp only
  congr 1
  conv_lhs => rw [←List.ofFn_get old,List.map_ofFn]
  rfl

private theorem product_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S) :
    let A := geoTransformAlong (geometricTemplate N born) S
    (retainedProductMarked N old born q S).ideal.IsCoherent ∧
      (∀ y ∈ A.N,IsNonzeroAlongAt A.N (retainedProductMarked N old born q S).ideal y) ∧
      (∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,(retainedProductMarked N old born q S).ideal.mem y g ↔
          HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g) ∧
      ∀ y ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q S).ideal y=
        ∑ i : Fin old.length,ordinaryTraceOrder A.N
          (chronologicalMarked (retainedResidualMarked N old born i) S).ideal y := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hWF : (geometricTemplate N born).IsWellFormed := ⟨hN,IdealWeightPowers.isCoherent_unitIdeal,hBorn,hTr⟩
  have hCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF S hS
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
  have hFam := family_geometry hn hN hE hTr hdense S hS
  have hList : ∀ I ∈ List.ofFn F,I.IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate N born) S).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate N born) S).N I y) ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate N born) S).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,I.mem y g ↔ HolomorphicAt n g y ∧
          IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate N born) S).N (·=f) y g := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact hFam i
  have hp := relativeIdealListProduct_actual_geometry hCurrent.isClosedSubmanifold_N (List.ofFn F)
    (fun I hI => (hList I hI).1) (fun I hI => (hList I hI).2.1) (fun I hI => (hList I hI).2.2)
  dsimp only
  rw [product_ideal]
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  intro y hy
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hp.2.2.2 y hy


/-- Derived WHOLE chronological marked-record comparison along the ACTUAL
extension isomorphism.  No row/product comparison is an input. -/
private theorem actual_retained_rows_open_tower_iso (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (hR : IsGeoTestTower (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
      (born.map ((Subtype.val : U → X) ⁻¹' ·))) R)
    (hFullR : IsGeoTestTower (geometricTemplate (univ : Set U)
      ((old.map ((Subtype.val : U → X) ⁻¹' ·)) ++ (born.map ((Subtype.val : U → X) ⁻¹' ·)))) R)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e) :
    let f : Z → Y := (Subtype.val : openPreimage S U → Y) ∘ e
    let NU := (Subtype.val : U → X) ⁻¹' N
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    (∀ i : Fin old.length,
      let iU : Fin OU.length := ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
      MarkedIdeal.pullback f (chronologicalMarked (retainedResidualMarked N old born i) S)=
        chronologicalMarked (retainedResidualMarked NU OU BU iU) R) ∧
      ∀ q : ℕ,MarkedIdeal.pullback f (retainedProductMarked N old born q S)=
        retainedProductMarked NU OU BU q R := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let A := geoTransformAlong (geometricTemplate N born) S
  let O := old.map (strictAlong S)
  let Ω := openPreimage S U
  let NV := (Subtype.val : Ω → Y) ⁻¹' A.N
  let OV := O.map ((Subtype.val : Ω → Y) ⁻¹' ·)
  let BV := A.E.map ((Subtype.val : Ω → Y) ⁻¹' ·)
  let AR := geoTransformAlong (geometricTemplate NU BU) R
  let f : Z → Y := (Subtype.val : Ω → Y) ∘ e
  have hGeoU := open_geometry hN hE hTr hdense U
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFullS
  have hGeoV := open_geometry hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 Ω
  have hTuple := tuple_open_iso hN born U S hS R e he
  have hCarrier : e ⁻¹' NV=AR.N := hTuple.1.symm
  have hBorn : BV.map (e ⁻¹' ·)=AR.E := by
    simp only [BV,List.map_map]
    exact hTuple.2.1.symm
  have hOld : OV.map (e ⁻¹' ·)=OU.map (strictAlong R) := by
    simp only [OV,O,OU,List.map_map]
    apply List.map_congr_left
    intro H _hH
    exact (hTuple.2.2 H).symm
  refine ⟨?_,?_⟩
  · intro i
    let iU : Fin OU.length := ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
    let iS : Fin O.length := Fin.cast (List.length_map (f := strictAlong S) (as := old)).symm i
    let iV : Fin OV.length := ⟨iS.val,by simpa only [OV,List.length_map] using iS.isLt⟩
    let OZ := OV.map (e ⁻¹' ·)
    let iZ : Fin OZ.length := ⟨iV.val,by simpa only [OZ,List.length_map] using iV.isLt⟩
    have hSource : retainedResidualMarked A.N O A.E iS=
        chronologicalMarked (retainedResidualMarked N old born i) S :=
      retained_seed_eq_chronological_current hn hN hE hTr hdense S hS hFullS i
    have hOpen := retainedResidualMarked_pullback_open hn hRec.1 hRec.2.1
      hRec.2.2.1 hRec.2.2.2.1 Ω iS
    rw [hSource] at hOpen
    have hBi := retained_seed_pullback_biholo (X := CMfd.of (n := n) Ω)
      (Y := Z) hn hGeoV.1 hGeoV.2.1 hGeoV.2.2.1 hGeoV.2.2.2 e iV
    have hSelected : OZ.get iZ=strictAlong R (OU.get iU) := by
      have hGetZ : OZ.get iZ=f ⁻¹' strictAlong S (old.get i) := by
        simp [OZ,OV,O,iZ,iV,iS,f]
        rfl
      have hGetU : OU.get iU=(Subtype.val : U → X) ⁻¹' old.get i := by simp [OU,iU]
      rw [hGetZ,hGetU]
      exact (hTuple.2.2 (old.get i)).symm
    have hFinal : retainedResidualMarked (e ⁻¹' NV) OZ (BV.map (e ⁻¹' ·)) iZ=
        chronologicalMarked (retainedResidualMarked NU OU BU iU) R := by
      rw [current_member_record (X := CMfd.of (n := n) U) hn hGeoU.1 hGeoU.2.1
        hGeoU.2.2.1 hGeoU.2.2.2 R hR hFullR iU]
      simp only [retainedResidualMarked,oldResidualPart,oldTraceIdeal,hSelected,hCarrier,hBorn]
      rfl
    have hSeedGeo := retainedResidualMarked_geometry hn hRec.1 hRec.2.1
      hRec.2.2.1 hRec.2.2.2.1 iS
    rw [hSource] at hSeedGeo
    have hComp := HironakaActualRawRecordPullbacks.marked_pullback_comp_hhol
      (J := chronologicalMarked (retainedResidualMarked N old born i) S)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSeedGeo.1.isCoherent hg)
      (a := (Subtype.val : Ω → Y)) (b := e) (d := f)
      contMDiff_subtype_val e.contMDiff (fun _ => rfl)
    exact hComp.symm.trans
      ((congrArg (fun K : MarkedIdeal n Ω => MarkedIdeal.pullback e K) hOpen).trans (hBi.trans hFinal))
  · intro q
    have hCanon := retainedProductMarked_eq_canonical hn hN hE hTr hdense q S hS hFullS
    rw [hCanon]
    have hOpen := canonicalProductMarked_pullback_open hn hRec.1 hRec.2.1
      hRec.2.2.1 hRec.2.2.2.1 q Ω
    have hBi := canonical_product_pullback_biholo (X := CMfd.of (n := n) Ω)
      (Y := Z) hn hGeoV.1 hGeoV.2.1 hGeoV.2.2.1 hGeoV.2.2.2 q e
    have hFinal : canonicalProductMarked (e ⁻¹' NV) (OV.map (e ⁻¹' ·)) (BV.map (e ⁻¹' ·)) q=
        retainedProductMarked NU OU BU q R := by
      rw [hCarrier,hOld,hBorn]
      exact (retainedProductMarked_eq_canonical (X := CMfd.of (n := n) U)
        hn hGeoU.1 hGeoU.2.1 hGeoU.2.2.1 hGeoU.2.2.2 q R hR hFullR).symm
    have hc := canonical_product_coherent hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 q
    have hComp := HironakaActualRawRecordPullbacks.marked_pullback_comp_hhol
      (J := canonicalProductMarked A.N O A.E q)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg)
      (a := (Subtype.val : Ω → Y)) (b := e) (d := f)
      contMDiff_subtype_val e.contMDiff (fun _ => rfl)
    exact hComp.symm.trans
      ((congrArg (fun K : MarkedIdeal n Ω => MarkedIdeal.pullback e K) hOpen).trans (hBi.trans hFinal))

private theorem actual_retained_orders_and_count_open_tower_iso (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (hR : IsGeoTestTower (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
      (born.map ((Subtype.val : U → X) ⁻¹' ·))) R)
    (hFullR : IsGeoTestTower (geometricTemplate (univ : Set U)
      ((old.map ((Subtype.val : U → X) ⁻¹' ·)) ++ (born.map ((Subtype.val : U → X) ⁻¹' ·)))) R)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate N born) S
    let AR := geoTransformAlong (geometricTemplate NU BU) R
    let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
    let G := fun i : Fin old.length =>
      let iU : Fin OU.length := ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
      (chronologicalMarked (retainedResidualMarked NU OU BU iU) R).ideal
    ∀ z : Z,
      (∀ i,ordinaryTraceOrder AR.N (G i) z=ordinaryTraceOrder A.N (F i) (e z).val) ∧
      actualDistinctProperCount G z=actualDistinctProperCount F (e z).val ∧
      ∀ q : ℕ,ordinaryTraceOrder AR.N (retainedProductMarked NU OU BU q R).ideal z=
        ordinaryTraceOrder A.N (retainedProductMarked N old born q S).ideal (e z).val := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let A := geoTransformAlong (geometricTemplate N born) S
  let AR := geoTransformAlong (geometricTemplate NU BU) R
  let Ω := openPreimage S U
  let f : Z → Y := (Subtype.val : Ω → Y) ∘ e
  let ι : Fin old.length → Fin OU.length := fun i => ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
  let G := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked NU OU BU (ι i)) R).ideal
  have hWhole := actual_retained_rows_open_tower_iso hn hN hE hTr hdense U S hS hFullS R hR hFullR e he
  have hTuple := tuple_open_iso hN born U S hS R e he
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFullS
  have hFam := family_geometry hn hN hE hTr hdense S hS
  have hI (i : Fin old.length) : GermIdeal.pullback (m := n) f (F i)=G i := by
    simpa only [MarkedIdeal.pullback] using congrArg (fun K : MarkedIdeal n Z => K.ideal) (hWhole.1 i)
  dsimp only
  intro z
  refine ⟨?_,?_,?_⟩
  · intro i
    have h := ordinary_order_pullback_open_iso (X := Y) (Y := Z) hn
      hRec.1 (hFam i).1 (hFam i).2.1 Ω e z
    rw [←hTuple.1,hI i] at h
    exact h
  · have hFun : (fun i => GermIdeal.pullback (m := n) f (F i))=G := funext hI
    have h := count_pullback_open_iso F (fun i => (hFam i).1) Ω e z
    rw [hFun] at h
    exact h
  · intro q
    have hp := product_geometry hn hN hE hTr hdense q S hS
    have hIdeal : GermIdeal.pullback (m := n) f (retainedProductMarked N old born q S).ideal=
        (retainedProductMarked NU OU BU q R).ideal := by
      simpa only [MarkedIdeal.pullback] using congrArg (fun K : MarkedIdeal n Z => K.ideal) (hWhole.2 q)
    have h := ordinary_order_pullback_open_iso (X := Y) (Y := Z) hn hRec.1 hp.1 hp.2.1 Ω e z
    rw [←hTuple.1,hIdeal] at h
    exact h


private theorem chronological_normalized_empty (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hNorm : restrictOn n M.N M.ideal=M.ideal) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),ResolutionInvariantExt.IsEmptyTower T →
      (chronologicalMarked M T).N=T.proj ⁻¹' M.N ∧
      (chronologicalMarked M T).ideal=GermIdeal.pullback (m := n) T.proj M.ideal
  | _,.refl,_ => by
    refine ⟨rfl,?_⟩
    exact (BlowupControlledTransform.pullback_id hI).symm
  | _,.step T C π hπ,hEmpty => by
    obtain ⟨hEmpty,rfl⟩ := hEmpty
    obtain ⟨hNT,hIT⟩ := chronological_normalized_empty M hN hI hNorm T hEmpty
    obtain ⟨e,hep⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection T hEmpty
    have hef : (e : _ → X)=T.proj := funext hep
    let A := chronologicalMarked M T
    have hAN : IsClosedSubmanifold n A.N := by
      change IsClosedSubmanifold n (chronologicalMarked M T).N
      rw [hNT,←hef]
      exact MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
        e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply hN
    have hAI : A.ideal.IsCoherent := by
      change (chronologicalMarked M T).ideal.IsCoherent
      rw [hIT]
      exact GermIdealPullbackCalculus.isCoherent_pullback T.contMDiff_proj hI
    have hNormA : restrictOn n A.N A.ideal=A.ideal := by
      change restrictOn n (chronologicalMarked M T).N (chronologicalMarked M T).ideal=_
      rw [hNT,hIT,←hef,←restrictOn_pullback_biholo e hN hI,hNorm]
    refine ⟨?_,?_⟩
    · change closure (π ⁻¹' (A.N \ ∅))=(T.proj ∘ π) ⁻¹' M.N
      rw [Set.sdiff_empty,(hAN.1.preimage hπ.contMDiff.continuous).closure_eq]
      change π ⁻¹' (chronologicalMarked M T).N=_
      rw [hNT]
      rfl
    · change HironakaSharpActualChronologicalStrictStep.nextRelativeStrict A.N A.ideal ∅ π=
        GermIdeal.pullback (m := n) (T.proj ∘ π) M.ideal
      rw [nextRelativeStrict_empty hAN hAI hNormA hπ]
      change GermIdeal.pullback (m := n) π (chronologicalMarked M T).ideal=_
      rw [hIT,←GermIdealTotalTransform.pullback_comp T.contMDiff_proj hπ.contMDiff hI]

/-- Every literal born position of an actual empty history is retained.
The normalized whole ideal, rather than only its restriction-equivalence
class, is pulled back by the actual projection. -/
private theorem chronological_whole_empty (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hNorm : restrictOn n M.N M.ideal=M.ideal) (hd : M.d=0)
    (hE : ∀ H ∈ M.E,IsClosed H)
    (T : BlowupTower X Y) (hEmpty : ResolutionInvariantExt.IsEmptyTower T) :
    chronologicalMarked M T=
      ({MarkedIdeal.pullback T.proj M with
        E:=M.E.map (T.proj ⁻¹' ·) ++ List.replicate T.length ∅} : MarkedIdeal n Y) := by
  obtain ⟨hNT,hIT⟩ := chronological_normalized_empty M hN hI hNorm T hEmpty
  have hET := (chronologicalMarked_geometric_fields M T).2.trans
    (HironakaOriginalBoundaryCanonicalPrincipalization.boundary_of_all_empty_tower
      (geometricTemplate M.N M.E) hE T hEmpty)
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hNT hET hIT
    ((chronologicalMarked_zero_mark M hd T).trans hd.symm)

private theorem geometric_carrier_empty {N : Set X} (hN : IsClosedSubmanifold n N)
    (born : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),ResolutionInvariantExt.IsEmptyTower T →
      (geoTransformAlong (geometricTemplate N born) T).N=T.proj ⁻¹' N
  | _,.refl,_ => rfl
  | _,.step T C π hπ,hEmpty => by
    obtain ⟨hEmpty,rfl⟩ := hEmpty
    have hNT := geometric_carrier_empty hN born T hEmpty
    obtain ⟨e,hep⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection T hEmpty
    have hef : (e : _ → X)=T.proj := funext hep
    have hAN : IsClosedSubmanifold n (geoTransformAlong (geometricTemplate N born) T).N := by
      rw [hNT,←hef]
      exact MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
        e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply hN
    change closure (π ⁻¹' ((geoTransformAlong (geometricTemplate N born) T).N \ ∅))=_
    rw [Set.sdiff_empty,(hAN.1.preimage hπ.contMDiff.continuous).closure_eq,hNT]
    rfl

private theorem retained_row_whole_empty (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (T : BlowupTower X Y) (hEmpty : ResolutionInvariantExt.IsEmptyTower T) (i : Fin old.length) :
    chronologicalMarked (retainedResidualMarked N old born i) T=
      ({MarkedIdeal.pullback T.proj (retainedResidualMarked N old born i) with
        E:=born.map (T.proj ⁻¹' ·) ++ List.replicate T.length ∅} : MarkedIdeal n Y) := by
  have hSeed := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hNorm : restrictOn n N (oldResidualPart N old born i)=oldResidualPart N old born i := by
    ext x g
    exact HironakaSharpActualControlledRelativeSaturation.restrictOn_colonAlong_mem_iff N (oldTraceIdeal N old i)
      (monomialPartAlong n N (oldTraceIdeal N old i) born) (fun _ hg => hg.1) g
  exact chronological_whole_empty (retainedResidualMarked N old born i) hN hSeed.1.isCoherent
    hNorm rfl (fun H hH => hE.1 H (List.mem_append_right old hH)) T hEmpty

private theorem retained_orders_count_empty (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (T : BlowupTower X Y) (hEmpty : ResolutionInvariantExt.IsEmptyTower T) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal
    ∀ y : Y,
      (∀ i,ordinaryTraceOrder A.N (F i) y=ordinaryTraceOrder N (oldResidualPart N old born i) (T.proj y)) ∧
      actualDistinctProperCount F y=actualDistinctProperCount (oldResidualPart N old born) (T.proj y) := by
  obtain ⟨e,hep⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection T hEmpty
  have hef : (e : Y → X)=T.proj := funext hep
  have hCarrier := geometric_carrier_empty hN born T hEmpty
  let F := fun i : Fin old.length => oldResidualPart N old born i
  have hFam := fun i => retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hI : (fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal)=
      fun i => GermIdeal.pullback (m := n) e (F i) := by
    funext i
    have hWhole := congrArg (fun M : MarkedIdeal n Y => M.ideal)
      (retained_row_whole_empty hn hN hE hTr hdense T hEmpty i)
    simpa only [MarkedIdeal.pullback,retainedResidualMarked,F,hef] using hWhole
  dsimp only
  rw [hI,hCarrier,←hef]
  intro y
  refine ⟨?_,actual_distinct_proper_count_biholo e F (fun i => (hFam i).1.isCoherent) y⟩
  intro i
  rw [congrFun hI i]
  exact NonmonomialOrderLocal.nmOrd_pullback_diffeo hn e
    (ordinaryTraceMarked_isWellFormed hN (hFam i).1.isCoherent) (hFam i).2.1 y

private theorem retained_orders_count_on_empty_restriction (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (U : Opens X) (hEmpty : ResolutionInvariantExt.IsEmptyTower (restrict U T)) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal
    ∀ y : Y,T.proj y ∈ U →
      (∀ i,ordinaryTraceOrder A.N (F i) y=ordinaryTraceOrder N (oldResidualPart N old born i) (T.proj y)) ∧
      actualDistinctProperCount F y=actualDistinctProperCount (oldResidualPart N old born) (T.proj y) := by
  let Ω := openPreimage T U
  let R := restrict U T
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let A := geoTransformAlong (geometricTemplate N born) T
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal
  let G := fun i : Fin old.length => oldResidualPart N old born i
  have hGeoU := open_geometry hN hE hTr hdense U
  have hR := isGeoTestTower_restrict U hN IdealWeightPowers.isCoherent_unitIdeal T hT
  rw [template_pullback (Y := CMfd.of (n := n) U) (Subtype.val : U → X) N born] at hR
  have hFullR := isGeoTestTower_restrict U isClosedSubmanifold_univ
    IdealWeightPowers.isCoherent_unitIdeal T hFull
  rw [template_pullback (Y := CMfd.of (n := n) U) (Subtype.val : U → X)
    (univ : Set X) (old ++ born)] at hFullR
  simp only [Set.preimage_univ,List.map_append] at hFullR
  let ρ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Ω ∞
  have hWhole := actual_retained_rows_open_tower_iso hn hN hE hTr hdense U
    T hT hFull R hR hFullR ρ (IsTowerIso.refl_self R)
  have hTuple := tuple_open_iso hN born U T hT R ρ (IsTowerIso.refl_self R)
  obtain ⟨β,hβ⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection R hEmpty
  have hβfun : (β : Ω → U)=R.proj := funext hβ
  let f : Ω → X := (Subtype.val : U → X) ∘ β
  have hCarrier : (Subtype.val : Ω → Y) ⁻¹' A.N=f ⁻¹' N := by
    have hc := geometric_carrier_empty hGeoU.1 BU R hEmpty
    rw [hTuple.1] at hc
    change (Subtype.val : Ω → Y) ⁻¹' A.N=R.proj ⁻¹' NU at hc
    simpa only [f,hβfun,NU,Set.preimage_comp] using hc
  have hSource (i : Fin old.length) := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hFinal := family_geometry hn hN hE hTr hdense T hT
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense T hT hFull
  have hI (i : Fin old.length) : GermIdeal.pullback (m := n) (Subtype.val : Ω → Y) (F i)=
      GermIdeal.pullback (m := n) f (G i) := by
    let iU : Fin OU.length := ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
    have hOpen := congrArg (fun M : MarkedIdeal n U => M.ideal)
      (retainedResidualMarked_pullback_open hn hN hE hTr hdense U i)
    have hEmptyI := congrArg (fun M : MarkedIdeal n Ω => M.ideal)
      (retained_row_whole_empty (X := CMfd.of (n := n) U) hn hGeoU.1 hGeoU.2.1
        hGeoU.2.2.1 hGeoU.2.2.2 R hEmpty iU)
    have hLocal := congrArg (fun M : MarkedIdeal n Ω => M.ideal) (hWhole.1 i)
    change GermIdeal.pullback (m := n) (Subtype.val : Ω → Y) (F i)=
      (chronologicalMarked (retainedResidualMarked NU OU BU iU) R).ideal at hLocal
    rw [hLocal,hEmptyI]
    change GermIdeal.pullback (m := n) R.proj (oldResidualPart NU OU BU iU)=_
    change GermIdeal.pullback (m := n) (Subtype.val : U → X) (G i)=
      oldResidualPart (X := CMfd.of (n := n) U) NU OU BU iU at hOpen
    have hcG : (G i).IsCoherent := (hSource i).1.isCoherent
    rw [←hOpen,←GermIdealTotalTransform.pullback_comp contMDiff_subtype_val R.contMDiff_proj
      hcG,←hβfun]
  have hFam : (fun i => GermIdeal.pullback (m := n) (Subtype.val : Ω → Y) (F i))=
      (fun i => GermIdeal.pullback (m := n) f (G i)) := funext hI
  dsimp only
  intro y hy
  let w : Ω := ⟨y,hy⟩
  have hPoint : (β w).val=T.proj y := by
    rw [hβ]
    exact proj_restrict U T w
  refine ⟨?_,?_⟩
  · intro i
    have hCurrent := ordinary_order_pullback_open_iso (X := Y) (Y := CMfd.of (n := n) Ω) hn hRec.1
      (hFinal i).1 (hFinal i).2.1 Ω ρ w
    change ordinaryTraceOrder (X := CMfd.of (n := n) Ω) ((Subtype.val : Ω → Y) ⁻¹' A.N)
      (GermIdeal.pullback (m := n) (Subtype.val : Ω → Y) (F i)) w=
      ordinaryTraceOrder A.N (F i) y at hCurrent
    have hInitial := ordinary_order_pullback_open_iso (Y := CMfd.of (n := n) Ω) hn hN (hSource i).1.isCoherent
      (hSource i).2.1 U β w
    change ordinaryTraceOrder (X := CMfd.of (n := n) Ω) (f ⁻¹' N) (GermIdeal.pullback (m := n) f (G i)) w=
      ordinaryTraceOrder N (G i) (β w).val at hInitial
    rw [←hCarrier,←hI i,hPoint] at hInitial
    exact hCurrent.symm.trans hInitial
  · have hCurrent := HironakaSharpActualDistinctCountOpenNaturality.actual_distinct_proper_count_open
      F (fun i => (hFinal i).1) Ω w
    have hInitial := count_pullback_open_iso G (fun i => (hSource i).1.isCoherent) U β w
    rw [←hFam,hPoint] at hInitial
    exact hCurrent.symm.trans hInitial

private theorem current_count_reindex {a b : ℕ} (e : Fin a ≃ Fin b)
    (F : Fin a → GermIdeal n X) (G : Fin b → GermIdeal n X)
    (h : ∀ i,G (e i)=F i) (x : X) :
    actualDistinctProperCount F x=actualDistinctProperCount G x := by
  classical
  have hRel : ∀ i j,(actualIdealGermSetoid F x) i j ↔ (actualIdealGermSetoid G x) (e i) (e j) := by
    intro i j
    change (∀ g,(F i).mem x g ↔ (F j).mem x g) ↔
      (∀ g,(G (e i)).mem x g ↔ (G (e j)).mem x g)
    rw [h i,h j]
  let eqQ := Quotient.congr e hRel
  have hProper (i : Fin a) : e i ∈ actualProperPositions G x ↔ i ∈ actualProperPositions F x := by
    simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and,h i]
  have hImage :
      Finset.map eqQ.toEmbedding ((actualProperPositions F x).image (Quotient.mk (actualIdealGermSetoid F x)))=
        (actualProperPositions G x).image (Quotient.mk (actualIdealGermSetoid G x)) := by
    ext c
    constructor
    · intro hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp hc
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_image.mpr ⟨e i,(hProper i).mpr hi,rfl⟩
    · intro hc
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hc
      refine Finset.mem_map.mpr ⟨Quotient.mk _ (e.symm j),?_,?_⟩
      · exact Finset.mem_image.mpr ⟨e.symm j,(hProper _).mp (by simpa using hj),rfl⟩
      · change Quotient.mk _ (e (e.symm j))=Quotient.mk _ j
        rw [e.apply_symm_apply]
  simpa only [actualDistinctProperCount,Finset.card_map] using congrArg Finset.card hImage


private theorem row_nonincrease_of_actual_open_iso (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (hR : IsGeoTestTower (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
      (born.map ((Subtype.val : U → X) ⁻¹' ·))) R)
    (hFullR : IsGeoTestTower (geometricTemplate (univ : Set U)
      ((old.map ((Subtype.val : U → X) ⁻¹' ·)) ++ (born.map ((Subtype.val : U → X) ⁻¹' ·)))) R)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e)
    (hRows : ∀ z ∈ (geoTransformAlong (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
        (born.map ((Subtype.val : U → X) ⁻¹' ·))) R).N,
      ∀ i : Fin (old.map ((Subtype.val : U → X) ⁻¹' ·)).length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
            (born.map ((Subtype.val : U → X) ⁻¹' ·))) R).N
          (chronologicalMarked (retainedResidualMarked ((Subtype.val : U → X) ⁻¹' N)
            (old.map ((Subtype.val : U → X) ⁻¹' ·)) (born.map ((Subtype.val : U → X) ⁻¹' ·)) i) R).ideal z ≤
        ordinaryTraceOrder ((Subtype.val : U → X) ⁻¹' N)
          (oldResidualPart (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
            (old.map ((Subtype.val : U → X) ⁻¹' ·)) (born.map ((Subtype.val : U → X) ⁻¹' ·)) i) (R.proj z)) :
    ∀ y ∈ (geoTransformAlong (geometricTemplate N born) S).N,S.proj y ∈ U →
      ∀ i,ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) S).N
        (chronologicalMarked (retainedResidualMarked N old born i) S).ideal y ≤
          ordinaryTraceOrder N (oldResidualPart N old born i) (S.proj y) := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  have hOrders := actual_retained_orders_and_count_open_tower_iso hn hN hE hTr hdense
    U S hS hFullS R hR hFullR e he
  have hTuple := tuple_open_iso hN born U S hS R e he
  intro y hy hyU i
  let w : openPreimage S U := ⟨y,hyU⟩
  let z := e.symm w
  let iU : Fin OU.length := ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
  have hTarget : (e z).val=y := by simp only [z,e.apply_symm_apply];rfl
  have hz : z ∈ (geoTransformAlong (geometricTemplate NU BU) R).N := by
    rw [hTuple.1]
    change (e z).val ∈ (geoTransformAlong (geometricTemplate N born) S).N
    rwa [hTarget]
  have hCurrent := (hOrders z).1 i
  rw [hTarget] at hCurrent
  have hSeed := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hInitial := ordinary_order_pullback_open_iso (Y := CMfd.of (n := n) U) hn hN
    hSeed.1.isCoherent hSeed.2.1 U (Diffeomorph.refl _ _ ∞) (R.proj z)
  have hOpen := congrArg (fun M : MarkedIdeal n U => M.ideal)
    (retainedResidualMarked_pullback_open hn hN hE hTr hdense U i)
  change GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i)=
    oldResidualPart (X := CMfd.of (n := n) U) NU OU BU iU at hOpen
  change ordinaryTraceOrder (X := CMfd.of (n := n) U) NU
    (GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i)) (R.proj z)=
      ordinaryTraceOrder N (oldResidualPart N old born i) (R.proj z).val at hInitial
  rw [hOpen] at hInitial
  have hProj : (R.proj z).val=S.proj y := by
    have hp := congrArg (Subtype.val : U → X) (he.proj_comm z)
    change (R.proj z).val=((restrict U S).proj (e z)).val at hp
    rw [proj_restrict,hTarget] at hp
    exact hp
  calc
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) S).N
        (chronologicalMarked (retainedResidualMarked N old born i) S).ideal y=
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate NU BU) R).N
        (chronologicalMarked (retainedResidualMarked NU OU BU iU) R).ideal z := hCurrent.symm
    _ ≤ ordinaryTraceOrder NU (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU iU) (R.proj z) :=
      hRows z hz iU
    _=ordinaryTraceOrder N (oldResidualPart N old born i) (R.proj z).val := hInitial
    _=ordinaryTraceOrder N (oldResidualPart N old born i) (S.proj y) := by rw [hProj]

private theorem retained_defect_footprint (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (D : Set X) (hD : IsCompact D)
    (hDefectD : D ⊆ actualFamilyDistinctDefect N (oldResidualPart N old born))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (hOver : RestrictEmptyTower.CentresOver D T) :
    actualFamilyDistinctDefect (geoTransformAlong (geometricTemplate N born) T).N
      (fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal) ⊆
        T.proj ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born) := by
  let A := geoTransformAlong (geometricTemplate N born) T
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal
  let G := oldResidualPart N old born
  intro y hy
  by_cases hyD : T.proj y ∈ D
  · exact hDefectD hyD
  · let O : Opens X := ⟨Dᶜ,hD.isClosed.isOpen_compl⟩
    have hEmpty := RestrictEmptyTower.isEmptyTower_restrict_of_centresOver O
      (Set.disjoint_left.mpr (fun _ hxO hxD => hxO hxD)) T hOver
    have hEq := retained_orders_count_on_empty_restriction hn hN hE hTr hdense T hT hFull O hEmpty y hyD
    have hyN : T.proj y ∈ N := by
      apply MemberInterTowerAlong.strictAlong_subset_preimage T hN.1
      simpa only [N_geoTransformAlong,geometricTemplate] using hy.1
    have hp := product_geometry hn hN hE hTr hdense 0 T hT
    have hp0 := product_geometry hn hN hE hTr hdense 0 (.refl : BlowupTower X X) trivial
    have hProd : ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) y=
        ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn G)) (T.proj y) := by
      calc
        ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) y=
            ordinaryTraceOrder A.N (retainedProductMarked N old born 0 T).ideal y := by
              rw [product_ideal]
        _=∑ i : Fin old.length,ordinaryTraceOrder A.N (F i) y := hp.2.2.2 y hy.1
        _=∑ i : Fin old.length,ordinaryTraceOrder N (G i) (T.proj y) :=
          Finset.sum_congr rfl (fun i _ => hEq.1 i)
        _=ordinaryTraceOrder N (retainedProductMarked N old born 0 (.refl : BlowupTower X X)).ideal
            (T.proj y) := (hp0.2.2.2 (T.proj y) hyN).symm
        _=ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn G)) (T.proj y) := by
          rw [product_ideal]
          rfl
    change T.proj y ∈ N ∧ actualDistinctProperCount G (T.proj y) <
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn G)) (T.proj y)
    refine ⟨hyN,?_⟩
    change y ∈ A.N ∧ actualDistinctProperCount F y <
      ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) y at hy
    rw [hEq.2,hProd] at hy
    exact hy.2

private theorem exists_current_profile_window_block (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (U : Opens X) (D : Set X) (hD : IsCompact D) (hDU : D ⊆ U)
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ U,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCount : ∀ x ∈ U,actualDistinctProperCount (oldResidualPart N old born) x < q)
    (hCos : (MarkedIdeal.pullback (Subtype.val : U → X) (canonicalProductMarked N old born q)).cosupp=
      (Subtype.val : U → X) ⁻¹' D) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N born) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) Q ∧
      CurrentSharpCentres N (old ++ born) Q ∧ RestrictEmptyTower.CentresOver D Q ∧
      IsGeoTestTower (canonicalProductMarked N old born q) Q ∧
      (∀ k : ℕ,
        let P := BlowupTowerSplit.head Q k
        let A := geoTransformAlong (geometricTemplate N born) P
        ∀ y ∈ A.N,∀ i,ordinaryTraceOrder A.N
          (chronologicalMarked (retainedResidualMarked N old born i) P).ideal y ≤
            ordinaryTraceOrder N (oldResidualPart N old born i) (P.proj y)) ∧
      (∀ k : ℕ,
        let P := BlowupTowerSplit.head Q k
        actualFamilyDistinctDefect (geoTransformAlong (geometricTemplate N born) P).N
          (fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) P).ideal) ⊆
            P.proj ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born)) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate N born) Q).N,Q.proj y ∈ U →
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) Q).N
          (retainedProductMarked N old born q Q).ideal y < q) ∧
      IsEquivariant N ((U : Set X) :: (old ++ born)) Q := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let pU : Fin OU.length → ℕ := fun i => profile ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
  let M := canonicalProductMarked N old born q
  let MU := canonicalProductMarked (X := CMfd.of (n := n) U) NU OU BU q
  have hGeoU := open_geometry hN hE hTr hdense U
  have hOpen := canonicalProductMarked_pullback_open hn hN hE hTr hdense q U
  let ι : Fin OU.length ≃ Fin old.length := finCongr (List.length_map _)
  have hSame : ∀ i,pU i=profile (ι i) := by
    intro i
    apply congrArg profile
    apply Fin.ext
    rfl
  have hSumU : ∑ i,pU i=q := by
    calc
      ∑ i,pU i=∑ i,profile (ι i) := Finset.sum_congr rfl (fun i _ => hSame i)
      _=∑ i,profile i := ι.sum_comp profile
      _=q := hsum
  have hSeed (i : Fin old.length) := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hRow (i : Fin old.length) :
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i)=
        oldResidualPart (X := CMfd.of (n := n) U) NU OU BU
          ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩ :=
    congrArg (fun L : MarkedIdeal n U => L.ideal)
      (retainedResidualMarked_pullback_open hn hN hE hTr hdense U i)
  have hOrdU : ∀ x ∈ NU,∀ i,ordinaryTraceOrder NU
      (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU i) x ≤ pU i := by
    intro x _hx i
    let j : Fin old.length := ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩
    have hIndex : (⟨j.val,by simpa only [OU,List.length_map] using j.isLt⟩ : Fin OU.length)=i := by
      apply Fin.ext
      rfl
    have hh := ordinary_order_pullback_open_iso (Y := CMfd.of (n := n) U) hn hN
      (hSeed j).1.isCoherent (hSeed j).2.1 U (Diffeomorph.refl _ _ ∞) x
    change ordinaryTraceOrder (X := CMfd.of (n := n) U) NU
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born j)) x=
        ordinaryTraceOrder N (oldResidualPart N old born j) x.val at hh
    rw [hRow j,hIndex] at hh
    exact hh.trans_le (hOrd x.val x.property j)
  have hCountU : ∀ x ∈ NU,ordinaryTraceOrder NU MU.ideal x=q →
      actualDistinctProperCount (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU) x < q := by
    intro x _hx _hTop
    have hc := HironakaSharpActualDistinctCountOpenNaturality.actual_distinct_proper_count_open
      (oldResidualPart N old born) (fun i => (hSeed i).1.isCoherent) U x
    have hF : (fun i => GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i))=
        fun i : Fin old.length => oldResidualPart (X := CMfd.of (n := n) U) NU OU BU
          ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩ := funext hRow
    rw [hF] at hc
    have hNative : actualDistinctProperCount (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU) x=
        actualDistinctProperCount (oldResidualPart N old born) x.val := by
      have hReindex := current_count_reindex (X := CMfd.of (n := n) U) ι.symm
        (fun i : Fin old.length => oldResidualPart (X := CMfd.of (n := n) U) NU OU BU
          ⟨i.val,by simpa only [OU,List.length_map] using i.isLt⟩)
        (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU)
        (fun i => congrArg (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU) (Fin.ext rfl)) x
      exact hReindex.symm.trans hc
    exact hNative.trans_lt (hCount x.val x.property)
  have hCosU : MU.cosupp=(Subtype.val : U → X) ⁻¹' D := by
    exact (congrArg (fun L : MarkedIdeal n U => L.cosupp) hOpen).symm.trans hCos
  have hCompactU : IsCompact MU.cosupp := by
    rw [hCosU]
    apply Subtype.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset (show D ⊆ Set.range (Subtype.val : U → X) from
      fun x hx => ⟨⟨x,hDU hx⟩,rfl⟩)]
    exact hD
  obtain ⟨Z,R,hR,hFullR,hSharpR,hResR,hOverR,hHeadsR,hExitR,hEquivR⟩ :=
    exists_actual_retained_boundary_profile_q_exit_equivariant (X := CMfd.of (n := n) U) hn hGeoU.1 hGeoU.2.1
      hGeoU.2.2.1 hGeoU.2.2.2 pU q hq hSumU hOrdU hCompactU hCountU
  have hOverD : RestrictEmptyTower.CentresOver ((Subtype.val : U → X) ⁻¹' D) R := by
    rw [←hCosU]
    exact hOverR
  have hFullPull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X)
      (geometricTemplate (univ : Set X) (old ++ born))) R := by
    rw [template_pullback (Y := CMfd.of (n := n) U) (Subtype.val : U → X)
      (univ : Set X) (old ++ born)]
    simpa only [Set.preimage_univ,List.map_append] using hFullR
  have hMPull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) R := by
    rw [hOpen]
    exact hResR.1
  have hcM : M.ideal.IsCoherent := canonical_product_coherent hn hN hE hTr hdense q
  have hIdealM : M.ideal=relativeIdealListProduct N (List.ofFn (oldResidualPart N old born)) := by
    change relativeIdealListProduct N (canonicalResidualFamily N old born)=_
    congr 1
    unfold canonicalResidualFamily
    conv_lhs => rw [←List.ofFn_get old,List.map_ofFn]
    rfl
  have hDefectD : D ⊆ actualFamilyDistinctDefect N (oldResidualPart N old born) := by
    intro x hx
    let xU : U := ⟨x,hDU hx⟩
    have hxCos : xU ∈ (MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp := by
      change xU ∈ (MarkedIdeal.pullback (Subtype.val : U → X) (canonicalProductMarked N old born q)).cosupp
      rw [hCos]
      exact hx
    rw [cosupp_pullback_val M (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcM hg) U] at hxCos
    have hxN : x ∈ N := M.cosupp_subset_N hxCos
    have hp0 := product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
    have hM0 : retainedProductMarked N old born q (.refl : BlowupTower X X)=M := by
      simpa [geometricTemplate,geoTransformAlong,strictAlong] using
        (retainedProductMarked_eq_canonical hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial trivial)
    have hNz : ∀ z ∈ N,IsNonzeroAlongAt N M.ideal z := by
      simpa only [hM0,geoTransformAlong,geometricTemplate] using hp0.2.1
    have hxOrder := (ordinaryTraceOrder_cosupport_iff hN hcM hNz hxN q).mp hxCos
    change x ∈ N ∧ actualDistinctProperCount (oldResidualPart N old born) x <
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn (oldResidualPart N old born))) x
    rw [←hIdealM]
    exact ⟨hxN,(hCount x (hDU hx)).trans_le hxOrder⟩
  have hSharpPull : CurrentSharpCentres NU ((old ++ born).map ((Subtype.val : U → X) ⁻¹' ·)) R := by
    simpa only [List.map_append] using hSharpR
  obtain ⟨Y,Q,hFullQ,hMQ,hSharpQ,hOverQ,e,he,_hLength,_hProj⟩ :=
    HironakaCompactFootprintSharpExtension.exists_current_sharp_joint_test_extension
      N (old ++ born) M hN hcM U D hD hDU R hOverD hFullPull hMPull hSharpPull
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hwM : M.IsWellFormed := ⟨hN,hcM,hBorn,hTr⟩
  have hCarrierQ := HironakaSharpActualOriginalControlledHistory.actual_original_test_history_template
    M hwM Q hMQ
  change IsGeoTestTower (geometricTemplate N born) Q at hCarrierQ
  have hOrders := actual_retained_orders_and_count_open_tower_iso hn hN hE hTr hdense
    U Q hCarrierQ hFullQ R hR hFullR e he
  have hTuple := tuple_open_iso hN born U Q hCarrierQ R e he
  have hGlobalRows : ∀ k : ℕ,
      let P := BlowupTowerSplit.head Q k
      let A := geoTransformAlong (geometricTemplate N born) P
      ∀ y ∈ A.N,∀ i,ordinaryTraceOrder A.N
        (chronologicalMarked (retainedResidualMarked N old born i) P).ideal y ≤
          ordinaryTraceOrder N (oldResidualPart N old born i) (P.proj y) := by
    intro k
    dsimp only
    let P := BlowupTowerSplit.head Q k
    have hP := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail
      (geometricTemplate N born) Q k).mp hCarrierQ).1
    have hFullP := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail
      (geometricTemplate (univ : Set X) (old ++ born)) Q k).mp hFullQ).1
    have hOverP := RestrictEmptyTower.centresOver_head D Q k hOverQ
    obtain ⟨χ,hχ,_hχtail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split he k
    obtain ⟨η,hη,_hηtail⟩ := exists_isTowerIso_split_restrict U Q k
    have hIso := BlowupTowerSplitIso.IsTowerIso.congr_base (hχ.trans hη) (fun _ => rfl)
    rcases hHeadsR k with ⟨hRK,hFullRK,_hSharpRK,_hFootRK,hRowsRK,_hRestRK⟩
    have hInside := row_nonincrease_of_actual_open_iso hn hN hE hTr hdense U P hP hFullP
      (BlowupTowerSplit.head R k) hRK hFullRK (χ.trans η) hIso hRowsRK
    let O : Opens X := ⟨Dᶜ,hD.isClosed.isOpen_compl⟩
    have hDisjoint : Disjoint (O : Set X) D := Set.disjoint_left.mpr (fun _ hxO hxD => hxO hxD)
    have hEmptyP := RestrictEmptyTower.isEmptyTower_restrict_of_centresOver O hDisjoint P hOverP
    have hOutside := retained_orders_count_on_empty_restriction hn hN hE hTr hdense
      P hP hFullP O hEmptyP
    intro y hy i
    by_cases hyU : P.proj y ∈ U
    · exact hInside y hy hyU i
    · have hyO : P.proj y ∈ O := fun hyD => hyU (hDU hyD)
      exact ((hOutside y hyO).1 i).le
  have hGlobalFoot : ∀ k : ℕ,
      let P := BlowupTowerSplit.head Q k
      actualFamilyDistinctDefect (geoTransformAlong (geometricTemplate N born) P).N
        (fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) P).ideal) ⊆
          P.proj ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born) := by
    intro k
    exact retained_defect_footprint hn hN hE hTr hdense D hD hDefectD
      (BlowupTowerSplit.head Q k)
      (((BlowupTowerSplit.isGeoTestTower_iff_head_tail (geometricTemplate N born) Q k).mp hCarrierQ).1)
      (((BlowupTowerSplit.isGeoTestTower_iff_head_tail
        (geometricTemplate (univ : Set X) (old ++ born)) Q k).mp hFullQ).1)
      (RestrictEmptyTower.centresOver_head D Q k hOverQ)
  have hEquivQ : IsEquivariant N ((U : Set X) :: (old ++ born)) Q := by
    refine HironakaG34ExtensionEquivariance.isEquivariant_of_extension hDU Q R hOverQ he ?_
    rw [List.map_append]
    exact hEquivR
  refine ⟨Y,Q,hCarrierQ,hFullQ,hSharpQ,hOverQ,hMQ,hGlobalRows,hGlobalFoot,?_,hEquivQ⟩
  intro y hy hyU
  let w : openPreimage Q U := ⟨y,hyU⟩
  let z := e.symm w
  have hz : z ∈ (geoTransformAlong (geometricTemplate NU BU) R).N := by
    rw [hTuple.1]
    change (e z).val ∈ (geoTransformAlong (geometricTemplate N born) Q).N
    simpa only [z,e.apply_symm_apply] using hy
  have hLocal := hExitR z hz
  have hIso := (hOrders z).2.2 q
  have hTarget : (e z).val=y := by simp only [z,e.apply_symm_apply];rfl
  rw [hTarget] at hIso
  exact hIso.symm.trans_lt hLocal

private theorem original_current_template (W : Set X) (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate W []) T=
      geometricTemplate (geoTransformAlong (geometricTemplate W []) T).N
        (geoTransformAlong (geometricTemplate W []) T).E := by
  simpa only [N_geoTransformAlong,geometricTemplate] using template_current W [] T

private theorem original_full_template (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate (univ : Set X) E) T=
      geometricTemplate (univ : Set Y)
        (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) := by
  rw [template_current,strict_univ]
  apply congrArg (geometricTemplate (univ : Set Y))
  simpa only [List.append_nil] using retained_born_full_boundary_ordered_dictionary W E [] T

private theorem original_current_geometry_append (W : Set X) (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    geoTransformAlong (geometricTemplate (geoTransformAlong (geometricTemplate W []) T).N
      (geoTransformAlong (geometricTemplate W []) T).E) S=
        geoTransformAlong (geometricTemplate W []) (T.append S) := by
  rw [geoTransformAlong_append,original_current_template W T]
  rfl

private theorem original_append_tests {W : Set X} {E : List (Set X)} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (S : BlowupTower Y Z)
    (hS : IsGeoTestTower (geometricTemplate (geoTransformAlong (geometricTemplate W []) T).N
      (geoTransformAlong (geometricTemplate W []) T).E) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set Y)
      (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E)) S) :
    IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) := by
  constructor
  · apply (isGeoTestTower_append_iff _ T S).mpr
    refine ⟨hT,?_⟩
    rw [original_current_template W T]
    exact hS
  · apply (isGeoTestTower_append_iff _ T S).mpr
    refine ⟨hFull,?_⟩
    rw [original_full_template W E T]
    exact hFullS

private theorem original_tail_row (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (S : BlowupTower Y Z) (i : Fin E.length) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let O := E.map (strictAlong T)
    let j : Fin O.length := ⟨i.val,by simpa only [O,List.length_map] using i.isLt⟩
    chronologicalMarked (retainedResidualMarked A.N O A.E j) S=
      chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S) := by
  dsimp only
  rw [HironakaG4OriginalSelectedResidualTail.chronological_append_native]
  exact congrArg (fun M : MarkedIdeal n Y => chronologicalMarked M S)
    (retained_seed_eq_original_chronological hn hW hE hdense T hT hFull i)

private theorem original_tail_product (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (S : BlowupTower Y Z)
    (hS : IsGeoTestTower (geometricTemplate (geoTransformAlong (geometricTemplate W []) T).N
      (geoTransformAlong (geometricTemplate W []) T).E) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set Y)
      (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E)) S) (q : ℕ) :
    let A := geoTransformAlong (geometricTemplate W []) T
    retainedProductMarked A.N (E.map (strictAlong T)) A.E q S=residualMarked W E q (T.append S) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let O := E.map (strictAlong T)
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hAppend := original_append_tests T hT hFull S hS hFullS
  have hProd := retainedProductMarked_eq_canonical (X := Y) hn hRec.1 hRec.2.1
    hRec.2.2.1 hRec.2.2.2.1 q S hS hFullS
  have hGeo := original_current_geometry_append W T S
  have hOld : O.map (strictAlong S)=E.map (strictAlong (T.append S)) := by
    simp only [O,List.map_map]
    apply List.map_congr_left
    intro H _hH
    exact (strictAlong_append T H S).symm
  dsimp only
  rw [hProd,hGeo,hOld]
  exact canonicalProductMarked_eq_original_residualMarked hn hW hE hdense
    (T.append S) hAppend.1 hAppend.2 q

private theorem original_tail_distinct_defect (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (S : BlowupTower Y Z)
    (hS : IsGeoTestTower (geometricTemplate (geoTransformAlong (geometricTemplate W []) T).N
      (geoTransformAlong (geometricTemplate W []) T).E) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set Y)
      (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E)) S) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let O := E.map (strictAlong T)
    actualFamilyDistinctDefect (geoTransformAlong (geometricTemplate A.N A.E) S).N
      (fun i : Fin O.length => (chronologicalMarked (retainedResidualMarked A.N O A.E i) S).ideal)=
        chronologicalDistinctDefect W E (T.append S) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let O := E.map (strictAlong T)
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S)).ideal
  let G := fun j : Fin O.length => (chronologicalMarked (retainedResidualMarked A.N O A.E j) S).ideal
  let ι : Fin E.length ≃ Fin O.length := (finCongr (List.length_map _)).symm
  have hRow (i : Fin E.length) : G (ι i)=F i := by
    exact congrArg (fun M : MarkedIdeal n Z => M.ideal)
      (original_tail_row hn hW hE hdense T hT hFull S i)
  have hProduct := congrArg (fun M : MarkedIdeal n Z => M.ideal)
    (original_tail_product hn hW hE hdense T hT hFull S hS hFullS 0)
  change (retainedProductMarked A.N O A.E 0 S).ideal=chronologicalMemberProduct W E (T.append S) at hProduct
  rw [product_ideal,chronological_product_eq_actual_family_product] at hProduct
  have hCarrier := congrArg (fun M : MarkedIdeal n Z => M.N) (original_current_geometry_append W T S)
  ext y
  have hCount := current_count_reindex ι F G hRow y
  change (y ∈ (geoTransformAlong (geometricTemplate A.N A.E) S).N ∧
    actualDistinctProperCount G y < ordinaryTraceOrder (geoTransformAlong (geometricTemplate A.N A.E) S).N
      (relativeIdealListProduct (geoTransformAlong (geometricTemplate A.N A.E) S).N (List.ofFn G)) y) ↔ _
  rw [hProduct,hCarrier,←hCount]
  rfl

/-- The equivariant original profile blocks with compactness supplied on
the current chronological defect. -/
theorem exists_actual_global_original_profile_blocks_equivariant_of_compact_defect (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hCompact : IsCompact (chronologicalDistinctDefect W E T))
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ q : ℕ,1 ≤ q ∧
      (∃ a ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) a=q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x ≤ q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x=q →
        ∃ profile ∈ realizedProfiles W E T q,
          x ∈ topProfileStratum W E T q (fun i => (profile i).val)) ∧
      ∀ profile ∈ realizedProfiles W E T q,
        let r := fun i => (profile i).val
        let D := topProfileStratum W E T q r
        let U := profileWindow W E T q r
        ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
          IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
          IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
          CurrentSharpCentres W E (T.append Q) ∧ RestrictEmptyTower.CentresOver D Q ∧
          IsGeoTestTower (residualMarked W E q T) Q ∧
          (∀ k : ℕ,
            let P := BlowupTowerSplit.head Q k
            let A := geoTransformAlong (geometricTemplate W []) (T.append P)
            ∀ y ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append P)).ideal y ≤
                ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
                  (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (P.proj y)) ∧
          (∀ k : ℕ,
            let P := BlowupTowerSplit.head Q k
            chronologicalDistinctDefect W E (T.append P) ⊆ P.proj ⁻¹' chronologicalDistinctDefect W E T) ∧
          (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,Q.proj y ∈ U →
            ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
              (chronologicalMemberProduct W E (T.append Q)) y < q) ∧
          IsEquivariant (geoTransformAlong (geometricTemplate W []) T).N
            ((U : Set Y) :: (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E)) Q := by
  classical
  obtain ⟨q,hq,hAttain,hMax,hCover,hProfiles⟩ :=
    exists_actual_distinct_defect_profile_windows_of_compact_defect hn hW hE hdense d hReg T hT hFull hCompact hne
  refine ⟨q,hq,hAttain,hMax,hCover,?_⟩
  intro profile hProfile
  dsimp only
  let r := fun i : Fin E.length => (profile i).val
  let D := topProfileStratum W E T q r
  let U := profileWindow W E T q r
  let A := geoTransformAlong (geometricTemplate W []) T
  let O := E.map (strictAlong T)
  let ι : Fin O.length ≃ Fin E.length := finCongr (List.length_map _)
  let p : Fin O.length → ℕ := fun j => r (ι j)
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hWindow := hProfiles profile hProfile
  dsimp only at hWindow
  rcases hWindow with ⟨_hDne,hD,hDU,_hDsource,_hTop,hBounds,hCos,_hCompact,_hDomain⟩
  have hSumOriginal : ∑ i : Fin E.length,r i=q := (Finset.mem_filter.mp hProfile).2.1
  have hSum : ∑ j : Fin O.length,p j=q := (ι.sum_comp r).trans hSumOriginal
  have hInitialRow (j : Fin O.length) : retainedResidualMarked A.N O A.E j=
      chronologicalMarked (originalRelativeMemberMarked W (E.get (ι j))) T := by
    have hj : (⟨(ι j).val,by simpa only [O,List.length_map] using (ι j).isLt⟩ : Fin O.length)=j := by
      apply Fin.ext
      rfl
    have h := retained_seed_eq_original_chronological hn hW hE hdense T hT hFull (ι j)
    rw [hj] at h
    exact h
  have hInitialIdeal (j : Fin O.length) : oldResidualPart A.N O A.E j=
      (chronologicalMarked (originalRelativeMemberMarked W (E.get (ι j))) T).ideal :=
    congrArg (fun M : MarkedIdeal n Y => M.ideal) (hInitialRow j)
  have hOrd : ∀ x ∈ U,∀ j,ordinaryTraceOrder A.N (oldResidualPart A.N O A.E j) x ≤ p j := by
    intro x hx j
    rw [hInitialIdeal j]
    exact (hBounds x hx).1 (ι j)
  have hCount : ∀ x ∈ U,actualDistinctProperCount (oldResidualPart A.N O A.E) x < q := by
    intro x hx
    have hIndex := current_count_reindex ι (oldResidualPart A.N O A.E)
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal)
      (fun j => (hInitialIdeal j).symm) x
    rw [hIndex]
    exact (hBounds x hx).2
  have hInitialProduct : canonicalProductMarked A.N O A.E q=residualMarked W E q T :=
    canonicalProductMarked_eq_original_residualMarked hn hW hE hdense T hT hFull q
  have hCosCurrent : (MarkedIdeal.pullback (Subtype.val : U → Y)
      (canonicalProductMarked A.N O A.E q)).cosupp=(Subtype.val : U → Y) ⁻¹' D := by
    rw [hInitialProduct]
    exact hCos
  obtain ⟨Z,Q,hQ,hFullQ,hSharpQ,hOverQ,hProductQ,hRowsQ,hFootQ,hExitQ,hEquivQ⟩ :=
    exists_current_profile_window_block (X := Y) hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1
      U D hD hDU p q hq hSum hOrd hCount hCosCurrent
  have hAppend := original_append_tests T hT hFull Q hQ hFullQ
  have hSharpAppend : CurrentSharpCentres W E (T.append Q) := by
    apply currentSharp_append W E T Q hSharp
    have hBoundary := congrArg (fun M : MarkedIdeal n Y => M.E) (original_full_template W E T)
    rw [hBoundary]
    simpa only [N_geoTransformAlong,geometricTemplate] using hSharpQ
  have hNativeProduct : IsGeoTestTower (residualMarked W E q T) Q := by
    rw [←hInitialProduct]
    exact hProductQ
  have hRowsOriginal : ∀ k : ℕ,
      let P := BlowupTowerSplit.head Q k
      let B := geoTransformAlong (geometricTemplate W []) (T.append P)
      ∀ y ∈ B.N,∀ i : Fin E.length,ordinaryTraceOrder B.N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append P)).ideal y ≤
          ordinaryTraceOrder A.N (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
            (P.proj y) := by
    intro k
    dsimp only
    let P := BlowupTowerSplit.head Q k
    have hGeo := original_current_geometry_append W T P
    intro y hy i
    let j : Fin O.length := ⟨i.val,by simpa only [O,List.length_map] using i.isLt⟩
    have hyCurrent : y ∈ (geoTransformAlong (geometricTemplate A.N A.E) P).N := by
      rw [hGeo]
      exact hy
    have hh := hRowsQ k y hyCurrent j
    rw [original_tail_row hn hW hE hdense T hT hFull P i,hGeo] at hh
    have hSource := congrArg (fun M : MarkedIdeal n Y => M.ideal)
      (retained_seed_eq_original_chronological hn hW hE hdense T hT hFull i)
    change oldResidualPart A.N O A.E j=
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal at hSource
    rw [hSource] at hh
    exact hh
  have hSourceDefect : actualFamilyDistinctDefect A.N (oldResidualPart A.N O A.E)=
      chronologicalDistinctDefect W E T := by
    simpa only [A,O,BlowupTower.append_refl,geoTransformAlong,chronologicalMarked,retainedResidualMarked,
      geometricTemplate] using
      (original_tail_distinct_defect hn hW hE hdense T hT hFull (.refl : BlowupTower Y Y) trivial trivial)
  have hFootOriginal : ∀ k : ℕ,
      let P := BlowupTowerSplit.head Q k
      chronologicalDistinctDefect W E (T.append P) ⊆ P.proj ⁻¹' chronologicalDistinctDefect W E T := by
    intro k
    dsimp only
    let P := BlowupTowerSplit.head Q k
    have hP := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail (geometricTemplate A.N A.E) Q k).mp hQ).1
    have hFullP := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail
      (geometricTemplate (univ : Set Y) (O ++ A.E)) Q k).mp hFullQ).1
    have hh := hFootQ k
    dsimp only at hh
    rw [original_tail_distinct_defect hn hW hE hdense T hT hFull P hP hFullP,hSourceDefect] at hh
    exact hh
  refine ⟨Z,Q,hAppend.1,hAppend.2,hSharpAppend,hOverQ,hNativeProduct,hRowsOriginal,hFootOriginal,?_,hEquivQ⟩
  intro y hy hyU
  have hGeo := original_current_geometry_append W T Q
  have hyCurrent : y ∈ (geoTransformAlong (geometricTemplate A.N A.E) Q).N := by
    rw [hGeo]
    exact hy
  have hh := hExitQ y hyCurrent hyU
  rw [hGeo,original_tail_product hn hW hE hdense T hT hFull Q hQ hFullQ q] at hh
  exact hh

/-- **The global profile blocks, equivariant** (`HironakaActualGlobalDefectProfileBlock.exists_actual_global_original_profile_blocks`
with an equivariance conclusion): the held conclusions, and each block `Q` is equivariant for the CURRENT data along `T`
(carrier `A.N`, members `E.map (strictAlong T) ++ A.E`) together with the profile window `U`. -/
theorem exists_actual_global_original_profile_blocks_equivariant (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ q : ℕ,1 ≤ q ∧
      (∃ a ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) a=q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x ≤ q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x=q →
        ∃ profile ∈ realizedProfiles W E T q,
          x ∈ topProfileStratum W E T q (fun i => (profile i).val)) ∧
      ∀ profile ∈ realizedProfiles W E T q,
        let r := fun i => (profile i).val
        let D := topProfileStratum W E T q r
        let U := profileWindow W E T q r
        ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
          IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
          IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
          CurrentSharpCentres W E (T.append Q) ∧ RestrictEmptyTower.CentresOver D Q ∧
          IsGeoTestTower (residualMarked W E q T) Q ∧
          (∀ k : ℕ,
            let P := BlowupTowerSplit.head Q k
            let A := geoTransformAlong (geometricTemplate W []) (T.append P)
            ∀ y ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append P)).ideal y ≤
                ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
                  (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (P.proj y)) ∧
          (∀ k : ℕ,
            let P := BlowupTowerSplit.head Q k
            chronologicalDistinctDefect W E (T.append P) ⊆ P.proj ⁻¹' chronologicalDistinctDefect W E T) ∧
          (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,Q.proj y ∈ U →
            ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
              (chronologicalMemberProduct W E (T.append Q)) y < q) ∧
          IsEquivariant (geoTransformAlong (geometricTemplate W []) T).N
            ((U : Set Y) :: (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E)) Q :=
  exists_actual_global_original_profile_blocks_equivariant_of_compact_defect hn hW hE hdense d hReg T hT hFull hSharp
    (isCompact_actual_chronological_distinct_defect hn hW hE hdense d hReg hK T hT hFull hSharp) hne

/-- **Appending a block equivariant for the current data and a natural window keeps a tower equivariant.**  Let `T` be a
multiple test blow-up of `(W, [])` and `(X, E)`, equivariant for `(W, E)`, and let `U` be a subset of its last stage which
is natural: every lift `χ` of a biholomorphism `φ` preserving `W` and the members of `E` along `T` preserves `U`.  If `Q`
is equivariant for the current data together with `U` (as the blocks of
`exists_actual_global_original_profile_blocks_equivariant` are, with `U` the profile window), then `T Q` is equivariant
for `(W, E)`. -/
theorem isEquivariant_append_of_window {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (hEqT : IsEquivariant W E T) (U : Set Y)
    (hU : ∀ (V V' : Opens X)
      (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V'),
      (∀ p : V, ((φ p : V') : X) ∈ W ↔ (p : X) ∈ W) →
      (∀ H ∈ E, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H) →
      ∀ χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T V'),
      IsTowerIso φ (restrict V T) (restrict V' T) χ →
      ∀ p : openPreimage T V, ((χ p : openPreimage T V') : Y) ∈ U ↔ (p : Y) ∈ U)
    (Q : BlowupTower Y Z)
    (hEqQ : IsEquivariant (geoTransformAlong (geometricTemplate W []) T).N
      (U :: (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E)) Q) :
    IsEquivariant W E (T.append Q) := by
  intro V V' φ hφN hφH
  obtain ⟨χ, hχ⟩ := hEqT V V' φ hφN hφH
  have hφH' : ∀ H ∈ E ++ [], ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H := by
    rw [List.append_nil]
    exact hφH
  have hFull' : IsGeoTestTower (geometricTemplate (univ : Set X) (E ++ [])) T := by
    rw [List.append_nil]
    exact hFull
  obtain ⟨hcN, hcH⟩ := HironakaG34MaskStepEquivariance.current_data_preserved φ hW hφN hφH' T hT hFull' hχ
  have hcH' : ∀ H ∈ U :: (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E),
      ∀ p : openPreimage T V, ((χ p : openPreimage T V') : Y) ∈ H ↔ (p : Y) ∈ H := by
    intro H hH
    rcases List.mem_cons.mp hH with rfl | hH
    · exact hU V V' φ hφN hφH χ hχ
    · exact hcH H hH
  obtain ⟨χ₁, h₁⟩ := hEqQ (openPreimage T V) (openPreimage T V') χ hcN hcH'
  exact HironakaG34CanonicalLocalEquivariance.exists_isTowerIso_restrict_append φ T hχ Q h₁

end
end Hironaka.HironakaG34ProfileBlockEquivariance
