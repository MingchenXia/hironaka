import Hironaka.Resolution.HironakaG34FieldMatrix
import Hironaka.Resolution.HironakaActualGlobalDefectProfileBlock
import Hironaka.Resolution.HironakaCompactFootprintSharpExtension
import Hironaka.Resolution.HironakaSharpOriginalDynamicGoodPrefixes
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Resolution.HironakaG4SharpBadFootprint
import Hironaka.Resolution.HironakaActualGeometricCleanupComposition
import Hironaka.Resolution.HironakaG34LowerTemplateBridge
import Hironaka.Resolution.HironakaG34CarrierPureDimension

/-! # The sharp cleanup of a NON-PURE `W` of dimension `≤ 3`, by phases on the open-closed pure pieces

Lane G34 (run 0080, round 7).  Blueprint: `hironaka-g34-resume-non-pure-low-dim.tex`.

`HironakaG34SharpCleanupLowDim.exists_actual_sharp_cleanup_dim_le_three` needs `W` pure of dimension
`m ≤ 3`.  A closed submanifold `W` all of whose points have dimension `≤ 3` is the disjoint union of its
pieces `dimPiece W m = {x ∈ W | W regular of dimension m at x}`, `m ≤ 3`, each closed in the ambient and
open in `W` (`isClosed_dimPiece`, `isClosed_diff_dimPiece`).  The pieces are cleaned one after another:

* `exists_piece_phase` (one phase, general base): for a problem `(N, F)` (closed submanifold, SNC, density)
  and an open `V` on which `N` is pure of dimension `m ≤ 3`, with compact bad locus over `V`, there is a
  tower with both tests of `(N, F)`, current sharp centres, and normal crossings at its end at every point
  of the strict carrier over `V`.  Proof: the pure theorem on the open submanifold `V`, extended to the
  ambient by the held compact-footprint extension `exists_current_sharp_joint_test_extension`, final
  normal crossings transported along the extension's tower isomorphism.
* `exists_piece_step`: one phase appended to an actual prefix `T` of the ORIGINAL problem `(W, E)` (the
  phase is run for the current problem on the open preimage of the piece's open neighbourhood); normal
  crossings already obtained over earlier pieces persist (sharp-bad footprint).
* `exists_actual_sharp_cleanup_dim_le_three_nonpure`: the four phases `m = 0, 1, 2, 3`; the whole sharp
  cleanup output (both tests, current sharp centres, centres over the original sharp bad locus, smooth
  carrier with normal crossings with the SNC boundary, proper, isomorphism off the bad locus). -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34NonPureLowDim
noncomputable section

section Copied
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  BlowupTowerIsomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-! Verbatim copies of private helpers of `HironakaActualGlobalDefectProfileBlock` (`open_full_density`,
`template_pullback`, `tuple_open_iso`) and `HironakaCompactFootprintSharpExtension`
(`normalCrossingsAt_preimage_diffeo`). -/

theorem open_full_density {N : Set X} {E : List (Set X)}
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

theorem template_pullback (f : Y → X) (N : Set X) (B : List (Set X)) :
    MarkedIdeal.pullback f (geometricTemplate N B)=geometricTemplate (f ⁻¹' N) (B.map (f ⁻¹' ·)) := by
  simp [MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal]

theorem tuple_open_iso {N : Set X} (hN : IsClosedSubmanifold n N)
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

theorem normalCrossingsAt_preimage_diffeo
    (Φ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {E : List (Set X)} {y : Y}
    (hNC : normalCrossingsAt (n := n) N E (Φ y)) :
    normalCrossingsAt (n := n) (Φ ⁻¹' N) (E.map (Φ ⁻¹' ·)) y := by
  obtain ⟨S₀,S,hcoord,hcard⟩ := hNC
  let c : Fin (E.map (Φ ⁻¹' ·)).length → Fin E.length := Fin.cast (List.length_map _)
  refine ⟨S₀,fun i => S (c i),?_,?_⟩
  · exact IsCoordinateFamilyAt.reindex ((pullsBackCoordinates Φ) _ _ y hcoord)
      (Option.map c) (by rintro (_|i); rfl; exact get_map_preimage E i)
      (by rintro (_|i) <;> rfl)
  · intro i hi
    rw [get_map_preimage] at hi
    exact hcard (c i) hi

/-- The converse transport of pointwise normal crossings along a biholomorphism. -/
theorem normalCrossingsAt_of_preimage_diffeo
    (Φ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {E : List (Set X)} {y : Y}
    (hNC : normalCrossingsAt (n := n) (Φ ⁻¹' N) (E.map (Φ ⁻¹' ·)) y) :
    normalCrossingsAt (n := n) N E (Φ y) := by
  have h := normalCrossingsAt_preimage_diffeo Φ.symm (y := Φ y)
    (N := Φ ⁻¹' N) (E := E.map (Φ ⁻¹' ·)) (by simpa only [Φ.symm_apply_apply] using hNC)
  have hset : ∀ A : Set X, Φ.symm ⁻¹' (Φ ⁻¹' A) = A := by
    intro A
    ext x
    simp
  rw [hset, List.map_map] at h
  have hfun : ((Φ.symm ⁻¹' ·) ∘ (Φ ⁻¹' ·) : Set X → Set X) = id := funext hset
  rw [hfun, List.map_id] at h
  exact h

end Copied

section Main
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  BlowupTowerIsomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport RestrictEmptyTower
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4RecordedTowerResidualCompatibility HironakaActualGeometricCleanupComposition

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The boundary list of the transform of a geometric template depends only on the boundary. -/
theorem template_E_eq (N N' : Set X) (B : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate N B) T).E = (geoTransformAlong (geometricTemplate N' B) T).E
  | _, .refl => rfl
  | _, .step T C π _ => by
    change (geoTransformAlong (geometricTemplate N B) T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] =
      (geoTransformAlong (geometricTemplate N' B) T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    rw [template_E_eq N N' B T]

/-- **The dimension-`m` piece of `W`**: the points of `W` at which `W` is regular of dimension `m`. -/
def dimPiece (W : Set X) (m : ℕ) : Set X := {x | x ∈ W ∧ RegularAtDim (n := n) W x m}

theorem dimPiece_subset (W : Set X) (m : ℕ) : dimPiece W m ⊆ W := fun _ h => h.1

/-- The complement of a piece in `W` is closed (a piece is open in `W`). -/
theorem isClosed_diff_dimPiece {W : Set X} (hW : IsClosed W) (m : ℕ) :
    IsClosed (W \ dimPiece W m) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  have hxW : x ∈ W := closure_minimal sdiff_subset hW hx
  refine ⟨hxW, fun hxm => ?_⟩
  have hev := RegularPatchNeighborhood.eventually_regularAtDim hxm.2
  obtain ⟨y, hy, hyD⟩ := mem_closure_iff_nhds.mp hx _ hev
  exact hyD.2 ⟨hyD.1, hy hyD.1⟩

/-- A piece is closed. -/
theorem isClosed_dimPiece {W : Set X} (hW : IsClosedSubmanifold n W) (m : ℕ) :
    IsClosed (dimPiece W m) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  have hxW : x ∈ W := closure_minimal (dimPiece_subset W m) hW.1 hx
  obtain ⟨k, hk⟩ := hW.2 x hxW
  have hev := RegularPatchNeighborhood.eventually_regularAtDim hk
  obtain ⟨y, hy, hyP⟩ := mem_closure_iff_nhds.mp hx _ hev
  have hkm : k = m := RegularPointDimension.eq_of_regularAtDim (hy hyP.1) hyP.2
  subst hkm
  exact ⟨hxW, hk⟩

/-- The open neighbourhood `(W \ piece)ᶜ` of a piece; it meets `W` exactly in the piece. -/
def pieceOpen {W : Set X} (hW : IsClosed W) (m : ℕ) : Opens X :=
  ⟨(W \ dimPiece W m)ᶜ, (isClosed_diff_dimPiece hW m).isOpen_compl⟩

theorem dimPiece_subset_pieceOpen {W : Set X} (hW : IsClosed W) (m : ℕ) :
    dimPiece W m ⊆ pieceOpen hW m := fun _ hx hx' => hx'.2 hx

theorem mem_dimPiece_of_mem_pieceOpen {W : Set X} (hW : IsClosed W) (m : ℕ) {x : X}
    (hxW : x ∈ W) (hxO : x ∈ pieceOpen hW m) : x ∈ dimPiece W m := by
  by_contra h
  exact hxO ⟨hxW, h⟩

/-- **One phase on an open where the carrier is pure of dimension `m ≤ 3`** (general base). -/
theorem exists_piece_phase (hn : 0 < n) {N : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hF : IsSNCDivisor n F)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ F, H))
    (V : Opens X) (G : Set X) (hGV : G ⊆ V) (hNVG : N ∩ V ⊆ G)
    (hK : IsCompact (originalSharpBadLocus (n := n) N F ∩ G))
    (m : ℕ) (hm : m ≤ 3) (hReg : ∀ y ∈ N, y ∈ V → RegularAtDim (n := n) N y m) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower X Z),
      IsGeoTestTower (geometricTemplate N F) S ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) F) S ∧
      CurrentSharpCentres N F S ∧
      ∀ z ∈ strictAlong S N, S.proj z ∈ V →
        normalCrossingsAt (n := n) (strictAlong S N)
          (geoTransformAlong (geometricTemplate (univ : Set X) F) S).E z := by
  let NU := (Subtype.val : V → X) ⁻¹' N
  let FU := F.map ((Subtype.val : V → X) ⁻¹' ·)
  let K := originalSharpBadLocus (n := n) N F ∩ G
  have hNU : IsClosedSubmanifold n NU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN V
  have hFU : IsSNCDivisor n FU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := n) V) continuous_subtype_val hF
  have hdenseU : NU ⊆ closure (NU \ ⋃ H ∈ FU, H) := open_full_density hdense V
  have hRegU : ∀ y ∈ NU, RegularAtDim (n := n) NU y m := fun y hy =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hReg y.val hy y.property)
  have hBadU : originalSharpBadLocus (n := n) NU FU = (Subtype.val : V → X) ⁻¹' K := by
    ext y
    constructor
    · rintro ⟨hy, hnc⟩
      exact ⟨⟨hy, fun h => hnc
        (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mpr h)⟩,
        hNVG ⟨hy, y.property⟩⟩
    · rintro ⟨⟨hy, hnc⟩, -⟩
      exact ⟨hy, fun h => hnc
        (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp h)⟩
  have hKV : K ⊆ V := fun x hx => hGV hx.2
  have hKU : IsCompact (originalSharpBadLocus (n := n) NU FU) := by
    rw [hBadU]
    apply Subtype.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset (show K ⊆ Set.range (Subtype.val : V → X) from
      fun x hx => ⟨⟨x, hKV hx⟩, rfl⟩)]
    exact hK
  obtain ⟨Z, TU, hTU, hFullU, hSharpU, hOverU, -, -, hNCU, -, -⟩ :=
    HironakaG34SharpCleanupLowDim.exists_actual_sharp_cleanup_dim_le_three (X := CMfd.of (n := n) V)
      hn hNU hFU hdenseU m hm hRegU hKU
  have hTUF : IsGeoTestTower (geometricTemplate NU FU) TU :=
    HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests NU FU TU hTU hFullU
  have hOverK : CentresOver ((Subtype.val : V → X) ⁻¹' K) TU := by
    rw [← hBadU]
    exact hOverU
  have hFullPull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X)
      (geometricTemplate (univ : Set X) F)) TU := by
    rw [template_pullback (Y := CMfd.of (n := n) V) (Subtype.val : V → X) (univ : Set X) F]
    simpa only [Set.preimage_univ] using hFullU
  have hMPull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X)
      (geometricTemplate N F)) TU := by
    rw [template_pullback (Y := CMfd.of (n := n) V) (Subtype.val : V → X) N F]
    exact hTUF
  obtain ⟨Y, Q, hFullQ, hMQ, hSharpQ, -, e, he, -, -⟩ :=
    HironakaCompactFootprintSharpExtension.exists_current_sharp_joint_test_extension
      N F (geometricTemplate N F) hN IdealWeightPowers.isCoherent_unitIdeal V K hK hKV TU hOverK
      hFullPull hMPull hSharpU
  refine ⟨Y, Q, hMQ, hFullQ, hSharpQ, ?_⟩
  intro z hz hzV
  obtain ⟨hTN, hTE, -⟩ := tuple_open_iso hN F V Q hMQ TU e he
  let w : openPreimage Q V := ⟨z, hzV⟩
  let z' : Z := e.symm w
  have hew : e z' = w := e.apply_symm_apply w
  have hNsame : (geoTransformAlong (geometricTemplate NU []) TU).N =
      (geoTransformAlong (geometricTemplate NU FU) TU).N := by
    have h0 : (geoTransformAlong (geometricTemplate NU []) TU).N = strictAlong TU NU :=
      N_geoTransformAlong _ TU
    have h1 : (geoTransformAlong (geometricTemplate NU FU) TU).N = strictAlong TU NU :=
      N_geoTransformAlong _ TU
    rw [h0, h1]
  have hAN : (geoTransformAlong (geometricTemplate N F) Q).N = strictAlong Q N :=
    N_geoTransformAlong _ Q
  have hz'N : z' ∈ (geoTransformAlong (geometricTemplate NU []) TU).N := by
    rw [hNsame, hTN]
    change (e z').val ∈ (geoTransformAlong (geometricTemplate N F) Q).N
    rw [hew, hAN]
    exact hz
  have hNC0 := hNCU z' hz'N
  have hEsame : (geoTransformAlong (geometricTemplate (univ : Set (CMfd.of (n := n) V)) FU) TU).E =
      (geoTransformAlong (geometricTemplate NU FU) TU).E := template_E_eq _ _ FU TU
  have hNC1 : normalCrossingsAt (n := n) (geoTransformAlong (geometricTemplate NU FU) TU).N
      (geoTransformAlong (geometricTemplate NU FU) TU).E z' := by
    rw [← hNsame, ← hEsame]
    exact hNC0
  rw [hTN, hTE] at hNC1
  let A := geoTransformAlong (geometricTemplate N F) Q
  have hList : A.E.map (((Subtype.val : openPreimage Q V → Y) ∘ e) ⁻¹' ·) =
      (A.E.map ((Subtype.val : openPreimage Q V → Y) ⁻¹' ·)).map (e ⁻¹' ·) := by
    rw [List.map_map]
    rfl
  rw [hList] at hNC1
  have hNC2 := normalCrossingsAt_of_preimage_diffeo (X := CMfd.of (n := n) (openPreimage Q V))
    (Y := Z) e
    (N := (Subtype.val : openPreimage Q V → Y) ⁻¹' A.N)
    (E := A.E.map ((Subtype.val : openPreimage Q V → Y) ⁻¹' ·)) hNC1
  rw [hew] at hNC2
  have hNC3 := HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp hNC2
  have hAE : A.E = (geoTransformAlong (geometricTemplate (univ : Set X) F) Q).E :=
    template_E_eq _ _ F Q
  rw [hAN, hAE] at hNC3
  exact hNC3

/-- **One piece appended to an actual prefix of the original problem.**  At an actual prefix `T` of
`(W, E)` (both tests, current sharp centres) at which the strict carrier has normal crossings with the
current boundary over a set `D`, the phase of the piece `dimPiece W m` (run for the current problem on
the open preimage of `pieceOpen`) gives an actual prefix `T·S` with normal crossings over
`D ∪ dimPiece W m`. -/
theorem exists_piece_step (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (m : ℕ) (hm : m ≤ 3)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) (D : Set X)
    (hD : ∀ z ∈ strictAlong T W, T.proj z ∈ D →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
      CurrentSharpCentres W E (T.append S) ∧
      ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ D ∪ dimPiece W m →
        normalCrossingsAt (n := n) (strictAlong (T.append S) W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  let N := strictAlong T W
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
  obtain ⟨hNsm, hSNC, -, hDen, -⟩ :=
    actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hNdef : (geoTransformAlong (geometricTemplate W []) T).N = N := N_geoTransformAlong _ T
  have hFdef : E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E = F := by
    have h := full_boundary_split W E [] T
    simp only [List.append_nil] at h
    exact h.symm
  have hN : IsClosedSubmanifold n N := by
    rw [← hNdef]
    exact hNsm
  have hF : IsSNCDivisor n F := by
    rw [← hFdef]
    exact hSNC
  have hdenseN : N ⊆ closure (N \ ⋃ H ∈ F, H) := by
    rw [← hNdef, ← hFdef]
    exact hDen
  let O := pieceOpen hW.1 m
  let V : Opens Y := openPreimage T O
  let G : Set Y := T.proj ⁻¹' dimPiece W m
  have hGV : G ⊆ V := fun z hz => dimPiece_subset_pieceOpen hW.1 m hz
  have hNVG : N ∩ V ⊆ G := fun z hz =>
    mem_dimPiece_of_mem_pieceOpen hW.1 m
      (MemberInterTowerAlong.strictAlong_subset_preimage T hW.1 hz.1) hz.2
  obtain ⟨hFoot, -⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hW.1 hE.1 T hSharp
  have hKT : IsCompact (originalSharpBadLocus (n := n) N F ∩ G) := by
    have hc : IsCompact (T.proj ⁻¹' originalSharpBadLocus (n := n) W E) :=
      (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK
    refine hc.of_isClosed_subset ?_ (fun z hz => hFoot hz.1)
    exact (isClosed_originalSharpBadLocus hN.1 hF.1).inter
      ((isClosed_dimPiece hW m).preimage T.contMDiff_proj.continuous)
  have hReg : ∀ y ∈ N, y ∈ V → RegularAtDim (n := n) N y m := by
    intro y hy hyV
    have hTO := isGeoTestTower_restrict O hW IdealWeightPowers.isCoherent_unitIdeal T hT
    rw [template_pullback (Y := CMfd.of (n := n) O) (Subtype.val : O → X) W []] at hTO
    simp only [List.map_nil] at hTO
    have hpure : ∀ x ∈ (Subtype.val : O → X) ⁻¹' W,
        RegularAtDim (n := n) ((Subtype.val : O → X) ⁻¹' W) x m := by
      intro x hx
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
        (mem_dimPiece_of_mem_pieceOpen hW.1 m hx x.property).2
    obtain ⟨-, hr⟩ := HironakaG34CarrierPureDimension.geoTransformAlong_N_regularAtDim
      (X := CMfd.of (n := n) O) (geometricTemplate ((Subtype.val : O → X) ⁻¹' W) [])
      (hW.1.preimage continuous_subtype_val) hpure (restrict O T) hTO
    let p : openPreimage T O := ⟨y, hyV⟩
    have hNr : (geoTransformAlong (geometricTemplate ((Subtype.val : O → X) ⁻¹' W) [])
        (restrict O T)).N = (Subtype.val : openPreimage T O → Y) ⁻¹' N := by
      rw [N_geoTransformAlong]
      exact strictAlong_restrict O T W
    have hp : p ∈ (geoTransformAlong (geometricTemplate ((Subtype.val : O → X) ⁻¹' W) [])
        (restrict O T)).N := by
      rw [hNr]
      exact hy
    have hrp := hr p hp
    rw [hNr] at hrp
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hrp
  obtain ⟨Z, S, hSM, hSFull, hSSharp, hSNC'⟩ :=
    exists_piece_phase hn hN hF hdenseN V G hGV hNVG hKT m hm hReg
  refine ⟨Z, S, ?_, ?_, ?_, ?_⟩
  · rw [geometric_test_append_iff]
    refine ⟨hT, ?_⟩
    have hsub : (geoTransformAlong (geometricTemplate W []) T).E.Sublist F := by
      rw [← hFdef]
      exact List.sublist_append_right _ _
    exact geometric_test_of_test (geometricTemplate N F) _ hsub S hSM
  · refine (isGeoTestTower_append_iff _ T S).mpr ⟨hFull, ?_⟩
    rw [template_current (univ : Set X) E T, strict_univ T]
    exact hSFull
  · exact currentSharp_append W E T S hSharp hSSharp
  · intro z hz hzD
    rw [MemberInterLocusAlong.strictAlong_append T W S] at hz ⊢
    have hEq : (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E =
        (geoTransformAlong (geometricTemplate (univ : Set Y) F) S).E := by
      rw [geoTransformAlong_append, template_current (univ : Set X) E T, strict_univ T]
    rw [hEq]
    rw [BlowupTower.proj_append] at hzD
    rcases hzD with hzD | hzP
    · by_contra hnc
      obtain ⟨hFootS, -⟩ :=
        HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hN.1 hF.1 S hSSharp
      have hbad : z ∈ originalSharpBadLocus (n := n) (strictAlong S N)
          (geoTransformAlong (geometricTemplate (univ : Set Y) F) S).E := ⟨hz, hnc⟩
      obtain ⟨hzN, hncN⟩ := hFootS hbad
      exact hncN (hD (S.proj z) hzN hzD)
    · exact hSNC' z hz (dimPiece_subset_pieceOpen hW.1 m hzP)

/-- **The sharp cleanup of a non-pure `W` of dimension `≤ 3`.**  `W` a closed submanifold all of whose
points have dimension `≤ 3`, `E` simple normal crossings, `W` dense off `E`, compact original sharp bad
locus: the whole sharp cleanup output, unconditionally. -/
theorem exists_actual_sharp_cleanup_dim_le_three_nonpure
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hDim : ∀ x ∈ W, ∃ m ≤ 3, RegularAtDim (n := n) W x m)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  have key : ∀ k : ℕ, k ≤ 4 → ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      ∀ z ∈ strictAlong T W, T.proj z ∈ {x | ∃ m < k, x ∈ dimPiece W m} →
        normalCrossingsAt (n := n) (strictAlong T W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨X, .refl, trivial, trivial, trivial,
        fun z _ hz => absurd hz.choose_spec.1 (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨Y, T, hT, hFull, hSharp, hD⟩ := ih (by omega)
      obtain ⟨Z, S, hTS, hFullS, hSharpS, hNC⟩ :=
        exists_piece_step hn hW hE hdense hK k (by omega) T hT hFull hSharp _ hD
      refine ⟨Z, T.append S, hTS, hFullS, hSharpS, fun z hz hzk => hNC z hz ?_⟩
      obtain ⟨m, hm, hmem⟩ := hzk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · exact Or.inl ⟨m, h, hmem⟩
      · subst h
        exact Or.inr hmem
  obtain ⟨Y, U, hU, hFullU, hSharpU, hNCU⟩ := key 4 le_rfl
  obtain ⟨-, hOver⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hW.1 hE.1 U hSharpU
  obtain ⟨hNsm, hSNC, -, -, -⟩ :=
    actual_recorded_tower_residual_dictionary hn hW hE hdense U hU hFullU
  have hFdef : E.map (strictAlong U) ++ (geoTransformAlong (geometricTemplate W []) U).E =
      (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E := by
    have h := full_boundary_split W E [] U
    simp only [List.append_nil] at h
    exact h.symm
  have hAN : (geoTransformAlong (geometricTemplate W []) U).N = strictAlong U W :=
    N_geoTransformAlong _ U
  refine ⟨Y, U, hU, hFullU, hSharpU, hOver, hNsm, ?_, ?_,
    HironakaLocalPrincipalization.isProperMap_proj U,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ U hOver⟩
  · rw [← hFdef]
    exact hSNC
  · show HasNormalCrossings n (geoTransformAlong (geometricTemplate W []) U).N
      (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
    rw [hAN]
    intro z hz
    have hzW : U.proj z ∈ W := MemberInterTowerAlong.strictAlong_subset_preimage U hW.1 hz
    obtain ⟨m, hm, hreg⟩ := hDim _ hzW
    exact hNCU z hz ⟨m, by omega, hzW, hreg⟩

end Main

end
end Hironaka.HironakaG34NonPureLowDim
