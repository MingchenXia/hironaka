import Hironaka.Resolution.HironakaG34ProtectedLowerStep
import Hironaka.Resolution.HironakaG34ProtectionNCCentre
import Hironaka.Resolution.HironakaSharpBadProcessedWindowGeometry

/-! # The lower centre near a prepared row is a stratum; protected-or-empty lower steps (G4K1B, route B)

Lane G34 (run 0080, round 4).  Blueprint: `hironaka-g34-resume-lower-centre-strata.tex`.

Setting: the lower entry of row `j` (actual prefix with both geometric tests, all rows of order `≤ 1`,
carrier pure of dimension `d + 1`, empty true distinct defect), a prepared row `i ≠ j` (normal
crossings and density of its support `S_i` with its boundary `F_i`), and the lower centre `C` = the
maximum locus of the marked-stratum history value of `(S_j, [], I(B_j), 1)`.

* `exists_sharp_bad_processed_window_stratum`: the held processed-window geometry with ONE more
  output, the auxiliary fibre `Z` is the stratum of `F_i` through the point on the carrier (the proof
  is the held one, verbatim; its helpers are private upstream and copied verbatim).
* `actual_lower_centre_stratum_window` / `actual_lower_centre_eventually_stratum` (**union-of-strata
  form**, caveat (c) of `REPORT-r3.md`): near every point `x` of `C ∩ S_i` the centre is the stratum
  of `F_i` through `x` on the carrier: `∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ N ∧ ∀ D ∈ F_i, x ∈ D → y ∈ D`; on a
  window it is `N ∩ memberInter F_i R`, `R` the members through `x`.
* `actual_lower_centre_protected_window` (caveat (b)): on that window the trace of `C` lies in the
  carrier, is TRANSVERSE to the auxiliary hypersurface `Haux` and has normal crossings with
  `Haux :: F_i` — all hypotheses of `protection_of_nc_centre` (no transversality left open).
* `actual_lower_step_protected_or_empty`: for ANY blowup `π` along `C` and every point `x` of `S_i`:
  either `x ∉ C` and the step is literally empty over an open `U ∋ x`, or `x ∈ C` and over a window
  `V ∋ x` the restricted blowup is the blowup of `V` along a stratum of the protected configuration,
  and the configuration stays protected (`protection_of_nc_centre` applied to the restricted blowup).
* `actual_row_prepared_of_lower_bad_empty`: at the lower entry, if `B_j = ∅` then row `j` is prepared
  (the terminal round of the lower phase of row `j`).
* `exists_actual_protected_lower_round_or_terminal`: each round (carrier phase, then the lower step)
  either ends the lower phase of row `j` (`B_j = ∅` after the carrier phase, and `insert j P` is
  prepared) or performs one protected lower step keeping `P` prepared. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34LowerCentreStrata
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  Hironaka.RegularLocusDense BlowupTowers BlowupTowerTransforms
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan
  RestrictedIdealExtension GermIdealOrder HironakaG4PreparedCentreCoordinates
  InvertibleIdealQuotient MonomialPartAlong DivisorExponentAlong GiraudAlong
  HironakaSharpOriginalProductTraceOrder
  HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualTraceIncidence
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsSNCBlockCarrier
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumNativeFields
  HironakaActualProtectedOtherRowLocalStep HironakaG4LowerPreparedNeighborhood
open HironakaSharpNormalCrossingsOpenLocus MarkedIdealRestrictOpen HironakaOriginalNCCountHistory
  HironakaOriginalNCMarkedStratum MarkedIdealBiholomorphism
open HomogenizedGlueingTower (strictAlong)
open HironakaSharpBadProcessedWindowGeometry
variable {n : ℕ} {X Y : CMfd.{u} n}

/-! ### Private verbatim copies (private upstream in `HironakaSharpBadProcessedWindowGeometry`) -/

theorem exists_sharp_bad_processed_window_stratum
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x≤1)
    (i j : Fin E.length) (hne : j≠i)
    (hNCi : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDensei : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si⊆closure (Si \ ⋃ H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H)) :
    let A:=geoTransformAlong (geometricTemplate W []) T
    let old:=E.map (strictAlong T)
    let J:=fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si:=A.N∩(J i).zeroLocus
    let L:=A.N∩(J j).zeroLocus
    let Fi:=old.eraseIdx i.val++A.E
    let Fj:=old.eraseIdx j.val++A.E
    let Bj:=originalSharpBadLocus (n:=n) L Fj
    let H:=⋃D∈Fj,D
    let Mbad : MarkedIdeal n Y:=⟨L,[],vanishingIdeal (n:=n) Bj,1⟩
    ∀ (_hIbad : (vanishingIdeal (n:=n) Bj).IsCoherent)
      (_hLowerDense : L⊆closure (L \ ⋃D∈Fj,D))
      (x : Y), x∈Bj∩Si →
      let q:=oldCount H (BlowupTower.refl : BlowupTower Y Y) x
      ∃ (U : Opens Y) (hxU : x∈U) (Haux Z : Set U)
        (Φ : LocalHolomorphicEquivAt (n:=n)
          (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩))
        (SL SZ : Finset (Fin n)),
        let NU:=(Subtype.val : U→Y) ⁻¹' A.N
        let LU:=(Subtype.val : U→Y) ⁻¹' L
        let FiU:=Fi.map ((Subtype.val : U→Y) ⁻¹' ·)
        let MU:=MarkedIdeal.pullback (Subtype.val : U→Y) Mbad
        let QU : Set U:={p | q≤oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val}
        (∀p : U, oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val≤q) ∧
        IsClosedSubmanifold n Z ∧
        (∀p : U, p∈Z ↔ p.val∈A.N ∧ ∀D∈Fi,x∈D→p.val∈D) ∧
        Z⊆LU ∧ Z⊆(Subtype.val : U→Y) ⁻¹' Bj ∧
        (∀p : U, p∈Z ↔ p.val∈Bj ∧ oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val=q) ∧
        markedStratum (X:=CMfd.of (n:=n) U) MU QU=(⟨LU,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n U) ∧
        (Subtype.val : U→Y) ⁻¹' Si=NU∩Haux ∧
        IsSNCDivisor n (Haux::FiU) ∧ IsTransverse n NU (Haux::FiU) ∧
        HasNormalCrossings n Z (Haux::FiU) ∧
        SL⊆SZ ∧ Φ.source⊆(chartAt (ComplexModel n) (⟨x,hxU⟩ : U)).target ∧
        Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩)=0 ∧
        (∀p∈flatDomain Φ, p∈LU ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SL) ∧
        (∀p∈flatDomain Φ, p∈Z ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SZ) := by
  exact exists_sharp_bad_processed_window_stratum_core hn hW hE hdense T hT hFull
    hOrd i j hne hNCi hDensei

/-! ### Private verbatim copy (private upstream in `HironakaActualSharpBadMaximumProcessedSlice`) -/

/-- Restrict the ENTIRE processed-window chart through a genuine open
embedding. Every original position stays its actual preimage. -/
private theorem processed_geometry_subopen
    {N S : Set Y} (F : List (Set Y))
    (U V : Opens Y) (hVU : V ≤ U) (Haux Z : Set U)
    (hSlice : (Subtype.val : U → Y) ⁻¹' S =
      (Subtype.val : U → Y) ⁻¹' N ∩ Haux)
    (hSNC : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)))
    (hTr : IsTransverse n ((Subtype.val : U → Y) ⁻¹' N)
      (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)))
    (hNC : HasNormalCrossings n Z (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·))) :
    let ι : V → U := fun z => ⟨z.val, hVU z.property⟩
    ∃ H' : Set V,
      (Subtype.val : V → Y) ⁻¹' S = (Subtype.val : V → Y) ⁻¹' N ∩ H' ∧
      IsSNCDivisor n (H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : V → Y) ⁻¹' N)
        (H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·)) ∧
      HasNormalCrossings n (ι ⁻¹' Z) (H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·)) := by
  let ι : V → U := fun z => ⟨z.val, hVU z.property⟩
  have hEmb : HironakaBaseChange.IsOpenHoloEmbedding n ι :=
    (HironakaBaseChange.isOpenHoloEmbedding_val V).codRestrict U (fun z => hVU z.property)
  let H' := ι ⁻¹' Haux
  have hMap : (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)).map (ι ⁻¹' ·) =
      H' :: F.map ((Subtype.val : V → Y) ⁻¹' ·) := by
    simp only [List.map_cons, List.map_map]
    rfl
  have hSlice' : (Subtype.val : V → Y) ⁻¹' S = (Subtype.val : V → Y) ⁻¹' N ∩ H' :=
    congrArg (fun D : Set U => ι ⁻¹' D) hSlice
  refine ⟨H', hSlice', ?_, ?_, ?_⟩
  · have h := isSNCDivisor_map_preimage hEmb.pullsBackCoordinates hEmb.continuous hSNC
    rw [hMap] at h
    exact h
  · have h := isTransverse_preimage hEmb.pullsBackCoordinates hTr
    rw [hMap] at h
    exact h
  · have h := hasNormalCrossings_preimage hEmb.pullsBackCoordinates hNC
    rw [hMap] at h
    exact h
/-! ### The lower centre near a prepared row -/

section Strata

open HironakaSharpActualChronologicalDistinctDefect HironakaG4CompactWholeMonomialMaskPhase
  RestrictEmptyTower HironakaG34PreparedRowEmptyTail
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)

/-- **Window form of the union-of-strata statement.**  Near every point `x` of the lower centre `C`
on a prepared support `S_i`, on an open window `V ∋ x` carrying the protected configuration
(`S_i = N ∩ Haux`, `Haux :: F_i` SNC and transverse to `N`), the centre is exactly the stratum of the
row's boundary `F_i` through `x` on the carrier. -/
theorem actual_lower_centre_stratum_window
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked
            (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n)
        (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (i j : Fin E.length) (hne : j ≠ i)
    (hNCi : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si
        ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDensei : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈
        (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si := A.N ∩ (J i).zeroLocus
    let L := A.N ∩ (J j).zeroLocus
    let Fi := old.eraseIdx i.val ++ A.E
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue M H
        (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
    ∀ x ∈ C ∩ Si, ∃ (V : Opens Y), x ∈ V ∧
      ∃ Haux : Set V,
        (Subtype.val : V → Y) ⁻¹' Si = (Subtype.val : V → Y) ⁻¹' A.N ∩ Haux ∧
        IsSNCDivisor n (Haux :: Fi.map ((Subtype.val : V → Y) ⁻¹' ·)) ∧
        IsTransverse n ((Subtype.val : V → Y) ⁻¹' A.N)
          (Haux :: Fi.map ((Subtype.val : V → Y) ⁻¹' ·)) ∧
        ∀ p : V, p.val ∈ C ↔ p.val ∈ A.N ∧ ∀ D ∈ Fi, x ∈ D → p.val ∈ D := by
  dsimp only
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  let L := A.N ∩ (J j).zeroLocus
  let Fi := old.eraseIdx i.val ++ A.E
  let Fj := old.eraseIdx j.val ++ A.E
  let Bj := originalSharpBadLocus (n := n) L Fj
  let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
  let H := ⋃ D ∈ Fj, D
  obtain ⟨hL, _hLreg, hLF, hM, hAdapt⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd d hReg hDistinct j
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n Fj := isSNCDivisor_of_sublist hRecorded.2.1
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl A.E))
  have hBclosed : IsClosed Bj := isClosed_originalSharpBadLocus hL.1 hFj.1
  have hCos : M.cosupp = Bj :=
    SmoothCentreLocus.cosupp_vanishingIdeal hBclosed (fun _ hx => hx.1)
  intro x hx
  have hxBj : x ∈ Bj := hCos ▸ hx.1.1
  obtain ⟨U, hxU, Haux, Z, Φ, SL, SZ, hBound, hZ, hZiff, hZL, _hZB, hFibre,
      hRecord, hSlice, hSNC, hTr, hNC, hMask, hsrc, hzero, hLflat, hZflat⟩ :=
    exists_sharp_bad_processed_window_stratum
      hn hW hE hdense T hT hFull hOrd i j hne hNCi hDensei
      hM.isWellFormed.isCoherent hLF x ⟨hxBj, hx.2⟩
  let q := oldCount H (BlowupTower.refl : BlowupTower Y Y) x
  have hUV : U ≤ HironakaOriginalNCCausalHistoryValue.oldCountLowOpen H (BlowupTower.refl : BlowupTower Y Y) q := by
    intro y hy
    exact hBound ⟨y, hy⟩
  have hpZ : (⟨x, hxU⟩ : U) ∈ Z := (hFibre _).mpr ⟨hxBj, rfl⟩
  have hFibreM : ∀ z : U, z ∈ Z ↔ z.val ∈ M.cosupp ∧
      oldCount H (BlowupTower.refl : BlowupTower Y Y) z.val = q := by
    intro z
    rw [hCos]
    exact hFibre z
  obtain ⟨W', hWo, hxW, hEq⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.native_maximum_germ_of_flat_auxiliary
      M hM hAdapt q U hUV Z hZ.1 hZL hFibreM hRecord
      (⟨x, hxU⟩ : U) hpZ hx.1 Φ hsrc hzero SL SZ hMask hLflat hZflat
  let V : Opens Y := ⟨(Subtype.val : U → Y) '' W', U.isOpen.isOpenMap_subtype_val W' hWo⟩
  have hxV : x ∈ V := ⟨⟨x, hxU⟩, hxW, rfl⟩
  have hVU : V ≤ U := by
    intro y hy
    obtain ⟨z, _hzW, hzy⟩ := hy
    rw [← hzy]
    exact z.property
  let ι : V → U := fun y => ⟨y.val, hVU y.property⟩
  have hInW (y : V) : ι y ∈ W' := by
    obtain ⟨z, hzW, hzy⟩ := y.property
    have he : ι y = z := Subtype.ext hzy.symm
    rw [he]
    exact hzW
  obtain ⟨H', hSlice', hSNC', hTr', _hNC'⟩ :=
    processed_geometry_subopen (N := A.N) (S := Si) Fi U V hVU Haux Z
      hSlice hSNC hTr hNC
  exact ⟨V, hxV, H', hSlice', hSNC', hTr',
    fun p => (hEq (ι p) (hInW p)).trans (hZiff (ι p))⟩

/-- **Union-of-strata form of the lower centre near a prepared row** (germ form): at every point `x`
of the lower centre on a prepared support `S_i`, the germ of the centre is the germ of the stratum of
`F_i` through `x` on the carrier. -/
theorem actual_lower_centre_eventually_stratum
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked
            (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n)
        (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (i j : Fin E.length) (hne : j ≠ i)
    (hNCi : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si
        ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDensei : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈
        (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si := A.N ∩ (J i).zeroLocus
    let L := A.N ∩ (J j).zeroLocus
    let Fi := old.eraseIdx i.val ++ A.E
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue M H
        (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
    ∀ x ∈ C ∩ Si, ∀ᶠ y in 𝓝 x, (y ∈ C ↔ y ∈ A.N ∧ ∀ D ∈ Fi, x ∈ D → y ∈ D) := by
  intro A old J Si L Fi Fj Bj M H C x hx
  obtain ⟨V, hxV, -, -, -, -, hV⟩ := actual_lower_centre_stratum_window hn hW hE hdense T hT hFull
    hOrd d hReg hDistinct i j hne hNCi hDensei x hx
  filter_upwards [V.isOpen.mem_nhds hxV] with y hy
  exact hV ⟨y, hy⟩

/-- **The lower centre is protected near a prepared row** (closes caveat (b)): on the window of
`actual_lower_centre_stratum_window` the trace of the centre is the stratum `N ∩ memberInter F_i R`
(`R` = the members through `x`), lies in the carrier, is transverse to the auxiliary hypersurface and
has normal crossings with `Haux :: F_i`: all hypotheses of `protection_of_nc_centre`. -/
theorem actual_lower_centre_protected_window
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked
            (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n)
        (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (i j : Fin E.length) (hne : j ≠ i)
    (hNCi : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si
        ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDensei : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈
        (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si := A.N ∩ (J i).zeroLocus
    let L := A.N ∩ (J j).zeroLocus
    let Fi := old.eraseIdx i.val ++ A.E
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue M H
        (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
    ∀ x ∈ C ∩ Si, ∃ (V : Opens Y) (hxV : x ∈ V) (Haux : Set V),
      let NV := (Subtype.val : V → Y) ⁻¹' A.N
      let FiV := Fi.map ((Subtype.val : V → Y) ⁻¹' ·)
      let CV := (Subtype.val : V → Y) ⁻¹' C
      (Subtype.val : V → Y) ⁻¹' Si = NV ∩ Haux ∧
      IsSNCDivisor n (Haux :: FiV) ∧ IsTransverse n NV (Haux :: FiV) ∧
      CV = NV ∩ BoundaryCount.memberInter FiV
        (Finset.univ.filter fun a : Fin FiV.length => (⟨x, hxV⟩ : V) ∈ FiV.get a) ∧
      CV ⊆ NV ∧ IsTransverse n CV [Haux] ∧ HasNormalCrossings n CV (Haux :: FiV) := by
  intro A old J Si L Fi Fj Bj M H C x hx
  obtain ⟨V, hxV, Haux, hSlice, hSNC, hTr, hV⟩ := actual_lower_centre_stratum_window hn hW hE
    hdense T hT hFull hOrd d hReg hDistinct i j hne hNCi hDensei x hx
  let NV := (Subtype.val : V → Y) ⁻¹' A.N
  let FiV := Fi.map ((Subtype.val : V → Y) ⁻¹' ·)
  let CV := (Subtype.val : V → Y) ⁻¹' C
  let xV : V := ⟨x, hxV⟩
  let R : Finset (Fin FiV.length) := Finset.univ.filter fun a : Fin FiV.length => xV ∈ FiV.get a
  have hStr : CV = NV ∩ BoundaryCount.memberInter FiV R := by
    ext p
    change p.val ∈ C ↔ p.val ∈ A.N ∧ p ∈ BoundaryCount.memberInter FiV R
    rw [hV p]
    refine and_congr Iff.rfl ?_
    exact ((incident_preimage_iff Fi xV p).symm.trans
      (incident_member_inter_iff (Y := CMfd.of (n := n) V) FiV xV p).symm)
  obtain ⟨hCN, hCH, hCNC⟩ := HironakaG34ProtectionNCCentre.nc_centre_of_local_strata
    (X := CMfd.of (n := n) V) (C := CV) hn hSNC hTr (fun p hp => ⟨R, hStr ▸ hp,
      Filter.Eventually.of_forall fun y => by rw [hStr]⟩)
  exact ⟨V, hxV, Haux, hSlice, hSNC, hTr, hStr, hCN, hCH, hCNC⟩

/-- **Each lower step is protected or literally empty near every point of a prepared support.**
For ANY blowup `π` along the lower centre `C` and every point `x` of a prepared support `S_i`
(`i ≠ j`): either `x ∉ C`, and the step restricted to an open `U ∋ x` is the empty tower; or
`x ∈ C`, and over a window `V ∋ x` carrying the protected configuration the restricted map `ρ` is the
blowup of `V` along the stratum `N ∩ memberInter F_i R`, after which the configuration is again
protected (`protection_of_nc_centre`): the strict carrier is a closed submanifold, `H' :: F'` is SNC
and transverse to it, the strict transform of `S_i` is `N' ∩ H'`, a closed submanifold whose ideal is
the relative strict transform of `I(S_i)`, with normal crossings with `F'` and dense off `F'`. -/
theorem actual_lower_step_protected_or_empty
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked
            (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n)
        (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (i j : Fin E.length) (hne : j ≠ i)
    (hNCi : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si
        ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDensei : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈
        (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si := A.N ∩ (J i).zeroLocus
    let L := A.N ∩ (J j).zeroLocus
    let Fi := old.eraseIdx i.val ++ A.E
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue M H
        (BlowupTower.refl : BlowupTower Y Y)) M.cosupp
    ∀ {Z : CMfd.{u} n} (π : Z → Y) (hπ : IsBlowupAlong n C π), ∀ x ∈ Si,
      (x ∉ C ∧ ∃ U : Opens Y, x ∈ U ∧ IsEmptyTower (restrict U (.step .refl C π hπ))) ∨
      (x ∈ C ∧ ∃ (V : Opens Y) (hxV : x ∈ V) (Haux : Set V),
        let NV := (Subtype.val : V → Y) ⁻¹' A.N
        let FiV := Fi.map ((Subtype.val : V → Y) ⁻¹' ·)
        let CV := (Subtype.val : V → Y) ⁻¹' C
        let WV : Opens Z := ⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩
        let ρ : WV → V := fun z => ⟨π z.val, z.property⟩
        let N' := BlowupStrictSubmanifold.geoStrictTransform ρ CV NV
        let H' := BlowupStrictSubmanifold.geoStrictTransform ρ CV Haux
        let F' := FiV.map (BlowupStrictSubmanifold.geoStrictTransform ρ CV) ++ [ρ ⁻¹' CV]
        let Z' := BlowupStrictSubmanifold.geoStrictTransform ρ CV (NV ∩ Haux)
        (Subtype.val : V → Y) ⁻¹' Si = NV ∩ Haux ∧
        IsSNCDivisor n (Haux :: FiV) ∧ IsTransverse n NV (Haux :: FiV) ∧
        CV = NV ∩ BoundaryCount.memberInter FiV
          (Finset.univ.filter fun a : Fin FiV.length => (⟨x, hxV⟩ : V) ∈ FiV.get a) ∧
        IsBlowupAlong n CV ρ ∧
        IsClosedSubmanifold n N' ∧ IsSNCDivisor n (H' :: F') ∧ IsTransverse n N' (H' :: F') ∧
        Z' = N' ∩ H' ∧ IsClosedSubmanifold n Z' ∧
        HironakaSharpActualChronologicalStrictStep.nextRelativeStrict (X := CMfd.of (n := n) V) (Y := CMfd.of (n := n) WV) NV
          (vanishingIdeal (n := n) (NV ∩ Haux)) CV ρ = vanishingIdeal (n := n) Z' ∧
        HasNormalCrossings n Z' F' ∧ Z' ⊆ closure (Z' \ ⋃ K ∈ F', K)) := by
  intro A old J Si L Fi Fj Bj M H C Z π hπ x hxS
  by_cases hxC : x ∈ C
  · right
    obtain ⟨V, hxV, Haux, hSlice, hSNC, hTr, hStr, hCN, hCH, hCNC⟩ :=
      actual_lower_centre_protected_window hn hW hE hdense T hT hFull hOrd d hReg hDistinct
        i j hne hNCi hDensei x ⟨hxC, hxS⟩
    have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
    have hNV : IsClosedSubmanifold n ((Subtype.val : V → Y) ⁻¹' A.N) :=
      BlowupRestrictOpen.isClosedSubmanifold_preimage_val hRecorded.1 V
    have hρ := BlowupRestrictOpen.isBlowupAlong_restrict hπ V
      (V.isOpen.preimage hπ.contMDiff.continuous)
    refine ⟨hxC, V, hxV, Haux, hSlice, hSNC, hTr, hStr, hρ, ?_⟩
    exact HironakaG34ProtectionNCCentre.protection_of_nc_centre
      (X := CMfd.of (n := n) V)
      (Y := CMfd.of (n := n) (⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩ : Opens Z))
      hn hNV hSNC hTr hCN hCNC hCH hρ
  · left
    refine ⟨hxC, ⟨Cᶜ, hπ.1.1.isOpen_compl⟩, hxC, ?_⟩
    exact (isEmptyTower_restrict_iff _ _).mpr ⟨trivial, disjoint_compl_right⟩

/-- **The terminal round of the lower phase of row `j`.** At the lower entry (every row of order
`≤ 1`, carrier pure of dimension `d + 1`, empty true distinct defect), if the lower sharp bad locus
`B_j` is empty then row `j` is prepared. -/
theorem actual_row_prepared_of_lower_bad_empty
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked
            (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n)
        (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (j : Fin E.length)
    (hBad : originalSharpBadLocus (n := n)
      ((geoTransformAlong (geometricTemplate W []) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
      ((E.map (strictAlong T)).eraseIdx j.val ++
        (geoTransformAlong (geometricTemplate W []) T).E) = ∅) :
    ActualRowPrepared W E j T := by
  obtain ⟨_hL, _hLreg, hLF, _hM, _hAdapt⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd d hReg hDistinct j
  have hNj := (chronologicalMarked_geometric_fields
    (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  refine ⟨?_, ?_, hLF⟩
  · rw [hNj]
    exact fun y hy => hOrd y hy j
  · dsimp only
    intro x hx
    by_contra hnot
    have hmem : x ∈ originalSharpBadLocus (n := n)
        ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
        ((E.map (strictAlong T)).eraseIdx j.val ++
          (geoTransformAlong (geometricTemplate W []) T).E) := ⟨hx, hnot⟩
    rw [hBad] at hmem
    exact hmem

/-- **A protected lower round, or the end of the lower phase of row `j`.**  From any actual prefix
with current sharp centres and prepared rows `P ∌ j`: the carrier phase `Q` (centres over the true
defect, literally empty near every prepared support, keeping `P` prepared) reaches the lower entry
(all rows of order `≤ 1`, carrier pure of dimension `d + 1`, empty true distinct defect); there,
EITHER `B_j = ∅` and row `j` is prepared as well (the lower phase of row `j` is over), OR `B_j ≠ ∅`
and the blowup along the lower centre `C` is again an actual prefix with current sharp centres,
`C ⊆ B_j` has normal crossings with the full boundary and every row of `P` is prepared after it.
At the entry `T·Q` the hypotheses of `actual_lower_step_protected_or_empty` hold for every `i ∈ P`,
so that step is protected or literally empty near every point of every prepared support. -/
theorem exists_actual_protected_lower_round_or_terminal (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length) (hj : j ∉ P) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      let U := T.append Q
      let A := geoTransformAlong (geometricTemplate W []) U
      let old := E.map (strictAlong U)
      let Jj := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) U).ideal
      let L := A.N ∩ Jj.zeroLocus
      let Fj := old.eraseIdx j.val ++ A.E
      let Bj := originalSharpBadLocus (n := n) L Fj
      let M : MarkedIdeal n Z := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
      let C := maxLocus (markedStratumHistoryValue M (⋃ D ∈ Fj, D)
        (BlowupTower.refl : BlowupTower Z Z)) M.cosupp
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      (∀ i ∈ P, ∃ V : Opens Y,
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ V ∧
        IsEmptyTower (restrict V Q)) ∧
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      (∀ x ∈ A.N, ∀ a : Fin E.length, ordinaryTraceOrder A.N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) U).ideal x ≤ 1) ∧
      (∀ x ∈ A.N, RegularAtDim (n := n) A.N x (d+1)) ∧
      chronologicalDistinctDefect W E U = ∅ ∧
      (∀ i ∈ P, ActualRowPrepared W E i U) ∧
      ((Bj = ∅ ∧ ActualRowPrepared W E j U) ∨
        (Bj.Nonempty ∧ ∃ (Z' : CMfd.{u} n) (pi : Z' → Z) (hpi : IsBlowupAlong n C pi),
          IsGeoTestTower (geometricTemplate W []) (.step U C pi hpi) ∧
          IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step U C pi hpi) ∧
          CurrentSharpCentres W E (.step U C pi hpi) ∧
          C.Nonempty ∧ C ⊆ Bj ∧ HasNormalCrossings n C (old ++ A.E) ∧
          ∀ i ∈ P, ActualRowPrepared W E i (.step U C pi hpi))) := by
  obtain ⟨Z, Q, hTQ, hFullTQ, hSharpTQ, hOver, hEmpty, hRows, hProt⟩ :=
    HironakaG34DefectEmptyOrder.exists_actual_carrier_phase_protected hn hW hE hdense d hRegW hK
      T hT hFull hSharp
  have hPQ : ∀ i ∈ P, ActualRowPrepared W E i (T.append Q) := by
    intro i hi
    obtain ⟨U, hSU, hEmptyU⟩ := hProt i (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2
    exact (actual_prepared_row_empty_tail hn hW hE hdense i T hT hFull (hP i hi) U hSU Q hTQ
      hEmptyU).1
  have hRegQ := HironakaG34CarrierPureDimension.actual_carrier_regularAtDim hW d hRegW
    (T.append Q) hTQ
  refine ⟨Z, Q, hOver, fun i hi => hProt i (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2, hTQ, hFullTQ,
    hSharpTQ, hRows, hRegQ, hEmpty, hPQ, ?_⟩
  by_cases hNe : (originalSharpBadLocus (n := n)
      ((geoTransformAlong (geometricTemplate W []) (T.append Q)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).ideal.zeroLocus)
      ((E.map (strictAlong (T.append Q))).eraseIdx j.val ++
        (geoTransformAlong (geometricTemplate W []) (T.append Q)).E)).Nonempty
  · right
    obtain ⟨-, hStep⟩ := HironakaG34ProtectedLowerStep.actual_lower_step_keeps_prepared hn hW hE
      hdense hK (T.append Q) hTQ hFullTQ hSharpTQ hRows d hRegQ hEmpty P hPQ j hj
    obtain ⟨Z', pi, hpi, hTn, hFn, hSn, hCne, hCB, hCNC, hPn⟩ := hStep hNe
    exact ⟨hNe, Z', pi, hpi, hTn, hFn, hSn, hCne, hCB, hCNC, hPn⟩
  · left
    have hBad := Set.not_nonempty_iff_eq_empty.mp hNe
    exact ⟨hBad, actual_row_prepared_of_lower_bad_empty hn hW hE hdense (T.append Q) hTQ hFullTQ
      hRows d hRegQ hEmpty j hBad⟩

end Strata

end
end Hironaka.HironakaG34LowerCentreStrata
