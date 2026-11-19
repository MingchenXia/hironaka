import Hironaka.Resolution.HironakaG34LowerTemplateBridge
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Invariant.CodimOneAdmissibleAlong

/-! # Surfaces: the sharp cleanup of every `(W, E)` with `W` pure of dimension 2 (route (L), `d = 1`)

Lane G34 (run 0080, round 6).  Blueprint: `hironaka-g34-resume-surface-sharp-cleanup.tex`.

The terminating driver of `HironakaG34LowerCleanupLift` is conditional on the named statement
`CertifiedLowerCleanupsExist W E d`.  For `d = 1` (`W` pure of dimension `2`) it is PROVED here (given
only the static hypotheses and the compactness of the original sharp bad locus):

* `eventually_mem_iff_eq_of_regularAtDim_zero`, `hasNormalCrossings_of_regularAtDim_zero` (point NC):
  a set all of whose points are regular of dimension `0` has normal crossings with every simple normal
  crossings divisor.
* `regularAtDim_zero_of_subset_sharpBad`: along a tower with the two zero-mark tests of a CURVE problem
  `(Z, F)`, every closed submanifold inside the current sharp bad locus is zero-dimensional (the current
  carrier is a curve, dense off the current boundary by the held recorded-tower dictionary, so the bad
  locus is thin; `ThinDimensionDrop`).
* `PointCentres`, `pointCentres_of_curve_sharp`: hence a curve problem's sharp towers have point
  centres.
* `protectedTail_of_pointCentres`: a tail with zero-dimensional centres is a protected tail for every
  set of prepared rows (window from the held `protected_slice_window`, normal crossings of a point).
* `lower_dense_of_two_tests` (density of the strict lower carrier off the transformed lower boundary,
  from the held dictionary).
* `certifiedLowerCleanupsExist_one`: the named statement for `d = 1`, from the UNCONDITIONAL curve
  cleanup `exists_actual_sharp_cleanup_dim_one` applied to each lower problem `(S_j, F_j)`.
* `exists_actual_sharp_cleanup_dim_two`: the sharp cleanup of every `(W, E)` with `W` pure of
  dimension `2`, UNCONDITIONAL (static hypotheses and compact bad locus only). -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34SurfaceSharpCleanup
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail
  HomogenizedGlueingTower HironakaG4RecordedTowerResidualCompatibility
  HironakaG34LowerCleanupLift RestrictEmptyTower

section Points
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- **A regular point of dimension `0` is isolated** (in germ form). -/
theorem eventually_mem_iff_eq_of_regularAtDim_zero {A : Set M} {y : M}
    (hy : RegularAtDim (n := n) A y 0) : ∀ᶠ z in 𝓝 y, z ∈ A ↔ z = y := by
  have hyA : y ∈ A := hy.2.1
  obtain ⟨-, -, Φ, -, hzero, hflat⟩ := hy
  have hO : IsOpen ((complexChartAt (n := n) y).val.source ∩
      (complexChartAt (n := n) y).val ⁻¹' Φ.source) :=
    (complexChartAt (n := n) y).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) y).val.open_source Φ.isOpen_source
  filter_upwards [hO.mem_nhds ⟨mem_complexChartAt_source y, Φ.center_mem_source⟩] with z hz
  obtain ⟨hzs, hzΦ⟩ := hz
  refine ⟨fun hzA => ?_, fun h => by rw [h]; exact hyA⟩
  have hz0 : Φ.toFun ((complexChartAt (n := n) y).val z) = 0 := by
    have hp := (hflat hzs hzΦ).mp hzA
    ext i
    simpa using hp i (Nat.zero_le _)
  have hez : (complexChartAt (n := n) y).val z = (complexChartAt (n := n) y).val y :=
    calc (complexChartAt (n := n) y).val z
        = Φ.invFun (Φ.toFun ((complexChartAt (n := n) y).val z)) := (Φ.left_inv _ hzΦ).symm
      _ = Φ.invFun (Φ.toFun ((complexChartAt (n := n) y).val y)) := by rw [hz0, hzero]
      _ = (complexChartAt (n := n) y).val y := Φ.left_inv _ Φ.center_mem_source
  exact (complexChartAt (n := n) y).val.injOn hzs (mem_complexChartAt_source y) hez

/-- **Points have normal crossings**: a set all of whose points are regular of dimension `0` has
normal crossings with every simple normal crossings divisor. -/
theorem hasNormalCrossings_of_regularAtDim_zero {C : Set M} {F : List (Set M)}
    (hF : IsSNCDivisor n F) (hC : ∀ x ∈ C, RegularAtDim (n := n) C x 0) :
    HasNormalCrossings n C F :=
  CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx =>
    ⟨{x}, mem_singleton x,
      (eventually_mem_iff_eq_of_regularAtDim_zero (hC x hx)).mono fun _ hz =>
        hz.trans mem_singleton_iff.symm,
      HironakaOneDimensionalCanonicalSuperlevels.hasNormalCrossings_singleton x hF⟩

end Points

section Curves
variable {n : ℕ} {Y : CMfd.{u} n}

/-- The transformed lower boundary is the strict old list followed by the born list of the carrier
template. -/
theorem lower_boundary_eq (Z : Set Y) (F : List (Set Y)) {Q : CMfd.{u} n} (R : BlowupTower Y Q) :
    (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E =
      F.map (strictAlong R) ++ (geoTransformAlong (geometricTemplate Z []) R).E := by
  rw [HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
      (geometricTemplate (univ : Set Y) F) (geometricTemplate (univ : Set Y) []) rfl R,
    HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
      (geometricTemplate Z []) (geometricTemplate (univ : Set Y) []) rfl R]
  rfl

/-- **Density of the strict carrier off the transformed boundary** along any tower with the two
zero-mark tests (the held recorded-tower dictionary, read with the single transformed boundary). -/
theorem lower_dense_of_two_tests (hn : 0 < n) {Z : Set Y} {F : List (Set Y)}
    (hZ : IsClosedSubmanifold n Z) (hF : IsSNCDivisor n F)
    (hZd : Z ⊆ closure (Z \ ⋃ H ∈ F, H))
    {Q : CMfd.{u} n} (R : BlowupTower Y Q)
    (h1 : IsGeoTestTower (geometricTemplate Z []) R)
    (h2 : IsGeoTestTower (geometricTemplate (univ : Set Y) F) R) :
    IsClosedSubmanifold n (strictAlong R Z) ∧
      strictAlong R Z ⊆ closure (strictAlong R Z \
        ⋃ H ∈ (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E, H) := by
  obtain ⟨hN, -, -, hDen, -⟩ := actual_recorded_tower_residual_dictionary hn hZ hF hZd R h1 h2
  have hNid : (geoTransformAlong (geometricTemplate Z []) R).N = strictAlong R Z :=
    N_geoTransformAlong _ R
  rw [hNid] at hN hDen
  rw [lower_boundary_eq Z F R]
  exact ⟨hN, hDen⟩

/-- **The two-template output in the single lower template**: final normal crossings of the strict
carrier with the full transformed boundary and final density give the conclusions of a lower cleanup. -/
theorem lower_nc_dense_of_two_template (Z : Set Y) (F : List (Set Y)) {Q : CMfd.{u} n}
    (R : BlowupTower Y Q)
    (hNC : HasNormalCrossings n (geoTransformAlong (geometricTemplate Z []) R).N
      (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E)
    (hDen : strictAlong R Z ⊆ closure (strictAlong R Z \
      ⋃ H ∈ (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E, H)) :
    HasNormalCrossings n (geoTransformAlong (geometricTemplate Z F) R).N
        (geoTransformAlong (geometricTemplate Z F) R).E ∧
      (geoTransformAlong (geometricTemplate Z F) R).N ⊆
        closure ((geoTransformAlong (geometricTemplate Z F) R).N \
          ⋃ D ∈ (geoTransformAlong (geometricTemplate Z F) R).E, D) := by
  have hN1 : (geoTransformAlong (geometricTemplate Z F) R).N = strictAlong R Z :=
    N_geoTransformAlong _ R
  have hN2 : (geoTransformAlong (geometricTemplate Z []) R).N = strictAlong R Z :=
    N_geoTransformAlong _ R
  have hE : (geoTransformAlong (geometricTemplate Z F) R).E =
      (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E := by
    rw [HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
        (geometricTemplate Z F) (geometricTemplate (univ : Set Y) []) rfl R,
      HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
        (geometricTemplate (univ : Set Y) F) (geometricTemplate (univ : Set Y) []) rfl R]
    rfl
  rw [hN1, hE]
  rw [hN2] at hNC
  exact ⟨hNC, hDen⟩

/-- **Centres inside the sharp bad locus of a curve problem are points.**  Along a tower with the two
zero-mark tests of `(Z, F)` with `Z` pure of dimension `1`, every closed submanifold `C` inside the
current sharp bad locus is zero-dimensional at each of its points. -/
theorem regularAtDim_zero_of_subset_sharpBad (hn : 0 < n) {Z : Set Y} {F : List (Set Y)}
    (hZ : IsClosedSubmanifold n Z) (hF : IsSNCDivisor n F)
    (hZd : Z ⊆ closure (Z \ ⋃ H ∈ F, H)) (hZreg : ∀ x ∈ Z, RegularAtDim (n := n) Z x 1)
    {Q : CMfd.{u} n} (R : BlowupTower Y Q)
    (h1 : IsGeoTestTower (geometricTemplate Z []) R)
    (h2 : IsGeoTestTower (geometricTemplate (univ : Set Y) F) R)
    {C : Set Q} (hC : IsClosedSubmanifold n C)
    (hCbad : C ⊆ originalSharpBadLocus (n := n) (strictAlong R Z)
      (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E) :
    ∀ x ∈ C, RegularAtDim (n := n) C x 0 := by
  obtain ⟨hN, hDen⟩ := lower_dense_of_two_tests hn hZ hF hZd R h1 h2
  have hthin := HironakaG4GeneralSharpBadLocus.originalSharpBadLocus_thin hN hDen
  have hreg := HironakaG34CarrierPureDimension.actual_carrier_regularAtDim hZ 0 hZreg R h1
  have hNid : (geoTransformAlong (geometricTemplate Z []) R).N = strictAlong R Z :=
    N_geoTransformAlong _ R
  rw [hNid] at hreg
  have hdim : AnalyticDimensionBasics.DimLE (n := n) (strictAlong R Z) 1 := fun x k hx =>
    (RegularPointDimension.eq_of_regularAtDim hx (hreg x hx.2.1)).le
  intro x hx
  obtain ⟨k, hk⟩ := hC.2 x hx
  have hCZ : C ⊆ strictAlong R Z := fun y hy => (hCbad hy).1
  have hlt := ThinDimensionDrop.lt_of_regularAtDim_of_thin
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hCZ
    (fun O hO hOC => hthin O hO (hOC.trans hCbad)) hdim hk
  have hk0 : k = 0 := by omega
  rw [hk0] at hk
  exact hk

/-- **Zero-dimensional centres**: every centre of the tower is regular of dimension `0` at each of its
points. -/
def PointCentres : {Q : CMfd.{u} n} → BlowupTower Y Q → Prop
  | _, .refl => True
  | _, .step R C _ _ => PointCentres R ∧ ∀ x ∈ C, RegularAtDim (n := n) C x 0

/-- **A curve problem's sharp towers have point centres.** -/
theorem pointCentres_of_curve_sharp (hn : 0 < n) {Z : Set Y} {F : List (Set Y)}
    (hZ : IsClosedSubmanifold n Z) (hF : IsSNCDivisor n F)
    (hZd : Z ⊆ closure (Z \ ⋃ H ∈ F, H)) (hZreg : ∀ x ∈ Z, RegularAtDim (n := n) Z x 1) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate Z []) R →
      IsGeoTestTower (geometricTemplate (univ : Set Y) F) R →
      CurrentSharpCentres Z F R → PointCentres R
  | _, .refl, _, _, _ => trivial
  | _, .step R C π hπ, h1, h2, hS => by
      obtain ⟨h10, hA1⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp h1
      obtain ⟨h20, -⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp h2
      obtain ⟨hS0, hCbad⟩ := hS
      exact ⟨pointCentres_of_curve_sharp hn hZ hF hZd hZreg R h10 h20 hS0,
        regularAtDim_zero_of_subset_sharpBad hn hZ hF hZd hZreg R h10 h20 hA1.1 hCbad⟩

end Curves

section Main
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **Point centres are protected.**  Along a tail `R` after an actual prefix `T` (both geometric tests
at `T·R`) whose centres are zero-dimensional, the protected-window certificate holds at every point of
every prepared support: the window and the protected configuration come from the held
`protected_slice_window` (the rows of `P` stay prepared stage by stage), and a zero-dimensional centre
has normal crossings with every simple normal crossings divisor. -/
theorem protectedTail_of_pointCentres
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (P : Finset (Fin E.length))
    (T : BlowupTower X Y) (hP : ∀ i ∈ P, ActualRowPrepared W E i T) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate W []) (T.append R) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) →
      PointCentres R → ProtectedTail W E P T R
  | _, .refl, _, _, _ => trivial
  | _, .step R C π hπ, hTR, hFR, hPt => by
      have hTR' : IsGeoTestTower (geometricTemplate W []) (.step (T.append R) C π hπ) := hTR
      have hFR' : IsGeoTestTower (geometricTemplate (univ : Set X) E)
        (.step (T.append R) C π hπ) := hFR
      obtain ⟨hT0, -⟩ := (isGeoTestTower_step_iff _ (T.append R) C π hπ).mp hTR'
      obtain ⟨hF0, -⟩ := (isGeoTestTower_step_iff _ (T.append R) C π hπ).mp hFR'
      have ih := protectedTail_of_pointCentres hn hW hE hdense P T hP R hT0 hF0 hPt.1
      have hPR := actual_rows_prepared_of_protected_tail hn hW hE hdense P T hP R hT0 hF0 ih
      refine ⟨ih, ?_⟩
      intro i hi x hx
      have hPi := hPR i hi
      have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i))
        (T.append R)).1
      change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).N =
        (geoTransformAlong (geometricTemplate W []) (T.append R)).N at hNi
      have hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus := by
        rw [hNi]
        exact hx.2
      obtain ⟨U, hxU, -, Haux, hSNC, hTr, hSlice, -⟩ :=
        HironakaActualProtectedOtherRowLocalStep.protected_slice_window hn hW hE hdense i (T.append R)
          hT0 hF0 hPi.1 hPi.2.1 hPi.2.2 hxi ⊤ (by simp)
      refine ⟨U, hxU, Haux, hSlice, hSNC, hTr, ?_⟩
      exact hasNormalCrossings_of_regularAtDim_zero hSNC fun z hz =>
        AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hPt.2 z.val hz)

/-- **The named statement of route (L) for `d = 1`** (`W` pure of dimension `2`): at every lower entry
the lower problem `(S_j, F_j)` is a curve problem; the unconditional curve cleanup
`exists_actual_sharp_cleanup_dim_one` of `(S_j, F_j)` (compact lower bad locus by the held
`actual_compact_sharp_bad_source`) is a certified lower cleanup: lower test from the two tests, final
normal crossings, final density (held dictionary), and protection because its centres are points. -/
theorem certifiedLowerCleanupsExist_one (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    CertifiedLowerCleanupsExist W E 1 := by
  intro Y T hT hFull hSharp hOrd hReg hDistinct P hP j hj
  obtain ⟨hL, hLreg, hLF, -, -⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd 1 hReg hDistinct j
  obtain ⟨-, hFj, hKj, -, -⟩ :=
    HironakaActualSharpBadFirstMaximumBlowup.actual_compact_sharp_bad_source
      hn hW hE hdense hK T hT hFull hSharp hOrd 1 hReg hDistinct j
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  rw [← hNj] at hL hLreg hLF hKj
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hOrd y hy j
  obtain ⟨Q, U, h1, h2, hS, -, -, -, hNC, -, -⟩ :=
    HironakaG34DriverBaseCases.exists_actual_sharp_cleanup_dim_one hn hL hFj hLF hLreg hKj
  obtain ⟨-, hDen⟩ := lower_dense_of_two_tests hn hL hFj hLF U h1 h2
  have hLT := HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests _ _ U h1 h2
  obtain ⟨_hZ, _hWhole, hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  obtain ⟨hTU, hFullU, -⟩ := hTails U hLT
  have hPt := pointCentres_of_curve_sharp hn hL hFj hLF hLreg U h1 h2 hS
  obtain ⟨hNC', hDen'⟩ := lower_nc_dense_of_two_template _ _ U hNC hDen
  exact ⟨Q, U, hLT, hS, hNC', hDen',
    protectedTail_of_pointCentres hn hW hE hdense P T hP U hTU hFullU hPt⟩

/-- **Surfaces, unconditional**: the sharp cleanup of every `(W, E)` with `W` pure of dimension `2`
(static hypotheses and compact original sharp bad locus only), by the terminating driver of route (L)
with the lower cleanups of `certifiedLowerCleanupsExist_one`. -/
theorem exists_actual_sharp_cleanup_dim_two
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x 2)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ :=
  exists_actual_sharp_cleanup_of_certified_lower_cleanups hn hW hE hdense 1 hRegW hK
    (certifiedLowerCleanupsExist_one hn hW hE hdense hK)

end Main

end
end Hironaka.HironakaG34SurfaceSharpCleanup
