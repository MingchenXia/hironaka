import Hironaka.Resolution.HironakaG34DriverEquivariance
import Hironaka.Resolution.HironakaG34SurfaceProtection
import Hironaka.Resolution.HironakaG34SurfaceSharpCleanup
import Hironaka.Resolution.HironakaG34DriverBaseCases
import Hironaka.Resolution.HironakaG34GammaCertifiedLift

/-!
# EQ_d: equivariant sharp cleanups; dimensions `≤ 3` unconditionally, all dimensions from the consumption (fourteenth brick)

Lane G34 (run 0080, round 10).  Blueprint: `hironaka-g34-resume-equivariant-sharp-cleanup.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §2(b) (the statement EQ_d), §2(c)(iv) (the induction), §3 (the
consumption).

`EquivariantSharpCleanupsExist n d` (EQ_d of the route note §2(b)): every sharp problem `(W, E)` (closed submanifold `W`
pure of dimension `d`, `E` simple normal crossings, `W` dense off `E`, compact original sharp bad locus) has a sharp
cleanup `U` (the conclusions of the route-(L) driver) which is EQUIVARIANT for `(W, E)`: for every biholomorphism
`φ : V ≅ V'` of opens preserving `W` and every member of `E`, `U|_V ≅ U|_{V'}` over `φ`.

The induction `EQ_d ⟹ EQ_{d+1}` runs the equivariant driver (`HironakaG34DriverEquivariance`) with, as lower cleanup of each
row, the EQ_d cleanup of the lower problem `(S_j, F_j)`; that cleanup is certified once it is a (Gamma-)protected tail.
`EquivariantLowerProtection W E d` names exactly this consumption step: at every lower entry, every lower tail with the two
zero-mark tests and lower sharp centres which is equivariant for the lower data is Gamma-protected (route note §3: rotations
at Gamma points, toric lift, torus lemma).  It is PROVED here for `d = 1` (point centres) and `d = 2` (surface lower
cleanups), without using the equivariance; for `d ≥ 3` it is the remaining named statement.

## Main results

* `EquivariantSharpCleanupsExist n d` (EQ_d); `EquivariantLowerProtection W E d` (the consumption, a named statement NOT
  assumed anywhere as an axiom); `IsEquivariantLowerSharpTail`;
* `equivariantLowerProtection_one`, `equivariantLowerProtection_two`: the consumption in lower dimension `1`, `2`;
* `equivariantCertifiedLowerCleanupsExist_zero`, `equivariantCertifiedLowerCleanupsExist_of_protection`;
* `equivariantSharpCleanupsExist_zero`, `equivariantSharpCleanupsExist_one`, `equivariantSharpCleanupsExist_succ`;
* **`equivariantSharpCleanupsExist_le_three`**: EQ_d for every `d ≤ 3`, unconditionally;
* **`equivariantSharpCleanupsExist_of_protection`**: EQ_d for every `d`, from the consumption for `d ≥ 3`.

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34EquivariantSharpCleanup
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold NormalCrossings
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail RestrictEmptyTower
  HomogenizedGlueingTower HironakaG4RecordedTowerResidualCompatibility
  HironakaG34MaskFoldEquivariance HironakaG34LowerCleanupLift HironakaG34GammaCertifiedLift
  HironakaG34DriverEquivariance NormalCrossingsComparison

/-! ### The statements -/

section Defs

/-- **EQ_d (equivariant sharp cleanups in dimension `d`)**: every sharp problem `(W, E)` with `W` a closed submanifold pure
of dimension `d`, `E` simple normal crossings, `W` dense off `E` and compact original sharp bad locus has a sharp cleanup
(the conclusions of the route-(L) driver) which is equivariant for `(W, E)`. -/
def EquivariantSharpCleanupsExist (n d : ℕ) : Prop :=
  ∀ (X : CMfd.{u} n) (W : Set X) (E : List (Set X)), IsClosedSubmanifold n W → IsSNCDivisor n E →
    W ⊆ closure (W \ ⋃ H ∈ E, H) → (∀ x ∈ W, RegularAtDim (n := n) W x d) →
    IsCompact (originalSharpBadLocus (n := n) W E) →
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      IsEquivariant W E U ∧
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **An equivariant lower sharp tail of row `j` at `T`**: a tower of the lower problem `(Z_j, F_j)` (support of the
chronological residual of row `j`, current boundary without the strict transform of `E_j`) with its two zero-mark tests,
lower sharp centres, equivariant for `(Z_j, F_j)`. -/
def IsEquivariantLowerSharpTail (W : Set X) (E : List (Set X)) (j : Fin E.length) (T : BlowupTower X Y)
    {Q : CMfd.{u} n} (R : BlowupTower Y Q) : Prop :=
  let Z := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
    (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
  let F := (E.map (strictAlong T)).eraseIdx j.val ++ (geoTransformAlong (geometricTemplate W []) T).E
  IsGeoTestTower (geometricTemplate Z []) R ∧ IsGeoTestTower (geometricTemplate (univ : Set Y) F) R ∧
    CurrentSharpCentres Z F R ∧ IsEquivariant Z F R

/-- **The consumption of EQ (route note §3), a named statement NOT assumed anywhere as an axiom**: at every lower entry of
the sharp driver for `(W, E)` (`W` pure of dimension `d + 1`), for every set `P` of prepared rows and every `j ∉ P`, every
equivariant lower sharp tail of row `j` is Gamma-protected for `P` (its centres carry the protected-window certificate at
the Gamma points of the prepared supports).  Proved below for `d = 1, 2`. -/
def EquivariantLowerProtection (W : Set X) (E : List (Set X)) (d : ℕ) : Prop :=
  ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    IsGeoTestTower (geometricTemplate W []) T →
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
    CurrentSharpCentres W E T →
    (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ a : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1) →
    (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1)) →
    chronologicalDistinctDefect W E T = ∅ →
    ∀ (P : Finset (Fin E.length)), (∀ i ∈ P, ActualRowPrepared W E i T) →
    ∀ j : Fin E.length, j ∉ P →
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q), IsEquivariantLowerSharpTail W E j T R →
      GammaProtectedTail W E P T R

/-- A protected tail is Gamma-protected. -/
theorem gammaProtectedTail_of_protectedTail {W : Set X} {E : List (Set X)} {P : Finset (Fin E.length)}
    {T : BlowupTower X Y} : ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      ProtectedTail W E P T R → GammaProtectedTail W E P T R
  | _, .refl, _ => trivial
  | _, .step R _ _ _, h => ⟨gammaProtectedTail_of_protectedTail R h.1, fun i hi x hx _ => h.2 i hi x hx⟩

end Defs

/-! ### The consumption in lower dimension `1` and `2` -/

section LowDim

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **Lower dimension `1`**: every lower sharp tail of a curve problem has point centres, hence is protected
(`W` pure of dimension `2`; the equivariance is not used). -/
theorem equivariantLowerProtection_one (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    EquivariantLowerProtection W E 1 := by
  intro Y T hT hFull _hSharp hOrd hReg hDistinct P hP j _hj Q R hR
  obtain ⟨h1, h2, hS, -⟩ := hR
  obtain ⟨hL, hLreg, hLF, -, -⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd 1 hReg hDistinct j
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n ((E.map (strictAlong T)).eraseIdx j.val ++
      (geoTransformAlong (geometricTemplate W []) T).E) :=
    isSNCDivisor_of_sublist hRec.2.1
      ((List.eraseIdx_sublist (E.map (strictAlong T)) j.val).append (List.Sublist.refl _))
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  rw [← hNj] at hL hLreg hLF
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hOrd y hy j
  have hLT := HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests _ _ R h1 h2
  obtain ⟨_hZ, _hWhole, hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  obtain ⟨hTU, hFullU, -⟩ := hTails R hLT
  have hPt := HironakaG34SurfaceSharpCleanup.pointCentres_of_curve_sharp hn hL hFj hLF hLreg R h1 h2 hS
  exact gammaProtectedTail_of_protectedTail R
    (HironakaG34SurfaceSharpCleanup.protectedTail_of_pointCentres hn hW hE hdense P T hP R hTU hFullU hPt)

/-- **Lower dimension `2`**: every lower sharp tail of a surface problem is protected (`W` pure of dimension `3`; the
equivariance is not used). -/
theorem equivariantLowerProtection_two (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    EquivariantLowerProtection W E 2 := by
  intro Y T hT hFull _hSharp hOrd hReg hDistinct P hP j hj Q R hR
  obtain ⟨h1, h2, hS, -⟩ := hR
  obtain ⟨hL, hLreg, hLF, -, -⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd 2 hReg hDistinct j
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n ((E.map (strictAlong T)).eraseIdx j.val ++
      (geoTransformAlong (geometricTemplate W []) T).E) :=
    isSNCDivisor_of_sublist hRec.2.1
      ((List.eraseIdx_sublist (E.map (strictAlong T)) j.val).append (List.Sublist.refl _))
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  rw [← hNj] at hL hLreg hLF
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hOrd y hy j
  exact gammaProtectedTail_of_protectedTail R
    (HironakaG34SurfaceProtection.protectedTail_of_surface_lower hn hW hE hdense j T hT hFull hReg hOrdj P hP hj
      hL hFj hLF hLreg R h1 h2 hS)

end LowDim

/-! ### Certified equivariant lower cleanups -/

section Certified

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **Lower dimension `0`**: the empty tower is an equivariant certified lower cleanup (`W` pure of dimension `1`). -/
theorem equivariantCertifiedLowerCleanupsExist_zero (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    EquivariantCertifiedLowerCleanupsExist W E 0 := by
  intro Y T hT hFull _hSharp hOrd hReg hDistinct P _hP j _hj
  obtain ⟨hL, hLreg, hLF, -, -⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd 0 hReg hDistinct j
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n ((E.map (strictAlong T)).eraseIdx j.val ++
      (geoTransformAlong (geometricTemplate W []) T).E) :=
    isSNCDivisor_of_sublist hRec.2.1
      ((List.eraseIdx_sublist (E.map (strictAlong T)) j.val).append (List.Sublist.refl _))
  have hBad := HironakaG4GeneralSharpBadLocus.originalSharpBadLocus_eq_empty_of_regular_zero
    hL hFj hLF hLreg
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  refine ⟨Y, .refl, ⟨trivial, trivial, ?_, ?_, trivial⟩, isEquivariant_refl _ _⟩
  · change HasNormalCrossings n
      ((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
      ((E.map (strictAlong T)).eraseIdx j.val ++ (geoTransformAlong (geometricTemplate W []) T).E)
    rw [hNj]
    intro x hx
    by_contra hnot
    have hmem : x ∈ originalSharpBadLocus (n := n)
        ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
        ((E.map (strictAlong T)).eraseIdx j.val ++
          (geoTransformAlong (geometricTemplate W []) T).E) := ⟨hx, hnot⟩
    rw [hBad] at hmem
    exact hmem
  · show ((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) ⊆
      closure (((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) \
          (⋃ D ∈ (E.map (strictAlong T)).eraseIdx j.val ++
            (geoTransformAlong (geometricTemplate W []) T).E, D))
    rw [hNj]
    exact hLF

/-- Resolve the lower problem of one actual original row. Compactness is
required for the selected lower bad locus. The same tail supplies the
certified cleanup, equivariance and its lower footprint. -/
theorem exists_equivariant_certified_lower_cleanup_of_compact_lower_bad
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hEQ : EquivariantSharpCleanupsExist.{u} n d) (hProt : EquivariantLowerProtection W E d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ a : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length) (hj : j ∉ P) :
    let J := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
    let L := J.N ∩ J.ideal.zeroLocus
    let F := (E.map (strictAlong T)).eraseIdx j.val ++ (geoTransformAlong (geometricTemplate W []) T).E
    IsCompact (originalSharpBadLocus (n := n) L F) →
    ∃ (Q : CMfd.{u} n) (R : BlowupTower Y Q),
      CertifiedLowerCleanup W E P j T R ∧ IsEquivariant L F R ∧
      CentresOver (originalSharpBadLocus (n := n) L F) R := by
  dsimp only
  intro hKj
  obtain ⟨hL, hLreg, hLF, -, -⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd d hReg hDistinct j
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n ((E.map (strictAlong T)).eraseIdx j.val ++
      (geoTransformAlong (geometricTemplate W []) T).E) :=
    isSNCDivisor_of_sublist hRec.2.1
      ((List.eraseIdx_sublist (E.map (strictAlong T)) j.val).append (List.Sublist.refl _))
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  rw [← hNj] at hL hLreg hLF
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hOrd y hy j
  obtain ⟨Q, U, hEqU, h1, h2, hS, hOver, -, -, hNC, -, -⟩ := hEQ _ _ _ hL hFj hLF hLreg hKj
  obtain ⟨-, hDen⟩ := HironakaG34SurfaceSharpCleanup.lower_dense_of_two_tests hn hL hFj hLF U h1 h2
  have hLT := HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests _ _ U h1 h2
  obtain ⟨hNC', hDen'⟩ := HironakaG34SurfaceSharpCleanup.lower_nc_dense_of_two_template _ _ U hNC hDen
  have hG := hProt T hT hFull hSharp hOrd hReg hDistinct P hP j hj U ⟨h1, h2, hS, hEqU⟩
  exact ⟨Q, U, ⟨hLT, hS, hNC', hDen',
    protectedTail_of_gammaProtectedTail hn hW hE hdense j T hT hFull hOrdj P hP hj U hLT hS hG⟩, hEqU, hOver⟩

/-- **EQ_d for the lower problems and the consumption give equivariant certified lower cleanups**: the EQ_d cleanup of the
lower problem `(S_j, F_j)` (closed, pure of dimension `d`, dense off `F_j`, `F_j` simple normal crossings, compact lower
sharp bad locus: held `sharp_bad_native_domain`, `actual_compact_sharp_bad_source`) is a lower test tail with final normal
crossings and density (held two-template bridges), Gamma-protected by the consumption, hence protected (r5). -/
theorem equivariantCertifiedLowerCleanupsExist_of_protection (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) (d : ℕ)
    (hEQ : EquivariantSharpCleanupsExist.{u} n d) (hProt : EquivariantLowerProtection W E d) :
    EquivariantCertifiedLowerCleanupsExist W E d := by
  intro Y T hT hFull hSharp hOrd hReg hDistinct P hP j hj
  obtain ⟨-, -, hKj, -, -⟩ :=
    HironakaActualSharpBadFirstMaximumBlowup.actual_compact_sharp_bad_source
      hn hW hE hdense hK T hT hFull hSharp hOrd d hReg hDistinct j
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  rw [← hNj] at hKj
  obtain ⟨Q, R, hR, hEqR, _⟩ :=
    exists_equivariant_certified_lower_cleanup_of_compact_lower_bad hn hW hE hdense d
      hEQ hProt T hT hFull hSharp hOrd hReg hDistinct P hP j hj hKj
  exact ⟨Q, R, hR, hEqR⟩

end Certified

/-! ### EQ_d -/

section EQ

variable {n : ℕ}

/-- **EQ_0**: in dimension `0` the original sharp bad locus is empty and the empty tower is an equivariant sharp
cleanup. -/
theorem equivariantSharpCleanupsExist_zero : EquivariantSharpCleanupsExist.{u} n 0 := by
  intro X W E hW hE hdense hRegW _hK
  have hBad := HironakaG4GeneralSharpBadLocus.originalSharpBadLocus_eq_empty_of_regular_zero
    hW hE hdense hRegW
  refine ⟨X, .refl, isEquivariant_refl W E, trivial, trivial, trivial, trivial, hW, hE, ?_, ?_, ?_⟩
  · change HasNormalCrossings n W E
    intro x hx
    by_contra hnot
    have hmem : x ∈ originalSharpBadLocus (n := n) W E := ⟨hx, hnot⟩
    rw [hBad] at hmem
    exact hmem
  · change IsProperMap (id : X → X)
    exact isProperMap_id
  · change IsIsomorphismOver n (id : X → X) (originalSharpBadLocus (n := n) W E)ᶜ
    refine ⟨?_, ?_⟩
    · simpa using (bijOn_id (originalSharpBadLocus (n := n) W E)ᶜ)
    · rw [exceptionalLocus_id]
      exact disjoint_empty _

/-- **EQ_1**: the equivariant driver with empty lower cleanups. -/
theorem equivariantSharpCleanupsExist_one (hn : 0 < n) : EquivariantSharpCleanupsExist.{u} n 1 := by
  intro X W E hW hE hdense hRegW hK
  exact exists_actual_sharp_cleanup_of_equivariant_certified_lower_cleanups hn hW hE hdense 0 hRegW hK
    (equivariantCertifiedLowerCleanupsExist_zero hn hW hE hdense)

/-- **The inductive step `EQ_d ⟹ EQ_{d+1}`**, given the consumption in lower dimension `d`. -/
theorem equivariantSharpCleanupsExist_succ (hn : 0 < n) (d : ℕ) (hEQ : EquivariantSharpCleanupsExist.{u} n d)
    (hProt : ∀ {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}, IsClosedSubmanifold n W → IsSNCDivisor n E →
      W ⊆ closure (W \ ⋃ H ∈ E, H) → EquivariantLowerProtection W E d) :
    EquivariantSharpCleanupsExist.{u} n (d + 1) := by
  intro X W E hW hE hdense hRegW hK
  exact exists_actual_sharp_cleanup_of_equivariant_certified_lower_cleanups hn hW hE hdense d hRegW hK
    (equivariantCertifiedLowerCleanupsExist_of_protection hn hW hE hdense hK d hEQ (hProt hW hE hdense))

/-- **EQ_d for every `d ≤ 3`, unconditionally.** -/
theorem equivariantSharpCleanupsExist_le_three (hn : 0 < n) (d : ℕ) (hd : d ≤ 3) :
    EquivariantSharpCleanupsExist.{u} n d := by
  have h1 : EquivariantSharpCleanupsExist.{u} n 1 := equivariantSharpCleanupsExist_one hn
  have h2 : EquivariantSharpCleanupsExist.{u} n 2 := equivariantSharpCleanupsExist_succ hn 1 h1
    (fun hW hE hdense => equivariantLowerProtection_one hn hW hE hdense)
  have h3 : EquivariantSharpCleanupsExist.{u} n 3 := equivariantSharpCleanupsExist_succ hn 2 h2
    (fun hW hE hdense => equivariantLowerProtection_two hn hW hE hdense)
  interval_cases d
  · exact equivariantSharpCleanupsExist_zero
  · exact h1
  · exact h2
  · exact h3

/-- **EQ_d for every `d`, from the consumption in lower dimension `≥ 3`** (induction on `d`; dimensions `≤ 3`
unconditional). -/
theorem equivariantSharpCleanupsExist_of_protection (hn : 0 < n)
    (hProt : ∀ d : ℕ, 3 ≤ d → ∀ {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}, IsClosedSubmanifold n W →
      IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) → EquivariantLowerProtection W E d) :
    ∀ d : ℕ, EquivariantSharpCleanupsExist.{u} n d := by
  intro d
  induction d with
  | zero => exact equivariantSharpCleanupsExist_zero
  | succ d ih =>
    by_cases hd : d + 1 ≤ 3
    · exact equivariantSharpCleanupsExist_le_three hn (d + 1) hd
    · exact equivariantSharpCleanupsExist_succ hn d ih (hProt d (by omega))

end EQ

end
end Hironaka.HironakaG34EquivariantSharpCleanup
