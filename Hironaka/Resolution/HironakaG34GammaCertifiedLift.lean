import Hironaka.Resolution.HironakaG34LowerCleanupLift
import Hironaka.Resolution.HironakaG34LowerBadMonomialSupport

/-! # Protection is needed only at Gamma points (G4K1B, T-L route (L), sharpened residual)

Lane G34 (run 0080, round 5).  Blueprint: `hironaka-g34-resume-gamma-certified-lift.tex`.

Along a lower test tail of row `j` with LOWER SHARP centres, every centre lies in the current lower bad
locus `B_j`; near a point `x` of a prepared support `S_i` this locus is the zero set of the monomial
factor `D_i` of row `i` on `S_j` (r2 `actual_prepared_row_lower_bad_eq_monomial_support`).  Hence a
centre meets `S_i` only at GAMMA points (`D_i` not a unit), and the protected-window certificate is
needed only there.

* `GammaProtectedTail`: the stagewise certificate required only at Gamma points.
* `protectedTail_of_gammaProtectedTail`: for a lower test tail with lower sharp centres, the Gamma
  certificate implies the full certificate (`ProtectedTail`), stage by stage, the prepared rows being
  carried along (`actual_rows_prepared_of_protected_tail`).
* `GammaCertifiedLowerCleanupsExist`, `certifiedLowerCleanupsExist_of_gamma`,
  `exists_actual_sharp_cleanup_of_gamma_certified_lower_cleanups`: the terminating driver of
  `HironakaG34LowerCleanupLift` from the sharpened residual (protection near Gamma points only). -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34GammaCertifiedLift
noncomputable section

section CopiedTwo
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings MemberInterLocusAlong
  HironakaG4OriginalSelectedLowerBoundaryHistory HironakaG4ResidualInductionInputs
  HironakaG4RecordedTowerResidualCompatibility HironakaG4PreparedCentreCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaSharpActualCurveWholeBoundaryTransversality
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X Y Q : CMfd.{u} n}

/-- Private verbatim copy from `HironakaG4OriginalSelectedLowerBadHistory` (private there). -/
private theorem actual_remaining_boundary_dictionary (W : Set X) (E : List (Set X))
    (i : ℕ) (T : BlowupTower X Y) (S : Set Y) (R : BlowupTower Y Q) :
    let B := geoTransformAlong (geometricTemplate W []) T
    (geoTransformAlong (geometricTemplate S ((E.map (strictAlong T)).eraseIdx i ++ B.E)) R).E=
      (E.map (strictAlong (T.append R))).eraseIdx i ++
        (geoTransformAlong (geometricTemplate W []) (T.append R)).E := by
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx i ++ B.E
  let K := geometricTemplate (univ : Set Y) []
  have hOld : (E.map (strictAlong T)).map (strictAlong R)=E.map (strictAlong (T.append R)) := by
    rw [List.map_map]
    exact congrArg (fun f : Set X → Set Q => E.map f)
      (funext fun H => (strictAlong_append T H R).symm)
  have hBorn : (geoTransformAlong (geometricTemplate W []) (T.append R)).E=
      B.E.map (strictAlong R) ++ (geoTransformAlong K R).E := by
    rw [geoTransformAlong_append]
    exact boundary_geoTransformAlong_decomposition B K rfl R
  calc
    (geoTransformAlong (geometricTemplate S F) R).E
        = F.map (strictAlong R) ++ (geoTransformAlong K R).E :=
      boundary_geoTransformAlong_decomposition (geometricTemplate S F) K rfl R
    _ = ((E.map (strictAlong T)).eraseIdx i).map (strictAlong R) ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [List.map_append,List.append_assoc]
    _ = (E.map (strictAlong (T.append R))).eraseIdx i ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [←List.eraseIdx_map,hOld]
    _ = _ := by rw [←hBorn]

end CopiedTwo

section Main
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold NormalCrossings
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail RestrictEmptyTower
  HomogenizedGlueingTower HironakaSharpActualChronologicalStrictStep
  HironakaG4RecordedTowerResidualCompatibility DivisorExponentAlong NormalCrossingsComparison
  MonomialPartAlong RestrictedIdealExtension HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **A Gamma-protected tail** after `T` for the rows `P`: at every stage `T·R'` of `R`, the next
centre carries the protected-window certificate at every point `x` of every prepared support `S_i`
(`i ∈ P`) at which the monomial factor `D_i` of row `i` is NOT a unit (a Gamma point). -/
def GammaProtectedTail (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length))
    (T : BlowupTower X Y) : {Q : CMfd.{u} n} → BlowupTower Y Q → Prop
  | _, .refl => True
  | _, .step R C _ _ => GammaProtectedTail W E P T R ∧
      ∀ i ∈ P, ∀ x ∈ C ∩ ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus),
        ¬ (monomialPartAlong n (geoTransformAlong (geometricTemplate W []) (T.append R)).N
            (restrictOn n (geoTransformAlong (geometricTemplate W []) (T.append R)).N
              (vanishingIdeal (n := n) (strictAlong (T.append R) (E.get i))))
            (geoTransformAlong (geometricTemplate W []) (T.append R)).E).mem x 1 →
        ProtectedWindowAt (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus)
          ((E.map (strictAlong (T.append R))).eraseIdx i.val ++
            (geoTransformAlong (geometricTemplate W []) (T.append R)).E) C x

/-- **Protection is needed only at Gamma points.**  Along a lower test tail of row `j` with lower sharp
centres, starting at an actual prefix where the rows of `P ∌ j` are prepared, the Gamma certificate
implies the full certificate. -/
theorem protectedTail_of_gammaProtectedTail
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (j : Fin E.length)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T) (hj : j ∉ P) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
    let Z := A.N ∩ A.ideal.zeroLocus
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q), IsGeoTestTower (geometricTemplate Z F) R →
      CurrentSharpCentres Z F R → GammaProtectedTail W E P T R → ProtectedTail W E P T R := by
  intro A B F Z
  obtain ⟨_hZ, _hWhole, hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  intro Q R
  induction R with
  | refl => intro _ _ _; trivial
  | @step Q₀ Q₁ R C π hπ ih =>
    intro hR hLS hG
    obtain ⟨hR0, hAdm⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp hR
    obtain ⟨hLS0, hCbad⟩ := hLS
    have hProt0 : ProtectedTail W E P T R := ih hR0 hLS0 hG.1
    refine ⟨hProt0, ?_⟩
    obtain ⟨hTR, hFullR, _hNR, hZR, hSub, hChronN, hChronI⟩ := hTails R hR0
    have hPR := actual_rows_prepared_of_protected_tail hn hW hE hdense P T hP R hTR hFullR hProt0
    -- the support of row `j` at `T·R` is the strict lower carrier
    have hGeoN : (geoTransformAlong (geometricTemplate W []) (T.append R)).N = strictAlong R A.N :=
      (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j))
        (T.append R)).1.symm.trans hChronN
    have hSupp : (geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus =
        strictAlong R Z := by
      rw [hGeoN, hChronI, BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hZR.1]
      exact inter_eq_right.mpr hSub
    -- the lower bad locus at `R` is the upper `B_j` at `T·R`
    have hLowE : (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E =
        (E.map (strictAlong (T.append R))).eraseIdx j.val ++
          (geoTransformAlong (geometricTemplate W []) (T.append R)).E := by
      rw [← actual_remaining_boundary_dictionary W E j.val T Z R,
        HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
          (geometricTemplate Z F) (geometricTemplate (univ : Set Y) []) rfl R,
        HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
          (geometricTemplate (univ : Set Y) F) (geometricTemplate (univ : Set Y) []) rfl R]
      rfl
    intro i hi x hx
    by_cases hDi : (monomialPartAlong n (geoTransformAlong (geometricTemplate W []) (T.append R)).N
        (restrictOn n (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (vanishingIdeal (n := n) (strictAlong (T.append R) (E.get i))))
        (geoTransformAlong (geometricTemplate W []) (T.append R)).E).mem x 1
    · exfalso
      have hne : j ≠ i := fun h => hj (h ▸ hi)
      have hxBad : x ∈ originalSharpBadLocus (n := n)
          ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus)
          ((E.map (strictAlong (T.append R))).eraseIdx j.val ++
            (geoTransformAlong (geometricTemplate W []) (T.append R)).E) := by
        rw [hSupp, ← hLowE]
        exact hCbad hx.1
      have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i))
        (T.append R)).1
      change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).N =
        (geoTransformAlong (geometricTemplate W []) (T.append R)).N at hNi
      have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j))
        (T.append R)).1
      change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).N =
        (geoTransformAlong (geometricTemplate W []) (T.append R)).N at hNj
      have hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus := by
        rw [hNi]
        exact hx.2
      have hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus := by
        rw [hNj]
        exact hxBad.1
      obtain ⟨U, hxU, hU⟩ :=
        HironakaG34LowerBadMonomialSupport.actual_prepared_row_lower_bad_eq_monomial_support hn hW hE
          hdense i (T.append R) hTR hFullR (hPR i hi).1 (hPR i hi).2.1 (hPR i hi).2.2 j hne hxi hxj
      exact ((hU x hxU).mp hxBad).2 hDi
    · exact hG.2 i hi x hx hDi

/-- **A Gamma-certified lower cleanup** of row `j` at `T` for `P`: as `CertifiedLowerCleanup`, with the
protection certificate required only at Gamma points. -/
def GammaCertifiedLowerCleanup (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length))
    (j : Fin E.length) (T : BlowupTower X Y) {Q : CMfd.{u} n} (R : BlowupTower Y Q) : Prop :=
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
  let Z := A.N ∩ A.ideal.zeroLocus
  let L := geoTransformAlong (geometricTemplate Z F) R
  IsGeoTestTower (geometricTemplate Z F) R ∧ CurrentSharpCentres Z F R ∧
    HasNormalCrossings n L.N L.E ∧ L.N ⊆ closure (L.N \ ⋃ D ∈ L.E, D) ∧
    GammaProtectedTail W E P T R

/-- **The sharpened residual of T-L under route (L)** (a named statement, not assumed anywhere as an
axiom): at every lower entry, for every prepared `P ∌ j`, the lower problem of row `j` admits a lower
cleanup whose centres are protected at the Gamma points of the prepared rows. -/
def GammaCertifiedLowerCleanupsExist (W : Set X) (E : List (Set X)) (d : ℕ) : Prop :=
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
    ∃ (Q : CMfd.{u} n) (R : BlowupTower Y Q), GammaCertifiedLowerCleanup W E P j T R

/-- The Gamma-certified residual implies the certified one. -/
theorem certifiedLowerCleanupsExist_of_gamma (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (h : GammaCertifiedLowerCleanupsExist W E d) : CertifiedLowerCleanupsExist W E d := by
  intro Y T hT hFull hSharp hOrd hReg hDistinct P hP j hj
  obtain ⟨Q, R, hLT, hLS, hNC, hDen, hG⟩ := h T hT hFull hSharp hOrd hReg hDistinct P hP j hj
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hOrd y hy j
  exact ⟨Q, R, hLT, hLS, hNC, hDen,
    protectedTail_of_gammaProtectedTail hn hW hE hdense j T hT hFull hOrdj P hP hj R hLT hLS hG⟩

/-- **The terminating sharp driver from the Gamma-certified residual** (route (L)). -/
theorem exists_actual_sharp_cleanup_of_gamma_certified_lower_cleanups
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : GammaCertifiedLowerCleanupsExist W E d) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ :=
  exists_actual_sharp_cleanup_of_certified_lower_cleanups hn hW hE hdense d hRegW hK
    (certifiedLowerCleanupsExist_of_gamma hn hW hE hdense d hIH)

end Main

end
end Hironaka.HironakaG34GammaCertifiedLift
