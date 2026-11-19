import Hironaka.Resolution.HironakaOriginalNCMarkedStratumNaturality

/-!
# Prescribed-H canonical open restriction of the NEW native value

The original native domain, prescribed-H adaptation, actual original open
and GIVEN raw NEW-Psi canonical tower internally produce target canonicality.
A source whole maximum is restricted to an ENTIRE local maximum only when
its actual preimage is nonempty; an empty trace gives the genuine empty
canonical-centre alternative. No maximum attainment in the open is assumed.

The same actual restricted tower has native tests, ALL original localbranch
histories and the whole current prescribed-H/ordered-E adapted pair. If the
original tower already resolves, its actual restriction resolves as well.
All literal empty years and born empty boundary positions are retained.

Mathematics/API first:
work/hironaka-g9-marked-stratum-canonical-open-restriction-20261024/.
SOURCE ONLY; no Lean or kernel check, Blueprint credit, nonempty-centre
restriction claim, independent resolving-tower uniqueness, local driver,
H-free invariant installation, G3 scheduler or original G9 closure.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumCanonicalOpenRestriction

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionDriver
  HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCOldStratumStrictEquality
  HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCMarkedStratumCanonicalHistory
  HironakaOriginalNCMarkedStratumNaturality
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ} {X : CMfd.{u} n}

/-- H-aware raw canonicality of the actual restricted tower. The only
value comparison is the verified NEW open field on each ORIGINAL raw-CAN
prefix. A missing original maximum produces an actual empty centre. -/
theorem markedStratum_canonical_restrictOpen
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonical M (markedStratumHistoryValue M H) T →
        IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
          (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
            ((Subtype.val : U → X) ⁻¹' H)) (restrict U T)
  | _, .refl, _hCan => trivial
  | _, .step T C π hπ, hCan => by
      obtain ⟨hT, hC⟩ : IsCanonical M (markedStratumHistoryValue M H) T ∧
          (C = ∅ ∨ C = maxLocus (markedStratumHistoryValue M H T)
            (geoTransformAlong M T).cosupp) := hCan
      have hCanU := markedStratum_canonical_restrictOpen M hM h U T hT
      have hTest : IsGeoTestTower M T :=
        (markedStratum_canonical_history_joint_interpretation M hM h T hT).1
      show IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
          (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
            ((Subtype.val : U → X) ⁻¹' H)) (restrict U T) ∧
        (((Subtype.val : openPreimage T U → _) ⁻¹' C) = ∅ ∨
          ((Subtype.val : openPreimage T U → _) ⁻¹' C) =
            maxLocus (markedStratumHistoryValue
              (MarkedIdeal.pullback (Subtype.val : U → X) M)
              ((Subtype.val : U → X) ⁻¹' H) (restrict U T))
              (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M)
                (restrict U T)).cosupp)
      refine ⟨hCanU, ?_⟩
      rcases hC with rfl | rfl
      · exact Or.inl preimage_empty
      · by_cases hNe : ((Subtype.val : openPreimage T U → _) ⁻¹'
            maxLocus (markedStratumHistoryValue M H T)
              (geoTransformAlong M T).cosupp).Nonempty
        · right
          rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
            hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent U T hTest]
          exact (ResolutionInvariantSegments.maxLocus_preimage _
            (fun p hp => markedStratum_history_value_restrictOpen M hM h U T hT p hp)
            hNe).symm
        · exact Or.inl (not_nonempty_iff_eq_empty.mp hNe)

/-- A natural H-aware open producer on the SAME actual restricted tower.
Target raw CAN, native domain/testness, ALL original branch histories and
the entire current H/E adapted pair are internal outputs. An existing
original resolution transports without a target resolving certificate. -/
theorem markedStratum_canonical_restrictOpen_interpretation
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T) :
    let MU : MarkedIdeal n U := MarkedIdeal.pullback (Subtype.val : U → X) M
    let HU : Set U := (Subtype.val : U → X) ⁻¹' H
    let TU := restrict U T
    IsInvDomain n MU ∧ IsBoundaryAdaptedCarrier (n := n) HU MU.E ∧
      IsCanonical MU (markedStratumHistoryValue MU HU) TU ∧
      IsGeoTestTower MU TU ∧ IsOriginalBranchTestTower MU HU TU ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong TU HU) (geoTransformAlong MU TU).E ∧
      (IsGeoResolution M T → IsGeoResolution MU TU) := by
  dsimp only
  let MU : MarkedIdeal n U := MarkedIdeal.pullback (Subtype.val : U → X) M
  let HU : Set U := (Subtype.val : U → X) ⁻¹' H
  let TU := restrict U T
  have hMU : IsInvDomain n MU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hHU : IsBoundaryAdaptedCarrier (n := n) HU MU.E := boundaryAdapted_open U h
  have hCanU : IsCanonical MU (markedStratumHistoryValue MU HU) TU :=
    markedStratum_canonical_restrictOpen M hM h U T hCan
  obtain ⟨hTestU, hHistoryU, _hBirthsU, _hFrameU⟩ :=
    markedStratum_canonical_history_joint_interpretation
      (X := CMfd.of (n := n) U) MU hMU hHU TU hCanU
  have hPairU : IsBoundaryAdaptedCarrier (n := n)
      (strictAlong TU HU) (geoTransformAlong MU TU).E :=
    (current_old_strata_eq_strict (X := CMfd.of (n := n) U) MU hHU TU hTestU hHistoryU).1
  refine ⟨hMU, hHU, hCanU, hTestU, hHistoryU, hPairU, ?_⟩
  intro hRes
  exact isGeoResolution_restrict U hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hRes

end
end Hironaka.HironakaOriginalNCMarkedStratumCanonicalOpenRestriction
