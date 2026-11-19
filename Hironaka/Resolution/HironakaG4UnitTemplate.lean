import Hironaka.Resolution.HironakaG4PreparedUnitChart
import Hironaka.Resolution.HironakaG4UnitSliceIdentity
import Hironaka.Resolution.HironakaG4OptionalChartRecognition
import Hironaka.Resolution.HironakaG4WellFormedSubopen

/-! Build the actual-member enlarged record in the unit branch. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4UnitTemplate
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates GiraudAlong DivisorExponentAlong MonomialPartAlong
  NonmonomialTransformAlong RestrictedIdealExtension RelativePrincipalizationSpan
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupRestrictOpen
  HironakaSharpActualFiniteChronologicalHistory IdealWeightPowers GermIdealPullbackCalculus
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks
  HironakaG4PreparedUnitChart HironakaG4UnitSliceIdentity HironakaG4OptionalChartRecognition
  HironakaG4WellFormedSubopen

variable {n : ℕ} {X : CMfd.{u} n}

/-- The unit branch supplies a locally well-formed zero-marked record whose
boundary is the actual old member followed by the remaining boundary, and
whose selected member cuts out the original protected slice. -/
theorem exists_unit_member_template (hn : 0 < n)
    {N Haux H : Set X} {F B L : List (Set X)} {x : X}
    (hNclosed : IsClosedSubmanifold n N)
    (hEF : IsSNCDivisor n (Haux :: F)) (hTF : IsTransverse n N (Haux :: F))
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxN : x ∈ N) (hxHaux : x ∈ Haux)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnz : IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) x)
    (hunit : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1)
    (hJZ : ∀ g, (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x g ↔
      (vanishingIdeal (n := n) (N ∩ Haux)).mem x g) :
    ∃ U : Opens X, x ∈ U ∧
      (MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate N (H :: F))).IsWellFormed ∧
      (Subtype.val : U → X) ⁻¹' (N ∩ Haux) = (Subtype.val : U → X) ⁻¹' (N ∩ H) := by
  obtain ⟨S,m,t,Φ,hm,hm0,htS,hsrc,h0,hN,hF,hH⟩ :=
    exists_prepared_unit_chart hn hEF hTF hL hHL hxN hxHaux hI hnz hunit hJZ
  have hclosed : ∀ K ∈ H :: F, IsClosed K := by
    intro K hK
    rcases List.mem_cons.mp hK with hK | hK
    · subst K
      exact hL.1 H hHL
    · exact hEF.1 K (List.mem_cons_of_mem _ hK)
  have hE : ∀ i y, y ∈ flatDomain Φ → (y ∈ (H :: F).get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro y hy
      have hh := hH y hy
      change y ∈ H ↔ flatMap Φ y ∈ optionalCoordLocus ((m ⟨0, by simp⟩).map (fun k => {k}))
      rw [hm0]
      simpa [hm0,optionalCoordLocus,coordSubspace] using hh
    · intro j y hy
      exact hF j y hy
  obtain ⟨V,hxV,hSNC,hTr⟩ := exists_snc_transverse_of_optional_chart hclosed Φ S m hN hE hm
  let D : MarkedIdeal n X := geometricTemplate N (H :: F)
  have hD : (MarkedIdeal.pullback (Subtype.val : V → X) D).IsWellFormed := by
    refine ⟨isClosedSubmanifold_preimage_val hNclosed V,
      isCoherent_pullback contMDiff_subtype_val (isCoherent_unitIdeal (n := n) (M := X)), ?_, ?_⟩
    · exact hSNC
    · exact hTr
  have hev := eventually_unit_slice_identity hn hEF hTF hL hHL hxN hxHaux hI hnz hunit hJZ
  obtain ⟨O,hOsub,hOopen,hxO⟩ := mem_nhds_iff.mp hev
  let U : Opens X := ⟨O ∩ V, hOopen.inter V.isOpen⟩
  have hUV : U ≤ V := fun _ hy => hy.2
  refine ⟨U,⟨hxO,hxV⟩,?_,?_⟩
  · exact wellFormed_pullback_val_of_subopen D hNclosed (isCoherent_unitIdeal (n := n) (M := X)) V U hUV hD
  · ext y
    exact hOsub y.property.1

end
end Hironaka.HironakaG4UnitTemplate
