import Hironaka.Analytic.Unibranch.HironakaG1DistinctNativeTerminalNormalization
import Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseComparison

/-! Full native endpoint from ordinary distinct RAW native records and
actual whole terminal histories. Blueprint FIRST:
hironaka-g1-distinct-native-terminal-comparison.tex.
Whole-power HSTowerState is derived; powered NativeHSState is not assumed.
-/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.HironakaG1DistinctNativeTerminalComparison
noncomputable section
open Hironaka Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11StrictTransformTowers HironakaG11PresReduction HironakaG11PresClassTransport
  HironakaG11PresLineState HironakaG11PresTowerState HironakaG11PresWindows
  HironakaG11InvCommonMark HironakaG1DistinctNativeTerminalNormalization
  HironakaActualPowerBoundaryExponents BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism CanonicalCentres
  HomogenizedGlueingTower HironakaActualAnalyticSubspace
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {X : SourceReducedComplexSpace} {n : ℕ} {ι : Type*}
  (w : ι → DimEmbedding X n) (raw : ∀i,MarkedIdeal n (Amb w i))
  (H : ℕ → ℕ) (hrec : ∀i,IsNativeWindowRecord (w i) (raw i) H)
  (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
  (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
  (hadm : mapAdm w i j U U' Φ) (e f : ℕ) (he : 1≤e) (hf : 1≤f)

def targetCarrier : Set (CMfd.of (n := n) U) :=
  (Subtype.val : U → (w i).ambient) ⁻¹' (w i).carrier

def sourceCarrier : Set (CMfd.of (n := n) U') :=
  (Subtype.val : U' → (w j).ambient) ⁻¹' (w j).carrier

local notation "P" => windowPower w raw i U e
local notation "B" => windowPower w raw j U' f
local notation "A" => overlapPower w raw i j U U' Φ e
local notation "W" => targetCarrier w i U

include hrec in
theorem target_carrier_analytic : IsComplexAnalyticSubset (n := n) W :=
  ((hrec i).2.2.restrict U).2.1

include hadm in
theorem source_carrier_eq : Φ ⁻¹' W=sourceCarrier w j U' := mapAdm_carrier hadm

include hrec he in
theorem target_power_domain : IsInvDomain n P :=
  InvDomainTowerAlong.isInvDomain_pullback_val U (powerMarked_isInvDomain (raw i) (hrec i).1 he)

include hrec he in
/-- Genuine RAW restriction, then weak-equivalence transport of its
whole power. This is a tower state, not a new native compression state. -/
theorem target_power_hsTowerState : HSTowerState P W H := by
  let R : MarkedIdeal n (CMfd.of (n := n) U) :=
    MarkedIdeal.pullback (Subtype.val : U → (w i).ambient) (raw i)
  have hR : IsInvDomain n R := InvDomainTowerAlong.isInvDomain_pullback_val U (hrec i).1
  have hsR : NativeHSState R W H := (hrec i).2.2.restrict U
  have hpow : P=powerMarked R e := HironakaG11PresClassTransport.pullback_powerMarked contMDiff_subtype_val
    (raw i) (hrec i).1.isWellFormed.isCoherent e
  have hsraw : HSTowerState R W H := fun {Z} V hV=>hsR.hsTowerState V hV
  have hw : MarkedIdealEquivalence.MarkedIdeal.WEquiv R (powerMarked R e) :=
    HironakaG11InvCommonMark.wEquiv_powerMarked R hR he
  have hspow : HSTowerState (powerMarked R e) W H := by
    intro Z V hV
    exact HSTowerState.of_wEquiv hw hsraw V hV
  rw [hpow]
  exact fun {Z} V hV=>hspow V hV

include hrec he in
theorem common_power_hsTowerState : HSTowerState A (Φ ⁻¹' W) H := by
  have hP:=target_power_domain w raw H hrec i U e he
  intro Z V hV
  exact HSTowerState.pullback Φ hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent
    (target_power_hsTowerState w raw H hrec i U e he) V hV

variable {Y' : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) U') Y')
  {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
  (hs : IsCanonical (windowPower w raw j U' f)
    ((canonicalInvariant n).inv (windowPower w raw j U' f)) S)
  (ht : IsCanonical (windowPower w raw i U e)
    ((canonicalInvariant n).inv (windowPower w raw i U e)) T)
  (hrs : IsGeoResolution (windowPower w raw j U' f) S)
  (hrt : IsGeoResolution (windowPower w raw i U e) T)

include hrec hadm he hf hs ht hrs hrt

def ambientComparison :=
  OriginalNativeTerminalPhaseComparison.ambientComparison P
    (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).1
    Φ S T (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.1
    ht (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.2 hrt

def nativeComparison :=
  OriginalNativeTerminalPhaseComparison.comparison P
    (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).1
    Φ S T (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.1
    ht (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.2 hrt
    W (target_carrier_analytic w raw H hrec i U)

theorem nativeComparison_projection :
    (nativeComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt).hom ≫
      OriginalNativeTerminalPhaseComparison.projection T W (target_carrier_analytic w raw H hrec i U)=
    OriginalNativeTerminalPhaseComparison.projection S (Φ ⁻¹' W)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage Φ.contMDiff
        (target_carrier_analytic w raw H hrec i U)) ≫
      (OriginalNativeTerminalPhaseComparison.baseIso Φ W
        (target_carrier_analytic w raw H hrec i U)).hom :=
  OriginalNativeTerminalPhaseComparison.comparison_projection P
    (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).1
    Φ S T (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.1
    ht (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.2 hrt
    W (target_carrier_analytic w raw H hrec i U)

theorem nativeComparison_scalar :
    (nativeComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt).hom.hom.left ≫
      (OriginalNativeTerminalPhaseComparison.strictSpace T W
        (target_carrier_analytic w raw H hrec i U)).obj.hom =
    (OriginalNativeTerminalPhaseComparison.strictSpace S (Φ ⁻¹' W)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage Φ.contMDiff
        (target_carrier_analytic w raw H hrec i U))).obj.hom :=
  Over.w (nativeComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt).hom.hom

theorem nativeComparison_inclusion :
    (nativeComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt).hom.hom.left ≫
      actualSubspaceInclusion (n := n) (strictTransform n T.proj W) =
    actualSubspaceInclusion (n := n) (strictTransform n S.proj (Φ ⁻¹' W)) ≫
      ChartedSpace.locallyRingedSpaceMap
        (ambientComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt)
        (ambientComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt).contMDiff :=
  (OriginalNativeTerminalPhaseComparison.comparison_inclusion P
    (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).1
    Φ S T (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.1
    ht (common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs).2.2 hrt
    W (target_carrier_analytic w raw H hrec i U)).symm

/-- Reg-avoidance is derived from actual powered tower states and the
held centres-over mother, never assumed of a future head. -/
theorem whole_iterated_carrier :
    strictAlong S (sourceCarrier w j U') =
      (ambientComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt) ⁻¹'
      strictAlong T W := by
  have h:=common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs
  have hA:=InvDomainTowerAlong.isInvDomain_pullback Φ h.1
  have hW:=target_carrier_analytic w raw H hrec i U
  have hW':=AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage Φ.contMDiff hW
  have hSing : (P).cosupp ⊆ HironakaEmbeddedAnalytic.singularSet (n := n) W :=
    (target_power_hsTowerState w raw H hrec i U e he .refl trivial).2.2.2.2
  have hSing' : (A).cosupp ⊆ HironakaEmbeddedAnalytic.singularSet (n := n) (Φ ⁻¹' W) :=
    (common_power_hsTowerState w raw H hrec i j U U' Φ e he .refl trivial).2.2.2.2
  have hAvoid : RestrictEmptyTower.CentresAvoid
      (HironakaResolutionSpaceComplex.regularOpen n hW.isClosed) T := by
    apply RestrictEmptyTower.centresAvoid_of_centresOver _ ?_ T
      (HironakaAdmissibleSequence.centresOver_cosupp P h.1.isWellFormed.isClosedSubmanifold_N
        h.1.isWellFormed.isCoherent T
        ((canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical h.1 T ht))
    exact Set.disjoint_left.mpr fun _ hxO hxCos=>hxO (hSing hxCos)
  have hAvoid' : RestrictEmptyTower.CentresAvoid
      (HironakaResolutionSpaceComplex.regularOpen n hW'.isClosed) S := by
    apply RestrictEmptyTower.centresAvoid_of_centresOver _ ?_ S
      (HironakaAdmissibleSequence.centresOver_cosupp A hA.isWellFormed.isClosedSubmanifold_N
        hA.isWellFormed.isCoherent S
        ((canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hA S h.2.1))
    exact Set.disjoint_left.mpr fun _ hxO hxCos=>hxO (hSing' hxCos)
  rw [← source_carrier_eq w i j U U' Φ hadm]
  exact OriginalNativeTerminalPhaseComparison.whole_iterated_carrier P h.1 Φ S T h.2.1 ht h.2.2 hrt
    W hW.isClosed (HironakaResolutionSpaceComplex.regularOpen n hW.isClosed)
    (HironakaResolutionSpaceComplex.regularOpen n hW'.isClosed)
    (HironakaResolutionSpace.subset_closure_diff_singularSet hW)
    (HironakaResolutionSpace.subset_closure_diff_singularSet hW') hAvoid hAvoid'

end
end Hironaka.Analytic.Unibranch.HironakaG1DistinctNativeTerminalComparison
