import Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison
import Hironaka.Resolution.HironakaG8P1ArcTangentTrace
import Hironaka.Resolution.HironakaG11PresLineState

/-! Actual original terminal phase inputs construct a whole native endpoint
comparison without a common physical clock. Blueprint FIRST:
original-native-terminal-phase-comparison.tex. No arbitrary native cocycle
or projection-only uniqueness is asserted. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseComparison
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres HomogenizedGlueingTower
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  MarkedIdealBiholomorphism HironakaReducedComplexAnalyticSpaces
  HironakaG11CompatibleAnalyticCover SourceReducedComplexSpace
  HironakaOriginalTerminalOverlapComparison HironakaG8LocalHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X X' Y Y' : CMfd.{0} n}

def strictSpace (T : BlowupTower X Y) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictTransform n T.proj W)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)

private theorem strict_mapsTo (T : BlowupTower X Y) (W : Set X) (hW : IsClosed W) :
    ∀ y ∈ strictTransform n T.proj W, T.proj y ∈ W := by
  intro y hy
  exact (closure_minimal sdiff_subset (hW.preimage T.contMDiff_proj.continuous)) hy

def projection (T : BlowupTower X Y) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) : strictSpace T W hW ⟶ ofClosedAnalytic W hW :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap T.contMDiff_proj (strict_mapsTo T W hW.isClosed))
    (actualSubspaceMap_point T.contMDiff_proj (strict_mapsTo T W hW.isClosed)))

private theorem preimage_analytic
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (Φ ⁻¹' W) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage Φ.contMDiff hW

def baseIso (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    ofClosedAnalytic (Φ ⁻¹' W) (preimage_analytic Φ W hW) ≅ ofClosedAnalytic W hW :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk (actualSubspaceBiholomorphicIso Φ (Φ ⁻¹' W) W (fun _ => Iff.rfl))
      (actualSubspaceMap_point Φ.contMDiff (fun _ hx => hx)))

variable (M : MarkedIdeal n X) (hM : IsInvDomain n M)
  (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
  (S : BlowupTower X' Y') (T : BlowupTower X Y)
  (hs : IsCanonical (MarkedIdeal.pullback Φ M)
    ((canonicalInvariant n).inv (MarkedIdeal.pullback Φ M)) S)
  (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
  (hrs : IsGeoResolution (MarkedIdeal.pullback Φ M) S) (hrt : IsGeoResolution M T)

def ambientComparison : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y :=
  (original_ambient_terminal_base_existsUnique M hM Φ S T hs ht hrs hrt).choose

theorem ambientComparison_proj (y : Y') :
    T.proj (ambientComparison M hM Φ S T hs ht hrs hrt y)=Φ (S.proj y) :=
  (original_ambient_terminal_base_existsUnique M hM Φ S T hs ht hrs hrt).choose_spec.1 y

private theorem strict_biholomorph
    {A B : CMfd.{0} n} (e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B)
    (C : Set B) (hC : IsClosed C) : strictTransform n e C=e ⁻¹' C := by
  have he : exceptionalLocus n e=∅ := eq_empty_iff_forall_notMem.mpr
    (MarkedIdealTowerTransport.notMem_exceptionalLocus e)
  change closure (e ⁻¹' C \ exceptionalLocus n e)=_
  rw [he,sdiff_empty]
  exact (hC.preimage e.contMDiff.continuous).closure_eq

theorem whole_carrier (W : Set X) (hW : IsClosed W) :
    strictTransform n S.proj (Φ ⁻¹' W) =
      (ambientComparison M hM Φ S T hs ht hrs hrt) ⁻¹' strictTransform n T.proj W := by
  let η := ambientComparison M hM Φ S T hs ht hrs hrt
  have hp : T.proj ∘ η=Φ ∘ S.proj :=
    funext (ambientComparison_proj M hM Φ S T hs ht hrs hrt)
  calc
    _ = strictTransform n S.proj (strictTransform n Φ W) := by rw [strict_biholomorph Φ W hW]
    _ = strictTransform n (Φ ∘ S.proj) W :=
      (StrictTransformComposition.strictTransform_comp Φ.contMDiff S.contMDiff_proj W).symm
    _ = strictTransform n (T.proj ∘ η) W := congrArg (fun f => strictTransform n f W) hp.symm
    _ = strictTransform n η (strictTransform n T.proj W) :=
      StrictTransformComposition.strictTransform_comp T.contMDiff_proj η.contMDiff W
    _ = _ := strict_biholomorph η _ isClosed_closure

private theorem carrier_iff (W : Set X) (hW : IsClosed W) (y : Y') :
    y ∈ strictTransform n S.proj (Φ ⁻¹' W) ↔
      ambientComparison M hM Φ S T hs ht hrs hrt y ∈ strictTransform n T.proj W := by
  rw [whole_carrier M hM Φ S T hs ht hrs hrt W hW]
  rfl

def comparison (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    strictSpace S (Φ ⁻¹' W) (preimage_analytic Φ W hW) ≅ strictSpace T W hW :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk (actualSubspaceBiholomorphicIso
      (ambientComparison M hM Φ S T hs ht hrs hrt) _ _
      (carrier_iff M hM Φ S T hs ht hrs hrt W hW.isClosed))
      (actualSubspaceMap_point (ambientComparison M hM Φ S T hs ht hrs hrt).contMDiff
        (fun y hy => (carrier_iff M hM Φ S T hs ht hrs hrt W hW.isClosed y).mp hy)))

theorem comparison_projection (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    (comparison M hM Φ S T hs ht hrs hrt W hW).hom ≫ projection T W hW =
      projection S (Φ ⁻¹' W) (preimage_analytic Φ W hW) ≫ (baseIso Φ W hW).hom := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change actualSubspaceMap _ _ ≫ actualSubspaceMap _ _ =
    actualSubspaceMap _ _ ≫ actualSubspaceMap _ _
  rw [← actualSubspaceMap_comp,← actualSubspaceMap_comp]
  have hp : T.proj ∘ ambientComparison M hM Φ S T hs ht hrs hrt = Φ ∘ S.proj :=
    funext (ambientComparison_proj M hM Φ S T hs ht hrs hrt)
  simp only [hp]

theorem comparison_scalar (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    (comparison M hM Φ S T hs ht hrs hrt W hW).hom.hom.left ≫
      (strictSpace T W hW).obj.hom =
        (strictSpace S (Φ ⁻¹' W) (preimage_analytic Φ W hW)).obj.hom :=
  Over.w (comparison M hM Φ S T hs ht hrs hrt W hW).hom.hom

theorem comparison_inclusion (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    type_of% (actualSubspaceMap_inclusion
      (ambientComparison M hM Φ S T hs ht hrs hrt).contMDiff
      (fun y hy => (carrier_iff M hM Φ S T hs ht hrs hrt W hW.isClosed y).mp hy)) :=
  actualSubspaceMap_inclusion _ _

theorem whole_iterated_carrier (W : Set X) (hW : IsClosed W)
    (O : Opens X) (O' : Opens X')
    (hDense : W ⊆ closure (W ∩ (O : Set X)))
    (hDense' : Φ ⁻¹' W ⊆ closure ((Φ ⁻¹' W) ∩ (O' : Set X')))
    (hAvoid : RestrictEmptyTower.CentresAvoid O T)
    (hAvoid' : RestrictEmptyTower.CentresAvoid O' S) :
    strictAlong S (Φ ⁻¹' W) =
      (ambientComparison M hM Φ S T hs ht hrs hrt) ⁻¹' strictAlong T W := by
  rw [HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid W hW O hDense T hAvoid,
    HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid
      (Φ ⁻¹' W) (hW.preimage Φ.contMDiff.continuous) O' hDense' S hAvoid']
  exact whole_carrier M hM Φ S T hs ht hrs hrt W hW



private theorem avoids_regular (A : MarkedIdeal n X) (hA : IsInvDomain n A)
    (R : BlowupTower X Y) (hCan : IsCanonical A ((canonicalInvariant n).inv A) R)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : A.cosupp ⊆ HironakaEmbeddedAnalytic.singularSet (n := n) W) :
    RestrictEmptyTower.CentresAvoid (HironakaResolutionSpaceComplex.regularOpen n hW.isClosed) R := by
  apply RestrictEmptyTower.centresAvoid_of_centresOver
    (HironakaResolutionSpaceComplex.regularOpen n hW.isClosed) ?_ R
      (HironakaAdmissibleSequence.centresOver_cosupp A hA.isWellFormed.isClosedSubmanifold_N
        hA.isWellFormed.isCoherent R
        ((canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hA R hCan))
  exact Set.disjoint_left.mpr fun _ hxO hxCos => hxO (hSing hxCos)

theorem whole_iterated_carrier_of_native_state (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ}
    (hState : HironakaG11PresLineState.NativeHSState M W H) :
    strictAlong S (Φ ⁻¹' W) =
      (ambientComparison M hM Φ S T hs ht hrs hrt) ⁻¹' strictAlong T W := by
  have hW' := preimage_analytic Φ W hW
  have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  have hState' := hState.pullback Φ
  have hSing : M.cosupp ⊆ HironakaEmbeddedAnalytic.singularSet (n := n) W :=
    (hState.hsTowerState .refl trivial).2.2.2.2
  have hSing' : (MarkedIdeal.pullback Φ M).cosupp ⊆
      HironakaEmbeddedAnalytic.singularSet (n := n) (Φ ⁻¹' W) :=
    (hState'.hsTowerState .refl trivial).2.2.2.2
  apply whole_iterated_carrier M hM Φ S T hs ht hrs hrt W hW.isClosed
    (HironakaResolutionSpaceComplex.regularOpen n hW.isClosed)
    (HironakaResolutionSpaceComplex.regularOpen n hW'.isClosed)
  · exact HironakaResolutionSpace.subset_closure_diff_singularSet hW
  · exact HironakaResolutionSpace.subset_closure_diff_singularSet hW'
  · exact avoids_regular M hM T ht W hW hSing
  · exact avoids_regular (MarkedIdeal.pullback Φ M) hM' S hs (Φ ⁻¹' W) hW' hSing'

end
end Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseComparison
