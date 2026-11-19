import Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseComparison
import Hironaka.Analytic.Unibranch.HironakaG1RSingularCentreEmbedded
import Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness
import Hironaka.Analytic.Unibranch.HironakaG11PresWindows
import Hironaka.Analytic.Unibranch.SourceMorphismExt
import Hironaka.Resolution.HironakaG8LocalPower

/-! Genuine original HS test histories derive the native dense-good
uniqueness criterion. Initial native isomorphisms may have different
ambient extensions off their carriers. Blueprint FIRST:
original-native-phase-endpoint-uniqueness.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativePhaseEndpointUniqueness
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower CanonicalCentres
  HironakaEmbeddedAnalytic HironakaG11PresTowerState HironakaG11PresLineState
  HironakaG8LocalHistory HironakaG8LocalPower HironakaActualPowerBoundaryExponents
  HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11CompatibleAnalyticCover HironakaG11PresWindows
  HironakaG11SingularCentreModification HironakaG1RSingularCentreEmbedded
  SourceReducedComplexSpace OriginalNativeTerminalPhaseComparison
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem conventional_eq_of_hsTowerState
    (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ}
    (hState : HSTowerState Q W H) (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) :
    strictAlong T W = strictTransform n T.proj W := by
  have hSing : Q.cosupp ⊆ singularSet (n := n) W :=
    (hState .refl trivial).2.2.2.2
  let O := HironakaResolutionSpaceComplex.regularOpen n hW.isClosed
  have hAvoid : RestrictEmptyTower.CentresAvoid O T :=
    RestrictEmptyTower.centresAvoid_of_centresOver O
      (Set.disjoint_left.mpr fun _ hxO hxCos => hxO (hSing hxCos)) T
      (HironakaAdmissibleSequence.centresOver_cosupp Q hQ.isWellFormed.isClosedSubmanifold_N
        hQ.isWellFormed.isCoherent T hT)
  exact HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid W hW.isClosed O
    (HironakaResolutionSpace.subset_closure_diff_singularSet hW) T hAvoid

theorem centresInSingular_of_hsTowerState
    (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ} (hState : HSTowerState Q W H) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower Q T → CentresInSingular W T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    have hSing := (hState T hT.1).2.2.2.2
    rw [conventional_eq_of_hsTowerState Q hQ W hW hState T hT.1] at hSing
    exact ⟨centresInSingular_of_hsTowerState Q hQ W hW hState T hT.1,
      hT.2.2.1.trans hSing⟩

theorem projection_isSingularCentreModification
    (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ} (hState : HSTowerState Q W H)
    (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) :
    IsSingularCentreModification (projection T W hW) :=
  isSingularCentreModification_projectionMorphism hW T
    (centresInSingular_of_hsTowerState Q hQ W hW hState T hT)

theorem projection_power_isSingularCentreModification
    (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ} (hState : NativeHSState Q W H)
    (e : ℕ) (he : 1 ≤ e) (T : BlowupTower X Y)
    (hCan : IsCanonical (powerMarked Q e) ((canonicalInvariant n).inv (powerMarked Q e)) T) :
    IsSingularCentreModification (projection T W hW) := by
  have hPow := powerMarked_isInvDomain Q hQ he
  have hWeak := (locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ he).wEquiv
  have hHS : HSTowerState (powerMarked Q e) W H :=
    HSTowerState.of_wEquiv hWeak hState.hsTowerState
  exact projection_isSingularCentreModification (powerMarked Q e) hPow W hW hHS T
    ((canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hPow T hCan)

private theorem native_lift_unique
    {A B C D : SourceReducedComplexSpace} {q : A ⟶ B} {p : C ⟶ D}
    (hq : IsSingularCentreModification q) (hp : IsSingularCentreModification p)
    (α : B ≅ D) (a b : A ⟶ C) (ha : a ≫ p=q ≫ α.hom) (hb : b ≫ p=q ≫ α.hom) : a=b := by
  have hα : LocallyRingedSpace.IsOpenImmersion α.hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft α).hom
    infer_instance
  have hBase : ∀ z, p.hom.left.base (a.hom.left.base z)=p.hom.left.base (b.hom.left.base z) := by
    intro z
    exact (congrArg (fun f : A ⟶ D => f.hom.left.base z) ha).trans
      (congrArg (fun f : A ⟶ D => f.hom.left.base z) hb).symm
  have hGood : ∀ z ∈ q.hom.left.base ⁻¹' intrinsicRegularLocus B.obj,
      p.hom.left.base (a.hom.left.base z) ∈ intrinsicRegularLocus D.obj := by
    intro z hz
    have hpoint := congrArg (fun f : A ⟶ D => f.hom.left.base z) ha
    change p.hom.left.base (a.hom.left.base z)=α.hom.hom.left.base (q.hom.left.base z) at hpoint
    rw [hpoint]
    by_contra hn
    have hSing := Set.ext_iff.mp
      (preimage_intrinsicSingularLocus_of_isOpenImmersion α.hom hα) (q.hom.left.base z)
    exact (hSing.mp hn) hz
  apply morphism_eq_of_pointwise_eq a b
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense hp.isIsoOver_intrinsicRegularLocus
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hBase
    hq.dense_preimage_intrinsicRegularLocus hGood) z

section TwoEndpoints
variable {m : ℕ} {Z E : CMfd.{0} m}
  (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (W : Set X)
  (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ} (hState : HSTowerState Q W H)
  (S : BlowupTower X Y) (hS : IsGeoTestTower Q S)
  (R : MarkedIdeal m Z) (hR : IsInvDomain m R) (V : Set Z)
  (hV : IsComplexAnalyticSubset (n := m) V) {K : ℕ → ℕ} (hStateR : HSTowerState R V K)
  (T : BlowupTower Z E) (hT : IsGeoTestTower R T)

include Q hQ hState hS R hR hStateR hT
theorem maps_eq_over_native_iso
    (α : ofClosedAnalytic W hW ≅ ofClosedAnalytic V hV)
    (a b : strictSpace S W hW ⟶ strictSpace T V hV)
    (ha : a ≫ projection T V hV=projection S W hW ≫ α.hom)
    (hb : b ≫ projection T V hV=projection S W hW ≫ α.hom) : a=b :=
  native_lift_unique (projection_isSingularCentreModification Q hQ W hW hState S hS)
    (projection_isSingularCentreModification R hR V hV hStateR T hT) α a b ha hb

theorem endpoint_cocycle {B C : SourceReducedComplexSpace} (p₂ : B ⟶ C)
    (α₁₂ : ofClosedAnalytic W hW ≅ C) (α₂₃ : C ≅ ofClosedAnalytic V hV)
    (α₁₃ : ofClosedAnalytic W hW ≅ ofClosedAnalytic V hV)
    (hα : α₁₂.hom ≫ α₂₃.hom=α₁₃.hom)
    (a₁₂ : strictSpace S W hW ⟶ B) (a₂₃ : B ⟶ strictSpace T V hV)
    (a₁₃ : strictSpace S W hW ⟶ strictSpace T V hV)
    (h₁₂ : a₁₂ ≫ p₂=projection S W hW ≫ α₁₂.hom)
    (h₂₃ : a₂₃ ≫ projection T V hV=p₂ ≫ α₂₃.hom)
    (h₁₃ : a₁₃ ≫ projection T V hV=projection S W hW ≫ α₁₃.hom) :
    a₁₂ ≫ a₂₃=a₁₃ := by
  apply maps_eq_over_native_iso Q hQ W hW hState S hS R hR V hV hStateR T hT
    α₁₃ (a₁₂ ≫ a₂₃) a₁₃ ?_ h₁₃
  rw [Category.assoc,h₂₃,← Category.assoc,h₁₂,Category.assoc,hα]

end TwoEndpoints
end
end Hironaka.Analytic.Unibranch.OriginalNativePhaseEndpointUniqueness
