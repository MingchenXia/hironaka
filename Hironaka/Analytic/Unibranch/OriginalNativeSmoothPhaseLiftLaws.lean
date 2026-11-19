import Hironaka.Analytic.Unibranch.OriginalNativePhaseEndpointUniqueness
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothComposition

/-! Ordinary RAW-power canonical histories derive genuine native smooth
lift uniqueness and actual identity/composition laws. Blueprint FIRST:
original-native-smooth-phase-lift-laws.tex. No lift existence, smooth HS
endpoint, powered NativeHSState, dense-good or fibre packet is assumed. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothPhaseLiftLaws
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11SingularCentreModification
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothSingularLocus
  OriginalNativeTerminalPhaseComparison OriginalNativePhaseEndpointUniqueness
  HironakaG11PresTowerState HironakaG11PresLineState HironakaG11PresWindows
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaActualPowerBoundaryExponents HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

private theorem native_lift_eq_of_smooth
    {A B C D : SourceReducedComplexSpace} {q : A ⟶ B} {p : C ⟶ D}
    (hq : IsSingularCentreModification q) (hp : IsSingularCentreModification p)
    (f : B ⟶ D) (hf : IsSmoothMorphism f) (a b : A ⟶ C)
    (ha : a ≫ p=q ≫ f) (hb : b ≫ p=q ≫ f) : a=b := by
  have hBase : ∀z,p.hom.left.base (a.hom.left.base z)=p.hom.left.base (b.hom.left.base z) := by
    intro z
    exact (congrArg (fun g : A ⟶ D=>g.hom.left.base z) ha).trans
      (congrArg (fun g : A ⟶ D=>g.hom.left.base z) hb).symm
  have hGood : ∀z∈q.hom.left.base ⁻¹' intrinsicRegularLocus B.obj,
      p.hom.left.base (a.hom.left.base z)∈intrinsicRegularLocus D.obj := by
    intro z hz
    have hPoint:=congrArg (fun g : A ⟶ D=>g.hom.left.base z) ha
    change p.hom.left.base (a.hom.left.base z)=f.hom.left.base (q.hom.left.base z) at hPoint
    rw [hPoint]
    exact (smoothAt_regular_iff f _ (hf _)).mp hz
  apply morphism_eq_of_pointwise_eq a b
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense hp.isIsoOver_intrinsicRegularLocus
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hBase
    hq.dense_preimage_intrinsicRegularLocus hGood) z

section ActualIteratedProjection
variable {n : ℕ} {M Z : CMfd.{0} n} (Q : MarkedIdeal n M) (hQ : IsInvDomain n Q)
  (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ}
  (hState : HSTowerState Q W H) (T : BlowupTower M Z) (hTest : IsGeoTestTower Q T)

include hQ hW hState hTest in
theorem strictCarrier_eq_conventional : strictAlong T W=strictTransform n T.proj W := by
  have hSing : Q.cosupp ⊆ HironakaEmbeddedAnalytic.singularSet (n := n) W :=
    (hState .refl trivial).2.2.2.2
  let O:=HironakaResolutionSpaceComplex.regularOpen n hW.isClosed
  have hAvoid : RestrictEmptyTower.CentresAvoid O T :=
    RestrictEmptyTower.centresAvoid_of_centresOver O
      (Set.disjoint_left.mpr fun _ hxO hxCos=>hxO (hSing hxCos)) T
      (HironakaAdmissibleSequence.centresOver_cosupp Q hQ.isWellFormed.isClosedSubmanifold_N
        hQ.isWellFormed.isCoherent T hTest)
  exact HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid W hW.isClosed O
    (HironakaResolutionSpace.subset_closure_diff_singularSet hW) T hAvoid

private theorem closedSpace_eq {C D : Set Z}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (h : C=D) :
    ofClosedAnalytic C hC=ofClosedAnalytic D hD := by
  cases h
  rfl

private theorem closedSpace_eqToHom_point {C D : Set Z}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (h : C=D)
    (z : (ofClosedAnalytic C hC).obj.left) :
    ((eqToHom (closedSpace_eq hC hD h)).hom.left.base z).val=z.val := by
  cases h
  rfl

def iteratedEndpoint : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictAlong T W) (hState T hTest).1

include hQ in
def iteratedEndpointIso : iteratedEndpoint Q W hState T hTest ≅ strictSpace T W hW :=
  eqToIso (closedSpace_eq (hState T hTest).1
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)
    (strictCarrier_eq_conventional Q hQ W hW hState T hTest))

include hQ in
theorem iteratedEndpointIso_point (z : (iteratedEndpoint Q W hState T hTest).obj.left) :
    ((iteratedEndpointIso Q hQ W hW hState T hTest).hom.hom.left.base z).val=z.val :=
  closedSpace_eqToHom_point (hState T hTest).1
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)
    (strictCarrier_eq_conventional Q hQ W hW hState T hTest) z

include hQ in
def iteratedProjection : iteratedEndpoint Q W hState T hTest ⟶ ofClosedAnalytic W hW :=
  (iteratedEndpointIso Q hQ W hW hState T hTest).hom ≫ projection T W hW

include hQ in
theorem iteratedEndpointIso_projection :
    (iteratedEndpointIso Q hQ W hW hState T hTest).hom ≫ projection T W hW=
      iteratedProjection Q hQ W hW hState T hTest := rfl

include hQ in
theorem iteratedProjection_point (z : (iteratedEndpoint Q W hState T hTest).obj.left) :
    ((iteratedProjection Q hQ W hW hState T hTest).hom.left.base z).val=T.proj z.val := by
  change T.proj ((iteratedEndpointIso Q hQ W hW hState T hTest).hom.hom.left.base z).val=T.proj z.val
  rw [iteratedEndpointIso_point]

include hQ in
theorem iteratedProjection_eq_of_pointwise
    (p : iteratedEndpoint Q W hState T hTest ⟶ ofClosedAnalytic W hW)
    (hp : ∀z,(p.hom.left.base z).val=T.proj z.val) :
    p=iteratedProjection Q hQ W hW hState T hTest := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  exact (hp z).trans (iteratedProjection_point Q hQ W hW hState T hTest z).symm

private theorem singularModification_eqToHom_comp
    {A B C : SourceReducedComplexSpace} (h : A=B) (p : B ⟶ C)
    (hp : IsSingularCentreModification p) : IsSingularCentreModification (eqToHom h ≫ p) := by
  cases h
  simpa only [eqToHom_refl,Category.id_comp] using hp

include hQ in
theorem iteratedProjection_isSingularCentreModification :
    IsSingularCentreModification (iteratedProjection Q hQ W hW hState T hTest) :=
  singularModification_eqToHom_comp
    (closedSpace_eq (hState T hTest).1
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)
      (strictCarrier_eq_conventional Q hQ W hW hState T hTest)) (projection T W hW)
    (projection_isSingularCentreModification Q hQ W hW hState T hTest)

variable {m : ℕ} {N E : CMfd.{0} m} (R : MarkedIdeal m N) (hR : IsInvDomain m R)
  (V : Set N) (hV : IsComplexAnalyticSubset (n := m) V) {K : ℕ → ℕ}
  (hStateR : HSTowerState R V K) (S : BlowupTower N E) (hTestR : IsGeoTestTower R S)

/-- The literal actual iterated native projections, at different ambient
dimensions, have no caller density/fibre/representation premise. -/
theorem iteratedLift_eq (f : ofClosedAnalytic W hW ⟶ ofClosedAnalytic V hV)
    (hf : IsSmoothMorphism f)
    (a b : iteratedEndpoint Q W hState T hTest ⟶ iteratedEndpoint R V hStateR S hTestR)
    (ha : a ≫ iteratedProjection R hR V hV hStateR S hTestR=
      iteratedProjection Q hQ W hW hState T hTest ≫ f)
    (hb : b ≫ iteratedProjection R hR V hV hStateR S hTestR=
      iteratedProjection Q hQ W hW hState T hTest ≫ f) : a=b :=
  native_lift_eq_of_smooth
    (iteratedProjection_isSingularCentreModification Q hQ W hW hState T hTest)
    (iteratedProjection_isSingularCentreModification R hR V hV hStateR S hTestR) f hf a b ha hb

end ActualIteratedProjection

section ActualHistories
variable {ι : Type*} (dim : ι → ℕ) (M Z : ∀i,CMfd.{0} (dim i))
  (Q : ∀i,MarkedIdeal (dim i) (M i)) (hQ : ∀i,IsInvDomain (dim i) (Q i))
  (W : ∀i,Set (M i)) (hW : ∀i,IsComplexAnalyticSubset (n := dim i) (W i))
  (H : ι → ℕ → ℕ) (hRaw : ∀i,NativeHSState (Q i) (W i) (H i))
  (e : ι → ℕ) (he : ∀i,1≤e i) (T : ∀i,BlowupTower (M i) (Z i))
  (hCan : ∀i,IsCanonical (powerMarked (Q i) (e i))
    ((canonicalInvariant (dim i)).inv (powerMarked (Q i) (e i))) (T i))

local notation "Base" => fun i=>ofClosedAnalytic (W i) (hW i)
local notation "End" => fun i=>strictSpace (T i) (W i) (hW i)
local notation "proj" => fun i=>projection (T i) (W i) (hW i)

include hQ hRaw he hCan in
/-- Actual RAW states and actual WHOLE-power canonical histories derive
the ordinary native modification data internally, at every dimension. -/
theorem phaseProjection_isSingularCentreModification (i : ι) :
    IsSingularCentreModification (proj i) :=
  projection_power_isSingularCentreModification (Q i) (hQ i) (W i) (hW i)
    (hRaw i) (e i) (he i) (T i) (hCan i)

include hQ hRaw he hCan in
/-- ANY two actual full native lifts over an arbitrary genuine smooth
base arrow agree; no fibre or density premise is supplied. -/
theorem phaseLift_eq (i j : ι) (f : Base i ⟶ Base j) (hf : IsSmoothMorphism f)
    (a b : End i ⟶ End j) (ha : a ≫ proj j=proj i ≫ f) (hb : b ≫ proj j=proj i ≫ f) : a=b :=
  native_lift_eq_of_smooth
    (phaseProjection_isSingularCentreModification dim M Z Q hQ W hW H hRaw e he T hCan i)
    (phaseProjection_isSingularCentreModification dim M Z Q hQ W hW H hRaw e he T hCan j)
    f hf a b ha hb

include hQ hRaw he hCan in
/-- The literal identity is the actual candidate; its square is derived. -/
theorem phaseLift_identity (i : ι) (a : End i ⟶ End i) (ha : a ≫ proj i=proj i) :
    a=𝟙 (End i) := by
  apply phaseLift_eq dim M Z Q hQ W hW H hRaw e he T hCan i i
    (𝟙 (Base i)) (isSmoothMorphism_identity (Base i)) a (𝟙 (End i))
  · simpa only [Category.comp_id] using ha
  · simp only [Category.id_comp,Category.comp_id]

include hQ hRaw he hCan in
/-- Genuine composition follows from the two actual squares and the
actual composite-base candidate, without a functor-law packet. -/
theorem phaseLift_composition (i j k : ι)
    (f : Base i ⟶ Base j) (g : Base j ⟶ Base k)
    (hf : IsSmoothMorphism f) (hg : IsSmoothMorphism g)
    (a : End i ⟶ End j) (b : End j ⟶ End k) (c : End i ⟶ End k)
    (ha : a ≫ proj j=proj i ≫ f) (hb : b ≫ proj k=proj j ≫ g)
    (hc : c ≫ proj k=proj i ≫ (f ≫ g)) : a ≫ b=c := by
  apply phaseLift_eq dim M Z Q hQ W hW H hRaw e he T hCan i k
    (f ≫ g) (isSmoothMorphism_comp f g hf hg) (a ≫ b) c
  · rw [Category.assoc,hb,← Category.assoc,ha,Category.assoc]
  · exact hc

end ActualHistories

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothPhaseLiftLaws
