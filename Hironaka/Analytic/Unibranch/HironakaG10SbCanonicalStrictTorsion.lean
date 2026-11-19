import Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
import Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy

/-!
# The native strict transform stalk is the joint pulled quotient modulo exceptional torsion (G10-02-06.b/c)

Lane G10SB, run 0081, plan item G10-02-06 (sub-items 06.b/06.c of `G10SB/G10-02-06a-strict-readout-route.md`).
The literal G10-02-06 (read the stalk off the native `IsStrictTransform` structure) is refuted
(`G10-02-01-contract.md` §4); here the CONSTRUCTED strict transform of one actual blowup step is read.

Setting: `F : X ⟶ Y` a morphism of reduced complex spaces, `b : B ⟶ 𝒪_Y` a finite-type ideal, the native
geometric blowup `Bl_B Y` and the strict transform `Bl_{F*B} X` (`HironakaG10ChowOneStepStrictTransform.strictSource`),
with the canonical chart data `t c g d E M` produced from ordinary inputs
(`CompatibleCanonicalIdealBlowupMonomialLift.exists_same_canonical_allambient_monomial_lift`).  For a pivot `j`
and a recentring vector `v` with zero pivot coordinate, at every point `w` of the source real-open chart near its
origin lying on the strict transform:

* `chartIso` — the actual reduced model of the real-open strict carrier is isomorphic, through the canonical
  recentred chart biholomorphism, to the source strict chart object of the canonical machinery;
* `nativeStrictStalkTorsionEquiv` — **the native stalk of `Bl_{F*B} X` at the image point is the joint quotient
  `𝒪_amb ⧸ (raw source graph ideal ⊔ pulled target strict ideal)` (the chart ideal of the pulled module over
  the blown-up base) modulo its WHOLE exceptional-power torsion** (Hironaka 1975 (4.3.1), p. 535);
* it is the composite of the two open-immersion stalk isomorphisms with the inverse of TN's
  `jointTorsionQuotientEquiv` (definitionally), so it is induced by the actual ambient germs
  (`jointTorsionQuotientEquiv_mk`, `jointStrictStalkMap_mk`).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation

/-- The ring isomorphism of stalks of an open immersion of locally ringed spaces. -/
def openImmersionStalkEquiv {S T : LocallyRingedSpace.{0}} (k : S ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion k] (s : S) :
    T.presheaf.stalk (k.base s) ≃+* S.presheaf.stalk s :=
  (asIso (k.stalkMap s)).commRingCatIsoToRingEquiv

theorem openImmersionStalkEquiv_apply {S T : LocallyRingedSpace.{0}} (k : S ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion k] (s : S) (r : T.presheaf.stalk (k.base s)) :
    openImmersionStalkEquiv k s r = (k.stalkMap s).hom r :=
  rfl

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)
  (M : AllAmbientMonomialLiftData B b F x t c g d E)
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

/-- The real-open strict carrier is the canonical strict chart carrier, read in the recentred chart. -/
theorem mem_strict_iff_chart
    (w : sourceDomain B b F x t c g d E j v) :
    w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) ↔
      arbitraryCanonicalRecenteredChart E.source.charts j v hvj w ∈
        strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j := by
  have h := original_strict_carrier_conjugacy E.source.charts j v hvj (sourceGraphSet B b F x t c)
  exact Set.ext_iff.mp h w

/-- The actual reduced model of the real-open strict carrier is the canonical source strict chart
object, through the recentred chart biholomorphism. -/
def chartIso :
    actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
        (realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
          (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)) ≅
      actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
        (strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j) :=
  actualSubspaceBiholomorphicIso (arbitraryCanonicalRecenteredChart E.source.charts j v hvj) _ _
    (mem_strict_iff_chart B b F x t c g d E j v hvj)

variable (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)
  (w : sourceDomain B b F x t c g d E j v)
  (hw : w ∈ localDomain c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) h0
      (originalGraph_analytic B b F x t c g d E j v))
  (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))

/-- The point of the native strict transform `Bl_{F*B} X` read by the chart. -/
def nativePoint :
    (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left :=
  (sourceChartMap B b F x t c g d E j).base
    ((chartIso B b F x t c g d E j v hvj).hom.base ⟨w, hwS⟩)

include M hw in
/-- **G10-02-06.c.**  The native stalk of the constructed strict transform `Bl_{F*B} X` at the chart point
is the joint pulled quotient modulo its whole exceptional-power torsion. -/
def nativeStrictStalkTorsionEquiv :
    (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.stalk
        (nativePoint B b F x t c g d E j v hvj w hwS) ≃+*
      JointQuotient (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
          (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
          (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w ⧸
        HironakaG10JointStrictTorsion.pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim
          t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
          (originalGraph B b F x t c g d E j v) (actualMap B b F x t c g d E j v hvj)
          (targetStrict B b F x t c g d E j) w :=
  (openImmersionStalkEquiv (sourceChartMap B b F x t c g d E j)
      ((chartIso B b F x t c g d E j v hvj).hom.base ⟨w, hwS⟩)).trans
    ((openImmersionStalkEquiv (chartIso B b F x t c g d E j v hvj).hom ⟨w, hwS⟩).trans
      (jointTorsionQuotientEquiv (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j
        (fun i => v i) (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) h0
        (originalGraph_analytic B b F x t c g d E j v)
        (actualMap_holomorphic B b F x t c g d E M j v hvj).continuous
        (actual_landing B b F x t c g d E M j v hvj) w hw hwS).symm)

/-- Unwinding a composite of three ring isomorphisms. -/
theorem trans_trans_symm_apply {R S T U : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [NonAssocSemiring T] [NonAssocSemiring U] (e₁ : R ≃+* S) (e₂ : S ≃+* T) (e₃ : U ≃+* T) (u : U) :
    e₂ (e₁ ((e₁.trans (e₂.trans e₃.symm)).symm u)) = e₃ u := by
  rw [RingEquiv.symm_trans_apply, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
    RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end

end Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
