import Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical
import Hironaka.Analytic.Unibranch.HironakaG10NfGeoFields
import Hironaka.Analytic.Unibranch.HironakaG10NfChartChoice
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelOrigin

/-!
# H3.4/H3.5: `fibreModel_of_canonical` and `hfib_of_canonical`

Lane G10H3, run 0081.  Hironaka 1975, Lemma 4.4.5 (fibre comparison), from the canonical charts.

* `geoFibreModel_canonical` — the local model `HironakaG10NfGeoFibreModel.GeoFibreModel` of `X ×_Y Bl_B Y` near
  `(x, y)` on a canonical recentred chart (G10FI's `W`, `pY`, `pT`, `square`, `cover`; the joint quotient with
  `ψ = targetStalkToJoint ∘ targetChartMap^♯` and the joint pivot torsion; G10N34's `flat_base_geo`), for any ideal
  family `H` locally finitely generated near `y`;
* `fibreModel_of_canonical` — at every stage point `x'` of `Z₁.support` over the centre and every `y` over it, the
  model `FibreModel₀` (chart choice: `exists_same_canonical_allambient_monomial_lift`, `exists_target_pivot_point`,
  G10FI's `exists_origin`; transport along `blowupIso`: `fibreModel₀_of_geo`);
* **`hfib_of_canonical`** — the `hfib` binder of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`,
  unconditionally.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelCanonical

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaG10ChowFibreAlgebra
  BlowupConstruction BlowupStrictSubmanifold
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion

section Canonical

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

-- the `IsFiniteType` instance of `HironakaG10NfGeoFibreModel`, so that the field types match literally
attribute [local instance] Hironaka.Analytic.Unibranch.HironakaG10NfGeoFibreModel.instIsFiniteTypeOpensCarrierCarrierCommRingCatLeftLocallyRingedSpaceObjOverComplexPointSourceReducedComplexSpacePropertyNativePulledIdealModuleLeftHomFullSubcategory

variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)
  (M : AllAmbientMonomialLiftData B b F x t c g d E)
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)
  (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)

include M in
/-- **The local model of the fibre product on a canonical chart** at an origin `w₀` over `(x, y)`. -/
theorem geoFibreModel_canonical (w₀ : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (hproj : HironakaG10NfFibreCover.proj B b F x t c g d E j v hvj w₀.1 = c.point.val)
    (hpY : HironakaG10NfFibreCover.pY B b F x t c g d E j v hvj h0 w₀ = x)
    (hpT : HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w₀ = y)
    (H : ∀ Q : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left,
      Ideal ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk Q))
    (V'' : Set (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hfg : HironakaG10HirIdealGerms.IsLocallyFinitelyGeneratedOn
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left V'' H)
    (hV'' : V'' ∈ 𝓝 y) :
    Nonempty (HironakaG10NfGeoFibreModel.GeoFibreModel B b F H x y) :=
  ⟨{ W := HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0
     w₀ := w₀
     pY := HironakaG10NfFibreCover.pY B b F x t c g d E j v hvj h0
     pT := HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0
     pY_w₀ := hpY
     pT_w₀ := hpT
     square := HironakaG10NfFibreCover.square B b F x t c g d E j v hvj h0
     cover := HironakaG10NfGeoFields.cover_of_eq _ _ w₀ hpY hpT _ _
       (HironakaG10NfFibreCover.cover B b F x t c g d E j v hvj h0 w₀)
     Bw := fun w => JointQuotient (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1
     ring := fun _ => inferInstance
     noetherian := fun _ => inferInstance
     ψ := fun w => HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2
     T := fun w => pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1
     local₀ := HironakaG10NfGeoFields.local₀_canonical B b F x t c g d E M j v hvj w₀.1 w₀.2.2.2
     T_w₀ := fun G hG hspan => HironakaG10NfJointPivotCanonical.pivotTorsion_eq_powerSat_canonical
       B b F x t c g d E M j v hvj w₀.1 w₀.2.2.2 G hG hspan
     flat_base₀ := fun J hJ => HironakaG10NfGeoFields.flat_base₀_canonical B b F x t c g d E M j v hvj h0 w₀
       hproj hpY J hJ
     strict := fun w hT => HironakaG10NfStrictCanonical.strict_field B b F x t c g d E M j v hvj h0 w hT
     strict₀ := fun hT => HironakaG10NfStrictCanonical.strict0_field B b F x t c g d E M j v hvj h0 w₀ hT
     spread := HironakaG10NfGeoFields.spread_canonical B b F x t c g d E M j v hvj h0 H V'' hfg w₀
       ((congrArg (fun q => V'' ∈ 𝓝 q) hpT).mpr hV'') }⟩

end Canonical

section Stage

open HironakaG10HirFlatQuotient HironakaG10ChowArtinReesCentre
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra Hironaka.Analytic.Unibranch.HironakaG10NfFibreReduction
  Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelOrigin
  Hironaka.Analytic.Unibranch.HironakaG10NfGeoFibreModel

attribute [local instance] AdmissibleCentre.finiteType

/-- **`fibreModel_of_canonical`**: a local model with base-change data at the origin, at every point of the next
local flattener's support over the centre, for every source point over it. -/
theorem fibreModel_of_canonical (s : Stage) (c : AdmissibleCentre s.f) (Z₁ : LocalFlattener (nextWith s c).f)
    (x' : (nextWith s c).X.obj.left) (hx₁ : x' ∈ Z₁.support)
    (hc : (stepσ s c).hom.left.base x' ∈ nonunitLocus c.B c.b)
    (y : s.Y.obj.left) (hy : s.f.hom.left.base y = (stepσ s c).hom.left.base x') :
    Nonempty (FibreModel₀ s c Z₁ y x') := by
  have hxy : s.f.hom.left.base y = (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left.base
      ((blowupIso c.B c.b c.dense).hom.hom.left.base x') := hy.trans (piT_hom_base s c x').symm
  have hc' : (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left.base
      ((blowupIso c.B c.b c.dense).hom.hom.left.base x') ∈ nonunitLocus c.B c.b :=
    (congrArg (fun z => z ∈ nonunitLocus c.B c.b) (piT_hom_base s c x')).mpr hc
  have hV'' : (invMap s c).base ⁻¹' Z₁.V ∈ 𝓝 ((blowupIso c.B c.b c.dense).hom.hom.left.base x') :=
    (invMap s c).base.hom.continuous.continuousAt.preimage_mem_nhds
      (Z₁.isOpen.mem_nhds ((congrArg (fun z => z ∈ Z₁.V) (inv_hom_base s c x')).mpr hx₁.1))
  have hfg := HironakaG10NfSpreadGerm.isLocallyFinitelyGeneratedOn_map (invMap s c) Z₁.V Z₁.H Z₁.fg
  refine (exists_same_canonical_allambient_monomial_lift c.B c.b s.f y _ hxy).elim fun t ht => ?_
  refine ht.elim fun c' hc'' => hc''.elim fun g hg => hg.elim fun d hd => hd.elim fun E hE => hE.elim fun M => ?_
  refine (HironakaG10NfChartChoice.exists_target_pivot_point c.B c.b s.f y t c' g d E hc').elim
    fun j hj => hj.elim fun p hp => ?_
  have hpy : s.f.hom.left.base y = (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left.base
      ((targetChartMap c.B c.b s.f y t c' g d E j).base p) :=
    hxy.trans (congrArg _ hp.1.symm)
  refine (HironakaG10NfFibreCover.exists_origin c.B c.b s.f y t c' g d E j p hp.2 hpy).elim
    fun v hv => hv.elim fun hvj hv' => hv'.elim fun h0 hw => hw.elim fun w₀ hw₀ => ?_
  refine (geoFibreModel_canonical c.B c.b s.f y t c' g d E M j v hvj h0 w₀ hw₀.2.1 hw₀.2.2.1
    (hw₀.2.2.2.trans hp.1) (transH s c Z₁) _ hfg hV'').elim fun Mg => ?_
  exact fibreModel₀_of_geo s c Z₁ y x' Mg

/-- **`hfib` (Hironaka Lemma 4.4.5, fibre comparison)**: the literal `hfib` binder of
`HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`, unconditionally. -/
theorem hfib_of_canonical :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support →
              ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
                ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
                  (nextWith s c).f.hom.left.base y'' = y' ∧
                  Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom
                      (fibreIdealAt (nextWith s c).f y'') ≤
                    fibreIdealAt s.f ((stepQ s c).hom.left.base y'') :=
  HironakaG10NfFibreModelOrigin.hfib_of_fibreModels₀
    (fun s _ _ c _ _ _ _ _ _ Z₁ hx₁ hc y hy => fibreModel_of_canonical s c Z₁ _ hx₁ hc y hy)

end Stage

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelCanonical
