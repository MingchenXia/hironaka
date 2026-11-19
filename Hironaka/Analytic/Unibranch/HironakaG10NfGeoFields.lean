import Hironaka.Analytic.Unibranch.HironakaG10NfJointPivotCanonical
import Hironaka.Analytic.Unibranch.HironakaG10NfJointLocal
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreCover
import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlatBase
import Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport
import Hironaka.Analytic.Unibranch.HironakaG10NfSpreadGerm

/-!
# H3.4 (fields `cover`, `local₀`, `flat_base₀`, `spread` on the canonical chart)

Lane G10H3, run 0081.  Canonical setting of `HironakaG10SbCanonicalStrictTorsion`; `W`, `pY`, `pT` are G10FI's
`HironakaG10NfFibreCover.{W, pY, pT}` and `ψ w := HironakaG10NfJointPivotCanonical.psi … w.1 w.2.2.2`.

* `cover_of_eq` — the covering property at `(pY w₀, pT w₀)` read at equal points (generic);
* `local₀_canonical` — `ψ(𝔪) ⊆ jacobson 0` of the joint quotient;
* `flat_base₀_canonical` — G10N34's `flat_base_geo`, read at `pY w₀ = x`;
* `spread_canonical` — a torsion bound by an ideal family locally finitely generated near `pT w₀` spreads to nearby
  pairs.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfGeoFields

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaG10HirFlatQuotient
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
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease

/-- **The covering property read at equal points** (generic). -/
theorem cover_of_eq {W A Bt : Type*} [TopologicalSpace W] [TopologicalSpace A] [TopologicalSpace Bt]
    (pY : W → A) (pT : W → Bt) (w₀ : W) {a : A} {q : Bt} (ha : pY w₀ = a) (hq : pT w₀ = q)
    (R N : A × Bt → Prop)
    (h : ∀ U ∈ 𝓝 w₀, ∀ᶠ p in 𝓝 (pY w₀, pT w₀), R p → ∃ w ∈ U, pY w = p.1 ∧ pT w = p.2) :
    ∀ U ∈ 𝓝 w₀, ∀ᶠ p in 𝓝 (a, q), N p → R p → ∃ w ∈ U, pY w = p.1 ∧ pT w = p.2 := by
  subst ha hq
  intro U hU
  filter_upwards [h U hU] with p hp _ hr
  exact hp hr

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
  (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)

include M in
/-- **`local₀`**: the canonical base map sends the maximal ideal into the Jacobson radical of the joint quotient. -/
theorem local₀_canonical (w : sourceDomain B b F x t c g d E j v)
    (hV : actualMap B b F x t c g d E j v hvj w ∈ targetStrict B b F x t c g d E j) :
    Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w hV)
      (IsLocalRing.maximalIdeal _) ≤ Ideal.jacobson ⊥ :=
  haveI : IsLocalHom ((targetChartMap B b F x t c g d E j).stalkMap
      ⟨actualMap B b F x t c g d E j v hvj w, hV⟩).hom := LocallyRingedSpace.isLocalHomStalkMap _ _
  HironakaG10NfJointLocal.map_targetStalkToJoint_comp_le_jacobson (n := t.embedding.dim+t.rank)
    c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
    (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w hV
    ((targetChartMap B b F x t c g d E j).stalkMap ⟨actualMap B b F x t c g d E j v hvj w, hV⟩).hom

include M in
/-- **`flat_base₀`** at the chart origin, read at `pY w₀ = x` (G10N34's `flat_base_geo`). -/
theorem flat_base₀_canonical (w₀ : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (hproj : HironakaG10NfFibreCover.proj B b F x t c g d E j v hvj w₀.1 = c.point.val)
    (hpY : HironakaG10NfFibreCover.pY B b F x t c g d E j v hvj h0 w₀ = x)
    (J : Ideal (Y.obj.left.presheaf.stalk ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
      (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w₀))))
    (hJ : (quotMap (fibreStalkMap F _ (HironakaG10NfFibreCover.pY B b F x t c g d E j v hvj h0 w₀)
      (HironakaG10NfFibreCover.square B b F x t c g d E j v hvj h0 w₀)) J).Flat) :
    (quotMap (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w₀.1 w₀.2.2.2)
      (Ideal.map ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
        (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w₀)).hom J)).Flat := by
  have hsq : F.hom.left.base x = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
      (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w₀) :=
    (congrArg F.hom.left.base hpY.symm).trans (HironakaG10NfFibreCover.square B b F x t c g d E j v hvj h0 w₀)
  exact HironakaG10GlCanonicalFlatBase.flat_base_geo B b F x t c g d E M j v hvj w₀.1 w₀.2.2.2
    (congrArg Prod.fst hproj) hsq J
    ((HironakaG10NfFlatTransport.fibreStalkMap_congr F hpY
      (HironakaG10NfFibreCover.square B b F x t c g d E j v hvj h0 w₀) hsq J).mp hJ)

include M in
/-- **`spread`** on the canonical chart: a torsion bound by an ideal family `H` locally finitely generated on a
neighbourhood of `pT w₀` spreads to all nearby pairs. -/
theorem spread_canonical
    (H : ∀ Q : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left,
      Ideal ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk Q))
    (V'' : Set (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hfg : HironakaG10HirIdealGerms.IsLocallyFinitelyGeneratedOn
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left V'' H)
    (w₀ : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (hV'' : V'' ∈ 𝓝 (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w₀))
    (h : pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w₀.1 ≤
      Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w₀.1 w₀.2.2.2)
        (H (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w₀))) :
    ∀ᶠ w in 𝓝 w₀, pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1 ≤
      Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2)
        (H (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w)) := by
  have h1 := HironakaG10NfSpreadGerm.eventually_pivotTorsion_le_of_fg c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) h0
    (originalGraph_analytic B b F x t c g d E j v) (actualMap_holomorphic B b F x t c g d E M j v hvj)
    (targetStrict_analytic B b F x t c g d E j) (actual_landing B b F x t c g d E M j v hvj)
    (targetChartMap B b F x t c g d E j) H V'' hfg w₀.1 w₀.2.1 w₀.2.2.2 hV'' h
  have h2 := (continuous_subtype_val.tendsto w₀).eventually h1
  filter_upwards [h2] with w hw
  exact hw w.2.1 w.2.2.2

end

end Hironaka.Analytic.Unibranch.HironakaG10NfGeoFields
