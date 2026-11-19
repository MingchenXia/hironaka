import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges

/-! Literal intrinsic canonical pivot restrictions, with actual native isomorphisms.
Complete blueprint FIRST. Ordinary caller fixes643 ONCE, then699 on SAME E.
No incoming range/iso/square/normal certificate; empty strict source is retained.
Fixed46907c.5 only: restricted squares/overlaps/Qsat/rawfibre remain separate. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRestrictions
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupExplicitProductCharts CompatibleCanonicalIdealBlowupMonomialLift
  CompatibleCanonicalIdealBlowupPivotOpenRanges
open scoped ProductComplexManifold

noncomputable section

/-- The literal restriction along the intrinsic open's subtype. -/
def literalOpenObject (T : LocallyRingedSpace.{0}) (O : Opens T.toTopCat) :
    LocallyRingedSpace.{0} :=
  T.restrict O.isOpenEmbedding

def literalOpenInclusion (T : LocallyRingedSpace.{0}) (O : Opens T.toTopCat) :
    literalOpenObject T O ⟶ T :=
  T.ofRestrict O.isOpenEmbedding

/-- A genuine native stalk specialization along an actual FULL-map equation.
The direction is T_stalk(fz) -> T_stalk(gz). -/
def nativeEquationTransport {S T : LocallyRingedSpace.{0}}
    (f g : S ⟶ T) (hfg : f = g) (z : S) :
    T.presheaf.stalk (f.base z) ⟶ T.presheaf.stalk (g.base z) :=
  T.presheaf.stalkSpecializes
    (specializes_of_eq (congrArg (fun H : S ⟶ T => H.base z) hfg).symm)

/-- Full equation dictionaries; there is no generator/residue restriction. -/
structure NativeEquationLaws {S T : LocallyRingedSpace.{0}}
    (f g : S ⟶ T) (hfg : f = g) : Prop where
  all_numerators : ∀ (z : S)
    (s : (T.presheaf.stalk (f.base z)).carrier),
    f.stalkMap z s = g.stalkMap z (nativeEquationTransport f g hfg z s)
  whole_ideals : ∀ (z : S)
    (I : Ideal (T.presheaf.stalk (f.base z)).carrier),
    Ideal.map (f.stalkMap z).hom I =
      Ideal.map (g.stalkMap z).hom
        (Ideal.map (nativeEquationTransport f g hfg z).hom I)

/-- Actual Iso data must be Type-valued, not a Prop containing hidden data. -/
structure LiteralOpenChartData {S T : LocallyRingedSpace.{0}}
    (O : Opens T.toTopCat) (k : S ⟶ T) where
  iso : S ≅ literalOpenObject T O
  hom_fac : iso.hom ≫ literalOpenInclusion T O = k
  inv_fac : iso.inv ≫ k = literalOpenInclusion T O

/-- Both actual original structural maps; no alternate complex action. -/
structure LiteralPointLaws {S T : LocallyRingedSpace.{0}}
    {O : Opens T.toTopCat} {k : S ⟶ T}
    (D : LiteralOpenChartData O k)
    (qS : S ⟶ complexPoint) (qT : T ⟶ complexPoint) : Prop where
  hom_point : D.iso.hom ≫ (literalOpenInclusion T O ≫ qT) = qS
  inv_point : D.iso.inv ≫ qS = literalOpenInclusion T O ≫ qT

/-- BOTH full inclusion equations act on EVERY original germ and whole ideal. -/
structure LiteralTransportLaws {S T : LocallyRingedSpace.{0}}
    {O : Opens T.toTopCat} {k : S ⟶ T}
    (D : LiteralOpenChartData O k) : Prop where
  hom_laws : NativeEquationLaws
    (D.iso.hom ≫ literalOpenInclusion T O) k D.hom_fac
  inv_laws : NativeEquationLaws
    (D.iso.inv ≫ k) (literalOpenInclusion T O) D.inv_fac

/-- Transport an original canonical germ to the literal restriction before
applying its full composite native map. The independent coordinate v is an
argument of this generic equation, and is fixed to the REAL geometric coordinate
in the canonical output fields below, never defined as an image. -/
def LiteralNormalEquation {S T : LocallyRingedSpace.{0}}
    {O : Opens T.toTopCat} {k : S ⟶ T}
    (D : LiteralOpenChartData O k) (z : S)
    (s : (T.presheaf.stalk (k.base z)).carrier)
    (v : (S.presheaf.stalk z).carrier) : Prop :=
  (D.iso.hom ≫ literalOpenInclusion T O).stalkMap z
    (nativeEquationTransport k (D.iso.hom ≫ literalOpenInclusion T O)
      D.hom_fac.symm z s) = v

instance literalOpenInclusion_isOpenImmersion (T : LocallyRingedSpace.{0})
    (O : Opens T.toTopCat) :
    LocallyRingedSpace.IsOpenImmersion (literalOpenInclusion T O) := by
  change LocallyRingedSpace.IsOpenImmersion (T.ofRestrict O.isOpenEmbedding)
  exact LocallyRingedSpace.IsOpenImmersion.ofRestrict T O.isOpenEmbedding

private theorem literalOpenInclusion_range (T : LocallyRingedSpace.{0})
    (O : Opens T.toTopCat) : Set.range (literalOpenInclusion T O).base = O.1 := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact u.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

private theorem native_equation_laws {S T : LocallyRingedSpace.{0}}
    (f g : S ⟶ T) (hfg : f = g) : NativeEquationLaws f g hfg := by
  subst g
  constructor
  · intro z s
    simp [nativeEquationTransport]
  · intro z I
    simp [nativeEquationTransport]

/-- The held native OI lifting engine, specialized to a literal intrinsic open. -/
private def constructedLiteralOpenChartData {S T : LocallyRingedSpace.{0}}
    (O : Opens T.toTopCat) (k : S ⟶ T) [LocallyRingedSpace.IsOpenImmersion k]
    (hRange : Set.range k.base = O.1) : LiteralOpenChartData O k := by
  let i := literalOpenInclusion T O
  have hki : Set.range k.base ⊆ Set.range i.base := by
    change Set.range k.base ⊆ Set.range (literalOpenInclusion T O).base
    rw [literalOpenInclusion_range,hRange]
  have hik : Set.range i.base ⊆ Set.range k.base := by
    change Set.range (literalOpenInclusion T O).base ⊆ Set.range k.base
    rw [literalOpenInclusion_range,hRange]
  let a := LocallyRingedSpace.IsOpenImmersion.lift i k hki
  let b := LocallyRingedSpace.IsOpenImmersion.lift k i hik
  have ha : a ≫ i = k := LocallyRingedSpace.IsOpenImmersion.lift_fac i k hki
  have hb : b ≫ k = i := LocallyRingedSpace.IsOpenImmersion.lift_fac k i hik
  exact {
    iso := {
      hom := a
      inv := b
      hom_inv_id := by
        apply (cancel_mono k).mp
        rw [Category.assoc,hb,ha,Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono i).mp
        rw [Category.assoc,ha,hb,Category.id_comp] }
    hom_fac := ha
    inv_fac := hb }

private theorem constructedLiteralPointLaws {S T : LocallyRingedSpace.{0}}
    {O : Opens T.toTopCat} {k : S ⟶ T} (D : LiteralOpenChartData O k)
    (qS : S ⟶ complexPoint) (qT : T ⟶ complexPoint)
    (hk : k ≫ qT = qS) : LiteralPointLaws D qS qT where
  hom_point := by rw [←Category.assoc,D.hom_fac,hk]
  inv_point := by rw [←hk,←Category.assoc,D.inv_fac]

private theorem constructedLiteralTransportLaws {S T : LocallyRingedSpace.{0}}
    {O : Opens T.toTopCat} {k : S ⟶ T} (D : LiteralOpenChartData O k) :
    LiteralTransportLaws D where
  hom_laws := native_equation_laws _ _ D.hom_fac
  inv_laws := native_equation_laws _ _ D.inv_fac

private theorem constructedLiteralNormalEquation {S T : LocallyRingedSpace.{0}}
    {O : Opens T.toTopCat} {k : S ⟶ T} (D : LiteralOpenChartData O k) (z : S)
    (s : (T.presheaf.stalk (k.base z)).carrier)
    (v : (S.presheaf.stalk z).carrier) (h : k.stalkMap z s = v) :
    LiteralNormalEquation D z s v :=
  ((native_equation_laws k (D.iso.hom ≫ literalOpenInclusion T O)
    D.hom_fac.symm).all_numerators z s).symm.trans h

section SameCanonical
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

/-- This is literally the old strict-j LRS already used by699, not a copy. -/
abbrev targetStrictChartObject (j : Fin t.rank) : LocallyRingedSpace.{0} :=
  actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
    (strictChartCarrier E.target.charts (targetGraphSet B b t) j)

abbrev sourceStrictChartObject (j : Fin t.rank) : LocallyRingedSpace.{0} :=
  actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
    (strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j)

def targetPivotRestriction (j : Fin t.rank) : LocallyRingedSpace.{0} :=
  literalOpenObject (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left
    (targetPivotOpen B b F x t c g d E j)

def sourcePivotRestriction (j : Fin t.rank) : LocallyRingedSpace.{0} :=
  literalOpenObject
    (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left
    (sourcePivotOpen B b F x t c g d E j)

def targetPivotInclusion (j : Fin t.rank) :
    targetPivotRestriction B b F x t c g d E j ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  literalOpenInclusion (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left
    (targetPivotOpen B b F x t c g d E j)

def sourcePivotInclusion (j : Fin t.rank) :
    sourcePivotRestriction B b F x t c g d E j ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject
        (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left :=
  literalOpenInclusion
    (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left
    (sourcePivotOpen B b F x t c g d E j)

/-- SAME actual canonical maps/ranges; these abbreviations add no new object. -/
abbrev TargetLiteralData (j : Fin t.rank) :=
  LiteralOpenChartData
    (S := targetStrictChartObject B b F x t c g d E j)
    (targetPivotOpen B b F x t c g d E j)
    (targetChartMap B b F x t c g d E j)

abbrev SourceLiteralData (j : Fin t.rank) :=
  LiteralOpenChartData
    (S := sourceStrictChartObject B b F x t c g d E j)
    (sourcePivotOpen B b F x t c g d E j)
    (sourceChartMap B b F x t c g d E j)

/-- Named complete proof predicates avoid repeated dependent object inference. -/
def TargetLiteralPointLaws (D : ∀ j : Fin t.rank, TargetLiteralData B b F x t c g d E j) : Prop :=
  ∀ j : Fin t.rank, LiteralPointLaws (D j)
    (subspacePointMap (n := t.embedding.dim+t.rank)
      (strictChartCarrier E.target.charts (targetGraphSet B b t) j))
    (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom

def SourceLiteralPointLaws (D : ∀ j : Fin t.rank, SourceLiteralData B b F x t c g d E j) : Prop :=
  ∀ j : Fin t.rank, LiteralPointLaws (D j)
    (subspacePointMap (n := c.embedding.dim+t.rank)
      (strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j))
    (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.hom

def TargetLiteralTransportLaws (D : ∀ j : Fin t.rank, TargetLiteralData B b F x t c g d E j) : Prop :=
  ∀ j : Fin t.rank, LiteralTransportLaws (D j)

def SourceLiteralTransportLaws (D : ∀ j : Fin t.rank, SourceLiteralData B b F x t c g d E j) : Prop :=
  ∀ j : Fin t.rank, LiteralTransportLaws (D j)

def TargetLiteralNormalLaws (D : ∀ j : Fin t.rank, TargetLiteralData B b F x t c g d E j) : Prop :=
  ∀ (j i : Fin t.rank) (z : strictChartCarrier E.target.charts (targetGraphSet B b t) j),
    LiteralNormalEquation
      (S := targetStrictChartObject B b F x t c g d E j)
      (T := (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
      (D j) z (targetSectionGerm B b F x t c g d E j i z)
      ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).stalkMap z
        (targetCoordinateClass B b F x t c g d E j i z))

def SourceLiteralNormalLaws (D : ∀ j : Fin t.rank, SourceLiteralData B b F x t c g d E j) : Prop :=
  ∀ (j i : Fin t.rank) (z : strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j),
    LiteralNormalEquation
      (S := sourceStrictChartObject B b F x t c g d E j)
      (T := (OriginalFiniteIdealGeometricBlowup.sourceObject
        (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left)
      (D j) z (sourceSectionGerm B b F x t c g d E j i z)
      ((strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j).stalkMap z
        (sourceCoordinateClass B b F x t c g d E j i z))

/-- Type-valued full output on the already-derived E, not an incoming packet. -/
structure SameCanonicalPivotLiteralRestrictionData where
  target : ∀ j : Fin t.rank, TargetLiteralData B b F x t c g d E j
  source : ∀ j : Fin t.rank, SourceLiteralData B b F x t c g d E j
  target_point : TargetLiteralPointLaws B b F x t c g d E target
  source_point : SourceLiteralPointLaws B b F x t c g d E source
  target_transport : TargetLiteralTransportLaws B b F x t c g d E target
  source_transport : SourceLiteralTransportLaws B b F x t c g d E source
  target_normal : TargetLiteralNormalLaws B b F x t c g d E target
  source_normal : SourceLiteralNormalLaws B b F x t c g d E source

theorem pivot_literal_restrictions_of_models :
    Nonempty (SameCanonicalPivotLiteralRestrictionData B b F x t c g d E) := by
  classical
  obtain ⟨P⟩ := pivot_chart_ranges_of_models B b F x t c g d E
  let DT (j : Fin t.rank) : TargetLiteralData B b F x t c g d E j :=
    constructedLiteralOpenChartData (targetPivotOpen B b F x t c g d E j)
      (targetChartMap B b F x t c g d E j) (P.target_range j)
  let DS (j : Fin t.rank) : SourceLiteralData B b F x t c g d E j :=
    constructedLiteralOpenChartData (sourcePivotOpen B b F x t c g d E j)
      (sourceChartMap B b F x t c g d E j) (P.source_range j)
  refine ⟨{
    target := DT
    source := DS
    target_point := ?_
    source_point := ?_
    target_transport := fun j => constructedLiteralTransportLaws (DT j)
    source_transport := fun j => constructedLiteralTransportLaws (DS j)
    target_normal := ?_
    source_normal := ?_ }⟩
  · intro j
    exact constructedLiteralPointLaws (DT j) _ _ (P.target_native.scalar j)
  · intro j
    exact constructedLiteralPointLaws (DS j) _ _ (P.source_native.scalar j)
  · intro j i z
    exact constructedLiteralNormalEquation (DT j) z _ _ (P.target_normals.normal j i z)
  · intro j i z
    exact constructedLiteralNormalEquation (DS j) z _ _ (P.source_normals.normal j i z)

end SameCanonical

section OrdinaryCaller
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

theorem exists_same_canonical_pivot_open_restrictions
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y)
      (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c)
      (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d)
      (_M : AllAmbientMonomialLiftData B b F x t c g d E),
      Nonempty (SameCanonicalPivotLiteralRestrictionData B b F x t c g d E) := by
  obtain ⟨t,c,g,d,E,⟨M⟩⟩ := exists_same_canonical_allambient_monomial_lift B b F x y hxy
  exact ⟨t,c,g,d,E,M,pivot_literal_restrictions_of_models B b F x t c g d E⟩

end OrdinaryCaller
end

end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRestrictions
