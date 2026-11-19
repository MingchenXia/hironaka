import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotSquare
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction

/-! FULL original conjugacy of the SAME actual restricted pivot map.
Approved complete blueprint FIRST; ordinary643 ONCE -> C1/B model SAME E.
Two FULL native Mono cancellations, original/inverse-chart/scalar/projection
squares and EVERY native numerator/whole-ideal/whole representative formula.
No incoming comparison packet or rawpair source point. C3/.7overlap/Qsat/raw
fibre remain separate. Nominal output definitions get zero engine credit. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotMonomialConjugacy
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates BlowupStrictSubmanifold
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk
  SourceReducedComplexSpace EmbeddedGeometricBlowup OriginalFiniteIdealGraphChart
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupExplicitProductCharts CompatibleCanonicalIdealBlowupMonomialLift
  CompatibleCanonicalIdealBlowupPivotOpenRanges CompatibleCanonicalIdealBlowupPivotOpenRestrictions
  CompatibleCanonicalIdealBlowupOriginalPivotObjects
  CompatibleCanonicalIdealBlowupOriginalPivotSquare CompatibleCanonicalIdealBlowupMonomialStrictRestriction
open scoped ProductComplexManifold

noncomputable section
section GenericWholeTransport
variable {n m : ℕ} {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
  [ChartedSpace (ComplexModel n) S] [IsComplexManifold n S]
  [ChartedSpace (ComplexModel m) T] [IsComplexManifold m T]

structure ConjugatedWholeStalkLaws (f : S → T)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (C : Set S) (D : Set T) (hCD : ∀ x ∈ C, f x ∈ D)
    (k : actualSubspaceLocallyRingedSpace (n := n) C ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hk : k = actualSubspaceMap hf hCD) : Prop where
  equation : ∀ (z : C)
    (r : actualComplexStructureStalk (n := m) (f z.val)),
    actualSubspaceStalkWholeEquiv (n := n) C z
      (k.stalkMap z
        (nativeEquationTransport (actualSubspaceMap hf hCD) k hk.symm z
          ((actualSubspaceInclusion (n := m) D).stalkMap
            (actualSubspaceMapTop hf hCD z) r))) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) z.val)
        ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap z.val r)

private theorem constructedConjugatedWholeStalkLaws (f : S → T)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (C : Set S) (D : Set T) (hCD : ∀ x ∈ C, f x ∈ D)
    (W : WholeNativeStalkLaws f hf C D hCD)
    (k : actualSubspaceLocallyRingedSpace (n := n) C ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hk : k = actualSubspaceMap hf hCD) :
    ConjugatedWholeStalkLaws f hf C D hCD k hk := by
  subst k
  constructor
  intro z r
  simpa [nativeEquationTransport] using W.equation z r
end GenericWholeTransport

private theorem nativeEquationLaws_of_eq {S T : LocallyRingedSpace.{0}}
    (f g : S ⟶ T) (hfg : f = g) : NativeEquationLaws f g hfg := by
  subst g
  constructor
  · intro z r
    simp [nativeEquationTransport]
  · intro z I
    simp [nativeEquationTransport]

-- The same categorical algebra, proved FIRST with abstract typed objects.
-- Actual geometric producer supplies every premise from the held mothers.
private theorem nativeMonoDiagram {C : Type*} [Category C]
    {A B X Y U V P Q : C}
    (h : A ⟶ B) (iX : A ⟶ X) (iY : B ⟶ Y)
    (qX : X ⟶ P) (qY : Y ⟶ Q) [Mono qY]
    (qXj : A ⟶ U) (qYj : B ⟶ V) (uX : U ⟶ P) (uY : V ⟶ Q)
    (Lj : U ⟶ V) (L : P ⟶ Q) (H : X ⟶ Y)
    (hy : iY ≫ qY = qYj ≫ uY) (hx : iX ≫ qX = qXj ≫ uX)
    (hl : h ≫ qYj = qXj ≫ Lj) (hm : Lj ≫ uY = uX ≫ L)
    (hH : H ≫ qY = qX ≫ L) : h ≫ iY = iX ≫ H := by
  apply (cancel_mono qY).mp
  calc
    (h ≫ iY) ≫ qY = h ≫ (iY ≫ qY) := Category.assoc h iY qY
    _ = h ≫ (qYj ≫ uY) := congrArg (fun a => h ≫ a) hy
    _ = (h ≫ qYj) ≫ uY := (Category.assoc h qYj uY).symm
    _ = (qXj ≫ Lj) ≫ uY := congrArg (fun a => a ≫ uY) hl
    _ = qXj ≫ (Lj ≫ uY) := Category.assoc qXj Lj uY
    _ = qXj ≫ (uX ≫ L) := congrArg (fun a => qXj ≫ a) hm
    _ = (qXj ≫ uX) ≫ L := (Category.assoc qXj uX L).symm
    _ = (iX ≫ qX) ≫ L := congrArg (fun a => a ≫ L) hx.symm
    _ = iX ≫ (qX ≫ L) := Category.assoc iX qX L
    _ = iX ≫ (H ≫ qY) := congrArg (fun a => iX ≫ a) hH.symm
    _ = (iX ≫ H) ≫ qY := (Category.assoc iX H qY).symm

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

-- Exact OLD whole strict-subspace inclusions. These definitions do not use E;
-- their inferred arities are respectively B,b,t and B,b,F,x,t,c. No new sheaf.
def targetWholeAmbientInclusion :
    (explicitTarget B b t).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))
        (BlowupSpace (t.embedding.dim+t.rank)
          {q : t.domain × ComplexModel t.rank | q.2=0}) :=
  actualSubspaceInclusion (n := t.embedding.dim+t.rank)
    (actualStrictCarrier (n := t.embedding.dim) (targetGraphSet B b t))

def sourceWholeAmbientInclusion :
    (explicitSource B b F x t c).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
        (BlowupSpace (c.embedding.dim+t.rank)
          {q : c.subdomain × ComplexModel t.rank | q.2=0}) :=
  actualSubspaceInclusion (n := c.embedding.dim+t.rank)
    (actualStrictCarrier (n := c.embedding.dim) (sourceGraphSet B b F x t c))

def targetChartAmbientMap (j : Fin t.rank) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))
      (productChartOpen E.target.charts j) ⟶
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))
      (BlowupSpace (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0}) :=
  ChartedSpace.locallyRingedSpaceMap
    (IM := 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)))
    (IN := 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)))
    (Subtype.val : productChartOpen E.target.charts j →
      BlowupSpace (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0})
    contMDiff_subtype_val

def sourceChartAmbientMap (j : Fin t.rank) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
      (productChartOpen E.source.charts j) ⟶
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
      (BlowupSpace (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0}) :=
  ChartedSpace.locallyRingedSpaceMap
    (IM := 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)))
    (IN := 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)))
    (Subtype.val : productChartOpen E.source.charts j →
      BlowupSpace (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0})
    contMDiff_subtype_val

-- Derived actual-chart/global-ambient equations, not caller inputs.
theorem target_strict_chart_ambient (j : Fin t.rank) :
    (targetStrictInclusion B b F x t c g d E j).hom.left ≫
        targetWholeAmbientInclusion B b t =
      targetChartAmbientInclusion B b F x t c g d E j ≫
        targetChartAmbientMap B b F x t c g d E j := by
  exact (actualSubspaceMap_inclusion
    (n := t.embedding.dim+t.rank) (m := t.embedding.dim+t.rank)
    (M := productChartOpen E.target.charts j)
    (N := BlowupSpace (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0})
    (f := (Subtype.val : productChartOpen E.target.charts j → _))
    (C := targetStrictSet B b F x t c g d E j)
    (D := actualStrictCarrier (n := t.embedding.dim) (targetGraphSet B b t))
    contMDiff_subtype_val (fun _ hx => hx)).symm

theorem source_strict_chart_ambient (j : Fin t.rank) :
    (sourceStrictInclusion B b F x t c g d E j).hom.left ≫
        sourceWholeAmbientInclusion B b F x t c =
      sourceChartAmbientInclusion B b F x t c g d E j ≫
        sourceChartAmbientMap B b F x t c g d E j := by
  exact (actualSubspaceMap_inclusion
    (n := c.embedding.dim+t.rank) (m := c.embedding.dim+t.rank)
    (M := productChartOpen E.source.charts j)
    (N := BlowupSpace (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0})
    (f := (Subtype.val : productChartOpen E.source.charts j → _))
    (C := sourceStrictSet B b F x t c g d E j)
    (D := actualStrictCarrier (n := c.embedding.dim) (sourceGraphSet B b F x t c))
    contMDiff_subtype_val (fun _ hx => hx)).symm

theorem monomial_full_strict_square
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    actualOriginalMonomialStrictMap B b F x t c g d E M j ≫
        targetStrictInclusion B b F x t c g d E j =
      sourceStrictInclusion B b F x t c g d E j ≫
        explicitStrictMap B b F x t c g E.target E.source := by
  let SChart := (sourceStrictOriginal B b F x t c g d E j).obj.left
  let TChart := (targetStrictOriginal B b F x t c g d E j).obj.left
  let SGlobal := (explicitSource B b F x t c).obj.left
  let TGlobal := (explicitTarget B b t).obj.left
  let SAmb := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
    (productChartOpen E.source.charts j)
  let TAmb := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))
    (productChartOpen E.target.charts j)
  let SBlow := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
    (BlowupSpace (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0})
  let TBlow := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))
    (BlowupSpace (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0})
  let h : SChart ⟶ TChart := (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left
  let iY : TChart ⟶ TGlobal := (targetStrictInclusion B b F x t c g d E j).hom.left
  let iX : SChart ⟶ SGlobal := (sourceStrictInclusion B b F x t c g d E j).hom.left
  let qY : TGlobal ⟶ TBlow := targetWholeAmbientInclusion B b t
  let qX : SGlobal ⟶ SBlow := sourceWholeAmbientInclusion B b F x t c
  let uY : TAmb ⟶ TBlow := targetChartAmbientMap B b F x t c g d E j
  let uX : SAmb ⟶ SBlow := sourceChartAmbientMap B b F x t c g d E j
  let qYj : TChart ⟶ TAmb := targetChartAmbientInclusion B b F x t c g d E j
  let qXj : SChart ⟶ SAmb := sourceChartAmbientInclusion B b F x t c g d E j
  let Lj : SAmb ⟶ TAmb := nativeMonomialAmbientMap B b F x t c g d E j
  let L : SBlow ⟶ TBlow := ChartedSpace.locallyRingedSpaceMap
    (explicitAmbientLift B b F x t c g E.target E.source) E.square.holomorphic
  let H : SGlobal ⟶ TGlobal := (explicitStrictMap B b F x t c g E.target E.source).hom.left
  let : Mono qY := by
    change Mono (actualSubspaceInclusion (n := t.embedding.dim+t.rank)
      (actualStrictCarrier (n := t.embedding.dim) (targetGraphSet B b t)))
    infer_instance
  have hy : iY ≫ qY = qYj ≫ uY := target_strict_chart_ambient B b F x t c g d E j
  have hx : iX ≫ qX = qXj ≫ uX := source_strict_chart_ambient B b F x t c g d E j
  have hl : h ≫ qYj = qXj ≫ Lj := monomial_strict_full_ambient B b F x t c g d E M j
  have hm : Lj ≫ uY = uX ≫ L := M.inclusion_square j
  have hH : H ≫ qY = qX ≫ L := E.square.ambient_inclusion
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change h ≫ iY = iX ≫ H
  exact nativeMonoDiagram
    (A := SChart) (B := TChart) (X := SGlobal) (Y := TGlobal)
    (U := SAmb) (V := TAmb) (P := SBlow) (Q := TBlow)
    h iX iY qX qY qXj qYj uX uY Lj L H hy hx hl hm hH

-- Q is an ACTUAL output of the held B MODEL theorem on this same E. The
-- ordinary producer below constructs Q internally; it is not an input there.
def conjugatedPivotMap (Q : OriginalPivotSquareData B b F x t c g d E)
    (j : Fin t.rank) :
    sourceStrictOriginal B b F x t c g d E j ⟶
      targetStrictOriginal B b F x t c g d E j :=
  (Q.objects.source_iso j).hom ≫ Q.restricted_map j ≫ (Q.objects.target_iso j).inv

private theorem constructedForward
    (M : AllAmbientMonomialLiftData B b F x t c g d E)
    (Q : OriginalPivotSquareData B b F x t c g d E) (j : Fin t.rank) :
    (Q.objects.source_iso j).hom ≫ Q.restricted_map j =
      actualOriginalMonomialStrictMap B b F x t c g d E M j ≫ (Q.objects.target_iso j).hom := by
  let aX := (Q.objects.source_iso j).hom
  let aY := (Q.objects.target_iso j).hom
  let jX := sourceOriginalInclusion B b F x t c g d E Q.objects.properties j
  let jY := targetOriginalInclusion B b F x t c g d E Q.objects.properties j
  let iX := sourceStrictInclusion B b F x t c g d E j
  let iY := targetStrictInclusion B b F x t c g d E j
  let KX := sourceCanonicalMap B b F x t c g E.source
  let KY := targetCanonicalMap B b t E.target
  let H := explicitStrictMap B b F x t c g E.target E.source
  let h := actualOriginalMonomialStrictMap B b F x t c g d E M j
  let Fj := Q.restricted_map j
  let Fp := OriginalFiniteIdealBlowupSquare.inducedMorphism B b F
  have hX : aX ≫ jX = iX ≫ KX := source_original_iso_inclusion B b F x t c g d E Q.objects j
  have hY : aY ≫ jY = iY ≫ KY := target_original_iso_inclusion B b F x t c g d E Q.objects j
  have hf : Fj ≫ jY = jX ≫ Fp := Q.canonical_square j
  have he : KX ≫ Fp = H ≫ KY := E.square.canonical_square
  have hs : h ≫ iY = iX ≫ H := monomial_full_strict_square B b F x t c g d E M j
  have hc : (aX ≫ Fj) ≫ jY = (h ≫ aY) ≫ jY := by
    calc
      (aX ≫ Fj) ≫ jY = aX ≫ (Fj ≫ jY) := Category.assoc aX Fj jY
      _ = aX ≫ (jX ≫ Fp) := congrArg (fun a => aX ≫ a) hf
      _ = (aX ≫ jX) ≫ Fp := (Category.assoc aX jX Fp).symm
      _ = (iX ≫ KX) ≫ Fp := congrArg (fun a => a ≫ Fp) hX
      _ = iX ≫ (KX ≫ Fp) := Category.assoc iX KX Fp
      _ = iX ≫ (H ≫ KY) := congrArg (fun a => iX ≫ a) he
      _ = (iX ≫ H) ≫ KY := (Category.assoc iX H KY).symm
      _ = (h ≫ iY) ≫ KY := congrArg (fun a => a ≫ KY) hs.symm
      _ = h ≫ (iY ≫ KY) := Category.assoc h iY KY
      _ = h ≫ (aY ≫ jY) := congrArg (fun a => h ≫ a) hY.symm
      _ = (h ≫ aY) ≫ jY := (Category.assoc h aY jY).symm
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (targetPivotInclusion B b F x t c g d E j)).mp
  exact congrArg (fun a => a.hom.left) hc

-- Exact named output assertions prevent repeated giant dependent-field conversion.
def StrictSquareLaws
    (M : AllAmbientMonomialLiftData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    actualOriginalMonomialStrictMap B b F x t c g d E M j ≫
        targetStrictInclusion B b F x t c g d E j =
      sourceStrictInclusion B b F x t c g d E j ≫
        explicitStrictMap B b F x t c g E.target E.source

def StrictProjectionLaws
    (M : AllAmbientMonomialLiftData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    actualOriginalMonomialStrictMap B b F x t c g d E M j ≫
        targetStrictInclusion B b F x t c g d E j ≫
        geometricProjectionMorphism
          (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic =
      sourceStrictInclusion B b F x t c g d E j ≫
        geometricProjectionMorphism
          (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic ≫
        graphNormalMorphism c.baseMap c.holomorphic t.functions
          ((Subtype.val : c.subdomain → c.domain) ⁻¹'
            ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier))
          ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
          c.landing c.analytic t.analytic

def ForwardConjugacyLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    (Q.objects.source_iso j).hom ≫ Q.restricted_map j =
      actualOriginalMonomialStrictMap B b F x t c g d E M j ≫
        (Q.objects.target_iso j).hom

def InverseConjugacyLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    Q.restricted_map j ≫ (Q.objects.target_iso j).inv =
      (Q.objects.source_iso j).inv ≫
        actualOriginalMonomialStrictMap B b F x t c g d E M j

def ConjugatedMapLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    conjugatedPivotMap B b F x t c g d E Q j =
      actualOriginalMonomialStrictMap B b F x t c g d E M j

def NativeFactoryLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    (conjugatedPivotMap B b F x t c g d E Q j).hom.left =
      actualSubspaceMap (M.restricted_holomorphic j)
        (monomial_strict_landing B b F x t c g d E M j)

def ForwardNativeLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E)
    (hf : ForwardConjugacyLaws B b F x t c g d E Q M) : Prop :=
  ∀ j : Fin t.rank,
    NativeEquationLaws
      (((Q.objects.source_iso j).hom ≫ Q.restricted_map j).hom.left)
      ((actualOriginalMonomialStrictMap B b F x t c g d E M j ≫
        (Q.objects.target_iso j).hom).hom.left)
      (congrArg (fun k => k.hom.left) (hf j))

def InverseNativeLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E)
    (hi : InverseConjugacyLaws B b F x t c g d E Q M) : Prop :=
  ∀ j : Fin t.rank,
    NativeEquationLaws
      ((Q.restricted_map j ≫ (Q.objects.target_iso j).inv).hom.left)
      (((Q.objects.source_iso j).inv ≫
        actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left)
      (congrArg (fun k => k.hom.left) (hi j))

def WholeNativeLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E)
    (hn : NativeFactoryLaws B b F x t c g d E Q M) : Prop :=
  ∀ j : Fin t.rank,
    NativeEquationLaws
      ((conjugatedPivotMap B b F x t c g d E Q j).hom.left)
      (actualSubspaceMap (M.restricted_holomorphic j)
        (monomial_strict_landing B b F x t c g d E M j))
      (hn j)

def WholeRepresentativeLaws
    (Q : OriginalPivotSquareData B b F x t c g d E)
    (M : AllAmbientMonomialLiftData B b F x t c g d E)
    (hn : NativeFactoryLaws B b F x t c g d E Q M) : Prop :=
  ∀ j : Fin t.rank,
    ConjugatedWholeStalkLaws
      (n := c.embedding.dim+t.rank) (m := t.embedding.dim+t.rank)
      (S := productChartOpen E.source.charts j) (T := productChartOpen E.target.charts j)
      (monomialAmbientFunction B b F x t c g d E j) (M.restricted_holomorphic j)
      (sourceStrictSet B b F x t c g d E j) (targetStrictSet B b F x t c g d E j)
      (monomial_strict_landing B b F x t c g d E M j)
      ((conjugatedPivotMap B b F x t c g d E Q j).hom.left)
      (hn j)

def ForwardScalarLaws
    (Q : OriginalPivotSquareData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    (((Q.objects.source_iso j).hom ≫ Q.restricted_map j).hom.left) ≫
        (targetOriginalPivot B b F x t c g d E Q.objects.properties j).obj.hom =
      (sourceStrictOriginal B b F x t c g d E j).obj.hom

def InverseScalarLaws
    (Q : OriginalPivotSquareData B b F x t c g d E) : Prop :=
  ∀ j : Fin t.rank,
    ((Q.restricted_map j ≫ (Q.objects.target_iso j).inv).hom.left) ≫
        (targetStrictOriginal B b F x t c g d E j).obj.hom =
      (sourceOriginalPivot B b F x t c g d E Q.objects.properties j).obj.hom

structure PivotMonomialConjugacyData
    (M : AllAmbientMonomialLiftData B b F x t c g d E) where
  canonical : OriginalPivotSquareData B b F x t c g d E
  strict_laws : MonomialStrictRestrictionLaws B b F x t c g d E M
  strict_square : StrictSquareLaws B b F x t c g d E M
  strict_projection : StrictProjectionLaws B b F x t c g d E M
  forward : ForwardConjugacyLaws B b F x t c g d E canonical M
  inverse : InverseConjugacyLaws B b F x t c g d E canonical M
  conjugated : ConjugatedMapLaws B b F x t c g d E canonical M
  native_factory_eq : NativeFactoryLaws B b F x t c g d E canonical M
  forward_transport : ForwardNativeLaws B b F x t c g d E canonical M forward
  inverse_transport : InverseNativeLaws B b F x t c g d E canonical M inverse
  whole_transport : WholeNativeLaws B b F x t c g d E canonical M native_factory_eq
  whole_stalk : WholeRepresentativeLaws B b F x t c g d E canonical M native_factory_eq
  forward_scalar : ForwardScalarLaws B b F x t c g d E canonical
  inverse_scalar : InverseScalarLaws B b F x t c g d E canonical

theorem pivot_monomial_conjugacy_of_models
    (M : AllAmbientMonomialLiftData B b F x t c g d E) :
    Nonempty (PivotMonomialConjugacyData B b F x t c g d E M) := by
  obtain ⟨Q⟩ := original_pivot_square_of_models B b F x t c g d E
  let W := monomial_strict_restriction_of_models B b F x t c g d E M
  have hf (j : Fin t.rank) :
      (Q.objects.source_iso j).hom ≫ Q.restricted_map j =
        actualOriginalMonomialStrictMap B b F x t c g d E M j ≫ (Q.objects.target_iso j).hom :=
    constructedForward B b F x t c g d E M Q j
  have hi (j : Fin t.rank) :
      Q.restricted_map j ≫ (Q.objects.target_iso j).inv =
        (Q.objects.source_iso j).inv ≫ actualOriginalMonomialStrictMap B b F x t c g d E M j := by
    apply (cancel_epi (Q.objects.source_iso j).hom).mp
    calc
      _ = ((Q.objects.source_iso j).hom ≫ Q.restricted_map j) ≫ (Q.objects.target_iso j).inv :=
        (Category.assoc _ _ _).symm
      _ = (actualOriginalMonomialStrictMap B b F x t c g d E M j ≫
          (Q.objects.target_iso j).hom) ≫ (Q.objects.target_iso j).inv :=
        congrArg (fun a => a ≫ (Q.objects.target_iso j).inv) (hf j)
      _ = actualOriginalMonomialStrictMap B b F x t c g d E M j := by
        rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
      _ = _ := by rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  have hk (j : Fin t.rank) : conjugatedPivotMap B b F x t c g d E Q j =
      actualOriginalMonomialStrictMap B b F x t c g d E M j := by
    unfold conjugatedPivotMap
    rw [← Category.assoc,hf,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hn (j : Fin t.rank) : (conjugatedPivotMap B b F x t c g d E Q j).hom.left =
      actualSubspaceMap (M.restricted_holomorphic j) (monomial_strict_landing B b F x t c g d E M j) :=
    congrArg (fun a => a.hom.left) (hk j)
  have hp (j : Fin t.rank) :
      actualOriginalMonomialStrictMap B b F x t c g d E M j ≫
          targetStrictInclusion B b F x t c g d E j ≫
          geometricProjectionMorphism
            (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic =
        sourceStrictInclusion B b F x t c g d E j ≫
          geometricProjectionMorphism
            (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic ≫
          graphNormalMorphism c.baseMap c.holomorphic t.functions
            ((Subtype.val : c.subdomain → c.domain) ⁻¹'
              ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier))
            ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
            c.landing c.analytic t.analytic := by
    rw [← Category.assoc,monomial_full_strict_square,Category.assoc,E.square.strict_projection]
  exact ⟨{
    canonical := Q
    strict_laws := W
    strict_square := monomial_full_strict_square B b F x t c g d E M
    strict_projection := hp
    forward := hf
    inverse := hi
    conjugated := hk
    native_factory_eq := hn
    forward_transport := fun j => nativeEquationLaws_of_eq _ _
      (congrArg (fun a => a.hom.left) (hf j))
    inverse_transport := fun j => nativeEquationLaws_of_eq _ _
      (congrArg (fun a => a.hom.left) (hi j))
    whole_transport := fun j => nativeEquationLaws_of_eq _ _ (hn j)
    whole_stalk := fun j => constructedConjugatedWholeStalkLaws
      (n := c.embedding.dim+t.rank) (m := t.embedding.dim+t.rank)
      (S := productChartOpen E.source.charts j) (T := productChartOpen E.target.charts j)
      (monomialAmbientFunction B b F x t c g d E j) (M.restricted_holomorphic j)
      (sourceStrictSet B b F x t c g d E j) (targetStrictSet B b F x t c g d E j)
      (monomial_strict_landing B b F x t c g d E M j) (W.whole_stalk_mk j)
      ((conjugatedPivotMap B b F x t c g d E Q j).hom.left) (hn j)
    forward_scalar := fun j => Over.w ((Q.objects.source_iso j).hom ≫ Q.restricted_map j).hom
    inverse_scalar := fun j => Over.w (Q.restricted_map j ≫ (Q.objects.target_iso j).inv).hom }⟩
end SameCanonical

section OrdinaryCaller
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

theorem exists_same_canonical_pivot_monomial_conjugacy
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y)
      (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c)
      (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d)
      (M : AllAmbientMonomialLiftData B b F x t c g d E),
      Nonempty (PivotMonomialConjugacyData B b F x t c g d E M) := by
  obtain ⟨t,c,g,d,E,⟨M⟩⟩ := exists_same_canonical_allambient_monomial_lift B b F x y hxy
  exact ⟨t,c,g,d,E,M,pivot_monomial_conjugacy_of_models B b F x t c g d E M⟩
end OrdinaryCaller
end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotMonomialConjugacy
