import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Resolution.HironakaG11IntrinsicRegularOpenImmersion
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.LocalAtTarget

/-! Literal relatively compact native restrictions of ORIGINAL reduced spaces.
Finite genuine model images covering compact closure derive countability ONLY
on the given open. Urysohn metrizability then gives actual paracompactness;
paracompactness is not assumed to be open hereditary. Proper inverse opens
retain the SAME native projection/scalars and actual original Reg/Sing loci.
Blueprint first: `original-relatively-compact-restriction.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction
noncomputable section
open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11IntrinsicRegularOpenImmersion
  SourceReducedComplexSpace

variable (X : SourceReducedComplexSpace) (U : Opens X.obj.left)

/-- Compact closure selects finitely many actual ORIGINAL model images. -/
theorem secondCountableTopology (hU : IsCompact (closure (U : Set X.obj.left))) :
    SecondCountableTopology U := by
  classical
  obtain ⟨s,hs⟩ := hU.elim_finite_subcover
    (fun x : X.obj.left => range (LocalEmbedding.ofPoint X x).toPoint)
    (fun x => (LocalEmbedding.ofPoint X x).isOpen_range_toPoint)
    (by intro x _hx; exact mem_iUnion.mpr ⟨x,LocalEmbedding.mem_range_ofPoint X x⟩)
  let I := {x : X.obj.left // x ∈ s}
  let W (i : I) : Set U := (Subtype.val : U → X.obj.left) ⁻¹'
    range (LocalEmbedding.ofPoint X i.val).toPoint
  have hW (i : I) : SecondCountableTopology (W i) := by
    let e := LocalEmbedding.ofPoint X i.val
    let E := e.isOpenEmbedding_toPoint.isEmbedding.toHomeomorph
    let : SecondCountableTopology (range e.toPoint) := E.symm.isEmbedding.secondCountableTopology
    let f : W i → range e.toPoint := fun z => ⟨z.val.val,z.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have he : IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hf continuous_subtype_val
      change IsEmbedding ((Subtype.val : U → X.obj.left) ∘ (Subtype.val : W i → U))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact he.secondCountableTopology
  let : ∀ i : I, SecondCountableTopology (W i) := hW
  apply secondCountableTopology_of_countable_cover
    (fun i : I => (LocalEmbedding.ofPoint X i.val).isOpen_range_toPoint.preimage continuous_subtype_val)
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨i,hi,hix⟩ := mem_iUnion₂.mp (hs (subset_closure x.property))
  exact ⟨⟨i,hi⟩,hix⟩

/-- The actual original para+Hausdorff topology is regular; Urysohn applies ONLY on U. -/
theorem metrizableSpace (hU : IsCompact (closure (U : Set X.obj.left))) : MetrizableSpace U := by
  let : T2Space X.obj.left := X.property.1
  let : ParacompactSpace X.obj.left := X.property.2.1
  let : SecondCountableTopology U := secondCountableTopology X U hU
  infer_instance

/-- A compatible actual metric derives para on U; no false open-heredity shortcut. -/
theorem paracompactSpace (hU : IsCompact (closure (U : Set X.obj.left))) : ParacompactSpace U := by
  let : MetrizableSpace U := metrizableSpace X U hU
  let : MetricSpace U := TopologicalSpace.metrizableSpaceMetric U
  infer_instance

/-- Every actual open restriction has the native original analytic-model clause. -/
theorem restriction_analytic_atlas (x : X.obj.left.restrict U.isOpenEmbedding) :
    ∃ (n : ℕ) (V : Opens (ComplexModel n)) (C : Set V),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ k : (modelOver V C).left ⟶ X.obj.left.restrict U.isOpenEmbedding,
        LocallyRingedSpace.IsOpenImmersion k ∧
        k ≫ (X.obj.left.ofRestrict U.isOpenEmbedding ≫ X.obj.hom) = (modelOver V C).hom ∧
        x ∈ range k.base := by
  obtain ⟨e,⟨c,hc⟩,heU,_hconn⟩ := LocalEmbedding.exists_domain (X := X) x.val U.isOpen x.property
  let I := X.obj.left.ofRestrict U.isOpenEmbedding
  have hI : LocallyRingedSpace.IsOpenImmersion I := by dsimp only [I]; infer_instance
  let : LocallyRingedSpace.IsOpenImmersion I := hI
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  have hr : range e.map.base ⊆ range I.base := by
    rintro _ ⟨a,rfl⟩
    exact ⟨⟨e.toPoint a,heU ⟨a,rfl⟩⟩,rfl⟩
  let k := LocallyRingedSpace.IsOpenImmersion.lift I e.map hr
  have hkI : k ≫ I = e.map := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hk : LocallyRingedSpace.IsOpenImmersion k := by
    let : IsIso (pullback.snd I e.map) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset I e.map hr
    dsimp only [k,LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  refine ⟨e.dim,e.ambient,e.carrier,e.analytic,k,hk,?_,c,?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ X.obj.hom) hkI).trans e.overPoint)
  · exact hI.base_open.injective ((congrArg (fun F => F.base c) hkI).trans hc)

/-- SAME literal raw native restriction and SAME full complex scalar map. -/
@[implicit_reducible]
def restriction (hU : IsCompact (closure (U : Set X.obj.left))) : SourceReducedComplexSpace := by
  let : T2Space X.obj.left := X.property.1
  refine ⟨Over.mk (X.obj.left.ofRestrict U.isOpenEmbedding ≫ X.obj.hom),?_,?_,?_⟩
  · change T2Space U
    infer_instance
  · exact paracompactSpace X U hU
  · exact restriction_analytic_atlas X U

def inclusion (hU : IsCompact (closure (U : Set X.obj.left))) : restriction X U hU ⟶ X :=
  ObjectProperty.homMk (Over.homMk (X.obj.left.ofRestrict U.isOpenEmbedding) rfl)

instance inclusion_isOpenImmersion (hU : IsCompact (closure (U : Set X.obj.left))) :
    LocallyRingedSpace.IsOpenImmersion (inclusion X U hU).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (X.obj.left.ofRestrict U.isOpenEmbedding)
  infer_instance

theorem inclusion_scalar (hU : IsCompact (closure (U : Set X.obj.left))) :
    (inclusion X U hU).hom.left ≫ X.obj.hom = (restriction X U hU).obj.hom := rfl

theorem inclusion_base (hU : IsCompact (closure (U : Set X.obj.left)))
    (x : (restriction X U hU).obj.left) : (inclusion X U hU).hom.left.base x = x.val := rfl

theorem inclusion_range (hU : IsCompact (closure (U : Set X.obj.left))) :
    range (inclusion X U hU).hom.left.base = (U : Set X.obj.left) := Subtype.range_coe

theorem inclusion_preimage_intrinsicRegularLocus (hU : IsCompact (closure (U : Set X.obj.left))) :
    (inclusion X U hU).hom.left.base ⁻¹' intrinsicRegularLocus X.obj =
      intrinsicRegularLocus (restriction X U hU).obj :=
  preimage_intrinsicRegularLocus (inclusion X U hU).hom.left
    (inclusion_isOpenImmersion X U hU) (inclusion_scalar X U hU)

theorem inclusion_preimage_intrinsicSingularLocus (hU : IsCompact (closure (U : Set X.obj.left))) :
    (inclusion X U hU).hom.left.base ⁻¹' intrinsicSingularLocus X.obj =
      intrinsicSingularLocus (restriction X U hU).obj := by
  simp only [intrinsicSingularLocus,preimage_compl,inclusion_preimage_intrinsicRegularLocus X U hU]

variable {X} {Y : SourceReducedComplexSpace} (p : Y ⟶ X)

/-- The actual original inverse-open point set, before any new native object. -/
def preimageOpen : Opens Y.obj.left :=
  ⟨p.hom.left.base ⁻¹' (U : Set X.obj.left),U.isOpen.preimage p.hom.left.base.hom.continuous⟩

theorem isCompact_closure_preimage (hU : IsCompact (closure (U : Set X.obj.left)))
    (hp : IsProperMap p.hom.left.base) : IsCompact (closure (preimageOpen U p : Set Y.obj.left)) := by
  apply (hp.isCompact_preimage hU).of_isClosed_subset isClosed_closure
  exact closure_minimal (by intro y hy; exact (show p.hom.left.base y ∈ closure (U : Set X.obj.left) from subset_closure hy))
    (isClosed_closure.preimage p.hom.left.base.hom.continuous)

/-- The SAME actual inverse-open restriction is an original reduced native object. -/
def preimageRestriction (hU : IsCompact (closure (U : Set X.obj.left)))
    (hp : IsProperMap p.hom.left.base) : SourceReducedComplexSpace :=
  restriction Y (preimageOpen U p) (isCompact_closure_preimage U p hU hp)

/-- The genuine full native target-open lift, with scalar compatibility DERIVED. -/
def restrictionProjection (hU : IsCompact (closure (U : Set X.obj.left)))
    (hp : IsProperMap p.hom.left.base) : preimageRestriction U p hU hp ⟶ restriction X U hU := by
  let I := inclusion X U hU
  let L := inclusion Y (preimageOpen U p) (isCompact_closure_preimage U p hU hp)
  have hr : range (L ≫ p).hom.left.base ⊆ range I.hom.left.base := by
    rintro _ ⟨y,rfl⟩
    exact ⟨⟨p.hom.left.base y.val,y.property⟩,rfl⟩
  let a := LocallyRingedSpace.IsOpenImmersion.lift I.hom.left (L ≫ p).hom.left hr
  have ha : a ≫ I.hom.left = (L ≫ p).hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  apply ObjectProperty.homMk
  refine Over.homMk a ?_
  calc
    _ = a ≫ (I.hom.left ≫ X.obj.hom) := rfl
    _ = (a ≫ I.hom.left) ≫ X.obj.hom := (Category.assoc _ _ _).symm
    _ = (L ≫ p).hom.left ≫ X.obj.hom := congrArg (fun t => t ≫ X.obj.hom) ha
    _ = _ := Over.w (L ≫ p).hom

theorem restrictionProjection_inclusion (hU : IsCompact (closure (U : Set X.obj.left)))
    (hp : IsProperMap p.hom.left.base) :
    restrictionProjection U p hU hp ≫ inclusion X U hU =
      inclusion Y (preimageOpen U p) (isCompact_closure_preimage U p hU hp) ≫ p := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _
    (by rintro _ ⟨y,rfl⟩; exact ⟨⟨p.hom.left.base y.val,y.property⟩,rfl⟩)

theorem restrictionProjection_base (hU : IsCompact (closure (U : Set X.obj.left)))
    (hp : IsProperMap p.hom.left.base) (y : (preimageRestriction U p hU hp).obj.left) :
    ((restrictionProjection U p hU hp).hom.left.base y).val = p.hom.left.base y.val :=
  congrArg (fun F => F.hom.left.base y) (restrictionProjection_inclusion U p hU hp)

/-- Properness is to the actual open U, using the literal inverse-open map. -/
theorem restrictionProjection_isProperMap (hU : IsCompact (closure (U : Set X.obj.left)))
    (hp : IsProperMap p.hom.left.base) : IsProperMap (restrictionProjection U p hU hp).hom.left.base := by
  have hmap : (fun y => (restrictionProjection U p hU hp).hom.left.base y) =
      (U : Set X.obj.left).restrictPreimage p.hom.left.base := by
    funext y
    exact Subtype.ext (restrictionProjection_base U p hU hp y)
  change IsProperMap (fun y => (restrictionProjection U p hU hp).hom.left.base y)
  rw [hmap]
  exact hp.restrictPreimage (U : Set X.obj.left)

end
end Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction
