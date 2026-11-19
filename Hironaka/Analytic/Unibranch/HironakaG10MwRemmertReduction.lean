import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular
import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspace
import Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlap

/-!
# Native Remmert, item 5.0: reduction to the core (lane G10MW)

**`nativeProperImage_of_core : NativeProperImageCore → NativeProperImage`.**  For `f : Y ⟶ X` proper on an
analytic `P`: pass to the reduced closed subspace on `P` (`OriginalAnalyticClosedSubspace`), on which `f` is
proper; near `x ∈ X` take a local embedding `e` whose image `V` has compact closure, restrict the source to
`f⁻¹ V` (`OriginalRelativelyCompactRestriction`: second countable, of bounded dimension
`exists_nativeDimLE_restriction`), and lift to a proper native morphism into `(C_e, 𝒪/𝓘)` (`liftNative`); the
core makes its image analytic in the ambient manifold of `e`, which is the trace of `f(P)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10MwRemmertReduction

open Hironaka Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus AnalyticDimensionBasics
  SourceReducedComplexSpace HironakaG10EpNativeDim Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular

noncomputable section

/-- Native reduced complex spaces are locally compact. -/
theorem locallyCompactSpace (X : SourceReducedComplexSpace) : LocallyCompactSpace X.obj.left := by
  let : T2Space X.obj.left := X.property.1
  have : WeaklyLocallyCompactSpace X.obj.left := by
    refine ⟨fun x => ?_⟩
    let e := LocalEmbedding.ofPoint X x
    obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint X x
    let : LocallyCompactSpace e.ambient := e.ambient.isOpen.locallyCompactSpace
    let : LocallyCompactSpace e.carrier := e.analytic.isClosed.locallyCompactSpace
    obtain ⟨L, hL, hcL⟩ := exists_compact_mem_nhds c
    refine ⟨e.toPoint '' L, hL.image e.isOpenEmbedding_toPoint.continuous, ?_⟩
    rw [← hc]
    exact e.isOpenEmbedding_toPoint.image_mem_nhds.mpr hcL
  infer_instance

/-- Lift of a native morphism through a native open immersion containing its image. -/
def liftNative {A Z X : SourceReducedComplexSpace} (j : A ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j.hom.left] (g : Z ⟶ X)
    (h : range g.hom.left.base ⊆ range j.hom.left.base) : Z ⟶ A := by
  let a := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left g.hom.left h
  have ha : a ≫ j.hom.left = g.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ h
  apply ObjectProperty.homMk
  refine Over.homMk a ?_
  calc
    _ = a ≫ (j.hom.left ≫ X.obj.hom) := by rw [Over.w j.hom]
    _ = (a ≫ j.hom.left) ≫ X.obj.hom := (Category.assoc _ _ _).symm
    _ = g.hom.left ≫ X.obj.hom := congrArg (fun t => t ≫ X.obj.hom) ha
    _ = _ := Over.w g.hom

theorem liftNative_base {A Z X : SourceReducedComplexSpace} (j : A ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j.hom.left] (g : Z ⟶ X)
    (h : range g.hom.left.base ⊆ range j.hom.left.base) (z : Z.obj.left) :
    j.hom.left.base ((liftNative j g h).hom.left.base z) = g.hom.left.base z :=
  congrArg (fun F => F.base z) (LocallyRingedSpace.IsOpenImmersion.lift_fac j.hom.left g.hom.left h)

/-- **Relatively compact restrictions have bounded native dimension.** -/
theorem exists_nativeDimLE_restriction (Z : SourceReducedComplexSpace) (U : Opens Z.obj.left)
    (hU : IsCompact (closure (U : Set Z.obj.left))) :
    ∃ m, NativeDimLE (OriginalRelativelyCompactRestriction.restriction Z U hU) univ m := by
  classical
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover
    (fun z : Z.obj.left => range (LocalEmbedding.ofPoint Z z).toPoint)
    (fun z => (LocalEmbedding.ofPoint Z z).isOpen_range_toPoint)
    (by intro z _; exact mem_iUnion.mpr ⟨z, LocalEmbedding.mem_range_ofPoint Z z⟩)
  refine ⟨s.sup fun z => (LocalEmbedding.ofPoint Z z).dim, ?_⟩
  intro e y j hy
  rw [trace_univ] at hy
  have hint := (regularAtDim_carrier_iff e ⟨y, hy.2.1⟩ j).mp hy
  set ι := OriginalRelativelyCompactRestriction.inclusion Z U hU
  have hint' : intrinsicRegularAtDim Z.obj (ι.hom.left.base (e.toPoint ⟨y, hy.2.1⟩)) j :=
    (HironakaG11IntrinsicRegularOpenImmersion.intrinsicRegularAtDim_map_iff ι.hom.left
      (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion Z U hU)
      (OriginalRelativelyCompactRestriction.inclusion_scalar Z U hU) _ j).mpr hint
  have hmem : ι.hom.left.base (e.toPoint ⟨y, hy.2.1⟩) ∈ closure (U : Set Z.obj.left) := by
    apply subset_closure
    rw [OriginalRelativelyCompactRestriction.inclusion_base]
    exact (e.toPoint ⟨y, hy.2.1⟩).property
  obtain ⟨z, hz, hzr⟩ := mem_iUnion₂.mp (hs hmem)
  obtain ⟨c, hc⟩ := hzr
  have hreg := (regularAtDim_carrier_iff (LocalEmbedding.ofPoint Z z) c j).mpr (by rw [hc]; exact hint')
  exact hreg.1.trans (Finset.le_sup (f := fun z => (LocalEmbedding.ofPoint Z z).dim) hz)

/-- Properness on `P` makes the restriction to the reduced closed subspace on `P` proper. -/
theorem isProperMap_inclusion_comp {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    {P : Set Y.obj.left} (hP : Y.IsAnalyticSubset P) (hprop : ProperOn f.hom.left.base P) :
    IsProperMap (OriginalAnalyticClosedSubspace.inclusion Y P hP ≫ f).hom.left.base := by
  have : T2Space X.obj.left.toPresheafedSpace := X.property.1
  have : LocallyCompactSpace X.obj.left.toPresheafedSpace := locallyCompactSpace X
  set ι := OriginalAnalyticClosedSubspace.inclusion Y P hP
  have hιc := OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding Y P hP
  refine isProperMap_iff_isCompact_preimage.mpr ⟨(ι ≫ f).hom.left.base.hom.continuous, fun K hK => ?_⟩
  have h1 : IsCompact (P ∩ f.hom.left.base ⁻¹' K) := hprop K hK
  have h2 : (ι ≫ f).hom.left.base ⁻¹' K = ι.hom.left.base ⁻¹' (P ∩ f.hom.left.base ⁻¹' K) := by
    ext q
    constructor
    · intro hq
      exact ⟨(OriginalAnalyticClosedSubspace.inclusion_range Y P hP).subset ⟨q, rfl⟩, hq⟩
    · intro hq
      exact hq.2
  rw [h2]
  exact hιc.isCompact_preimage h1

/-- **5.0: native Remmert from its core.** -/
theorem nativeProperImage_of_core (hcore : NativeProperImageCore) : NativeProperImage := by
  intro X Y f P hP hprop x
  have : T2Space X.obj.left.toPresheafedSpace := X.property.1
  have : LocallyCompactSpace X.obj.left.toPresheafedSpace := locallyCompactSpace X
  have : T2Space X.obj.left := X.property.1
  have : LocallyCompactSpace X.obj.left := locallyCompactSpace X
  -- the reduced closed subspace on `P`
  set Q := OriginalAnalyticClosedSubspace.sourceObject Y P hP
  set f₀ := OriginalAnalyticClosedSubspace.inclusion Y P hP ≫ f
  have hf₀ : IsProperMap f₀.hom.left.base := isProperMap_inclusion_comp f hP hprop
  have hrange : range f₀.hom.left.base = f.hom.left.base '' P := by
    have h : f₀.hom.left.base = f.hom.left.base ∘
        (OriginalAnalyticClosedSubspace.inclusion Y P hP).hom.left.base := rfl
    rw [h, range_comp, OriginalAnalyticClosedSubspace.inclusion_range]
  -- a local embedding at `x` with relatively compact image
  obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨e, hxe, heK, -⟩ := LocalEmbedding.exists_domain x isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hKx)
  let V : Opens X.obj.left := ⟨range e.toPoint, e.isOpen_range_toPoint⟩
  have hV : IsCompact (closure (V : Set X.obj.left)) :=
    hKc.of_isClosed_subset isClosed_closure
      (closure_minimal (heK.trans interior_subset) hKc.isClosed)
  -- the restricted source
  set W := OriginalRelativelyCompactRestriction.preimageOpen V f₀
  have hW := OriginalRelativelyCompactRestriction.isCompact_closure_preimage V f₀ hV hf₀
  set QV := OriginalRelativelyCompactRestriction.restriction Q W hW
  set ιV := OriginalRelativelyCompactRestriction.inclusion Q W hW
  let : SecondCountableTopology QV.obj.left :=
    OriginalRelativelyCompactRestriction.secondCountableTopology Q W hW
  obtain ⟨m, hm⟩ := exists_nativeDimLE_restriction Q W hW
  -- the lift into the model of `e`
  set j := EmbeddedBlowupOverlap.chartMorphism e
  have hlift : range (ιV ≫ f₀).hom.left.base ⊆ range j.hom.left.base := by
    rintro _ ⟨q, rfl⟩
    exact q.property
  set ψ := liftNative j (ιV ≫ f₀) hlift
  have hψ : ∀ q, e.toPoint (ψ.hom.left.base q) = f₀.hom.left.base q.val :=
    fun q => liftNative_base j (ιV ≫ f₀) hlift q
  have hψprop : IsProperMap (pointMap ψ) := by
    refine isProperMap_iff_isCompact_preimage.mpr
      ⟨continuous_pointMap ψ, fun L hL => ?_⟩
    have hcl : IsClosedEmbedding (Subtype.val : e.carrier → e.ambient) :=
      e.analytic.isClosed.isClosedEmbedding_subtypeVal
    have hL' : IsCompact ((Subtype.val : e.carrier → e.ambient) ⁻¹' L) := hcl.isCompact_preimage hL
    have hL'' : IsCompact (e.toPoint '' ((Subtype.val : e.carrier → e.ambient) ⁻¹' L)) :=
      hL'.image e.isOpenEmbedding_toPoint.continuous
    have hpre : IsCompact (f₀.hom.left.base ⁻¹' (e.toPoint '' ((Subtype.val : e.carrier → e.ambient) ⁻¹' L))) :=
      hf₀.isCompact_preimage hL''
    have hsub : f₀.hom.left.base ⁻¹' (e.toPoint '' ((Subtype.val : e.carrier → e.ambient) ⁻¹' L)) ⊆
        range (Subtype.val : W → Q.obj.left) := by
      rintro q ⟨c, -, hc⟩
      exact ⟨⟨q, ⟨c, hc⟩⟩, rfl⟩
    have h := Topology.IsInducing.subtypeVal.isCompact_preimage' hpre hsub
    have hset : ∀ q : QV.obj.left, q ∈ pointMap ψ ⁻¹' L ↔
        q ∈ (Subtype.val : W → Q.obj.left) ⁻¹' (f₀.hom.left.base ⁻¹'
          (e.toPoint '' ((Subtype.val : e.carrier → e.ambient) ⁻¹' L))) := by
      intro q
      constructor
      · intro hq
        exact ⟨ψ.hom.left.base q, hq, hψ q⟩
      · rintro ⟨c, hcL, hc⟩
        have : ψ.hom.left.base q = c := e.toPoint_injective ((hψ q).trans hc.symm)
        change (ψ.hom.left.base q).val ∈ L
        rw [this]
        exact hcL
    rw [Set.ext hset]
    exact h
  have hana := hcore QV m hm e.dim e.ambient e.carrier e.analytic ψ hψprop
  refine ⟨e, hxe, range (pointMap ψ), hana, ?_⟩
  ext c
  simp only [mem_preimage, mem_range]
  constructor
  · intro hc
    rw [← hrange] at hc
    obtain ⟨q, hq⟩ := hc
    have hqW : q ∈ W := by
      change f₀.hom.left.base q ∈ range e.toPoint
      rw [hq]
      exact ⟨c, rfl⟩
    refine ⟨⟨q, hqW⟩, ?_⟩
    have : ψ.hom.left.base ⟨q, hqW⟩ = c := e.toPoint_injective ((hψ _).trans hq)
    change (ψ.hom.left.base ⟨q, hqW⟩).val = c.val
    rw [this]
  · rintro ⟨q, hq⟩
    have : ψ.hom.left.base q = c := Subtype.ext hq
    rw [← hrange]
    exact ⟨q.val, (hψ q).symm.trans (by rw [this])⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10MwRemmertReduction
