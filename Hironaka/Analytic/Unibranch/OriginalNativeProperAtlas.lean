import Hironaka.Analytic.Unibranch.OriginalNativeIsoOverSaturatedCover
import Hironaka.Analytic.Unibranch.EmbeddedBlowupTopology
import Hironaka.Analytic.Unibranch.EmbeddedBlowupParacompact
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-! Ordinary native proper atlases, with arbitrary overlapping original charts.
The full ordinary GlueData and LOCAL inverse-image overlaps are inputs; the
global projection, saturation, full restriction isos and original native source
are constructed. Local maps are proper to their own target OPEN, not to X.
Blueprint first: `original-native-proper-atlas.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProperAtlas
noncomputable section
open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace

variable (D : LocallyRingedSpace.GlueData.{0})
  (σ : ∀ i : D.J, D.U i ⟶ complexPoint)
  (hA : ∀ i, sourceReducedComplexSpaceProperty (Over.mk (σ i)))

/-- The unchanged given local LRS with its ordinary original scalar structure. -/
@[implicit_reducible]
def localSource (i : D.J) : SourceReducedComplexSpace := ⟨Over.mk (σ i),hA i⟩

variable {X : SourceReducedComplexSpace} {B : D.J → SourceReducedComplexSpace}
  (J : ∀ i, B i ⟶ X) (p : ∀ i, localSource D σ hA i ⟶ B i)

/-- The entire local projection, retaining its native structure-sheaf map. -/
def localProjection (i : D.J) : D.U i ⟶ X.obj.left := (p i ≫ J i).hom.left

/-- The existing native gluer on the SAME ordinary full overlap data. -/
def glued : LocallyRingedSpace := D.toGlueData.glued

/-- Its genuine full native chart inclusion. -/
def inclusion (i : D.J) : D.U i ⟶ glued D := D.toGlueData.ι i

instance inclusion_isOpenImmersion (i : D.J) :
    LocallyRingedSpace.IsOpenImmersion (inclusion D i) := D.ι_isOpenImmersion i

variable (hover : ∀ i j,
  D.f i j ≫ localProjection D σ hA J p i =
    (D.t i j ≫ D.f j i) ≫ localProjection D σ hA J p j)

/-- Actual descent constructs the full map; no global projection is supplied. -/
def projection : glued D ⟶ X.obj.left :=
  Multicoequalizer.desc D.toGlueData.diagram X.obj.left
    (localProjection D σ hA J p) (by rintro ⟨i,j⟩; exact hover i j)

theorem inclusion_projection (i : D.J) :
    inclusion D i ≫ projection D σ hA J p hover = localProjection D σ hA J p i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X.obj.left (localProjection D σ hA J p) _ i

/-- The complex scalar triangle follows from the FULL local projection. -/
theorem inclusion_scalar (i : D.J) :
    inclusion D i ≫ (projection D σ hA J p hover ≫ X.obj.hom) = σ i := by
  rw [← Category.assoc,inclusion_projection]
  exact Over.w (p i ≫ J i).hom

theorem inclusion_cover (x : glued D) :
    ∃ (i : D.J) (y : D.U i), (inclusion D i).base y = x := D.ι_jointly_surjective x

variable (hOverlap : ∀ i j, range (D.f i j).base =
  (localProjection D σ hA J p i).base ⁻¹' range (J j).hom.left.base)

include hOverlap in
/-- LOCAL inverse-image overlap ranges derive GLOBAL saturation. -/
theorem preimage_chart_range (i : D.J) :
    (projection D σ hA J p hover).base ⁻¹' range (J i).hom.left.base =
      range (inclusion D i).base := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,y,rfl⟩ := inclusion_cover D x
    have hp := congrArg (fun F => F.base y) (inclusion_projection D σ hA J p hover j)
    have hy : (localProjection D σ hA J p j).base y ∈ range (J i).hom.left.base := hp ▸ hx
    have hy' : y ∈ range (D.f j i).base := by rw [hOverlap]; exact hy
    obtain ⟨v,hv⟩ := hy'
    refine ⟨(D.f i j).base ((D.t j i).base v),?_⟩
    have heq := congrArg (fun F => F.base v) (D.toGlueData.glue_condition j i)
    exact heq.trans (congrArg (inclusion D j).base hv)
  · rintro ⟨y,rfl⟩
    have hp := congrArg (fun F => F.base y) (inclusion_projection D σ hA J p hover i)
    change (inclusion D i ≫ projection D σ hA J p hover).base y ∈ range (J i).hom.left.base
    exact hp.symm ▸ ⟨(p i).hom.left.base y,rfl⟩

/-- The literal saturated open and the SAME local source are homeomorphic. -/
def saturatedHomeomorph (i : D.J) :
    ((projection D σ hA J p hover).base ⁻¹' range (J i).hom.left.base) ≃ₜ D.U i :=
  ((inclusion_isOpenImmersion D i).base_open.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (preimage_chart_range D σ hA J p hover hOverlap i).symm)).symm

theorem saturatedHomeomorph_symm_val (i : D.J) (y : D.U i) :
    ((saturatedHomeomorph D σ hA J p hover hOverlap i).symm y).val = (inclusion D i).base y := rfl

theorem saturatedHomeomorph_projection (i : D.J)
    (x : (projection D σ hA J p hover).base ⁻¹' range (J i).hom.left.base) :
    (localProjection D σ hA J p i).base ((saturatedHomeomorph D σ hA J p hover hOverlap i) x) =
      (projection D σ hA J p hover).base x.val := by
  let e := saturatedHomeomorph D σ hA J p hover hOverlap i
  have hv : (inclusion D i).base (e x) = x.val := congrArg Subtype.val (e.symm_apply_apply x)
  have hp := congrArg (fun F => F.base (e x)) (inclusion_projection D σ hA J p hover i)
  exact hp.symm.trans (congrArg (projection D σ hA J p hover).base hv)

variable (hJ : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left)

/-- The actual saturated open of the SAME raw glued source. -/
def restrictionOpen (i : D.J) : Opens (glued D) :=
  ⟨(projection D σ hA J p hover).base ⁻¹' range (J i).hom.left.base,
    (hJ i).base_open.isOpen_range.preimage (projection D σ hA J p hover).base.hom.continuous⟩

def restrictionLRS (i : D.J) : LocallyRingedSpace :=
  (glued D).restrict (restrictionOpen D σ hA J p hover hJ i).isOpenEmbedding

def restrictionInclusion (i : D.J) : restrictionLRS D σ hA J p hover hJ i ⟶ glued D :=
  (glued D).ofRestrict (restrictionOpen D σ hA J p hover hJ i).isOpenEmbedding

instance restrictionInclusion_isOpenImmersion (i : D.J) :
    LocallyRingedSpace.IsOpenImmersion (restrictionInclusion D σ hA J p hover hJ i) := by
  dsimp only [restrictionInclusion,restrictionLRS]
  infer_instance

include hOverlap in
private theorem restriction_range (i : D.J) :
    range (restrictionInclusion D σ hA J p hover hJ i).base = range (inclusion D i).base :=
  (Subtype.range_coe).trans (preimage_chart_range D σ hA J p hover hOverlap i)

/-- Two actual native OI lifts give a FULL LRS isomorphism, not only a point map. -/
def restrictionIso (i : D.J) : D.U i ≅ restrictionLRS D σ hA J p hover hJ i := by
  let r := restrictionInclusion D σ hA J p hover hJ i
  let L := inclusion D i
  have hrange : range r.base = range L.base := restriction_range D σ hA J p hover hOverlap hJ i
  let a := LocallyRingedSpace.IsOpenImmersion.lift r L (le_of_eq hrange.symm)
  let b := LocallyRingedSpace.IsOpenImmersion.lift L r (le_of_eq hrange)
  have ha : a ≫ r = L := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hb : b ≫ L = r := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  refine ⟨a,b,?_,?_⟩
  · apply (cancel_mono L).mp
    rw [Category.assoc,hb,ha,Category.id_comp]
  · apply (cancel_mono r).mp
    rw [Category.assoc,ha,hb,Category.id_comp]

theorem restrictionIso_inclusion (i : D.J) :
    (restrictionIso D σ hA J p hover hOverlap hJ i).hom ≫
      restrictionInclusion D σ hA J p hover hJ i = inclusion D i :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _
    (le_of_eq (restriction_range D σ hA J p hover hOverlap hJ i).symm)

/-- The actual isomorphism respects the full complex scalar map. -/
theorem restrictionIso_over (i : D.J) :
    (restrictionIso D σ hA J p hover hOverlap hJ i).hom ≫
      (restrictionInclusion D σ hA J p hover hJ i ≫
        (projection D σ hA J p hover ≫ X.obj.hom)) = σ i := by
  rw [← Category.assoc,restrictionIso_inclusion]
  exact inclusion_scalar D σ hA J p hover i

/-- Its full projection is precisely the given local projection. -/
theorem restrictionIso_projection (i : D.J) :
    (restrictionIso D σ hA J p hover hOverlap hJ i).hom ≫
      (restrictionInclusion D σ hA J p hover hJ i ≫ projection D σ hA J p hover) =
        localProjection D σ hA J p i := by
  rw [← Category.assoc,restrictionIso_inclusion]
  exact inclusion_projection D σ hA J p hover i

private def chartOpen (i : D.J) : Opens X.obj.left :=
  ⟨range (J i).hom.left.base,(hJ i).base_open.isOpen_range⟩

private def chartRangeHomeomorph (i : D.J) : (B i).obj.left ≃ₜ chartOpen D J hJ i :=
  (hJ i).base_open.isEmbedding.toHomeomorph

private def localTargetProjection (i : D.J) : D.U i → chartOpen D J hJ i :=
  chartRangeHomeomorph D J hJ i ∘ (p i).hom.left.base

variable (hcover : ∀ x : X.obj.left, ∃ (i : D.J) (b : (B i).obj.left), (J i).hom.left.base b = x)

include hcover in
private theorem chartOpen_cover : IsOpenCover (chartOpen D J hJ) := by
  apply IsOpenCover.of_sets (fun i => (hJ i).base_open.isOpen_range)
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨i,b,hb⟩ := hcover x
  exact ⟨i,b,hb⟩

include σ hA p hover hOverlap hJ hcover in
/-- Exact source saturation yields Hausdorffness without any global countability. -/
theorem glued_t2 : T2Space (glued D) := by
  apply @EmbeddedBlowupTopology.t2Space_of_saturated_cover X.obj.left (glued D) D.J _ _ X.property.1
    (projection D σ hA J p hover).base (projection D σ hA J p hover).base.hom.continuous
    (chartOpen D J hJ) (chartOpen_cover D J hJ hcover)
  intro i
  let : T2Space (D.U i) := (hA i).1
  exact (saturatedHomeomorph D σ hA J p hover hOverlap i).symm.t2Space

variable (hproper : ∀ i, IsProperMap (p i).hom.left.base)

include hOverlap hJ hcover hproper in
/-- LOCAL proper maps to actual target OPENS derive global properness. -/
theorem projection_isProperMap : IsProperMap (projection D σ hA J p hover).base := by
  apply EmbeddedBlowupTopology.isProperMap_of_saturated_cover
    (projection D σ hA J p hover).base (projection D σ hA J p hover).base.hom.continuous
    (chartOpen D J hJ) (chartOpen_cover D J hJ hcover)
  intro i
  have hcomm : localTargetProjection D σ hA J p hJ i ∘
      saturatedHomeomorph D σ hA J p hover hOverlap i =
        ((chartOpen D J hJ i : Set X.obj.left).restrictPreimage
          (projection D σ hA J p hover).base) := by
    funext x
    apply Subtype.ext
    exact saturatedHomeomorph_projection D σ hA J p hover hOverlap i x
  rw [← hcomm]
  exact ((chartRangeHomeomorph D J hJ i).isProperMap.comp (hproper i)).comp
    (saturatedHomeomorph D σ hA J p hover hOverlap i).isProperMap

include σ hA p hover hOverlap hJ hcover hproper in
theorem glued_paracompact : ParacompactSpace (glued D) :=
  @EmbeddedBlowupParacompact.paracompactSpace_of_isProperMap X.obj.left (glued D) _ _ X.property.2.1
    (projection D σ hA J p hover).base
    (projection_isProperMap D σ hA J p hover hOverlap hJ hcover hproper)

/-- The original analytic-model clause uses the SAME local sources and native charts. -/
theorem original_analytic_atlas (x : glued D) :
    ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ k : (modelOver U C).left ⟶ glued D,
        LocallyRingedSpace.IsOpenImmersion k ∧
        k ≫ (projection D σ hA J p hover ≫ X.obj.hom) = (modelOver U C).hom ∧
        x ∈ range k.base := by
  obtain ⟨i,y,hy⟩ := inclusion_cover D x
  obtain ⟨n,U,C,hC,k,hk,hks,z,hz⟩ := (hA i).2.2 y
  refine ⟨n,U,C,hC,k ≫ inclusion D i,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k hk _ (inclusion_isOpenImmersion D i),?_,z,?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => k ≫ t) (inclusion_scalar D σ hA J p hover i)).trans hks)
  · change (inclusion D i).base (k.base z) = x
    rw [hz]
    exact hy

include hcover in
/-- SAME raw LRS and scalar, now proved to be an original native reduced space. -/
@[implicit_reducible]
def sourceObject : SourceReducedComplexSpace :=
  ⟨Over.mk (projection D σ hA J p hover ≫ X.obj.hom),
    glued_t2 D σ hA J p hover hOverlap hJ hcover,
    glued_paracompact D σ hA J p hover hOverlap hJ hcover hproper,
    original_analytic_atlas D σ hA J p hover⟩

include hcover in
def projectionMorphism : sourceObject D σ hA J p hover hOverlap hJ hcover hproper ⟶ X :=
  ObjectProperty.homMk (Over.homMk (projection D σ hA J p hover) rfl)

include hcover in
def localMorphism (i : D.J) : localSource D σ hA i ⟶
    sourceObject D σ hA J p hover hOverlap hJ hcover hproper :=
  ObjectProperty.homMk (Over.homMk (inclusion D i) (inclusion_scalar D σ hA J p hover i))

include hcover in
instance localMorphism_isOpenImmersion (i : D.J) :
    LocallyRingedSpace.IsOpenImmersion
      (localMorphism D σ hA J p hover hOverlap hJ hcover hproper i).hom.left :=
  inclusion_isOpenImmersion D i

include hcover in
theorem localMorphism_projection (i : D.J) :
    localMorphism D σ hA J p hover hOverlap hJ hcover hproper i ≫
      projectionMorphism D σ hA J p hover hOverlap hJ hcover hproper = p i ≫ J i := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact inclusion_projection D σ hA J p hover i

include hcover in
theorem localMorphism_cover
    (x : (sourceObject D σ hA J p hover hOverlap hJ hcover hproper).obj.left) :
    ∃ (i : D.J) (a : (localSource D σ hA i).obj.left),
      (localMorphism D σ hA J p hover hOverlap hJ hcover hproper i).hom.left.base a = x :=
  inclusion_cover D x

end
end Hironaka.Analytic.Unibranch.OriginalNativeProperAtlas
