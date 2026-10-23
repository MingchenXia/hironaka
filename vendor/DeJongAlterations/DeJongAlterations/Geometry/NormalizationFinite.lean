import DeJongAlterations.Geometry.AffineCurveAlteration
import DeJongAlterations.Geometry.NormalizationGluing
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Topology.Sets.OpenCover

/-!
# Finiteness of the actual global normalization over a perfect field

The affine finite-type coefficient maps are induced by the actual structure
morphism. Finiteness of integral closure is proved in the actual function field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalizationFinite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The coefficient map on an actual affine coordinate ring, obtained from
the structure morphism and the canonical sections isomorphism of `Spec k`. -/
def affineCoefficientMap (p : X ⟶ Spec (.of k)) (U : X.affineOpens) :
    k →+* Γ(X, U.1) :=
  (p.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- Local finite type of the actual structure morphism gives finite type of
its canonical field-to-affine-sections map. -/
theorem affineCoefficientMap_finiteType (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : X.affineOpens) : (affineCoefficientMap p U).FiniteType := by
  apply (p.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
  exact RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2

/-- The canonical algebra on each affine coordinate ring is finite type. -/
theorem affineSections_finiteType (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : X.affineOpens) :
    letI := (affineCoefficientMap p U).toAlgebra
    Algebra.FiniteType k Γ(X, U.1) :=
  affineCoefficientMap_finiteType p U

/-- Finiteness of the actual affine integral closure in the scheme's own
function field, from the actual perfect-field structure morphism. -/
theorem finite_integralClosure_functionField [PerfectField k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    Module.Finite Γ(X, U.1) (integralClosure Γ(X, U.1) X.functionField) := by
  let := (affineCoefficientMap p U).toAlgebra
  let : Algebra.FiniteType k Γ(X, U.1) := affineSections_finiteType p U
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  let : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact AffineCurveAlteration.finite_integralClosure k Γ(X, U.1) X.functionField

/-- An actual affine coordinate ring has dimension at most that of the
original scheme, expressed here at the dimension-one bound. -/
theorem affineSections_krullDimLE_one (U : X.affineOpens)
    (hdim : topologicalKrullDim X ≤ 1) : Ring.KrullDimLE 1 Γ(X, U.1) := by
  have hU : IsAffineOpen U.1 := U.2
  have h : topologicalKrullDim (Spec Γ(X, U.1)) ≤ 1 :=
    hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  change topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) ≤ 1 at h
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  exact Ring.krullDimLE_iff.mpr h

/-- The actual normalized affine charts of an integral curve are regular,
without a supplied normality or regularity certificate. -/
theorem integralClosure_functionField_isRegular [PerfectField k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1]
    (hdim : topologicalKrullDim X ≤ 1) :
    IsRegularScheme (Spec (.of (integralClosure Γ(X, U.1) X.functionField))) := by
  let := (affineCoefficientMap p U).toAlgebra
  let : Algebra.FiniteType k Γ(X, U.1) := affineSections_finiteType p U
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  let : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let : Ring.KrullDimLE 1 Γ(X, U.1) := affineSections_krullDimLE_one U hdim
  let : Ring.DimensionLEOne Γ(X, U.1) := ⟨fun _ hP ↦ hP.isMaximal_of_ne_bot ‹_›⟩
  let : Ring.DimensionLEOne (integralClosure Γ(X, U.1) X.functionField) := inferInstance
  let : IsNoetherianRing (integralClosure Γ(X, U.1) X.functionField) :=
    AffineCurveAlteration.isNoetherianRing_integralClosure k Γ(X, U.1) X.functionField
  let : IsIntegrallyClosed (integralClosure Γ(X, U.1) X.functionField) :=
    AffineCurveAlteration.isIntegrallyClosed_integralClosure Γ(X, U.1) X.functionField
  exact isRegularScheme_spec_of_isIntegrallyClosed_of_krullDimLE_one _

/-- The genuine affine normalization map in the original common function field. -/
def affineNormalizationMap [IsIntegral X] (U : X.affineOpens) [Nonempty U.1] :
    Spec (.of (integralClosure Γ(X, U.1) X.functionField)) ⟶ Spec Γ(X, U.1) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) X.functionField)))

/-- The actual affine normalization map is finite over a perfect ground field. -/
theorem affineNormalizationMap_isFinite [PerfectField k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    IsFinite (affineNormalizationMap U) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (finite_integralClosure_functionField p U)

/-- Lying over proves surjectivity for the actual common-function-field
normalization map; no finiteness hypothesis is required. -/
theorem affineNormalizationMap_surjective [IsIntegral X] (U : X.affineOpens)
    [Nonempty U.1] : Function.Surjective (affineNormalizationMap U) := by
  let : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  have hinj : Function.Injective
      (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) X.functionField)) := by
    intro a b hab
    apply IsFractionRing.injective Γ(X, U.1) X.functionField
    exact congrArg (fun c : integralClosure Γ(X, U.1) X.functionField ↦
      (c : X.functionField)) hab
  exact (show (algebraMap Γ(X, U.1)
    (integralClosure Γ(X, U.1) X.functionField)).IsIntegral from
      algebraMap_isIntegral_iff.mpr inferInstance).comap_surjective hinj

/-- Nonempty actual affine coordinate spectra cover every scheme. -/
@[simps! I₀ X f]
def nonemptyAffineCoordinateOpenCover (X : Scheme.{u}) : X.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers
    {U : X.AffineZariskiSite // Nonempty U.1}
    (fun U => Spec Γ(X, U.val.1)) (fun U => U.val.2.fromSpec) (by
      intro x
      obtain ⟨W, hW, hxW, _⟩ :=
        exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
      refine ⟨⟨⟨W, hW⟩, ⟨⟨x, hxW⟩⟩⟩, ?_⟩
      change x ∈ Set.range hW.fromSpec
      rw [hW.range_fromSpec]
      exact hxW)

/-- The actual map from the coordinate spectrum of a nonempty affine open
to an integral scheme is dominant. -/
theorem affineCoordinate_isDominant [IsIntegral X] (U : X.affineOpens) [Nonempty U.1] :
    IsDominant U.2.fromSpec := by
  constructor
  change Dense (Set.range U.2.fromSpec)
  rw [U.2.range_fromSpec]
  exact U.1.isOpen.dense (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U.1))

open NormalizationGluing

section Integral

variable [IsIntegral X]

/-- Every genuine common-field affine normalization chart is integral. -/
theorem chart_isIntegral (U : NonemptyAffineOpen X) :
    IsIntegral (Spec (.of (closureRing U))) := by
  infer_instance

/-- Each actual affine normalization chart maps dominantly to the original scheme. -/
theorem chartInclusion_comp_isDominant (U : NonemptyAffineOpen X) :
    IsDominant (chartInclusion X U ≫ normalizationStructure X) := by
  rw [chartInclusion_structure]
  let : IsDominant (affineStructure U) :=
    ⟨(affineNormalizationMap_surjective ⟨U.1.1, U.1.2⟩).denseRange⟩
  let := affineCoordinate_isDominant ⟨U.1.1, U.1.2⟩
  infer_instance

/-- The native affine chart images intersect inside the actual normalization. -/
theorem chartInclusion_not_disjoint (U V : NonemptyAffineOpen X) :
    ¬ Disjoint (chartInclusion X U).opensRange (chartInclusion X V).opensRange := by
  let := chartInclusion_comp_isDominant U
  obtain ⟨p, hp⟩ := (chartInclusion X U ≫ normalizationStructure X).denseRange.exists_mem_open
    V.1.1.isOpen (Set.nonempty_coe_sort.mp (inferInstance : Nonempty V.1.1))
  have hpV : chartInclusion X U p ∈ (chartInclusion X V).opensRange := by
    rw [chartInclusion_opensRange]
    exact hp
  intro hd
  exact hd.le_bot ⟨⟨p, rfl⟩, hpV⟩

/-- Integrality is derived for the constructed global normalization from its
actual integral charts and their pairwise intersecting open images. -/
theorem isIntegral_normalization : IsIntegral (normalization X) := by
  let C := normalizationCover X
  let : ∀ i : C.I₀, IsIntegral (C.X i) := fun i => chart_isIntegral i
  let : AlgebraicGeometry.IsReduced (normalization X) :=
    AlgebraicGeometry.IsReduced.of_openCover (normalization X) C
  have hpair : Pairwise (fun i j : C.I₀ =>
      ¬ Disjoint (C.f i).opensRange (C.f j).opensRange) := by
    intro i j _
    exact chartInclusion_not_disjoint i j
  have hpre (i : C.I₀) : PreirreducibleSpace (C.f i).opensRange := by
    apply isPreirreducible_iff_preirreducibleSpace.mp
    have h := (PreirreducibleSpace.isPreirreducible_univ :
      IsPreirreducible (Set.univ : Set (C.X i))).image
      (C.f i) (C.f i).continuous.continuousOn
    simpa only [Set.image_univ, Scheme.Hom.coe_opensRange] using h
  let : PreirreducibleSpace (normalization X) :=
    PreirreducibleSpace.of_isOpenCover hpair C.isOpenCover_opensRange hpre
  let : Nonempty (normalization X) := by
    let U : NonemptyAffineOpen X :=
      (nonemptyAffineCoordinateOpenCover X).idx (Classical.choice inferInstance)
    let : IsIntegral (Spec (.of (closureRing U))) := chart_isIntegral U
    exact ⟨chartInclusion X U (Classical.choice inferInstance)⟩
  let : IrreducibleSpace (normalization X) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Dominance is derived for the same actual normalization structure morphism. -/
theorem normalizationStructure_isDominant : IsDominant (normalizationStructure X) := by
  let U : NonemptyAffineOpen X :=
    (nonemptyAffineCoordinateOpenCover X).idx (Classical.choice inferInstance)
  let := chartInclusion_comp_isDominant U
  exact IsDominant.of_comp (chartInclusion X U) (normalizationStructure X)

/-- The actual native global normalization is finite over a scheme locally of
finite type over a perfect field; the chart comparisons are constructed internally. -/
theorem normalizationStructure_isFinite [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] : IsFinite (normalizationStructure X) := by
  apply IsZariskiLocalAtTarget.of_openCover (nonemptyAffineCoordinateOpenCover X)
  intro U
  let V : NonemptyAffineOpen X := U
  let h := (isPullback_chart V).flip
  change IsFinite (Limits.pullback.snd (normalizationStructure X) V.1.2.fromSpec)
  rw [← h.isoPullback_inv_snd]
  let : IsFinite (affineStructure V) :=
    affineNormalizationMap_isFinite p ⟨V.1.1, V.1.2⟩
  infer_instance

/-- The actual finite dominant global normalization is an alteration. -/
theorem normalizationStructure_isAlteration [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] : IsAlteration (normalizationStructure X) := by
  let : IsIntegral (normalization X) := isIntegral_normalization
  let : IsFinite (normalizationStructure X) := normalizationStructure_isFinite p
  let : IsDominant (normalizationStructure X) := normalizationStructure_isDominant
  exact isAlteration_of_isFinite _

/-- The actual global normalization of an integral curve is regular, with
regularity transported through its genuine chart inclusions on local rings. -/
theorem normalization_isRegular [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (hdim : topologicalKrullDim X ≤ 1) :
    IsRegularScheme (normalization X) := by
  intro x
  let C := normalizationCover X
  obtain ⟨y, hy⟩ := C.covers x
  let U : NonemptyAffineOpen X := C.idx x
  let : IsRegularLocalRing ((C.X U).presheaf.stalk y) :=
    integralClosure_functionField_isRegular p ⟨U.1.1, U.1.2⟩ hdim y
  have hr : IsRegularLocalRing ((normalization X).presheaf.stalk (C.f U y)) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((C.f U).stalkMap y)).symm.commRingCatIsoToRingEquiv
  rw [hy] at hr
  exact hr

end Integral

/-- The actual normalization remains a variety over the original field. -/
theorem normalization_isVariety [PerfectField k] (p : X ⟶ Spec (.of k)) [IsVariety p] :
    IsVariety (normalizationStructure X ≫ p) := by
  let : IsIntegral (normalization X) := isIntegral_normalization
  let : IsFinite (normalizationStructure X) := normalizationStructure_isFinite p
  exact .mk

/-- Every variety of dimension at most one over a perfect field admits the
actual global normalization as a regular alteration, including nonaffine curves. -/
theorem hasRegularAlteration_curve [PerfectField k] (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hdim : topologicalKrullDim X ≤ 1) : HasRegularAlteration p := by
  exact ⟨normalization X, normalizationStructure X ≫ p, normalizationStructure X,
    normalization_isVariety p, rfl, normalizationStructure_isAlteration p,
    normalization_isRegular p hdim⟩

end DeJongAlterations.Geometry.NormalizationFinite
