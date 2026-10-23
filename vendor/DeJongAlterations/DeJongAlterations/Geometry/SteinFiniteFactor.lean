import DeJongAlterations.Geometry.ProjectiveCompactification
import DeJongAlterations.Geometry.NormalCurveModification
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Extension of genuine generic lifts to finite schemes

The actual schematic closure of a spread generic graph is finite and
birational over the normal source; its native inverse constructs the lift.
No factorization, graph compatibility, or birationality certificate is supplied.
This is a prerequisite to source 4.12, not a Stein factorization theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.SteinFiniteFactor

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X N S : Scheme.{u}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  (f : X ⟶ S) (ν : N ⟶ S) [IsFinite ν]
  (φ : Spec X.functionField ⟶ N)
  (hφ : φ ≫ ν = X.fromSpecStalk (genericPoint X) ≫ f)

/-- The original generic lift, spread over an actual dense open of the source. -/
def partialLift : X.PartialMap N :=
  Scheme.PartialMap.ofFromSpecStalk f ν φ hφ

/-- The literal coefficient triangle on the constructed open domain. -/
@[reassoc]
theorem partialLift_structure :
    (partialLift f ν φ hφ).hom ≫ ν = (partialLift f ν φ hφ).domain.ι ≫ f :=
  Scheme.PartialMap.ofFromSpecStalk_comp f ν φ hφ

private instance partialLift_nonempty : Nonempty (partialLift f ν φ hφ).domain :=
  ⟨⟨genericPoint X, Scheme.PartialMap.mem_domain_ofFromSpecStalk f ν φ hφ⟩⟩

/-- The native graph of this actual partial morphism. -/
def graph : (partialLift f ν φ hφ).domain.toScheme ⟶ pullback f ν :=
  pullback.lift (partialLift f ν φ hφ).domain.ι
    (partialLift f ν φ hφ).hom (partialLift_structure f ν φ hφ).symm

@[reassoc (attr := simp)]
theorem graph_fst : graph f ν φ hφ ≫ pullback.fst f ν =
    (partialLift f ν φ hφ).domain.ι := by simp [graph]

@[reassoc (attr := simp)]
theorem graph_snd : graph f ν φ hφ ≫ pullback.snd f ν =
    (partialLift f ν φ hφ).hom := by simp [graph]

instance graph_isImmersion : IsImmersion (graph f ν φ hφ) := by
  have : IsImmersion (graph f ν φ hφ ≫ pullback.fst f ν) := by
    rw [graph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst f ν)

instance graph_isQuasiCompact : QuasiCompact (graph f ν φ hφ) := by
  have : QuasiCompact (graph f ν φ hφ ≫ pullback.fst f ν) := by
    rw [graph_fst]
    infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst f ν)

/-- The actual kernel subscheme of the generic graph in the genuine fibre product. -/
def graphClosure : Scheme.{u} := (graph f ν φ hφ).image

def inclusion : (partialLift f ν φ hφ).domain.toScheme ⟶ graphClosure f ν φ hφ :=
  (graph f ν φ hφ).toImage

def projection : graphClosure f ν φ hφ ⟶ X :=
  (graph f ν φ hφ).imageι ≫ pullback.fst f ν

def finiteMap : graphClosure f ν φ hφ ⟶ N :=
  (graph f ν φ hφ).imageι ≫ pullback.snd f ν

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion f ν φ hφ) := by
  unfold inclusion
  infer_instance

instance inclusion_isDominant : IsDominant (inclusion f ν φ hφ) := by
  unfold inclusion
  infer_instance

instance graphClosure_isIntegral : IsIntegral (graphClosure f ν φ hφ) :=
  ProjectiveCompactification.image_isIntegral (graph f ν φ hφ)

instance projection_isFinite : IsFinite (projection f ν φ hφ) := by
  unfold projection
  infer_instance

@[reassoc (attr := simp)]
theorem inclusion_projection : inclusion f ν φ hφ ≫ projection f ν φ hφ =
    (partialLift f ν φ hφ).domain.ι := by
  rw [projection, inclusion, ← Category.assoc, Scheme.Hom.toImage_imageι, graph_fst]

@[reassoc (attr := simp)]
theorem inclusion_finiteMap : inclusion f ν φ hφ ≫ finiteMap f ν φ hφ =
    (partialLift f ν φ hφ).hom := by
  rw [finiteMap, inclusion, ← Category.assoc, Scheme.Hom.toImage_imageι, graph_snd]

@[reassoc]
theorem finiteMap_structure : finiteMap f ν φ hφ ≫ ν = projection f ν φ hφ ≫ f := by
  rw [finiteMap, projection, Category.assoc, Category.assoc, pullback.condition]

/-- The two actual dense open immersions produce the birational identification. -/
def partialIso : (graphClosure f ν φ hφ).PartialIso X where
  source := (inclusion f ν φ hφ).opensRange
  dense_source := (inclusion f ν φ hφ).denseRange
  target := (partialLift f ν φ hφ).domain
  dense_target := (partialLift f ν φ hφ).dense_domain
  iso := (inclusion f ν φ hφ).isoOpensRange.symm

theorem projection_birational :
    Scheme.BirationalOver (projection f ν φ hφ) (𝟙 X) := by
  refine ⟨partialIso f ν φ hφ, ?_⟩
  change (inclusion f ν φ hφ).isoOpensRange.inv ≫
      (partialLift f ν φ hφ).domain.ι ≫ 𝟙 X =
    (inclusion f ν φ hφ).opensRange.ι ≫ projection f ν φ hφ
  rw [Category.comp_id, ← inclusion_projection f ν φ hφ, ← Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp]

theorem projection_isIso (hnormal : IsNormalScheme X) : IsIso (projection f ν φ hφ) :=
  NormalCurveModification.isIso_of_finite_birational
    (projection f ν φ hφ) (projection_birational f ν φ hφ) hnormal

/-- The actual inverse of the proved finite birational graph projection constructs the lift. -/
def lift (hnormal : IsNormalScheme X) : X ⟶ N := by
  let := projection_isIso f ν φ hφ hnormal
  exact inv (projection f ν φ hφ) ≫ finiteMap f ν φ hφ

@[reassoc]
theorem lift_structure (hnormal : IsNormalScheme X) : lift f ν φ hφ hnormal ≫ ν = f := by
  let := projection_isIso f ν φ hφ hnormal
  rw [lift, Category.assoc, finiteMap_structure, IsIso.inv_hom_id_assoc]

@[reassoc]
theorem partialLift_lift (hnormal : IsNormalScheme X) :
    (partialLift f ν φ hφ).domain.ι ≫ lift f ν φ hφ hnormal =
      (partialLift f ν φ hφ).hom := by
  let := projection_isIso f ν φ hφ hnormal
  rw [← inclusion_projection f ν φ hφ, lift, Category.assoc,
    IsIso.hom_inv_id_assoc, inclusion_finiteMap]

/-- The extended morphism retains the originally specified actual generic morphism. -/
@[reassoc]
theorem lift_generic (hnormal : IsNormalScheme X) :
    X.fromSpecStalk (genericPoint X) ≫ lift f ν φ hφ hnormal = φ := by
  let U := (partialLift f ν φ hφ).domain
  have hη : genericPoint X ∈ U :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk f ν φ hφ
  rw [← U.fromSpecStalkOfMem_ι (genericPoint X) hη, Category.assoc, partialLift_lift]
  exact Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk f ν φ hφ

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The original generic point morphism is genuinely dominant. -/
theorem genericMap_isDominant : IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- A finite target over the original base makes the actual generic extension unique. -/
theorem generic_lift_unique (a b : X ⟶ N)
    (ha : a ≫ ν = f) (hb : b ≫ ν = f)
    (hgen : X.fromSpecStalk (genericPoint X) ≫ a =
      X.fromSpecStalk (genericPoint X) ≫ b) : a = b := by
  let := genericMap_isDominant (X := X)
  exact ext_of_isDominant_of_isSeparated ν (ha.trans hb.symm)
    (X.fromSpecStalk (genericPoint X)) hgen

include hφ in
/-- Genuine existence and uniqueness, with the actual original generic morphism retained. -/
theorem existsUnique_lift (hnormal : IsNormalScheme X) :
    ∃! h : X ⟶ N, h ≫ ν = f ∧ X.fromSpecStalk (genericPoint X) ≫ h = φ := by
  refine ⟨lift f ν φ hφ hnormal,
    ⟨lift_structure f ν φ hφ hnormal, lift_generic f ν φ hφ hnormal⟩, ?_⟩
  intro h hh
  exact generic_lift_unique f ν h (lift f ν φ hφ hnormal) hh.1
    (lift_structure f ν φ hφ hnormal)
    (hh.2.trans (lift_generic f ν φ hφ hnormal).symm)

end DeJongAlterations.Geometry.SteinFiniteFactor
