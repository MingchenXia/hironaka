import Hironaka.Geometry.NodeCompletedLocalSelectedAffine

/-! The SAME prescribed original geometric point on its literal original-stalk tensor. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

namespace Hironaka.Geometry.NodeCompletedLocalSelectedTensor

open NodeCompletedLocalResiduePoint NodeCompletedLocalLocalizationPoint
  NodeCompletedLocalSelectedAffine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

attribute [local instance] NodeCompletedLocalMap.originalAlgebra baseFieldAlgebra

local notation "A" => S.presheaf.stalk (f x)
local notation "R" => X.presheaf.stalk x
local notation "V" => AffineFiber f x L
local notation "a" => pullback.fst (Spec.map (f.stalkMap x)) (localBaseMap f x L)
local notation "b" => pullback.snd (Spec.map (f.stalkMap x)) (localBaseMap f x L)

/-- The actual tensor ring of the ORIGINAL source and base stalks. -/
abbrev TensorRing := L ⊗[A] R

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The native actual affine pullback/tensor-spectrum isomorphism. -/
def tensorIso : V ≅ Spec (.of (TensorRing f x L)) :=
  NodeCompletedLocalAffineBaseChangeUV.actualTensorIso A R L

/-- Its whole ORIGINAL source-stalk projection is the literal right tensor inclusion. -/
theorem tensorIso_original :
    (tensorIso f x L).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (TensorRing f x L))) = a :=
  NodeCompletedLocalAffineBaseChangeUV.actualTensorIso_hom_original A R L

/-- Its whole external field projection is the literal left tensor inclusion. -/
theorem tensorIso_field :
    (tensorIso f x L).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap L (TensorRing f x L))) = b :=
  NodeCompletedLocalAffineBaseChangeUV.actualTensorIso_hom_field A R L

/-- The inverse retains the whole original stalk projection. -/
theorem tensorIso_inv_original :
    (tensorIso f x L).inv ≫ a = Spec.map (CommRingCat.ofHom
      (algebraMap R (TensorRing f x L))) := by
  rw [← tensorIso_original f x L, Iso.inv_hom_id_assoc]

/-- The inverse retains the whole external field projection. -/
theorem tensorIso_inv_field :
    (tensorIso f x L).inv ≫ b = Spec.map (CommRingCat.ofHom
      (algebraMap L (TensorRing f x L))) := by
  rw [← tensorIso_field f x L, Iso.inv_hom_id_assoc]

/-- The SAME prescribed original local coefficient map as an actual base-algebra homomorphism. -/
def originalEvaluation : R →ₐ[A] L where
  toRingHom := (algebraMap (X.residueField x) L).comp (X.residue x).hom
  commutes' _ := rfl

/-- The actual original tensor augmentation, constructed from the tensor universal property. -/
def augmentation : TensorRing f x L →ₐ[L] L :=
  AlgHom.liftEquiv A L R L (originalEvaluation f x L)

/-- Every original scalar and germ has precisely the prescribed original residue image. -/
theorem augmentation_tmul (l : L) (r : R) :
    augmentation f x L (l ⊗ₜ[A] r) =
      l * algebraMap (X.residueField x) L ((X.residue x) r) := rfl

/-- The whole original right-factor triangle retains the prescribed original point map. -/
theorem augmentation_original :
    (augmentation f x L).toRingHom.comp (algebraMap R (TensorRing f x L)) =
      (algebraMap (X.residueField x) L).comp (X.residue x).hom := by
  ext r
  change augmentation f x L ((1 : L) ⊗ₜ[A] r) = _
  rw [augmentation_tmul, one_mul]
  rfl

/-- The actual selected section on the SAME literal tensor spectrum. -/
def tensorSection : Spec (.of L) ⟶ Spec (.of (TensorRing f x L)) :=
  affineSection f x L ≫ (tensorIso f x L).hom

/-- The entire selected tensor section is exactly the ACTUAL augmentation spectrum map. -/
theorem tensorSection_eq :
    tensorSection f x L = Spec.map (CommRingCat.ofHom (augmentation f x L).toRingHom) := by
  apply (cancel_mono (tensorIso f x L).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, tensorIso_inv_original]
    rw [← Spec.map_comp]
    change tensorSection f x L ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (TensorRing f x L))) =
        Spec.map (CommRingCat.ofHom ((augmentation f x L).toRingHom.comp
          (algebraMap R (TensorRing f x L))))
    rw [augmentation_original]
    exact (by
      rw [tensorSection, Category.assoc, tensorIso_original, affineSection_local]
      rfl)
  · simp only [Category.assoc, tensorIso_inv_field]
    rw [← Spec.map_comp]
    change tensorSection f x L ≫ Spec.map (CommRingCat.ofHom
      (algebraMap L (TensorRing f x L))) =
        Spec.map (CommRingCat.ofHom ((augmentation f x L).toRingHom.comp
          (algebraMap L (TensorRing f x L))))
    have hc : (augmentation f x L).toRingHom.comp
        (algebraMap L (TensorRing f x L)) = RingHom.id L := by
      ext l
      exact (augmentation f x L).commutes l
    rw [hc, tensorSection, Category.assoc, tensorIso_field, affineSection_field]
    change 𝟙 (Spec (.of L)) = Spec.map (𝟙 (.of L))
    simp

/-- The SAME actual selected point, on the literal original-stalk tensor spectrum. -/
def tensorPoint : PrimeSpectrum (TensorRing f x L) :=
  tensorSection f x L (fieldPoint L)

/-- Its actual native prime ideal is the kernel of the SAME original augmentation. -/
theorem tensorPoint_asIdeal :
    (tensorPoint f x L).asIdeal = RingHom.ker (augmentation f x L).toRingHom := by
  rw [tensorPoint, tensorSection_eq]
  rfl

/-- The SAME literal tensor spectrum maps to the original actual geometric fibre. -/
def tensorToGeometric : Spec (.of (TensorRing f x L)) ⟶ SelectedFiber f x L :=
  (tensorIso f x L).inv ≫ affineMap f x L

/-- The entire ORIGINAL scheme projection retains the literal original stalk inclusion. -/
theorem tensorToGeometric_source :
    tensorToGeometric f x L ≫ pullback.fst f (selectedBaseMap f x L) =
      Spec.map (CommRingCat.ofHom (algebraMap R (TensorRing f x L))) ≫ X.fromSpecStalk x := by
  rw [tensorToGeometric, Category.assoc, affineMap_source, ← Category.assoc,
    tensorIso_inv_original]

/-- The entire external field projection is exactly the original left tensor inclusion. -/
theorem tensorToGeometric_field :
    tensorToGeometric f x L ≫ pullback.snd f (selectedBaseMap f x L) =
      Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L))) := by
  rw [tensorToGeometric, Category.assoc, affineMap_field, tensorIso_inv_field]

/-- The SAME actual tensor section maps to the original selected geometric section. -/
theorem tensorSection_geometric :
    tensorSection f x L ≫ tensorToGeometric f x L = selectedSection f x L := by
  rw [tensorSection, tensorToGeometric, Category.assoc, Iso.hom_inv_id_assoc,
    affineSection_geometric]

/-- The actual augmentation-kernel point maps to precisely the SAME original geometric point. -/
theorem tensorPoint_geometric :
    tensorToGeometric f x L (tensorPoint f x L) = selectedPoint f x L :=
  congrArg (fun k : Spec (.of L) ⟶ SelectedFiber f x L => k (fieldPoint L))
    (tensorSection_geometric f x L)

/-- Native completion under the same affine tensor isomorphism preserves the whole external field. -/
def completedTensorFieldEquiv (z : V) :
    letI := Scheme.completedLocalRingAlgebra
      (Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L)))) ((tensorIso f x L).hom z)
    letI := Scheme.completedLocalRingAlgebra b z
    (Spec (.of (TensorRing f x L))).completedLocalRing ((tensorIso f x L).hom z)
      ≃ₐ[L] (V).completedLocalRing z :=
  Scheme.completedLocalRingAlgEquivOfIsoOver (tensorIso f x L) b
    (Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L))))
    (tensorIso_field f x L) z

/-- The original geometric-to-affine completed equivalence has the SAME actual affine field action. -/
def completedGeometricFieldEquiv (z : V) :
    letI := Scheme.completedLocalRingAlgebra
      (pullback.snd f (selectedBaseMap f x L)) (affineMap f x L z)
    letI := Scheme.completedLocalRingAlgebra b z
    (SelectedFiber f x L).completedLocalRing (affineMap f x L z) ≃ₐ[L]
      (V).completedLocalRing z := by
  letI := Scheme.completedLocalRingAlgebra
    (pullback.snd f (selectedBaseMap f x L)) (affineMap f x L z)
  letI := Scheme.completedLocalRingAlgebra b z
  letI := NodeCompletedLocalSelectedAffine.actualStalkMap_isIso f x L z
  refine AlgEquiv.ofRingEquiv
    (f := Algebra.CompletionLocalMap.completionEquiv
      (asIso ((affineMap f x L).stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro l
  change Algebra.CompletionLocalMap.completionMap ((affineMap f x L).stalkMap z).hom
    (algebraMap _ (AdicCompletion _ _)
      (Scheme.baseToStalk (pullback.snd f (selectedBaseMap f x L)) (affineMap f x L z) l)) = _
  rw [Algebra.CompletionLocalMap.completionMap_algebraMap]
  have h := ConcreteCategory.congr_hom
    (Scheme.baseToStalk_comp_stalkMap (affineMap f x L)
      (pullback.snd f (selectedBaseMap f x L)) z) l
  rw [affineMap_field] at h
  exact congrArg (algebraMap ((V).presheaf.stalk z) ((V).completedLocalRing z)) h

/-- The actual SAME geometric point completion is the SAME actual literal tensor-point completion. -/
def geometricTensorCompletedEquiv (z : V) :
    letI := Scheme.completedLocalRingAlgebra
      (pullback.snd f (selectedBaseMap f x L)) (affineMap f x L z)
    letI := Scheme.completedLocalRingAlgebra
      (Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L)))) ((tensorIso f x L).hom z)
    (SelectedFiber f x L).completedLocalRing (affineMap f x L z) ≃ₐ[L]
      (Spec (.of (TensorRing f x L))).completedLocalRing ((tensorIso f x L).hom z) := by
  letI := Scheme.completedLocalRingAlgebra
    (pullback.snd f (selectedBaseMap f x L)) (affineMap f x L z)
  letI := Scheme.completedLocalRingAlgebra b z
  letI := Scheme.completedLocalRingAlgebra
    (Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L)))) ((tensorIso f x L).hom z)
  exact (completedGeometricFieldEquiv f x L z).trans (completedTensorFieldEquiv f x L z).symm

/-- EVERY original geometric local germ retains its SAME actual affine completion image. -/
theorem geometricTensorCompletedEquiv_original (z : V)
    (c : (SelectedFiber f x L).presheaf.stalk (affineMap f x L z)) :
    let := Scheme.completedLocalRingAlgebra
      (pullback.snd f (selectedBaseMap f x L)) (affineMap f x L z)
    let := Scheme.completedLocalRingAlgebra b z
    let := Scheme.completedLocalRingAlgebra
      (Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L)))) ((tensorIso f x L).hom z)
    completedTensorFieldEquiv f x L z
      (geometricTensorCompletedEquiv f x L z
        ((SelectedFiber f x L).toCompletedLocalRing (affineMap f x L z) c)) =
      (V).toCompletedLocalRing z ((affineMap f x L).stalkMap z c) := by
  let := Scheme.completedLocalRingAlgebra
    (pullback.snd f (selectedBaseMap f x L)) (affineMap f x L z)
  let := Scheme.completedLocalRingAlgebra b z
  let := Scheme.completedLocalRingAlgebra
    (Spec.map (CommRingCat.ofHom (algebraMap L (TensorRing f x L)))) ((tensorIso f x L).hom z)
  change completedTensorFieldEquiv f x L z
    ((completedTensorFieldEquiv f x L z).symm
      (completedGeometricFieldEquiv f x L z
        ((SelectedFiber f x L).toCompletedLocalRing (affineMap f x L z) c))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact Algebra.CompletionLocalMap.completionMap_algebraMap ((affineMap f x L).stalkMap z).hom c

end Hironaka.Geometry.NodeCompletedLocalSelectedTensor
