import Hironaka.Geometry.NodeCompletedLocalLocalizationPoint
import Hironaka.Geometry.NodeCompletedLocalAffineBaseChangeUV

/-! The literal original-stalk affine base change at the SAME prescribed geometric point. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeCompletedLocalSelectedAffine

open NodeCompletedLocalResiduePoint NodeCompletedLocalLocalizationPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

attribute [local instance] NodeCompletedLocalMap.originalAlgebra

/-- The literal original base stalk acts through the SAME specified original residue embedding. -/
@[instance_reducible]
def baseFieldAlgebra : Algebra (S.presheaf.stalk (f x)) L :=
  (((algebraMap (X.residueField x) L).comp (X.residue x).hom).comp
    (f.stalkMap x).hom).toAlgebra

attribute [local instance] baseFieldAlgebra

/-- The actual local-base morphism retains the full original local coefficient map. -/
def localBaseMap : Spec (.of L) ⟶ Spec (S.presheaf.stalk (f x)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x)) L))

/-- The whole local point/base triangle uses exactly the original scheme stalk map. -/
theorem localBaseMap_eq :
    localPointMap x L ≫ Spec.map (f.stalkMap x) = localBaseMap f x L := by
  rw [localPointMap, ← Spec.map_comp]
  rfl

/-- The selected actual geometric base map factors through the actual ORIGINAL base stalk. -/
theorem localBaseMap_source :
    localBaseMap f x L ≫ S.fromSpecStalk (f x) = selectedBaseMap f x L := by
  rw [← localBaseMap_eq, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc, localPointMap_source]
  rfl

/-- The literal affine pullback of the ORIGINAL local stalk map. -/
abbrev AffineFiber :=
  pullback (Spec.map (f.stalkMap x)) (localBaseMap f x L)

local notation "V" => AffineFiber f x L
local notation "Y" => SelectedFiber f x L
local notation "a" => pullback.fst (Spec.map (f.stalkMap x)) (localBaseMap f x L)
local notation "b" => pullback.snd (Spec.map (f.stalkMap x)) (localBaseMap f x L)
local notation "π" => pullback.fst f (selectedBaseMap f x L)
local notation "q" => pullback.snd f (selectedBaseMap f x L)

/-- The actual affine projections satisfy the SAME original geometric coefficient square. -/
theorem affine_condition :
    (a ≫ X.fromSpecStalk x) ≫ f = b ≫ selectedBaseMap f x L := by
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc, pullback.condition, Category.assoc, localBaseMap_source]

/-- The actual local affine pullback maps to the SAME actual selected geometric fibre. -/
def affineMap : V ⟶ Y :=
  pullback.lift (a ≫ X.fromSpecStalk x) b (affine_condition f x L)

/-- The whole original source projection is unchanged. -/
theorem affineMap_source : affineMap f x L ≫ π = a ≫ X.fromSpecStalk x :=
  pullback.lift_fst _ _ _

/-- The whole external field projection is unchanged. -/
theorem affineMap_field : affineMap f x L ≫ q = b :=
  pullback.lift_snd _ _ _

/-- This is internally the actual base change of the ORIGINAL source localization. -/
theorem affineMap_isPullback :
    IsPullback (affineMap f x L) a π (X.fromSpecStalk x) := by
  have hright : IsPullback (𝟙 (Spec (X.presheaf.stalk x))) (Spec.map (f.stalkMap x))
      (Spec.map (f.stalkMap x) ≫ S.fromSpecStalk (f x)) (S.fromSpecStalk (f x)) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hbig : IsPullback a b (X.fromSpecStalk x ≫ f) (selectedBaseMap f x L) := by
    simpa only [Category.comp_id, Scheme.SpecMap_stalkMap_fromSpecStalk,
      localBaseMap_source] using
        (IsPullback.of_hasPullback (Spec.map (f.stalkMap x))
          (localBaseMap f x L)).paste_horiz hright
  have houter : IsPullback a (affineMap f x L ≫ q)
      (X.fromSpecStalk x ≫ f) (selectedBaseMap f x L) := by
    rw [affineMap_field]
    exact hbig
  exact (IsPullback.of_bot houter (affineMap_source f x L).symm
    (IsPullback.of_hasPullback f (selectedBaseMap f x L))).flip

/-- The SAME prescribed residue embedding constructs the actual affine field section. -/
def affineSection : Spec (.of L) ⟶ V :=
  pullback.lift (localPointMap x L) (𝟙 _) (by simpa using localBaseMap_eq f x L)

/-- The prescribed original local-source map is retained in its entirety. -/
theorem affineSection_local : affineSection f x L ≫ a = localPointMap x L :=
  pullback.lift_fst _ _ _

/-- The whole original field section is the identity. -/
theorem affineSection_field : affineSection f x L ≫ b = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The affine section maps to the SAME original selected geometric section, not a replacement. -/
theorem affineSection_geometric :
    affineSection f x L ≫ affineMap f x L = selectedSection f x L := by
  apply pullback.hom_ext
  · rw [Category.assoc, affineMap_source, ← Category.assoc, affineSection_local,
      localPointMap_source, selectedSection_source]
  · rw [Category.assoc, affineMap_field, affineSection_field, selectedSection_field]

/-- The actual selected affine point. -/
def affinePoint : V := affineSection f x L (fieldPoint L)

/-- Its actual image is precisely the SAME originally selected geometric point. -/
theorem affinePoint_geometric :
    affineMap f x L (affinePoint f x L) = selectedPoint f x L :=
  congrArg (fun k : Spec (.of L) ⟶ Y => k (fieldPoint L)) (affineSection_geometric f x L)

/-- Native stalk preservation is derived from the ACTUAL original-localization Cartesian square. -/
theorem actualStalkMap_isIso (z : V) : IsIso ((affineMap f x L).stalkMap z) :=
  NodeCompletedLocalMap.isIso_stalkMap_of_isPullback_fromSpecStalk
    (affineMap_isPullback f x L) z

/-- The actual native stalk equivalence preserves the SAME whole external field. -/
def actualStalkEquiv (z : V) :
    letI := Scheme.stalkAlgebra q (affineMap f x L z)
    letI := Scheme.stalkAlgebra (affineMap f x L ≫ q) z
    (Y).presheaf.stalk (affineMap f x L z) ≃ₐ[L] (V).presheaf.stalk z := by
  letI := Scheme.stalkAlgebra q (affineMap f x L z)
  letI := Scheme.stalkAlgebra (affineMap f x L ≫ q) z
  letI := actualStalkMap_isIso f x L z
  refine AlgEquiv.ofRingEquiv
    (f := (asIso ((affineMap f x L).stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro l
  exact ConcreteCategory.congr_hom
    (Scheme.baseToStalk_comp_stalkMap (affineMap f x L) q z) l

/-- Every geometric germ has exactly its actual native image. -/
theorem actualStalkEquiv_original (z : V) (c : (Y).presheaf.stalk (affineMap f x L z)) :
    letI := Scheme.stalkAlgebra q (affineMap f x L z)
    letI := Scheme.stalkAlgebra (affineMap f x L ≫ q) z
    actualStalkEquiv f x L z c = (affineMap f x L).stalkMap z c := rfl

/-- The same native affine comparison induces an actual completed external-field equivalence. -/
def actualCompletedEquiv (z : V) :
    letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
    letI := Scheme.completedLocalRingAlgebra (affineMap f x L ≫ q) z
    (Y).completedLocalRing (affineMap f x L z) ≃ₐ[L] (V).completedLocalRing z := by
  letI := Scheme.stalkAlgebra q (affineMap f x L z)
  letI := Scheme.stalkAlgebra (affineMap f x L ≫ q) z
  letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
  letI := Scheme.completedLocalRingAlgebra (affineMap f x L ≫ q) z
  letI := actualStalkMap_isIso f x L z
  refine AlgEquiv.ofRingEquiv
    (f := Algebra.CompletionLocalMap.completionEquiv
      (asIso ((affineMap f x L).stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro l
  change Algebra.CompletionLocalMap.completionMap ((affineMap f x L).stalkMap z).hom
    (algebraMap ((Y).presheaf.stalk (affineMap f x L z))
      ((Y).completedLocalRing (affineMap f x L z))
      (Scheme.baseToStalk q (affineMap f x L z) l)) = _
  rw [Algebra.CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap ((V).presheaf.stalk z) ((V).completedLocalRing z))
    (ConcreteCategory.congr_hom
      (Scheme.baseToStalk_comp_stalkMap (affineMap f x L) q z) l)

/-- Its ENTIRE forward map is the canonical completion of this SAME native stalk map. -/
theorem actualCompletedEquiv_toRingHom (z : V) :
    letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
    letI := Scheme.completedLocalRingAlgebra (affineMap f x L ≫ q) z
    (actualCompletedEquiv f x L z).toRingHom =
      NodeCompletedLocalMap.completedMap (affineMap f x L) z := rfl

/-- Every original geometric germ retains the actual affine-stalk completion image. -/
theorem actualCompletedEquiv_original (z : V) (c : (Y).presheaf.stalk (affineMap f x L z)) :
    letI := Scheme.completedLocalRingAlgebra q (affineMap f x L z)
    letI := Scheme.completedLocalRingAlgebra (affineMap f x L ≫ q) z
    actualCompletedEquiv f x L z ((Y).toCompletedLocalRing (affineMap f x L z) c) =
      (V).toCompletedLocalRing z ((affineMap f x L).stalkMap z c) :=
  Algebra.CompletionLocalMap.completionMap_algebraMap ((affineMap f x L).stalkMap z).hom c

end Hironaka.Geometry.NodeCompletedLocalSelectedAffine
