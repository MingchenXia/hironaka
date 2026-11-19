import Hironaka.Geometry.NodeCompletedLocalResiduePoint
import Hironaka.Geometry.NodeCompletedLocalFiberStalk

/-! ACTUAL base change of the original source localization at the SAME selected
geometric point. Native stalk maps and native completion maps, over the whole L. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeCompletedLocalLocalizationPoint

open NodeCompletedLocalResiduePoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

/-- The prescribed original residue embedding as an ACTUAL original local-source map. -/
def localPointMap : Spec (.of L) ⟶ Spec (X.presheaf.stalk x) :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (X.residueField x) L).comp (X.residue x).hom))

/-- The ENTIRE chosen original point map factors through its SAME actual original localization. -/
theorem localPointMap_source :
    localPointMap x L ≫ X.fromSpecStalk x = sourcePointMap x L := by
  change Spec.map (X.residue x ≫ CommRingCat.ofHom (algebraMap (X.residueField x) L)) ≫
    X.fromSpecStalk x = _
  rw [Spec.map_comp, Category.assoc]
  rfl

local notation "Y" => SelectedFiber f x L
local notation "π" => pullback.fst f (selectedBaseMap f x L)
local notation "q" => pullback.snd f (selectedBaseMap f x L)

/-- The SAME actual base change of the ORIGINAL scheme localization, not an abstract ring. -/
abbrev LocalizedFiber := pullback π (X.fromSpecStalk x)

local notation "W" => LocalizedFiber f x L
local notation "g" => pullback.fst π (X.fromSpecStalk x)
local notation "h" => pullback.snd π (X.fromSpecStalk x)

/-- The SAME prescribed selected field section lifts internally to the actual localization. -/
def localSection : Spec (.of L) ⟶ W :=
  pullback.lift (selectedSection f x L) (localPointMap x L)
    ((selectedSection_source f x L).trans (localPointMap_source x L).symm)

/-- The WHOLE original geometric projection retains the SAME selected field section. -/
theorem localSection_source : localSection f x L ≫ g = selectedSection f x L :=
  pullback.lift_fst _ _ _

/-- The WHOLE original local-source projection retains the prescribed actual local map. -/
theorem localSection_local : localSection f x L ≫ h = localPointMap x L :=
  pullback.lift_snd _ _ _

/-- The ENTIRE actual field projection of this SAME lifted section is the identity. -/
theorem localSection_field : localSection f x L ≫ (g ≫ q) = 𝟙 _ := by
  rw [← Category.assoc, localSection_source, selectedSection_field]

/-- The actual selected point of the SAME localization pullback. -/
def localPoint : W := localSection f x L (fieldPoint L)

/-- Its actual projection is exactly the ORIGINAL selected geometric point. -/
theorem localPoint_source : g (localPoint f x L) = selectedPoint f x L :=
  congrArg (fun k : Spec (.of L) ⟶ Y => k (fieldPoint L)) (localSection_source f x L)

/-- Native stalk preservation is internally DERIVED for EVERY actual localization point. -/
theorem actualStalkMap_isIso (z : W) : IsIso ((g).stalkMap z) :=
  NodeCompletedLocalMap.isIso_stalkMap_of_isPullback_fromSpecStalk
    (IsPullback.of_hasPullback π (X.fromSpecStalk x)) z

/-- The ACTUAL localization stalk equivalence preserves the ENTIRE external field. -/
def actualStalkEquiv (z : W) :
    letI := Scheme.stalkAlgebra q (g z)
    letI := Scheme.stalkAlgebra (g ≫ q) z
    (Y).presheaf.stalk (g z) ≃ₐ[L] (W).presheaf.stalk z := by
  letI := Scheme.stalkAlgebra q (g z)
  letI := Scheme.stalkAlgebra (g ≫ q) z
  letI := actualStalkMap_isIso f x L z
  refine AlgEquiv.ofRingEquiv (f := (asIso ((g).stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro a
  exact ConcreteCategory.congr_hom (Scheme.baseToStalk_comp_stalkMap g q z) a

/-- Every original geometric local germ has precisely its ACTUAL native stalk image. -/
theorem actualStalkEquiv_original (z : W) (a : (Y).presheaf.stalk (g z)) :
    letI := Scheme.stalkAlgebra q (g z)
    letI := Scheme.stalkAlgebra (g ≫ q) z
    actualStalkEquiv f x L z a = (g).stalkMap z a := rfl

/-- The SAME actual original localization map induces a genuine completed L-equivalence. -/
def actualCompletedEquiv (z : W) :
    letI := Scheme.completedLocalRingAlgebra q (g z)
    letI := Scheme.completedLocalRingAlgebra (g ≫ q) z
    (Y).completedLocalRing (g z) ≃ₐ[L] (W).completedLocalRing z := by
  letI := Scheme.stalkAlgebra q (g z)
  letI := Scheme.stalkAlgebra (g ≫ q) z
  letI := Scheme.completedLocalRingAlgebra q (g z)
  letI := Scheme.completedLocalRingAlgebra (g ≫ q) z
  letI := actualStalkMap_isIso f x L z
  refine AlgEquiv.ofRingEquiv
    (f := Algebra.CompletionLocalMap.completionEquiv
      (asIso ((g).stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro a
  change Algebra.CompletionLocalMap.completionMap ((g).stalkMap z).hom
    (algebraMap ((Y).presheaf.stalk (g z)) ((Y).completedLocalRing (g z))
      (Scheme.baseToStalk q (g z) a)) = _
  rw [Algebra.CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap ((W).presheaf.stalk z) ((W).completedLocalRing z))
    (ConcreteCategory.congr_hom (Scheme.baseToStalk_comp_stalkMap g q z) a)

/-- The WHOLE actual completed map is the canonical completed native scheme stalk map. -/
theorem actualCompletedEquiv_toRingHom (z : W) :
    letI := Scheme.completedLocalRingAlgebra q (g z)
    letI := Scheme.completedLocalRingAlgebra (g ≫ q) z
    (actualCompletedEquiv f x L z).toRingHom = NodeCompletedLocalMap.completedMap g z := rfl

/-- EVERY original geometric germ retains its SAME actual local-completion image. -/
theorem actualCompletedEquiv_original (z : W) (a : (Y).presheaf.stalk (g z)) :
    letI := Scheme.completedLocalRingAlgebra q (g z)
    letI := Scheme.completedLocalRingAlgebra (g ≫ q) z
    actualCompletedEquiv f x L z ((Y).toCompletedLocalRing (g z) a) =
      (W).toCompletedLocalRing z ((g).stalkMap z a) :=
  Algebra.CompletionLocalMap.completionMap_algebraMap ((g).stalkMap z).hom a

end Hironaka.Geometry.NodeCompletedLocalLocalizationPoint
