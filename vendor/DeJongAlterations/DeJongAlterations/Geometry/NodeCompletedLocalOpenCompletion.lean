import DeJongAlterations.Geometry.NodeCompletedLocalMap
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! Canonical ORIGINAL field-coefficient stalk/completion maps of an ACTUAL open immersion.
No Noetherianity, nodal model, residue-field identification, or output-map certificate is input. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalOpenCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [CommRing K] {X Y : Scheme.{u}}
  (j : X ⟶ Y) [IsOpenImmersion j] (q : Y ⟶ Spec (.of K)) (z : X)

/-- The ACTUAL open-immersion stalk map is an equivalence for the ENTIRE original base action. -/
def stalkEquiv :
    letI := Scheme.stalkAlgebra q (j z)
    letI := Scheme.stalkAlgebra (j ≫ q) z
    Y.presheaf.stalk (j z) ≃ₐ[K] X.presheaf.stalk z := by
  letI := Scheme.stalkAlgebra q (j z)
  letI := Scheme.stalkAlgebra (j ≫ q) z
  refine AlgEquiv.ofRingEquiv (f := (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro k
  change j.stalkMap z (Scheme.baseToStalk q (j z) k) = Scheme.baseToStalk (j ≫ q) z k
  exact ConcreteCategory.congr_hom (Scheme.baseToStalk_comp_stalkMap j q z) k

/-- Every original target germ has exactly its ACTUAL native open-immersion stalk image. -/
theorem stalkEquiv_original (a : Y.presheaf.stalk (j z)) :
    letI := Scheme.stalkAlgebra q (j z)
    letI := Scheme.stalkAlgebra (j ≫ q) z
    stalkEquiv K j q z a = j.stalkMap z a := by
  rfl

/-- The ACTUAL canonical completion map is an equivalence over the WHOLE original base. -/
def completedEquiv :
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra (j ≫ q) z
    Y.completedLocalRing (j z) ≃ₐ[K] X.completedLocalRing z := by
  letI := Scheme.stalkAlgebra q (j z)
  letI := Scheme.stalkAlgebra (j ≫ q) z
  letI := Scheme.completedLocalRingAlgebra q (j z)
  letI := Scheme.completedLocalRingAlgebra (j ≫ q) z
  refine AlgEquiv.ofRingEquiv
    (f := Algebra.CompletionLocalMap.completionEquiv (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro k
  change Algebra.CompletionLocalMap.completionMap (j.stalkMap z).hom
      (algebraMap (Y.presheaf.stalk (j z)) (Y.completedLocalRing (j z)) (Scheme.baseToStalk q (j z) k)) =
    algebraMap (X.presheaf.stalk z) (X.completedLocalRing z) (Scheme.baseToStalk (j ≫ q) z k)
  rw [Algebra.CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap (X.presheaf.stalk z) (X.completedLocalRing z))
    (ConcreteCategory.congr_hom (Scheme.baseToStalk_comp_stalkMap j q z) k)

/-- Every ORIGINAL target germ retains its native actual image in the SAME completion. -/
theorem completedEquiv_original (a : Y.presheaf.stalk (j z)) :
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra (j ≫ q) z
    completedEquiv K j q z (Y.toCompletedLocalRing (j z) a) =
      X.toCompletedLocalRing z (j.stalkMap z a) := by
  exact Algebra.CompletionLocalMap.completionMap_algebraMap (j.stalkMap z).hom a

/-- The underlying WHOLE completed ring map is literally the ACTUAL induced scheme map. -/
theorem completedEquiv_toRingHom :
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra (j ≫ q) z
    (completedEquiv K j q z).toRingHom = NodeCompletedLocalMap.completedMap j z := by
  rfl

/-- Variant with the separately named ACTUAL original source base morphism and its
proved WHOLE coefficient triangle, preserving the SAME underlying native stalk map. -/
def stalkEquivOver (p : X ⟶ Spec (.of K)) (h : j ≫ q = p) :
    letI := Scheme.stalkAlgebra q (j z)
    letI := Scheme.stalkAlgebra p z
    Y.presheaf.stalk (j z) ≃ₐ[K] X.presheaf.stalk z := by
  subst p
  exact stalkEquiv K j q z

/-- Variant with the separately named ACTUAL original source base morphism and its
proved WHOLE coefficient triangle, preserving the SAME underlying native completed map. -/
def completedEquivOver (p : X ⟶ Spec (.of K)) (h : j ≫ q = p) :
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra p z
    Y.completedLocalRing (j z) ≃ₐ[K] X.completedLocalRing z := by
  subst p
  exact completedEquiv K j q z

/-- Retaining a separately named base morphism does not change the ACTUAL whole completed map. -/
theorem completedEquivOver_toRingHom (p : X ⟶ Spec (.of K)) (h : j ≫ q = p) :
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra p z
    (completedEquivOver K j q z p h).toRingHom = NodeCompletedLocalMap.completedMap j z := by
  subst p
  rfl

end DeJongAlterations.Geometry.NodeCompletedLocalOpenCompletion
