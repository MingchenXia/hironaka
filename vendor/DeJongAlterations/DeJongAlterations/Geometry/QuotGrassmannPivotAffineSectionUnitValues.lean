import DeJongAlterations.Geometry.QuotGrassmannPivotAffineSectionUnit

/-!
# Actual original one-tensor affine section readback

The whole native unit square is read at EVERY original section. The original
pushforward-section comparison is the literal original equality transport of
the top open; its value is computed directly from native actual definitions.
-/

noncomputable section

open scoped TensorProduct

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace DeJongAlterations.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original native pushforward-section comparison is literal original top-open equality transport. -/
theorem originalSpecPushforwardSectionsIso_apply {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (N : (Spec B).Modules)
    (m : moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj N)) :
    (originalSpecPushforwardSectionsIso φ).hom.app N m =
      N.presheaf.map (eqToHom (show (⊤ : (Spec B).Opens) =
        (Spec.map φ) ⁻¹ᵁ (⊤ : (Spec A).Opens) by simp)).op m := by
  rfl

/-- The actual pullback-unit section on the SAME original top open. -/
def originalSpecPullbackUnitTop {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M : (Spec A).Modules) (m : Γ(M, ⊤)) : Γ((pullback (Spec.map φ)).obj M, ⊤) :=
  ((pullback (Spec.map φ)).obj M).presheaf.map
    (eqToHom (show (⊤ : (Spec B).Opens) =
      (Spec.map φ) ⁻¹ᵁ (⊤ : (Spec A).Opens) by simp)).op
    (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).val.app (op ⊤) m)

/-- EVERY original section's one-tensor is carried to its literal actual native original pullback-unit section. -/
theorem originalSpecPullbackSectionsIso_one_tmul {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (M : (Spec A).Modules) [M.IsQuasicoherent] (m : Γ(M, ⊤)) :
    (originalSpecPullbackSectionsIso φ M).hom ((1 : B) ⊗ₜ[A] m) =
      originalSpecPullbackUnitTop φ M m := by
  have h := ConcreteCategory.congr_hom (originalSpecPullbackSectionsIso_unit φ M) m
  exact h.trans (originalSpecPushforwardSectionsIso_apply φ ((pullback (Spec.map φ)).obj M)
    (moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) m))

end DeJongAlterations.Geometry.QuotGrassmann
