import DeJongAlterations.StableModification.Projectivity.LineBundleOps

/-! # Whole native comparison of a line-bundle power with its original twist -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace DeJongAlterations.StableModificationBridge.LineBundlePowerComparison

open StableModification.Projectivity

universe u

variable {X : Scheme.{u}} (L : LineBundleData X) (F : X.Modules) (m : ℤ)

/-- The entire original compatible family, viewed with the original exponent. -/
def powerTwistHom : (L.pow m).twist F 1 ⟶ L.twist F m where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun t => ⟨t.1, by
            intro i j
            simpa only [LineBundleData.transPow_pow, mul_one] using t.2 i j⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality := fun {_ _} _ => by
        ext t
        rfl }
    (fun _ _ _ => rfl)

instance : IsIso (powerTwistHom L F m) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro s t h
    exact Subtype.ext (congrArg (fun z : L.twistSubgroup F m W => z.1) h)
  · intro t
    refine ⟨⟨t.1, ?_⟩, rfl⟩
    intro i j
    simpa only [LineBundleData.transPow_pow, mul_one] using t.2 i j

/-- The native module `(L^m)^1 ⊗ F` is the whole original native twist `L^m ⊗ F`. -/
def powerTwistIso : (L.pow m).twist F 1 ≅ L.twist F m :=
  asIso (powerTwistHom L F m)

end DeJongAlterations.StableModificationBridge.LineBundlePowerComparison
