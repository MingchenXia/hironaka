import Hironaka.Geometry.CurveFibrationBaseChangeProjective
import Hironaka.Geometry.SteinCurveFactor

/-!
# The SAME original intrinsic Stein factor has its actual relative closed presentation

Original absolute projectivity and internally proved properness produce the
actual relative closed embedding, with both original coefficient triangles.
The previously general proper/global-section identity is not narrowed.
-/

universe u
open CategoryTheory AlgebraicGeometry
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f] [AlgebraicGeometry.IsNoetherian X]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hf : IsProper f) (hnormal : IsNormalScheme X) (hp : IsProjectiveOver (f ≫ p))

include hf hp

/-- Original absolute projectivity yields a genuine relative embedding of the SAME actual factor. -/
theorem factorRelativeEmbedding_exists :
    ∃ (n : ℕ) (e : X ⟶ RelativeChow.relativeSpace (SteinCurveFactor.base f) n),
      IsClosedImmersion e ∧ e ≫ RelativeChow.relativeStructure _ n =
        SteinCurveFactor.factor f hdim p hnormal := by
  let := SteinCurveFactor.factor_isProper f hdim p hf hnormal
  apply CurveFibrationBaseChange.exists_relativeEmbedding_of_isProjective
    (SteinCurveFactor.baseMap f ≫ p) (SteinCurveFactor.factor f hdim p hnormal)
  simpa only [← Category.assoc, SteinCurveFactor.factor_structure] using hp

/-- The actual dimension chosen from the internally produced SAME-factor embedding. -/
def factorProjectiveDimension : ℕ :=
  (factorRelativeEmbedding_exists f hdim p hf hnormal hp).choose

/-- The actual ORIGINAL source embeds closed into projective space over its SAME intrinsic factor base. -/
def factorProjectiveEmbedding :
    X ⟶ RelativeChow.relativeSpace (SteinCurveFactor.base f)
      (factorProjectiveDimension f hdim p hf hnormal hp) :=
  (factorRelativeEmbedding_exists f hdim p hf hnormal hp).choose_spec.choose

instance factorProjectiveEmbedding_isClosedImmersion :
    IsClosedImmersion (factorProjectiveEmbedding f hdim p hf hnormal hp) :=
  (factorRelativeEmbedding_exists f hdim p hf hnormal hp).choose_spec.choose_spec.1

@[reassoc]
theorem factorProjectiveEmbedding_structure :
    factorProjectiveEmbedding f hdim p hf hnormal hp ≫ RelativeChow.relativeStructure _ _ =
      SteinCurveFactor.factor f hdim p hnormal :=
  (factorRelativeEmbedding_exists f hdim p hf hnormal hp).choose_spec.choose_spec.2

@[reassoc]
theorem factorProjectiveEmbedding_originalBase :
    factorProjectiveEmbedding f hdim p hf hnormal hp ≫ RelativeChow.relativeStructure _ _ ≫
      SteinCurveFactor.baseMap f = f := by
  rw [← Category.assoc, factorProjectiveEmbedding_structure, SteinCurveFactor.factor_structure]

/-- The SAME actual embedding retains the ORIGINAL coefficient structure, rather than a new one. -/
theorem factorProjectiveEmbedding_originalCoefficients :
    factorProjectiveEmbedding f hdim p hf hnormal hp ≫ RelativeChow.relativeStructure _ _ ≫
      SteinCurveFactor.baseMap f ≫ p = f ≫ p := by
  rw [← Category.assoc, ← Category.assoc, factorProjectiveEmbedding_structure,
    SteinCurveFactor.factor_structure]

end
end Hironaka.Geometry.ProperSteinProjectiveCech
