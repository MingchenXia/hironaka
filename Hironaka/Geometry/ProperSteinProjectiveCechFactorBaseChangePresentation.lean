import Hironaka.Geometry.ProperSteinProjectiveCechFactorPresentation
import Hironaka.Geometry.ProperSteinGlobalSectionsFlatAffine

/-! # Original polynomial projective presentations of the SAME actual factor base changes

All pullback squares, closed immersions and structure triangles are internally
constructed from the original factor presentation and actual affine restriction.
No other project's imports or projectivity output certificates are used.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.FactorBaseChangePresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

section Cartesian
variable {B : Type u} [CommRing B] {X Y T : Scheme.{u}} {n : ℕ}
  (g : X ⟶ T) (e : X ⟶ RelativeChow.relativeSpace T n)
  (he : e ≫ RelativeChow.relativeStructure T n = g)
  (s : Y ⟶ X) (q : Y ⟶ Spec (.of B)) (b : Spec (.of B) ⟶ T)
  (H : IsPullback s q g b)

/-- The ORIGINAL affine Cartesian square constructs an actual polynomial projective map. -/
def affineCartesianEmbedding : Y ⟶ projectiveSpace B n :=
  (RelativeChow.affineProjectiveMap_isPullback b n).lift (s ≫ e) q
    (by rw [Category.assoc, he]; exact H.w)

/-- The WHOLE original structure map is retained exactly. -/
@[reassoc (attr := simp)]
theorem affineCartesianEmbedding_structure :
    affineCartesianEmbedding g e he s q b H ≫ projectiveSpaceStructure B n = q := by
  exact IsPullback.lift_snd _ _ _ _

/-- The actual source map back to the ORIGINAL relative closed presentation is retained. -/
@[reassoc (attr := simp)]
theorem affineCartesianEmbedding_original :
    affineCartesianEmbedding g e he s q b H ≫ RelativeChow.affineProjectiveMap b n = s ≫ e := by
  exact IsPullback.lift_fst _ _ _ _

/-- Actual pullback cancellation identifies the constructed map with the ORIGINAL closed-immersion base change. -/
theorem affineCartesianEmbedding_isPullback :
    IsPullback s (affineCartesianEmbedding g e he s q b H) e
      (RelativeChow.affineProjectiveMap b n) := by
  apply IsPullback.of_bot (v₂₁ := projectiveSpaceStructure B n)
    (v₂₂ := RelativeChow.relativeStructure T n) ?_
    (affineCartesianEmbedding_original g e he s q b H).symm
    (RelativeChow.affineProjectiveMap_isPullback b n)
  rw [affineCartesianEmbedding_structure, he]
  exact H

instance affineCartesianEmbedding_isClosedImmersion [IsClosedImmersion e] :
    IsClosedImmersion (affineCartesianEmbedding g e he s q b H) :=
  MorphismProperty.of_isPullback (affineCartesianEmbedding_isPullback g e he s q b H) inferInstance
end Cartesian

section Affine
variable {X T : Scheme.{u}} (g : X ⟶ T) (V : T.Opens) (hV : IsAffineOpen V)

/-- The ORIGINAL affine-coordinate restriction square is genuinely Cartesian, with its actual inverse affine isomorphism. -/
theorem affineRestriction_isPullback :
    IsPullback (g ⁻¹ᵁ V).ι ((g ∣_ V) ≫ hV.isoSpec.hom) g (hV.isoSpec.inv ≫ V.ι) := by
  apply (isPullback_morphismRestrict g V).flip.of_iso
    (Iso.refl _) (Iso.refl _) hV.isoSpec (Iso.refl _)
  all_goals simp

variable (B : Type u) [CommRing B] [Algebra Γ(T, V) B]

/-- EVERY actual original affine coefficient pullback is an actual pullback of the ORIGINAL whole morphism. -/
theorem affineBaseChange_isPullback :
    let q := (g ∣_ V) ≫ hV.isoSpec.hom
    IsPullback (ProperGeometricGlobalFunctions.firstProjection (S := B) q ≫ (g ⁻¹ᵁ V).ι)
      (ProperGeometricGlobalFunctions.structureMap (S := B) q) g
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, V) B)) ≫ hV.isoSpec.inv ≫ V.ι) := by
  exact (IsPullback.of_hasPullback _ _).paste_horiz (affineRestriction_isPullback g V hV)
end Affine

section Factor
variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f] [AlgebraicGeometry.IsNoetherian X]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hf : IsProper f) (hnormal : IsNormalScheme X) (hp : IsProjectiveOver (f ≫ p))
  (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V)
  (B : Type u) [CommRing B] [Algebra Γ(SteinCurveFactor.base f, V) B]

/-- ONLY original geometry constructs the closed polynomial embedding of the SAME actual base-changed factor. -/
def factorBaseChangeEmbedding :
    ProperGeometricGlobalFunctions.baseChange (S := B)
      (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV) ⟶
        projectiveSpace B (factorProjectiveDimension f hdim p hf hnormal hp) :=
  affineCartesianEmbedding (SteinCurveFactor.factor f hdim p hnormal)
    (factorProjectiveEmbedding f hdim p hf hnormal hp)
    (factorProjectiveEmbedding_structure f hdim p hf hnormal hp)
    _ _ _ (affineBaseChange_isPullback (SteinCurveFactor.factor f hdim p hnormal) V hV B)

instance factorBaseChangeEmbedding_isClosedImmersion :
    IsClosedImmersion (factorBaseChangeEmbedding f hdim p hf hnormal hp V hV B) := by
  unfold factorBaseChangeEmbedding
  infer_instance

/-- The ENTIRE actual original flat-model structure map is the actual embedding structure map. -/
@[reassoc (attr := simp)]
theorem factorBaseChangeEmbedding_structure :
    factorBaseChangeEmbedding f hdim p hf hnormal hp V hV B ≫ projectiveSpaceStructure B _ =
      ProperGeometricGlobalFunctions.structureMap (S := B)
        (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV) :=
  affineCartesianEmbedding_structure _ _ _ _ _ _ _

/-- The SAME actual original source retains its whole triangle to the ORIGINAL relative factor embedding. -/
@[reassoc (attr := simp)]
theorem factorBaseChangeEmbedding_original :
    factorBaseChangeEmbedding f hdim p hf hnormal hp V hV B ≫
      RelativeChow.affineProjectiveMap
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(SteinCurveFactor.base f, V) B)) ≫
          hV.isoSpec.inv ≫ V.ι) _ =
      (ProperGeometricGlobalFunctions.firstProjection (S := B)
        (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV) ≫
          (SteinCurveFactor.factor f hdim p hnormal ⁻¹ᵁ V).ι) ≫
            factorProjectiveEmbedding f hdim p hf hnormal hp :=
  affineCartesianEmbedding_original _ _ _ _ _ _ _

include hf hp

/-- Original absolute projectivity DERIVES polynomial projectivity of EVERY actual affine coefficient base change of the SAME factor. -/
theorem factorBaseChange_isProjective :
    IsProjectiveOver (ProperGeometricGlobalFunctions.structureMap (S := B)
      (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV)) :=
  ⟨_, factorBaseChangeEmbedding f hdim p hf hnormal hp V hV B, inferInstance,
    factorBaseChangeEmbedding_structure f hdim p hf hnormal hp V hV B⟩
end Factor
end Hironaka.Geometry.ProperSteinProjectiveCech.FactorBaseChangePresentation
