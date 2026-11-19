import Hironaka.Geometry.AlgebraicFieldFiniteModel

/-! The WHOLE original scalar arrow is internally modeled over ONE actual finite field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.AlgebraicFieldFiniteArrowModel

open StableModification.Limits AlgebraicFieldFiniteModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

/-- Original actual FP schemes and their ENTIRE original arrow internally produce ONE finite
field, BOTH canonical scalar models, the actual arrow model and EVERY coefficient triangle. -/
theorem exists_finite_field_arrow_model {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (.of L)) (q : Z ⟶ Spec (.of L))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    (a : Y ⟶ Z) (ha : a ≫ q = p) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ (Y₀ Z₀ : Scheme.{u}) (p₀ : Y₀ ⟶ Spec (.of E)) (q₀ : Z₀ ⟶ Spec (.of E))
        (gY : Y ⟶ Y₀) (gZ : Z ⟶ Z₀) (a₀ : Y₀ ⟶ Z₀),
        LocallyOfFinitePresentation p₀ ∧ QuasiCompact p₀ ∧ QuasiSeparated p₀ ∧
        LocallyOfFinitePresentation q₀ ∧ QuasiCompact q₀ ∧ QuasiSeparated q₀ ∧
        IsPullback gY p p₀ (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        IsPullback gZ q q₀ (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        a₀ ≫ q₀ = p₀ ∧ gY ≫ a₀ = a ≫ gZ ∧ IsPullback gY a a₀ gZ ∧
        (gY ≫ p₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
          p ≫ Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
        gZ ≫ q₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
          q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  obtain ⟨i, mY, hmY⟩ := exists_model (isLimitScalarCone k L) p
  obtain ⟨j, mZ, hmZ⟩ := exists_model (isLimitScalarCone k L) q
  let gY := IsCofiltered.minToLeft i j
  let gZ := IsCofiltered.minToRight i j
  let rY := mY.baseChange gY
  let rZ := mZ.baseChange gZ
  have hrY : rY.IsFP := hmY.baseChange gY
  have hrZ : rZ.IsFP := hmZ.baseChange gZ
  let : QuasiCompact rY.fY := hrY.2.1
  let : QuasiSeparated rY.fY := hrY.2.2
  let : LocallyOfFinitePresentation rZ.fY := hrZ.1
  obtain ⟨l, b, hb, hb'⟩ := exists_hom_of_isPullback (diagram k L) (scalarCone k L)
    (isLimitScalarCone k L) rY.fY rZ.fY rY.isPullback (a ≫ rZ.g) (by
      rw [Category.assoc, rZ.isPullback.w, ← Category.assoc, ha, rY.isPullback.w])
  let sY := rY.baseChange l.hom
  let sZ := rZ.baseChange l.hom
  have hsY : sY.IsFP := hrY.baseChange l.hom
  have hsZ : sZ.IsFP := hrZ.baseChange l.hom
  let a₀ : sY.Y ⟶ sZ.Y := pullback.lift b (pullback.snd _ _) (by rw [hb, pullback.condition])
  have ha₀ : a₀ ≫ sZ.fY = sY.fY := pullback.lift_snd _ _ _
  have hga : sY.g ≫ a₀ = a ≫ sZ.g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, a₀, pullback.lift_fst]
      exact hb'.trans (by simp [sZ, Model.baseChange])
    · simp [a₀, sY, sZ, Model.baseChange, reassoc_of% ha]
  have Hmap : IsPullback sY.g a a₀ sZ.g := by
    refine IsPullback.of_bot ?_ hga sZ.isPullback
    simpa only [ha, ha₀] using sY.isPullback
  have HY := sY.isPullback
  have HZ := sZ.isPullback
  rw [scalarCone_π] at HY HZ
  refine ⟨levelField k L l.left, levelField_finiteDimensional k L l.left,
    sY.Y, sZ.Y, sY.fY, sZ.fY, sY.g, sZ.g, a₀,
    hsY.1, hsY.2.1, hsY.2.2, hsZ.1, hsZ.2.1, hsZ.2.2, HY, HZ, ha₀, hga, Hmap, ?_, ?_⟩
  · rw [HY.w_assoc, levelField_coefficient_triangle]
  · rw [HZ.w_assoc, levelField_coefficient_triangle]

end Hironaka.Geometry.AlgebraicFieldFiniteArrowModel
