import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Finiteness of the actual constant field of a curve function field

The constants are the native relative algebraic closure in the original
ambient field. Polynomial evaluation and its injectivity are constructed
internally; no finite-constant-extension certificate is supplied.
-/

noncomputable section

open Polynomial IntermediateField

namespace DeJongAlterations.Algebra.SteinCurveConstants

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K F : Type u) [Field K] [Field F]
  [Algebra K F] [hKF : Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [hFF : FunctionField K F]

omit [FunctionField K F] in
/-- The actual image of the original rational-function variable is transcendental. -/
theorem parameter_transcendental :
    Transcendental K (algebraMap (RatFunc K) F (RatFunc.X : (RatFunc K))) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) F).injective).mpr
    RatFunc.transcendental_X

/-- The actual relative algebraic closure has finite degree over the original base. -/
theorem finite_constants : FiniteDimensional K (algebraicClosure K F) := by
  let C := algebraicClosure K F
  let t : F := algebraMap (RatFunc K) F (RatFunc.X : (RatFunc K))
  have ht : Transcendental C t := (parameter_transcendental K F).algebraicClosure
  let : Algebra K[X] F := ((algebraMap (RatFunc K) F).comp
    (algebraMap K[X] (RatFunc K))).toAlgebra
  let : IsScalarTower K[X] (RatFunc K) F := .of_algebraMap_eq' rfl
  let : FaithfulSMul K[X] F :=
    (faithfulSMul_iff_algebraMap_injective K[X] F).mpr
      ((algebraMap (RatFunc K) F).injective.comp (IsFractionRing.injective K[X] (RatFunc K)))
  let : Algebra C[X] F := (aeval t).toRingHom.toAlgebra
  let : FaithfulSMul C[X] F :=
    (faithfulSMul_iff_algebraMap_injective C[X] F).mpr
      (transcendental_iff_injective.mp ht)
  let : Algebra K[X] C[X] := Polynomial.algebra K C
  let : Algebra (RatFunc K) F := hKF
  let : IsScalarTower K[X] C[X] F := .of_algebraMap_eq fun p => by
    symm
    change ((aeval t : C[X] →ₐ[C] F).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap K C))) p =
      ((algebraMap (RatFunc K) F).comp (algebraMap K[X] (RatFunc K))) p
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom]
    change (aeval t : C[X] →ₐ[C] F) (Polynomial.map (algebraMap K C) p) = _
    rw [Polynomial.aeval_map_algebraMap]
    have he : (aeval t : K[X] →ₐ[K] F).toRingHom =
        (algebraMap (RatFunc K) F).comp (algebraMap K[X] (RatFunc K)) := by
      ext x
      · change (aeval t : K[X] →ₐ[K] F) (Polynomial.C x) = _
        rw [aeval_C]
        simpa only [RingHom.comp_apply, RatFunc.algebraMap_C,
          RatFunc.algebraMap_eq_C] using
          (IsScalarTower.algebraMap_apply K (RatFunc K) F x)
      · simp [t, RatFunc.algebraMap_X]
    exact RingHom.congr_fun he p
  have ha : RatFunc.liftAlgebra K F = hKF := by
    apply Algebra.algebra_ext
    intro r
    change (IsFractionRing.lift (FaithfulSMul.algebraMap_injective K[X] F)
      : RatFunc K →+* F) r = _
    exact RingHom.congr_fun (IsFractionRing.lift_unique
      (FaithfulSMul.algebraMap_injective K[X] F)
      (f := @algebraMap (RatFunc K) F _ _ hKF) (fun p => rfl)) r
  let : @FunctionField K F _ _ (RatFunc.liftAlgebra K F) := by
    rw [ha]
    exact hFF
  exact FunctionField.finiteDimensional_of_constantExtension (F := K)
    (E := C) F

omit [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] in
/-- Over the actual constant field there are no further algebraic constants. -/
theorem algebraicClosure_constants_eq_bot :
    algebraicClosure (algebraicClosure K F) F = ⊥ :=
  algebraicClosure.algebraicClosure_eq_bot K F

omit [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] in
/-- The actual constants are finite in every finitely generated extension of degree at most one. -/
theorem finite_constants_of_trdeg_le_one [Algebra.EssFiniteType K F]
    (htr : Algebra.trdeg K F ≤ 1) :
    FiniteDimensional K (algebraicClosure K F) := by
  by_cases halg : Algebra.IsAlgebraic K F
  · let := halg
    let : Module.Finite K F := Algebra.finite_of_essFiniteType_of_isAlgebraic
    infer_instance
  · obtain ⟨t, ht⟩ :=
      (Algebra.transcendental_iff_not_isAlgebraic.mpr halg).transcendental
    have hi : AlgebraicIndependent K (fun _ : ULift.{u} Unit => t) :=
      algebraicIndependent_unique_type_iff.mpr ht
    have hb := hi.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
    let : Algebra.IsAlgebraic K⟮t⟯ F := by
      have hr : Set.range (fun _ : ULift.{u} Unit => t) = {t} := by
        ext x
        simp
      have ha := hb.isAlgebraic_field
      rw [hr] at ha
      exact ha
    let : Algebra.EssFiniteType K⟮t⟯ F := .of_comp K _ _
    let : Module.Finite K⟮t⟯ F := Algebra.finite_of_essFiniteType_of_isAlgebraic
    let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
    let : Algebra (RatFunc K) K⟮t⟯ := e.toRingHom.toAlgebra
    let : Module.Finite (RatFunc K) K⟮t⟯ :=
      RingHom.Finite.of_surjective e.toRingHom e.surjective
    let : Algebra (RatFunc K) F :=
      (K⟮t⟯.val.toRingHom.comp e.toRingHom).toAlgebra
    let : IsScalarTower (RatFunc K) K⟮t⟯ F := .of_algebraMap_eq' rfl
    let : IsScalarTower K (RatFunc K) F := .of_algebraMap_eq fun x =>
      (congrArg (fun y : K⟮t⟯ => (y : F)) (e.commutes x)).symm
    let : FunctionField K F := Module.Finite.trans K⟮t⟯ F
    exact finite_constants K F

end DeJongAlterations.Algebra.SteinCurveConstants
