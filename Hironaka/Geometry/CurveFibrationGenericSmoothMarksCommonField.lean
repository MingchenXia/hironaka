import Hironaka.Geometry.CurveFibrationGenericSmoothMarksPoints
import Hironaka.Algebra.FiniteSeparableSplitting

/-! One genuinely constructed finite Galois field for the original three smooth marks. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
universe u

namespace Hironaka.Geometry.CurveFibrationGenericSmoothMarks

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- The literal pullback lift of the original field-valued point. -/
def scalarPoint (p : C ⟶ Spec (.of k)) {L : Type u} [Field L] [Algebra k L]
    (q : Spec (.of L) ⟶ C)
    (hq : q ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    Spec (.of L) ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  pullback.lift q (𝟙 _) (by simpa only [Category.id_comp] using hq)

/-- The WHOLE original point map is the first actual projection. -/
theorem scalarPoint_original (p : C ⟶ Spec (.of k)) {L : Type u} [Field L] [Algebra k L]
    (q : Spec (.of L) ⟶ C)
    (hq : q ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    scalarPoint p q hq ≫ pullback.fst _ _ = q := pullback.lift_fst _ _ _

/-- The WHOLE original field action is the second actual projection. -/
theorem scalarPoint_structure (p : C ⟶ Spec (.of k)) {L : Type u} [Field L] [Algebra k L]
    (q : Spec (.of L) ⟶ C)
    (hq : q ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    scalarPoint p q hq ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

/-- The SAME actual pullback point has precisely its original underlying image. -/
theorem scalarPoint_underlying (p : C ⟶ Spec (.of k)) {L : Type u} [Field L] [Algebra k L]
    (q : Spec (.of L) ⟶ C)
    (hq : q ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (scalarPoint p q hq (⊥ : PrimeSpectrum L)) = q (⊥ : PrimeSpectrum L) :=
  congrArg (fun f : Spec (.of L) ⟶ C => f (⊥ : PrimeSpectrum L))
    (scalarPoint_original p q hq)

/-- The actual original finite separable points acquire ONE internally constructed
finite Galois field, preserving original underlying images and literal rational lifts. -/
theorem exists_common_field_points (p : C ⟶ Spec (.of k)) (U : C.Opens)
    (z : Fin 3 → Point p U) (hz : Function.Injective (fun i => point (z i))) :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧ IsGalois k L ∧
      ∃ q : Fin 3 → (Spec (.of L) ⟶ C),
        ∃ hq : ∀ i, q i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L)),
          (∀ i, q i (⊥ : PrimeSpectrum L) ∈ U) ∧
          Function.Injective (fun i => q i (⊥ : PrimeSpectrum L)) ∧
          Function.Injective (fun i => scalarPoint p (q i) (hq i) (⊥ : PrimeSpectrum L)) := by
  let E (i : ULift.{u} (Fin 3)) : Type u := (z i.down).extension
  let (i : ULift.{u} (Fin 3)) : FiniteDimensional k (E i) := (z i.down).finite
  let (i : ULift.{u} (Fin 3)) : Algebra.IsSeparable k (E i) := (z i.down).separable
  let L := Algebra.FiniteSeparableSplitting.commonField k E
  let χ (i : Fin 3) := Algebra.FiniteSeparableSplitting.embedding k E (ULift.up i)
  let q (i : Fin 3) : Spec (.of L) ⟶ C :=
    Spec.map (CommRingCat.ofHom (χ i).toRingHom) ≫ (z i).map
  have hq (i : Fin 3) : q i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    dsimp only [q]
    rw [Category.assoc, (z i).over, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => (χ i).commutes a)
  have hpoint (i : Fin 3) : q i (⊥ : PrimeSpectrum L) = point (z i) := by
    change (z i).map ((Spec.map (CommRingCat.ofHom (χ i).toRingHom)) (⊥ : PrimeSpectrum L)) = _
    exact congrArg (z i).map (Subsingleton.elim _ _)
  have hinj : Function.Injective (fun i => q i (⊥ : PrimeSpectrum L)) := by
    intro i j hij
    exact hz (by simpa only [hpoint] using hij)
  refine ⟨L, inferInstance, inferInstance, q, hq, ?_, hinj, ?_⟩
  · intro i
    rw [hpoint]
    exact (z i).mem_open
  · intro i j hij
    apply hinj
    have hf := congrArg
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) hij
    simpa only [scalarPoint_underlying] using hf

/-- ONLY original positive-dimensional proper integral geometry and the SAME
specified smooth open produce three distinct marks over ONE finite Galois field. -/
theorem exists_three_common_field_points [IsIntegral C]
    (p : C ⟶ Spec (.of k)) [IsProper p] (hdim : 0 < topologicalKrullDim C)
    (U : C.Opens) (hU : (U : Set C).Nonempty) [Smooth (U.ι ≫ p)] :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧ IsGalois k L ∧
      ∃ q : Fin 3 → (Spec (.of L) ⟶ C),
        ∃ hq : ∀ i, q i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L)),
          (∀ i, q i (⊥ : PrimeSpectrum L) ∈ U) ∧
          Function.Injective (fun i => q i (⊥ : PrimeSpectrum L)) ∧
          Function.Injective (fun i => scalarPoint p (q i) (hq i) (⊥ : PrimeSpectrum L)) := by
  obtain ⟨z, hz⟩ := exists_three_distinct_points p hdim U hU
  exact exists_common_field_points p U z hz

end Hironaka.Geometry.CurveFibrationGenericSmoothMarks
