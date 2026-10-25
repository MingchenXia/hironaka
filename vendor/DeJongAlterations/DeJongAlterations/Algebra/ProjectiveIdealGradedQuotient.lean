/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
/- Reused from EnvelopeProperty/GradedQuotient.lean; SHA256 544fbab3417f233fc9cafd82aaa2aadb55c14668648205b2fd20e7d1ee7ba6f6. -/


/-!
# Genuine grading of homogeneous ideal quotients

For an arbitrary commutative coefficient ring and additive grading monoid,
the actual images of the homogeneous components form a genuine internal
grading on the actual homogeneous ideal quotient. The canonical quotient map
is graded and has same-degree lifts. Natural-number gradings also retain the
actual irrelevant ideal image. No radical replacement or reducedness, field,
Noetherianity or finite-generation hypothesis is used. The scheme quotient
closed immersion and its ideal sheaf are separate constructions.
-/

open scoped DirectSum
open DirectSum
noncomputable section
namespace DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [DecidableEq ι] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- The genuine quotient homogeneous component is the actual image of the original component. -/
def grading (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap

/-- The original quotient map on a homogeneous component, preserving its actual degree. -/
def componentMap (i : ι) : 𝒜 i →+ grading 𝒜 I i where
  toFun a := ⟨Ideal.Quotient.mk I a, Submodule.mem_map.mpr ⟨a, a.2, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add (Ideal.Quotient.mk I) (a : A) (b : A))

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- Every whole component value is the original quotient class. -/
@[simp]
theorem componentMap_coe (i : ι) (a : 𝒜 i) :
    (componentMap 𝒜 I i a : A ⧸ I) = Ideal.Quotient.mk I a := rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- Every genuine quotient homogeneous element has an actual same-degree homogeneous lift. -/
theorem componentMap_surjective (i : ι) : Function.Surjective (componentMap 𝒜 I i) := by
  intro q
  obtain ⟨a, ha, hq⟩ := Submodule.mem_map.mp q.2
  exact ⟨⟨a, ha⟩, Subtype.ext hq⟩

/-- The actual quotient-component images have genuine graded multiplication. -/
instance instGradedMonoid : SetLike.GradedMonoid (grading 𝒜 I) where
  one_mem := Submodule.mem_map.mpr ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mkₐ R I)⟩
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mkₐ R I) a b⟩

private theorem recompose_map (z : ⨁ i, 𝒜 i) :
    DirectSum.coeAddMonoidHom (grading 𝒜 I) (DirectSum.map (componentMap 𝒜 I) z) =
      Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 z) := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a => simp only [DirectSum.map_of, DirectSum.coeAddMonoidHom_of, componentMap_coe]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem recompose_zero (hI : I.IsHomogeneous 𝒜)
    (z : ⨁ i, grading 𝒜 I i)
    (hz : DirectSum.coeAddMonoidHom (grading 𝒜 I) z = 0) : z = 0 := by
  obtain ⟨z', rfl⟩ := ((DirectSum.map_surjective (componentMap 𝒜 I)).mpr (componentMap_surjective 𝒜 I)) z
  have he : Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 z') = 0 :=
    (recompose_map 𝒜 I z').symm.trans hz
  have hIz : DirectSum.coeAddMonoidHom 𝒜 z' ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp he
  apply DirectSum.ext
  intro i
  rw [DirectSum.map_apply]
  apply Subtype.ext
  change Ideal.Quotient.mk I (z' i) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hi := hI i hIz
  change ((DirectSum.decompose 𝒜) ((DirectSum.decompose 𝒜).symm z') i : A) ∈ I at hi
  simpa only [Equiv.apply_symm_apply] using hi

/-- Actual original homogeneity makes the quotient component family a true internal direct sum. -/
theorem isInternal (hI : I.IsHomogeneous 𝒜) : DirectSum.IsInternal (grading 𝒜 I) := by
  constructor
  · intro z z' h
    have hz : DirectSum.coeAddMonoidHom (grading 𝒜 I) (z - z') = 0 := by
      rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (recompose_zero 𝒜 I hI (z - z') hz)
  · intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨DirectSum.map (componentMap 𝒜 I) (DirectSum.decompose 𝒜 a), ?_⟩
    rw [recompose_map]
    exact congrArg (Ideal.Quotient.mk I) ((DirectSum.decompose 𝒜).symm_apply_apply a)

/-- The actual homogeneous quotient ring has its genuine internal grading; the original ideal is retained. -/
@[instance_reducible]
def gradedRing (hI : I.IsHomogeneous 𝒜) : GradedRing (grading 𝒜 I) where
  __ := instGradedMonoid 𝒜 I
  __ := (isInternal 𝒜 I hI).chooseDecomposition

/-- The original quotient homomorphism is graded on every actual homogeneous element. -/
def gradedMk : 𝒜 →+*ᵍ grading 𝒜 I where
  __ := Ideal.Quotient.mk I
  map_mem h := Submodule.mem_map.mpr ⟨_, h, rfl⟩

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- The entire graded quotient homomorphism is the true original quotient map. -/
@[simp]
theorem gradedMk_apply (a : A) : gradedMk 𝒜 I a = Ideal.Quotient.mk I a := rfl

/-- Bundled genuine homogeneous ideals provide the actual quotient grading without an extra grading hypothesis. -/
instance instGradedRingHomogeneous (J : HomogeneousIdeal 𝒜) :
    GradedRing (grading 𝒜 J.toIdeal) := gradedRing 𝒜 J.toIdeal J.isHomogeneous

end DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient

namespace DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : HomogeneousIdeal 𝒜)

/-- Every positive homogeneous quotient element lifts in the same positive degree, so the true irrelevant ideal is covered. -/
theorem irrelevant_le_map :
    HomogeneousIdeal.irrelevant (grading 𝒜 J.toIdeal) ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (gradedMk 𝒜 J.toIdeal) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi x hx
  obtain ⟨a, ha⟩ := componentMap_surjective 𝒜 J.toIdeal i ⟨x, hx⟩
  have he : (gradedMk 𝒜 J.toIdeal) a = x := congrArg Subtype.val ha
  change x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (gradedMk 𝒜 J.toIdeal).toRingHom
  rw [← he]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi a.2)

/-- The true quotient irrelevant ideal is exactly the image of the original irrelevant ideal. -/
theorem map_irrelevant :
    (HomogeneousIdeal.irrelevant 𝒜).map (gradedMk 𝒜 J.toIdeal) =
      HomogeneousIdeal.irrelevant (grading 𝒜 J.toIdeal) := by
  refine le_antisymm ?_ (irrelevant_le_map 𝒜 J)
  apply (HomogeneousIdeal.map_le_iff_le_comap _).mpr
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi x hx
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ hi ((gradedMk 𝒜 J.toIdeal).map_mem hx)

end DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
