import DeJongAlterations.Algebra.ReesLocalization
import DeJongAlterations.Geometry.ProjStructureMap

/-!
# Canonical affine blowup maps under coefficient homomorphisms

Extension of ideal powers constructs the irrelevant-ideal containment needed
by native Proj. The induced morphism uses the actual Rees coefficient map
and commutes with the original affine-base morphism.
-/

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Algebra.ReesLocalization

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Coefficient extension of an ideal produces the irrelevant containment
required to construct the actual native blowup morphism. -/
theorem reesGradedMap_irrelevant_le_map (I : Ideal R) (f : R →+* S) :
    HomogeneousIdeal.irrelevant (reesGrading (I.map f)) ≤
      (HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGradedMap I f) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn b hb
  let K := ((HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGradedMap I f)).toIdeal
  have H (a : S) (ha : a ∈ (I ^ n).map f) :
      ∃ p : reesAlgebra (I.map f), (p : S[X]) = monomial n a ∧ p ∈ K := by
    change a ∈ Ideal.span (f '' (I ^ n : Ideal R)) at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr, rfl⟩ := ha
      let p : reesAlgebra I := ⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩
      have hp : p ∈ reesGrading I n := ⟨r, rfl⟩
      refine ⟨reesMap I f p, ?_, ?_⟩
      · exact Polynomial.map_monomial f
      · exact Ideal.mem_map_of_mem (reesGradedMap I f).toRingHom
          (HomogeneousIdeal.mem_irrelevant_of_mem (reesGrading I) hn hp)
    | zero => exact ⟨0, by simp, K.zero_mem⟩
    | add a b ha hb hia hib =>
      obtain ⟨p, hp, hpK⟩ := hia
      obtain ⟨q, hq, hqK⟩ := hib
      refine ⟨p + q, ?_, K.add_mem hpK hqK⟩
      change (p : S[X]) + (q : S[X]) = monomial n (a + b)
      rw [hp, hq, map_add]
    | smul r a ha hia =>
      obtain ⟨p, hp, hpK⟩ := hia
      refine ⟨algebraMap S (reesAlgebra (I.map f)) r * p, ?_, K.mul_mem_left _ hpK⟩
      change C r * (p : S[X]) = monomial n (r * a)
      rw [hp, Polynomial.C_mul_monomial]
  have ha : (b : S[X]).coeff n ∈ (I ^ n).map f := by
    rw [Ideal.map_pow]
    exact b.property n
  obtain ⟨p, hp, hpK⟩ := H _ ha
  have heq : b = p := Subtype.ext (((mem_reesGrading_iff _ _ _).mp hb).trans hp.symm)
  subst p
  exact hpK

/-- The genuine native morphism induced by extension of the center ideal. -/
def affineBlowupMap (I : Ideal R) (f : R →+* S) :
    affineBlowup (I.map f) ⟶ affineBlowup I :=
  Proj.map (reesGradedMap I f) (reesGradedMap_irrelevant_le_map I f)

/-- The coefficient map commutes with the actual degree-zero identifications. -/
theorem reesGradedMap_degreeZero_constants (I : Ideal R) (f : R →+* S) :
    (reesGradedMap I f).gradedZeroRingHom.comp (reesDegreeZeroEquiv I).toRingHom =
      (reesDegreeZeroEquiv (I.map f)).toRingHom.comp f := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact reesMap_algebraMap I f r

/-- The native induced blowup map lies over the actual affine coefficient map. -/
theorem affineBlowupMap_structure (I : Ideal R) (f : R →+* S) :
    affineBlowupMap I f ≫ affineBlowupStructure I =
      affineBlowupStructure (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  have H := Geometry.ProjStructureMap.map_toSpec_base (reesGradedMap I f)
    (reesGradedMap_irrelevant_le_map I f) (reesDegreeZeroEquiv I).toRingHom
    ((reesDegreeZeroEquiv (I.map f)).toRingHom.comp f)
    (reesGradedMap_degreeZero_constants I f)
  change Proj.map (reesGradedMap I f) (reesGradedMap_irrelevant_le_map I f) ≫
      (Proj.toSpecZero (reesGrading I) ≫
        Spec.map (CommRingCat.ofHom (reesDegreeZeroEquiv I).toRingHom)) =
    Proj.toSpecZero (reesGrading (I.map f)) ≫
      Spec.map (CommRingCat.ofHom (reesDegreeZeroEquiv (I.map f)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom f)
  simpa only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] using H


/-- The actual graded coefficient map with an explicitly named extended ideal.
This form gives composition without transporting the target scheme by an ideal equality. -/
def reesGradedMapTo (I : Ideal R) (J : Ideal S) (f : R →+* S) (hIJ : I.map f = J) :
    reesGrading I →+*ᵍ reesGrading J := by
  subst J
  exact reesGradedMap I f

@[simp]
theorem reesGradedMapTo_apply (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hIJ : I.map f = J) (p : reesAlgebra I) :
    (reesGradedMapTo I J f hIJ p : S[X]) = Polynomial.map f (p : R[X]) := by
  subst J
  rfl

/-- The irrelevant containment for an explicitly named extended ideal is derived internally. -/
theorem reesGradedMapTo_irrelevant (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hIJ : I.map f = J) :
    HomogeneousIdeal.irrelevant (reesGrading J) ≤
      (HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGradedMapTo I J f hIJ) := by
  subst J
  exact reesGradedMap_irrelevant_le_map I f

/-- The genuine induced blowup map with explicitly named source and target ideals. -/
def affineBlowupMapTo (I : Ideal R) (J : Ideal S) (f : R →+* S) (hIJ : I.map f = J) :
    affineBlowup J ⟶ affineBlowup I :=
  Proj.map (reesGradedMapTo I J f hIJ) (reesGradedMapTo_irrelevant I J f hIJ)

/-- Naming the extended ideal preserves the literal coefficient structure square. -/
theorem affineBlowupMapTo_structure (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hIJ : I.map f = J) :
    affineBlowupMapTo I J f hIJ ≫ affineBlowupStructure I =
      affineBlowupStructure J ≫ Spec.map (CommRingCat.ofHom f) := by
  subst J
  exact affineBlowupMap_structure I f

/-- Coefficient mapping on actual Rees algebras preserves identities. -/
theorem reesGradedMapTo_id (I : Ideal R) (hI : I.map (RingHom.id R) = I) :
    reesGradedMapTo I I (RingHom.id R) hI = GradedRingHom.id (reesGrading I) := by
  apply GradedRingHom.ext
  intro p
  apply Subtype.ext
  simp

variable {T : Type u} [CommRing T]

/-- Coefficient mapping on actual Rees algebras preserves composition. -/
theorem reesGradedMapTo_comp (I : Ideal R) (J : Ideal S) (L : Ideal T)
    (f : R →+* S) (g : S →+* T) (hIJ : I.map f = J) (hJL : J.map g = L)
    (hIL : I.map (g.comp f) = L) :
    (reesGradedMapTo J L g hJL).comp (reesGradedMapTo I J f hIJ) =
      reesGradedMapTo I L (g.comp f) hIL := by
  apply GradedRingHom.ext
  intro p
  apply Subtype.ext
  simp only [GradedRingHom.comp_apply, reesGradedMapTo_apply, Polynomial.map_map]

/-- The actual induced blowup morphisms preserve identity coefficients. -/
theorem affineBlowupMapTo_id (I : Ideal R) (hI : I.map (RingHom.id R) = I) :
    affineBlowupMapTo I I (RingHom.id R) hI = 𝟙 (affineBlowup I) := by
  change Proj.map (reesGradedMapTo I I (RingHom.id R) hI)
    (reesGradedMapTo_irrelevant I I (RingHom.id R) hI) = 𝟙 (Proj (reesGrading I))
  simpa only [reesGradedMapTo_id I hI] using (Proj.map_id (𝒜 := reesGrading I))

/-- The actual induced blowup morphisms preserve coefficient composition. -/
theorem affineBlowupMapTo_comp (I : Ideal R) (J : Ideal S) (L : Ideal T)
    (f : R →+* S) (g : S →+* T) (hIJ : I.map f = J) (hJL : J.map g = L)
    (hIL : I.map (g.comp f) = L) :
    affineBlowupMapTo J L g hJL ≫ affineBlowupMapTo I J f hIJ =
      affineBlowupMapTo I L (g.comp f) hIL := by
  dsimp only [affineBlowupMapTo]
  rw [← Proj.map_comp]
  simp only [reesGradedMapTo_comp I J L f g hIJ hJL hIL]

/-- Extension along the inverse coefficient equivalence recovers the original ideal. -/
theorem ideal_map_ringEquiv_symm (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (hIJ : I.map e.toRingHom = J) : J.map e.symm.toRingHom = I := by
  rw [← hIJ, Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]

/-- A genuine coefficient ring equivalence induces the canonical isomorphism
of the native blowups, with its actual coefficient map as forward morphism. -/
def affineBlowupRingEquiv (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (hIJ : I.map e.toRingHom = J) : affineBlowup J ≅ affineBlowup I where
  hom := affineBlowupMapTo I J e.toRingHom hIJ
  inv := affineBlowupMapTo J I e.symm.toRingHom (ideal_map_ringEquiv_symm I J e hIJ)
  hom_inv_id := by
    have hJJ : J.map (e.toRingHom.comp e.symm.toRingHom) = J := by simp
    rw [affineBlowupMapTo_comp J I J e.symm.toRingHom e.toRingHom
      (ideal_map_ringEquiv_symm I J e hIJ) hIJ hJJ]
    simpa only [RingEquiv.toRingHom_comp_symm_toRingHom] using
      affineBlowupMapTo_id J (by simp)
  inv_hom_id := by
    have hII : I.map (e.symm.toRingHom.comp e.toRingHom) = I := by simp
    rw [affineBlowupMapTo_comp I J I e.toRingHom e.symm.toRingHom
      hIJ (ideal_map_ringEquiv_symm I J e hIJ) hII]
    simpa only [RingEquiv.symm_toRingHom_comp_toRingHom] using
      affineBlowupMapTo_id I (by simp)

@[simp]
theorem affineBlowupRingEquiv_hom (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (hIJ : I.map e.toRingHom = J) :
    (affineBlowupRingEquiv I J e hIJ).hom = affineBlowupMapTo I J e.toRingHom hIJ := rfl

end DeJongAlterations
