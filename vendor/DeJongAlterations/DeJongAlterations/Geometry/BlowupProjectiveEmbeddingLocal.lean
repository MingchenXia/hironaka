import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingForms
import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingUnits

/-!
# Compatibility of the actual local projective blowup morphisms

The coefficient ring map is obtained from the original structure morphism.
Restrictions use the actual affine-site coefficient homomorphisms; changes of
projective coordinate use the genuine whole-ring units proved for the forms.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

open ProjectiveIdeal BlowupGluing

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    {X : Scheme.{u}} {n m : ℕ}

/-- Proof-irrelevant replacement of the actual coefficient map and generator family. -/
theorem affineProjectiveMap_congr (I : Ideal A) {r s : R →+* A}
    {g h : Fin (m + 1) → A} (hr : r = s) (hg : g = h)
    (hspan : Ideal.span (Set.range g) = I) (hspan' : Ideal.span (Set.range h) = I) :
    affineProjectiveMap r I g hspan = affineProjectiveMap s I h hspan' := by
  cases hr
  cases hg
  rfl

/-- Actual coefficient naturality with the fixed named target ideal of the global affine diagram. -/
theorem affineProjectiveMapTo_naturality (r : R →+* A) (I : Ideal A) (J : Ideal B)
    (g : Fin (m + 1) → A) (hspan : Ideal.span (Set.range g) = I)
    (f : A →+* B) (hIJ : I.map f = J)
    (hspan' : Ideal.span (Set.range (fun a => f (g a))) = J) :
    affineBlowupMapTo I J f hIJ ≫ affineProjectiveMap r I g hspan =
      affineProjectiveMap (f.comp r) J (fun a => f (g a)) hspan' := by
  subst J
  exact affineProjectiveMap_naturality r I g hspan f

/-- The coefficient map on an actual affine open induced by the original structure morphism. -/
def affineBaseCoefficients (p : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :
    R →+* Γ(X, U.1) :=
  (p.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Actual affine-site restriction preserves the original coefficient map. -/
theorem affineBaseCoefficients_restrict (p : X ⟶ Spec (CommRingCat.of R))
    {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    (coefficientMap h).comp (affineBaseCoefficients p ⟨V.1, V.2⟩) =
      affineBaseCoefficients p ⟨U.1, U.2⟩ := by
  have H := p.appLE_map (U := ⊤) (V := V.1) (by simp)
    ((Scheme.AffineZariskiSite.toOpensFunctor X).map h).op
  ext a
  exact congrArg (fun q => q ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) H

/-- The induced coefficient homomorphism has the exact original spectrum structure triangle. -/
theorem affineBaseCoefficients_structure (p : X ⟶ Spec (CommRingCat.of R))
    (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (affineBaseCoefficients p U)) = U.2.fromSpec ≫ p := by
  have ht : (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    rw [IsAffineOpen.fromSpec_top]
    apply (cancel_mono (Spec (CommRingCat.of R)).toSpecΓ).mp
    rw [Scheme.isoSpec_inv_toSpecΓ, SpecMap_ΓSpecIso_inv_toSpecΓ]
  have H := IsAffineOpen.SpecMap_appLE_fromSpec p
    (isAffineOpen_top (Spec (CommRingCat.of R))) U.2 (by simp)
  rw [ht, ← Spec.map_comp] at H
  exact H

/-- Restricting a genuine form is its actual image under the native affine-site coefficient map. -/
theorem pulledForm_restrict (j : X ⟶ projectiveSpace R n)
    {U V : X.AffineZariskiSite} (h : U ⟶ V) (i : Fin (n + 1))
    (hi : V.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (F : MvPolynomial (Fin (n + 1)) R) :
    coefficientMap h (pulledForm j ⟨V.1, V.2⟩ i hi F) =
      pulledForm j ⟨U.1, U.2⟩ i
        ((Scheme.AffineZariskiSite.toOpens_mono h.le).trans hi) F := by
  have H := j.appLE_map hi ((Scheme.AffineZariskiSite.toOpensFunctor X).map h).op
  exact congrArg (fun q => q (nativeFormSection i F)) H

/-- Lifting a finite index type does not change the image family. -/
theorem range_ulift_down {α : Type*} {β : Type*} (g : α → β) :
    Set.range (fun a : ULift.{u} α => g a.down) = Set.range g := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.down, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a⟩, rfl⟩

/-- The finite-index version of the exact native pulled-form span, in every base universe. -/
theorem pulledForm_span_fin (j : X ⟶ projectiveSpace R n) (U : X.affineOpens)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (i : Fin (n + 1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) :
    Ideal.span (Set.range (fun a => pulledForm j U i hi (F a))) =
      ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).ideal U := by
  have hs : Ideal.span (Set.range (fun a : ULift.{u} (Fin (m + 1)) => F a.down)) = J.toIdeal := by
    rw [range_ulift_down]
    exact hspan
  have H := pulledForm_span j U J (fun a : ULift.{u} (Fin (m + 1)) => F a.down) hs i hi
  have he := range_ulift_down (fun a : Fin (m + 1) => pulledForm j U i hi (F a))
  rw [he] at H
  exact H

/-- The native local morphism determined by the whole original pulled-back ideal. -/
def localProjectiveMap (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (U : X.affineOpens)
    (i : Fin (n + 1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) :
    affineBlowup (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).ideal U) ⟶
      projectiveSpace R m :=
  affineProjectiveMap (m := m) (affineBaseCoefficients p U)
    (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).ideal U)
    (fun a => pulledForm j U i hi (F a)) (pulledForm_span_fin j U J F hspan i hi)

/-- Changing projective coordinate gives literally the same native local projective morphism. -/
theorem localProjectiveMap_coordinate (p : X ⟶ Spec (CommRingCat.of R))
    (j : X ⟶ projectiveSpace R n) (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) {d : ℕ} (hF : ∀ a, (F a).IsHomogeneous d)
    (U : X.affineOpens) (i k : Fin (n + 1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hk : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen k) :
    localProjectiveMap p j J F hspan U k hk = localProjectiveMap p j J F hspan U i hi := by
  obtain ⟨v, hv⟩ := (pulledForm_ratio_isUnit j U i k hi hk).pow d
  have hg : (fun a => pulledForm j U k hk (F a)) =
      (fun a => (v : Γ(X, U.1)) * pulledForm j U i hi (F a)) := by
    funext a
    rw [pulledForm_ratio j U i k hi hk (hF a), hv, mul_comm]
  dsimp only [localProjectiveMap]
  exact (affineProjectiveMap_congr _ rfl hg _
    (generator_span_unit _ _ (pulledForm_span_fin j U J F hspan i hi) v)).trans
      (affineProjectiveMap_unit _ _ _ _ v)

/-- The local map preserves the original structure morphism of the actual affine open. -/
@[reassoc]
theorem localProjectiveMap_structure (p : X ⟶ Spec (CommRingCat.of R))
    (j : X ⟶ projectiveSpace R n) (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (U : X.affineOpens)
    (i : Fin (n + 1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) :
    localProjectiveMap p j J F hspan U i hi ≫ projectiveSpaceStructure R m =
      affineBlowupStructure
        (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).ideal U) ≫
          U.2.fromSpec ≫ p := by
  rw [localProjectiveMap, affineProjectiveMap_structure, affineBaseCoefficients_structure]

/-- Every actual affine-site arrow preserves the local morphisms, including coordinate changes. -/
theorem localProjectiveMap_naturality (p : X ⟶ Spec (CommRingCat.of R))
    (j : X ⟶ projectiveSpace R n) (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) {d : ℕ} (hF : ∀ a, (F a).IsHomogeneous d)
    {U V : X.AffineZariskiSite} (h : U ⟶ V) (i k : Fin (n + 1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hk : V.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen k) :
    (affineDiagram ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j)).map h ≫
      localProjectiveMap p j J F hspan ⟨V.1, V.2⟩ k hk =
      localProjectiveMap p j J F hspan ⟨U.1, U.2⟩ i hi := by
  let D := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let hkU := (Scheme.AffineZariskiSite.toOpens_mono h.le).trans hk
  have hg : (fun a => coefficientMap h (pulledForm j ⟨V.1, V.2⟩ k hk (F a))) =
      (fun a => pulledForm j ⟨U.1, U.2⟩ k hkU (F a)) := by
    funext a
    exact pulledForm_restrict j h k hk (F a)
  have hspan' := (generator_span_map (D.ideal ⟨V.1, V.2⟩)
    (fun a => pulledForm j ⟨V.1, V.2⟩ k hk (F a))
    (pulledForm_span_fin j ⟨V.1, V.2⟩ J F hspan k hk) (coefficientMap h)).trans (center_map D h)
  change affineBlowupMapTo (D.ideal ⟨V.1, V.2⟩) (D.ideal ⟨U.1, U.2⟩)
      (coefficientMap h) (center_map D h) ≫
    affineProjectiveMap (affineBaseCoefficients p ⟨V.1, V.2⟩) _
      (fun a => pulledForm j ⟨V.1, V.2⟩ k hk (F a)) _ = _
  rw [affineProjectiveMapTo_naturality _ _ _ _ _ _ _ hspan']
  exact (affineProjectiveMap_congr _ (affineBaseCoefficients_restrict p h) hg _
      (pulledForm_span_fin j ⟨U.1, U.2⟩ J F hspan k hkU)).trans
    (localProjectiveMap_coordinate p j J F hspan hF ⟨U.1, U.2⟩ i k hi hkU)

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
