import DeJongAlterations.Geometry.ProperSteinProjectiveCechPolynomialLocalization
import DeJongAlterations.Geometry.ProperSteinProjectiveCechShiftedLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Pi

/-! # Actual finite products of homogeneous coordinate Čech complexes

The pointwise finite product is certified as a genuine native finite biproduct
by its literal projections, insertions, and finite total identity. The actual
Čech and homology functors preserve that identity by additivity.
-/

/-!
Adapted from the same workspace `BingWangEntropy/FiniteProductCechCohomology.lean`,
SHA256 44132b51d23fcd5a3a5d8b231c590199e5e7c9a4f34746f2cf8032b908ee4954.
Only native Mathlib and owned DeJongAlterations modules are imported.
The final polynomial finiteness producer is generalized from field coefficients
to ORIGINAL Noetherian commutative rings.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section AdditiveBicones

variable {A C D : Type*} [Fintype A] [Category* C] [Category* D]
  [Preadditive C] [Preadditive D]

/-- An actual additive functor transports the literal finite total identity
of a genuine finite biproduct bicone. -/
theorem actualAdditiveFiniteBiconeMap_total (G : C ⥤ D) [G.Additive]
    {F : A → C} (b : Bicone F) (htotal : ∑ a, b.π a ≫ b.ι a = 𝟙 b.pt) :
    ∑ a, (G.mapBicone b).π a ≫ (G.mapBicone b).ι a = 𝟙 (G.mapBicone b).pt := by
  simp_rw [G.mapBicone_π, G.mapBicone_ι, ← G.map_comp]
  rw [← G.map_sum, htotal, G.map_id]
  rfl

/-- The image of a genuine finite biproduct bicone under an actual additive
functor is a genuine native bilimit, with no assumed homology formula. -/
def actualAdditiveFiniteBiconeMapIsBilimit (G : C ⥤ D) [G.Additive]
    {F : A → C} (b : Bicone F) (hb : b.IsBilimit) :
    (G.mapBicone b).IsBilimit :=
  isBilimitOfTotal _ (actualAdditiveFiniteBiconeMap_total G b (IsBilimit.total hb))

end AdditiveBicones

section DiagramBiproducts

variable {K I A : Type u} [CommRing K] [LinearOrder I] [Fintype A]
  (F : A → Finset I ⥤ ModuleCat.{u} K)

/-- The true coordinate projection from the actual pointwise module product diagram. -/
def actualModuleSubsetDiagramPiProjection (a : A) : actualModuleSubsetDiagramPi F ⟶ F a where
  app S := ModuleCat.ofHom (LinearMap.proj a)
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The true coordinate insertion into the actual pointwise module product diagram. -/
def actualModuleSubsetDiagramPiInsertion (a : A) : F a ⟶ actualModuleSubsetDiagramPi F := by
  classical
  refine
    { app := fun S => ModuleCat.ofHom (LinearMap.single K (fun a => (F a).obj S) a)
      naturality := ?_ }
  intro S T f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext b
  change (Pi.single a ((F a).map f x) : ∀ b, (F b).obj T) b =
    (F b).map f ((Pi.single a x : ∀ b, (F b).obj S) b)
  by_cases hb : b = a
  · subst b
    simp
  · simp [hb]

/-- Literal projections and insertions give a genuine native bicone for the
actual family of module-valued coordinate diagrams. -/
def actualModuleSubsetDiagramPiBicone : Bicone F where
  pt := actualModuleSubsetDiagramPi F
  π := actualModuleSubsetDiagramPiProjection F
  ι := actualModuleSubsetDiagramPiInsertion F
  ι_π a b := by
    classical
    by_cases hab : a = b
    · subst b
      simp only [eqToHom_refl]
      apply NatTrans.ext
      funext S
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (Pi.single a x : ∀ b, (F b).obj S) a = x
      simp
    · simp only [dif_neg hab]
      apply NatTrans.ext
      funext S
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (Pi.single a x : ∀ b, (F b).obj S) b = 0
      simp [Ne.symm hab]

omit [LinearOrder I] in
/-- The actual finite insertion/projection sum is the identity on the actual
pointwise coordinate-diagram product. -/
theorem actualModuleSubsetDiagramPiBicone_total :
    ∑ a, (actualModuleSubsetDiagramPiBicone F).π a ≫
      (actualModuleSubsetDiagramPiBicone F).ι a = 𝟙 (actualModuleSubsetDiagramPiBicone F).pt := by
  classical
  apply NatTrans.ext
  funext S
  rw [NatTrans.app_sum]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply]
  change (∑ a, (Pi.single a (x a) : ∀ a, (F a).obj S)) = x
  exact LinearMap.sum_single_apply (fun a => (F a).obj S) x

/-- The actual finite pointwise module product is a genuine native finite
biproduct of the actual coordinate-intersection diagrams. -/
def actualModuleSubsetDiagramPiIsBilimit : (actualModuleSubsetDiagramPiBicone F).IsBilimit :=
  isBilimitOfTotal _ (actualModuleSubsetDiagramPiBicone_total F)

/-- The actual projection/insertion bilimit produces native finite biproduct
existence for the actual coordinate-diagram family. -/
instance actualModuleSubsetDiagramPiHasBiproduct : HasBiproduct F :=
  HasBiproduct.mk ⟨actualModuleSubsetDiagramPiBicone F, actualModuleSubsetDiagramPiIsBilimit F⟩

/-- The actual pointwise coordinate-diagram product is isomorphic to the native
finite biproduct of its actual component diagrams. -/
def actualModuleSubsetDiagramPiBiproductIso :
    actualModuleSubsetDiagramPi F ≅ ⨁ F :=
  biproduct.uniqueUpToIso F (actualModuleSubsetDiagramPiIsBilimit F)

/-- The actual normalized Čech functor preserves addition of actual diagram maps. -/
instance actualSubsetCechFunctorAdditive :
    (actualSubsetCechFunctor (K := K) (I := I)).Additive where
  map_add := by
    intro X Y α β
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext S
    rfl

/-- The actual normalized Čech complex of the pointwise product is the vertex
of the actual image bicone of the component Čech complexes. -/
def actualFiniteProductCechBicone :
    Bicone (fun a => subsetCechComplex (F a)) :=
  (actualSubsetCechFunctor (K := K) (I := I)).mapBicone (actualModuleSubsetDiagramPiBicone F)

/-- The actual product coordinate Čech complex is a genuine native finite
biproduct of the actual component complexes. -/
def actualFiniteProductCechIsBilimit : (actualFiniteProductCechBicone F).IsBilimit :=
  actualAdditiveFiniteBiconeMapIsBilimit _ _ (actualModuleSubsetDiagramPiIsBilimit F)

/-- The actual Čech bilimit produces native finite biproduct existence for the
actual component complexes. -/
instance actualFiniteProductCechHasBiproduct :
    HasBiproduct (fun a => subsetCechComplex (F a)) :=
  HasBiproduct.mk ⟨actualFiniteProductCechBicone F, actualFiniteProductCechIsBilimit F⟩

/-- The genuine normalized Čech complex of the actual pointwise product diagram
is isomorphic to the native finite biproduct of the actual component complexes. -/
def actualFiniteProductCechBiproductIso :
    subsetCechComplex (actualModuleSubsetDiagramPi F) ≅
      ⨁ (fun a => subsetCechComplex (F a)) :=
  biproduct.uniqueUpToIso _ (actualFiniteProductCechIsBilimit F)

/-- Applying the native homology functor gives the genuine cohomology bicone
whose vertex is the actual product diagram's native Čech cohomology. -/
def actualFiniteProductCechHomologyBicone (p : ℕ) :
    Bicone (fun a => (subsetCechComplex (F a)).homology p) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (ComplexShape.up ℕ) p).mapBicone
    (actualFiniteProductCechBicone F)

/-- Native homology carries the actual finite-product Čech bilimit to a genuine
native finite-product bilimit, by its proved native additivity. -/
def actualFiniteProductCechHomologyIsBilimit (p : ℕ) :
    (actualFiniteProductCechHomologyBicone F p).IsBilimit :=
  actualAdditiveFiniteBiconeMapIsBilimit _ _ (actualFiniteProductCechIsBilimit F)

/-- Native cohomology of the actual finite-product coordinate Čech complex is
isomorphic to the literal finite product of the actual component cohomology modules. -/
def actualFiniteProductCechHomologyPiIso (p : ℕ) :
    (subsetCechComplex (actualModuleSubsetDiagramPi F)).homology p ≅
      ModuleCat.of K (∀ a, (subsetCechComplex (F a)).homology p) :=
  IsLimit.conePointUniqueUpToIso
    (actualFiniteProductCechHomologyIsBilimit F p).isLimit
    (ModuleCat.HasLimit.productLimitCone (fun a => (subsetCechComplex (F a)).homology p)).isLimit

/-- A genuine finite product of actual coordinate Čech complexes has finite
native cohomology whenever its actual component cohomology modules are finite. -/
theorem actualModuleSubsetDiagramPi_homology_finite (p : ℕ)
    (hf : ∀ a, Module.Finite K ((subsetCechComplex (F a)).homology p)) :
    Module.Finite K ((subsetCechComplex (actualModuleSubsetDiagramPi F)).homology p) := by
  let : ∀ a, Module.Finite K ((subsetCechComplex (F a)).homology p) := hf
  exact Module.Finite.equiv (actualFiniteProductCechHomologyPiIso F p).toLinearEquiv.symm

end DiagramBiproducts

section ActualShiftedPolynomialCohomology

variable {K I A : Type u} [CommRing K] [hK : IsNoetherianRing K] [LinearOrder I] [Fintype I]
  [Fintype A] [DecidableEq A] (δ : A → ℤ)
omit hK

/-- The true finite shifted polynomial module coordinate Čech complex is
isomorphic to the actual product of its genuinely shifted polynomial coordinate complexes. -/
def finiteShiftedPolynomialCoordinateCechProductIso (m : ℤ) :
    homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
      (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
      (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m ≅
      subsetCechComplex (actualModuleSubsetDiagramPi
        (fun a => polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (m - δ a))) :=
  (actualSubsetCechFunctor (K := K) (I := I)).mapIso
    (finiteShiftedCoordinateSubsetDiagramIso (polynomialIntegralGrading (K := K) (I := I))
      δ (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m)

include hK in
/-- Every native cohomology module of the actual finite shifted free polynomial
module's genuine coordinate-localization Čech complex is finite in every integral degree. -/
theorem finiteShiftedPolynomialCoordinateCech_homology_finite (m : ℤ) (p : ℕ) :
    Module.Finite K
      ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
        (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
        (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m).homology p) := by
  have hfin : Module.Finite K
      ((subsetCechComplex (actualModuleSubsetDiagramPi
        (fun a => polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (m - δ a)))).homology p) :=
    actualModuleSubsetDiagramPi_homology_finite _ p
      (fun a => polynomialCoordinateHomogeneousCech_homology_finite (K := K) (I := I) (m - δ a) p)
  let := hfin
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso
      (finiteShiftedPolynomialCoordinateCechProductIso (K := K) (I := I) δ m) p).toLinearEquiv.symm

end ActualShiftedPolynomialCohomology

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
