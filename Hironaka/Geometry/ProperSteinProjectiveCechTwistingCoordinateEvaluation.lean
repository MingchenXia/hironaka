import Hironaka.Geometry.ProperSteinProjectiveCechTwistingCoordinatePieces

/-!
# Actual original twisting coordinate fractions retain ALL original prime values

The native specialization/evaluation pattern adapts same-workspace
`BingWangEntropy/ProjectiveTwistingSections.lean`,
SHA256 aa9e1bf9b3af283dc6568948ac9200c55aa8314599e8a04eda483500605ebeb9.
The field-based zero-prime argument is excluded; ANY CommRing is allowed.
-/

universe u
open CategoryTheory AlgebraicGeometry
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original product localization specializes to the SAME original prime localization. -/
def polynomialCoordinateAtPoint (S : Finset I)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S)) :
    Localization.Away (polynomialCoordinateProduct (K := K) S) →+*
      projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x :=
  IsLocalization.map (M := Submonoid.powers (polynomialCoordinateProduct (K := K) S))
    (T := x.asHomogeneousIdeal.toIdeal.primeCompl)
    (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x)
    (RingHom.id (MvPolynomial I K))
    (Submonoid.powers_le.mpr ((Proj.mem_basicOpen _ _ _).mp hx))

omit [LinearOrder I] [Fintype I] in
/-- Every ORIGINAL polynomial is retained by the actual prime specialization. -/
theorem polynomialCoordinateAtPoint_algebraMap (S : Finset I)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S)) (p : MvPolynomial I K) :
    polynomialCoordinateAtPoint S x hx
        (algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S)) p) =
      algebraMap (MvPolynomial I K)
        (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x) p :=
  IsLocalization.map_eq _ _

omit [LinearOrder I] [Fintype I] in
/-- Actual native basic-open regular sections evaluate by the SAME original specialization. -/
theorem polynomialNativeAwayBasicOpenEquiv_eval (S : Finset I) (hS : S.Nonempty)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S))
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)) :
    ((polynomialNativeAwayBasicOpenEquiv S hS z).val ⟨x, hx⟩).val =
      polynomialCoordinateAtPoint S x hx z.val :=
  ProjectiveSpectrum.Proj.awayToSection_apply
    (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S) z ⟨x, hx⟩

omit [LinearOrder I] in
/-- The actual native Away/module equivalence preserves the SAME ordinary original fraction. -/
theorem polynomialNativeAwayModuleEquiv_value (S : Finset I)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S)) :
    polynomialCoordinateModuleLocalizationEquiv S (polynomialNativeAwayModuleEquiv S z).val = z.val := by
  change (polynomialCoordinateModuleLocalizationEquiv S)
    ((polynomialCoordinateModuleLocalizationEquiv S).symm z.val) = z.val
  exact (polynomialCoordinateModuleLocalizationEquiv S).apply_symm_apply z.val

omit [LinearOrder I] in
/-- The actual twisting coordinate comparison has the SAME original shifted ordinary fraction value. -/
theorem polynomialTwistingCoordinatePieceEquiv_value (k : ℕ) (S : Finset I) (i : I) (hi : i ∈ S)
    (s : bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S))) :
    let F := projectiveTwistingChartSectionsFrame (MvPolynomial.homogeneousSubmodule I K) k
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S))
      (Proj.basicOpen_mono _ _ _ (Finset.dvd_prod_of_mem (MvPolynomial.X : I → MvPolynomial I K) hi))
    polynomialCoordinateModuleLocalizationEquiv S (polynomialTwistingCoordinatePieceEquiv k S i hi s).val =
      ((polynomialNativeAwayBasicOpenEquiv S ⟨i, hi⟩).symm (F s)).val *
        algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S))
          ((MvPolynomial.X i : MvPolynomial I K) ^ k) := by
  dsimp only
  change (polynomialCoordinateModuleLocalizationEquiv S)
    (((MvPolynomial.X i : MvPolynomial I K) ^ k) •
      (polynomialNativeAwayModuleEquiv S _).val) = _
  rw [LinearEquiv.map_smul, Algebra.smul_def, polynomialNativeAwayModuleEquiv_value, mul_comm]
  rfl

omit [LinearOrder I] in
/-- EVERY original prime evaluates the actual original coordinate fraction to the SAME entire section. -/
theorem polynomialTwistingCoordinatePieceEquiv_eval (k : ℕ) (S : Finset I) (i : I) (hi : i ∈ S)
    (s : bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)))
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)) :
    polynomialCoordinateAtPoint S x hx
      (polynomialCoordinateModuleLocalizationEquiv S (polynomialTwistingCoordinatePieceEquiv k S i hi s).val) =
        s.val ⟨x, hx⟩ := by
  let F := projectiveTwistingChartSectionsFrame (MvPolynomial.homogeneousSubmodule I K) k
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S))
    (Proj.basicOpen_mono _ _ _ (Finset.dvd_prod_of_mem (MvPolynomial.X : I → MvPolynomial I K) hi))
  have he := congrArg (fun r => (r.val ⟨x, hx⟩).val)
    ((polynomialNativeAwayBasicOpenEquiv S ⟨i, hi⟩).apply_symm_apply (F s))
  have hf := congrArg (fun t : projectiveTwistingSections (MvPolynomial.homogeneousSubmodule I K) k
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)) => t.val ⟨x, hx⟩)
    (F.symm_apply_apply s)
  rw [polynomialTwistingCoordinatePieceEquiv_value, map_mul, polynomialCoordinateAtPoint_algebraMap]
  rw [polynomialNativeAwayBasicOpenEquiv_eval] at he
  rw [he]
  exact hf

omit [LinearOrder I] in
/-- The inverse actual comparison retains the SAME original fractional value at EVERY original prime. -/
theorem polynomialTwistingCoordinatePieceEquiv_symm_eval (k : ℕ) (S : Finset I) (i : I) (hi : i ∈ S)
    (z : polynomialCoordinateHomogeneousPiece (K := K) (I := I) (k : ℤ) S)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)) :
    (polynomialTwistingCoordinatePieceEquiv k S i hi |>.symm z).val ⟨x, hx⟩ =
      polynomialCoordinateAtPoint S x hx (polynomialCoordinateModuleLocalizationEquiv S z.val) := by
  have h := polynomialTwistingCoordinatePieceEquiv_eval k S i hi
    ((polynomialTwistingCoordinatePieceEquiv k S i hi).symm z) x hx
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end
end Hironaka.Geometry.ProperSteinProjectiveCech
