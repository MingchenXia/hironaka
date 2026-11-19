import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The ACTUAL diagonal residue-field point, its actual localization, original
local map and the ENTIRE native residue identity. No separability is assumed. -/

noncomputable section

open IsLocalRing TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionDiagonalPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable (K R : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The literal original residue-field tensor neighbourhood. -/
abbrev TensorRing := ResidueField R ⊗[K] R

/-- The canonical diagonal augmentation from the actual original residue map. -/
def augmentation : TensorRing K R →ₐ[ResidueField R] ResidueField R where
  toRingHom := (Algebra.TensorProduct.lift (AlgHom.id K (ResidueField R))
    (IsScalarTower.toAlgHom K R (ResidueField R)) (fun _ _ => Commute.all _ _)).toRingHom
  commutes' a := by simp

/-- EVERY actual tensor coefficient and original germ has its prescribed diagonal image. -/
theorem augmentation_tmul (a : ResidueField R) (r : R) :
    augmentation K R (a ⊗ₜ[K] r) = a * residue R r := rfl

/-- The actual augmentation fixes EVERY left coefficient, hence is onto. -/
theorem augmentation_surjective : Function.Surjective (augmentation K R) := by
  intro a
  exact ⟨algebraMap (ResidueField R) (TensorRing K R) a, (augmentation K R).commutes a⟩

/-- The SAME actual diagonal point ideal. -/
def diagonalPoint : Ideal (TensorRing K R) := RingHom.ker (augmentation K R).toRingHom

/-- Maximality is derived from the actual augmentation, never a point certificate input. -/
theorem diagonalPoint_isMaximal : (diagonalPoint K R).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (augmentation K R) (augmentation_surjective K R)

attribute [local instance] diagonalPoint_isMaximal

/-- The actual local ring at the SAME canonical diagonal point. -/
abbrev DiagonalLocal := Localization.AtPrime (diagonalPoint K R)

/-- The native external point-field action, with no inverse-defined replacement action. -/
@[instance_reducible]
def pointFieldAlgebra : Algebra (ResidueField R) (DiagonalLocal K R) := inferInstance

/-- The native original local source action through right tensor inclusion. -/
@[instance_reducible]
def originalAlgebra : Algebra R (DiagonalLocal K R) := inferInstance

attribute [local instance] pointFieldAlgebra originalAlgebra

/-- The WHOLE actual original source map is the original tensor/localization composite. -/
theorem originalMap_eq : algebraMap R (DiagonalLocal K R) =
    (algebraMap (TensorRing K R) (DiagonalLocal K R)).comp
      (Algebra.TensorProduct.includeRight.toRingHom : R →+* TensorRing K R) :=
  IsScalarTower.algebraMap_eq R (TensorRing K R) (DiagonalLocal K R)

/-- Every actual denominator has a unit image under the actual diagonal augmentation. -/
theorem augmentation_denominator_unit (s : (diagonalPoint K R).primeCompl) :
    IsUnit (augmentation K R s) := by
  apply isUnit_iff_ne_zero.mpr
  exact s.property

/-- Actual localization of the SAME augmentation at its SAME point. -/
def residueLift : DiagonalLocal K R →+* ResidueField R :=
  IsLocalization.lift (S := DiagonalLocal K R) (augmentation_denominator_unit K R)

/-- The extended map retains EVERY original actual tensor element. -/
theorem residueLift_tensor (d : TensorRing K R) :
    residueLift K R (algebraMap (TensorRing K R) (DiagonalLocal K R) d) =
      augmentation K R d :=
  IsLocalization.lift_eq _ d

/-- The ENTIRE original local germ composite is the original native residue map. -/
theorem residueLift_original (r : R) :
    residueLift K R (algebraMap R (DiagonalLocal K R) r) = residue R r := by
  rw [originalMap_eq, RingHom.comp_apply, residueLift_tensor]
  exact augmentation_tmul K R 1 r |>.trans (one_mul _)

/-- The actual external point-field coefficients are fixed by the SAME localization map. -/
def residueLiftAlgHom : DiagonalLocal K R →ₐ[ResidueField R] ResidueField R where
  toRingHom := residueLift K R
  commutes' a := by
    change residueLift K R (algebraMap (ResidueField R) (DiagonalLocal K R) a) = a
    rw [IsScalarTower.algebraMap_eq (ResidueField R) (TensorRing K R) (DiagonalLocal K R),
      RingHom.comp_apply, residueLift_tensor]
    exact (augmentation K R).commutes a

/-- Surjectivity uses all actual original residue coefficients, with no separability input. -/
theorem residueLift_surjective : Function.Surjective (residueLift K R) := by
  intro a
  exact ⟨algebraMap (ResidueField R) (DiagonalLocal K R) a,
    (residueLiftAlgHom K R).commutes a⟩

/-- The SAME actual local residue kernel is its native maximal ideal. -/
theorem residueLift_ker : RingHom.ker (residueLift K R) = maximalIdeal (DiagonalLocal K R) :=
  IsLocalRing.ker_eq_maximalIdeal _ (residueLift_surjective K R)

/-- The original source map contracts the actual target maximal ideal exactly. -/
theorem originalMap_maximalIdeal_comap :
    (maximalIdeal (DiagonalLocal K R)).comap (algebraMap R (DiagonalLocal K R)) =
      maximalIdeal R := by
  rw [← residueLift_ker]
  change RingHom.ker ((residueLift K R).comp (algebraMap R (DiagonalLocal K R))) = _
  have h : (residueLift K R).comp (algebraMap R (DiagonalLocal K R)) = residue R :=
    RingHom.ext (residueLift_original K R)
  rw [h, ker_residue]

/-- The actual original map to its diagonal neighbourhood is local. -/
theorem originalMap_isLocalHom : IsLocalHom (algebraMap R (DiagonalLocal K R)) :=
  ((IsLocalRing.local_hom_TFAE _).out 0 4).mpr (originalMap_maximalIdeal_comap K R)

attribute [local instance] originalMap_isLocalHom

/-- The original localized augmentation factors through the ACTUAL native residue map. -/
def localResidueMap : ResidueField (DiagonalLocal K R) →+* ResidueField R :=
  (residue (DiagonalLocal K R)).liftOfSurjective residue_surjective
    ⟨residueLift K R, by rw [ker_residue, residueLift_ker]⟩

/-- The native quotient factor retains EVERY original localized representative. -/
theorem localResidueMap_residue (t : DiagonalLocal K R) :
    localResidueMap K R (residue (DiagonalLocal K R) t) = residueLift K R t :=
  RingHom.liftOfSurjective_comp_apply _ _ _ t

/-- Native actual residue identity, constructed independently of any scalar-action choice. -/
def localResidueRingEquiv : ResidueField (DiagonalLocal K R) ≃+* ResidueField R :=
  RingEquiv.ofBijective (localResidueMap K R) ⟨RingHom.injective _, by
    intro a
    obtain ⟨t, ht⟩ := residueLift_surjective K R a
    exact ⟨residue (DiagonalLocal K R) t, (localResidueMap_residue K R t).trans ht⟩⟩

/-- EVERY native residue representative retains the SAME actual localized augmentation. -/
theorem localResidueRingEquiv_residue (t : DiagonalLocal K R) :
    localResidueRingEquiv K R (residue (DiagonalLocal K R) t) = residueLift K R t := localResidueMap_residue K R t

/-- The ENTIRE original native residue-field map is exactly the inverse identification. -/
theorem localResidueRingEquiv_comp_original :
    (localResidueRingEquiv K R).toRingHom.comp
      (ResidueField.map (algebraMap R (DiagonalLocal K R))) = RingHom.id (ResidueField R) := by
  ext a
  obtain ⟨r, rfl⟩ := residue_surjective a
  change localResidueRingEquiv K R
    (ResidueField.map (algebraMap R (DiagonalLocal K R)) (residue R r)) = residue R r
  rw [ResidueField.map_residue, localResidueRingEquiv_residue, residueLift_original]

/-- The actual original local residue map is bijective, with all native actions retained. -/
theorem originalResidue_bijective :
    Function.Bijective (ResidueField.map (algebraMap R (DiagonalLocal K R))) := by
  constructor
  · exact RingHom.injective _
  · intro a
    refine ⟨localResidueRingEquiv K R a, ?_⟩
    apply (localResidueRingEquiv K R).injective
    change ((localResidueRingEquiv K R).toRingHom.comp
      (ResidueField.map (algebraMap R (DiagonalLocal K R)))) (localResidueRingEquiv K R a) = _
    rw [localResidueRingEquiv_comp_original]
    rfl

/-- The native ORIGINAL residue action is the SAME actual external coefficient residue map. -/
theorem externalCoefficient_residue (a : ResidueField R) :
    ResidueField.map (algebraMap R (DiagonalLocal K R)) a =
      residue (DiagonalLocal K R) (algebraMap (ResidueField R) (DiagonalLocal K R) a) := by
  apply (localResidueRingEquiv K R).injective
  have h := congrArg (fun g : ResidueField R →+* ResidueField R => g a)
    (localResidueRingEquiv_comp_original K R)
  rw [RingHom.comp_apply, RingHom.id_apply] at h
  change localResidueRingEquiv K R
    (ResidueField.map (algebraMap R (DiagonalLocal K R)) a) = a at h
  rw [h, localResidueRingEquiv_residue]
  exact ((residueLiftAlgHom K R).commutes a).symm

/-- The entire native original point-field residue action is retained as an algebra equivalence. -/
def localResidueEquiv : ResidueField (DiagonalLocal K R) ≃ₐ[ResidueField R] ResidueField R :=
  AlgEquiv.ofRingEquiv (f := localResidueRingEquiv K R) fun a => by
    change ((localResidueRingEquiv K R).toRingHom.comp
      (ResidueField.map (algebraMap R (DiagonalLocal K R)))) a = a
    rw [localResidueRingEquiv_comp_original]
    rfl

/-- The literal local quotient has its actual EXTERNAL coefficient-compatible residue model. -/
def localResidueQuotientEquiv :
    (DiagonalLocal K R ⧸ maximalIdeal (DiagonalLocal K R)) ≃ₐ[ResidueField R] ResidueField R :=
  (Ideal.quotientEquivAlgOfEq (ResidueField R) (residueLift_ker K R).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := residueLiftAlgHom K R)
      (residueLift_surjective K R))

/-- EVERY local quotient representative retains the SAME actual localized augmentation. -/
theorem localResidueQuotientEquiv_mk (t : DiagonalLocal K R) :
    localResidueQuotientEquiv K R (Ideal.Quotient.mk _ t) = residueLift K R t := rfl

end Hironaka.Algebra.NodeGeometricCompletionDiagonalPoint
