import Hironaka.Algebra.NodeEtaleResidueIdentity
import Hironaka.Algebra.NodeGeometricCompletionCoefficients

/-! # Collapse of the SAME constructed completed coefficients from original residue bijectivity -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleCoefficientCollapse

open IsLocalRing CompletionRegularityBasics CompletionLocalMap NodeGeometricCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]

/-- The genuine original residue equivalence has exactly the native original map as its forward map. -/
def originalResidueEquiv
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    ResidueField A ≃+* ResidueField B :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap A B)) hκ

/-- Finiteness of the SAME original residue action follows internally from its bijectivity. -/
theorem originalResidue_finite
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    FiniteDimensional (ResidueField A) (ResidueField B) := by
  exact Module.Finite.of_equiv_equiv (RingEquiv.refl (ResidueField A))
    (originalResidueEquiv A B hκ) (by ext a; rfl)

/-- Separability of the SAME original residue action follows internally from its bijectivity. -/
theorem originalResidue_separable
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
  exact Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField A))
    (originalResidueEquiv A B hκ) (by ext a; rfl)

variable [IsNoetherianRing A] [IsNoetherianRing B]

attribute [local instance] CompletionFlatMap.completedAlgebra

local instance : IsLocalHom (algebraMap (Completion A) (Completion B)) :=
  isLocalHom_completionMap (algebraMap A B)

/-- The actual completed native residue map is bijective by the WHOLE original completion square. -/
theorem completedResidue_bijective
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Function.Bijective (ResidueField.map (completionMap (algebraMap A B))) := by
  let E := (residueFieldEquiv A).symm.trans
    ((originalResidueEquiv A B hκ).trans (residueFieldEquiv B))
  have hE : ResidueField.map (completionMap (algebraMap A B)) = E.toRingHom := by
    apply RingHom.ext
    intro a
    have h := RingHom.congr_fun (completedResidue_triangle A B) ((residueFieldEquiv A).symm a)
    change ResidueField.map (completionMap (algebraMap A B))
        ((residueFieldEquiv A) ((residueFieldEquiv A).symm a)) =
      (residueFieldEquiv B) (ResidueField.map (algebraMap A B)
        ((residueFieldEquiv A).symm a)) at h
    rw [RingEquiv.apply_symm_apply] at h
    exact h
  rw [hE]
  exact E.bijective

/-- The actual upper-base residue map is surjective INTERNALLY, through the SAME Hensel residue triangle. -/
theorem upperResidue_surjective
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    Function.Surjective (ResidueField.map
      (algebraMap (Completion A) (CompletedCoefficientRing A B))) := by
  let := originalResidue_finite A B hκ
  let := originalResidue_separable A B hκ
  let := completedResidue_finite A B
  let := completedResidue_separable A B
  intro t
  obtain ⟨a, ha⟩ := (completedResidue_bijective A B hκ).2
    (completedCoefficientResidueEquiv A B t)
  refine ⟨a, (completedCoefficientResidueEquiv A B).injective ?_⟩
  have h := RingHom.congr_fun
    (NodeEtaleCoefficients.coefficientResidueEquiv_triangle (Completion A) (Completion B)) a
  exact h.trans ha

/-- The forward map is EXACTLY the actual algebra map from the original completed base to the SAME constructed T. -/
def baseEquiv
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    Completion A ≃ₐ[Completion A] CompletedCoefficientRing A B := by
  letI := originalResidue_finite A B hκ
  letI := originalResidue_separable A B hκ
  exact NodeEtaleResidueIdentity.algebraEquiv (Completion A) (CompletedCoefficientRing A B)
    (upperResidue_surjective A B hκ)

/-- EVERY completed base coefficient follows precisely the original actual forward map. -/
theorem baseEquiv_apply
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    ∀ a : Completion A, baseEquiv A B hκ a =
      algebraMap (Completion A) (CompletedCoefficientRing A B) a := by
  let := originalResidue_finite A B hκ
  let := originalResidue_separable A B hκ
  intro a
  rfl

/-- The genuine inverse collapses the SAME actual constructed coefficients to the unchanged completed base. -/
def collapseEquiv
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    CompletedCoefficientRing A B ≃ₐ[Completion A] Completion A := by
  letI := originalResidue_finite A B hκ
  letI := originalResidue_separable A B hκ
  exact (baseEquiv A B hκ).symm

/-- EVERY original completed-base coefficient is retained by the actual inverse. -/
theorem collapseEquiv_coefficient
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    ∀ a : Completion A, collapseEquiv A B hκ
      (algebraMap (Completion A) (CompletedCoefficientRing A B) a) = a := by
  let := originalResidue_finite A B hκ
  let := originalResidue_separable A B hκ
  intro a
  exact (baseEquiv A B hκ).symm_apply_apply a

/-- On EVERY actual T element, the SAME Hensel map factors through the unchanged native completed original map. -/
theorem coefficientMap_collapse
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    ∀ t : CompletedCoefficientRing A B, completedCoefficientMap A B t =
      completionMap (algebraMap A B) (collapseEquiv A B hκ t) := by
  let := originalResidue_finite A B hκ
  let := originalResidue_separable A B hκ
  intro t
  have h := RingHom.congr_fun (completedCoefficientMap_triangle A B)
    (collapseEquiv A B hκ t)
  change completedCoefficientMap A B
      (baseEquiv A B hκ ((baseEquiv A B hκ).symm t)) = _ at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

/-- The ENTIRE actual Hensel map, not just selected coefficients, is the SAME original completed map after collapse. -/
theorem coefficientMap_wholeFactor
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    (completedCoefficientMap A B).toRingHom =
      (completionMap (algebraMap A B)).comp (collapseEquiv A B hκ).toRingHom := by
  let := originalResidue_finite A B hκ
  let := originalResidue_separable A B hκ
  apply RingHom.ext
  intro t
  exact coefficientMap_collapse A B hκ t

/-- EVERY original uncompleted base representative keeps its original native completion under collapse. -/
theorem collapseEquiv_originalBase
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := originalResidue_finite A B hκ
    letI := originalResidue_separable A B hκ
    ∀ a : A, collapseEquiv A B hκ
      (algebraMap (Completion A) (CompletedCoefficientRing A B)
        (algebraMap A (Completion A) a)) = algebraMap A (Completion A) a := by
  let := originalResidue_finite A B hκ
  let := originalResidue_separable A B hκ
  intro a
  exact collapseEquiv_coefficient A B hκ _

end Hironaka.Algebra.NodeEtaleCoefficientCollapse
