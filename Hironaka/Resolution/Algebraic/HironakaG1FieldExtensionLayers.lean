import Hironaka.Resolution.Algebraic.ActualGlobalDimensionSeparationIdeal
import Hironaka.Resolution.Algebraic.ActualGlobalDimensionClopenPartition
import Hironaka.Algebra.RegularSmooth.SingularLocus
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Resolution.HironakaG1RComponentBaseChange
import Hironaka.Resolution.HironakaG1RSingularIdealCartesian
import Hironaka.Resolution.HironakaG1RReducedEquidimensionalBaseChange
import Hironaka.Resolution.HironakaG1RNoetherianBaseChange

/-!
# Actual field-extension bridges for the dimension-separation step

Source-first proof: `hironaka-g1-field-extension-layers.tex`.
The actual EP/Hironaka definitions are compared with the proved TN
field-extension facts, then flat blowup base change constructs the actual
dimension-separation square. The intrinsic singular-ideal comparison is
provided over two perfect fields and for every extension in characteristic
zero. No smoothness of a general field extension is assumed.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Hironaka.Resolution.Algebraic.HironakaG1FieldExtensionLayers

noncomputable section

open ActualGlobalDimensionSeparationIdeal ActualGlobalDimensionClopenPartition

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {X XL : Scheme.{u}} {f : X ⟶ Spec (.of k)} {fL : XL ⟶ Spec (.of L)}
  {p : XL ⟶ X}

theorem componentDimension_eq (C : irreducibleComponents X) :
    ActualIntrinsicComponentDimensions.componentDimension C =
      Hironaka.HironakaG1RComponentBaseChange.componentDimension C := rfl

theorem complementaryClosed_eq [NoetherianSpace X] (d : WithBot ℕ∞) :
    complementaryClosed X d =
      Hironaka.HironakaG1RComponentBaseChange.complementaryClosed X d := rfl

theorem separationIdeal_eq [NoetherianSpace X] :
    separationIdeal X =
      Hironaka.HironakaG1RComponentBaseChange.separationIdeal X := rfl

/-- Complementary dimension loci for the actual EP definitions under an
arbitrary cartesian field-extension square. -/
theorem complementaryClosed_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL]
    (d : WithBot ℕ∞) :
    (complementaryClosed X d).preimage p.continuous = complementaryClosed XL d :=
  Hironaka.HironakaG1RComponentBaseChange.preimage_complementaryClosed h d

/-- The actual range of irreducible-component dimensions is unchanged. -/
theorem range_componentDimension_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] :
    Set.range (ActualIntrinsicComponentDimensions.componentDimension (X := XL)) =
      Set.range (ActualIntrinsicComponentDimensions.componentDimension (X := X)) :=
  Hironaka.HironakaG1RComponentBaseChange.range_componentDimension h

/-- The entire actual EP separation ideal, with no affine or generator packet. -/
theorem separationIdeal_baseChange [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] :
    (separationIdeal X).comap p = separationIdeal XL :=
  Hironaka.HironakaG1RComponentBaseChange.comap_separationIdeal_of_isPullback h

/-- The noetherian space on the extended field is derived from the original
finite-type noetherian input rather than a caller-supplied target hypothesis. -/
theorem separationIdeal_baseChange_of_noetherianSource [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] :
    letI := Hironaka.HironakaG1RNoetherianBaseChange.noetherianSpace_of_isPullback h
    (separationIdeal X).comap p = separationIdeal XL := by
  let := Hironaka.HironakaG1RNoetherianBaseChange.noetherianSpace_of_isPullback h
  exact separationIdeal_baseChange h

/-- The dependency's intrinsic singular ideal is the TN relative singular
ideal over a perfect field. -/
theorem singIdeal_eq [PerfectField k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    X.singIdeal = Scheme.IdealSheafData.vanishingIdeal
      (Hironaka.HironakaG1RSingularIdealSheaf.singularLocus f) := by
  rw [Scheme.singIdeal_eq_vanishingIdeal_closure_singularLocus]
  congr 1
  ext1
  change closure X.singularLocus = (f.smoothLocus : Set X)ᶜ
  rw [(Scheme.isClosed_singularLocus f).closure_eq,
    Scheme.singularLocus_eq_compl_smoothLocus f]

/-- Singular ideals base-change when both field presentations have the
perfect-field regular/smooth comparison. -/
theorem singIdeal_baseChange [PerfectField k] [PerfectField L]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] :
    X.singIdeal.comap p = XL.singIdeal := by
  let : LocallyOfFiniteType fL :=
    MorphismProperty.of_isPullback h (inferInstance : LocallyOfFiniteType f)
  rw [singIdeal_eq f, singIdeal_eq fL]
  exact Hironaka.HironakaG1RSingularIdealCartesian.comap_singularIdeal_of_isPullback h

/-- In the original characteristic-zero route, the extension field's
perfectness is derived from the injective original algebra map. -/
theorem singIdeal_baseChange_charZero [CharZero k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] :
    X.singIdeal.comap p = XL.singIdeal := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  exact singIdeal_baseChange h

theorem isReducedEquidimensional_iff [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    X.IsReducedEquidimensional k ↔
      Hironaka.HironakaG1RReducedEquidimensionalBaseChange.IsReducedEquidimensional
        (X ↘ Spec (.of k)) := Iff.rfl

theorem isReducedEquidimensional_baseChange [PerfectField k]
    [X.Over (Spec (.of k))] [XL.Over (Spec (.of L))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (XL ↘ Spec (.of L))]
    (h : IsPullback p (XL ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (hX : X.IsReducedEquidimensional k) : XL.IsReducedEquidimensional L :=
  Hironaka.HironakaG1RReducedEquidimensionalBaseChange.isReducedEquidimensional_of_isPullback
    h hX

/-- Equality-of-centres transport for the public flat blowup base-change
theorem; the comparable existing EP helper is private to its smooth module. -/
private theorem idealEq_isPullback {A B : Scheme.{u}} (g : A ⟶ B) [Flat g]
    (I : B.IdealSheafData) (J : A.IdealSheafData) (hI : I.comap g = J) :
    IsPullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp hI.symm) ≫
      Scheme.Hom.blowUpMap g I) J.blowUpπ I.blowUpπ g := by
  subst J
  simpa only [eqToHom_refl, Category.id_comp] using isPullback_blowUpMap g I

/-- The actual field-extension separation morphism. No smoothness of a
possibly infinite field extension is assumed. -/
def separationMap_baseChange [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] :
    separationSpace XL ⟶ separationSpace X :=
  eqToHom (congrArg Scheme.IdealSheafData.blowUp (separationIdeal_baseChange h).symm) ≫
    Scheme.Hom.blowUpMap p (separationIdeal X)

theorem separationMap_baseChange_isPullback [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] :
    IsPullback (separationMap_baseChange h) (separationProjection XL)
      (separationProjection X) p := by
  let : Flat p := Hironaka.HironakaG1RComponentBaseChange.flat_of_isPullback h
  exact idealEq_isPullback p _ _ (separationIdeal_baseChange h)

theorem separationMap_baseChange_over [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] :
    separationMap_baseChange h ≫ separationProjection X = separationProjection XL ≫ p :=
  (separationMap_baseChange_isPullback h).w

theorem separationMap_baseChange_flat [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] :
    Flat (separationMap_baseChange h) :=
  MorphismProperty.of_isPullback (separationMap_baseChange_isPullback h).flip
    (Hironaka.HironakaG1RComponentBaseChange.flat_of_isPullback h)

theorem separationMap_baseChange_surjective [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] :
    Surjective (separationMap_baseChange h) :=
  MorphismProperty.of_isPullback (separationMap_baseChange_isPullback h).flip
    (Hironaka.HironakaG1RComponentBaseChange.surjective_of_isPullback h)

/-- The separation blowup square from the original noetherian finite-type
scheme alone; noetherianity of the extended scheme is constructed internally. -/
theorem exists_separationMap_baseChange_of_noetherianSource [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] :
    letI := Hironaka.HironakaG1RNoetherianBaseChange.noetherianSpace_of_isPullback h
    ∃ q : separationSpace XL ⟶ separationSpace X,
      IsPullback q (separationProjection XL) (separationProjection X) p ∧
      Flat q ∧ Surjective q := by
  let := Hironaka.HironakaG1RNoetherianBaseChange.noetherianSpace_of_isPullback h
  exact ⟨separationMap_baseChange h, separationMap_baseChange_isPullback h,
    separationMap_baseChange_flat h, separationMap_baseChange_surjective h⟩

end

end Hironaka.Resolution.Algebraic.HironakaG1FieldExtensionLayers
