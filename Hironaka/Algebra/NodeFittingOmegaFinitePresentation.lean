import Hironaka.Algebra.NodeFittingOmegaGluing
import Hironaka.Algebra.NodeFittingModuleFinite

/-! # Native local finite presentation of the actual original intrinsic Fitting subscheme -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Algebra.NodeFittingOmegaFinitePresentation

open NodeFittingOmegaCharts NodeFittingOmegaGluing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

/-- The ENTIRE ideal image of an actual finite generating set is still finitely generated. -/
theorem ideal_map_fg {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (J : Ideal R) (hJ : J.FG) (ρ : R →+* S) : (J.map ρ).FG := by
  obtain ⟨s, hs, he⟩ := Submodule.fg_def.mp hJ
  change Ideal.span s = J at he
  rw [← he, Ideal.map_span]
  exact Submodule.fg_span (hs.image ρ)

/-- The actual closed immersion over an actual affine scheme is LocFP from its WHOLE original ideal. -/
theorem affine_subscheme_locallyOfFinitePresentation {Z : Scheme.{u}} [IsAffine Z]
    (J : Z.IdealSheafData) (hJ : (J.ideal ⟨⊤, isAffineOpen_top Z⟩).FG) :
    LocallyOfFinitePresentation J.subschemeι := by
  let : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)
    (f := J.subschemeι)).mpr
  apply RingHom.FinitePresentation.of_surjective _
    (J.subschemeι_app_surjective ⟨⊤, isAffineOpen_top Z⟩)
  change (RingHom.ker J.subschemeι.appTop.hom).FG
  rw [J.ker_subschemeι_app ⟨⊤, isAffineOpen_top Z⟩]
  exact hJ

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- Finite generation of the actual original chart's WHOLE intrinsic differential ideal. -/
theorem chartIdeal_fg (C : Chart f) (i : ℕ) : (C.ideal f i).FG := by
  let := C.algebra f
  let := C.differentialFinitePresentation f
  exact NodeFittingModule.fittingIdeal_fg i

/-- The original local chart's WHOLE ideal on its actual affine open is natively finitely generated. -/
theorem localIdeal_top_fg (C : Chart f) (i : ℕ) :
    ((localIdeal f i C).ideal ⟨⊤, isAffineOpen_top C.source.1.toScheme⟩).FG := by
  have ht : (localIdeal f i C).ideal ⟨⊤, isAffineOpen_top C.source.1.toScheme⟩ =
      (C.ideal f i).map C.source.1.topIso.inv.hom := by
    simp [localIdeal, Scheme.IdealSheafData.ofIdealTop_ideal]
    change Ideal.map (RingHom.id _) _ = _
    rw [Ideal.map_id]
  rw [ht]
  exact ideal_map_fg _ (chartIdeal_fg f C i) _

/-- The ACTUAL intrinsic Fitting closed immersion is locally finitely presented over ANY original base. -/
theorem inclusion_locallyOfFinitePresentation (i : ℕ) :
    LocallyOfFinitePresentation (idealSheaf f i).subschemeι := by
  apply IsZariskiLocalAtTarget.of_openCover (chartCover f)
  intro C
  let I := idealSheaf f i
  let J := I.comap C.source.1.ι
  let : LocallyOfFinitePresentation J.subschemeι := by
    rw [show J = localIdeal f i C from idealSheaf_comap f i C]
    exact affine_subscheme_locallyOfFinitePresentation _ (localIdeal_top_fg f C i)
  let : LocallyOfFinitePresentation (pullback.fst C.source.1.ι I.subschemeι) := by
    rw [← I.comapIso_inv_subschemeι C.source.1.ι]
    infer_instance
  have h : LocallyOfFinitePresentation
      ((pullbackSymmetry I.subschemeι C.source.1.ι).hom ≫
        pullback.fst C.source.1.ι I.subschemeι) := inferInstance
  change LocallyOfFinitePresentation (pullback.snd I.subschemeι C.source.1.ι)
  simpa using h

/-- The SAME actual Fitting structural morphism to the SAME original base is LocFP. -/
theorem fittingMorphism_locallyOfFinitePresentation (i : ℕ) :
    LocallyOfFinitePresentation (fittingMorphism f i) := by
  let := inclusion_locallyOfFinitePresentation f i
  exact locallyOfFinitePresentation_comp _ _

end Hironaka.Algebra.NodeFittingOmegaFinitePresentation
