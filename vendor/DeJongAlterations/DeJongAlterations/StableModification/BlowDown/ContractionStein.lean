/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.Contraction
import DeJongAlterations.StableModification.BlowDown.ProjectiveBookkeeping
import DeJongAlterations.StableModification.Limits.SpreadModification
import DeJongAlterations.StableModification.ValCurves.ModificationsUnique
import DeJongAlterations.Geometry.AffineBlowupBirational
import DeJongAlterations.Geometry.NormalCurveModificationFunctionField

/-!
# The blow-down as a relative normalization (Temkin, Prop. 4.4.6, last step)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6 (T:3224–3229): a morphism `h̄ : C' → ℙ¹_C` over `C` which contracts the exceptional
component `Z` of the closed fibre and no other component of it gives the blow-down
`C'' = Nor_{C'}(h̄(C'))`. In Lean the relative normalization of the target in `C'`
(`Scheme.Hom.normalization`) is already the normalization of the image, so we take
`C'' = h̄.normalization` with `b = h̄.toNormalization : C' → C''` and
`β'' = h̄.fromNormalization ≫ π : C'' → C` (blueprint `lem:sm-bdg-stein`,
`sm-blow-down-global.tex`). We work with any `π : P → C` with `P` projective and of finite
presentation over `V` (Temkin's `P = ℙ¹_C`) and prove:

* `isIso_toNormalization_restrict`: over an open of `P` over which `h̄` is a closed immersion,
  `b` is an isomorphism (a dominant closed immersion into a reduced scheme);
* `isProjectiveOver_blowDown`, `flat_blowDown`, `locallyOfFinitePresentation_blowDown`,
  `isRelativelyProjective_blowDown`, `isModification_blowDown`, `isEtaModification_blowDown`,
  `isEtaModification_blowDown_base`, `image_closure_subsingleton_toNormalization_iff`:
  `C''` is integral, normal, projective, flat and of finite
  presentation over `V` (Stein finiteness, `isProjectiveOver_fromNormalization`), `b` is a
  modification, projective relative to `C'' → Spec V` and an η-modification, `β''` is an
  η-modification with `b ≫ β'' = β`, and `b` contracts exactly the components of the closed
  fibre contracted by `h̄` (`ν = h̄.fromNormalization` is integral, so it contracts no curve).

The generic point of `Spec V` is open (`V` of finite height, lane LIM3's
`isOpen_singleton_genericPoint_of_finite`), and `h̄` is a closed immersion over it (a section of
the separated `P → C` over the generic fibre, where `β = h̄ ≫ π` is an isomorphism).
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Geometry.ModificationCenter (isomorphismOpen center)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Normalization

variable {Y P : Scheme.{u}} (g : Y ⟶ P) [IsProper g] [IsIntegral Y]

/-- **The normalization map is an isomorphism where `g` is a closed immersion**: if
`g ∣_ O : g⁻¹O → O` is a closed immersion, then `b = g.toNormalization` is an isomorphism over
`ν⁻¹O`, `ν = g.fromNormalization`: `b ∣_ ν⁻¹O` is a closed immersion (its composite with the
separated `ν ∣_ O` is `g ∣_ O`), surjective (`b` is proper and dominant) and the target is
reduced. -/
theorem isIso_toNormalization_restrict (O : P.Opens) [IsClosedImmersion (g ∣_ O)] :
    IsIso (g.toNormalization ∣_ (g.fromNormalization ⁻¹ᵁ O)) := by
  have : IsProper g.toNormalization := isProper_toNormalization g
  have hcomp : g.toNormalization ∣_ (g.fromNormalization ⁻¹ᵁ O) ≫ g.fromNormalization ∣_ O =
      (g.toNormalization ≫ g.fromNormalization) ∣_ O :=
    (morphismRestrict_comp g.toNormalization g.fromNormalization O).symm
  have h1 : IsClosedImmersion ((g.toNormalization ≫ g.fromNormalization) ∣_ O) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  have : IsClosedImmersion
      (g.toNormalization ∣_ (g.fromNormalization ⁻¹ᵁ O) ≫ g.fromNormalization ∣_ O) := by
    rw [hcomp]
    exact h1
  have : IsClosedImmersion (g.toNormalization ∣_ (g.fromNormalization ⁻¹ᵁ O)) :=
    IsClosedImmersion.of_comp _ (g.fromNormalization ∣_ O)
  have : Surjective g.toNormalization := inferInstance
  have : Surjective (g.toNormalization ∣_ (g.fromNormalization ⁻¹ᵁ O)) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
  exact isIso_of_isClosedImmersion_of_surjective _

end Normalization

section Base

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {Y P C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (π : P ⟶ C) (g : Y ⟶ P)

/-- The open generic point of `Spec V`. -/
def genericOpen (V : Type u) [CommRing V] [IsDomain V] [Finite (PrimeSpectrum V)] :
    (Spec (CommRingCat.of V)).Opens :=
  ⟨{genericPoint (Spec (CommRingCat.of V))},
    Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite (CommRingCat.of V)⟩

theorem coe_genericOpen : (genericOpen V : Set (Spec (CommRingCat.of V))) =
    {genericPoint (Spec (CommRingCat.of V))} := rfl

instance quasiCompact_genericOpen_ι : QuasiCompact (genericOpen V).ι := by
  have : CompactSpace (genericOpen V) := isCompact_iff_compactSpace.mp
    (show IsCompact (genericOpen V : Set (Spec (CommRingCat.of V))) from
      (Set.finite_singleton _).isCompact)
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := (genericOpen V).ι)).mpr
    inferInstance

/-- **An η-modification is an isomorphism over the generic fibre** (lane LIM3's
`isIso_morphismRestrict_of_isIso_fiberMap`). -/
theorem isIso_restrict_genericOpen {X : Scheme.{u}} (β : X ⟶ C) (hβ : Curves.IsEtaModification β φ) :
    IsIso (β ∣_ (φ ⁻¹ᵁ genericOpen V)) := by
  have := hβ.isIso_fiberMap
  exact Limits.SpreadModification.isIso_morphismRestrict_of_isIso_fiberMap β φ (genericOpen V) rfl

/-- **`g` is a closed immersion over the generic fibre**: `g ≫ π = β` is an isomorphism there,
so `g` is a section of the separated `π`. -/
theorem isClosedImmersion_restrict_genericOpen [IsSeparated π] (β : Y ⟶ C) (hg : g ≫ π = β)
    (hβ : Curves.IsEtaModification β φ) :
    IsClosedImmersion (g ∣_ (π ⁻¹ᵁ (φ ⁻¹ᵁ genericOpen V))) := by
  have hiso := isIso_restrict_genericOpen φ β hβ
  have hcomp : g ∣_ (π ⁻¹ᵁ (φ ⁻¹ᵁ genericOpen V)) ≫ π ∣_ (φ ⁻¹ᵁ genericOpen V) =
      (g ≫ π) ∣_ (φ ⁻¹ᵁ genericOpen V) :=
    (morphismRestrict_comp g π _).symm
  have h1 : IsClosedImmersion ((g ≫ π) ∣_ (φ ⁻¹ᵁ genericOpen V)) := by
    rw [hg]
    infer_instance
  have : IsClosedImmersion
      (g ∣_ (π ⁻¹ᵁ (φ ⁻¹ᵁ genericOpen V)) ≫ π ∣_ (φ ⁻¹ᵁ genericOpen V)) := by
    rw [hcomp]
    exact h1
  exact IsClosedImmersion.of_comp _ (π ∣_ (φ ⁻¹ᵁ genericOpen V))

end Base

section QuasiFinite

variable {X Y Z : Scheme.{u}}

/-- **No proper specializations in the fibres of a locally quasi-finite morphism** (the fibres
are discrete, `Scheme.Hom.isDiscrete_preimage_singleton`). -/
theorem eq_of_specializes_of_apply_eq (f : X ⟶ Y) [LocallyQuasiFinite f] {x z : X} (h : x ⤳ z)
    (hf : f x = f z) : x = z := by
  obtain ⟨u, hu, hus⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1
    (f.isDiscrete_preimage_singleton (f z)) z rfl
  have hzu : z ∈ u ∩ f ⁻¹' {f z} := by
    rw [hus]
    rfl
  have : x ∈ u ∩ f ⁻¹' {f z} := ⟨h.mem_open hu hzu.1, hf⟩
  rw [hus] at this
  exact this

/-- **Contraction through a locally quasi-finite map**: `b` maps the closure of `w` to a point iff
`b ≫ ν` does, for `ν` locally quasi-finite (e.g. finite). -/
theorem image_closure_subsingleton_iff_comp (b : X ⟶ Y) (ν : Y ⟶ Z) [LocallyQuasiFinite ν]
    (w : X) : (b '' closure {w}).Subsingleton ↔ ((b ≫ ν) '' closure {w}).Subsingleton := by
  constructor
  · intro h
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
    exact h.image _
  · intro h
    have key : ∀ z ∈ closure ({w} : Set X), b z = b w := by
      intro z hz
      have hsp : b w ⤳ b z := (specializes_iff_mem_closure.2 hz).map b.continuous
      have heq : ν (b w) = ν (b z) := h ⟨w, subset_closure rfl, rfl⟩ ⟨z, hz, rfl⟩
      exact (eq_of_specializes_of_apply_eq ν hsp heq).symm
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    rw [key z hz, key z' hz']

end QuasiFinite

section Main

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {Y P C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (π : P ⟶ C) (g : Y ⟶ P)
  (β : Y ⟶ C) [IsIntegral Y] [IsProper g] [IsSeparated (π ≫ φ)]
  [LocallyOfFinitePresentation (π ≫ φ)] [Flat (β ≫ φ)]

include φ in
/-- `b ≫ β'' = β` for `b = g.toNormalization`, `β'' = g.fromNormalization ≫ π`. -/
theorem toNormalization_comp_eq (hg : g ≫ π = β) :
    g.toNormalization ≫ g.fromNormalization ≫ π = β := by
  rw [Scheme.Hom.toNormalization_fromNormalization_assoc, hg]

omit [IsIntegral Y] [IsProper g] [IsSeparated (π ≫ φ)] [LocallyOfFinitePresentation (π ≫ φ)] in
theorem flat_comp_of_eq (hg : g ≫ π = β) : Flat (g ≫ π ≫ φ) := by
  rw [← Category.assoc, hg]
  infer_instance

omit [IsIntegral Y] [IsProper g] [IsSeparated (π ≫ φ)] [LocallyOfFinitePresentation (π ≫ φ)]
  [Flat (β ≫ φ)] in
theorem isProjectiveOver_comp_of_eq (hg : g ≫ π = β) (hY : IsProjectiveOver (β ≫ φ)) :
    IsProjectiveOver (g ≫ π ≫ φ) := by
  rw [← Category.assoc, hg]
  exact hY

/-- `g` is projective relative to `P → Spec V` (cancellation). -/
theorem isRelativelyProjective_contracting (hg : g ≫ π = β) (hY : IsProjectiveOver (β ≫ φ)) :
    DeJong.IsRelativelyProjective (π ≫ φ) g :=
  isRelativelyProjective_of_isProjectiveOver_comp (π ≫ φ) g (isProjectiveOver_comp_of_eq φ π g β hg hY)

/-- **The blow-down is projective over `V`** (blueprint `lem:sm-bdg-stein`; Stein finiteness and
Codex's "finite over projective is projective"). -/
theorem isProjectiveOver_blowDown (hP : IsProjectiveOver (π ≫ φ)) (hg : g ≫ π = β)
    (hY : IsProjectiveOver (β ≫ φ)) : IsProjectiveOver ((g.fromNormalization ≫ π) ≫ φ) := by
  have := flat_comp_of_eq φ π g β hg
  rw [Category.assoc]
  exact isProjectiveOver_fromNormalization (π ≫ φ) g hP (isProjectiveOver_comp_of_eq φ π g β hg hY)

/-- **The blow-down is flat over `V`** (lane T44A's `flat_normalization`). -/
theorem flat_blowDown (hg : g ≫ π = β) (hY : IsProjectiveOver (β ≫ φ)) :
    Flat ((g.fromNormalization ≫ π) ≫ φ) := by
  have := flat_comp_of_eq φ π g β hg
  rw [Category.assoc]
  exact flat_normalization g (π ≫ φ) (isRelativelyProjective_contracting φ π g β hg hY)

/-- **The blow-down is of finite presentation over `V`** (lane T44A's
`locallyOfFinitePresentation_normalization`). -/
theorem locallyOfFinitePresentation_blowDown (hg : g ≫ π = β) (hY : IsProjectiveOver (β ≫ φ)) :
    LocallyOfFinitePresentation ((g.fromNormalization ≫ π) ≫ φ) := by
  have := flat_comp_of_eq φ π g β hg
  rw [Category.assoc]
  exact locallyOfFinitePresentation_normalization g (π ≫ φ)
    (isRelativelyProjective_contracting φ π g β hg hY)

/-- **`b : Y → Y''` is projective relative to `Y'' → Spec V`.** -/
theorem isRelativelyProjective_blowDown (hg : g ≫ π = β) (hY : IsProjectiveOver (β ≫ φ)) :
    DeJong.IsRelativelyProjective ((g.fromNormalization ≫ π) ≫ φ) g.toNormalization := by
  have := flat_comp_of_eq φ π g β hg
  rw [Category.assoc]
  exact isRelativelyProjective_toNormalization (π ≫ φ) g (isProjectiveOver_comp_of_eq φ π g β hg hY)

/-- **`b` is an isomorphism over the generic fibre.** -/
theorem isIso_toNormalization_restrict_genericOpen (hg : g ≫ π = β)
    (hβ : Curves.IsEtaModification β φ) :
    IsIso (g.toNormalization ∣_ (((g.fromNormalization ≫ π) ≫ φ) ⁻¹ᵁ genericOpen V)) := by
  have : IsSeparated π := IsSeparated.of_comp π φ
  have := isClosedImmersion_restrict_genericOpen φ π g β hg hβ
  exact isIso_toNormalization_restrict g (π ⁻¹ᵁ (φ ⁻¹ᵁ genericOpen V))

omit [IsProper g] [IsSeparated (π ≫ φ)] [LocallyOfFinitePresentation (π ≫ φ)] in
/-- A point of `Y` over the generic point of `Spec V`. -/
theorem exists_apply_eq_genericPoint :
    ∃ y : Y, (β ≫ φ) y = genericPoint (Spec (CommRingCat.of V)) := by
  obtain ⟨y, hy⟩ := genericPoint_mem_range_of_flat (β ≫ φ)
  exact ⟨y, hy⟩

/-- **`b : Y → Y''` is a modification** (blueprint `lem:sm-bdg-stein`): proper (lane T44A's
`isProper_toNormalization`), between integral schemes, and an isomorphism over the nonempty
generic fibre (`isIso_toNormalization_restrict_genericOpen`), hence birational (Codex's
`birationalOver_id_of_isIso_morphismRestrict`). -/
theorem isModification_blowDown (hg : g ≫ π = β) (hβ : Curves.IsEtaModification β φ) :
    IsModification g.toNormalization where
  toIsProper := isProper_toNormalization g
  sourceIntegral := inferInstance
  targetIntegral := inferInstance
  birational := by
    have := isIso_toNormalization_restrict_genericOpen φ π g β hg hβ
    refine birationalOver_id_of_isIso_morphismRestrict g.toNormalization
      (((g.fromNormalization ≫ π) ≫ φ) ⁻¹ᵁ genericOpen V) ?_
    obtain ⟨y, hy⟩ := exists_apply_eq_genericPoint φ β
    refine ⟨g.toNormalization y, ?_⟩
    have : (g.toNormalization ≫ (g.fromNormalization ≫ π) ≫ φ) y =
        genericPoint (Spec (CommRingCat.of V)) := by
      rw [← Category.assoc, toNormalization_comp_eq φ π g β hg]
      exact hy
    exact this

/-- **`b : Y → Y''` is an η-modification** (lane LIM3's `isEtaModification_of_isIso_morphismRestrict`). -/
theorem isEtaModification_blowDown (hg : g ≫ π = β) (hY : IsProjectiveOver (β ≫ φ))
    (hβ : Curves.IsEtaModification β φ) :
    Curves.IsEtaModification g.toNormalization ((g.fromNormalization ≫ π) ≫ φ) := by
  have : IsProper g.toNormalization := isProper_toNormalization g
  have := flat_blowDown φ π g β hg hY
  have : Flat (g.toNormalization ≫ (g.fromNormalization ≫ π) ≫ φ) := by
    rw [← Category.assoc, toNormalization_comp_eq φ π g β hg]
    infer_instance
  have := isIso_toNormalization_restrict_genericOpen φ π g β hg hβ
  exact Limits.SpreadModification.isEtaModification_of_isIso_morphismRestrict _ _ (genericOpen V)
    ⟨_, rfl⟩

/-- **The new structure map `β'' : Y'' → C` is an η-modification**: `β = b ≫ β''` and `b` are
isomorphisms over the generic fibre. -/
theorem isEtaModification_blowDown_base [Flat φ] [IsSeparated φ] (hP : IsProjectiveOver (π ≫ φ))
    (hg : g ≫ π = β) (hY : IsProjectiveOver (β ≫ φ)) (hβ : Curves.IsEtaModification β φ) :
    Curves.IsEtaModification (g.fromNormalization ≫ π) φ := by
  have : IsProper ((g.fromNormalization ≫ π) ≫ φ) :=
    (isProjectiveOver_blowDown φ π g β hP hg hY).isProper
  have : IsProper (g.fromNormalization ≫ π) := IsProper.of_comp _ φ
  have := flat_blowDown φ π g β hg hY
  have h1 : IsIso ((g.toNormalization ≫ g.fromNormalization ≫ π) ∣_ (φ ⁻¹ᵁ genericOpen V)) := by
    rw [toNormalization_comp_eq φ π g β hg]
    exact isIso_restrict_genericOpen φ β hβ
  rw [morphismRestrict_comp] at h1
  have : IsIso (g.toNormalization ∣_ ((g.fromNormalization ≫ π) ⁻¹ᵁ (φ ⁻¹ᵁ genericOpen V))) :=
    isIso_toNormalization_restrict_genericOpen φ π g β hg hβ
  have : IsIso ((g.fromNormalization ≫ π) ∣_ (φ ⁻¹ᵁ genericOpen V)) :=
    IsIso.of_isIso_comp_left (g.toNormalization ∣_ _) _
  exact Limits.SpreadModification.isEtaModification_of_isIso_morphismRestrict _ φ (genericOpen V)
    ⟨_, rfl⟩

/-- **`b` contracts exactly what `g` contracts** (`g.fromNormalization` is finite, so it
contracts no curve): `b '' closure {w}` is a point iff `g '' closure {w}` is. -/
theorem image_closure_subsingleton_toNormalization_iff (hg : g ≫ π = β)
    (hY : IsProjectiveOver (β ≫ φ)) (w : Y) :
    (g.toNormalization '' closure {w}).Subsingleton ↔ (g '' closure {w}).Subsingleton := by
  have := flat_comp_of_eq φ π g β hg
  have := isFinite_fromNormalization_of_isProjectiveOver (π ≫ φ) g
    (isProjectiveOver_comp_of_eq φ π g β hg hY)
  rw [image_closure_subsingleton_iff_comp g.toNormalization g.fromNormalization w,
    Scheme.Hom.toNormalization_fromNormalization]

end Main

end

end DeJongAlterations.StableModification.BlowDown
