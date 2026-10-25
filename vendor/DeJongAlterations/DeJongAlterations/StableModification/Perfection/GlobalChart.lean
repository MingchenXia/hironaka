/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL-GLOBAL)
-/
import DeJongAlterations.Geometry.NormalizationInExtension

/-!
# Local rings of the normalization in a purely inseparable extension

Blueprint chapter `sm-dj-perfection-global`, node `lem:sm-dj-perfection-global-stalks` (new route,
not in de Jong 1996).

Let `X` be an integral scheme and `L` a finite extension of its function field `K(X)`. Codex's
`Geometry.NormalizationInExtension.normalization X L` is glued from the spectra of the integral
closures `C_U` of the coordinate rings `Γ(X, U)` in `L`, for nonempty affine opens `U ⊆ X`
(`chartInclusion X L U : Spec C_U ⟶ X₁`), and its function field is identified with `L` by
`normalizationFunctionFieldEquiv`, built from one chosen chart.

* `functionFieldEquiv_eq_of_isPurelyInseparable`: if `L / K(X)` is purely inseparable, the
  identifications of the function field with `L` through the different charts all agree: a
  purely inseparable extension has only one `K(X)`-embedding into `L`.
* `stalkToField x`: the local ring of `X₁` at `x`, embedded into `L` through the function field.
* `stalkToField_inv_stalkMap_toStalk`: at a point `x = chartInclusion U P` of the chart `U`, this
  embedding restricts to the inclusion `C_U ⊆ L` on the image of `C_U` in the local ring
  `(C_U)_P`.
* `exists_stalkToField_eq`, `exists_stalkToField_mul_eq_one`, `exists_stalkToField_mul_eq`:
  consequently the image of the local ring of `X₁` at `x` in `L` contains `C_U`, contains the
  inverses of the elements of `C_U ∖ P`, and consists of fractions `c / s` with `c, s ∈ C_U`,
  `s ∉ P`; that is, it is the localization `(C_U)_P` inside `L`.
* `stalkToField_comp_stalkMap`: the local ring map `O_{X, φ(x)} ⟶ O_{X₁, x}` of the structure
  morphism `φ` is the inclusion of images in `L` (through `K(X) ⊆ L`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.StableModification.Perfection

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Geometry Geometry.NormalizationInExtension

variable {X : Scheme.{u}} [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]
  [FiniteDimensional X.functionField L]

attribute [local instance] sectionsAlgebra

/-- In a purely inseparable extension, the chart identifications of the function field of the
normalization with `L` do not depend on the chart. -/
theorem functionFieldEquiv_eq_of_isPurelyInseparable [IsPurelyInseparable X.functionField L]
    (U V : NonemptyAffineOpen X) : functionFieldEquiv L U = functionFieldEquiv L V := by
  let := normalizationFunctionFieldAlgebra (X := X) L
  have h : (functionFieldAlgEquiv L V).toAlgHom.comp (functionFieldAlgEquiv L U).symm.toAlgHom =
      AlgHom.id X.functionField L := Subsingleton.elim _ _
  ext y
  have := DFunLike.congr_fun h (functionFieldAlgEquiv L U y)
  rw [AlgHom.comp_apply, AlgHom.id_apply] at this
  change (functionFieldAlgEquiv L V) ((functionFieldAlgEquiv L U).symm
    (functionFieldAlgEquiv L U y)) = _ at this
  rw [AlgEquiv.symm_apply_apply] at this
  exact this.symm

/-- In a purely inseparable extension, the chosen function field identification of the
normalization is the one of any chart. -/
theorem normalizationFunctionFieldEquiv_eq [IsPurelyInseparable X.functionField L]
    (U : NonemptyAffineOpen X) :
    normalizationFunctionFieldEquiv (X := X) L = functionFieldEquiv L U :=
  functionFieldEquiv_eq_of_isPurelyInseparable L _ U

/-- The local ring of the normalization at `x`, embedded into `L` through the function field. -/
def stalkToField (x : normalization X L) : (normalization X L).presheaf.stalk x →+* L :=
  (normalizationFunctionFieldEquiv (X := X) L).toRingHom.comp
    (algebraMap _ (normalization X L).functionField)

theorem stalkToField_injective (x : normalization X L) : Function.Injective (stalkToField L x) :=
  (normalizationFunctionFieldEquiv (X := X) L).injective.comp
    (IsFractionRing.injective _ (normalization X L).functionField)

/-- The embedding of a local ring into `L` is the generic-stalk map followed by the identification
of the function field with `L`. -/
theorem stalkToField_apply (x : normalization X L) (t : (normalization X L).presheaf.stalk x) :
    stalkToField L x t = normalizationFunctionFieldEquiv (X := X) L
      (algebraMap _ (normalization X L).functionField t) := rfl

/-- The local ring map of the structure morphism `X₁ ⟶ X` is the inclusion of images in `L`. -/
theorem stalkToField_comp_stalkMap (x : normalization X L)
    (a : X.presheaf.stalk (normalizationStructure X L x)) :
    stalkToField L x ((normalizationStructure X L).stalkMap x a) =
      algebraMap X.functionField L (algebraMap _ X.functionField a) := by
  have h := congrArg (fun φ => φ.hom a) (functionFieldMap_stalk (normalizationStructure X L) x)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [stalkToField_apply, ← h]
  exact congrArg (fun φ : X.functionField →+* L => φ (algebraMap _ X.functionField a))
    (normalizationFunctionFieldEquiv_comp (X := X) L)

/-- **The chart computes the local rings.** At a point `chartInclusion U P` of the chart `U`, the
embedding of the local ring into `L` sends the image of `c ∈ C_U` to `c`. -/
theorem stalkToField_inv_stalkMap_toStalk [IsPurelyInseparable X.functionField L]
    (U : NonemptyAffineOpen X) (P : Spec (.of (closureRing L U))) (c : closureRing L U) :
    stalkToField L (chartInclusion X L U P)
      ((inv ((chartInclusion X L U).stalkMap P)).hom
        ((StructureSheaf.toStalk (closureRing L U) P).hom c)) = (c : L) := by
  set ι := chartInclusion X L U
  set t := (inv (ι.stalkMap P)).hom ((StructureSheaf.toStalk (closureRing L U) P).hom c)
  have ht : (ι.stalkMap P).hom t = (StructureSheaf.toStalk (closureRing L U) P).hom c := by
    change (inv (ι.stalkMap P) ≫ ι.stalkMap P).hom _ = _
    rw [IsIso.inv_hom_id]
    rfl
  rw [stalkToField_apply, normalizationFunctionFieldEquiv_eq L U]
  let := closureRing_isFractionRing L U
  change (IsLocalization.algEquiv (nonZeroDivisors (closureRing L U))
    (Spec (.of (closureRing L U))).functionField L)
      ((functionFieldMap ι).hom (algebraMap _ (normalization X L).functionField t)) = (c : L)
  have hstalk := congrArg (fun φ => φ.hom t) (functionFieldMap_stalk ι P)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hstalk
  rw [hstalk, ht]
  have h2 := congrArg (fun φ => φ.hom c) (toStalk_functionField (.of (closureRing L U)) P)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  refine (congrArg (IsLocalization.algEquiv (nonZeroDivisors (closureRing L U))
    (Spec (.of (closureRing L U))).functionField L) h2).trans ?_
  exact (IsLocalization.algEquiv (nonZeroDivisors (closureRing L U))
    (Spec (.of (closureRing L U))).functionField L).commutes c

variable [IsPurelyInseparable X.functionField L] (U : NonemptyAffineOpen X)
  (P : Spec (.of (closureRing L U)))

/-- The image of the local ring at a chart point contains the chart ring `C_U`. -/
theorem exists_stalkToField_eq (c : closureRing L U) :
    ∃ t, stalkToField L (chartInclusion X L U P) t = (c : L) :=
  ⟨_, stalkToField_inv_stalkMap_toStalk L U P c⟩

/-- The elements of `C_U` outside `P` are units of the local ring at `chartInclusion U P`. -/
theorem exists_stalkToField_mul_eq_one (s : closureRing L U) (hs : s ∉ P.asIdeal) :
    ∃ t, stalkToField L (chartInclusion X L U P) t * (s : L) = 1 := by
  set ι := chartInclusion X L U
  let O := (Spec.structureSheaf (closureRing L U)).presheaf.stalk P
  have : IsLocalization.AtPrime O P.asIdeal := StructureSheaf.IsLocalization.to_stalk _ P
  have hunit : IsUnit (algebraMap (closureRing L U) O s) :=
    IsLocalization.map_units O (⟨s, hs⟩ : P.asIdeal.primeCompl)
  obtain ⟨v, hv⟩ := hunit.exists_left_inv
  refine ⟨(inv (ι.stalkMap P)).hom v, ?_⟩
  rw [← stalkToField_inv_stalkMap_toStalk L U P s, ← map_mul, ← map_mul]
  change stalkToField L (ι P) ((inv (ι.stalkMap P)).hom (v * algebraMap _ O s)) = 1
  rw [hv, map_one, map_one]

/-- **The local ring at a chart point is `(C_U)_P` inside `L`.** Every element of the image is a
fraction `c / s` with `c, s ∈ C_U` and `s ∉ P`. -/
theorem exists_stalkToField_mul_eq
    (t : (normalization X L).presheaf.stalk (chartInclusion X L U P)) :
    ∃ c s : closureRing L U, s ∉ P.asIdeal ∧
      stalkToField L (chartInclusion X L U P) t * (s : L) = c := by
  let O := (Spec.structureSheaf (closureRing L U)).presheaf.stalk P
  have : IsLocalization.AtPrime O P.asIdeal := StructureSheaf.IsLocalization.to_stalk _ P
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj (S := O) P.asIdeal.primeCompl
    (show O from ((chartInclusion X L U).stalkMap P).hom t)
  refine ⟨c, s, s.2, ?_⟩
  have ht : t = (inv ((chartInclusion X L U).stalkMap P)).hom
      (((chartInclusion X L U).stalkMap P).hom t) := by
    change t = ((chartInclusion X L U).stalkMap P ≫ inv ((chartInclusion X L U).stalkMap P)).hom t
    rw [IsIso.hom_inv_id]
    rfl
  rw [← stalkToField_inv_stalkMap_toStalk L U P s, ← stalkToField_inv_stalkMap_toStalk L U P c,
    ← map_mul]
  conv_lhs => rw [ht]
  rw [← map_mul]
  congr 2

end DeJongAlterations.StableModification.Perfection

end
