/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness at a point and its affine-local form

Smoothness at a point is Mathlib's: for `f : X ⟶ Y` locally of finite presentation,
`x ∈ f.smoothLocus` means that the stalk map `𝒪_{Y, f x} → 𝒪_{X, x}` is formally smooth
(`Scheme.Hom.mem_smoothLocus`). This agrees with the definition of the sources, "`f` is smooth at
`x` when its restriction to some open neighbourhood of `x` is smooth" [Sta, Tag 01V9], with
[Sta, Tag 00TB] for the affine form; the agreement is `mem_smoothLocus_iff_exists_smooth` below.
Over a field `k`, indeed over any locally Noetherian base, a morphism locally of finite type is
locally of finite presentation (Mathlib's instance in `AlgebraicGeometry/Noetherian.lean`), so
`f.smoothLocus` makes sense for `X` locally of finite type over `k`, the standing hypothesis of
the comparison of smooth and regular points in this directory.

The reduction to the affine local statement ("the question is local", as in the proof of
[Sta, Tag 038X]): for `f : X ⟶ Spec k` and an affine open `U ∋ x`, the ring of sections
`S = Γ(X, U)` is a `k`-algebra through `k ≅ Γ(Spec k, ⊤) → Γ(X, U)` (`Scheme.Hom.sectionsAlgebra`),
of finite type when `f` is locally of finite type; with `𝔮 = hU.primeIdealOf ⟨x, hx⟩` the prime
of `x`, the point `x` lies in `f.smoothLocus` iff `S` is smooth at `𝔮` over `k` in Mathlib's sense
`Algebra.IsSmoothAt k 𝔮 := Algebra.FormallySmooth k (Localization.AtPrime 𝔮)`
(`mem_smoothLocus_iff_isSmoothAt`, from Mathlib's `formallySmooth_stalkMap_iff` applied to the
affine open `⊤` of `Spec k`, and the invariance of formal smoothness under the isomorphism
`k ≅ Γ(Spec k, ⊤)` of base rings). The stalk of `Spec k` at its unique point is `k`
(`isIso_toStalk_Spec_of_field`, as in the proof of Mathlib's
`Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`). The regular half of the reduction is
`Scheme.isRegularAt_iff_isRegularLocalRing_localization` in
`Hironaka/Algebra/RegularSmooth/Regular.lean`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y : Scheme.{u}}

/-- A point lies in the smooth locus of `f` iff the restriction of `f` to some open neighbourhood
of the point is smooth: Mathlib's smooth locus agrees with the definition of "smooth at `x`" of
[Sta, Tag 01V9] (and of [Sta, Tag 00TB] in the affine case). -/
theorem Scheme.Hom.mem_smoothLocus_iff_exists_smooth (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    {x : X} : x ∈ f.smoothLocus ↔ ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  constructor
  · intro hx
    obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk f x hx
    refine ⟨V, hxV, ?_⟩
    have : IsAffine U := hU
    have : IsAffine V := hV
    have hres : Smooth (f.resLE U V hVU) := by
      rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
      exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f U V hVU)).mpr H
    have := MorphismProperty.comp_mem @Smooth _ _ hres (inferInstance : Smooth U.ι)
    rwa [Scheme.Hom.resLE_comp_ι] at this
  · rintro ⟨U, hxU, hU⟩
    have h : (U.ι ≫ f).smoothLocus = ⊤ := (U.ι ≫ f).smoothLocus_eq_top
    have : (⟨x, hxU⟩ : U) ∈ U.ι ⁻¹ᵁ f.smoothLocus := by
      rw [Scheme.Hom.preimage_smoothLocus_eq, h]; trivial
    exact this

/-- Over a field, a morphism locally of finite type is locally of finite presentation (Mathlib's
instance for a locally Noetherian target, in `AlgebraicGeometry/Noetherian.lean`), so
`f.smoothLocus` is defined for `X` locally of finite type over `k`. -/
theorem Scheme.Hom.locallyOfFinitePresentation_of_field {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f :=
  inferInstance

/-- Formal smoothness of a ring map is unchanged by precomposition with a ring isomorphism (the
second half of `RingHom.FormallySmooth.respectsIso`, as an equivalence). -/
theorem _root_.RingHom.FormallySmooth.comp_ringEquiv_iff {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] (g : S →+* T) (e : R ≃+* S) :
    (g.comp e.toRingHom).FormallySmooth ↔ g.FormallySmooth := by
  refine ⟨fun H => ?_, fun H => RingHom.FormallySmooth.respectsIso.2 _ e H⟩
  have := RingHom.FormallySmooth.respectsIso.2 _ e.symm H
  rwa [RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom, RingHom.comp_id] at this

section sectionsAlgebra

variable {k : Type u} [CommRing k]

/-- For `f : X ⟶ Spec k`, the `k`-algebra structure on the sections of `X` over an open `U`, by
`k ≅ Γ(Spec k, ⊤) → Γ(X, U)` (`Scheme.ΓSpecIso` followed by `f.appLE ⊤ U`): the ring `S` of an
affine open `U = Spec S` becomes a `k`-algebra. Not an instance: the structure depends on `f`. -/
@[instance_reducible]
noncomputable def Scheme.Hom.sectionsAlgebra (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

theorem Scheme.Hom.algebraMap_sectionsAlgebra (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    letI := f.sectionsAlgebra U
    algebraMap k Γ(X, U) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom :=
  rfl

/-- For `f : X ⟶ Spec k` locally of finite type and `U` an affine open, `Γ(X, U)` is a
`k`-algebra of finite type (for the structure `Scheme.Hom.sectionsAlgebra`). -/
theorem Scheme.Hom.finiteType_sectionsAlgebra (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    Algebra.FiniteType k Γ(X, U) := by
  let := f.sectionsAlgebra U
  exact (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The affine-local form of smoothness at a point ([Sta, Tag 00TB]; "the question is local" in
the proof of [Sta, Tag 038X]): for `f : X ⟶ Spec k` locally of finite presentation and an affine
open `U ∋ x` with `𝔮 = hU.primeIdealOf ⟨x, hx⟩` the prime of `x`, the point `x` lies in the smooth
locus of `f` iff `Γ(X, U)` is smooth at `𝔮` over `k`: `Algebra.IsSmoothAt k 𝔮`, i.e. `Γ(X, U)_𝔮`
is formally smooth over `k`. Mathlib's `formallySmooth_stalkMap_iff` for the affine open `⊤` of
`Spec k`, then the base ring `Γ(Spec k, ⊤)` is replaced by `k` along `Scheme.ΓSpecIso`. -/
theorem Scheme.Hom.mem_smoothLocus_iff_isSmoothAt (f : X ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI := f.sectionsAlgebra U
    x ∈ f.smoothLocus ↔ Algebra.IsSmoothAt k (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let := f.sectionsAlgebra U
  let := (f.appLE ⊤ U le_top).hom.toAlgebra
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) U hU le_top hx]
  change Algebra.FormallySmooth Γ(Spec (.of k), ⊤) (Localization.AtPrime _) ↔
    Algebra.FormallySmooth k (Localization.AtPrime _)
  rw [← RingHom.formallySmooth_algebraMap, ← RingHom.formallySmooth_algebraMap,
    IsScalarTower.algebraMap_eq k Γ(X, U) (Localization.AtPrime _),
    IsScalarTower.algebraMap_eq Γ(Spec (.of k), ⊤) Γ(X, U) (Localization.AtPrime _)]
  exact (RingHom.FormallySmooth.comp_ringEquiv_iff _
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv).symm

end sectionsAlgebra

/-- The stalk of `Spec k` at its point is `k` (as in the proof of Mathlib's
`Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`): for a field `k`, the canonical map
`k → 𝒪_{Spec k, y}` is an isomorphism at the unique point `y` of `Spec k`. -/
theorem isIso_toStalk_Spec_of_field {k : Type u} [Field k] (y : Spec (.of k)) :
    IsIso (StructureSheaf.toStalk k y) := by
  obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  have h := stalkClosedPointIso_inv (.of k)
  have : IsIso (stalkClosedPointIso (.of k)).inv := inferInstance
  rwa [h] at this

end AlgebraicGeometry
