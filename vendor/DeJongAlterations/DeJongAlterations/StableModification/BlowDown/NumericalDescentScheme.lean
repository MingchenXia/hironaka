/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NumericalDescentAlgebra

/-!
# Base change of a scheme along an extension of algebraically closed fields

Let `k` be an algebraically closed field, `Y` a scheme locally of finite type over `k`,
`ψ : k → K` a field extension and `Y_K = Y ×_k K` with projection `π : Y_K → Y`. This file proves
the properties of `π` used to compare the fibre of a curve over a point with algebraically closed
residue field with its geometric fibres (`BlowDown.NoClosedExc.NumericalDescent`; Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2):

* `surjective_fst_of_isPullback`: `π` is surjective;
* `sectionsEquiv`: on an affine open `U ⊆ Y`, `Γ(π⁻¹U, 𝒪) ≅ K ⊗_k Γ(U, 𝒪)` (lane COH2's
  `Cohomology.isPushout_baseChange_sections`);
* `isReduced_of_isPullback`: `Y_K` is reduced if `Y` is (`isReduced_tensorProduct_of_isAlgClosed`);
* `irreducibleSpace_of_isPullback`: `Y_K` is irreducible if `Y` is integral
  (`isDomain_tensorProduct_of_isAlgClosed` on the affine opens, which pairwise meet).

All statements are for an arbitrary pullback square `P → Y`, `P → Spec K` of `Y → Spec k` along
`Spec K → Spec k`.

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-base-change-scheme`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology TensorProduct

namespace DeJongAlterations.StableModification.BlowDown.NumericalDescent

universe u

open Cohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Topology

/-- **A space covered by pairwise meeting irreducible open sets is irreducible.** -/
theorem irreducibleSpace_of_cover {X : Type*} [TopologicalSpace X] [Nonempty X] {ι : Type*}
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hcov : ∀ x, ∃ i, x ∈ W i)
    (hirr : ∀ i, IsPreirreducible (W i)) (hint : ∀ i j, (W i ∩ W j).Nonempty) :
    IrreducibleSpace X := by
  have hpre : IsPreirreducible (Set.univ : Set X) := by
    intro u v hu hv hxu' hyv'
    obtain ⟨x, -, hxu⟩ := hxu'
    obtain ⟨y, -, hyv⟩ := hyv'
    obtain ⟨i, hxi⟩ := hcov x
    obtain ⟨j, hyj⟩ := hcov y
    obtain ⟨z, hzi, hzu, hzj⟩ := hirr i u (W j) hu (hW j) ⟨x, hxi, hxu⟩ (hint i j)
    obtain ⟨w, hwj, hwu, hwv⟩ := hirr j u v hu hv ⟨z, hzj, hzu⟩ ⟨y, hyj, hyv⟩
    exact ⟨w, trivial, hwu, hwv⟩
  exact { isPreirreducible_univ := hpre, toNonempty := inferInstance }

end Topology

section BaseChange

variable {k K : Type u} [Field k] [Field K] (ψ : k →+* K) {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of k))

instance : Subsingleton (Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

instance : Nonempty (Spec (CommRingCat.of K)) :=
  inferInstanceAs (Nonempty (PrimeSpectrum K))

/-- `Spec K → Spec k` is surjective. -/
instance surjective_specMap : Surjective (Spec.map (CommRingCat.ofHom ψ)) :=
  ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

/-- **The projection of a base change along a field extension is surjective.** -/
theorem surjective_fst_of_isPullback {P : Scheme.{u}} {fst : P ⟶ Y}
    {snd : P ⟶ Spec (CommRingCat.of K)} (H : IsPullback fst snd q (Spec.map (CommRingCat.ofHom ψ))) :
    Function.Surjective fst :=
  (MorphismProperty.of_isPullback H.flip (surjective_specMap ψ)).surj

/-- The algebra structure `k → Γ(U, 𝒪_Y)` of an open `U`. -/
abbrev sectionsAlgebra (U : Y.Opens) : Algebra k Γ(Y, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appLE ⊤ U le_top).hom.toAlgebra

/-- **The sections of the base change over the preimage of an affine open**:
`Γ(π⁻¹U, 𝒪) ≅ K ⊗_k Γ(U, 𝒪)` (`Cohomology.isPushout_baseChange_sections`). -/
theorem nonempty_sectionsEquiv {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra q U
    letI := ψ.toAlgebra
    Nonempty (Γ(pullback q (Spec.map (CommRingCat.ofHom ψ)), bcFst ψ q ⁻¹ᵁ U) ≃+*
      K ⊗[k] Γ(Y, U)) := by
  have H := isPushout_baseChange_sections ψ q hU
  let A := Γ(Y, U)
  let S' := Γ(pullback q (Spec.map (CommRingCat.ofHom ψ)), bcFst ψ q ⁻¹ᵁ U)
  let fA : CommRingCat.of k ⟶ Γ(Y, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appLE ⊤ U le_top
  let fK : CommRingCat.of K ⟶ S' :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (bcSnd ψ q).appLE ⊤ (bcFst ψ q ⁻¹ᵁ U) le_top
  let g : Γ(Y, U) ⟶ S' := (bcFst ψ q).appLE U (bcFst ψ q ⁻¹ᵁ U) le_rfl
  let _ : Algebra k A := fA.hom.toAlgebra
  let _ : Algebra k K := ψ.toAlgebra
  let _ : Algebra K S' := fK.hom.toAlgebra
  let _ : Algebra A S' := g.hom.toAlgebra
  let _ : Algebra k S' := (g.hom.comp fA.hom).toAlgebra
  have : IsScalarTower k A S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k K S' := IsScalarTower.of_algebraMap_eq' (by
    have := congrArg CommRingCat.Hom.hom H.w
    simp only [CommRingCat.hom_comp] at this
    exact this.symm)
  have hpush : Algebra.IsPushout k K A S' := CommRingCat.isPushout_iff_isPushout.mp H
  exact ⟨(Algebra.IsPushout.equiv k K A S').toRingEquiv.symm⟩

/-- The preimage of an affine open under the base change projection is affine. -/
theorem isAffineOpen_preimage_bcFst {U : Y.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (bcFst ψ q ⁻¹ᵁ U) := by
  have : IsAffineHom (Spec.map (CommRingCat.ofHom ψ)) := inferInstance
  have : IsAffineHom (bcFst ψ q) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback q _).flip this
  exact hU.preimage _

variable [IsAlgClosed k] [LocallyOfFiniteType q]

/-- The sections over an affine open are of finite type over `k`. -/
theorem finiteType_sections {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra q U
    Algebra.FiniteType k Γ(Y, U) :=
  Geometry.NormalizationFinite.affineSections_finiteType q ⟨U, hU⟩

/-- **The sections of the base change over the preimage of an affine open are reduced** if `Y`
is reduced. -/
theorem isReduced_sections_preimage [IsReduced Y] {U : Y.Opens} (hU : IsAffineOpen U) :
    _root_.IsReduced Γ(pullback q (Spec.map (CommRingCat.ofHom ψ)), bcFst ψ q ⁻¹ᵁ U) := by
  obtain ⟨e⟩ := nonempty_sectionsEquiv ψ q hU
  letI := sectionsAlgebra q U
  letI := ψ.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := finiteType_sections q hU
  have : _root_.IsReduced (Γ(Y, U) ⊗[k] K) := isReduced_tensorProduct_of_isAlgClosed
  have : _root_.IsReduced (K ⊗[k] Γ(Y, U)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k K Γ(Y, U)).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm k K Γ(Y, U)).injective
  exact isReduced_of_injective e.toRingHom e.injective

/-- **The sections of the base change over the preimage of a nonempty affine open are a domain**
if `Y` is integral. -/
theorem isDomain_sections_preimage [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    IsDomain Γ(pullback q (Spec.map (CommRingCat.ofHom ψ)), bcFst ψ q ⁻¹ᵁ U) := by
  obtain ⟨e⟩ := nonempty_sectionsEquiv ψ q hU
  letI := sectionsAlgebra q U
  letI := ψ.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := finiteType_sections q hU
  have : IsDomain (Γ(Y, U) ⊗[k] K) := isDomain_tensorProduct_of_isAlgClosed
  have : IsDomain (K ⊗[k] Γ(Y, U)) :=
    (Algebra.TensorProduct.comm k K Γ(Y, U)).injective.isDomain
      (Algebra.TensorProduct.comm k K Γ(Y, U)).toRingEquiv.toRingHom
  exact e.injective.isDomain e.toRingHom

/-- **The base change of a reduced scheme to an extension of `k = k̄` is reduced.** -/
theorem isReduced_baseChange [IsReduced Y] :
    IsReduced (pullback q (Spec.map (CommRingCat.ofHom ψ))) := by
  set P := pullback q (Spec.map (CommRingCat.ofHom ψ))
  have hst : ∀ x : P, _root_.IsReduced (P.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := bcFst ψ q x) (U := ⊤) trivial
    have hW := isAffineOpen_preimage_bcFst ψ q hU
    have hxW : x ∈ bcFst ψ q ⁻¹ᵁ U := hxU
    have : _root_.IsReduced Γ(P, bcFst ψ q ⁻¹ᵁ U) := isReduced_sections_preimage ψ q hU
    let _ : Algebra Γ(P, bcFst ψ q ⁻¹ᵁ U) (P.presheaf.stalk x) :=
      (P.presheaf.germ _ x hxW).hom.toAlgebra
    have := hW.isLocalization_stalk ⟨x, hxW⟩
    exact isReduced_localizationPreserves (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl _
      inferInstance
  exact isReduced_of_isReduced_stalk P

/-- **The base change of an integral scheme to an extension of `k = k̄` is irreducible**: it is
covered by the preimages of the nonempty affine opens of `Y`, which are spectra of domains
(`isDomain_sections_preimage`) and pairwise meet. -/
theorem irreducibleSpace_baseChange [IsIntegral Y] :
    IrreducibleSpace (pullback (C := Scheme.{u}) q (Spec.map (CommRingCat.ofHom ψ))) := by
  set P := pullback q (Spec.map (CommRingCat.ofHom ψ))
  have hsurj : Function.Surjective (bcFst ψ q) :=
    surjective_fst_of_isPullback ψ q (IsPullback.of_hasPullback _ _)
  have : Nonempty P := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    obtain ⟨x, -⟩ := hsurj y
    exact ⟨x⟩
  let ι := {U : Y.affineOpens // ((U : Y.Opens) : Set Y).Nonempty}
  let W : ι → Set P := fun U => (bcFst ψ q ⁻¹ᵁ U.1.1 : P.Opens)
  refine irreducibleSpace_of_cover W (fun U => (bcFst ψ q ⁻¹ᵁ U.1.1).isOpen) ?_ ?_ ?_
  · intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := bcFst ψ q x) (U := ⊤) trivial
    exact ⟨⟨⟨U, hU⟩, ⟨_, hxU⟩⟩, hxU⟩
  · intro U
    have hU := U.1.2
    have hW := isAffineOpen_preimage_bcFst ψ q hU
    have : Nonempty (U.1.1 : Y.Opens) := U.2.to_subtype
    have : IsDomain Γ(P, bcFst ψ q ⁻¹ᵁ U.1.1) := isDomain_sections_preimage ψ q hU
    have : IsAffine (bcFst ψ q ⁻¹ᵁ U.1.1 : P.Opens) := hW
    obtain ⟨y, hy⟩ := U.2
    obtain ⟨x, hx⟩ := hsurj y
    have : Nonempty (bcFst ψ q ⁻¹ᵁ U.1.1 : P.Opens) := ⟨⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact hy⟩⟩
    have : IsDomain Γ((bcFst ψ q ⁻¹ᵁ U.1.1 : P.Opens), ⊤) :=
      (Scheme.Opens.topIso _).commRingCatIsoToRingEquiv.injective.isDomain
        (Scheme.Opens.topIso _).commRingCatIsoToRingEquiv.toRingHom
    have : IsIntegral (bcFst ψ q ⁻¹ᵁ U.1.1 : P.Opens) := isIntegral_of_isAffine_of_isDomain _
    have h := (IrreducibleSpace.isIrreducible_univ (bcFst ψ q ⁻¹ᵁ U.1.1 : P.Opens)).image
      Subtype.val continuous_subtype_val.continuousOn
    rw [Set.image_univ, Subtype.range_coe] at h
    exact h.isPreirreducible
  · intro U V
    obtain ⟨y, hyU, hyV⟩ := nonempty_preirreducible_inter (U.1.1 : Y.Opens).isOpen
      (V.1.1 : Y.Opens).isOpen U.2 V.2
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨x, ?_, ?_⟩
    · change bcFst ψ q x ∈ (U.1.1 : Y.Opens)
      rw [hx]
      exact hyU
    · change bcFst ψ q x ∈ (V.1.1 : Y.Opens)
      rw [hx]
      exact hyV

end BaseChange

end DeJongAlterations.StableModification.BlowDown.NumericalDescent
