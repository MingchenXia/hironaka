/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Proj.BaseChange
public import Hironaka.Scheme.Smooth.ExceptionalDivisor
public import Hironaka.Scheme.Smooth.ExceptionalModel
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.CoordinateSubspace.ExceptionalProj
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUp.Glue.RestrictOpen
import Hironaka.Scheme.Smooth.BlowUpSmooth
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.ExceptionalBaseChange
import Hironaka.Scheme.Smooth.ExceptionalChart
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.FiniteLength

/-!
# The exceptional divisor is locally `(Z ∩ U) ×_k ℙ^{r-1}_k`

Over a chart `E` of étale coordinates adapted to `Z`, the exceptional divisor `F_U` of `B_{Z∩U} U`
is isomorphic over `Z ∩ U` to `(Z ∩ U) ×_k ℙ^{r-1}_k` (`exists_iso_exceptional_pullback_proj`), and
the fibre of `F → Z` over a point `z` of the center is `ℙ^{r-1}_{κ(z)}` (`exists_iso_fiber_proj`):
the exceptional divisor of a smooth blow-up, smooth by [Kol07, Notation 19], is a projective
bundle over the center (the description of the blow-up of affine space by secant lines,
[Hau14, Definition 4.8]).

**Why it holds.** Three cartesian squares are pasted. (1) The chart square of
`Hironaka/Scheme/Smooth/ExceptionalChart.lean`: `F_U → Z ∩ U` is the base change of the model's
`F_L → L` along `Z ∩ U → L` (`isPullback_exceptionalMapOfIsPullback_subschemeMap`). (2) The model
(`Hironaka/Scheme/BlowUp/CoordinateSubspace/ExceptionalProj.lean`): `F_L ≅ ℙ^{r-1}_L = Proj 𝒪(L)[u]`
compatibly with the structure maps to `L = Spec 𝒪(L)` (`exists_iso_exceptional_proj`, for the
model blow-up; transported to the glued blow-up of `𝔸ⁿ` along `L` through the identification of
the two blow-ups, `comap_π_coordinateSubspace_eq`). (3) The base change of projective space
(`AlgebraicGeometry.Proj.isPullback_projMap`): `ℙ^{r-1}_L = L ×_k ℙ^{r-1}_k`. Pasting (2)–(3) gives
`F_L → L` as the base change of `ℙ^{r-1}_k → Spec k` along `L → Spec k`, and pasting (1) on top
gives `F_U → Z ∩ U` as the base change of `ℙ^{r-1}_k → Spec k` along
`Z ∩ U → L → Spec k = Z ∩ U → U → Spec k` (`toAffineSpace_comp_structure`).

## Main declarations

* `AlgebraicGeometry.exists_iso_exceptional_coordinateSubspace_proj`: `F_L ≅ Proj 𝒪(L)[u]` for the
  glued blow-up of `𝔸ⁿ_k` along `L`, over `L ≅ Spec 𝒪(L)`.
* `AlgebraicGeometry.isPullback_exceptional_coordinateSubspace_proj`: `F_L → L` is the base change
  of `ℙ^{r-1}_k → Spec k`.
* `AlgebraicGeometry.exists_isPullback_exceptional_proj`, `exists_iso_exceptional_pullback_proj`:
  `F_U → Z ∩ U` is the base change of `ℙ^{r-1}_k → Spec k`, and the isomorphism
  `F_U ≅ (Z ∩ U) ×_k ℙ^{r-1}_k` over `Z ∩ U`.
* `AlgebraicGeometry.exists_iso_fiber_proj`: the fibre of `F → Z` over `z` is `ℙ^{r-1}_{κ(z)}`,
  compatibly with the structure morphisms to `Spec κ(z)`. A point `z` of the center lies in some
  chart `U` at a closed point (the Jacobson cover, as for `exceptionalDivisorCover` in
  `ExceptionalDivisor.lean`); the fibre of `F → Z` at `z` is the fibre of `F_U → Z ∩ U` at the
  point `z'` of `Z ∩ U` over `z` (Mathlib's `isPullback_fiberToSpecResidueField_of_isPullback`
  for the square `F_U = F ×_Z (Z ∩ U)`, the residue fields agreeing along the open immersion);
  that fibre is `Spec κ(z) ×_k ℙ^{r-1}_k` by pasting the fibre square onto the chart square, and
  `Spec κ(z) ×_k ℙ^{r-1}_k = ℙ^{r-1}_{κ(z)}` is the base change of projective space along
  `k → κ(z)`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Scheme.IdealSheafData
open TopologicalSpace AlgebraicGeometry Scheme.IdealSheafData Scheme.Hom CoordinateSubspace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

section EqToHom

variable {X : Scheme.{u}}

/-- The closed subscheme of an ideal sheaf is transported along an equality of ideal sheaves; the
`reassoc` attribute gives the composed form. -/
@[reassoc]
theorem eqToHom_subschemeι {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst h
  simp

end EqToHom

section Model

variable (k : Type u) [Field k] (n r : ℕ)

/-- `L = V(t_0, …, t_{r-1}) ≅ Spec (k[t]/(t_0, …, t_{r-1}))` (the inverse of
`specQuotientToSubscheme`). -/
noncomputable def coordinateSubspaceIsoSpec :
    (coordinateSubspace k n r).subscheme ≅
      Spec (.of (MvPolynomial (Fin n) k ⧸ centerIdeal k n r)) :=
  (asIso (specQuotientToSubscheme (centerIdeal k n r))).symm

@[reassoc]
theorem coordinateSubspaceIsoSpec_hom_SpecMap :
    (coordinateSubspaceIsoSpec k n r).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal k n r))) =
      (coordinateSubspace k n r).subschemeι := by
  change inv (specQuotientToSubscheme (centerIdeal k n r)) ≫ _ =
    (specIdealSheaf (centerIdeal k n r)).subschemeι
  exact (IsIso.inv_comp_eq _).mpr (specQuotientToSubscheme_subschemeι _).symm

/-- The exceptional divisor `F_L` of the glued blow-up `B_L 𝔸ⁿ_k` is
`ℙ^{r-1}_L = Proj 𝒪(L)[u_0, …, u_{r-1}]`, compatibly with the structure maps to `L ≅ Spec 𝒪(L)`
(the computation for the model blow-up, transported along the identification of the two
blow-ups). -/
theorem exists_iso_exceptional_coordinateSubspace_proj (hrn : r ≤ n) :
    ∃ e : ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subscheme ≅
        Proj (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) k ⧸ centerIdeal k n r)),
      e.hom ≫ Proj.projToSpec (Fin r) (MvPolynomial (Fin n) k ⧸ centerIdeal k n r) =
        subschemeMap _ (coordinateSubspace k n r) (blowUpπ (coordinateSubspace k n r))
          (le_map_comap _ _) ≫ (coordinateSubspaceIsoSpec k n r).hom := by
  obtain ⟨eB, heB⟩ := exists_iso_blowUp_coordinateSubspace k n r
  obtain ⟨e₇, -, he₇⟩ := exists_iso_exceptional_proj k n r hrn
  have hF := comap_π_coordinateSubspace_eq k n r eB heB
  have : IsIso (subschemeMap ((affineBlowUp.exceptionalIdeal (centerIdeal k n r)).comap eB.hom)
      (affineBlowUp.exceptionalIdeal (centerIdeal k n r)) eB.hom (le_map_comap _ _)) :=
    isIso_subschemeMap_comap_of_isIso eB.hom _
  refine ⟨eqToIso (congrArg Scheme.IdealSheafData.subscheme hF) ≪≫
    asIso (subschemeMap _ _ eB.hom (le_map_comap _ _)) ≪≫ e₇, ?_⟩
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal k n r)))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of _) _
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal k n r)))),
    Category.assoc, Category.assoc, coordinateSubspaceIsoSpec_hom_SpecMap, subschemeMap_subschemeι,
    Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, eqToIso.hom, asIso_hom]
  have h₇ : e₇.hom ≫ Proj.projToSpec (Fin r) (MvPolynomial (Fin n) k ⧸ centerIdeal k n r) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal k n r))) =
      (affineBlowUp.exceptionalIdeal (centerIdeal k n r)).subschemeι ≫
        affineBlowUp.π (centerIdeal k n r) := by
    rw [Proj.projToSpec, Category.assoc, ← he₇, Iso.hom_inv_id_assoc]
  rw [h₇, subschemeMap_subschemeι_assoc, eqToHom_subschemeι_assoc hF, heB]

/-- `F_L → L` is the base change of `ℙ^{r-1}_k → Spec k` along `L → 𝔸ⁿ_k → Spec k`. -/
theorem isPullback_exceptional_coordinateSubspace_proj (hrn : r ≤ n) :
    ∃ q : ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subscheme ⟶
        Proj (homogeneousSubmodule (Fin r) k),
      IsPullback
        (subschemeMap _ (coordinateSubspace k n r) (blowUpπ (coordinateSubspace k n r))
          (le_map_comap _ _)) q
        ((coordinateSubspace k n r).subschemeι ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))))
        (Proj.projToSpec (Fin r) k) := by
  obtain ⟨e, he⟩ := exists_iso_exceptional_coordinateSubspace_proj k n r hrn
  refine ⟨e.hom ≫ Proj.projMap (Fin r) k (MvPolynomial (Fin n) k ⧸ centerIdeal k n r), ?_⟩
  refine (Proj.isPullback_projMap (Fin r) k
    (MvPolynomial (Fin n) k ⧸ centerIdeal k n r)).of_iso' e (coordinateSubspaceIsoSpec k n r)
    (Iso.refl _) (Iso.refl _) he ?_ ?_ ?_
  · simp
  · rw [Iso.refl_hom, Category.comp_id, ← coordinateSubspaceIsoSpec_hom_SpecMap, Category.assoc,
      ← Spec.map_comp]
    rfl
  · simp

end Model

section Chart

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n r : ℕ}
  {Z : X.IdealSheafData} {x : X} (E : EtaleCoordinatesAdapted f n r Z x)

/-- Over a chart `E`, `F_U → Z ∩ U` is the base change of `ℙ^{r-1}_k → Spec k` along the structure
morphism `Z ∩ U → U → Spec k`. -/
theorem exists_isPullback_exceptional_proj (hrn : r ≤ n) :
    ∃ q : ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subscheme ⟶
        Proj (homogeneousSubmodule (Fin r) k),
      IsPullback
        (subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι)) (le_map_comap _ _)) q
        ((Z.comap E.U.1.ι).subschemeι ≫ E.U.1.ι ≫ f) (Proj.projToSpec (Fin r) k) := by
  obtain ⟨φ, H⟩ := exists_isPullback_blowUp E
  obtain ⟨q, hq⟩ := isPullback_exceptional_coordinateSubspace_proj k n r hrn
  refine ⟨exceptionalMapOfIsPullback E H ≫ q, ?_⟩
  have := (isPullback_exceptionalMapOfIsPullback_subschemeMap E H).flip.paste_vert hq
  rwa [← Category.assoc, subschemeMap_subschemeι, Category.assoc, toAffineSpace_comp_structure]
    at this

/-- Over a chart `E` of étale coordinates adapted to `Z`, the exceptional divisor `F_U` of
`B_{Z∩U} U` is isomorphic over `Z ∩ U` to `(Z ∩ U) ×_k ℙ^{r-1}_k` (cf. [Hau14, Definition 4.8],
the blow-up of affine space by secant lines). -/
theorem exists_iso_exceptional_pullback_proj (hrn : r ≤ n) :
    ∃ e : ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subscheme ≅
        pullback ((Z.comap E.U.1.ι).subschemeι ≫ E.U.1.ι ≫ f)
          (Proj.projToSpec (Fin r) k),
      e.hom ≫ pullback.fst _ _ =
        subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι)) (le_map_comap _ _) := by
  obtain ⟨q, hq⟩ := exists_isPullback_exceptional_proj E hrn
  exact ⟨hq.isoPullback, hq.isoPullback_hom_fst⟩

end Chart

section Restrict

variable {X : Scheme.{u}} (Z : X.IdealSheafData) (U : X.Opens)

/-- `B_{Z∩U} U → B_Z X` is the base change of `U → X` (the restriction of a blow-up to an open, as
a cartesian square). -/
theorem isPullback_restrictHom :
    IsPullback (blowUpπ (Z.comap U.ι)) (blowUpMap U.ι Z) U.ι (blowUpπ Z) := by
  have : IsIso (restrictHomToPreimage Z U) := (blowUp.restrictIso Z U).isIso_hom
  have h := IsOpenImmersion.isPullback (blowUpπ (Z.comap U.ι))
    (restrictHomToPreimage Z U ≫ (blowUpπ Z ⁻¹ᵁ U).ι) U.ι (blowUpπ Z)
    (by rw [restrictHomToPreimage_ι]; exact blowUpMap_π U.ι Z)
    (by rw [Scheme.Opens.opensRange_ι, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι])
  rwa [restrictHomToPreimage_ι] at h

/-- The piece `F_U → F` over the piece `Z ∩ U → Z`: the square `F_U → F`, `F_U → Z ∩ U`,
`F → Z`, `Z ∩ U → Z` is cartesian (`F_U = F ×_Z (Z ∩ U)`). -/
theorem isPullback_exceptionalRestrictPiece_subschemeMap :
    IsPullback (exceptionalRestrictPiece Z U)
      (subschemeMap _ (Z.comap U.ι) (blowUpπ (Z.comap U.ι)) (le_map_comap _ _))
      (subschemeMap _ Z (blowUpπ Z) (le_map_comap Z (blowUpπ Z)))
      (subschemeMap (Z.comap U.ι) Z U.ι (le_map_comap Z U.ι)) := by
  have s := isPullback_subschemeMap_of_isPullback (isPullback_restrictHom Z U).flip
    (Z.comap (blowUpπ Z)) ((Z.comap U.ι).comap (blowUpπ (Z.comap U.ι)))
    (comap_restrictHom Z U).symm (le_map_restrictHom Z U)
  rw [← subschemeMap_subschemeι _ (Z.comap U.ι) (blowUpπ (Z.comap U.ι)) (le_map_comap _ _),
    ← subschemeMap_subschemeι _ Z (blowUpπ Z) (le_map_comap Z (blowUpπ Z))] at s
  refine s.of_bot ?_ (isPullback_subschemeMap_comap U.ι Z)
  rw [← cancel_mono Z.subschemeι, Category.assoc, subschemeMap_subschemeι, Category.assoc,
    subschemeMap_subschemeι, subschemeMap_subschemeι_assoc, blowUpMap_π,
    subschemeMap_subschemeι_assoc]

end Restrict

section Fiber

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n r : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
  [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n)

/-- Every point of the center `Z` lies in an adapted chart at a closed point of `V(Z)` (the
Jacobson cover, as for the pieces of `F` in `Hironaka/Scheme/Smooth/ExceptionalDivisor.lean`). -/
theorem exists_adaptedChart_mem (z : Z.subscheme) :
    ∃ x : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support},
      Z.subschemeι z ∈ (adaptedChart f n r Z hrn x).U.1 := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hZ : Z.subschemeι z ∈ Z.support := by
    have h1 : Z.subschemeι z ∈ Set.range Z.subschemeι := ⟨z, rfl⟩
    rwa [range_subschemeι] at h1
  have hcover := iSup_eq_top_of_forall_isClosed Z (fun x => (adaptedChart f n r Z hrn x).U.1)
    (fun x => (adaptedChart f n r Z hrn x).mem)
  have hmem : Z.subschemeι z ∈ (⨆ x, (adaptedChart f n r Z hrn x).U.1) ⊔ Z.support.compl := by
    rw [hcover]
    trivial
  rw [Opens.mem_sup] at hmem
  rcases hmem with hmem | hmem
  · rw [Opens.mem_iSup] at hmem
    exact hmem
  · exact (hmem hZ).elim

omit [PerfectField k] [SmoothOfRelativeDimension n f]
  [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] in
/-- A point of `Z` lying in `U` is the image of a point of `Z ∩ U`. -/
theorem exists_subschemeMap_comap_ι_eq (U : X.Opens) (z : Z.subscheme)
    (hz : Z.subschemeι z ∈ U) :
    ∃ z' : (Z.comap U.ι).subscheme,
      subschemeMap (Z.comap U.ι) Z U.ι (le_map_comap Z U.ι) z' = z := by
  obtain ⟨u, hu⟩ := Scheme.Opens.exists_ι_eq_of_mem hz
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_subschemeMap_comap U.ι Z)
    z u hu.symm
  exact ⟨p, hp⟩

include f n hrn in
/-- For a smooth blow-up over the perfect field `k` and a point `z` of the center, the fibre of
`F → Z` over `z` is `ℙ^{r-1}_{κ(z)} = Proj κ(z)[u_0, …, u_{r-1}]`, compatibly with the structure
morphisms to `Spec κ(z)`. -/
theorem exists_iso_fiber_proj (z : Z.subscheme) :
    ∃ e : (subschemeMap _ Z (blowUpπ Z) (le_map_comap Z (blowUpπ Z))).fiber z ≅
        Proj (homogeneousSubmodule (Fin r) (Z.subscheme.residueField z)),
      e.hom ≫ Proj.projToSpec (Fin r) (Z.subscheme.residueField z) =
        (subschemeMap _ Z (blowUpπ Z) (le_map_comap Z (blowUpπ Z))).fiberToSpecResidueField
          z := by
  obtain ⟨x, hx⟩ := exists_adaptedChart_mem f n r Z hrn z
  obtain ⟨E, hE⟩ : ∃ E : EtaleCoordinatesAdapted f n r Z x.1, Z.subschemeι z ∈ E.U.1 :=
    ⟨adaptedChart f n r Z hrn x, hx⟩
  obtain ⟨z', rfl⟩ := exists_subschemeMap_comap_ι_eq Z E.U.1 z hE
  -- the fibre of `F_U → Z ∩ U` at `z'` is `Spec κ(z') ×_k ℙ^{r-1}_k`
  obtain ⟨q, hq⟩ := exists_isPullback_exceptional_proj E hrn
  have hfib' : IsPullback
      ((subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι))
        (le_map_comap _ _)).fiberι z' ≫ q)
      ((subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι))
        (le_map_comap _ _)).fiberToSpecResidueField z')
      (Proj.projToSpec (Fin r) k)
      ((Z.comap E.U.1.ι).subscheme.fromSpecResidueField z' ≫
        (Z.comap E.U.1.ι).subschemeι ≫ E.U.1.ι ≫ f) :=
    (IsPullback.of_hasPullback _ _).paste_horiz hq.flip
  -- the fibre of `F → Z` at `z` is the fibre of `F_U → Z ∩ U` at `z'`
  obtain ⟨e, hfz⟩ : ∃ e : (subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι))
      (le_map_comap _ _)).fiber z' ≅
        (subschemeMap _ Z (blowUpπ Z) (le_map_comap Z (blowUpπ Z))).fiber
          (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z'),
      IsPullback e.hom
        ((subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι))
          (le_map_comap _ _)).fiberToSpecResidueField z')
        ((subschemeMap _ Z (blowUpπ Z) (le_map_comap Z (blowUpπ Z))).fiberToSpecResidueField
          (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z'))
        (Spec.map ((subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι
          (le_map_comap Z E.U.1.ι)).residueFieldMap z')) := by
    have h := isPullback_fiberToSpecResidueField_of_isPullback
      (isPullback_exceptionalRestrictPiece_subschemeMap Z E.U.1) z'
    have hi : IsIso _ := h.isIso_fst_of_isIso
    exact ⟨@asIso _ _ _ _ _ hi, h⟩
  -- transport to the fibre of `F → Z` over `Spec κ(z)`
  have hfib := hfib'.of_iso e (Iso.refl _)
    (asIso (Spec.map ((subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι
      (le_map_comap Z E.U.1.ι)).residueFieldMap z'))) (Iso.refl _)
    (fst' := e.inv ≫ (subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι))
      (le_map_comap _ _)).fiberι z' ≫ q)
    (snd' := (subschemeMap _ Z (blowUpπ Z) (le_map_comap Z (blowUpπ Z))).fiberToSpecResidueField
      (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z'))
    (f' := Proj.projToSpec (Fin r) k)
    (g' := Z.subscheme.fromSpecResidueField
      (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z') ≫ Z.subschemeι ≫ f)
    (by rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
    (by rw [asIso_hom]; exact hfz.w.symm)
    (by simp)
    (by
      rw [Iso.refl_hom, Category.comp_id, asIso_hom,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
        subschemeMap_subschemeι_assoc])
  -- the base change of projective space along `k → κ(z)`
  let φ := Spec.preimage (Z.subscheme.fromSpecResidueField
    (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z') ≫ Z.subschemeι ≫ f)
  let _ : Algebra k (Z.subscheme.residueField
    (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z')) := φ.hom.toAlgebra
  have hbc := (Proj.isPullback_projMap (Fin r) k (Z.subscheme.residueField
    (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z'))).flip
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k (Z.subscheme.residueField
      (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z')))) =
      Z.subscheme.fromSpecResidueField
        (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι) z') ≫
        Z.subschemeι ≫ f :=
    Spec.map_preimage _
  rw [hφ] at hbc
  exact ⟨hfib.isoIsPullback _ _ hbc, hfib.isoIsPullback_hom_snd _ _ hbc⟩

end Fiber

end AlgebraicGeometry
