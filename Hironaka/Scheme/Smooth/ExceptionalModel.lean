/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Exceptional
public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Exceptional
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The exceptional divisor of the model blow-up is smooth

The model case of the smoothness of the exceptional divisor of a smooth blow-up: the blow-up
`B_L 𝔸ⁿ_A` of `𝔸ⁿ_A = Spec A[x_0, …, x_{n-1}]` along the coordinate subspace
`L = V(x_0, …, x_{r-1})`, with exceptional divisor `F_L = π⁻¹(L)` (the blow-up via the Rees
algebra, [Hau14, Definition 4.7]). Kollár's sentence "if `π_{Z,X}` is a smooth blow-up, then `F` …
[is] smooth" [Kol07, Notation 19] is stated without proof;
`Hironaka/Scheme/Smooth/ExceptionalChart.lean` and `ExceptionalDivisor.lean` reduce it to the model,
and this file proves the model.

**Why the theorems hold.** In the chart `U_j` (`j < r`) the exceptional ideal pulls back along the
chart `U_j ≅ 𝔸ⁿ_A` to the ideal `(x_j)`, so `F_L ∩ U_j = V(x_j) = Spec A[x]/(x_j) ≅ 𝔸^{n-1}_A`,
smooth over `A` of relative dimension `n − 1` (`smoothOfRelativeDimension_quotient_span_X`); and
through the chart map `π_j` (`x_i ↦ x_i x_j` for `i < r`, `i ≠ j`) the ring `A[x]/(x_j)` is the
polynomial ring over `𝒪(L) = A[x]/I` in the `r − 1` variables `x_i`, `i < r`, `i ≠ j`
(`fibreAlgEquivOverCenter`), so `V(x_j) → L` is smooth of relative dimension `r − 1` (cf. [Hau14,
Example 5.9]). The charts `U_j`, `j < r`, cover `B_L 𝔸ⁿ`, hence the pieces
`F_L ∩ U_j` cover `F_L`, and both smoothness statements are Zariski-local on the source. Two
bookkeeping identifications make this a proof about the glued blow-up: the closed subscheme of
the ideal sheaf of an ideal `J` on `Spec S` is `Spec (S/J)` (`specQuotientToSubscheme`, an
isomorphism because both are closed immersions with the same kernel), and the glued blow-up
`blowUp (coordinateSubspace k n r)` is identified with the affine model over `𝔸ⁿ` by the
uniqueness of blow-ups (`exists_iso_blowUp_coordinateSubspace`), which carries the exceptional
divisors and the maps to `L` along (`prop_subschemeι_comp_iff_of_eq_comap`,
`prop_subschemeMap_iff_of_eq_comap`).

## Main declarations

* `AlgebraicGeometry.specQuotientToSubscheme`: `Spec (R/I) ≅ V(I)` over `Spec R`, and the transport
  lemmas `prop_subschemeι_comp_iff_of_eq_specIdealSheaf`,
  `prop_subschemeMap_iff_of_eq_specIdealSheaf` (a morphism property of `V(J) → Y`, or of the
  induced `V(J) → V(I)`, read on `Spec (S/J) → Y`, or on `Spec (S/J) → Spec (R/I)`).
* `AlgebraicGeometry.isIso_subschemeMap_comap_of_isIso`, `prop_subschemeι_comp_iff_of_eq_comap`,
  `prop_subschemeMap_iff_of_eq_comap`: the same along an isomorphism of ambient schemes.
* `AlgebraicGeometry.CoordinateSubspace.exceptionalCover`: the open cover of `F_L` by the pieces
  `F_L ∩ U_j`, `j < r`.
* `AlgebraicGeometry.CoordinateSubspace.smoothOfRelativeDimension_exceptionalIdeal_modelBlowUp`:
  `F_L → Spec A` is smooth of relative dimension `n − 1`.
* `smoothOfRelativeDimension_subschemeMap_exceptionalIdeal_modelBlowUp` (same namespace):
  `F_L → L` is smooth of relative dimension `r − 1`.
* `AlgebraicGeometry.smoothOfRelativeDimension_exceptional_coordinateSubspace`,
  `AlgebraicGeometry.smoothOfRelativeDimension_subschemeMap_exceptional_coordinateSubspace`: the
  two statements for the glued `blowUp (coordinateSubspace k n r)`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData MvPolynomial

namespace AlgebraicGeometry

section SpecQuotient

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The closed immersion `Spec (R/I) → Spec R` factored through the closed subscheme `V(I)` of the
ideal sheaf `specIdealSheaf I` of `I`: an isomorphism, both being closed immersions with kernel
the ideal sheaf of `I`. -/
noncomputable def specQuotientToSubscheme : Spec (.of (R ⧸ I)) ⟶ (specIdealSheaf I).subscheme :=
  IsClosedImmersion.lift (specIdealSheaf I).subschemeι
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_Spec_map_mk (R :=
        .of R)])

@[reassoc (attr := simp)]
theorem specQuotientToSubscheme_subschemeι :
    specQuotientToSubscheme I ≫ (specIdealSheaf I).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  IsClosedImmersion.lift_fac _ _ _

instance isIso_specQuotientToSubscheme : IsIso (specQuotientToSubscheme I) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of R) I
  exact IsClosedImmersion.isIso_lift (specIdealSheaf I).subschemeι
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_Spec_map_mk (R :=
        .of R)])

/-- The exceptional ideal of the affine blow-up contains the pullback of the center's ideal sheaf:
`I·𝒪_B` is the inverse image of `I`, so `I ≤ π_*(I·𝒪_B)` (Mathlib's `le_map_comap`, stated with
the exceptional ideal's name so that `subschemeMap` terms carry a syntactically matching proof). -/
theorem affineBlowUp.le_map_exceptionalIdeal :
    specIdealSheaf I ≤ (affineBlowUp.exceptionalIdeal I).map (affineBlowUp.π I) :=
  Scheme.IdealSheafData.le_map_comap _ _

/-- A morphism property of `V(J) → Y`, for `J` the ideal sheaf of an ideal `I` on `Spec R`, is read
on `Spec (R/I) → Y`. -/
theorem prop_subschemeι_comp_iff_of_eq_specIdealSheaf (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {Y : Scheme.{u}} (K : (Spec (.of R)).IdealSheafData)
    (hK : K = specIdealSheaf I) (q : Spec (.of R) ⟶ Y) :
    P (K.subschemeι ≫ q) ↔ P (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ q) := by
  subst hK
  rw [← specQuotientToSubscheme_subschemeι, Category.assoc,
    P.cancel_left_of_respectsIso (specQuotientToSubscheme I)]

/-- A morphism property of the map of closed subschemes `V(J) → V(I)` induced by
`Spec φ : Spec S → Spec R` (`φ : R → S` carrying `I` into `J`) is read on
`Spec (R/I → S/J)`. -/
theorem prop_subschemeMap_iff_of_eq_specIdealSheaf (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {S : Type u} [CommRing S] (J : Ideal S) (φ : R →+* S) (hφ : I ≤ J.comap φ)
    (K : (Spec (.of S)).IdealSheafData) (hK : K = specIdealSheaf J)
    {g : Spec (.of S) ⟶ Spec (.of R)} (hg : g = Spec.map (CommRingCat.ofHom φ))
    (H : specIdealSheaf I ≤ K.map g) :
    P (Scheme.IdealSheafData.subschemeMap K (specIdealSheaf I) g H) ↔
      P (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J φ hφ))) := by
  subst hK hg
  have h : specQuotientToSubscheme J ≫
        Scheme.IdealSheafData.subschemeMap (specIdealSheaf J) (specIdealSheaf I) (Spec.map
            (CommRingCat.ofHom φ)) H =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap J φ hφ)) ≫ specQuotientToSubscheme I := by
    rw [← cancel_mono (specIdealSheaf I).subschemeι, Category.assoc,
        Scheme.IdealSheafData.subschemeMap_subschemeι,
      specQuotientToSubscheme_subschemeι_assoc, Category.assoc,
      specQuotientToSubscheme_subschemeι, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  rw [← P.cancel_left_of_respectsIso (specQuotientToSubscheme J), h,
    P.cancel_right_of_respectsIso]

end SpecQuotient

section Transport

variable {B B' : Scheme.{u}} (e : B ⟶ B') [IsIso e] (J : B'.IdealSheafData)

/-- The closed subscheme of the inverse image of `J` along an isomorphism maps isomorphically onto
`V(J)` (Mathlib's `isPullback_of_isClosedImmersion`). -/
theorem isIso_subschemeMap_comap_of_isIso :
    IsIso (Scheme.IdealSheafData.subschemeMap (J.comap e) J e
        (Scheme.IdealSheafData.le_map_comap J e)) := by
  have sq : IsPullback (J.comap e).subschemeι (Scheme.IdealSheafData.subschemeMap (J.comap e) J e
      (Scheme.IdealSheafData.le_map_comap J e)) e
      J.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _
        _).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])
  exact sq.isIso_snd_of_isIso

/-- A morphism property of `V(K) → Y` transports along an isomorphism `e : B ≅ B'` carrying `K`
to `J` (`K = J.comap e`). -/
theorem prop_subschemeι_comp_iff_of_eq_comap (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Y : Scheme.{u}} (K : B.IdealSheafData) (hK : K = J.comap e) {q : B' ⟶ Y} {q' : B ⟶ Y}
    (hq : q' = e ≫ q) : P (K.subschemeι ≫ q') ↔ P (J.subschemeι ≫ q) := by
  subst hK hq
  have := isIso_subschemeMap_comap_of_isIso e J
  rw [← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι (J.comap e) J e
      (Scheme.IdealSheafData.le_map_comap J e),
    Category.assoc, P.cancel_left_of_respectsIso]

/-- A morphism property of the induced map `V(K) → V(L)` transports along an isomorphism
`e : B ≅ B'` carrying `K` to `J`. -/
theorem prop_subschemeMap_iff_of_eq_comap (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Y : Scheme.{u}} (K : B.IdealSheafData) (hK : K = J.comap e) {q : B' ⟶ Y} {q' : B ⟶ Y}
    (hq : q' = e ≫ q) (L : Y.IdealSheafData) (H1 : L ≤ K.map q') (H2 : L ≤ J.map q) :
    P (Scheme.IdealSheafData.subschemeMap K L q' H1) ↔ P (Scheme.IdealSheafData.subschemeMap J L q
        H2) := by
  subst hK hq
  have := isIso_subschemeMap_comap_of_isIso e J
  have h : Scheme.IdealSheafData.subschemeMap (J.comap e) L (e ≫ q) H1 =
      Scheme.IdealSheafData.subschemeMap (J.comap e) J e (Scheme.IdealSheafData.le_map_comap J e) ≫
          Scheme.IdealSheafData.subschemeMap J L q H2 := by
    rw [← cancel_mono L.subschemeι, Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Scheme.IdealSheafData.subschemeMap_subschemeι,
          Scheme.IdealSheafData.subschemeMap_subschemeι_assoc]
  rw [h, P.cancel_left_of_respectsIso]

end Transport

namespace CoordinateSubspace

open affineBlowUpAlgebra

variable (A : Type u) [CommRing A] (n r : ℕ)

/-- The piece `F_L ∩ U_j` of the model's exceptional divisor over the chart `U_j`, as the closed
subscheme of the inverse image ideal, mapping into `F_L` (an open immersion). -/
noncomputable def exceptionalChartPiece (j : Fin n) (hj : j.val < r) :
    ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).comap (modelChart A n r j hj)).subscheme ⟶
      (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (modelChart A n r j hj)
      (Scheme.IdealSheafData.le_map_comap _ _)

instance isOpenImmersion_exceptionalChartPiece (j : Fin n) (hj : j.val < r) :
    IsOpenImmersion (exceptionalChartPiece A n r j hj) :=
  Scheme.IdealSheafData.isOpenImmersion_subschemeMap_of_comap _ _ _ rfl _

@[reassoc (attr := simp)]
theorem exceptionalChartPiece_subschemeι (j : Fin n) (hj : j.val < r) :
    exceptionalChartPiece A n r j hj ≫
        (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι =
      ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).comap
        (modelChart A n r j hj)).subschemeι ≫ modelChart A n r j hj :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The pieces `F_L ∩ U_j`, `j < r`, cover `F_L` (the charts cover `B_L 𝔸ⁿ`,
`iSup_opensRange_modelChart`). -/
theorem exists_exceptionalChartPiece_eq
    (y : (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subscheme) :
    ∃ (j : {j : Fin n // j.val < r})
      (p : ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).comap
        (modelChart A n r j.1 j.2)).subscheme),
      exceptionalChartPiece A n r j.1 j.2 p = y := by
  have hy : (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι y ∈
      (⊤ : (modelBlowUp A n r).Opens) := trivial
  rw [← iSup_opensRange_modelChart A n r] at hy
  simp only [TopologicalSpace.Opens.mem_iSup] at hy
  obtain ⟨j, hj, hy⟩ := hy
  obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hy
  have sq : IsPullback ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).comap
      (modelChart A n r j hj)).subschemeι (exceptionalChartPiece A n r j hj)
      (modelChart A n r j hj) (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (exceptionalChartPiece_subschemeι A n r j hj).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])
  obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback sq u y hu
  exact ⟨⟨j, hj⟩, p, hp⟩

/-- The open cover of the model's exceptional divisor `F_L` by its chart pieces `F_L ∩ U_j`,
`j < r`. -/
noncomputable def exceptionalCover :
    (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subscheme.OpenCover :=
  Scheme.Cover.mkOfCovers {j : Fin n // j.val < r}
    (fun j => ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).comap
      (modelChart A n r j.1 j.2)).subscheme)
    (fun j => exceptionalChartPiece A n r j.1 j.2) (exists_exceptionalChartPiece_eq A n r)

/-- Over `Spec A` the chart `U_j` is `Spec A[x] → Spec A` (the chart map is an `A`-algebra map). -/
theorem modelChart_π_comp_structure (j : Fin n) (hj : j.val < r) :
    modelChart A n r j hj ≫ affineBlowUp.π (centerIdeal A n r) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) := by
  rw [← Category.assoc, modelChart_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]

/-- On the chart `U_j`: the piece `F_L ∩ U_j = Spec A[x]/(x_j) ≅ 𝔸^{n-1}_A` is smooth over `A` of
relative dimension `n − 1`. -/
theorem smoothOfRelativeDimension_exceptionalChartPiece_comp (j : Fin n) (hj : j.val < r) :
    SmoothOfRelativeDimension (n - 1)
      (exceptionalChartPiece A n r j hj ≫
        (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι ≫
          affineBlowUp.π (centerIdeal A n r) ≫
            Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (n - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} (n - 1)) := hloc.toRespects
  rw [exceptionalChartPiece_subschemeι_assoc, modelChart_π_comp_structure,
    prop_subschemeι_comp_iff_of_eq_specIdealSheaf (I := Ideal.span {(X j : MvPolynomial (Fin n) A)})
      (P := @SmoothOfRelativeDimension.{u} (n - 1)) _
      (comap_exceptionalIdeal_modelChart A n r j hj), ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact smoothOfRelativeDimension_quotient_span_X A j

/-- The exceptional divisor `F_L` of `B_L 𝔸ⁿ_A` is smooth over `A` of relative dimension `n − 1`
(the model case of [Kol07, Notation 19]): on the piece `F_L ∩ U_j = Spec A[x]/(x_j) ≅ 𝔸^{n-1}_A`
by the chart computation, and smoothness is Zariski-local on the source. -/
theorem smoothOfRelativeDimension_exceptionalIdeal_modelBlowUp :
    SmoothOfRelativeDimension (n - 1)
      ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι ≫
        affineBlowUp.π (centerIdeal A n r) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (n - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} (n - 1))
    (exceptionalCover A n r) fun j =>
      smoothOfRelativeDimension_exceptionalChartPiece_comp A n r j.1 j.2

/-- `{i < r, i ≠ j}` has `r − 1` elements when `j < r ≤ n`. -/
theorem card_lt_ne (j : Fin n) (hj : j.val < r) (hrn : r ≤ n) :
    Nat.card {i : Fin n // i.val < r ∧ i ≠ j} = r - 1 := by
  have h1 : Nat.card {i : Fin n // i.val < r} = r :=
    Nat.card_congr
      { toFun := fun i => (⟨i.1.1, i.2⟩ : Fin r)
        invFun := fun i => ⟨⟨i.1, lt_of_lt_of_le i.2 hrn⟩, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } |>.trans (Nat.card_eq_fintype_card.trans (Fintype.card_fin r))
  have h2 : (Finset.univ.filter fun i : Fin n => i.val < r ∧ i ≠ j) =
      (Finset.univ.filter fun i : Fin n => i.val < r).erase j := by
    ext i
    simp [Finset.mem_erase, and_comm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, h2,
    Finset.card_erase_of_mem (by simpa using hj), ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card, h1]

/-- In the chart `U_j`: `V(x_j) → L`, `Spec` of the map `A[x]/I → A[x]/(x_j)` induced by the chart
map, is smooth of relative dimension `r − 1`, `A[x]/(x_j)` being the polynomial ring over `𝒪(L)`
in the `r − 1` variables `x_i`, `i < r`, `i ≠ j` (cf. [Hau14, Example 5.9]). -/
theorem smoothOfRelativeDimension_Spec_map_quotientMap_chartSubst (j : Fin n) (hj : j.val < r)
    (hrn : r ≤ n) :
    SmoothOfRelativeDimension (r - 1) (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.span {(X j : MvPolynomial (Fin n) A)})
        (chartSubst A (center n r) j).toRingHom (centerIdeal_le_comap_chartSubst A n r j)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} (r - 1)),
    CommRingCat.hom_ofHom]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  let _ : Algebra (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)
      (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)}) :=
    (Ideal.quotientMap (Ideal.span {(X j : MvPolynomial (Fin n) A)})
      (chartSubst A (center n r) j).toRingHom (centerIdeal_le_comap_chartSubst A n r j)).toAlgebra
  have h := ringHom_isStandardSmoothOfRelativeDimension_algebraMap_mvPolynomial
    (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) {i : Fin n // i.val < r ∧ i ≠ j}
  rw [card_lt_ne n r j hj hrn] at h
  have := isStandardSmoothOfRelativeDimension_algebraMap_of_algEquiv
    (fibreAlgEquivOverCenter A n r j hj).symm h
  rwa [RingHom.algebraMap_toAlgebra] at this

/-- On the chart `U_j`: the piece `F_L ∩ U_j → L` of `F_L → L` is `Spec (A[x]/I → A[x]/(x_j))`,
smooth of relative dimension `r − 1`. -/
theorem smoothOfRelativeDimension_exceptionalChartPiece_comp_subschemeMap (j : Fin n)
    (hj : j.val < r) (hrn : r ≤ n) :
    SmoothOfRelativeDimension (r - 1)
      (exceptionalChartPiece A n r j hj ≫
        Scheme.IdealSheafData.subschemeMap (affineBlowUp.exceptionalIdeal (centerIdeal A n r))
          (specIdealSheaf (centerIdeal A n r)) (affineBlowUp.π (centerIdeal A n r))
          (affineBlowUp.le_map_exceptionalIdeal (centerIdeal A n r))) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (r - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} (r - 1)) := hloc.toRespects
  have hle : specIdealSheaf (centerIdeal A n r) ≤
      ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).comap (modelChart A n r j hj)).map
        (modelChart A n r j hj ≫ affineBlowUp.π (centerIdeal A n r)) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (Scheme.IdealSheafData.comap_comp (specIdealSheaf (centerIdeal A n r)) (modelChart A n r j hj)
        (affineBlowUp.π (centerIdeal A n r))).le
  have h : exceptionalChartPiece A n r j hj ≫
        Scheme.IdealSheafData.subschemeMap (affineBlowUp.exceptionalIdeal (centerIdeal A n r))
          (specIdealSheaf (centerIdeal A n r)) (affineBlowUp.π (centerIdeal A n r))
          (affineBlowUp.le_map_exceptionalIdeal (centerIdeal A n r)) =
      Scheme.IdealSheafData.subschemeMap _ (specIdealSheaf (centerIdeal A n r))
        (modelChart A n r j hj ≫ affineBlowUp.π (centerIdeal A n r)) hle := by
    rw [← cancel_mono (specIdealSheaf (centerIdeal A n r)).subschemeι, Category.assoc,
      Scheme.IdealSheafData.subschemeMap_subschemeι, Scheme.IdealSheafData.subschemeMap_subschemeι,
          exceptionalChartPiece_subschemeι_assoc]
  rw [h, prop_subschemeMap_iff_of_eq_specIdealSheaf (I := centerIdeal A n r)
    (P := @SmoothOfRelativeDimension.{u} (r - 1)) (Ideal.span {(X j : MvPolynomial (Fin n) A)})
    (chartSubst A (center n r) j).toRingHom (centerIdeal_le_comap_chartSubst A n r j) _
    (comap_exceptionalIdeal_modelChart A n r j hj) (modelChart_π A n r j hj)]
  exact smoothOfRelativeDimension_Spec_map_quotientMap_chartSubst A n r j hj hrn

/-- `F_L → L` is smooth of relative dimension `r − 1`: on the piece `F_L ∩ U_j` it is
`Spec (A[x]/I → A[x]/(x_j))`, and smoothness is Zariski-local on the source. -/
theorem smoothOfRelativeDimension_subschemeMap_exceptionalIdeal_modelBlowUp (hrn : r ≤ n) :
    SmoothOfRelativeDimension (r - 1)
      (Scheme.IdealSheafData.subschemeMap (affineBlowUp.exceptionalIdeal (centerIdeal A n r))
        (specIdealSheaf (centerIdeal A n r)) (affineBlowUp.π (centerIdeal A n r))
        (affineBlowUp.le_map_exceptionalIdeal (centerIdeal A n r))) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (r - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} (r - 1))
    (exceptionalCover A n r) fun j =>
      smoothOfRelativeDimension_exceptionalChartPiece_comp_subschemeMap A n r j.1 j.2 hrn

end CoordinateSubspace

end AlgebraicGeometry

namespace AlgebraicGeometry

open AlgebraicGeometry Scheme.IdealSheafData CoordinateSubspace

variable (k : Type u) [Field k] (n r : ℕ)

/-- Under the identification `e` of the glued `blowUp (coordinateSubspace k n r)` with the model
(`exists_iso_blowUp_coordinateSubspace`), the exceptional divisor `F_L` of the glued blow-up is the
inverse image of the model's exceptional ideal. -/
theorem comap_π_coordinateSubspace_eq (e : blowUp (coordinateSubspace k n r) ≅ modelBlowUp k n r)
    (he : e.hom ≫ affineBlowUp.π (centerIdeal k n r) = blowUpπ (coordinateSubspace k n r)) :
    (coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r)) =
      (affineBlowUp.exceptionalIdeal (centerIdeal k n r)).comap e.hom := by
  have h1 : (coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r)) =
      (coordinateSubspace k n r).comap (e.hom ≫ affineBlowUp.π (centerIdeal k n r)) :=
    congrArg _ he.symm
  exact h1.trans
    (comap_comp (coordinateSubspace k n r) e.hom (affineBlowUp.π (centerIdeal k n r)))

/-- The exceptional divisor of the glued `blowUp (coordinateSubspace k n r)` is smooth over `k` of
relative dimension `n − 1`. -/
theorem smoothOfRelativeDimension_exceptional_coordinateSubspace :
    SmoothOfRelativeDimension (n - 1)
      (((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subschemeι ≫
        blowUpπ (coordinateSubspace k n r) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) := by
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace k n r
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (n - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} (n - 1)) := hloc.toRespects
  rw [prop_subschemeι_comp_iff_of_eq_comap (e := e.hom)
    (J := affineBlowUp.exceptionalIdeal (centerIdeal k n r))
    (P := @SmoothOfRelativeDimension.{u} (n - 1)) _ (comap_π_coordinateSubspace_eq k n r e he)
    (q := affineBlowUp.π (centerIdeal k n r) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))))
    (by rw [← he, Category.assoc])]
  exact smoothOfRelativeDimension_exceptionalIdeal_modelBlowUp k n r

/-- `F_L → L` is smooth of relative dimension `r − 1` for the glued
`blowUp (coordinateSubspace k n r)`. -/
theorem smoothOfRelativeDimension_subschemeMap_exceptional_coordinateSubspace (hrn : r ≤ n) :
    SmoothOfRelativeDimension (r - 1)
      (subschemeMap ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r)))
        (coordinateSubspace k n r) (blowUpπ (coordinateSubspace k n r)) (le_map_comap _ _)) := by
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace k n r
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (r - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} (r - 1)) := hloc.toRespects
  rw [prop_subschemeMap_iff_of_eq_comap (e := e.hom)
    (J := affineBlowUp.exceptionalIdeal (centerIdeal k n r))
    (P := @SmoothOfRelativeDimension.{u} (r - 1)) _ (comap_π_coordinateSubspace_eq k n r e he)
    (q := affineBlowUp.π (centerIdeal k n r)) he.symm (coordinateSubspace k n r) _
    (affineBlowUp.le_map_exceptionalIdeal (centerIdeal k n r))]
  exact smoothOfRelativeDimension_subschemeMap_exceptionalIdeal_modelBlowUp k n r hrn

end AlgebraicGeometry
