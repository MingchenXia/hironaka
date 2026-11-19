/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.ExceptionalModel
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The exceptional divisor over a chart of adapted coordinates

`f : X ⟶ Spec k`, `Z` an ideal sheaf on `X`, and a chart `E : EtaleCoordinatesAdapted f n r Z x`:
an affine open `U ∋ x` with étale `g = toAffineSpace f U v : U ⟶ 𝔸ⁿ_k` and `Z ∩ U = g⁻¹(L)`,
`L = coordinateSubspace k n r`. The chart computation of
`Hironaka/Scheme/Smooth/BlowUpSmoothChart.lean` gives a cartesian square `IsPullback φ π_U π_L g`,
`B_{Z∩U} U ≅ U ×_{𝔸ⁿ} B_L 𝔸ⁿ`. This file does the same for the exceptional divisors: `F_U ≅ U ×_{𝔸ⁿ}
F_L`, and consequently `F_U` is smooth of relative dimension `n − 1` over `k` and `F_U → Z ∩ U` is
smooth of relative dimension `r − 1`, the chart form of "if `π_{Z,X}` is a smooth blow-up, then `F`
… [is] smooth" [Kol07, Notation 19].

**Why the theorems hold.** The exceptional ideal of `B_{Z∩U} U` is
`(Z ∩ U)·𝒪 = (g⁻¹L)·𝒪 = (π_U ≫ g)⁻¹L = (φ ≫ π_L)⁻¹L = φ⁻¹(F_L)`: inverse images of ideal
sheaves compose (`IdealSheafData.comap_comp`) and the square commutes
(`comap_π_eq_comap_of_isPullback`). The closed subschemes of an ideal sheaf and of its inverse
image form a cartesian square over the morphism (Mathlib's `isPullback_of_isClosedImmersion`),
and pasting it on top of the square of `BlowUpSmoothChart.lean` gives `F_U ≅ U ×_{𝔸ⁿ} F_L`
(`exists_isPullback_exceptional`). The projection `ψ : F_U → F_L` is then a base change of the
étale `g`, hence étale; so `F_U → Spec k = ψ ≫ (F_L → Spec k)` is smooth of relative dimension
`0 + (n − 1)` by the model (`smoothOfRelativeDimension_exceptional_comap`). Cancelling the bottom
square `Z ∩ U = U ×_{𝔸ⁿ} L` (adaptedness) from the big square shows `F_U → Z ∩ U` is the base
change of `F_L → L` along `Z ∩ U → L`, hence smooth of relative dimension `r − 1`
(`smoothOfRelativeDimension_subschemeMap_exceptional_comap`); composing with the open immersion
`Z ∩ U → Z` keeps the relative dimension.

## Main declarations

* `AlgebraicGeometry.isPullback_subschemeMap_of_isPullback`: closed subschemes of an ideal sheaf
  and its inverse image, pasted onto a cartesian square.
* `AlgebraicGeometry.subschemeMap_comp_subschemeMap`: composition of induced maps of subschemes.
* `AlgebraicGeometry.comap_π_eq_comap_of_isPullback` (the ideal), `exists_isPullback_exceptional`
  (the schemes), `etale_exceptionalMapOfIsPullback` (the projection `F_U → F_L` is étale).
* `AlgebraicGeometry.smoothOfRelativeDimension_exceptional_comap`: `F_U → Spec k` is smooth of
  relative dimension `n − 1`.
* `AlgebraicGeometry.smoothOfRelativeDimension_subschemeMap_exceptional_comap`,
  `smoothOfRelativeDimension_subschemeMap_exceptional_comap_comp`: `F_U → Z ∩ U` and `F_U → Z`
  are smooth of relative dimension `r − 1`.

`Hironaka/Scheme/Smooth/ExceptionalDivisor.lean` glues these chart statements over the Jacobson
cover.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

namespace AlgebraicGeometry

section Pasting

variable {P X Y S : Scheme.{u}}

/-- Pasting of closed subschemes: for a cartesian square `IsPullback φ p q g` and an ideal sheaf
`J` on `X` with inverse image `K = J.comap φ` on `P`, the closed subschemes `V(K) → Y`, `V(J) → S`
form a cartesian square over `g` (Mathlib's `isPullback_of_isClosedImmersion` pasted on top). -/
theorem isPullback_subschemeMap_of_isPullback {φ : P ⟶ X} {p : P ⟶ Y} {q : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback φ p q g) (J : X.IdealSheafData) (K : P.IdealSheafData) (hK : K = J.comap φ)
    (h : J ≤ K.map φ) :
    IsPullback (Scheme.IdealSheafData.subschemeMap K J φ h) (K.subschemeι ≫ p)
        (J.subschemeι ≫ q) g := by
  have top : IsPullback K.subschemeι (Scheme.IdealSheafData.subschemeMap K J φ h) φ J.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι K J φ
        h).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hK])
  exact top.flip.paste_vert H

/-- Composition of the induced maps of closed subschemes. -/
theorem subschemeMap_comp_subschemeMap {K : P.IdealSheafData} {J : X.IdealSheafData}
    {L : S.IdealSheafData} (ρ : P ⟶ X) (q : X ⟶ S) (h1 : J ≤ K.map ρ) (h2 : L ≤ J.map q)
    (h3 : L ≤ K.map (ρ ≫ q)) :
    Scheme.IdealSheafData.subschemeMap K J ρ h1 ≫ Scheme.IdealSheafData.subschemeMap J L q h2 =
        Scheme.IdealSheafData.subschemeMap K L (ρ ≫ q) h3 := by
  rw [← cancel_mono L.subschemeι, Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
    Scheme.IdealSheafData.subschemeMap_subschemeι_assoc,
        Scheme.IdealSheafData.subschemeMap_subschemeι]

end Pasting

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.IdealSheafData AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n r : ℕ}
  {Z : X.IdealSheafData} {x : X} (E : EtaleCoordinatesAdapted f n r Z x)
  {φ : blowUp (Z.comap E.U.1.ι) ⟶ blowUp (coordinateSubspace k n r)}
  (H : IsPullback φ (blowUpπ (Z.comap E.U.1.ι)) (blowUpπ (coordinateSubspace k n r))
    (toAffineSpace f E.U.1 E.v))

include H in
/-- In a cartesian square `IsPullback φ π_U π_L g` as in `exists_isPullback_blowUp`, the
exceptional ideal of `B_{Z∩U} U` is the inverse image along `φ` of the model's exceptional ideal:
`Z ∩ U = g⁻¹(L)` and `π_U ≫ g = φ ≫ π_L`. -/
theorem comap_π_eq_comap_of_isPullback :
    (Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι)) =
      ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).comap φ := by
  have h1 : (Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι)) =
      ((coordinateSubspace k n r).comap (toAffineSpace f E.U.1 E.v)).comap
        (blowUpπ (Z.comap E.U.1.ι)) :=
    congrArg (fun J : E.U.1.toScheme.IdealSheafData => J.comap (blowUpπ (Z.comap E.U.1.ι)))
      E.adapted
  have h2 := (comap_comp (coordinateSubspace k n r) (blowUpπ (Z.comap E.U.1.ι))
    (toAffineSpace f E.U.1 E.v)).symm
  have h3 : (coordinateSubspace k n r).comap
        (blowUpπ (Z.comap E.U.1.ι) ≫ toAffineSpace f E.U.1 E.v) =
      (coordinateSubspace k n r).comap (φ ≫ blowUpπ (coordinateSubspace k n r)) :=
    congrArg (fun m => (coordinateSubspace k n r).comap m) H.w.symm
  have h4 := comap_comp (coordinateSubspace k n r) φ (blowUpπ (coordinateSubspace k n r))
  exact h1.trans (h2.trans (h3.trans h4))

include H in
/-- The model's exceptional ideal pushes forward along `φ` to contain the chart's. -/
theorem le_map_exceptional_of_isPullback :
    (coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r)) ≤
      ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).map φ :=
  le_map_iff_comap_le.mpr (comap_π_eq_comap_of_isPullback E H).ge

/-- The projection `ψ : F_U → F_L` of the exceptional divisors, the restriction of `φ`. -/
noncomputable def exceptionalMapOfIsPullback :
    ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subscheme ⟶
      ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subscheme :=
  subschemeMap _ _ φ (le_map_exceptional_of_isPullback E H)

@[reassoc (attr := simp)]
theorem exceptionalMapOfIsPullback_subschemeι :
    exceptionalMapOfIsPullback E H ≫
        ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subschemeι =
      ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subschemeι ≫ φ :=
  subschemeMap_subschemeι _ _ _ _

/-- `F_U ≅ U ×_{𝔸ⁿ} F_L`: the square of the exceptional divisors over `g`, pasted onto the
cartesian square of the blow-ups, is cartesian. -/
theorem isPullback_exceptionalMapOfIsPullback :
    IsPullback (exceptionalMapOfIsPullback E H)
      (((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subschemeι ≫
        blowUpπ (Z.comap E.U.1.ι))
      (((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subschemeι ≫
        blowUpπ (coordinateSubspace k n r))
      (toAffineSpace f E.U.1 E.v) :=
  isPullback_subschemeMap_of_isPullback H _ _ (comap_π_eq_comap_of_isPullback E H) _

include H in
/-- `F_U ≅ U ×_{𝔸ⁿ} F_L`, in existential form: a map `ψ : F_U → F_L` over `φ` making the square of
the exceptional divisors over `g` cartesian. -/
theorem exists_isPullback_exceptional :
    ∃ ψ : ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subscheme ⟶
        ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subscheme,
      ψ ≫ ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subschemeι =
          ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subschemeι ≫ φ ∧
      IsPullback ψ
        (((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subschemeι ≫
          blowUpπ (Z.comap E.U.1.ι))
        (((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subschemeι ≫
          blowUpπ (coordinateSubspace k n r))
        (toAffineSpace f E.U.1 E.v) :=
  ⟨exceptionalMapOfIsPullback E H, exceptionalMapOfIsPullback_subschemeι E H,
    isPullback_exceptionalMapOfIsPullback E H⟩

/-- The projection `ψ : F_U → F_L` is étale, being a base change of the étale `g` (as
`etale_of_isPullback_blowUp`). -/
theorem etale_exceptionalMapOfIsPullback : Etale (exceptionalMapOfIsPullback E H) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
    (isPullback_exceptionalMapOfIsPullback E H).flip E.etale

include H in
/-- `F_U → Spec k` is smooth of relative dimension `n − 1`, the composite of the étale `ψ` with the
model's `F_L → 𝔸ⁿ → Spec k` (the smoothness of the exceptional divisor of [Kol07, Notation 19],
over a chart). -/
theorem smoothOfRelativeDimension_exceptional_comap :
    SmoothOfRelativeDimension (n - 1)
      (((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subschemeι ≫
        blowUpπ (Z.comap E.U.1.ι) ≫ E.U.1.ι ≫ f) := by
  have hψ : Etale (exceptionalMapOfIsPullback E H) := etale_exceptionalMapOfIsPullback E H
  have hL := smoothOfRelativeDimension_exceptional_coordinateSubspace k n r
  have heq : ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).subschemeι ≫
        blowUpπ (Z.comap E.U.1.ι) ≫ E.U.1.ι ≫ f =
      exceptionalMapOfIsPullback E H ≫
        ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subschemeι ≫
          blowUpπ (coordinateSubspace k n r) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) := by
    rw [← toAffineSpace_comp_structure f E.U.1 E.v, exceptionalMapOfIsPullback_subschemeι_assoc,
      ← Category.assoc φ, H.w, Category.assoc]
  rw [heq]
  have : SmoothOfRelativeDimension (0 + (n - 1)) (exceptionalMapOfIsPullback E H ≫
      ((coordinateSubspace k n r).comap (blowUpπ (coordinateSubspace k n r))).subschemeι ≫
        blowUpπ (coordinateSubspace k n r) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) := inferInstance
  rwa [zero_add] at this

/-- Adaptedness as a pushforward inequality: `L ≤ g_*(Z ∩ U)`. -/
theorem coordinateSubspace_le_map_toAffineSpace :
    coordinateSubspace k n r ≤ (Z.comap E.U.1.ι).map (toAffineSpace f E.U.1 E.v) :=
  le_map_iff_comap_le.mpr E.adapted.ge

/-- Adaptedness as a cartesian square: `Z ∩ U = U ×_{𝔸ⁿ} L`. -/
theorem isPullback_subschemeMap_toAffineSpace :
    IsPullback (subschemeMap (Z.comap E.U.1.ι) (coordinateSubspace k n r)
        (toAffineSpace f E.U.1 E.v) (coordinateSubspace_le_map_toAffineSpace E))
      (Z.comap E.U.1.ι).subschemeι (coordinateSubspace k n r).subschemeι
      (toAffineSpace f E.U.1 E.v) :=
  (isPullback_of_isClosedImmersion _ _ _ _ (subschemeMap_subschemeι _ _ _ _).symm
    (by rw [ker_subschemeι, ker_subschemeι, E.adapted])).flip

include H in
/-- The square `F_U → F_L`, `F_U → Z ∩ U`, `F_L → L`, `Z ∩ U → L` is cartesian: cancel the
adaptedness square from the bottom of the square `F_U ≅ U ×_{𝔸ⁿ} F_L`. -/
theorem isPullback_exceptionalMapOfIsPullback_subschemeMap :
    IsPullback (exceptionalMapOfIsPullback E H)
      (subschemeMap _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι)) (le_map_comap _ _))
      (subschemeMap _ (coordinateSubspace k n r) (blowUpπ (coordinateSubspace k n r))
        (le_map_comap _ _))
      (subschemeMap (Z.comap E.U.1.ι) (coordinateSubspace k n r) (toAffineSpace f E.U.1 E.v)
        (coordinateSubspace_le_map_toAffineSpace E)) := by
  have s := isPullback_exceptionalMapOfIsPullback E H
  rw [← subschemeMap_subschemeι _ (Z.comap E.U.1.ι) (blowUpπ (Z.comap E.U.1.ι))
    (le_map_comap _ _), ← subschemeMap_subschemeι _ (coordinateSubspace k n r)
    (blowUpπ (coordinateSubspace k n r)) (le_map_comap _ _)] at s
  refine s.of_bot ?_ (isPullback_subschemeMap_toAffineSpace E)
  rw [← cancel_mono (coordinateSubspace k n r).subschemeι, Category.assoc,
    subschemeMap_subschemeι, Category.assoc, subschemeMap_subschemeι,
    exceptionalMapOfIsPullback_subschemeι_assoc, H.w, subschemeMap_subschemeι_assoc]

include H in
/-- `F_U → Z ∩ U` is smooth of relative dimension `r − 1`, the base change of the model's `F_L → L`
along `Z ∩ U → L`. -/
theorem smoothOfRelativeDimension_subschemeMap_exceptional_comap (hrn : r ≤ n) :
    SmoothOfRelativeDimension (r - 1)
      (subschemeMap ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))) (Z.comap E.U.1.ι)
        (blowUpπ (Z.comap E.U.1.ι)) (le_map_comap _ _)) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{u} (n := r - 1)
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @SmoothOfRelativeDimension.{u} (r - 1))
    (isPullback_exceptionalMapOfIsPullback_subschemeMap E H)
    (smoothOfRelativeDimension_subschemeMap_exceptional_coordinateSubspace k n r hrn)

/-- `Z ∩ U → Z` is an open immersion (the base change of `U → X`). -/
instance isOpenImmersion_subschemeMap_comap_ι :
    IsOpenImmersion (subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι)) :=
  isOpenImmersion_subschemeMap_of_comap _ _ _ rfl _

/-- `Z ≤ (π_U ≫ U.ι)_* F_U`, the pushforward inequality behind `F_U → Z`. -/
theorem le_map_exceptional_comap_comp :
    Z ≤ ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).map
      (blowUpπ (Z.comap E.U.1.ι) ≫ E.U.1.ι) :=
  le_map_iff_comap_le.mpr (comap_comp Z (blowUpπ (Z.comap E.U.1.ι)) E.U.1.ι).le

include H in
/-- Composed with the open immersion `Z ∩ U → Z`: `F_U → Z` is smooth of relative dimension
`r − 1`. -/
theorem smoothOfRelativeDimension_subschemeMap_exceptional_comap_comp (hrn : r ≤ n) :
    SmoothOfRelativeDimension (r - 1)
      (subschemeMap ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))) Z
        (blowUpπ (Z.comap E.U.1.ι) ≫ E.U.1.ι) (le_map_exceptional_comap_comp E)) := by
  rw [← subschemeMap_comp_subschemeMap (blowUpπ (Z.comap E.U.1.ι)) E.U.1.ι (le_map_comap _ _)
    (le_map_comap Z E.U.1.ι)]
  have := smoothOfRelativeDimension_subschemeMap_exceptional_comap E H hrn
  have : SmoothOfRelativeDimension (r - 1 + 0)
      (subschemeMap ((Z.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))) (Z.comap E.U.1.ι)
        (blowUpπ (Z.comap E.U.1.ι)) (le_map_comap _ _) ≫
        subschemeMap (Z.comap E.U.1.ι) Z E.U.1.ι (le_map_comap Z E.U.1.ι)) := inferInstance
  rwa [add_zero] at this

end AlgebraicGeometry
