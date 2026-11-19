/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUp.Glue.RestrictOpen
import Hironaka.Scheme.Smooth.BlowUpSmooth
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
public import Hironaka.Scheme.Smooth.EtaleCoordinatesAdapted
import Hironaka.Scheme.Smooth.ExceptionalChart
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.FiniteLength

/-!
# The exceptional divisor of a smooth blow-up is smooth

Kollár: "If `π_{Z,X}` is a smooth blow-up, then `F` and `B_Z X` are both smooth"
[Kol07, Notation 19], the sentence for `F = π⁻¹(Z)`, stated there without proof. Setting: `X`
smooth over the perfect field `k` of relative dimension `n`, `V(Z)` smooth of relative dimension
`n − r`, `r ≤ n`. Proved here: `F → Spec k` is smooth of relative dimension `n − 1`, `F → Z` is
smooth of relative dimension `r − 1`, and so is every fibre `F_z → Spec κ(z)`.

**Why the theorems hold.** At every closed point `x` of `V(Z)` there is a chart `U ∋ x` of étale
coordinates adapted to `Z` (`EtaleCoordinatesAdapted`), and over `U` the blow-up is the fibre
product with the model, `B_{Z∩U} U ≅ U ×_{𝔸ⁿ} B_L 𝔸ⁿ` (`BlowUpSmoothChart.lean`), so its
exceptional divisor is `F_U ≅ U ×_{𝔸ⁿ} F_L` (`ExceptionalChart.lean`). The model's `F_L` is smooth
of relative dimension `n − 1` over `k` and `F_L → L` is smooth of relative dimension `r − 1`
(`ExceptionalModel.lean`), and both properties pass to `F_U` by base change along the étale `g`,
resp. along `Z ∩ U → L` (`ExceptionalChart.lean`). Now `π⁻¹(U) ≅ B_{Z∩U} U` (`restrictIso`), and
the pieces `F ∩ π⁻¹(U) = F_U` cover `F`: a point of `F` lies over a point of `V(Z)`, which lies in
one of the charts `U_x` because the charts and `X ∖ V(Z)` cover the Jacobson space `X` (the cover
of `BlowUpSmooth.lean`). Smoothness of relative dimension `m` is Zariski-local on the source, which
gives the smoothness of `F → Spec k` (relative dimension `n − 1`) and of `F → Z` (relative
dimension `r − 1`); the fibre of `F → Z` over `z ∈ Z` is its base change along `Spec κ(z) → Z`,
smooth of relative dimension `r − 1` over `κ(z)`.

## Main declarations

* `AlgebraicGeometry.exceptionalRestrictPiece`: `F_U → F`, the open immersion of the exceptional
  divisor of `B_{Z∩U} U` into that of `B_Z X`, with `exists_exceptionalRestrictPiece_eq`.
* `AlgebraicGeometry.exceptionalDivisorCover`: the open cover of `F` by the pieces over the adapted
  charts at the closed points of `V(Z)`.
* `AlgebraicGeometry.smoothOfRelativeDimension_exceptional`, `smooth_exceptional`: `F` is smooth
  over `k` of relative dimension `n − 1`.
* `AlgebraicGeometry.smoothOfRelativeDimension_subschemeMap_exceptional`: `F → Z` is smooth of
  relative dimension `r − 1`, over a perfect field (the arbitrary-field form is obtained by
  descent in `ExceptionalBaseChange.lean` and `ExceptionalDivisorSmooth.lean`).
* `AlgebraicGeometry.smoothOfRelativeDimension_fiberToSpecResidueField_exceptional`: the fibres of
  `F → Z` are smooth of relative dimension `r − 1`.

The projective-bundle structure of `F` over `Z` is in `ExceptionalBundle.lean`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

namespace AlgebraicGeometry

open Scheme.Hom

/-- Two induced maps of closed subschemes along equal morphisms are equal. -/
theorem subschemeMap_congr_hom {B Y : Scheme.{u}} {K : B.IdealSheafData} {L : Y.IdealSheafData}
    {g g' : B ⟶ Y} (h : g = g') (H1 : L ≤ K.map g) (H2 : L ≤ K.map g') :
    Scheme.IdealSheafData.subschemeMap K L g H1 = Scheme.IdealSheafData.subschemeMap K L g' H2 := by
  subst h
  rfl

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens)

/-- `blowUpMap U.ι I : B_{I|_U} U ⟶ B_I X` is an open immersion: it is `π⁻¹(U) → B_I X` up to the
isomorphism `restrictIso`. -/
instance isOpenImmersion_restrictHom : IsOpenImmersion (blowUpMap U.ι I) := by
  rw [← restrictHomToPreimage_ι]
  have : IsIso (restrictHomToPreimage I U) := (Scheme.IdealSheafData.blowUp.restrictIso I
      U).isIso_hom
  infer_instance

/-- The exceptional divisor of `B_I X`, pulled back to `B_{I|_U} U`, is the exceptional divisor of
the latter (`blowUpMap U.ι I ≫ π = π_U ≫ U.ι`). -/
theorem comap_restrictHom :
    (I.comap (Scheme.IdealSheafData.blowUpπ I)).comap (blowUpMap U.ι I) =
      (I.comap U.ι).comap (Scheme.IdealSheafData.blowUpπ (I.comap U.ι)) :=
  (Scheme.IdealSheafData.comap_comp I (blowUpMap U.ι I) (Scheme.IdealSheafData.blowUpπ
      I)).symm.trans
    ((congrArg (fun m => I.comap m) (blowUpMap_π U.ι I)).trans
      (Scheme.IdealSheafData.comap_comp I (Scheme.IdealSheafData.blowUpπ (I.comap U.ι)) U.ι))

/-- `F ≤ (blowUpMap U.ι I)_* F_U`. -/
theorem le_map_restrictHom :
    I.comap (Scheme.IdealSheafData.blowUpπ I) ≤
      ((I.comap U.ι).comap (Scheme.IdealSheafData.blowUpπ (I.comap U.ι))).map (blowUpMap U.ι I) :=
  Scheme.IdealSheafData.le_map_iff_comap_le.mpr (comap_restrictHom I U).le

/-- The piece of the exceptional divisor over `U`: `F_U → F`, the restriction of `blowUpMap U.ι I`
to the exceptional divisors. -/
noncomputable def exceptionalRestrictPiece :
    ((I.comap U.ι).comap (Scheme.IdealSheafData.blowUpπ (I.comap U.ι))).subscheme ⟶ (I.comap
        (Scheme.IdealSheafData.blowUpπ I)).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (blowUpMap U.ι I) (le_map_restrictHom I U)

instance isOpenImmersion_exceptionalRestrictPiece :
    IsOpenImmersion (exceptionalRestrictPiece I U) :=
  Scheme.IdealSheafData.isOpenImmersion_subschemeMap_of_comap _ _ _ (comap_restrictHom I U).symm _

@[reassoc (attr := simp)]
theorem exceptionalRestrictPiece_subschemeι :
    exceptionalRestrictPiece I U ≫ (I.comap (Scheme.IdealSheafData.blowUpπ I)).subschemeι =
      ((I.comap U.ι).comap (Scheme.IdealSheafData.blowUpπ (I.comap U.ι))).subschemeι ≫ blowUpMap
          U.ι I :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- `F_U` is the base change of `F` along `blowUpMap U.ι I`. -/
theorem isPullback_exceptionalRestrictPiece :
    IsPullback ((I.comap U.ι).comap (Scheme.IdealSheafData.blowUpπ (I.comap U.ι))).subschemeι
      (exceptionalRestrictPiece I U) (blowUpMap U.ι I) (I.comap
          (Scheme.IdealSheafData.blowUpπ I)).subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (exceptionalRestrictPiece_subschemeι I U).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
        comap_restrictHom])

/-- A point of `F` lying over `U` is in the image of the piece `F_U`. -/
theorem exists_exceptionalRestrictPiece_eq (y : (I.comap (Scheme.IdealSheafData.blowUpπ
    I)).subscheme)
    (hy : Scheme.IdealSheafData.blowUpπ I ((I.comap (Scheme.IdealSheafData.blowUpπ I)).subschemeι
        y) ∈ U) :
    ∃ p, exceptionalRestrictPiece I U p = y := by
  have hb : (I.comap (Scheme.IdealSheafData.blowUpπ I)).subschemeι y ∈
      Scheme.IdealSheafData.blowUpπ I ⁻¹ᵁ U := hy
  obtain ⟨w, hw⟩ := Scheme.Opens.exists_ι_eq_of_mem hb
  have hres : blowUpMap U.ι I (preimageToRestrict I U w) =
      (I.comap (Scheme.IdealSheafData.blowUpπ I)).subschemeι y := by
    rw [← Scheme.Hom.comp_apply, preimageToRestrict_restrictHom]
    exact hw
  obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_exceptionalRestrictPiece I U) (preimageToRestrict I U w) y hres
  exact ⟨p, hp⟩

/-- `I ≤ (blowUpMap U.ι I ≫ π)_* F_U`, the pushforward inequality behind `F_U → F → V(I)`. -/
theorem le_map_comap_restrictHom_comp :
    I ≤ ((I.comap U.ι).comap (Scheme.IdealSheafData.blowUpπ (I.comap U.ι))).map
      (blowUpMap U.ι I ≫ Scheme.IdealSheafData.blowUpπ I) :=
  Scheme.IdealSheafData.le_map_iff_comap_le.mpr
    ((Scheme.IdealSheafData.comap_comp I (blowUpMap U.ι I) (Scheme.IdealSheafData.blowUpπ I)).trans
        (comap_restrictHom I U)).le

end AlgebraicGeometry

namespace AlgebraicGeometry

open AlgebraicGeometry Scheme.Hom

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n r : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
  [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n)

include f hrn

/-- A chart of étale coordinates adapted to `Z` at a closed point of `V(Z)`
(`nonempty_etaleCoordinatesAdapted`). -/
noncomputable def adaptedChart (x : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support}) :
    EtaleCoordinatesAdapted f n r Z x.1 :=
  Classical.choice (nonempty_etaleCoordinatesAdapted f n r Z hrn x.2.2 x.2.1)

/-- The pieces `F_{U_x}` over the adapted charts at the closed points `x` of `V(Z)` cover `F`:
a point of `F` lies over a point of `V(Z)`, which lies in some `U_x` by the Jacobson cover (the
charts and `X ∖ V(Z)` cover `X`, `iSup_eq_top_of_forall_isClosed`). -/
theorem exists_exceptionalRestrictPiece_adaptedChart_eq (y : (Z.comap
    (Scheme.IdealSheafData.blowUpπ Z)).subscheme) :
    ∃ (x : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support})
      (p : ((Z.comap (adaptedChart f n r Z hrn x).U.1.ι).comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap (adaptedChart f n r Z hrn x).U.1.ι))).subscheme),
      exceptionalRestrictPiece Z (adaptedChart f n r Z hrn x).U.1 p = y := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hZ : Scheme.IdealSheafData.blowUpπ Z ((Z.comap (Scheme.IdealSheafData.blowUpπ Z)).subschemeι
      y) ∈ Z.support := by
    have h1 : (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).subschemeι y ∈
        Set.range (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).subschemeι := ⟨y, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap] at h1
    exact h1
  have hcover := iSup_eq_top_of_forall_isClosed Z (fun x => (adaptedChart f n r Z hrn x).U.1)
    (fun x => (adaptedChart f n r Z hrn x).mem)
  have hmem : Scheme.IdealSheafData.blowUpπ Z ((Z.comap (Scheme.IdealSheafData.blowUpπ
      Z)).subschemeι y) ∈
      (⨆ x, (adaptedChart f n r Z hrn x).U.1) ⊔ Z.support.compl := by
    rw [hcover]
    trivial
  rw [Opens.mem_sup] at hmem
  rcases hmem with hmem | hmem
  · rw [Opens.mem_iSup] at hmem
    obtain ⟨x, hx⟩ := hmem
    obtain ⟨p, hp⟩ := exists_exceptionalRestrictPiece_eq Z _ y hx
    exact ⟨x, p, hp⟩
  · exact (hmem hZ).elim

/-- The open cover of the exceptional divisor `F` by the pieces `F_{U_x}` over the adapted charts
at the closed points of `V(Z)`. -/
noncomputable def exceptionalDivisorCover : (Z.comap (Scheme.IdealSheafData.blowUpπ
    Z)).subscheme.OpenCover :=
  Scheme.Cover.mkOfCovers {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support}
    (fun x => ((Z.comap (adaptedChart f n r Z hrn x).U.1.ι).comap
      (Scheme.IdealSheafData.blowUpπ (Z.comap (adaptedChart f n r Z hrn x).U.1.ι))).subscheme)
    (fun x => exceptionalRestrictPiece Z (adaptedChart f n r Z hrn x).U.1)
    (exists_exceptionalRestrictPiece_adaptedChart_eq f n r Z hrn)

/-- On the piece over a chart: `F_{U_x} → F → B_Z X → Spec k` is smooth of relative dimension
`n − 1` (it is `F_{U_x} → B_{Z∩U} U → U → Spec k`, `ExceptionalChart.lean`). -/
theorem smoothOfRelativeDimension_exceptionalRestrictPiece_comp
    (x : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support}) :
    SmoothOfRelativeDimension (n - 1)
      (exceptionalRestrictPiece Z (adaptedChart f n r Z hrn x).U.1 ≫
        (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).subschemeι ≫ Scheme.IdealSheafData.blowUpπ Z ≫
            f) := by
  obtain ⟨φ, H⟩ := exists_isPullback_blowUp (adaptedChart f n r Z hrn x)
  have := smoothOfRelativeDimension_exceptional_comap (adaptedChart f n r Z hrn x) H
  rwa [exceptionalRestrictPiece_subschemeι_assoc,
    ← Category.assoc (blowUpMap _ Z) (Scheme.IdealSheafData.blowUpπ Z) f, blowUpMap_π,
    Category.assoc]

/-- **The exceptional divisor of a smooth blow-up is smooth over `k` of relative dimension `n − 1`**
("if `π_{Z,X}` is a smooth blow-up, then `F` … [is] smooth", [Kol07, Notation 19]): étale-locally
the model's `F_L`, covered by copies of `𝔸^{n-1}`, pulled back along the étale `F_U → F_L`, glued
over the Jacobson cover as in `BlowUpSmooth.lean`. -/
theorem smoothOfRelativeDimension_exceptional :
    SmoothOfRelativeDimension (n - 1)
      ((Z.comap (Scheme.IdealSheafData.blowUpπ Z)).subschemeι ≫ Scheme.IdealSheafData.blowUpπ Z ≫
          f) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (n - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} (n - 1))
    (exceptionalDivisorCover f n r Z hrn) fun x =>
      smoothOfRelativeDimension_exceptionalRestrictPiece_comp f n r Z hrn x

/-- In Kollár's words [Kol07, Notation 19]: `F` is smooth over `k`. -/
theorem smooth_exceptional : Smooth ((Z.comap (Scheme.IdealSheafData.blowUpπ Z)).subschemeι ≫
    Scheme.IdealSheafData.blowUpπ Z ≫ f) := by
  have := smoothOfRelativeDimension_exceptional f n r Z hrn
  exact SmoothOfRelativeDimension.smooth (n - 1) _

/-- On the piece over a chart: `F_{U_x} → F → Z` is smooth of relative dimension `r − 1` (it is
`F_{U_x} → Z ∩ U → Z`, `ExceptionalChart.lean`). -/
theorem smoothOfRelativeDimension_exceptionalRestrictPiece_comp_subschemeMap
    (x : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support}) :
    SmoothOfRelativeDimension (r - 1)
      (exceptionalRestrictPiece Z (adaptedChart f n r Z hrn x).U.1 ≫
        Scheme.IdealSheafData.subschemeMap (Z.comap (Scheme.IdealSheafData.blowUpπ Z)) Z
            (Scheme.IdealSheafData.blowUpπ Z) (Scheme.IdealSheafData.le_map_comap Z
            (Scheme.IdealSheafData.blowUpπ Z))) := by
  obtain ⟨φ, H⟩ := exists_isPullback_blowUp (adaptedChart f n r Z hrn x)
  have := smoothOfRelativeDimension_subschemeMap_exceptional_comap_comp
    (adaptedChart f n r Z hrn x) H hrn
  rw [exceptionalRestrictPiece, subschemeMap_comp_subschemeMap _ _ _ _
    (le_map_comap_restrictHom_comp Z _),
    subschemeMap_congr_hom (blowUpMap_π _ Z) _
      (le_map_exceptional_comap_comp (adaptedChart f n r Z hrn x))]
  exact this

/-- Over a perfect field, **`F → Z` is smooth of relative dimension `r − 1`** ([Kol07, Notation 19];
the projective bundle of [Hau14, Definition 4.8]): on the piece over a chart it is the base change
of the model's `F_L → L` along `Z ∩ U → L`, glued over the Jacobson cover. -/
theorem smoothOfRelativeDimension_subschemeMap_exceptional :
    SmoothOfRelativeDimension (r - 1)
      (Scheme.IdealSheafData.subschemeMap (Z.comap (Scheme.IdealSheafData.blowUpπ Z)) Z
          (Scheme.IdealSheafData.blowUpπ Z) (Scheme.IdealSheafData.le_map_comap Z
          (Scheme.IdealSheafData.blowUpπ Z))) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (r - 1)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} (r - 1))
    (exceptionalDivisorCover f n r Z hrn) fun x =>
      smoothOfRelativeDimension_exceptionalRestrictPiece_comp_subschemeMap f n r Z hrn x

/-- For `z ∈ Z` the fibre `F_z = F ×_Z Spec κ(z)` of `F → Z` is smooth over `Spec κ(z)` of
relative dimension `r − 1` (the base change of `smoothOfRelativeDimension_subschemeMap_exceptional`
along `Spec κ(z) → Z`). -/
theorem smoothOfRelativeDimension_fiberToSpecResidueField_exceptional (z : Z.subscheme) :
    SmoothOfRelativeDimension (r - 1)
      ((Scheme.IdealSheafData.subschemeMap (Z.comap (Scheme.IdealSheafData.blowUpπ Z)) Z
          (Scheme.IdealSheafData.blowUpπ Z)
        (Scheme.IdealSheafData.le_map_comap Z (Scheme.IdealSheafData.blowUpπ
            Z))).fiberToSpecResidueField z) := by
  have := smoothOfRelativeDimension_subschemeMap_exceptional f n r Z hrn
  have hbc := smoothOfRelativeDimension_isStableUnderBaseChange.{u} (n := r - 1)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @SmoothOfRelativeDimension.{u} (r - 1))
    (IsPullback.of_hasPullback _ (Z.subscheme.fromSpecResidueField z)) this

end AlgebraicGeometry
