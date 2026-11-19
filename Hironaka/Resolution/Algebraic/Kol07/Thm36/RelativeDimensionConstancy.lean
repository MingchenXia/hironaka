/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.RegularSmooth.SingularLocus
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.DisjointIntegralComponents

/-!
# The relative dimension of a smooth morphism between reduced equidimensional schemes is constant

For a smooth `k`-morphism `h : Y ⟶ X` between reduced schemes whose smooth loci over `k` have
relative dimensions `dY` and `dX` (the members of the class `IsReducedEquidimensional` of the
functorial resolution theorem), `h` is smooth of relative dimension `dY - dX`
(`smoothOfRelativeDimension_sub_of_smoothLocus`). This is what clause (4a) of the theorem needs:
the affine (34.1) (`BRAffine_eq_eraseEmpty_pullback_of_smooth`) and its descent to the resolution
functor (`BR_eq_eraseEmpty_pullback_of_smooth`) take the relative dimension `d` of `h` as an input,
and on the class of the theorem it is `dY - dX`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36`).
Kollár's schemes are equidimensional by convention [Kol07, Notation 64], so the relative dimension
of a smooth morphism between them is constant when the source is connected; here it is derived.

The argument uses no dimension theory:

* `smoothOfRelativeDimension_ι_comp_of_appLE`, `exists_smoothOfRelativeDimension_ι_comp`: a smooth
  morphism has a relative dimension near every point (Mathlib's `Smooth` is affine-locally standard
  smooth, and a submersive presentation has a dimension), lifted to the scheme level on an affine
  open of the source.
* `exists_smoothOfRelativeDimension_of_irreducibleSpace`: on an irreducible source the local
  relative dimensions agree (`SmoothOfRelativeDimension.eq_of_nonempty` on the nonempty overlaps)
  and glue (`SmoothOfRelativeDimension n` is Zariski-local at the source).
* `smoothOfRelativeDimension_sub_of_smoothLocus`: near every point of `Y` the relative dimension
  `n` of `h` satisfies `n + dX = dY`, by `eq_of_nonempty` on a nonempty open of that neighbourhood
  lying over both smooth loci: the smooth locus of the reduced `Y` is dense
  (`dense_smoothLocus_of_perfectField`), the smooth `h` is an open map, and the smooth locus of the
  reduced `X` is dense, so some smooth point of the neighbourhood maps to a smooth point of `X`;
  source-locality assembles `h`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Scheme

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]


variable {k : Type u} [Field k] [CharZero k]

/-- An affine pair `U ⊆ X`, `V ⊆ Y` on which `f` is standard smooth of relative dimension `n` gives
the scheme-level relative dimension of `f` on the open `V`: `f.resLE U V e` has it by
`HasRingHomProperty.iff_of_isAffine` (the global sections of the restriction are `f.appLE U V e` up
to isomorphism, `arrowResLEAppIso`), and `V.ι ≫ f = f.resLE U V e ≫ U.ι` adds the relative
dimension `0` of the open immersion. -/
theorem smoothOfRelativeDimension_ι_comp_of_appLE {X Y : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) (n : ℕ)
    (hn : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have : IsAffine (U : Scheme.{u}) := hU
  have : IsAffine (V : Scheme.{u}) := hV
  have hres : SmoothOfRelativeDimension n (f.resLE U V e) := by
    refine (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)
      (f := f.resLE U V e)).mpr ?_
    have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
        (f.appLE U V e).hom :=
      RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn
    exact ((RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).arrow_mk_iso_iff
      (arrowResLEAppIso f U V e)).mpr hloc
  have hcomp : SmoothOfRelativeDimension (n + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  rw [Nat.add_zero, Scheme.Hom.resLE_comp_ι] at hcomp
  exact hcomp

/-- A smooth morphism has a relative dimension near every point of the source: Mathlib's `Smooth`
is affine-locally standard smooth (`Smooth.exists_isStandardSmooth`), and a submersive presentation
has a dimension. -/
theorem exists_smoothOfRelativeDimension_ι_comp {X Y : Scheme.{u}} (f : Y ⟶ X) [Smooth f]
    (y : Y) : ∃ (V : Y.Opens) (n : ℕ), y ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hy, e, hss⟩ := Smooth.exists_isStandardSmooth f y
  let _ : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V e).hom.toAlgebra
  have hss' : Algebra.IsStandardSmooth Γ(X, U) Γ(Y, V) := hss
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hss'.out
  refine ⟨V, P.dimension, hy, smoothOfRelativeDimension_ι_comp_of_appLE f hU hV e _ ?_⟩
  exact P.isStandardSmoothOfRelativeDimension rfl

/-- A smooth morphism from an IRREDUCIBLE scheme has a global relative dimension: two local
relative dimensions agree on the (nonempty) overlap of their opens
(`SmoothOfRelativeDimension.eq_of_nonempty`), and `SmoothOfRelativeDimension n` is Zariski-local at
the source. -/
theorem exists_smoothOfRelativeDimension_of_irreducibleSpace {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Smooth f] [IrreducibleSpace Y] : ∃ n, SmoothOfRelativeDimension n f := by
  choose V n hmem hP using exists_smoothOfRelativeDimension_ι_comp f
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  have hn : ∀ y, n y = n y₀ := by
    intro y
    obtain ⟨w, hw⟩ := nonempty_preirreducible_inter (V y).isOpen (V y₀).isOpen ⟨y, hmem y⟩
      ⟨y₀, hmem y₀⟩
    let W : Y.Opens := V y ⊓ V y₀
    have : Nonempty (W : Scheme.{u}) := ⟨⟨w, hw⟩⟩
    have i1 : SmoothOfRelativeDimension (0 + n y)
        (Y.homOfLE (inf_le_left : W ≤ V y) ≫ ((V y).ι ≫ f)) := inferInstance
    have i2 : SmoothOfRelativeDimension (0 + n y₀)
        (Y.homOfLE (inf_le_right : W ≤ V y₀) ≫ ((V y₀).ι ≫ f)) := inferInstance
    rw [Nat.zero_add, ← Category.assoc, Scheme.homOfLE_ι] at i1 i2
    exact SmoothOfRelativeDimension.eq_of_nonempty (W.ι ≫ f)
  refine ⟨n y₀, ?_⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n y₀)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have hV : ⨆ y, V y = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hmem y⟩
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension (n y₀))
    V hV).mpr fun y => ?_
  rw [← hn y]
  exact hP y

/-- The relative dimension of a smooth morphism between reduced equidimensional schemes is constant:
a smooth `k`-morphism `h : Y ⟶ X` between reduced schemes whose smooth loci over `k` have relative
dimensions `dY` and `dX` is smooth of relative dimension `dY - dX`. Source-locality over opens
`U ∋ y` on which `h` has a relative dimension `n` (`exists_smoothOfRelativeDimension_ι_comp`);
`n + dX = dY` by `eq_of_nonempty` on the nonempty open `U ∩ Y^ns ∩ h⁻¹(X^ns)` of `U`: `U ∩ Y^ns` is
a nonempty open (`Y^ns` is dense, `dense_smoothLocus_of_perfectField`), its image under the open
map `h` (`Scheme.Hom.isOpenMap`, smooth morphisms being flat and locally of finite presentation)
meets the dense `X^ns`; there the structure morphism of `Y` factors through `Y^ns` (relative
dimension `dY`) and through `h` and `X^ns` (relative dimension `n + dX`). No dimension theory
enters. -/
theorem smoothOfRelativeDimension_sub_of_smoothLocus (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [IsReduced X] [IsReduced Y] {dX dY : ℕ}
    [hdX : SmoothOfRelativeDimension dX
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))]
    [hdY : SmoothOfRelativeDimension dY
      ((Y ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (Y ↘ Spec (CommRingCat.of k)))]
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] [Smooth h] :
    SmoothOfRelativeDimension (dY - dX) h := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (dY - dX)) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  -- the local relative dimensions
  choose V n hmem hP using exists_smoothOfRelativeDimension_ι_comp h
  have hV : ⨆ y, V y = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hmem y⟩
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension (dY - dX))
    V hV).mpr fun y => ?_
  suffices hne : n y = dY - dX by
    rw [← hne]
    exact hP y
  set U : Y.Opens := V y with hUdef
  set g : (U : Scheme.{u}) ⟶ X := U.ι ≫ h with hgdef
  have hn : SmoothOfRelativeDimension (n y) g := hP y
  have hgπ : g ≫ (X ↘ Spec (CommRingCat.of k)) = U.ι ≫ (Y ↘ Spec (CommRingCat.of k)) := by
    rw [hgdef, Category.assoc, HomIsOver.comp_over (f := h) (S := Spec (CommRingCat.of k))]
  -- a smooth point of `U` over a smooth point of `X`
  have hdenseY := (Y ↘ Spec (CommRingCat.of k)).dense_smoothLocus_of_perfectField
  have hdenseX := (X ↘ Spec (CommRingCat.of k)).dense_smoothLocus_of_perfectField
  have hopenMap : IsOpenMap h := h.isOpenMap
  obtain ⟨y₁, hy₁U, hy₁s⟩ := hdenseY.inter_open_nonempty (U : Set Y) U.isOpen ⟨y, hmem y⟩
  have hO : IsOpen ((U : Set Y) ∩ ((Y ↘ Spec (CommRingCat.of k)).smoothLocus : Set Y)) :=
    U.isOpen.inter (Y ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen
  obtain ⟨_, ⟨y₂, ⟨hy₂U, hy₂s⟩, rfl⟩, hy₂X⟩ :=
    hdenseX.inter_open_nonempty _ (hopenMap _ hO) ⟨h y₁, y₁, ⟨hy₁U, hy₁s⟩, rfl⟩
  -- the nonempty open `WU` over both smooth loci
  set WU : (U : Scheme.{u}).Opens :=
    U.ι ⁻¹ᵁ (Y ↘ Spec (CommRingCat.of k)).smoothLocus ⊓
      g ⁻¹ᵁ (X ↘ Spec (CommRingCat.of k)).smoothLocus with hWUdef
  have : Nonempty (WU : Scheme.{u}) := ⟨⟨⟨y₂, hy₂U⟩, hy₂s, hy₂X⟩⟩
  -- relative dimension `dY` of `WU.ι ≫ U.ι ≫ πY` through the smooth locus of `Y`
  have hrange : Set.range ⇑(WU.ι ≫ U.ι) ⊆
      Set.range ⇑(Y ↘ Spec (CommRingCat.of k)).smoothLocus.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact w.2.1
  have hj := IsOpenImmersion.lift_fac (Y ↘ Spec (CommRingCat.of k)).smoothLocus.ι (WU.ι ≫ U.ι)
    hrange
  have iY : SmoothOfRelativeDimension (0 + dY)
      (IsOpenImmersion.lift (Y ↘ Spec (CommRingCat.of k)).smoothLocus.ι (WU.ι ≫ U.ι) hrange ≫
        ((Y ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (Y ↘ Spec (CommRingCat.of k)))) :=
    inferInstance
  rw [Nat.zero_add, ← Category.assoc, hj] at iY
  -- relative dimension `n + dX` of the same morphism through the smooth locus of `X`
  have e : WU ≤ g ⁻¹ᵁ (X ↘ Spec (CommRingCat.of k)).smoothLocus := inf_le_right
  have hgres : SmoothOfRelativeDimension (n y)
      (g.resLE (X ↘ Spec (CommRingCat.of k)).smoothLocus WU e) := by
    have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension (n y)) :=
      @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
    have hres : SmoothOfRelativeDimension (n y)
        (g ∣_ (X ↘ Spec (CommRingCat.of k)).smoothLocus) :=
      IsZariskiLocalAtTarget.restrict hn _
    have : SmoothOfRelativeDimension (0 + n y)
        ((U : Scheme.{u}).homOfLE e ≫ (g ∣_ (X ↘ Spec (CommRingCat.of k)).smoothLocus)) :=
      inferInstance
    rw [Nat.zero_add] at this
    exact this
  have iX : SmoothOfRelativeDimension (n y + dX)
      (g.resLE (X ↘ Spec (CommRingCat.of k)).smoothLocus WU e ≫
        ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))) :=
    inferInstance
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgπ, ← Category.assoc] at iX
  have hnd : n y + dX = dY :=
    SmoothOfRelativeDimension.eq_of_nonempty ((WU.ι ≫ U.ι) ≫ (Y ↘ Spec (CommRingCat.of k)))
  omega

end Hironaka.Resolution
