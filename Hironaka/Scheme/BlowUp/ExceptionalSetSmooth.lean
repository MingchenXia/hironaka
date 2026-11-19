/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.ExceptionalSet
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The exceptional set of a blow-up with smooth centre of positive relative dimension

For a sequence of nontrivial blow-ups the exceptional set is the total exceptional divisor
[Kol07, Definition 25]; for a single blow-up `π : B_Z X → X` along a smooth centre `Z` of
codimension at least two this is `Ex(π) = |F|`.  The inclusion `Ex(π) ⊆ |F|` is
`Hironaka.Scheme.BlowUp.ExceptionalSet`.  The reverse inclusion is proved here from one fact about
the exceptional divisor: **`F → Z` is smooth of relative dimension `r − 1 ≥ 1`**.  The argument: if
`π` were a local isomorphism at `x' ∈ F`, with `π|_{U'}` an open immersion on an open `U' ∋ x'`,
then `F ∩ U' → Z` would be an open immersion (the base change of `π|_{U'}` along `Z → X`), hence
smooth of relative dimension `0`; but it is also the restriction of `F → Z` to the open
`F ∩ U' ∋ x'` of `F`, hence smooth of relative dimension `r − 1`; and a morphism with nonempty
source has only one relative dimension (`SmoothOfRelativeDimension.eq_of_nonempty`: on an affine
piece the Kähler differentials are free of rank the relative dimension, Mathlib's
`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`, and a free module over a
nontrivial ring has one rank).  So `r − 1 = 0`, against `r ≥ 2`.  The usual phrasing of the
obstruction is through the fibre dimension `r − 1 ≥ 1` of `F → Z`; relative dimension is the form
Mathlib carries.

## Main declarations

* `AlgebraicGeometry.SmoothOfRelativeDimension.eq_of_nonempty`: a morphism with nonempty source
  that is smooth of relative dimensions `n` and `m` has `n = m`.  It is used wherever a relative
  dimension has to be read off a morphism (`Hironaka.Resolution.Algebraic.Kol07.Thm36.SmoothCharts`,
  `Hironaka.Resolution.Algebraic.OrderReduction.Step3Globalization`).
* `AlgebraicGeometry.Scheme.IdealSheafData.isOpenImmersion_subschemeMap_of_comap`: the map of
  closed subschemes induced by an open immersion `f` from `V(I.comap f)` to `V(I)` is an open
  immersion (a base change of `f`); also used in `Hironaka.Scheme.Smooth.ExceptionalModel` and
  `HironakaExamples.Sequence.Remark33OrderSeq`.
* `AlgebraicGeometry.support_comap_subset_exceptionalSet`: for `π : B ⟶ X` and a centre `Z` such
  that the induced `V(Z·𝒪_B) → V(Z)` is smooth of relative dimension `m ≥ 1`, every point of
  `V(Z·𝒪_B)` is in the exceptional set of `π`.  `Hironaka.Scheme.BlowUp.ExceptionalSetSmoothCodim`
  applies it to the monoidal transformation of a smooth centre, whose `F → Z` is smooth of
  relative dimension `r − 1` (`Hironaka.Scheme.Smooth.ExceptionalDivisorSmooth`), and combines it
  with the inclusion of `Hironaka.Scheme.BlowUp.ExceptionalSet`.
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

section RelativeDimension

variable {X Y : Scheme.{u}}

/-- On an open `V` covered by the basic opens of a set `s` of sections spanning the unit ideal,
every point lies in some `D(t)`, `t ∈ s` (Mathlib's `iSup_basicOpen_of_span_eq_top`). -/
theorem exists_mem_basicOpen_of_span_eq_top {V : X.Opens} (s : Set Γ(X, V))
    (hs : Ideal.span s = ⊤) {x : X} (hx : x ∈ V) : ∃ t ∈ s, x ∈ X.basicOpen t := by
  have h := iSup_basicOpen_of_span_eq_top V s hs
  rw [← h] at hx
  obtain ⟨t, ht⟩ := Opens.mem_iSup.mp hx
  obtain ⟨hts, hxt⟩ := Opens.mem_iSup.mp ht
  exact ⟨t, hts, hxt⟩

/-- A section that is a unit at a point is not nilpotent, so its localization is a nontrivial
ring. -/
theorem nontrivial_localizationAway_of_mem_basicOpen {V : X.Opens} (t : Γ(X, V)) {x : X}
    (hx : x ∈ X.basicOpen t) : Nontrivial (Localization.Away t) := by
  have hxV : x ∈ V := X.basicOpen_le t hx
  have hunit : IsUnit (X.presheaf.germ V x hxV t) := (Scheme.mem_basicOpen X t x hxV).mp hx
  rw [← not_subsingleton_iff_nontrivial,
    IsLocalization.subsingleton_iff (M := Submonoid.powers t) (S := Localization.Away t)]
  rintro ⟨k, hk⟩
  have h0 : IsUnit ((X.presheaf.germ V x hxV) (0 : Γ(X, V))) := by
    rw [← hk, map_pow]
    exact hunit.pow k
  rw [map_zero] at h0
  exact zero_ne_one (isUnit_zero_iff.mp h0)

/-- **A morphism with nonempty source has one relative dimension.**  If `f` is smooth of relative
dimensions `n` and `m`, pick a point; the definition gives an affine pair on which
`Γ(Y, U) → Γ(X, V)` is standard smooth of relative dimension `n`, Mathlib's
`HasRingHomProperty.appLE` gives the relative dimension `m` locally on `V`, so on a basic open
`D(t) ∋ x` both hold for `Γ(Y, U) → Γ(X, V)_t`; the Kähler differentials of that nontrivial
algebra are free of rank `n` and of rank `m`
(`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`). -/
theorem SmoothOfRelativeDimension.eq_of_nonempty (f : X ⟶ Y) [Nonempty X] {n m : ℕ}
    [hn : SmoothOfRelativeDimension n f] [hm : SmoothOfRelativeDimension m f] : n = m := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ := hn.1 x
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m)
      (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) f hm ⟨U, hU⟩ ⟨V, hV⟩ e
  obtain ⟨s, hs, hsP⟩ := hloc
  obtain ⟨t, hts, hxt⟩ := exists_mem_basicOpen_of_span_eq_top s hs hxV
  have hQm := hsP t hts
  have hQn : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom) :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
      (Localization.Away t) t _ hP
  have hnt : Nontrivial (Localization.Away t) := nontrivial_localizationAway_of_mem_basicOpen t hxt
  set ψ := (algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom with hψ
  algebraize [ψ]
  have h1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) n
  have h2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) m
  exact_mod_cast h1.symm.trans h2

end RelativeDimension

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The map of closed subschemes `V(J) → V(I)` induced by an open immersion `f : Y ⟶ X` with
`J = I.comap f` is an open immersion: it is the base change of `f` along `V(I) → X`
(Mathlib's `isPullback_of_isClosedImmersion`). -/
theorem isOpenImmersion_subschemeMap_of_comap (f : Y ⟶ X) [IsOpenImmersion f]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (hJ : J = I.comap f) (H : I ≤ J.map f) :
    IsOpenImmersion (subschemeMap J I f H) := by
  have sq : IsPullback J.subschemeι (subschemeMap J I f H) f I.subschemeι :=
    isPullback_of_isClosedImmersion J.subschemeι I.subschemeι (subschemeMap J I f H) f
      (subschemeMap_subschemeι J I f H).symm (by rw [ker_subschemeι, ker_subschemeι, hJ])
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance

/-- A point of an open `U` is the image of a point of the open subscheme `U`. -/
theorem _root_.AlgebraicGeometry.Scheme.Opens.exists_ι_eq_of_mem {Z : Scheme.{u}} {U : Z.Opens}
    {u : Z} (hu : u ∈ U) : ∃ y : U.toScheme, U.ι y = u := by
  have : u ∈ U.ι.opensRange := by rwa [Opens.opensRange_ι]
  exact Scheme.Hom.mem_opensRange.mp this

end Scheme.IdealSheafData

end AlgebraicGeometry

namespace AlgebraicGeometry

open AlgebraicGeometry Scheme.IdealSheafData

/-- **Every point of the exceptional divisor is exceptional** when the divisor is smooth of
positive relative dimension over the centre [Kol07, Definition 25]: if the induced map
`V(Z·𝒪_B) → V(Z)` of a morphism `π : B ⟶ X` is smooth of relative dimension `m ≥ 1`, then every
point of `V(Z·𝒪_B)` lies in the exceptional set of `π`.
A local isomorphism at such a point would make the restriction of `V(Z·𝒪_B) → V(Z)` to an open
neighbourhood an open immersion, smooth of relative dimension `0` and `m` at once, on a nonempty
scheme. -/
theorem support_comap_subset_exceptionalSet {B X : Scheme.{u}} (π : B ⟶ X)
    (Z : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    [SmoothOfRelativeDimension m (Scheme.IdealSheafData.subschemeMap (Z.comap π) Z π
        (Scheme.IdealSheafData.le_map_comap Z π))] :
    ((Z.comap π).support : Set B) ⊆ π.exceptionalSet := by
  intro x' hx'
  by_contra h
  obtain ⟨U', hxU', hj⟩ := (Scheme.Hom.notMem_exceptionalSet_iff π).mp h
  -- the piece `F' := V(Z·𝒪_{U'})` of the exceptional divisor over `U'`
  have hcomp : Z.comap (U'.ι ≫ π) = (Z.comap π).comap U'.ι :=
      Scheme.IdealSheafData.comap_comp Z U'.ι π
  have hle : Z.comap π ≤ (Z.comap (U'.ι ≫ π)).map U'.ι :=
      Scheme.IdealSheafData.le_map_iff_comap_le.mpr hcomp.ge
  set ι' : (Z.comap (U'.ι ≫ π)).subscheme ⟶ (Z.comap π).subscheme :=
    Scheme.IdealSheafData.subschemeMap (Z.comap (U'.ι ≫ π)) (Z.comap π) U'.ι hle with hι'_def
  have hι' : IsOpenImmersion ι' :=
    Scheme.IdealSheafData.isOpenImmersion_subschemeMap_of_comap U'.ι (Z.comap π) (Z.comap
        (U'.ι ≫ π)) hcomp hle
  set g := Scheme.IdealSheafData.subschemeMap (Z.comap π) Z π
      (Scheme.IdealSheafData.le_map_comap Z π) with hg_def
  -- `F' → F → Z` is the open immersion `V(Z·𝒪_{U'}) → V(Z)` induced by `π|_{U'}`
  have hcomp2 : ι' ≫ g = Scheme.IdealSheafData.subschemeMap (Z.comap (U'.ι ≫ π)) Z (U'.ι ≫ π)
      (Scheme.IdealSheafData.le_map_comap _ _) := by
    rw [← cancel_mono Z.subschemeι, Category.assoc, hg_def,
        Scheme.IdealSheafData.subschemeMap_subschemeι, hι'_def,
      Scheme.IdealSheafData.subschemeMap_subschemeι_assoc,
          Scheme.IdealSheafData.subschemeMap_subschemeι]
  have hopen : IsOpenImmersion (ι' ≫ g) := by
    rw [hcomp2]
    exact Scheme.IdealSheafData.isOpenImmersion_subschemeMap_of_comap (U'.ι ≫ π) Z _ rfl _
  -- `F'` is nonempty: it contains a point over `x'`
  have hne : Nonempty (Z.comap (U'.ι ≫ π)).subscheme := by
    obtain ⟨y, hy⟩ := Scheme.Opens.exists_ι_eq_of_mem hxU'
    rw [Scheme.IdealSheafData.support_comap] at hx'
    change π x' ∈ Z.support at hx'
    have hy' : y ∈ (Z.comap (U'.ι ≫ π)).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change (U'.ι ≫ π) y ∈ Z.support
      rw [Scheme.Hom.comp_apply, hy]
      exact hx'
    have hy'' : y ∈ Set.range (Z.comap (U'.ι ≫ π)).subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hy'
    obtain ⟨p, -⟩ := hy''
    exact ⟨p⟩
  -- relative dimension `0` (open immersion) and `0 + m` (restriction of `F → Z`)
  have h0 : SmoothOfRelativeDimension 0 (ι' ≫ g) := inferInstance
  have hm' : SmoothOfRelativeDimension (0 + m) (ι' ≫ g) := inferInstance
  have := SmoothOfRelativeDimension.eq_of_nonempty (ι' ≫ g) (n := 0) (m := 0 + m)
  omega

end AlgebraicGeometry
