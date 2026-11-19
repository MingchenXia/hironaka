/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Snc.DictionaryRegular
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# An snc support is Zariski-local

[Kol07, Definition 24] is a pointwise condition: a divisor `E = ∑ E^i` has simple normal crossings
iff at every point `x` there are local coordinates `z₁, …, zₙ` with each component through `x` one
of the coordinate hypersurfaces. Consequently, the EXISTENCE of an snc family with a given support
`S` is a Zariski-local question: if every piece `𝒰.X i` of an open cover of `Y` carries an snc
family whose support is the preimage of `S`, then `Y` carries one with support `S`
(`exists_snc_of_openCover`). The witness is the family of the irreducible components of `S` with
their reduced structure (`componentFamily` of the vanishing ideal of `S`,
`Hironaka.Scheme.Snc.Dictionary`): locally at `x = 𝒰.f i w` each component through `x` is the
reduced component of a generic point `η` of `S`, `η = 𝒰.f i η'` with `η'` a generic point of the
local support, hence of one member `F^j` of the local family (the members' supports cover the local
support), so its stalk at `x` is the stalk of `F^j` at `w` transported along the stalk isomorphism
of the open immersion — the coordinate `z_{c(j)}` of the local snc data
(`stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme`). The dictionary between the reduced
components and the snc data (`componentFamily_isSncAt_iff`: snc at `x` iff every minimal prime of
the stalk of `S` is a coordinate) then gives `IsSncAt` at `x` with the transported coordinates, and
the members are regular because their stalk quotients are those of the local members
(`isRegular_subscheme_of_isRegularLocalRing_quotient`). This is how clause (3) of
[Kol07, Theorem 36] — `Π⁻¹(Sing X)` an snc divisor — is checked on the last stage of the resolution
from its restrictions to an affine cover
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.ClauseLocality`).

**Finiteness.** The statement needs `[NoetherianSpace Y]` (so that `S` has finitely many irreducible
components, `Closeds.genericPoints_finite`): without it the conclusion is FALSE — on the infinite
disjoint union `⨆ₙ 𝔸²` with `S ∩ 𝔸²ₙ` a configuration of `n` lines in general position, every piece
carries an snc family (`n` members), but the members of any snc family are regular, so two crossing
lines lie in different members and a global family would need infinitely many. The last stage of a
blow-up sequence of a scheme of finite type over a field has a Noetherian space.

* `Closeds.mem_genericPoints_of_le` — a generic point of `Z` lying in a closed `Z' ≤ Z` is a generic
  point of `Z'`;
* `AlgebraicGeometry.Scheme.DivisorFamily.mem_support_iff_exists` — a point lies in the support of a
  family iff on one of its
  members;
* `isClosed_of_openCover` — a set whose preimages under the pieces of an open cover are closed is
  closed;
* `preimage_closure_singleton` — the preimage of `closure {ι η}` along an open immersion `ι` is
  `closure {η}`;
* `exists_stalkIdeal_vanishingIdeal_closure_eq` — the local identification of the stalk of a reduced
  component of `S` at `ι w` with the transported stalk of a member of the local family;
* `exists_snc_of_openCover` — the theorem.

Sources: [Kol07, Definition 24] (the pointwise condition); [Hir64, Definition 2] (normal crossings
through a regular system of parameters, the form the dictionary uses).
-/

public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.IdealSheafData
  Hironaka.Sequence

namespace Hironaka.Snc

section Topology

variable {α : Type*} [TopologicalSpace α]

/-- A generic point of a closed set `Z` lying in a closed subset `Z' ≤ Z` is a generic point of `Z'`
(`Closeds.mem_genericPoints_iff`: the closure of the point is a maximal irreducible subset of `Z`,
hence of `Z'`). -/
theorem _root_.TopologicalSpace.Closeds.mem_genericPoints_of_le [T0Space α] [QuasiSober α]
    {Z Z' : Closeds α} (hle : Z' ≤ Z) {η : α} (hη : η ∈ Z.genericPoints) (hη' : η ∈ Z') :
    η ∈ Z'.genericPoints := by
  rw [Closeds.mem_genericPoints_iff] at hη ⊢
  refine ⟨⟨Z'.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη'),
    isIrreducible_singleton.closure⟩, fun T hT hTη => ?_⟩
  exact hη.2 ⟨hT.1.trans (SetLike.coe_subset_coe.mpr hle), hT.2⟩ hTη

end Topology

section Family

variable {X : Scheme.{u}}

end Family

section Cover

variable {Y : Scheme.{u}}

/-- A subset of `Y` whose preimages under the pieces of an open cover are closed is closed: its
complement is the union of the images of the open preimages of the complement under the (open)
pieces, which cover `Y`. -/
theorem isClosed_of_openCover (𝒰 : Y.OpenCover.{v}) (S : Set Y)
    (h : ∀ i, IsClosed (𝒰.f i ⁻¹' S)) : IsClosed S := by
  rw [← isOpen_compl_iff]
  have hS : Sᶜ = ⋃ i, 𝒰.f i '' (𝒰.f i ⁻¹' Sᶜ) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq y
      exact Set.mem_iUnion.mpr ⟨i, w, hy, rfl⟩
    · intro hy
      obtain ⟨i, w, hw, rfl⟩ := Set.mem_iUnion.mp hy
      exact hw
  rw [hS]
  exact isOpen_iUnion fun i => (𝒰.f i).isOpenEmbedding.isOpenMap _ (h i).isOpen_compl

end Cover

section Local

variable {Y W : Scheme.{u}} (ι : W ⟶ Y) [IsOpenImmersion ι]

/-- The preimage of the closure of a point along an open immersion is the closure of the point (an
open embedding commutes with closures and is injective). -/
theorem preimage_closure_singleton (η : W) :
    (Closeds.closure {ι η}).preimage ι.continuous = Closeds.closure {η} := by
  apply SetLike.coe_injective
  change ι ⁻¹' closure {ι η} = closure {η}
  rw [ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage ι.continuous,
    ← Set.image_singleton, ι.isOpenEmbedding.injective.preimage_image]

/-- **The local identification** behind `exists_snc_of_openCover`. Let `S` be closed in the
Noetherian `Y`, `ι : W ⟶ Y` an open immersion, `F` an snc family on `W` with support `ι⁻¹ S`, `η` a
generic point of `S` specializing to `ι w`. Then `η = ι η'` with `η'` a generic point of the support
of some member `F^j` through `w`, and the stalk at `ι w` of the reduced component `closure {η}` is
the stalk of `F^j` at `w` transported along the stalk isomorphism of `ι`
(`stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme` on `W`, the pull-back of a vanishing
ideal along a smooth morphism `comap_vanishingIdeal_of_smooth`, and
`stalkIdeal_eq_map_symm_stalkIdeal_comap`). -/
theorem exists_stalkIdeal_vanishingIdeal_closure_eq [NoetherianSpace Y] (S : Closeds Y)
    {F : DivisorFamily W} (hF : F.IsSnc) (hsupp : (F.support : Set W) = ι ⁻¹' S) {η : Y}
    (hη : η ∈ S.genericPoints) {w : W} (hηw : η ⤳ ι w) :
    ∃ j : F.ι, w ∈ (F.component j).support ∧
      (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal (ι w) =
        ((F.component j).stalkIdeal w).map (stalkEquivOfIsOpenImmersion ι w).symm := by
  obtain ⟨η', rfl⟩ : η ∈ Set.range ι :=
    hηw.mem_open ι.isOpenEmbedding.isOpen_range (Set.mem_range_self w)
  have hη'w : η' ⤳ w := ι.isOpenEmbedding.isInducing.specializes_iff.mp hηw
  have hpre : F.support = S.preimage ι.continuous := SetLike.coe_injective hsupp
  have hη'S : η' ∈ F.support.genericPoints := by
    have h1 : ι η' ∈ (IdealSheafData.vanishingIdeal S).support.genericPoints := by
      rwa [support_vanishingIdeal_eq]
    have h2 := mem_genericPoints_comap_of_isOpenImmersion ι (IdealSheafData.vanishingIdeal S) h1
    rwa [Hironaka.Smooth.comap_vanishingIdeal_of_smooth, support_vanishingIdeal_eq, ← hpre] at h2
  obtain ⟨j, hη'j⟩ := (F.mem_support_iff_exists η').mp hη'S.1
  have hgen : η' ∈ (F.component j).support.genericPoints :=
    Closeds.mem_genericPoints_of_le
      (le_iSup (fun i => (F.component i).support) j : (F.component j).support ≤ F.support)
      hη'S hη'j
  have hwj : w ∈ (F.component j).support :=
    hη'w.mem_closed (F.component j).support.isClosed hη'j
  refine ⟨j, hwj, ?_⟩
  rw [stalkIdeal_eq_map_symm_stalkIdeal_comap ι, Hironaka.Smooth.comap_vanishingIdeal_of_smooth,
    preimage_closure_singleton,
    Hironaka.Monomial.stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme (hF.1 j) hgen
      hη'w]

end Local

section Main

variable {Y : Scheme.{u}}

/-- **An snc support is Zariski-local** ([Kol07, Definition 24] is pointwise). If every piece of an
open cover of the Noetherian `Y` carries a simple normal crossing family whose support is the
preimage of `S`, then `Y` carries one with support `S` — the family of the irreducible components of
`S` with their reduced structure (`componentFamily` of the vanishing ideal of `S`): its support is
`S` (`support_componentFamily`), at `x = 𝒰.f i w` its snc data are the local family's coordinates
transported along the stalk isomorphism (`componentFamily_isSncAt_iff`, each minimal prime of the
stalk of `S` being the stalk of a reduced component through `x`,
`exists_stalkIdeal_vanishingIdeal_closure_eq`), and its members are regular because their stalk
quotients are those of the local members. The hypothesis `[NoetherianSpace Y]` is the finiteness the
statement needs (module docstring). -/
theorem exists_snc_of_openCover [NoetherianSpace Y] (S : Set Y) (𝒰 : Y.OpenCover.{v})
    (h : ∀ i, ∃ F : DivisorFamily (𝒰.X i), F.IsSnc ∧ (F.support : Set (𝒰.X i)) = 𝒰.f i ⁻¹' S) :
    ∃ F : DivisorFamily Y, F.IsSnc ∧ (F.support : Set Y) = S := by
  classical
  choose F hF hsupp using h
  have hS : IsClosed S := isClosed_of_openCover 𝒰 S fun i => by
    rw [← hsupp i]
    exact (F i).support.isClosed
  let Z : Closeds Y := ⟨S, hS⟩
  have key : ∀ (i : 𝒰.I₀) (w : 𝒰.X i) {η : Y}, η ∈ Z.genericPoints → η ⤳ 𝒰.f i w →
      ∃ j : (F i).ι, w ∈ ((F i).component j).support ∧
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal (𝒰.f i w) =
          (((F i).component j).stalkIdeal w).map
            (stalkEquivOfIsOpenImmersion (𝒰.f i) w).symm :=
    fun i w _ hη hηw =>
      exists_stalkIdeal_vanishingIdeal_closure_eq (𝒰.f i) Z (hF i) (hsupp i) hη hηw
  refine ⟨(IdealSheafData.vanishingIdeal Z).componentFamily, ⟨fun η => ?_, fun x => ?_⟩, ?_⟩
  · -- the members are regular: their stalk quotients are those of the local members
    refine isRegular_subscheme_of_isRegularLocalRing_quotient _ fun x hx => ?_
    obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq x
    have hηx : η.1 ⤳ 𝒰.f i w := by
      change 𝒰.f i w ∈ (IdealSheafData.vanishingIdeal (Closeds.closure {η.1})).support at hx
      rw [support_vanishingIdeal_eq] at hx
      exact specializes_iff_mem_closure.mpr (Closeds.mem_closure.mp hx)
    have hη : η.1 ∈ Z.genericPoints := by
      have h : η.1 ∈ (IdealSheafData.vanishingIdeal Z).support.genericPoints := η.2
      generalize η.1 = y at h ⊢
      rwa [support_vanishingIdeal_eq] at h
    obtain ⟨j, hwj, heq⟩ := key i w hη hηx
    change IsRegularLocalRing (Y.presheaf.stalk (𝒰.f i w) ⧸
      (IdealSheafData.vanishingIdeal (Closeds.closure {η.1})).stalkIdeal (𝒰.f i w))
    rw [heq]
    obtain ⟨w', rfl⟩ := ((F i).component j).exists_subschemeι_eq hwj
    have hreg : IsRegularLocalRing
        ((𝒰.X i).presheaf.stalk (((F i).component j).subschemeι w') ⧸
          ((F i).component j).stalkIdeal (((F i).component j).subschemeι w')) := by
      have : IsRegularLocalRing (((F i).component j).subscheme.presheaf.stalk w') :=
        ((hF i).1 j).isRegularAt w'
      exact IsRegularLocalRing.of_ringEquiv (((F i).component j).stalkQuotientEquiv w').symm
    refine IsRegularLocalRing.of_ringEquiv
      (Ideal.quotientEquiv
        (Ideal.map (stalkEquivOfIsOpenImmersion (𝒰.f i) (((F i).component j).subschemeι w')).symm
          (((F i).component j).stalkIdeal (((F i).component j).subschemeι w')))
        (((F i).component j).stalkIdeal (((F i).component j).subschemeι w'))
        (stalkEquivOfIsOpenImmersion (𝒰.f i) (((F i).component j).subschemeι w')) ?_).symm
    rw [Ideal.map_symm]
    exact (Ideal.map_comap_of_surjective
      (stalkEquivOfIsOpenImmersion (𝒰.f i) (((F i).component j).subschemeι w') :
        Y.presheaf.stalk (𝒰.f i (((F i).component j).subschemeι w')) →+*
          (𝒰.X i).presheaf.stalk (((F i).component j).subschemeι w'))
      (stalkEquivOfIsOpenImmersion (𝒰.f i) _).surjective _).symm
  · -- snc at `x = 𝒰.f i w`: the local coordinates at `w`, transported
    obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq x
    obtain ⟨n, z, hz⟩ := (hF i).2 w
    refine ⟨n, transportCoords (𝒰.f i) w z, ?_⟩
    rw [componentFamily_isSncAt_iff]
    refine ⟨isRegularSystemOfParameters_comp_ringEquiv
      (stalkEquivOfIsOpenImmersion (𝒰.f i) w).symm hz.1, fun P hP => ?_⟩
    obtain ⟨η, hη, hηx, rfl⟩ := exists_mem_genericPoints_of_mem_minimalPrimes _ hP
    have hη' : η ∈ Z.genericPoints := by
      rwa [support_vanishingIdeal_eq] at hη
    obtain ⟨j, hwj, heq⟩ := key i w hη' hηx
    obtain ⟨-, c, -, hc⟩ := hz
    refine ⟨c ⟨j, hwj⟩, ?_⟩
    have hcj : ((F i).component j).stalkIdeal w = Ideal.span {z (c ⟨j, hwj⟩)} := hc ⟨j, hwj⟩
    rw [heq, hcj, Ideal.map_span, Set.image_singleton]
    rfl
  · -- the support is `S`
    rw [support_componentFamily, support_vanishingIdeal_eq]
    rfl

end Main

end Hironaka.Snc
