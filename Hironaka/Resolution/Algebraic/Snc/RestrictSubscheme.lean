/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Resolution.Algebraic.Kol07.RefineFamily
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.GraphCompletion
import Hironaka.Scheme.Snc.EraseFamily
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The restriction of an snc family to a smooth subscheme it has simple normal crossings with

[Kol07, Definition 24], the last sentence: "If `E` does not contain `Z`, then `E|_Z` is again a
simple normal crossing divisor on `Z`." `hasSncWith_comap_of_isClosedImmersion` of
`Hironaka.Scheme.Snc.RestrictHypersurface` is the case of a smooth divisor `H` that is itself a
member of the family; `isSnc_restrictedFamily` of
`Hironaka.Resolution.Algebraic.BoundaryClearing.Restriction` restricts `E − E^j` to `E^j`. Clause
(3) of [Kol07, Theorem 36] for the affine resolution
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular`; the proof of [Kol07, Theorem 27]:
"`g⁻¹(Sing X̄) = Z_j ∩ Ex_tot(π_0 ⋯ π_{j−1})` is a simple normal crossing divisor on `Z_j`") needs
the general case: the total exceptional divisor `Ex_tot(π_0 ⋯ π_{j−1})` has simple normal crossings
with the smooth centre `Z_j` (Theorem 35 (1)) and no component of it contains the strict transform
`X̄_j = Z_j^η`, so its restriction to `X̄_j` — a subscheme of codimension `≥ 2` in general — is snc.
In snc coordinates `z` at a point `x ∈ Z` with `Z_x = (z_l : l ∈ s)`, the images of the `z_j`, `j ∉
s`, are a regular system of parameters of `𝒪_{Z,x} = 𝒪_{X,x}/(z_s)`
(`Hironaka.Scheme.Snc.ParameterSubset`, through the surjective stalk map of the closed immersion),
and every component `E^i = (z_{c(i)})` through `x` has `c(i) ∉ s` exactly when `E^i` does not
contain `Z` near `x` (`span_singleton_le_span_image_iff`).

* `isSncAt_comap_of_hasSncWith`: the pointwise statement at every point of `Z = V(ker g)`.
* `isSnc_comap_of_hasSncWith`: `E|_Z` is snc when `Z` is smooth over `k`.
* `stalkIdeal_eq_of_isOpenImmersion_inclusion`, `HasSncWith.of_isOpenImmersion_inclusion`: when
  `V(T) ⊆ V(Z)` is an open subscheme (the identification of the strict transform `X̄_j` with the
  component `Z_j^η` of the centre through the generic point), the two ideals have the same stalks
  along `V(T)`, so `E` has snc with `T` as soon as it has snc with `Z`.
* `not_stalkIdeal_le_of_isGenericPoint_notMem`: the hypothesis `hnot` from the generic point — a
  component `D` whose stalk at `x ∈ V(T)` is contained in that of `T` contains `V(T)` near `x`,
  hence contains the generic point of the irreducible `V(T)` (`stalkIdeal_specializes` of
  `Hironaka.Scheme.IdealSheaf.Order.Constructible`).

Sources: [Kol07, Definition 24; Theorem 27 (the proof); Theorem 36].
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme TopologicalSpace

namespace Hironaka.Snc

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The last sentence of [Kol07, Definition 24], pointwise: for a closed immersion `g : Y ⟶ X` with
image `Z = V(ker g)` having simple normal crossings with `E`, such that no component of `E` contains
`Z` near any point of `Z` (`hnot`, stalkwise), the family `E|_Z = E.comap g` has snc coordinates at
every point of `Y`: the images of the snc coordinates of `X` not among those cutting out `Z`. -/
theorem isSncAt_comap_of_hasSncWith (g : Y ⟶ X) [IsClosedImmersion g]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {E : DivisorFamily X}
    (hZ : E.HasSncWith g.ker)
    (hnot : ∀ (i : E.ι) (x : X), x ∈ g.ker.support → x ∈ (E.component i).support →
      ¬ (E.component i).stalkIdeal x ≤ g.ker.stalkIdeal x) (y : Y) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y), (E.comap g).IsSncAt y z := by
  classical
  have hy : g y ∈ g.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq]
    exact ⟨y, rfl⟩
  have := hreg (g y)
  obtain ⟨n, z, ⟨⟨hzspan, hzdim⟩, c, hcinj, hc⟩, s, hs⟩ := hZ (g y) hy
  have hs' : g.ker.stalkIdeal (g y) = span (z '' ↑s) := hs
  have hc' : ∀ i : {i : E.ι // g y ∈ (E.component i).support},
      (E.component i.1).stalkIdeal (g y) = span {z (c i)} := hc
  -- the stalk map: surjective with kernel `(z_l : l ∈ s)`
  set φ : X.presheaf.stalk (g y) →+* Y.presheaf.stalk y := (g.stalkMap y).hom with hφdef
  have hφ : Function.Surjective φ := g.stalkMap_surjective y
  have hkerφ : RingHom.ker φ = span (z '' ↑s) := by
    rw [hφdef, ker_stalkMap_of_isClosedImmersion, hs']
  -- the coordinates of `Y` at `y`: the images of the `z_j`, `j ∉ s`
  set z' : Fin sᶜ.card → Y.presheaf.stalk y := φ ∘ z ∘ sᶜ.orderEmbOfFin rfl with hz'
  have hz'span : span (Set.range z') = maximalIdeal (Y.presheaf.stalk y) :=
    span_range_comp_compl_eq_maximalIdeal hzspan.symm hφ hkerφ
  have hz'dim : ((sᶜ.card : ℕ) : WithBot ℕ∞) = ringKrullDim (Y.presheaf.stalk y) := by
    rw [Finset.card_compl, Fintype.card_fin]
    exact natCast_sub_card_eq_ringKrullDim_of_ker hzspan.symm hzdim hφ hkerφ
  -- the components of `E` through `y` are the components of `E` through `g y`
  have hEy : ∀ i : {i : E.ι // y ∈ ((E.comap g).component i).support},
      g y ∈ (E.component i.1).support := fun i => by
    have hi := i.2
    rwa [show (E.comap g).component i.1 = (E.component i.1).comap g from rfl,
      Scheme.IdealSheafData.support_comap] at hi
  -- none of them is cut out by a coordinate of `Z`
  have hno : ∀ i : {i : E.ι // y ∈ ((E.comap g).component i).support},
      c ⟨i.1, hEy i⟩ ∉ s := fun i hmem => by
    apply hnot i.1 (g y) hy (hEy i)
    rw [hc' ⟨i.1, hEy i⟩, hs']
    exact (span_singleton_le_span_image_iff hzspan.symm hzdim s _).2 hmem
  refine ⟨_, z', ⟨hz'span, hz'dim⟩, fun i => complIndex (hno i), ?_, fun i => ?_⟩
  · intro i i' hii'
    have h' := congrArg (sᶜ.orderEmbOfFin rfl) hii'
    simp only [orderEmbOfFin_complIndex] at h'
    have h'' : (⟨i.1, hEy i⟩ : {j : E.ι // g y ∈ (E.component j).support}) = ⟨i'.1, hEy i'⟩ :=
      hcinj h'
    injection h'' with hval
    exact Subtype.ext hval
  · change ((E.component i.1).comap g).stalkIdeal y = span {z' (complIndex (hno i))}
    rw [Scheme.IdealSheafData.stalkIdeal_comap, hc' ⟨i.1, hEy i⟩, Ideal.map_span,
      Set.image_singleton, hz']
    simp only [Function.comp_apply, orderEmbOfFin_complIndex]
    rfl

/-- The last sentence of [Kol07, Definition 24]: for a closed immersion `g : Y ⟶ X` with `Y` smooth
over `k` and image `Z = V(ker g)` having simple normal crossings with `E`, if no component of `E`
contains `Z` near any of its points, then `E|_Z = E.comap g` is a simple normal crossing family on
`Y`. -/
theorem isSnc_comap_of_hasSncWith {k : Type u} [Field k] (f : Y ⟶ Spec (.of k)) [Smooth f]
    (g : Y ⟶ X) [IsClosedImmersion g] (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    {E : DivisorFamily X} (hZ : E.HasSncWith g.ker)
    (hnot : ∀ (i : E.ι) (x : X), x ∈ g.ker.support → x ∈ (E.component i).support →
      ¬ (E.component i).stalkIdeal x ≤ g.ker.stalkIdeal x) :
    (E.comap g).IsSnc := by
  have hat : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y), (E.comap g).IsSncAt y z :=
    isSncAt_comap_of_hasSncWith g hreg hZ hnot
  exact ⟨fun i => HasSncWith.isRegular f (DivisorFamily.hasSncWith_component _ hat i), hat⟩

/-! ### Transport along the identification `X̄_j = Z_j^η` -/

/-- Along an open-immersion inclusion `V(T) ⊆ V(Z)` of closed subschemes, the ideals `Z ≤ T` have
the same stalk at every point of `V(T)`: the stalk map of `T.subschemeι = inclusion ≫ Z.subschemeι`
factors through the isomorphism of stalks of the open immersion, so its kernel `T_x`
(`ker_stalkMap_of_isClosedImmersion`) is the kernel `Z_x` of the stalk map of `Z.subschemeι`. -/
theorem stalkIdeal_eq_of_isOpenImmersion_inclusion {Z T : X.IdealSheafData} (hle : Z ≤ T)
    [IsOpenImmersion (Scheme.IdealSheafData.inclusion hle)] {x : X} (hx : x ∈ T.support) :
    Z.stalkIdeal x = T.stalkIdeal x := by
  obtain ⟨x', rfl⟩ : x ∈ Set.range T.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  refine le_antisymm (Scheme.IdealSheafData.stalkIdeal_mono hle _) fun a ha => ?_
  have hcomp : T.subschemeι = Scheme.IdealSheafData.inclusion hle ≫ Z.subschemeι :=
    (Scheme.IdealSheafData.inclusion_subschemeι hle).symm
  have hpt : T.subschemeι x' = Z.subschemeι (Scheme.IdealSheafData.inclusion hle x') := by
    rw [hcomp]
    exact Scheme.Hom.comp_apply _ _ _
  have ha' : (T.subschemeι.stalkMap x').hom a = 0 := by
    rw [← RingHom.mem_ker, ker_stalkMap_of_isClosedImmersion,
      Scheme.IdealSheafData.ker_subschemeι]
    exact ha
  rw [Scheme.Hom.stalkMap_congr_hom _ _ hcomp x', Scheme.Hom.stalkMap_comp] at ha'
  have ha'' : ((Scheme.IdealSheafData.inclusion hle).stalkMap x').hom
      ((Z.subschemeι.stalkMap (Scheme.IdealSheafData.inclusion hle x')).hom
        ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom a)) = 0 := ha'
  have hinj : Function.Injective ((Scheme.IdealSheafData.inclusion hle).stalkMap x').hom :=
    (asIso ((Scheme.IdealSheafData.inclusion hle).stalkMap x')).commRingCatIsoToRingEquiv.injective
  have h0 : (Z.subschemeι.stalkMap (Scheme.IdealSheafData.inclusion hle x')).hom
      ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom a) = 0 :=
    hinj (by rw [ha'', map_zero])
  have hkerZ : RingHom.ker (Z.subschemeι.stalkMap (Scheme.IdealSheafData.inclusion hle x')).hom =
      Z.stalkIdeal (Z.subschemeι (Scheme.IdealSheafData.inclusion hle x')) := by
    rw [ker_stalkMap_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
  have hmem : (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom a ∈
      Z.stalkIdeal (Z.subschemeι (Scheme.IdealSheafData.inclusion hle x')) := by
    rw [← hkerZ]
    exact RingHom.mem_ker.2 h0
  have key : (Z.stalkIdeal (T.subschemeι x')).map
      (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom =
      Z.stalkIdeal (Z.subschemeι (Scheme.IdealSheafData.inclusion hle x')) :=
    stalkIdeal_map_stalkCongr Z hpt
  rw [← key] at hmem
  have hbij : Function.Bijective (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom :=
    (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).commRingCatIsoToRingEquiv.bijective
  rw [← Ideal.comap_map_of_bijective _ hbij (I := Z.stalkIdeal (T.subschemeι x'))]
  exact hmem

/-- The proof of [Kol07, Theorem 27] read on the identification `X̄_j = Z_j^η`: if `E` has simple
normal crossings with `Z` and `V(T) ⊆ V(Z)` is an open subscheme (`Z ≤ T`, the inclusion an open
immersion), then `E` has simple normal crossings with `T` — the snc coordinates at a point of `V(T)`
cut out `V(Z)`, which is `V(T)` there. -/
theorem HasSncWith.of_isOpenImmersion_inclusion {E : DivisorFamily X} {Z T : X.IdealSheafData}
    (hE : E.HasSncWith Z) (hle : Z ≤ T)
    [IsOpenImmersion (Scheme.IdealSheafData.inclusion hle)] : E.HasSncWith T := by
  intro x hx
  obtain ⟨n, z, hz, s, hs⟩ := hE x (Scheme.IdealSheafData.support_antitone hle hx)
  refine ⟨n, z, hz, s, ?_⟩
  rw [← stalkIdeal_eq_of_isOpenImmersion_inclusion hle hx]
  exact hs

/-- The hypothesis `hnot` of `isSncAt_comap_of_hasSncWith` from a generalisation: if a point
`η ∈ V(T)` generalises `x` and `η ∉ V(D)`, then `D_x ⊄ T_x` — otherwise
`D_η = D_x 𝒪_η ⊆ T_x 𝒪_η = T_η ≠ (1)` (`stalkIdeal_specializes`), i.e. `η ∈ V(D)`. For a reducible
`V(T)`, `η` is the generic point of an irreducible component of `V(T)` through `x`. -/
theorem not_stalkIdeal_le_of_specializes_notMem (T D : X.IdealSheafData) {η x : X} (hspec : η ⤳ x)
    (hηT : η ∈ T.support) (hηD : η ∉ D.support) : ¬ D.stalkIdeal x ≤ T.stalkIdeal x := by
  intro hle
  have h1 : D.stalkIdeal η = ⊤ := Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support D hηD
  rw [D.stalkIdeal_specializes hspec] at h1
  have h2 : T.stalkIdeal η = ⊤ := by
    rw [T.stalkIdeal_specializes hspec, eq_top_iff, ← h1]
    exact Ideal.map_mono hle
  exact Hironaka.Sequence.notMem_support_of_stalkIdeal_eq_top h2 hηT

/-- The hypothesis `hnot` of `isSncAt_comap_of_hasSncWith` from the generic point: if `V(T)` is
irreducible with generic point `η ∉ V(D)`, then at no point `x ∈ V(T)` is `D_x ⊆ T_x`
(`not_stalkIdeal_le_of_specializes_notMem` at the generalisation `η ⤳ x`). -/
theorem not_stalkIdeal_le_of_isGenericPoint_notMem (T D : X.IdealSheafData) {η x : X}
    (hη : IsGenericPoint η (T.support : Set X)) (hx : x ∈ T.support) (hηD : η ∉ D.support) :
    ¬ D.stalkIdeal x ≤ T.stalkIdeal x :=
  not_stalkIdeal_le_of_specializes_notMem T D (hη.specializes hx) hη.mem hηD

end Hironaka.Snc
