/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.ParameterSubset
public import Hironaka.Scheme.Snc.SmoothDivisor
public import Hironaka.Scheme.Snc.Defs
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.SubschemeStalk
import Mathlib.AlgebraicGeometry.Morphisms.Proper
/-!
# `Z` has simple normal crossings with `E`: the consequences

[Kol07, Definition 24 (4)]: a closed subscheme `Z ⊆ X` has simple normal crossings with the divisor
`E = ∑ E^i` if at every `x ∈ Z` there are local coordinates `z_1, …, z_n ∈ 𝔪_x` (a regular system of
parameters of `𝒪_{X,x}`) with every component through `x` of the form `E^i = (z_{c(i)} = 0)`, `c`
injective, and `Z = (z_j = 0 : j ∈ s)` for a set `s` of indices. The consequences Kollár draws — "in
particular, `Z` is smooth", some `E^i` may contain `Z`, and if none does then "`E|_Z` is again a
simple normal crossing divisor on `Z`" — are all local at a point `w` of `V(Z)` over `x = ι w`,
where `ι : V(Z) ⟶ X` is the closed immersion and the stalk map `φ = ι^♯_w : 𝒪_{X,x} → 𝒪_{Z,w}` is
surjective with kernel `I_{Z,x} = (z_j : j ∈ s)` (`ker_stalkMap_subschemeι`). Everything is then the
ring-level statement of `Hironaka.Scheme.Snc.ParameterSubset` for this `φ`:

* "`Z` is smooth": `𝒪_{Z,w}` is regular, of dimension `n − |s|`
  (`isRegularLocalRing_stalk_subscheme`, `natCast_card_compl_eq_ringKrullDim_stalk_subscheme`);
* containment: `E^i = (z_j = 0)` contains `Z` near `x` (`(E^i)_x ⊆ I_{Z,x}`) iff `j ∈ s`
  (`stalkIdeal_le_stalkIdeal_iff_mem`);
* transversality: for `j ∉ s` the image `φ z_j` generates the stalk of `E^i ∩ Z = (E^i).comap ι` at
  `w`, lies in `𝔪_w ∖ 𝔪_w²`, and `𝒪_{Z,w}/(φ z_j) = 𝒪_{X,x}/(z_l : l ∈ s ∪ {j})` is regular
  (`stalkIdeal_comap_subschemeι_eq_span`, `stalkMap_notMem_maximalIdeal_sq`,
  `isRegularLocalRing_quotient_stalkIdeal_comap`); a closed subscheme all of whose stalk quotients
  are regular is regular (`isRegular_subscheme_of_isRegularLocalRing_quotient`);
* restriction: when no component through `x` contains `Z`, the images of the `z_l`, `l ∉ s`, are a
  regular system of parameters of `𝒪_{Z,w}` and the snc data `c` restrict to the family
  `(E^i).comap ι` (`span_range_stalkMap_comp_eq_maximalIdeal`, `exists_snc_data_comap`).

In the sections at a point and on the subscheme, as in `Hironaka.Scheme.Snc.Family`, the snc data
are explicit hypotheses. The last section states the consequences for the predicates
`DivisorFamily.IsSncAt` and `HasSncWith` on a scheme smooth over `k`: `hasSncWith_iff`,
`IsSncAt.stalkIdeal_le_iff_mem`, `HasSncWith.isRegularLocalRing_quotient_stalkIdeal`,
`HasSncWith.isRegular`, `HasSncWith.smooth`, `IsSncAt.exists_generator_stalkIdeal_comap_of_notMem`,
`HasSncWith.isSmoothDivisor_comap`, `IsSncAt.exists_isSncAt_comap`, `HasSncWith.isSnc_comap`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Every point of `V(D)` lies over a point of the support of `D`. -/
theorem subschemeι_mem_support {Y : Scheme.{u}} (D : Y.IdealSheafData) (v : D.subscheme) :
    D.subschemeι v ∈ D.support := by
  have hv : D.subschemeι v ∈ Set.range D.subschemeι := Set.mem_range_self v
  rwa [D.range_subschemeι] at hv

/-- A closed subscheme `V(D)` is regular as soon as every stalk quotient `𝒪_{Y,w}/D_w`, `w ∈ V(D)`,
is regular — `𝒪_{V(D),v} ≅ 𝒪_{Y,ι v}/D_{ι v}` (`stalkQuotientEquiv`). -/
theorem isRegular_subscheme_of_isRegularLocalRing_quotient {Y : Scheme.{u}}
    (D : Y.IdealSheafData)
    (h : ∀ w ∈ D.support, IsRegularLocalRing (Y.presheaf.stalk w ⧸ D.stalkIdeal w)) :
    IsRegular D.subscheme := ⟨fun v =>
  have := h (D.subschemeι v) (subschemeι_mem_support D v)
  IsRegularLocalRing.of_ringEquiv (D.stalkQuotientEquiv v)⟩

/-! ### At a point `x` of `X` -/

section Point

variable {x : X} {n : ℕ} {z : Fin n → X.presheaf.stalk x} {s : Finset (Fin n)}
  {Z D : X.IdealSheafData}

variable [IsRegularLocalRing (X.presheaf.stalk x)]

/-- A component `E^i = (z_j = 0)` through `x` contains `Z` near `x` iff `j` is one of the
coordinates of `Z`. -/
theorem stalkIdeal_le_stalkIdeal_iff_mem
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hZ : Z.stalkIdeal x = span (z '' ↑s)) {j : Fin n} (hD : D.stalkIdeal x = span {z j}) :
    D.stalkIdeal x ≤ Z.stalkIdeal x ↔ j ∈ s := by
  rw [hD, hZ]
  exact span_singleton_le_span_image_iff hz.1.symm hz.2 s j

theorem notMem_of_not_stalkIdeal_le
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hZ : Z.stalkIdeal x = span (z '' ↑s)) {j : Fin n} (hD : D.stalkIdeal x = span {z j})
    (hle : ¬ D.stalkIdeal x ≤ Z.stalkIdeal x) : j ∉ s :=
  fun hj => hle ((stalkIdeal_le_stalkIdeal_iff_mem hz hZ hD).mpr hj)

/-- `𝒪_{X,x}/I_{Z,x}` is regular (Kollár's "in particular, `Z` is smooth"). -/
theorem isRegularLocalRing_quotient_stalkIdeal_of_eq_span
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hZ : Z.stalkIdeal x = span (z '' ↑s)) :
    IsRegularLocalRing (X.presheaf.stalk x ⧸ Z.stalkIdeal x) := by
  rw [hZ]
  exact isRegularLocalRing_quotient_span_image_finset hz.1.symm hz.2 s

end Point

/-! ### At a point `w` of `V(Z)` over `x = ι w` -/

section Subscheme

variable (Z : X.IdealSheafData) (w : Z.subscheme) {n : ℕ}
  {z : Fin n → X.presheaf.stalk (Z.subschemeι w)} {s : Finset (Fin n)}

theorem mem_support_comap_iff (D : X.IdealSheafData) :
    w ∈ (D.comap Z.subschemeι).support ↔ Z.subschemeι w ∈ D.support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

theorem ker_stalkMap_eq_of_stalkIdeal_eq (hZ : Z.stalkIdeal (Z.subschemeι w) = span (z '' ↑s)) :
    RingHom.ker (Z.subschemeι.stalkMap w).hom = span (z '' ↑s) := by
  rw [Z.ker_stalkMap_subschemeι w, hZ]

/-- The stalk at `w` of the restriction `D ∩ Z = D.comap ι` is generated by the image of a generator
of `D_x`. -/
theorem stalkIdeal_comap_subschemeι_eq_span (D : X.IdealSheafData)
    {a : X.presheaf.stalk (Z.subschemeι w)} (hD : D.stalkIdeal (Z.subschemeι w) = span {a}) :
    (D.comap Z.subschemeι).stalkIdeal w = span {(Z.subschemeι.stalkMap w).hom a} := by
  rw [Scheme.IdealSheafData.stalkIdeal_comap, hD, Ideal.map_span, Set.image_singleton]

/-- When no component through `x = ι w` contains `Z`, the snc data `c` of `E` at `x` restrict to snc
data of the family `E^i ∩ Z = (E^i).comap ι` at `w`, with coordinates the images of the `z_l`,
`l ∉ s`, enumerated by `sᶜ.orderEmbOfFin` (Kollár's "`E|_Z` is again a simple normal crossing
divisor on `Z`"). -/
theorem exists_snc_data_comap {ι : Type*} (E : ι → X.IdealSheafData)
    (c : {i : ι // Z.subschemeι w ∈ (E i).support} → Fin n) (hcinj : Function.Injective c)
    (hc : ∀ i, (E i.1).stalkIdeal (Z.subschemeι w) = span {z (c i)}) (hno : ∀ i, c i ∉ s) :
    ∃ c' : {i : ι // w ∈ ((E i).comap Z.subschemeι).support} → Fin sᶜ.card,
      Function.Injective c' ∧ ∀ i, ((E i.1).comap Z.subschemeι).stalkIdeal w =
        span {((Z.subschemeι.stalkMap w).hom ∘ z ∘ sᶜ.orderEmbOfFin rfl) (c' i)} := by
  have hi : ∀ i : {i : ι // w ∈ ((E i).comap Z.subschemeι).support},
      Z.subschemeι w ∈ (E i.1).support :=
    fun i => (mem_support_comap_iff Z w (E i.1)).mp i.2
  refine ⟨fun i => complIndex (hno ⟨i.1, hi i⟩), ?_, fun i => ?_⟩
  · intro i i' h
    have h' := congrArg (sᶜ.orderEmbOfFin rfl) h
    simp only [orderEmbOfFin_complIndex] at h'
    exact Subtype.ext (Subtype.mk.inj (hcinj h'))
  · simp only [Function.comp_apply, orderEmbOfFin_complIndex]
    exact stalkIdeal_comap_subschemeι_eq_span Z w (E i.1) (hc ⟨i.1, hi i⟩)

variable [IsRegularLocalRing (X.presheaf.stalk (Z.subschemeι w))]

/-- `𝒪_{Z,w} = 𝒪_{X,x}/(z_j : j ∈ s)` is a regular local ring (Kollár's "`Z` is smooth"). -/
theorem isRegularLocalRing_stalk_subscheme
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (Z.subschemeι w)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.subschemeι w)))
    (hZ : Z.stalkIdeal (Z.subschemeι w) = span (z '' ↑s)) :
    IsRegularLocalRing (Z.subscheme.presheaf.stalk w) :=
  isRegularLocalRing_of_ker_eq_span_image (φ := (Z.subschemeι.stalkMap w).hom) hz.1.symm hz.2
    (Z.subschemeι.stalkMap_surjective w) (ker_stalkMap_eq_of_stalkIdeal_eq Z w hZ)

/-- `dim 𝒪_{Z,w} = n − |s|`. -/
theorem natCast_sub_card_eq_ringKrullDim_stalk_subscheme
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (Z.subschemeι w)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.subschemeι w)))
    (hZ : Z.stalkIdeal (Z.subschemeι w) = span (z '' ↑s)) :
    ((n - s.card : ℕ) : WithBot ℕ∞) = ringKrullDim (Z.subscheme.presheaf.stalk w) :=
  natCast_sub_card_eq_ringKrullDim_of_ker (φ := (Z.subschemeι.stalkMap w).hom) hz.1.symm hz.2
    (Z.subschemeι.stalkMap_surjective w) (ker_stalkMap_eq_of_stalkIdeal_eq Z w hZ)

/-- `dim 𝒪_{Z,w} = |sᶜ|`, the number of remaining coordinates. -/
theorem natCast_card_compl_eq_ringKrullDim_stalk_subscheme
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (Z.subschemeι w)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.subschemeι w)))
    (hZ : Z.stalkIdeal (Z.subschemeι w) = span (z '' ↑s)) :
    ((sᶜ.card : ℕ) : WithBot ℕ∞) = ringKrullDim (Z.subscheme.presheaf.stalk w) := by
  rw [Finset.card_compl, Fintype.card_fin]
  exact natCast_sub_card_eq_ringKrullDim_stalk_subscheme Z w hz hZ

/-- The images of the coordinates `z_l`, `l ∉ s`, generate `𝔪_w`. -/
theorem span_range_stalkMap_comp_eq_maximalIdeal
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (Z.subschemeι w)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.subschemeι w)))
    (hZ : Z.stalkIdeal (Z.subschemeι w) = span (z '' ↑s)) :
    span (Set.range ((Z.subschemeι.stalkMap w).hom ∘ z ∘ sᶜ.orderEmbOfFin rfl)) =
      maximalIdeal (Z.subscheme.presheaf.stalk w) :=
  span_range_comp_compl_eq_maximalIdeal hz.1.symm (Z.subschemeι.stalkMap_surjective w)
    (ker_stalkMap_eq_of_stalkIdeal_eq Z w hZ)

theorem stalkMap_mem_maximalIdeal
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (Z.subschemeι w)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.subschemeι w))) (j : Fin n) :
    (Z.subschemeι.stalkMap w).hom (z j) ∈ maximalIdeal (Z.subscheme.presheaf.stalk w) :=
  apply_mem_maximalIdeal hz.1.symm (Z.subschemeι.stalkMap_surjective w) j

/-- For `j ∉ s`, the image of `z_j` in `𝒪_{Z,w}` lies outside `𝔪_w²` — `E^i ∩ Z = (z_j = 0)` is a
smooth divisor of `Z` at `w`. -/
theorem stalkMap_notMem_maximalIdeal_sq
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (Z.subschemeι w)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.subschemeι w)))
    (hZ : Z.stalkIdeal (Z.subschemeι w) = span (z '' ↑s)) {j : Fin n} (hj : j ∉ s) :
    (Z.subschemeι.stalkMap w).hom (z j) ∉ maximalIdeal (Z.subscheme.presheaf.stalk w) ^ 2 :=
  apply_notMem_maximalIdeal_sq hz.1.symm hz.2 (Z.subschemeι.stalkMap_surjective w)
    (ker_stalkMap_eq_of_stalkIdeal_eq Z w hZ) hj

/-- `𝒪_{Z,w}/(E^i ∩ Z)_w = 𝒪_{X,x}/(z_l : l ∈ s ∪ {j})` is regular. -/
theorem isRegularLocalRing_quotient_stalkIdeal_comap
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (Z.subschemeι w)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.subschemeι w)))
    (hZ : Z.stalkIdeal (Z.subschemeι w) = span (z '' ↑s)) (D : X.IdealSheafData) {j : Fin n}
    (hD : D.stalkIdeal (Z.subschemeι w) = span {z j}) :
    IsRegularLocalRing (Z.subscheme.presheaf.stalk w ⧸ (D.comap Z.subschemeι).stalkIdeal w) := by
  rw [stalkIdeal_comap_subschemeι_eq_span Z w D hD]
  exact isRegularLocalRing_quotient_span_singleton_apply hz.1.symm hz.2
    (Z.subschemeι.stalkMap_surjective w) (ker_stalkMap_eq_of_stalkIdeal_eq Z w hZ) j

end Subscheme

end AlgebraicGeometry

/-! ### The predicates `IsSncAt` and `HasSncWith` on a scheme smooth over `k`

[Kol07, Definition 24 (4)] asks, at each point `x` of the closed subscheme `Z`, for local
coordinates `z_1, …, z_n` as in (1)–(3) — a regular system of parameters of `𝒪_{X,x}` with each
component `E^i` through `x` equal to `(z_{c(i)} = 0)` — such that moreover `Z = (z_j = 0 : j ∈ s)`
near `x`. The predicate `HasSncWith` says exactly this (`hasSncWith_iff` is `Iff.rfl`). On `X`
smooth over `k` every stalk is a regular local ring (`AlgebraicGeometry.isRegularLocalRing_stalk`),
so Kollár's consequences are the ring-level statements of the two sections above:

* **`Z` is smooth.** `𝒪_{Z,x} = 𝒪_{X,x}/(z_j : j ∈ s)` is the quotient of a regular local ring by
  part of a regular system of parameters, hence regular (after moving the `z_j`, `j ∈ s`, to the
  front: `Hironaka.Scheme.Snc.ParameterSubset`). A point `w` of `V(Z)` lies over `x = ι w ∈ Z`, and
  `𝒪_{Z,w}` is that quotient through the surjective stalk map of the closed immersion `ι` (kernel
  `I_{Z,x}`); so `V(Z)` is regular and, over the perfect field `k`, smooth. The regular quotient
  `𝒪_{X,x}/I_{Z,x}` at `x` is stated separately.
* **Containment.** `E^i = (z_j = 0)` contains `Z` near `x`, that is `(z_j) ⊆ (z_l : l ∈ s)`, iff
  `j ∈ s`: the classes of `z_1, …, z_n` are a basis of `𝔪_x/𝔪_x²`, so `z_j` is a combination of the
  `z_l`, `l ∈ s`, only when it is one of them.
* **Transversal components.** If `j ∉ s`, the restriction `E^i ∩ Z = (E^i).comap ι` has at `w` the
  stalk `(φ z_j)` (`stalkIdeal_comap`), `φ z_j ∈ 𝔪_w ∖ 𝔪_w²` (again the basis of `𝔪_x/𝔪_x²`:
  `z_j ∉ 𝔪_x² + (z_l : l ∈ s)`), and `𝒪_{Z,w}/(φ z_j) = 𝒪_{X,x}/(z_l : l ∈ s ∪ {j})` is regular.
  When `E^i` contains `Z` near no point of `Z ∩ E^i`, this makes `E^i ∩ Z` a smooth divisor of
  `V(Z)`: its closed subscheme is regular because all its stalk quotients are.
* **Restriction.** If no component through `x` contains `Z`, the images of the `z_l`, `l ∉ s`, are a
  regular system of parameters of `𝒪_{Z,w}` (they generate `𝔪_w = φ(𝔪_x)`, and
  `dim 𝒪_{Z,w} = n − |s|` is their number), and the assignment `c` restricts: each component
  `E^i ∩ Z` through `w` is `(φ z_{c(i)} = 0)` with `c(i) ∉ s`, injectively. Hence `E|_Z` is again a
  simple normal crossing divisor on `V(Z)`.

The namespace is reopened so that the section variables are bound in the order `{k} [Field k] {X}`.
-/

namespace AlgebraicGeometry

section Smooth

open Scheme DivisorFamily

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- [Kol07, Definition 24 (4)] unfolded: `Z` has simple normal crossings with `E` iff at every
`x ∈ Z` there are local coordinates satisfying (1)–(3) and an index set `s` with
`I_{Z,x} = (z_j : j ∈ s)`. -/
theorem hasSncWith_iff (E : DivisorFamily X) (Z : X.IdealSheafData) :
    E.HasSncWith Z ↔ ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      E.IsSncAt x z ∧ ∃ s : Finset (Fin n), Z.stalkIdeal x = Ideal.span (z '' ↑s) :=
  Iff.rfl

/-- Under (4), a component `E^i = (z_j = 0)` through `x` contains `Z` near `x` iff `j` is one of the
coordinates of `Z` — `z_j ∈ (z_l : l ∈ s)` iff `j ∈ s`, the classes of the coordinates being a basis
of `𝔪_x/𝔪_x²`. -/
theorem IsSncAt.stalkIdeal_le_iff_mem (f : X ⟶ Spec (.of k)) [Smooth f] {E : DivisorFamily X}
    {x : X} {n : ℕ} {z : Fin n → X.presheaf.stalk x} (h : E.IsSncAt x z) {Z : X.IdealSheafData}
    {s : Finset (Fin n)} (hZ : Z.stalkIdeal x = Ideal.span (z '' ↑s)) {i : E.ι} {j : Fin n}
    (hij : (E.component i).stalkIdeal x = Ideal.span {z j}) :
    (E.component i).stalkIdeal x ≤ Z.stalkIdeal x ↔ j ∈ s :=
  have := isRegularLocalRing_stalk f x
  stalkIdeal_le_stalkIdeal_iff_mem h.1 hZ hij

/-- At `x ∈ Z`, the stalk `𝒪_{Z,x} = 𝒪_{X,x}/I_{Z,x}` is a regular local ring — the quotient of a
regular local ring by part of a regular system of parameters. -/
theorem HasSncWith.isRegularLocalRing_quotient_stalkIdeal (f : X ⟶ Spec (.of k)) [Smooth f]
    {E : DivisorFamily X} {Z : X.IdealSheafData} (h : E.HasSncWith Z) {x : X}
    (hx : x ∈ Z.support) : IsRegularLocalRing (X.presheaf.stalk x ⧸ Z.stalkIdeal x) :=
  have := isRegularLocalRing_stalk f x
  let ⟨_n, _z, hsnc, _s, hZ⟩ := h x hx
  isRegularLocalRing_quotient_stalkIdeal_of_eq_span hsnc.1 hZ

/-- `V(Z)` is regular. -/
theorem HasSncWith.isRegular (f : X ⟶ Spec (.of k)) [Smooth f] {E : DivisorFamily X}
    {Z : X.IdealSheafData} (h : E.HasSncWith Z) : IsRegular Z.subscheme := ⟨fun w =>
  have := isRegularLocalRing_stalk f (Z.subschemeι w)
  let ⟨_n, _z, hsnc, _s, hZ⟩ := h _ (subschemeι_mem_support Z w)
  isRegularLocalRing_stalk_subscheme Z w hsnc.1 hZ⟩

/-- `V(Z)` is smooth over the perfect field `k` (Kollár's "in particular, `Z` is smooth"). -/
theorem HasSncWith.smooth [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]
    {E : DivisorFamily X} {Z : X.IdealSheafData} (h : E.HasSncWith Z) :
    Smooth (Z.subschemeι ≫ f) :=
  (Scheme.smooth_iff_isRegular (Z.subschemeι ≫ f)).mpr (HasSncWith.isRegular f h)

/-- The transversal case at a point `w` of `V(Z)` over `x = ι w`: for a component `E^i = (z_j = 0)`
through `x` with `j ∉ s`, the restriction `E^i ∩ Z` (the inverse image `(E^i).comap ι`) has at `w` a
stalk generated by the image of `z_j`, an element of `𝔪_w ∖ 𝔪_w²`, with regular quotient —
`E^i ∩ Z = (z_j = 0) ⊆ Z` is a smooth divisor of `Z` at `w`. -/
theorem IsSncAt.exists_generator_stalkIdeal_comap_of_notMem (f : X ⟶ Spec (.of k)) [Smooth f]
    {E : DivisorFamily X} {Z : X.IdealSheafData} {w : Z.subscheme} {n : ℕ}
    {z : Fin n → X.presheaf.stalk (Z.subschemeι w)} (h : E.IsSncAt (Z.subschemeι w) z)
    {s : Finset (Fin n)} (hZ : Z.stalkIdeal (Z.subschemeι w) = Ideal.span (z '' ↑s)) {i : E.ι}
    {j : Fin n} (hij : (E.component i).stalkIdeal (Z.subschemeι w) = Ideal.span {z j})
    (hj : j ∉ s) :
    ∃ a : Z.subscheme.presheaf.stalk w, a ∈ maximalIdeal (Z.subscheme.presheaf.stalk w) ∧
      a ∉ maximalIdeal (Z.subscheme.presheaf.stalk w) ^ 2 ∧
      ((E.component i).comap Z.subschemeι).stalkIdeal w = Ideal.span {a} ∧
      IsRegularLocalRing (Z.subscheme.presheaf.stalk w ⧸
        ((E.component i).comap Z.subschemeι).stalkIdeal w) :=
  have := isRegularLocalRing_stalk f (Z.subschemeι w)
  ⟨Z.subschemeι.stalkMap w (z j), stalkMap_mem_maximalIdeal Z w h.1 j,
    stalkMap_notMem_maximalIdeal_sq Z w h.1 hZ hj,
    stalkIdeal_comap_subschemeι_eq_span Z w _ hij,
    isRegularLocalRing_quotient_stalkIdeal_comap Z w h.1 hZ _ hij⟩

/-- Globally: if the component `E^i` contains `Z` near no point of `Z ∩ E^i`, then `E^i ∩ Z` is a
smooth divisor of `V(Z)`. -/
theorem HasSncWith.isSmoothDivisor_comap (f : X ⟶ Spec (.of k)) [Smooth f]
    {E : DivisorFamily X} {Z : X.IdealSheafData} (h : E.HasSncWith Z) (i : E.ι)
    (hi : ∀ x ∈ Z.support, x ∈ (E.component i).support →
      ¬ (E.component i).stalkIdeal x ≤ Z.stalkIdeal x) :
    IsSmoothDivisor ((E.component i).comap Z.subschemeι) := by
  refine ⟨isRegular_subscheme_of_isRegularLocalRing_quotient _ fun w hw => ?_,
    fun w hw => ?_⟩
  · have hx := subschemeι_mem_support Z w
    have hxi := (mem_support_comap_iff Z w _).mp hw
    have := isRegularLocalRing_stalk f (Z.subschemeι w)
    obtain ⟨n, z, hsnc, s, hZ⟩ := h _ hx
    obtain ⟨c, -, hc⟩ := hsnc.2
    exact isRegularLocalRing_quotient_stalkIdeal_comap Z w hsnc.1 hZ _ (hc ⟨i, hxi⟩)
  · have hx := subschemeι_mem_support Z w
    have hxi := (mem_support_comap_iff Z w _).mp hw
    have := isRegularLocalRing_stalk f (Z.subschemeι w)
    obtain ⟨n, z, hsnc, s, hZ⟩ := h _ hx
    obtain ⟨c, -, hc⟩ := hsnc.2
    have hj := notMem_of_not_stalkIdeal_le hsnc.1 hZ (hc ⟨i, hxi⟩) (hi _ hx hxi)
    exact ⟨Z.subschemeι.stalkMap w (z (c ⟨i, hxi⟩)),
      stalkMap_mem_maximalIdeal Z w hsnc.1 _,
      stalkMap_notMem_maximalIdeal_sq Z w hsnc.1 hZ hj,
      stalkIdeal_comap_subschemeι_eq_span Z w _ (hc ⟨i, hxi⟩)⟩

/-- At a point `w` of `V(Z)` over `x = ι w`: if no component through `x` contains `Z` near `x`, the
restricted family `E|_Z = E.comap ι` satisfies Kollár's (1)–(3) at `w` with coordinates the images
of the `z_l`, `l ∉ s` — enumerated by an injective `σ : Fin m → Fin n` with values outside `s`. -/
theorem IsSncAt.exists_isSncAt_comap (f : X ⟶ Spec (.of k)) [Smooth f] {E : DivisorFamily X}
    {Z : X.IdealSheafData} {w : Z.subscheme} {n : ℕ}
    {z : Fin n → X.presheaf.stalk (Z.subschemeι w)} (h : E.IsSncAt (Z.subschemeι w) z)
    {s : Finset (Fin n)} (hZ : Z.stalkIdeal (Z.subschemeι w) = Ideal.span (z '' ↑s))
    (hno : ∀ i, Z.subschemeι w ∈ (E.component i).support →
      ¬ (E.component i).stalkIdeal (Z.subschemeι w) ≤ Z.stalkIdeal (Z.subschemeι w)) :
    ∃ (m : ℕ) (σ : Fin m → Fin n), Function.Injective σ ∧ (∀ l, σ l ∉ s) ∧
      (E.comap Z.subschemeι).IsSncAt w (fun l => Z.subschemeι.stalkMap w (z (σ l))) := by
  have := isRegularLocalRing_stalk f (Z.subschemeι w)
  obtain ⟨c, hcinj, hc⟩ := h.2
  have hno' : ∀ i, c i ∉ s := fun i =>
    notMem_of_not_stalkIdeal_le h.1 hZ (hc i) (hno i.1 i.2)
  obtain ⟨c', hc'inj, hc'⟩ :=
    exists_snc_data_comap Z w E.component c hcinj hc hno'
  exact ⟨sᶜ.card, sᶜ.orderEmbOfFin rfl, (sᶜ.orderEmbOfFin rfl).injective,
    fun l => Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem rfl l),
    ⟨span_range_stalkMap_comp_eq_maximalIdeal Z w h.1 hZ,
      natCast_card_compl_eq_ringKrullDim_stalk_subscheme Z w h.1 hZ⟩,
    c', hc'inj, hc'⟩

/-- Kollár's "if `E` does not contain `Z`, then `E|_Z` is again a simple normal crossing divisor on
`Z`" [Kol07, Definition 24]: if `Z` has simple normal crossings with `E` and no component of `E`
contains `Z` near any point of `Z`, the inverse image family `E.comap ι` on `V(Z)` is a simple
normal crossing divisor. -/
theorem HasSncWith.isSnc_comap (f : X ⟶ Spec (.of k)) [Smooth f] {E : DivisorFamily X}
    {Z : X.IdealSheafData} (h : E.HasSncWith Z)
    (hno : ∀ x ∈ Z.support, ∀ i, x ∈ (E.component i).support →
      ¬ (E.component i).stalkIdeal x ≤ Z.stalkIdeal x) :
    (E.comap Z.subschemeι).IsSnc :=
  ⟨fun i => (HasSncWith.isSmoothDivisor_comap f h i fun x hx hxi => hno x hx i hxi).1,
    fun w =>
      let ⟨_n, _z, hsnc, _s, hZ⟩ := h _ (subschemeι_mem_support Z w)
      let ⟨m, _σ, _, _, hsnc'⟩ :=
        IsSncAt.exists_isSncAt_comap f hsnc hZ (hno _ (subschemeι_mem_support Z w))
      ⟨m, _, hsnc'⟩⟩

end Smooth

end AlgebraicGeometry
