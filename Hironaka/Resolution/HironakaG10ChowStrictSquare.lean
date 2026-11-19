import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Closure

/-!
# Point-set and stalk lemmas for a strict-transform square

General lemmas used by the Chow-side reduction of domination to flattening
(blueprint `hironaka-g10-chowside-strict-square.tex`).  The situation is a commutative
square

```
Y' --q--> Y
|p        |f
v         v
X' --σ--> X
```

in which `σ` is a modification with exceptional set `E ⊆ X'` (closed, with empty interior,
`σ` open off `E`), `f` is injective over the complement of a thin set `B ⊆ X`, and `Y'` is a
strict transform: the pair map `(p, q)` is injective and every point of the fibre product
over `X' \ E` lies in `Y'`.

Main declarations:

* `interior_preimage_eq_empty_of_isOpen_image` — the preimage of a set with empty interior
  under a map which is open off a closed set with empty interior has empty interior.
* `interior_union_preimage_eq_empty`, `dense_compl_inter_preimage_compl` — the good locus
  `X' \ (E ∪ σ⁻¹ B)` is dense.
* `injOn_of_square`, `subset_range_of_square` — `p` is injective over the good locus and
  covers it.
* `isIso_stalkMap_of_eq`, `isIso_stalkMap_of_square` — in a commutative square of locally
  ringed spaces, if the stalk maps of `q`, `f` and `σ` at the relevant points are
  isomorphisms, so is the stalk map of `p`.
-/

set_option autoImplicit false

open Set Topology CategoryTheory AlgebraicGeometry

namespace Hironaka.HironakaG10ChowStrictSquare

section Thin

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

/-- **Thin sets pull back to thin sets under a generically open map.**  If `σ` maps open
subsets of the complement of a closed set `E` with empty interior to open sets, the preimage
of a set with empty interior has empty interior.  (No continuity of `σ` is needed.) -/
theorem interior_preimage_eq_empty_of_isOpen_image {σ : X' → X} {E : Set X'}
    (hEc : IsClosed E) (hEint : interior E = ∅)
    (hopen : ∀ U : Set X', IsOpen U → U ⊆ Eᶜ → IsOpen (σ '' U)) {B : Set X}
    (hB : interior B = ∅) : interior (σ ⁻¹' B) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
  have hnotsub : ¬ interior (σ ⁻¹' B) ⊆ E := fun hsub => by
    have hxE : x ∈ interior E := interior_maximal hsub isOpen_interior hx
    rw [hEint] at hxE
    exact hxE
  obtain ⟨z, hzO, hzE⟩ := not_subset.mp hnotsub
  have hU : IsOpen (interior (σ ⁻¹' B) ∩ Eᶜ) := isOpen_interior.inter hEc.isOpen_compl
  have himg : σ '' (interior (σ ⁻¹' B) ∩ Eᶜ) ⊆ B := by
    rintro _ ⟨u, ⟨huO, _⟩, rfl⟩
    exact (interior_subset huO : u ∈ σ ⁻¹' B)
  have hmem : σ z ∈ interior B :=
    interior_maximal himg (hopen _ hU inter_subset_right) ⟨z, ⟨hzO, hzE⟩, rfl⟩
  rw [hB] at hmem
  exact hmem

/-- The bad locus `E ∪ σ⁻¹ B` of a square has empty interior. -/
theorem interior_union_preimage_eq_empty {σ : X' → X} {E : Set X'}
    (hEc : IsClosed E) (hEint : interior E = ∅)
    (hopen : ∀ U : Set X', IsOpen U → U ⊆ Eᶜ → IsOpen (σ '' U)) {B : Set X}
    (hB : interior B = ∅) : interior (E ∪ σ ⁻¹' B) = ∅ := by
  rw [interior_union_isClosed_of_interior_empty hEc
    (interior_preimage_eq_empty_of_isOpen_image hEc hEint hopen hB), hEint]

/-- The good locus `(X' \ E) ∩ σ⁻¹(X \ B)` of a square is dense. -/
theorem dense_compl_inter_preimage_compl {σ : X' → X} {E : Set X'}
    (hEc : IsClosed E) (hEint : interior E = ∅)
    (hopen : ∀ U : Set X', IsOpen U → U ⊆ Eᶜ → IsOpen (σ '' U)) {B : Set X}
    (hB : interior B = ∅) : Dense (Eᶜ ∩ σ ⁻¹' Bᶜ) := by
  have h := interior_eq_empty_iff_dense_compl.mp
    (interior_union_preimage_eq_empty hEc hEint hopen hB)
  rwa [compl_union, ← preimage_compl] at h

/-- A map which is open off `E₁`, followed by a map which is open off `E₂`, is open off
`E₁ ∪ π⁻¹ E₂`. -/
theorem isOpen_image_comp_of_isOpen_image {X'' : Type*} [TopologicalSpace X'']
    {π : X'' → X'} {σ : X' → X} {E₁ : Set X''} {E₂ : Set X'}
    (hπ : ∀ U : Set X'', IsOpen U → U ⊆ E₁ᶜ → IsOpen (π '' U))
    (hσ : ∀ U : Set X', IsOpen U → U ⊆ E₂ᶜ → IsOpen (σ '' U))
    (U : Set X'') (hU : IsOpen U) (hUE : U ⊆ (E₁ ∪ π ⁻¹' E₂)ᶜ) : IsOpen ((σ ∘ π) '' U) := by
  rw [image_comp]
  refine hσ _ (hπ U hU fun u hu => fun hu₁ => hUE hu (Or.inl hu₁)) ?_
  rintro _ ⟨u, hu, rfl⟩ hu₂
  exact hUE hu (Or.inr hu₂)

end Thin

section Square

variable {X X' Y Y' : Type*} {p : Y' → X'} {q : Y' → Y} {f : Y → X} {σ : X' → X}

/-- **`p` is injective over the good locus.**  In a commutative square with injective pair
map `(p, q)`, if `f` is injective over `X \ B` then `p` is injective over `σ⁻¹(X \ B)`. -/
theorem injOn_of_square (hsq : ∀ y', f (q y') = σ (p y'))
    (hpair : ∀ a b : Y', p a = p b → q a = q b → a = b) {B : Set X}
    (hf : InjOn f (f ⁻¹' Bᶜ)) : InjOn p (p ⁻¹' (σ ⁻¹' Bᶜ)) := by
  intro a ha b hb hab
  have ha' : q a ∈ f ⁻¹' Bᶜ := by
    change f (q a) ∈ Bᶜ
    rw [hsq a]
    exact ha
  have hb' : q b ∈ f ⁻¹' Bᶜ := by
    change f (q b) ∈ Bᶜ
    rw [hsq b]
    exact hb
  exact hpair a b hab (hf ha' hb' (by rw [hsq a, hsq b, hab]))

/-- **`p` covers the good locus.**  If `f` covers `X \ B` and every point of the fibre
product over `X' \ E` is of the form `(p y', q y')`, then `p` covers
`(X' \ E) ∩ σ⁻¹(X \ B)`. -/
theorem subset_range_of_square {E : Set X'} {B : Set X} (hf : Bᶜ ⊆ range f)
    (hcov : ∀ (y : Y) (x' : X'), x' ∉ E → f y = σ x' → ∃ y', p y' = x' ∧ q y' = y) :
    Eᶜ ∩ σ ⁻¹' Bᶜ ⊆ range p := by
  rintro x' ⟨hxE, hxB⟩
  obtain ⟨y, hy⟩ := hf hxB
  obtain ⟨y', hy', _⟩ := hcov y x' hxE hy
  exact ⟨y', hy'⟩

end Square

section Stalks

variable {X Y : LocallyRingedSpace}

/-- Equal morphisms have simultaneously isomorphic stalk maps. -/
theorem isIso_stalkMap_of_eq {g g' : Y ⟶ X} (h : g = g') (y : Y)
    (hg : IsIso (g.stalkMap y)) : IsIso (g'.stalkMap y) := by
  subst h
  exact hg

/-- **Stalks in a commutative square.**  If `q ≫ f = p ≫ σ` and the stalk maps of `q` at
`y'`, of `f` at `q y'` and of `σ` at `p y'` are isomorphisms, the stalk map of `p` at `y'`
is an isomorphism. -/
theorem isIso_stalkMap_of_square {X' Y' : LocallyRingedSpace} {p : Y' ⟶ X'} {q : Y' ⟶ Y}
    {f : Y ⟶ X} {σ : X' ⟶ X} (hsq : q ≫ f = p ≫ σ) (y' : Y')
    (hq : IsIso (q.stalkMap y')) (hf : IsIso (f.stalkMap (q.base y')))
    (hσ : IsIso (σ.stalkMap (p.base y'))) : IsIso (p.stalkMap y') := by
  have h₁ : IsIso ((q ≫ f).stalkMap y') := by
    rw [LocallyRingedSpace.stalkMap_comp]
    exact IsIso.comp_isIso' hf hq
  have h₂ : IsIso ((p ≫ σ).stalkMap y') := isIso_stalkMap_of_eq hsq y' h₁
  rw [LocallyRingedSpace.stalkMap_comp] at h₂
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (σ.stalkMap (p.base y')) (p.stalkMap y') hσ h₂

end Stalks

end Hironaka.HironakaG10ChowStrictSquare
