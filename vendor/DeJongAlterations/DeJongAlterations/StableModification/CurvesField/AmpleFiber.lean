/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3B)
-/
import DeJongAlterations.StableModification.CurvesField.AmpleSection

/-!
# Fibre-ampleness of line bundles of positive degree on curves

Let `X` be a projective scheme of dimension at most one over an infinite field `K` (possibly
reducible, singular and non-reduced, possibly with isolated points), and `L` line-bundle data on
`X`. Suppose that some power `𝓛^n`, `n > 0`, has a global section `s` which does not vanish at the
generic point of any one-dimensional irreducible component and vanishes at some point of each of
them (on every component the restriction of `𝓛` has positive degree, witnessed by `s`). Then `𝓛`
is **ample in Serre's sense** (`CurvesField.serreAmple_of_section`): for every quasi-coherent `F` of
finite type and all `m ≫ 0`, `F ⊗ 𝓛^m` is globally generated with `H¹ = 0`. For a fibre `X_y` of a
morphism `β : X → Y` this is OM3A's fibre-ampleness (`CurvesField.fiberAmple_of_positive`,
`CurvesField.fiberAmple_of_section`), the input of the local-to-global theorem of the projectivity
route for M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
Theorem 1.1 (`references/temkin10-stable-modification/source/semi-stable.tex`, lines 1713--1749:
"relative ampleness can be checked separately on each fiber"). Blueprint
`sm-curves-fields-ample.tex`, `thm:sm-fiber-ample`.

The conditions are topological: `s` does not vanish at the non-closed points, and every non-closed
point specializes to a zero of `s`.

## The argument (blueprint `sm-curves-fields-ample.tex`)

1. (`exists_section_sup_eq_top`) A section `t` of some `𝓛^{n(m+1)}` without zero on the finite
   zero set of `s`.
2. (`isAffineOpen_nonvanishingLocus`) `(s^{m+1} : t) : X → ℙ¹_K` is finite, so `D(s)` and `D(t)` are
   affine.
3. (`serreAmple_of_two_sections`) On the affine cover `X = D(s) ∪ D(t)`, the twists by `𝓛^{N k}`,
   `N = n(m+1)`, are divisor twists; Serre vanishing and generation follow from the two-chart
   computations of lane COH4 and the finiteness of the cohomology of coherent modules on projective
   schemes (`Cohomology.finite_cohomology_of_isProjectiveOver`).

No normalization, no degree theory and no dévissage of coherent modules are used: the two-chart
computation applies to every coherent module directly, torsion and nilpotents included.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField

noncomputable section

open Ample Projectivity.LineBundleData

/-- **Serre ampleness of a line bundle of positive degree on a projective curve** (blueprint
`thm:sm-fiber-ample`): let `X` be projective over an infinite field `K` with
`topologicalKrullDim X ≤ 1`, and `s` a global section of `𝓛^n`, `n > 0`, which does not vanish at
the non-closed points of `X` and such that every non-closed point specializes to a zero of `s`.
Then `𝓛` is ample in Serre's sense. -/
theorem serreAmple_of_section {K : Type u} [Field K] [Infinite K] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    {L : Projectivity.LineBundleData X} {n : ℕ} (hn : 0 < n) (s : L.Sections n ⊤)
    (hgen : ∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    L.SerreAmple := by
  have : IsProper p := hp.isProper
  have : CompactSpace X := compactSpace_of_quasiCompact p
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated p
  have hdim' := eq_or_eq_of_topologicalKrullDim_le_one hdim
  obtain ⟨m, t, ht⟩ := exists_section_sup_eq_top hp hdim' s hgen
  set N : ℕ := n * (m + 1)
  have hN : 0 < N := Nat.mul_pos hn (Nat.succ_pos m)
  have hcast : (n : ℤ) * ((m + 1 : ℕ) : ℤ) = ((N : ℕ) : ℤ) := by
    simp only [N]
    push_cast
    ring
  let s₀ : L.Sections (N : ℤ) ⊤ := (s.npow (m + 1)).cast hcast
  let s₁ : L.Sections (N : ℤ) ⊤ := t.cast hcast
  have hs₀ : s₀.nonvanishingLocus = s.nonvanishingLocus := by
    rw [Sections.nonvanishingLocus_cast, Sections.nonvanishingLocus_npow _ (Nat.succ_pos m)]
  have hs₁ : s₁.nonvanishingLocus = t.nonvanishingLocus := Sections.nonvanishingLocus_cast _ _
  have hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ := by rw [hs₀, hs₁, ht]
  obtain ⟨h₀, h₁⟩ := isAffineOpen_nonvanishingLocus p hdim' s₀ s₁ hcov
    (fun x hx => hs₀ ▸ hgen x hx) (fun x hx => hs₀ ▸ hzero x hx)
  exact serreAmple_of_two_sections hN s₀ s₁ hcov h₀ h₁ (structureCoeff p)
    (fun G _ hG => finite_cohomology_of_isProjectiveOver hp G hG 1)

/-- **The complement of the zero set of a section is affine** (blueprint
`cor:sm-ample-affine-complement`): on a projective curve over an infinite field, the
non-vanishing locus of a global section of `𝓛^n` which does not vanish at the non-closed points,
and vanishes at a specialization of each of them, is affine. With the canonical section of an
effective Cartier divisor (`Projectivity.LocalEquations.canonicalSection`) this says that the
complement of the support of an effective Cartier divisor meeting every one-dimensional
irreducible component is affine. -/
theorem isAffineOpen_nonvanishingLocus_of_section {K : Type u} [Field K] [Infinite K]
    {X : Scheme.{u}} {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ 1) {L : Projectivity.LineBundleData X} {n : ℤ}
    (s : L.Sections n ⊤)
    (hgen : ∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    IsAffineOpen s.nonvanishingLocus := by
  have : IsProper p := hp.isProper
  have hdim' := eq_or_eq_of_topologicalKrullDim_le_one hdim
  obtain ⟨m, t, ht⟩ := exists_section_sup_eq_top hp hdim' s hgen
  have hs₀ : (s.npow (m + 1)).nonvanishingLocus = s.nonvanishingLocus :=
    Sections.nonvanishingLocus_npow _ (Nat.succ_pos m)
  obtain ⟨h₀, -⟩ := isAffineOpen_nonvanishingLocus p hdim' (s.npow (m + 1)) t (by rw [hs₀, ht])
    (fun x hx => hs₀ ▸ hgen x hx) (fun x hx => hs₀ ▸ hzero x hx)
  rwa [hs₀] at h₀

/-- **Fibre-ampleness from a section of positive degree on the fibre** (blueprint
`thm:sm-fiber-ample`, `CurvesField.fiberAmple_of_positive`): let `β : X ⟶ Y`, `y ∈ Y` with
infinite residue field, and suppose that the scheme-theoretic fibre `X_y` is projective over
`κ(y)` of dimension at most one. If some power `𝓛^n|_{X_y}`, `n > 0`, has a global section which
does not vanish at the non-closed points of `X_y` and vanishes at a specialization of each of them,
then `𝓛` is ample on the fibre (OM3A's `Projectivity.FiberAmple`). -/
theorem fiberAmple_of_positive {X Y : Scheme.{u}} (L : Projectivity.LineBundleData X) (β : X ⟶ Y)
    (y : Y) [Infinite (Y.residueField y)]
    (hproj : IsProjectiveOver (k := Y.residueField y) (β.fiberToSpecResidueField y))
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1) {n : ℕ} (hn : 0 < n)
    (s : (L.pullback (β.fiberι y)).Sections n ⊤)
    (hgen : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) → x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    FiberAmple L β y :=
  (fiberAmple_iff_serreAmple L β y).mpr (serreAmple_of_section hproj hdim hn s hgen hzero)

/-- **Fibre-ampleness from a global section** (the form for the canonical section of an effective
Cartier divisor, e.g. `𝒪(Σ P̄ᵢ)` for sections `P̄ᵢ` through the contracted components): if a global
section `s` of `𝓛^n` on `X`, restricted to the fibre `X_y`, does not vanish at the non-closed
points of `X_y` and vanishes at a specialization of each of them, then `𝓛` is ample on the fibre. -/
theorem fiberAmple_of_section {X Y : Scheme.{u}} (L : Projectivity.LineBundleData X) (β : X ⟶ Y)
    (y : Y) [Infinite (Y.residueField y)]
    (hproj : IsProjectiveOver (k := Y.residueField y) (β.fiberToSpecResidueField y))
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1) {n : ℕ} (hn : 0 < n) (s : L.Sections n ⊤)
    (hgen : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      β.fiberι y x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      ∃ z, x ⤳ z ∧ β.fiberι y z ∉ s.nonvanishingLocus) :
    FiberAmple L β y := by
  let s' : (L.pullback (β.fiberι y)).Sections n ⊤ :=
    (s.pullback (β.fiberι y)).restrict (le_of_eq (Scheme.Hom.preimage_top _).symm)
  have hs' : ∀ x, x ∈ s'.nonvanishingLocus ↔ β.fiberι y x ∈ s.nonvanishingLocus := by
    intro x
    rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_pullback]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  exact fiberAmple_of_positive L β y hproj hdim hn s'
    (fun x hx => (hs' x).mpr (hgen x hx))
    (fun x hx => by
      obtain ⟨z, hxz, hz⟩ := hzero x hx
      exact ⟨z, hxz, fun h => hz ((hs' z).mp h)⟩)

/-! ### Fibres of locally relatively projective morphisms -/

/-- A morphism projective relative to `𝟙 : Spec V ⟶ Spec V` is projective over `V`. -/
theorem isProjectiveOver_of_isRelativelyProjective_id {V : Type u} [CommRing V] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of V)} (h : DeJong.IsRelativelyProjective (𝟙 (Spec (.of V))) f) :
    IsProjectiveOver f := by
  obtain ⟨n, i, hi, hif⟩ := h
  have := hi
  refine ⟨n, i ≫ pullback.snd (𝟙 _) (projectiveSpaceStructure V n), inferInstance, ?_⟩
  rw [Category.assoc, ← pullback.condition, Category.comp_id, hif]

/-- **The fibres of a locally relatively projective morphism are projective** over the residue
fields: if `β : X ⟶ Y` is projective over the members of an open cover of `Y` (relative to
`pY : Y ⟶ Spec k`), then the fibre `X_y` is a closed subscheme of `ℙⁿ_{κ(y)}`. -/
theorem isProjectiveOver_fiber_of_locallyRelativelyProjective {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} {pY : Y ⟶ Spec (.of k)} {β : X ⟶ Y}
    (hloc : LocallyRelativelyProjective pY β) (y : Y) :
    IsProjectiveOver (k := Y.residueField y) (β.fiberToSpecResidueField y) := by
  obtain ⟨J, _, W, hW, hWβ⟩ := hloc
  obtain ⟨j, hj⟩ : ∃ j, y ∈ W j := Opens.mem_iSup.mp (by rw [hW]; trivial)
  set t := Y.fromSpecResidueField y
  have hrange : Set.range t ⊆ Set.range (W j).ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hj
  let t' : Spec (Y.residueField y) ⟶ W j := IsOpenImmersion.lift (W j).ι t hrange
  have ht' : t' ≫ (W j).ι = t := IsOpenImmersion.lift_fac _ _ _
  -- the fibre is the base change of `β ∣_ W j` along `t'`
  have hP : IsPullback (pullback.fst (β ∣_ W j) t' ≫ (β ⁻¹ᵁ W j).ι)
      (pullback.snd (β ∣_ W j) t') β (t' ≫ (W j).ι) :=
    ((IsPullback.of_hasPullback (β ∣_ W j) t').flip.paste_vert
      (isPullback_morphismRestrict β (W j))).flip
  rw [ht'] at hP
  have h₁ := (hWβ j).pullback_snd t'
  have h₂ := Projectivity.isRelativelyProjective_iso_hom_comp h₁ hP.isoPullback.symm
  rw [Iso.symm_hom, ← Category.assoc t' (W j).ι pY, ht', IsPullback.isoPullback_inv_snd] at h₂
  -- change of the coefficient ring along `k → κ(y)`
  set φ := Spec.preimage (t ≫ pY)
  have hφ : t ≫ pY = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ.hom) := by
    rw [Category.id_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [hφ] at h₂
  exact isProjectiveOver_of_isRelativelyProjective_id
    ((Projectivity.isRelativelyProjective_comp_specMap_iff φ.hom (𝟙 _) _).mp h₂)

/-- **Fibre-ampleness for a locally relatively projective morphism** (the form used by the
local-to-global theorem): if `β` is locally relatively projective, the fibre `X_y` has dimension at
most one and `κ(y)` is infinite, a section of `𝓛^n` on `X` which does not vanish at the non-closed
points of `X_y` and vanishes at a specialization in `X_y` of each of them makes `𝓛` ample on
`X_y`. -/
theorem fiberAmple_of_section_of_locallyRelativelyProjective {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} {pY : Y ⟶ Spec (.of k)} (L : Projectivity.LineBundleData X) (β : X ⟶ Y)
    (hloc : LocallyRelativelyProjective pY β) (y : Y) [Infinite (Y.residueField y)]
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1) {n : ℕ} (hn : 0 < n) (s : L.Sections n ⊤)
    (hgen : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      β.fiberι y x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      ∃ z, x ⤳ z ∧ β.fiberι y z ∉ s.nonvanishingLocus) :
    FiberAmple L β y :=
  fiberAmple_of_section L β y (isProjectiveOver_fiber_of_locallyRelativelyProjective hloc y) hdim
    hn s hgen hzero

end

end DeJongAlterations.StableModification.CurvesField
