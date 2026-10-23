import DeJongAlterations.StableModification.ValCurves.ModificationsFinite
import DeJongAlterations.Geometry.ModificationCenterOpen
import DeJongAlterations.Geometry.CurveCompactificationRestriction
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Modifications of curves over a valuation ring (Temkin, Lemma 4.2.1)

Let `S` be a scheme whose local rings are valuation rings (for instance `S = Spec R` for a
valuation ring `R`), `C` an integral scheme and `φ : C → S` a morphism whose generic point has
residue field of transcendence degree at most one over its image (a *relative curve*). This is
the setting of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
§4.2 (`semi-stable.tex` lines 2857–2902): `R` a valuation ring of finite height, `C` a connected
`S`-curve with smooth generic fibre, hence integral. Modifications are de Jong's
`DeJongAlterations.IsModification` (proper birational morphisms of integral schemes); since the
generic fibre `C_η` is smooth, Temkin's modifications of `C` are exactly these (T:2859–2861 and
`Curves.IsSchematicModification.isModification`).

* `fibreGenericSet φ`: Temkin's `(C/S)⁰ = ⋃ₛ C_s⁰`, the set of points `x` with
  `trdeg (κ(x)/κ(φ x)) = 1` (for a relative curve locally of finite type these are the generic
  points of the fibres, T:2872).
* `fiberTrdeg_le_one`: every modification of `C` is again a relative curve: the transcendence
  degree of `κ(x')` over the base is at most that of the generic point (dimension inequality
  over a valuation ring, `ValuationRing.fiberTrdeg_le_of_specializes`), which is unchanged by a
  birational morphism.
* `mem_isomorphismOpen_of_mem_fibreGenericSet` (**Lemma 4.2.1 (i)**, `normmodlem`): if `C` is
  normal, every `x ∈ (C/S)⁰` lies in the open where the modification `f : C' → C` is an
  isomorphism; consequently `f⁻¹(x)` is one point `x'` (`existsUnique_preimage_of_mem…`) and
  `𝒪_{C,x} → 𝒪_{C',x'}` is an isomorphism (`isIso_stalkMap_of_mem…`).
* `fiberTrdeg_eq_zero_of_mem_center`, `finite_center_inter_preimage`, `finite_center`
  (**Lemma 4.2.1 (ii)**): every point of the modification locus `Z` has residue field algebraic
  over the base (so `Z` is quasi-finite over `S`), `Z ∩ C_s` is finite for every `s`, and `Z` is
  finite when `S` is (finite height).
* `exists_specializes_mem_fibreGenericSet_isClosed`: a point of `(C'/S)⁰` contracted by `f` has a
  specialization in `(C'/S)⁰` which `f` maps to a closed point of `C` (the geometric step of
  Temkin's Lemma 4.2.2, T:2914–2922).

## Adaptations

Temkin proves Lemma 4.2.1 by base change to `Spec 𝒪_{C,x}` and EGA IV 8.11.1. Here the points of
`C'` over a point of `(C/S)⁰` are shown to have algebraic residue fields by additivity of
transcendence degrees; such fibres are finite, so the proper `f` is finite over a neighbourhood
`V` of `x` by Zariski's Main Theorem (`exists_isFinite_morphismRestrict_of_isAlgebraicAt`), and
finite birational morphisms onto the normal `V` are isomorphisms (Codex's
`Geometry.NormalCurveModification.isIso_of_finite_birational`). This gives the slightly stronger
conclusion that `f` is an isomorphism over a neighbourhood of `x`. The relative dimension bound
is stated with transcendence degrees of residue fields; flatness and finite presentation of `C`
are not needed for these statements.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace DeJongAlterations.StableModification.ValCurves

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg
  fiberTrdeg_le_of_specializes)
open Geometry.ModificationCenter (isomorphismOpen center)

variable {S C C' : Scheme.{u}} (φ : C ⟶ S)

/-- Temkin's set `(C/S)⁰` (T:2872): the points of `C` whose residue field has transcendence
degree one over the residue field of their image in `S`. For a relative curve these are the
generic points of the fibres. -/
def fibreGenericSet : Set C := {x | fiberTrdeg φ x = 1}

theorem mem_fibreGenericSet_iff {x : C} : x ∈ fibreGenericSet φ ↔ fiberTrdeg φ x = 1 := Iff.rfl

/-- A cardinal at most one which is not one is zero. -/
theorem Cardinal.eq_zero_of_le_one_of_ne_one {c : Cardinal} (h1 : c ≤ 1) (h : c ≠ 1) :
    c = 0 :=
  Cardinal.lt_one_iff.mp (lt_of_le_of_ne h1 h)

/-- If `1 + c ≤ 1` for a cardinal `c`, then `c = 0`. -/
theorem Cardinal.eq_zero_of_one_add_le_one {c : Cardinal} (h : 1 + c ≤ 1) : c = 0 := by
  by_contra hc
  have h1 : (1 : Cardinal) ≤ c := Cardinal.one_le_iff_ne_zero.mpr hc
  have : (1 : Cardinal) + 1 ≤ 1 := (add_le_add_right h1 1).trans h
  rw [one_add_one_eq_two] at this
  exact absurd this (by norm_num)

/-- A point of `(C'/S)⁰` with algebraic residue field over its image lies over `(C/S)⁰`. -/
theorem mem_fibreGenericSet_of_comp {f : C' ⟶ C} {x' : C'} (hx : x' ∈ fibreGenericSet (f ≫ φ))
    (halg : IsAlgebraicAt f x') : f x' ∈ fibreGenericSet φ := by
  rw [mem_fibreGenericSet_iff, fiberTrdeg_comp,
    (isAlgebraicAt_iff_fiberTrdeg_eq_zero f x').mp halg, add_zero] at hx
  exact hx

variable [∀ s : S, PreValuationRing (S.presheaf.stalk s)]

/-- Over a base whose local rings are valuation rings, the transcendence degree of any point of an
integral scheme is bounded by that of the generic point. -/
theorem fiberTrdeg_le_genericPoint [IsIntegral C] (x : C) :
    fiberTrdeg φ x ≤ fiberTrdeg φ (genericPoint C) :=
  fiberTrdeg_le_of_specializes φ ((genericPoint_spec C).specializes (Set.mem_univ x))

omit [∀ s : S, PreValuationRing (S.presheaf.stalk s)] in
/-- A modification does not change the transcendence degree of the generic point. -/
theorem fiberTrdeg_comp_genericPoint [IsIntegral C] [IsIntegral C'] (f : C' ⟶ C)
    [hf : IsModification f] :
    fiberTrdeg (f ≫ φ) (genericPoint C') = fiberTrdeg φ (genericPoint C) := by
  have := Geometry.NormalCurveModification.generic_stalkMap_isIso f hf.birational
  rw [fiberTrdeg_comp, (isAlgebraicAt_iff_fiberTrdeg_eq_zero f _).mp
    isAlgebraicAt_of_isIso_stalkMap, add_zero,
    Geometry.NormalCurveModification.genericPoint_map f hf.birational]

/-- **Modifications of a relative curve are relative curves**: if the generic point of `C` has
transcendence degree at most one over `S`, so has every point of every modification of `C`. -/
theorem fiberTrdeg_le_one [IsIntegral C] [IsIntegral C']
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] (x' : C') :
    fiberTrdeg (f ≫ φ) x' ≤ 1 := (fiberTrdeg_le_genericPoint (f ≫ φ) x').trans
    ((fiberTrdeg_comp_genericPoint φ f).trans_le hdim)

/-- The bound for `C` itself. -/
theorem fiberTrdeg_le_one_self [IsIntegral C] (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (x : C) : fiberTrdeg φ x ≤ 1 :=
  (fiberTrdeg_le_genericPoint φ x).trans hdim

/-- Over a point of `(C/S)⁰`, every point of a modification has algebraic residue field. -/
theorem isAlgebraicAt_of_mem_fibreGenericSet [IsIntegral C] [IsIntegral C']
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (f : C' ⟶ C) [IsModification f] {x' : C'} (hx : f x' ∈ fibreGenericSet φ) :
    IsAlgebraicAt f x' := by
  rw [isAlgebraicAt_iff_fiberTrdeg_eq_zero]
  have h := fiberTrdeg_le_one φ hdim f x'
  rw [fiberTrdeg_comp, hx] at h
  exact Cardinal.eq_zero_of_one_add_le_one h

/-- The preimage of `(C/S)⁰` under a modification is contained in `(C'/S)⁰` (this gives
`Γ(C) ⊆ Γ(C')`, T:2916). -/
theorem mem_fibreGenericSet_comp [IsIntegral C] [IsIntegral C']
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (f : C' ⟶ C) [IsModification f] {x' : C'} (hx : f x' ∈ fibreGenericSet φ) :
    x' ∈ fibreGenericSet (f ≫ φ) := by
  rw [mem_fibreGenericSet_iff, fiberTrdeg_comp, hx,
    (isAlgebraicAt_iff_fiberTrdeg_eq_zero f x').mp
      (isAlgebraicAt_of_mem_fibreGenericSet φ hdim f hx),
    add_zero]

/-- **Temkin, Lemma 4.2.1 (i)** (`normmodlem`). Let `C` be normal and `f : C' → C` a modification.
Every point `x ∈ (C/S)⁰` lies in the open of `C` over which `f` is an isomorphism. -/
theorem mem_isomorphismOpen_of_mem_fibreGenericSet [IsIntegral C] [IsIntegral C']
    (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [hf : IsModification f] {x : C}
    (hx : x ∈ fibreGenericSet φ) : x ∈ isomorphismOpen f := by
  obtain ⟨V, hxV, hfin, -⟩ := exists_isFinite_morphismRestrict_of_isAlgebraicAt f x
    fun x' hx' ↦ isAlgebraicAt_of_mem_fibreGenericSet φ hdim f (hx' ▸ hx)
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hn : IsNormalScheme V.toScheme :=
    Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion V.ι hnormal
  have hr := Geometry.CurveCompactification.isModification_morphismRestrict f V
  have := hr.sourceIntegral
  have := hr.targetIntegral
  have : IsIso (f ∣_ V) :=
    Geometry.NormalCurveModification.isIso_of_finite_birational (f ∣_ V) hr.birational hn
  exact Geometry.ModificationCenter.le_isomorphismOpen_of_isIso f V hxV

/-- **Temkin, Lemma 4.2.1 (i)**: `f⁻¹(x)` is a single point for `x ∈ (C/S)⁰`. -/
theorem existsUnique_preimage_of_mem_fibreGenericSet [IsIntegral C] [IsIntegral C']
    (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] {x : C}
    (hx : x ∈ fibreGenericSet φ) : ∃! x' : C', f x' = x := by
  have hW := mem_isomorphismOpen_of_mem_fibreGenericSet φ hnormal hdim f hx
  let W := isomorphismOpen f
  have hbij : Function.Bijective (f ∣_ W) := by
    have := (f ∣_ W).homeomorph.bijective
    convert this using 1
    funext a
    exact (Scheme.Hom.homeomorph_apply _ a).symm
  obtain ⟨x'', hx''⟩ := hbij.2 ⟨x, hW⟩
  have hx''' : f x''.1 = x := by
    have := congrArg Subtype.val hx''
    rwa [morphismRestrict_base_coe] at this
  refine ⟨x''.1, hx''', fun y hy ↦ ?_⟩
  have hyW : y ∈ f ⁻¹ᵁ W := by
    change f y ∈ W
    rw [hy]
    exact hW
  let y' : (f ⁻¹ᵁ W).toScheme := ⟨y, hyW⟩
  have : (f ∣_ W) y' = (f ∣_ W) x'' := by
    apply Subtype.ext
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe, hx''']
    exact hy
  exact congrArg Subtype.val (hbij.1 this)

/-- **Temkin, Lemma 4.2.1 (i)**: `𝒪_{C,x} → 𝒪_{C',x'}` is an isomorphism for `x = f x' ∈ (C/S)⁰`. -/
theorem isIso_stalkMap_of_mem_fibreGenericSet [IsIntegral C] [IsIntegral C']
    (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] {x' : C'}
    (hx : f x' ∈ fibreGenericSet φ) : IsIso (f.stalkMap x') := by
  have hW := mem_isomorphismOpen_of_mem_fibreGenericSet φ hnormal hdim f hx
  let W := isomorphismOpen f
  let p : (f ⁻¹ᵁ W).toScheme := ⟨x', hW⟩
  have : IsIso ((f ∣_ W).stalkMap p) := inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (morphismRestrictStalkMap f W p)).mp this

/-- **Temkin, Lemma 4.2.1 (ii)**: every point of the modification locus of `f` has residue field
algebraic over the base, i.e. the modification locus is quasi-finite over `S`. -/
theorem fiberTrdeg_eq_zero_of_mem_center [IsIntegral C] [IsIntegral C'] (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] {z : C}
    (hz : z ∈ center f) : fiberTrdeg φ z = 0 := by
  refine Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one_self φ hdim z) fun h ↦ hz ?_
  exact mem_isomorphismOpen_of_mem_fibreGenericSet φ hnormal hdim f h

/-- **Temkin, Lemma 4.2.1 (ii)**: the modification locus meets each fibre in a finite set. -/
theorem finite_center_inter_preimage [IsIntegral C] [IsIntegral C'] [QuasiCompact φ] [IsSeparated φ]
    [LocallyOfFiniteType φ] (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] (s : S) :
    ((center f : Set C) ∩ φ ⁻¹' {s}).Finite :=
  finite_inter_preimage_of_isAlgebraicAt φ (center f).isClosed s fun z hz _ ↦
    (isAlgebraicAt_iff_fiberTrdeg_eq_zero φ z).mpr
      (fiberTrdeg_eq_zero_of_mem_center φ hnormal hdim f hz)

/-- **Temkin, Lemma 4.2.1 (ii)**: over a base with finitely many points (a valuation ring of finite
height), the modification locus is finite. -/
theorem finite_center [Finite S] [IsIntegral C] [IsIntegral C'] [QuasiCompact φ] [IsSeparated φ]
    [LocallyOfFiniteType φ] (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] :
    (center f : Set C).Finite := by
  refine (Set.finite_iUnion fun s ↦
    finite_center_inter_preimage φ hnormal hdim f s).subset fun z hz ↦ ?_
  exact Set.mem_iUnion.mpr ⟨φ z, hz, rfl⟩

/-- **Contracted points specialize to points over closed points** (Temkin, proof of Lemma 4.2.2,
T:2914–2922). Let `C` be quasi-compact, `f : C' → C` a modification and `x' ∈ (C'/S)⁰` with
`f x' ∉ (C/S)⁰`. Then `x'` specializes to a point `y' ∈ (C'/S)⁰` such that `f y'` is a closed point
of `C`.

Proof: choose a closed point `z₀` of `C` in the closure of `z = f x'`. If every point of the
closure `X` of `x'` (with its reduced structure) over `z₀` had residue field algebraic over
`κ(z₀)`, the proper map `X → C` would have algebraic residue field extensions over a
neighbourhood of `z₀`, which contains `z`; but `κ(x')` has transcendence degree one over `κ(z)`. -/
theorem exists_specializes_mem_fibreGenericSet_isClosed [IsIntegral C] [IsIntegral C']
    [CompactSpace C] (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f]
    {x' : C'}
    (hx' : x' ∈ fibreGenericSet (f ≫ φ)) (hfx : f x' ∉ fibreGenericSet φ) :
    ∃ y' : C', x' ⤳ y' ∧ y' ∈ fibreGenericSet (f ≫ φ) ∧ IsClosed ({f y'} : Set C) := by
  have hz0 : fiberTrdeg φ (f x') = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one_self φ hdim _) hfx
  obtain ⟨z₀, hz₀, hz₀cl⟩ :=
    (isClosed_closure (s := {f x'})).exists_closed_singleton ⟨f x', subset_closure rfl⟩
  by_contra H
  push Not at H
  -- the reduced closed subscheme on the closure of `x'`
  let Z : C'.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨closure {x'}, isClosed_closure⟩
  let i := Z.subschemeι
  have hrange : Set.range i = closure {x'} := by
    rw [Z.range_subschemeι, Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
    rfl
  have halg : ∀ p, (i ≫ f) p = z₀ → IsAlgebraicAt (i ≫ f) p := by
    intro p hp
    have hsp : x' ⤳ i p := by
      rw [specializes_iff_mem_closure, ← hrange]
      exact ⟨p, rfl⟩
    have hne : i p ∉ fibreGenericSet (f ≫ φ) := fun hmem ↦ by
      refine H (i p) hsp hmem ?_
      change IsClosed {(i ≫ f) p}
      rw [hp]
      exact hz₀cl
    have h0 : fiberTrdeg (f ≫ φ) (i p) = 0 :=
      Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f (i p)) hne
    rw [fiberTrdeg_comp] at h0
    exact (isAlgebraicAt_of_surjectiveOnStalks i p).comp
      ((isAlgebraicAt_iff_fiberTrdeg_eq_zero f _).mpr (add_eq_zero.mp h0).2)
  obtain ⟨V, hz₀V, -, hV⟩ := exists_isFinite_morphismRestrict_of_isAlgebraicAt (i ≫ f) z₀ halg
  obtain ⟨p₀, hp₀⟩ : x' ∈ Set.range i := by
    rw [hrange]
    exact subset_closure rfl
  have hzV : (i ≫ f) p₀ ∈ V := by
    change f (i p₀) ∈ V
    rw [hp₀]
    exact (specializes_iff_mem_closure.mpr hz₀).mem_open V.isOpen hz₀V
  have h1 := (isAlgebraicAt_iff_fiberTrdeg_eq_zero _ _).mp (hV p₀ hzV)
  rw [fiberTrdeg_comp, hp₀] at h1
  have h2 : fiberTrdeg (f ≫ φ) x' = 0 := by
    rw [fiberTrdeg_comp, hz0, (add_eq_zero.mp h1).1, add_zero]
  rw [mem_fibreGenericSet_iff, h2] at hx'
  exact zero_ne_one hx'

end DeJongAlterations.StableModification.ValCurves
