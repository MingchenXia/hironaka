/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.ValCurves.Modifications
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Localizing at a contracted point (Temkin, proof of Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (`stabcritlem`, T:3108–3114): "The modification locus `V` of `f` is quasi-finite over
`S`, hence `V_x := Spec(𝒪_{V,x})` is an open neighbourhood of `x` in `V`. Thus, shrinking `C`
again, we can achieve that `x` is the only closed point of `V`." Blueprint `lem:sm-bd-localize`
(chapter `sm-blow-down-criterion.tex`), parts (1) and (2):

* `finite_center`, `isAlgebraicAt_of_mem_center`, `isClosed_singleton_preimage_of_mem_center`:
  the modification locus `Z(f)` of a modification `f : C' → C` of a normal relative curve over a
  base with finitely many points is finite, its points are algebraic over their images in `S` and
  closed in their fibres (lane T42's Temkin Lemma 4.2.1(ii));
* `not_finite_preimage_of_mem_center` (Temkin's "`Z` is a curve"): the fibre of `f` over a point
  of `Z(f)` is infinite (otherwise `f` is finite over a neighbourhood by Zariski's main theorem,
  hence an isomorphism there since `C` is normal);
* `isConnected_preimage_of_mem_center`: these fibres are connected (lane COH3E's Zariski
  connectedness, over a valuation ring of finite height);
* `exists_isOpen_inter_center_eq` (part (2)): `x ∈ Z(f)` has an open neighbourhood `U` with
  `Z(f) ∩ U` the set `Z_x` of generizations of `x` in `Z(f)`, and `Z_x` meets the fibre of `x`
  only in `x`.

Part (3) of `lem:sm-bd-localize` (extending `f|_{f⁻¹U}` by the identity to a compactification) is
not formalized; see `cor:sm-bd-stability-local`.
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits Topology
open Geometry.ModificationCenter (isomorphismOpen center)

universe u

section Locus

variable {S C C' : Scheme.{u}} (φ : C ⟶ S) [∀ s : S, PreValuationRing (S.presheaf.stalk s)]
  [IsIntegral C] [IsIntegral C'] (f : C' ⟶ C) [IsModification f]

/-- **The modification locus is finite** over a base with finitely many points (Temkin,
Lemma 4.2.1(ii), `ValCurves.finite_center`). -/
theorem finite_center [Finite S] [QuasiCompact φ] [IsSeparated φ] [LocallyOfFiniteType φ]
    (hnormal : IsNormalScheme C) (hdim : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1) :
    (center f : Set C).Finite :=
  ValCurves.finite_center φ hnormal hdim f

/-- **Points of the modification locus are algebraic over the base** (Temkin, Lemma 4.2.1(ii)). -/
theorem isAlgebraicAt_of_mem_center (hnormal : IsNormalScheme C)
    (hdim : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1) {x : C} (hx : x ∈ center f) :
    ValCurves.IsAlgebraicAt φ x :=
  (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero φ x).2
    (ValCurves.fiberTrdeg_eq_zero_of_mem_center φ hnormal hdim f hx)

/-- **Points of the modification locus are closed in their fibres.** -/
theorem isClosed_singleton_preimage_of_mem_center [IsSeparated φ] (hnormal : IsNormalScheme C)
    (hdim : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1) {x : C} (hx : x ∈ center f) :
    IsClosed ({⟨x, rfl⟩} : Set (φ ⁻¹' {φ x})) :=
  ValCurves.isClosed_singleton_preimage_of_isAlgebraicAt φ rfl
    (isAlgebraicAt_of_mem_center φ f hnormal hdim hx)

omit [∀ s : S, PreValuationRing (S.presheaf.stalk s)] [IsIntegral C] [IsIntegral C'] in
/-- **The fibre over a point of the modification locus is infinite** (Temkin's hypothesis "`Z` is
a curve" holds automatically): if `f⁻¹(x)` were finite, the proper `f` would be finite over a
neighbourhood `W` of `x` (Zariski's main theorem), hence an isomorphism over `W` as `C` is normal
(a finite birational morphism onto a normal integral scheme), so `x ∉ Z(f)`. -/
theorem not_finite_preimage_of_mem_center (hnormal : IsNormalScheme C) {x : C}
    (hx : x ∈ center f) : ¬ (f ⁻¹' {x}).Finite := by
  intro hfin
  obtain ⟨W, hxW, hfinW⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hfin
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hn : IsNormalScheme W.toScheme :=
    Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion W.ι hnormal
  have hr := Geometry.CurveCompactification.isModification_morphismRestrict f W
  have := hr.sourceIntegral
  have := hr.targetIntegral
  have : IsIso (f ∣_ W) :=
    Geometry.NormalCurveModification.isIso_of_finite_birational (f ∣_ W) hr.birational hn
  exact hx (Geometry.ModificationCenter.le_isomorphismOpen_of_isIso f W hxW)

omit [∀ s : S, PreValuationRing (S.presheaf.stalk s)] [IsIntegral C] [IsIntegral C']
  [IsModification f] in
/-- **Localizing at a point of the modification locus** (blueprint `lem:sm-bd-localize`(2);
Temkin, T:3110–3114): if `Z(f)` is finite and its points are closed in their fibres, every
`x` (in Temkin's use `x ∈ Z(f)`) has an open neighbourhood `U` in which `Z(f)` consists of the
generizations of `x`, and
the only such generization in the fibre of `x` is `x` itself. -/
theorem exists_isOpen_inter_center_eq (hfin : (center f : Set C).Finite)
    (hcl : ∀ z ∈ center f, IsClosed ({⟨z, rfl⟩} : Set (φ ⁻¹' {φ z}))) (x : C) :
    ∃ U : C.Opens, x ∈ U ∧ (center f : Set C) ∩ U = {z | z ∈ center f ∧ z ⤳ x} ∧
      ∀ z ∈ center f, z ⤳ x → φ z = φ x → z = x := by
  let F : Set C := {z | z ∈ center f ∧ ¬ z ⤳ x}
  have hF : F.Finite := hfin.subset fun z hz => hz.1
  let U : C.Opens := ⟨(⋃ z ∈ F, closure ({z} : Set C))ᶜ,
    (hF.isClosed_biUnion fun _ _ => isClosed_closure).isOpen_compl⟩
  have hU : ∀ w, w ∈ U ↔ ∀ z ∈ F, ¬ z ⤳ w := by
    intro w
    change w ∈ (⋃ z ∈ F, closure ({z} : Set C))ᶜ ↔ _
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists, specializes_iff_mem_closure]
  refine ⟨U, (hU x).2 fun z hz hzx => hz.2 hzx, ?_, fun z hz hzx hφ => ?_⟩
  · ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hw, hwU⟩
      refine ⟨hw, ?_⟩
      by_contra hwx
      exact (hU w).1 hwU w ⟨hw, hwx⟩ specializes_rfl
    · rintro ⟨hw, hwx⟩
      refine ⟨hw, (hU w).2 fun z hz hzw => hz.2 (hzw.trans hwx)⟩
  · -- `z` is closed in the fibre of `x`, which contains its specialization `x`
    have hxz : (⟨x, hφ.symm⟩ : φ ⁻¹' {φ z}) ∈ closure {(⟨z, rfl⟩ : φ ⁻¹' {φ z})} := by
      rw [← specializes_iff_mem_closure]
      exact IsInducing.subtypeVal.specializes_iff.1 hzx
    rw [(hcl z hz).closure_eq, Set.mem_singleton_iff] at hxz
    exact (congrArg Subtype.val hxz).symm

end Locus

section Connected

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C C' : Scheme.{u}}
  (p : C ⟶ Spec (CommRingCat.of V)) (f : C' ⟶ C)

/-- **The fibres of `f` over the modification locus are connected** (Zariski's connectedness
theorem over a valuation ring of finite height, lane COH3E): `V` with finitely many primes, all
`Frac(V/𝔭)` separably closed and infinite residue field, `p` projective and of finite presentation
with `C` integral, normal, of relative dimension one, and `f` birational, projective relative to
`p`, with `C'` integral and flat over `V`. -/
theorem isConnected_preimage_of_isProjectiveOver [IsIntegral C] [IsIntegral C']
    [LocallyOfFinitePresentation p] [Flat (f ≫ p)] [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hp : IsProjectiveOver p) (hfp : DeJong.IsRelativelyProjective p f) (hnormal : IsNormalScheme C)
    (hbir : Scheme.BirationalOver f (𝟙 C))
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1) (x : C) :
    _root_.IsConnected (f ⁻¹' {x}) :=
  Cohomology.ConnectedBirationalHeight.isConnected_preimage_singleton_of_isProjectiveOver f p hsep
    hp hfp hnormal hbir hcurve x

end Connected

end DeJongAlterations.StableModification.BlowDown
