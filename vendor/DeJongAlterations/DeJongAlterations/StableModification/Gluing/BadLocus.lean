/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.ValCurves.Modifications
import DeJongAlterations.Geometry.ModificationCenter
import DeJongAlterations.StableModification.Cohomology.ConnectedBirational

/-!
# The bad locus of the normalized refinement is finite (PLAN-T5 node A6)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (T:3243–3266) and Lemma 4.2.1 (`normmodlem`, T:2878–2902). `PLAN-T5.md` §2.2
step 6: on the normalization `N` of the refinement, covered by opens `Oᵢ` carrying modifications
`τᵢ : Bᵢ → Oᵢ` (the strictly semi-stable models, `N|Oᵢ = Nor_{Bᵢ}(Oᵢ)`), the points where `N` is
not semi-stable form a finite set of points algebraic over the base.

We work with an arbitrary open `G ⊆ N` (the "good locus": the semi-stable locus, or the
semi-stable locus of a pair) containing every point at which some `τᵢ` is an isomorphism. This is
all that is used: the bad locus `N ∖ G` is then contained in the union of the modification loci
`localCenter Oᵢ τᵢ` of the `τᵢ`, which are finite and consist of algebraic points by Temkin's
Lemma 4.2.1(ii) (`ValCurves.finite_center`, `ValCurves.fiberTrdeg_eq_zero_of_mem_center`) because
`N` is normal.

## Main results

* `localCenter O τ`: the modification locus of `τ : B → O`, `O ⊆ N` open, as a subset of `N`;
  `isClosed_preimage_localCenter`, `genericPoint_not_mem_localCenter`.
* `fiberTrdeg_eq_zero_of_mem_localCenter`, `finite_localCenter`: it is finite and consists of
  points algebraic over `V`.
* `compl_inter_subset_localCenter`, `finite_compl`, `fiberTrdeg_eq_zero_of_not_mem`: **the bad
  locus `N ∖ G` is finite and consists of algebraic points** (node A6).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace DeJongAlterations.StableModification.Gluing

open Geometry.ModificationCenter ValCurves
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section General

variable {U X Y : Scheme.{u}}

/-- Relative transcendence degrees do not change along open immersions. -/
theorem fiberTrdeg_openImmersion_comp (j : U ⟶ X) [IsOpenImmersion j] (g : X ⟶ Y) (t : U) :
    fiberTrdeg (j ≫ g) t = fiberTrdeg g (j t) := by
  rw [ValCurves.fiberTrdeg_comp, (isAlgebraicAt_iff_fiberTrdeg_eq_zero j t).mp
    isAlgebraicAt_of_isIso_stalkMap, add_zero]

/-- **The locus of a local modification**: for a morphism `τ : B → O` to an open `O ⊆ N`, the
modification locus `center τ ⊆ O` viewed in `N`. -/
def localCenter {N B : Scheme.{u}} (O : N.Opens) (τ : B ⟶ O) : Set N :=
  O.ι '' (center τ : Set O)

variable {N B : Scheme.{u}} (O : N.Opens) (τ : B ⟶ O)

/-- The local modification locus lies in `O`. -/
theorem localCenter_subset : localCenter O τ ⊆ O := by
  rintro _ ⟨t, -, rfl⟩
  exact t.2

/-- The local modification locus is closed in `O`. -/
theorem isClosed_preimage_localCenter :
    IsClosed (((↑) : O → N) ⁻¹' localCenter O τ) := by
  have : ((↑) : O → N) ⁻¹' localCenter O τ = (center τ : Set O) := by
    ext t
    constructor
    · rintro ⟨t', ht', h⟩
      have : t' = t := Subtype.ext h
      exact this ▸ ht'
    · exact fun ht ↦ ⟨t, ht, rfl⟩
  rw [this]
  exact (center τ).isClosed

/-- Outside the local modification locus, `τ` is an isomorphism: a point `z ∈ O` not in
`localCenter O τ` lies in `isomorphismOpen τ`. -/
theorem mem_isomorphismOpen_of_not_mem_localCenter {z : O} (hz : (z : N) ∉ localCenter O τ) :
    z ∈ isomorphismOpen τ := by
  by_contra h
  exact hz ⟨z, h, rfl⟩

/-- The generic point does not lie in the locus of a modification. -/
theorem genericPoint_not_mem_localCenter [IsIntegral N] [IsModification τ] :
    genericPoint N ∉ localCenter O τ := by
  have hmod : IsModification τ := inferInstance
  have := hmod.targetIntegral
  rintro ⟨t, ht, he⟩
  have hgen : genericPoint O.toScheme ∈ isomorphismOpen τ := by
    obtain ⟨⟨y, hy⟩⟩ := nonempty_isomorphismOpen τ
    exact ((genericPoint_spec O.toScheme).mem_open_set_iff (isomorphismOpen τ).isOpen).mpr
      ⟨y, Set.mem_univ y, hy⟩
  have htg : t = genericPoint O.toScheme := by
    apply O.ι.isOpenEmbedding.injective
    rw [he, genericPoint_eq_of_isOpenImmersion]
  exact ht (htg ▸ hgen)

end General

section Valuation

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {N : Scheme.{u}} [IsIntegral N] (pN : N ⟶ Spec (.of V))

omit [IsDomain V] [ValuationRing V] in
/-- The generic point of an open of an integral curve is the generic point of the curve, so the
relative dimension bound restricts to opens. -/
theorem fiberTrdeg_genericPoint_opens (O : N.Opens) [Nonempty O] :
    fiberTrdeg (O.ι ≫ pN) (genericPoint O.toScheme) = fiberTrdeg pN (genericPoint N) := by
  have : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  rw [fiberTrdeg_openImmersion_comp, genericPoint_eq_of_isOpenImmersion]

variable {B : Scheme.{u}} {O : N.Opens} (τ : B ⟶ O) [IsModification τ]

/-- **Points of a local modification locus are algebraic over the base** (Temkin, Lemma 4.2.1(ii),
`ValCurves.fiberTrdeg_eq_zero_of_mem_center`, transported to `N`). -/
theorem fiberTrdeg_eq_zero_of_mem_localCenter (hN : IsNormalScheme N)
    (hdim : fiberTrdeg pN (genericPoint N) ≤ 1) {t : N} (ht : t ∈ localCenter O τ) :
    fiberTrdeg pN t = 0 := by
  have hmod : IsModification τ := inferInstance
  have := hmod.targetIntegral
  have := hmod.sourceIntegral
  have : Nonempty O := (inferInstance : Nonempty O.toScheme)
  obtain ⟨t, ht, rfl⟩ := ht
  have hnO : IsNormalScheme O.toScheme :=
    Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion O.ι hN
  have hdimO : fiberTrdeg (O.ι ≫ pN) (genericPoint O.toScheme) ≤ 1 := by
    rw [fiberTrdeg_genericPoint_opens]
    exact hdim
  have h := fiberTrdeg_eq_zero_of_mem_center (O.ι ≫ pN) hnO hdimO τ ht
  rwa [fiberTrdeg_openImmersion_comp] at h

/-- Points of a local modification locus are algebraic over the base. -/
theorem isAlgebraicAt_of_mem_localCenter (hN : IsNormalScheme N)
    (hdim : fiberTrdeg pN (genericPoint N) ≤ 1) {t : N} (ht : t ∈ localCenter O τ) :
    IsAlgebraicAt pN t :=
  (isAlgebraicAt_iff_fiberTrdeg_eq_zero pN t).mpr
    (fiberTrdeg_eq_zero_of_mem_localCenter pN τ hN hdim ht)

/-- **A local modification locus is finite** over a valuation ring of finite height (Temkin,
Lemma 4.2.1(ii), `ValCurves.finite_center`). -/
theorem finite_localCenter [Finite (PrimeSpectrum V)] [IsProper pN] (hN : IsNormalScheme N)
    (hdim : fiberTrdeg pN (genericPoint N) ≤ 1) : (localCenter O τ).Finite := by
  have hmod : IsModification τ := inferInstance
  have := hmod.targetIntegral
  have := hmod.sourceIntegral
  have : Nonempty O := (inferInstance : Nonempty O.toScheme)
  have : Finite (Spec (.of V)) := inferInstanceAs (Finite (PrimeSpectrum V))
  have : TopologicalSpace.NoetherianSpace N :=
    Cohomology.ConnectedBirational.noetherianSpace_of_finite pN
  have : TopologicalSpace.NoetherianSpace O.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (O : Set N))
  have hnO : IsNormalScheme O.toScheme :=
    Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion O.ι hN
  have hdimO : fiberTrdeg (O.ι ≫ pN) (genericPoint O.toScheme) ≤ 1 := by
    rw [fiberTrdeg_genericPoint_opens]
    exact hdim
  exact (finite_center (O.ι ≫ pN) hnO hdimO τ).image _

end Valuation

section BadLocus

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {N : Scheme.{u}} [IsIntegral N] (pN : N ⟶ Spec (.of V))
variable {ι : Type*} (O : ι → N.Opens) {B : ι → Scheme.{u}} (τ : ∀ i, B i ⟶ O i)
  (G : N.Opens)

omit [IsIntegral N] in
/-- **The bad locus is covered by the local modification loci**: if `G ⊆ N` contains every point
where some `τᵢ` is an isomorphism, then `(N ∖ G) ∩ Oᵢ ⊆ localCenter Oᵢ τᵢ`. -/
theorem compl_inter_subset_localCenter (hG : ∀ i, (O i).ι ''ᵁ isomorphismOpen (τ i) ≤ G) (i : ι)
    {z : N} (hz : z ∉ G) (hzO : z ∈ O i) : z ∈ localCenter (O i) (τ i) := by
  by_contra h
  have h' := mem_isomorphismOpen_of_not_mem_localCenter (O i) (τ i) (z := ⟨z, hzO⟩) h
  exact hz (hG i ⟨⟨z, hzO⟩, h', rfl⟩)

/-- **The bad locus `Σ = N ∖ G` is finite** (`PLAN-T5.md` §2.2 step 6, node A6): `N` is covered by
finitely many opens `Oᵢ` with modifications `τᵢ : Bᵢ → Oᵢ`, and `G` contains the loci where the
`τᵢ` are isomorphisms; then `N ∖ G` lies in the union of the (finite) modification loci. -/
theorem finite_compl [Finite (PrimeSpectrum V)] [IsProper pN] (hN : IsNormalScheme N)
    (hdim : fiberTrdeg pN (genericPoint N) ≤ 1) [Finite ι] (hO : ⨆ i, O i = ⊤)
    [∀ i, IsModification (τ i)] (hG : ∀ i, (O i).ι ''ᵁ isomorphismOpen (τ i) ≤ G) :
    ((G : Set N)ᶜ).Finite := by
  refine (Set.finite_iUnion fun i ↦ finite_localCenter pN (τ i) hN hdim).subset fun z hz ↦ ?_
  have hzt : z ∈ (⊤ : N.Opens) := trivial
  rw [← hO] at hzt
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hzt
  exact Set.mem_iUnion.mpr ⟨i, compl_inter_subset_localCenter O τ G hG i hz hi⟩

/-- **The bad locus consists of points algebraic over the base** (node A6). -/
theorem fiberTrdeg_eq_zero_of_not_mem (hN : IsNormalScheme N)
    (hdim : fiberTrdeg pN (genericPoint N) ≤ 1) (hO : ⨆ i, O i = ⊤)
    [∀ i, IsModification (τ i)] (hG : ∀ i, (O i).ι ''ᵁ isomorphismOpen (τ i) ≤ G) {z : N}
    (hz : z ∉ G) : fiberTrdeg pN z = 0 := by
  have hzt : z ∈ (⊤ : N.Opens) := trivial
  rw [← hO] at hzt
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hzt
  exact fiberTrdeg_eq_zero_of_mem_localCenter pN (τ i) hN hdim
    (compl_inter_subset_localCenter O τ G hG i hz hi)

end BadLocus

end DeJongAlterations.StableModification.Gluing
