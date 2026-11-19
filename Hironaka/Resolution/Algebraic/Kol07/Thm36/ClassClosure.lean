/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.AffineCover
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Hironaka.Scheme.Snc.RelativeDimensionConstant
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Hironaka.Scheme.DisjointIntegralComponents
public import Hironaka.Scheme.ReducedEquidimensional
/-!
# Closure properties of the classes of inputs

The functorial resolution theorem `AlgebraicGeometry.exists_functorial_resolution` is stated on the
class `IsReducedEquidimensional k X` of reduced schemes whose smooth locus over `k` is smooth of
one relative dimension (`Hironaka.Scheme.Resolution.Defs`). The descent of
[Kol07, Proposition 37] constructs the resolution functor from the affine cover `X' = ∐ Uᵢ → X`
through the kernel pair `X'' = X' ×_X X'`, so `Hironaka.Resolution.Algebraic.Kol07.Thm36.BR` needs
`X'` and `X''` in the class whenever `X` is, and the affine functoriality
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineFunctoriality`) needs the coproducts of its
charts in the class. The second part of this file proves these closure properties:

* `IsReducedEquidimensional.of_isOpenImmersion`: open subschemes over `k`
  (`smoothOfRelativeDimension_of_isOpenImmersion`: the smooth locus of an open subscheme is the
  preimage of the smooth locus, `preimage_smoothLocus_eq`, and the restricted open immersion is
  étale);
* `IsReducedEquidimensional.of_openCover`: a scheme covered by reduced opens whose smooth loci have
  ONE common relative dimension `d` (`SmoothOfRelativeDimension d` is Zariski-local at the source);
* `IsReducedEquidimensional.of_openCover_of_isOpenImmersion`, `.sigma`: a scheme covered by open
  subschemes of ONE member, over `k`, and in particular a disjoint union `∐ Wᵢ` of open subschemes
  of one member — the class is NOT closed under arbitrary disjoint unions (a point and a line);
* `IsReducedEquidimensional.affineCoverScheme`, `.affineCoverPair`: Kollár's `X'` and `X''`;
* `isReducedEquidimensional_of_isIntegral`: an integral algebraic `k`-scheme is a member.

The first part of the file is the corresponding closure theory of the class
`HasDisjointIntegralComponents X` of reduced schemes with pairwise disjoint irreducible components,
finite disjoint unions of integral schemes, used by Hironaka's Main Theorems on regular schemes
(`Hironaka.Resolution.Algebraic.Hir64`). The same descent needs `X'` and `X''` in the
class whenever `X` is, and the components' open neighbourhoods `irreducibleComponentOpen` in the
class too. This file proves the closure properties:

* `HasDisjointIntegralComponents.of_isOpenImmersion`: open subschemes (the components of an open
  subspace are the traces of the components meeting it,
  `exists_eq_preimage_of_mem_irreducibleComponents`);
* `HasDisjointIntegralComponents.of_openCover_of_pairwise_disjoint`: a scheme covered by pairwise
  disjoint open subschemes in the class (an irreducible set inside such a cover lies in one member,
  `subset_of_isPreirreducible_of_pairwise_disjoint`);
* `HasDisjointIntegralComponents.sigma`: disjoint unions `∐ Z` (Mathlib's `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`);
* `HasDisjointIntegralComponents.affineCoverScheme`, `.affineCoverPair`: Kollár's `X'` and `X''`
  (the affine opens, respectively their pairwise fibre products, are open subschemes of `X`);
* the component lemmas: `irreducibleComponentOpen_eq`, on the class Mathlib's open neighbourhood of
  a component IS the component; `support_irreducibleComponentIdeal`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme Topology

namespace Hironaka.Resolution

/-! ### Irreducible components under open embeddings and disjoint covers (topology) -/

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every irreducible component of the source of an open embedding is the preimage of an
irreducible component of the target. -/
theorem exists_eq_preimage_of_mem_irreducibleComponents {f : Y → X} (hf : IsOpenEmbedding f)
    {D : Set Y} (hD : D ∈ irreducibleComponents Y) :
    ∃ C ∈ irreducibleComponents X, D = f ⁻¹' C := by
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (f '' D)
    (hD.1.image f hf.continuous.continuousOn)
  refine ⟨C, hC, ?_⟩
  have hD' : D ⊆ f ⁻¹' C := Set.image_subset_iff.mp hsub
  have hirr : IsIrreducible (f ⁻¹' C) := ⟨hD.1.1.mono hD', hC.1.2.preimage hf⟩
  exact hD'.antisymm (hD.2 hirr hD')

/-- A preirreducible set inside a union of pairwise disjoint open sets that meets one of them lies
in it. -/
theorem subset_of_isPreirreducible_of_pairwise_disjoint {ι : Type*} {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) (hd : Pairwise fun i j => Disjoint (U i) (U j))
    (hcov : ∀ x, ∃ i, x ∈ U i) {S : Set X} (hS : IsPreirreducible S) {i : ι}
    (hi : (S ∩ U i).Nonempty) : S ⊆ U i := by
  intro x hx
  obtain ⟨j, hj⟩ := hcov x
  by_cases hij : i = j
  · exact hij ▸ hj
  · exfalso
    obtain ⟨z, -, hzi, hzj⟩ := hS (U i) (U j) (hU i) (hU j) hi ⟨x, hx, hj⟩
    exact Set.disjoint_left.mp (hd hij) hzi hzj

end Topology

end Hironaka.Resolution

/-! ### The class is closed under open subschemes, disjoint covers and disjoint unions -/

namespace AlgebraicGeometry.Scheme.HasDisjointIntegralComponents

open Hironaka.Resolution

/-- An open subscheme of a member of the class is in the class: reducedness is local, and two
components of `Y` meeting are the traces of two components of `X` meeting. -/
theorem of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (hX : HasDisjointIntegralComponents X) : HasDisjointIntegralComponents Y := by
  have := hX.1
  refine ⟨isReduced_of_isOpenImmersion f, fun D₁ hD₁ D₂ hD₂ hne => ?_⟩
  obtain ⟨C₁, hC₁, rfl⟩ := exists_eq_preimage_of_mem_irreducibleComponents f.isOpenEmbedding hD₁
  obtain ⟨C₂, hC₂, rfl⟩ := exists_eq_preimage_of_mem_irreducibleComponents f.isOpenEmbedding hD₂
  obtain ⟨y, hy₁, hy₂⟩ := hne
  rw [hX.2 C₁ hC₁ C₂ hC₂ ⟨f y, hy₁, hy₂⟩]

/-- A scheme covered by pairwise disjoint open subschemes in the class is in the class: an
irreducible component lies in one member of the cover, and two components meeting lie in the same
member, where they are the images of two meeting components. -/
theorem of_openCover_of_pairwise_disjoint {X : Scheme.{u}} (𝒰 : X.OpenCover)
    (hd : Pairwise fun i j => Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j)))
    (h : ∀ i, HasDisjointIntegralComponents (𝒰.X i)) : HasDisjointIntegralComponents X := by
  have : ∀ i, IsReduced (𝒰.X i) := fun i => (h i).1
  refine ⟨IsReduced.of_openCover _ 𝒰, fun C₁ hC₁ C₂ hC₂ hne => ?_⟩
  obtain ⟨x, hx₁, hx₂⟩ := hne
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  have hcov : ∀ z : X, ∃ j, z ∈ Set.range (𝒰.f j) := fun z => by
    obtain ⟨j, w, hw⟩ := 𝒰.exists_eq z
    exact ⟨j, w, hw⟩
  have hopen : ∀ j, IsOpen (Set.range (𝒰.f j)) := fun j => (𝒰.f j).isOpenEmbedding.isOpen_range
  have hsub₁ : C₁ ⊆ Set.range (𝒰.f i) :=
    subset_of_isPreirreducible_of_pairwise_disjoint hopen hd hcov hC₁.1.2 ⟨_, hx₁, y, rfl⟩
  have hsub₂ : C₂ ⊆ Set.range (𝒰.f i) :=
    subset_of_isPreirreducible_of_pairwise_disjoint hopen hd hcov hC₂.1.2 ⟨_, hx₂, y, rfl⟩
  have hD₁ := preimage_mem_irreducibleComponents hC₁ (𝒰.f i).isOpenEmbedding ⟨_, hx₁, y, rfl⟩
  have hD₂ := preimage_mem_irreducibleComponents hC₂ (𝒰.f i).isOpenEmbedding ⟨_, hx₂, y, rfl⟩
  have heq := (h i).2 _ hD₁ _ hD₂ ⟨y, hx₁, hx₂⟩
  calc C₁ = 𝒰.f i '' (𝒰.f i ⁻¹' C₁) := (Set.image_preimage_eq_of_subset hsub₁).symm
    _ = 𝒰.f i '' (𝒰.f i ⁻¹' C₂) := by rw [heq]
    _ = C₂ := Set.image_preimage_eq_of_subset hsub₂

/-- A disjoint union of members of the class is in the class ("`X' := ∐ Uᵢ`", [Kol07, Proposition
37, proof]). -/
theorem sigma {ι : Type u} (Z : ι → Scheme.{u})
    (h : ∀ i, HasDisjointIntegralComponents (Z i)) : HasDisjointIntegralComponents (∐ Z) := by
  refine .of_openCover_of_pairwise_disjoint (sigmaOpenCover Z) (fun i j hij => ?_) h
  have hd := disjoint_opensRange_sigmaι Z i j hij
  rw [← Opens.coe_disjoint] at hd
  change Disjoint (Set.range (Sigma.ι Z i)) (Set.range (Sigma.ι Z j))
  exact hd

/-- The finite affine cover `X' = ∐ Uᵢ` of a member of the class is in the class [Kol07,
Proposition 37, proof]. -/
theorem affineCoverScheme {X : Scheme.{u}} [CompactSpace X]
    (hX : HasDisjointIntegralComponents X) :
    HasDisjointIntegralComponents (AlgebraicGeometry.affineCoverScheme X) :=
  .sigma _ fun i => .of_isOpenImmersion ((finiteAffineCover X).f i) hX

/-- The kernel pair `X'' = X' ×_X X'` of the affine cover of a member of the class is in the class
("the disjoint union of the `Uᵢ ∩ Uⱼ`", [Kol07, Proposition 37, proof]): it is covered by the
pairwise disjoint open subschemes `Uᵢ ×_X X'` (the base changes of the pieces `Uᵢ → X`), each an
open subscheme of `X'`. -/
theorem affineCoverPair {X : Scheme.{u}} [CompactSpace X]
    (hX : HasDisjointIntegralComponents X) :
    HasDisjointIntegralComponents (AlgebraicGeometry.affineCoverPair X) := by
  -- notation-free: `𝒰` is the cover of `X' = ∐ Uᵢ` by its pieces, `g : X' → X`
  have hopen : ∀ i, IsOpenImmersion
      ((sigmaOpenCover fun i => (finiteAffineCover X).X i).f i ≫
        affineCoverDesc X) := fun i => by
    have e : (sigmaOpenCover fun i => (finiteAffineCover X).X i).f i ≫
        affineCoverDesc X = (finiteAffineCover X).f i :=
      ι_comp_affineCoverDesc X i
    rw [e]
    exact (finiteAffineCover X).map_prop i
  -- each member `Uᵢ ×_X X'` is an open subscheme of `X'` (the base change of `Uᵢ → X`): in the
  -- class
  have hmem : ∀ i : (sigmaOpenCover fun i => (finiteAffineCover X).X i).I₀,
      HasDisjointIntegralComponents (pullback
        ((sigmaOpenCover fun i => (finiteAffineCover X).X i).f i ≫
          affineCoverDesc X) (affineCoverDesc X)) := fun i => by
    have := hopen i
    exact .of_isOpenImmersion (pullback.snd _ _) hX.affineCoverScheme
  -- the members' images are pairwise disjoint: their first projections land in the disjoint `Uᵢ`
  have hcomp : ∀ k : (sigmaOpenCover fun i => (finiteAffineCover X).X i).I₀,
      (Scheme.Pullback.openCoverOfLeft
        (sigmaOpenCover fun i => (finiteAffineCover X).X i)
        (affineCoverDesc X) (affineCoverDesc X)).f k ≫
        pullback.fst (affineCoverDesc X) (affineCoverDesc X) =
      pullback.fst ((sigmaOpenCover fun i => (finiteAffineCover X).X i).f k ≫
          affineCoverDesc X) (affineCoverDesc X) ≫
        (sigmaOpenCover fun i => (finiteAffineCover X).X i).f k := fun k =>
    pullback.lift_fst _ _ _
  have h1 : ∀ (k : (sigmaOpenCover fun i => (finiteAffineCover X).X i).I₀) r,
      pullback.fst (affineCoverDesc X)
        (affineCoverDesc X) ((Scheme.Pullback.openCoverOfLeft
          (sigmaOpenCover fun i => (finiteAffineCover X).X i)
          (affineCoverDesc X) (affineCoverDesc X)).f k r) =
      (sigmaOpenCover fun i => (finiteAffineCover X).X i).f k
        (pullback.fst ((sigmaOpenCover fun i => (finiteAffineCover X).X i).f k ≫
          affineCoverDesc X) (affineCoverDesc X) r) := by
    intro k r
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun φ => φ r) (hcomp k)).trans (Scheme.Hom.comp_apply _ _ _))
  refine .of_openCover_of_pairwise_disjoint
    (Scheme.Pullback.openCoverOfLeft
      (sigmaOpenCover fun i => (finiteAffineCover X).X i)
      (affineCoverDesc X) (affineCoverDesc X))
    (fun i j hij => ?_) (fun i => hmem i)
  change Disjoint (Set.range ((Scheme.Pullback.openCoverOfLeft _ _ _).f i))
    (Set.range ((Scheme.Pullback.openCoverOfLeft _ _ _).f j))
  rw [Set.disjoint_left]
  rintro p ⟨q, rfl⟩ ⟨q', hq'⟩
  have hdisj :=
    disjoint_opensRange_sigmaι (fun i => (finiteAffineCover X).X i) i j hij
  rw [← Opens.coe_disjoint] at hdisj
  have e3 := congrArg (pullback.fst (affineCoverDesc X)
    (affineCoverDesc X)) hq'
  have e := (h1 j q').symm.trans (e3.trans (h1 i q))
  exact Set.disjoint_left.mp hdisj ⟨_, e.symm⟩ ⟨_, rfl⟩

/-! ### The components on the class -/

/-- On the class, Mathlib's open neighbourhood of a component, the complement of the other
components, is the component itself. -/
theorem irreducibleComponentOpen_eq {X : Scheme.{u}} [IsNoetherian X]
    (hX : HasDisjointIntegralComponents X) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    ((X.irreducibleComponentOpen Z : TopologicalSpace.Opens X) : Set X) = Z := by
  ext x
  change x ∈ (⋃₀ (irreducibleComponents X \ {Z}))ᶜ ↔ x ∈ Z
  rw [Set.mem_compl_iff, Set.mem_sUnion]
  constructor
  · intro hx
    by_contra hxZ
    have hmem : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]; trivial
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp hmem
    exact hx ⟨W, ⟨hW, fun hWZ => hxZ ((Set.mem_singleton_iff.mp hWZ) ▸ hxW)⟩, hxW⟩
  · rintro hxZ ⟨W, ⟨hW, hWZ⟩, hxW⟩
    exact hWZ (Set.mem_singleton_iff.mpr (hX.2 W hW Z hZ ⟨x, hxW, hxZ⟩))

/-- An integral scheme is in the class: reduced, with a single irreducible component
(`irreducibleComponents_eq_singleton`). -/
theorem of_isIntegral (X : Scheme.{u}) [IsIntegral X] : HasDisjointIntegralComponents X := by
  refine ⟨inferInstance, fun C₁ h₁ C₂ h₂ _ => ?_⟩
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h₁ h₂
  rw [h₁, h₂]

end AlgebraicGeometry.Scheme.HasDisjointIntegralComponents

namespace Hironaka.Resolution

/-- The support of the reduced ideal of an irreducible component is the component. -/
theorem support_irreducibleComponentIdeal {X : Scheme.{u}} [IsNoetherian X] (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) :
    ((X.irreducibleComponentIdeal Z hZ).support : Set X) = Z :=
  rfl

end Hironaka.Resolution

/-- The kernel pair `X'' = X' ×_X X'` of the finite affine cover is locally of finite type over `k`
(`locallyOfFiniteType_affineCoverPair`), the instance needed to evaluate the affine construction on
it (the condition (37.1) of [Kol07, Proposition 37]). -/
instance Hironaka.Resolution.instLocallyOfFiniteTypeAffineCoverPair (k : Type u) [Field k]
    (X : Scheme.{u}) [CompactSpace X] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    LocallyOfFiniteType (affineCoverPair X ↘ Spec (CommRingCat.of k)) :=
  locallyOfFiniteType_affineCoverPair X k

/-- The kernel pair of the finite affine cover of a separated `X` is affine
(`isAffine_affineCoverPair`), hence quasi-compact over `k`: the instance needed to evaluate the
affine construction on it. -/
instance Hironaka.Resolution.instQuasiCompactAffineCoverPair (k : Type u) [Field k]
    (X : Scheme.{u}) [CompactSpace X] [X.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] :
    QuasiCompact (affineCoverPair X ↘ Spec (CommRingCat.of k)) :=
  haveI : IsAffine (affineCoverPair X) :=
    isAffine_affineCoverPair X k
  inferInstance

/-! ### The class of reduced equidimensional schemes -/

namespace AlgebraicGeometry.Scheme.IsReducedEquidimensional

variable {k : Type u} [Field k]

/-- The smooth locus over `k` of an open subscheme `f : Y ⟶ X`, with `Y` over `k` through
`φ = f ≫ (X ↘ Spec k)`, is smooth of the relative dimension of the smooth locus of `X`: it is the
preimage of the smooth locus of `X` (`preimage_smoothLocus_eq`), and the restriction of `f` to the
smooth loci is an open immersion, étale. -/
theorem smoothOfRelativeDimension_of_isOpenImmersion {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] (f : Y ⟶ X)
    [IsOpenImmersion f] (φ : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation φ]
    (hφ : f ≫ (X ↘ Spec (.of k)) = φ) {d : ℕ}
    [SmoothOfRelativeDimension d ((X ↘ Spec (.of k)).smoothLocus.ι ≫ (X ↘ Spec (.of k)))] :
    SmoothOfRelativeDimension d (φ.smoothLocus.ι ≫ φ) := by
  subst hφ
  set g := X ↘ Spec (.of k)
  have hpre : (f ≫ g).smoothLocus = f ⁻¹ᵁ g.smoothLocus := (f.preimage_smoothLocus_eq g).symm
  have e : (f ≫ g).smoothLocus ≤ f ⁻¹ᵁ g.smoothLocus := hpre.le
  have hoi : IsOpenImmersion (f.resLE g.smoothLocus (f ≫ g).smoothLocus e) := by
    have : IsOpenImmersion (f.resLE g.smoothLocus (f ≫ g).smoothLocus e ≫ g.smoothLocus.ι) := by
      rw [Scheme.Hom.resLE_comp_ι]
      infer_instance
    exact IsOpenImmersion.of_comp _ g.smoothLocus.ι
  have hres : SmoothOfRelativeDimension (0 + d)
      (f.resLE g.smoothLocus (f ≫ g).smoothLocus e ≫ (g.smoothLocus.ι ≫ g)) := inferInstance
  rwa [Nat.zero_add, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc] at hres

/-- An open subscheme over `k` of a member of the class is in the class: reducedness is local, and
the smooth locus is the preimage of the smooth locus
(`smoothOfRelativeDimension_of_isOpenImmersion`). -/
theorem of_isOpenImmersion {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] (f : Y ⟶ X) [IsOpenImmersion f]
    [f.IsOver (Spec (.of k))] (hX : X.IsReducedEquidimensional k) :
    Y.IsReducedEquidimensional k := by
  have := hX.1
  obtain ⟨d, hd⟩ := hX.2
  exact ⟨isReduced_of_isOpenImmersion f, d, smoothOfRelativeDimension_of_isOpenImmersion (k := k) f
    (Y ↘ Spec (.of k)) (HomIsOver.comp_over (f := f) (S := Spec (.of k))) (d := d)⟩

/-- A scheme covered by reduced open subschemes whose smooth loci over `k` all have the relative
dimension `d` is in the class: `SmoothOfRelativeDimension d` is Zariski-local at the source, and
the smooth locus of `X` is covered by its traces on the pieces, each an open subscheme of the smooth
locus of the piece. -/
theorem of_openCover {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (𝒰 : X.OpenCover) (d : ℕ)
    (hred : ∀ i, IsReduced (𝒰.X i))
    (hd : ∀ i, SmoothOfRelativeDimension d
      ((𝒰.f i ≫ (X ↘ Spec (.of k))).smoothLocus.ι ≫ (𝒰.f i ≫ (X ↘ Spec (.of k))))) :
    X.IsReducedEquidimensional k := by
  set g := X ↘ Spec (.of k) with hg
  have := hred
  refine ⟨IsReduced.of_openCover _ 𝒰, d, ?_⟩
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} d) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  set U : X.Opens := g.smoothLocus with hU
  -- the traces `V i := U ∩ Uᵢ` of the pieces on the smooth locus cover it
  let V : 𝒰.I₀ → (U : Scheme.{u}).Opens := fun i => U.ι ⁻¹ᵁ (𝒰.f i).opensRange
  have hV : ⨆ i, V i = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨i, w, hw⟩ := 𝒰.exists_eq (U.ι u)
    exact Opens.mem_iSup.mpr ⟨i, ⟨w, hw⟩⟩
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} d)
    V hV).mpr fun i => ?_
  -- `V i` is an open subscheme of the smooth locus `W` of the piece `Uᵢ`
  set W : (𝒰.X i).Opens := (𝒰.f i ≫ g).smoothLocus with hW
  have hWeq : W = 𝒰.f i ⁻¹ᵁ U := ((𝒰.f i).preimage_smoothLocus_eq g).symm
  have h₁ : Set.range ((V i).ι ≫ U.ι) ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact v.2
  let ℓ₁ : (V i : Scheme.{u}) ⟶ 𝒰.X i := IsOpenImmersion.lift (𝒰.f i) ((V i).ι ≫ U.ι) h₁
  have hℓ₁ : ℓ₁ ≫ 𝒰.f i = (V i).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  have h₂ : Set.range ℓ₁ ⊆ Set.range W.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι, hWeq]
    change 𝒰.f i (ℓ₁ v) ∈ U
    rw [← Scheme.Hom.comp_apply, hℓ₁, Scheme.Hom.comp_apply]
    exact ((V i).ι v).2
  let ℓ : (V i : Scheme.{u}) ⟶ W := IsOpenImmersion.lift W.ι ℓ₁ h₂
  have hℓ : ℓ ≫ W.ι = ℓ₁ := IsOpenImmersion.lift_fac _ _ _
  have hℓ₁oi : IsOpenImmersion ℓ₁ := by
    have : IsOpenImmersion (ℓ₁ ≫ 𝒰.f i) := by
      rw [hℓ₁]
      infer_instance
    exact IsOpenImmersion.of_comp ℓ₁ (𝒰.f i)
  have hℓoi : IsOpenImmersion ℓ := by
    have : IsOpenImmersion (ℓ ≫ W.ι) := by
      rw [hℓ]
      exact hℓ₁oi
    exact IsOpenImmersion.of_comp ℓ W.ι
  have := hd i
  have hcomp : SmoothOfRelativeDimension (0 + d) (ℓ ≫ (W.ι ≫ (𝒰.f i ≫ g))) := inferInstance
  rw [Nat.zero_add, ← Category.assoc, hℓ, ← Category.assoc, hℓ₁, Category.assoc] at hcomp
  exact hcomp

/-- A scheme covered by open subschemes of ONE member `Y`, compatibly over `k`, is in the class:
the pieces are reduced and their smooth loci have the relative dimension of that of `Y`
(`smoothOfRelativeDimension_of_isOpenImmersion`). -/
theorem of_openCover_of_isOpenImmersion {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] (hY : Y.IsReducedEquidimensional k)
    (𝒰 : X.OpenCover) (e : ∀ i, 𝒰.X i ⟶ Y) (hoi : ∀ i, IsOpenImmersion (e i))
    (he : ∀ i, 𝒰.f i ≫ (X ↘ Spec (.of k)) = e i ≫ (Y ↘ Spec (.of k))) :
    X.IsReducedEquidimensional k := by
  have := hY.1
  obtain ⟨d, hd⟩ := hY.2
  refine of_openCover 𝒰 d (fun i => ?_) fun i => ?_
  · have := hoi i
    exact isReduced_of_isOpenImmersion (e i)
  · have := hoi i
    exact smoothOfRelativeDimension_of_isOpenImmersion (k := k) (e i) _ (he i).symm (d := d)

/-- A disjoint union `∐ Wᵢ` of open subschemes `e i : Wᵢ ⟶ Y` of one member `Y`, over `k`
compatibly with the `e i`, is in the class ("`X' := ∐ Uᵢ`", [Kol07, Proposition 37, proof]). -/
theorem sigma {ι : Type u} {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] (W : ι → Scheme.{u}) (e : ∀ i, W i ⟶ Y)
    [∀ i, IsOpenImmersion (e i)] [(∐ W).Over (Spec (.of k))]
    [LocallyOfFiniteType ((∐ W) ↘ Spec (.of k))]
    (hover : ∀ i, Sigma.ι W i ≫ ((∐ W) ↘ Spec (.of k)) = e i ≫ (Y ↘ Spec (.of k)))
    (hY : Y.IsReducedEquidimensional k) : (∐ W).IsReducedEquidimensional k :=
  of_openCover_of_isOpenImmersion hY (sigmaOpenCover W) e
    (fun i => ‹∀ i, IsOpenImmersion (e i)› i) hover

/-- The finite affine cover `X' = ∐ Uᵢ` of a member of the class is in the class [Kol07,
Proposition 37, proof]. -/
theorem affineCoverScheme {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [CompactSpace X]
    (hX : X.IsReducedEquidimensional k) :
    (AlgebraicGeometry.affineCoverScheme X).IsReducedEquidimensional k :=
  sigma _ (finiteAffineCover X).f (fun i => by
    change Sigma.ι _ i ≫ affineCoverDesc X ≫ (X ↘ Spec (.of k)) = _
    rw [← Category.assoc, ι_comp_affineCoverDesc]) hX

/-- The kernel pair `X'' = X' ×_X X'` of the affine cover of a member of the class is in the class
("the disjoint union of the `Uᵢ ∩ Uⱼ`", [Kol07, Proposition 37, proof]): it is covered by the open
subschemes `Uᵢ ×_X X'` of `X'` (the base changes of the pieces `Uᵢ → X`). -/
theorem affineCoverPair {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [CompactSpace X]
    (hX : X.IsReducedEquidimensional k) :
    (AlgebraicGeometry.affineCoverPair X).IsReducedEquidimensional k := by
  set g := affineCoverDesc X with hg
  set 𝒰 := sigmaOpenCover fun i => (finiteAffineCover X).X i with h𝒰
  have hopen : ∀ i, IsOpenImmersion (𝒰.f i ≫ g) := fun i => by
    have e : 𝒰.f i ≫ g = (finiteAffineCover X).f i := ι_comp_affineCoverDesc X i
    rw [e]
    exact (finiteAffineCover X).map_prop i
  have hsnd : ∀ i, IsOpenImmersion (pullback.snd (𝒰.f i ≫ g) g) := fun i => by
    have := hopen i
    infer_instance
  have key : ∀ (j : 𝒰.I₀) (φ : pullback (𝒰.f j ≫ g) g ⟶ pullback g g),
      φ ≫ pullback.fst g g = pullback.fst (𝒰.f j ≫ g) g ≫ 𝒰.f j →
      φ ≫ (pullback.fst g g ≫ (g ≫ (X ↘ Spec (.of k)))) =
        pullback.snd (𝒰.f j ≫ g) g ≫ (g ≫ (X ↘ Spec (.of k))) := by
    intro j φ hφ
    rw [← Category.assoc, hφ, Category.assoc, ← Category.assoc (𝒰.f j) g (X ↘ Spec (.of k)),
      ← Category.assoc (pullback.fst (𝒰.f j ≫ g) g) (𝒰.f j ≫ g) (X ↘ Spec (.of k)),
      pullback.condition, Category.assoc]
  exact of_openCover_of_isOpenImmersion hX.affineCoverScheme
    (Scheme.Pullback.openCoverOfLeft 𝒰 g g) (fun i => pullback.snd (𝒰.f i ≫ g) g) hsnd
    fun i => key i _ (pullback.lift_fst _ _ _)

end AlgebraicGeometry.Scheme.IsReducedEquidimensional

namespace Hironaka.Resolution

/-- An integral scheme locally of finite type over a field `k` of characteristic zero is a member
of the class `IsReducedEquidimensional k X` of the functorial resolution theorem (Kollár's
equidimensional schemes, [Kol07, Notation 64]). It is reduced; the smooth locus of `X` over `k`
contains the generic point (`genericPoint_mem_smoothLocus_of_perfectField`), so it is a nonempty
open subscheme of the integral `X`, itself integral hence preconnected, smooth over `k`
(`preimage_smoothLocus_eq` with `smoothLocus_eq_top_iff`), and of one relative dimension by
`exists_smoothOfRelativeDimension_of_preconnectedSpace`. -/
theorem isReducedEquidimensional_of_isIntegral {k : Type u} [Field k] [CharZero k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsIntegral X] :
    X.IsReducedEquidimensional k := by
  refine ⟨inferInstance, ?_⟩
  set F : X ⟶ Spec (CommRingCat.of k) := X ↘ Spec (CommRingCat.of k) with hF
  have hη : genericPoint X ∈ F.smoothLocus := F.genericPoint_mem_smoothLocus_of_perfectField
  have : Nonempty F.smoothLocus := ⟨⟨genericPoint X, hη⟩⟩
  have : IsIntegral F.smoothLocus := isIntegral_of_isOpenImmersion F.smoothLocus.ι
  have : Smooth (F.smoothLocus.ι ≫ F) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact F.smoothLocus.ι_preimage_self
  exact exists_smoothOfRelativeDimension_of_preconnectedSpace (F.smoothLocus.ι ≫ F)

end Hironaka.Resolution
