/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ContractionDimension
import DeJongAlterations.StableModification.CurvesField.OrdinaryGluing

/-!
# Exceptional blow-downs are semi-stable (Temkin, Lemma 4.4.5)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), §4.4,
T:3172–3186: an *exceptional blow-down* of a semi-stable modification `(C', D') → (C, D)` is a
normal modification `C'' → C` dominated by `C'` such that `C' → C''` contracts exactly one point of
`Γ₀(C')`, which is an exceptional component; Lemma 4.4.5 says that `(C'', D'')` is semi-stable.

In the de Jong route all curves are projective over a valuation ring `V` of finite height, and a
point of `Γ₀(C')` is the generic point of a component `Z` of the closed fibre `C'_{s₀}` (closed
points of a proper `V`-curve lie over the closed point `s₀`). We prove Lemma 4.4.5 for a
modification `b : X → Y` of projective `V`-curves which contracts exactly the component `Z` of
the closed fibre `X_{s₀}`, in the sense that a component of `X_{s₀}` is mapped to a point by
`b_{s₀}` iff it is `Z` (`ContractsExactly`), with `Z` an exceptional component in the
combinatorial sense of Temkin's Appendix B (a `ℙ¹`-tree `{Z}` with `|∂Z| + m ≤ 2`, `m` the number
of marks on `Z`). The proof is Temkin's (blueprint `lem:sm-bdg-exceptional-blowdown`,
`sm-blow-down-global.tex`):

* the points of `Y_{s₀}` over the modification locus `Z(b)` are exactly `x = b(Z)`, and
  `b_{s₀}⁻¹(x) = Z` (`center_inter_closedFibre`, `contractedPoint_criterion`);
* the fibrewise stability criterion (Lemma 4.4.2, lane T44A2's `stability_criterion_fibre_iff`)
  for the single point `x` shows that `x` is a smooth point or an ordinary double point of
  `Y_{s₀}`, with at most one mark, and smooth if it carries one
  (`contractedPoint_criterion`);
* semi-stability is open (Lemma 5.1(i), lane SS2's `exists_isNodalCurve_nbhd`, for which the
  geometric fibres of `Y` have pure dimension one, `pureOneDimensionalFibres_of_isNodalCurve_comp`),
  `b` is an isomorphism off `Z(b)`, the closed points of `Y` lie over `s₀`, and `Z(b)` meets the
  closed fibre only in `x`; so `Y → Spec V` is a nodal curve (`isNodalCurve_of_contractsExactly`).

The marks part of semi-stability of `(C'', D'')` (`D''` étale and in the smooth locus) is not
treated in this file.
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus
open Geometry.ModificationCenter (isomorphismOpen center)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Graph

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [CompactSpace X] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [LocallyOfFinitePresentation q]
  (hdim : topologicalKrullDim X ≤ 1)

omit [LocallyOfFinitePresentation q]

open scoped Classical in
/-- The incidence graph along a set only depends on the set (transport of the `Fintype`
instances). -/
theorem nodalGraph_isP1Tree_congr {Z₁ Z₂ : Set X} (h : Z₁ = Z₂) [i₁ : Fintype (nodesIn q Z₁)]
    [i₂ : Fintype (nodesIn q Z₂)] (Y : Finset X) :
    (nodalGraph q hdim Z₁).IsP1Tree Y ↔ (nodalGraph q hdim Z₂).IsP1Tree Y := by
  subst h
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  rfl

open scoped Classical in
/-- The boundary in the incidence graph along a set only depends on the set. -/
theorem nodalGraph_boundary_card_congr {Z₁ Z₂ : Set X} (h : Z₁ = Z₂)
    [i₁ : Fintype (nodesIn q Z₁)] [i₂ : Fintype (nodesIn q Z₂)] (Y : Finset X) :
    ((nodalGraph q hdim Z₁).boundary Y).card = ((nodalGraph q hdim Z₂).boundary Y).card := by
  subst h
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  rfl

end Graph

section Dominant

variable {S X : Scheme.{u}} [IrreducibleSpace S] (g : X ⟶ S) [Flat g]

/-- A flat morphism from a nonempty scheme to an irreducible scheme hits the generic point. -/
theorem genericPoint_mem_range_of_flat [Nonempty X] : genericPoint S ∈ Set.range g := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hgen : GeneralizingMap g := Flat.generalizingMap g
  obtain ⟨x', -, hx'⟩ := hgen ((genericPoint_spec S).specializes (Set.mem_univ (g x)))
  exact ⟨x', hx'⟩

/-- A flat morphism from a nonempty scheme to an irreducible scheme is dominant. -/
theorem isDominant_of_flat [Nonempty X] : IsDominant g := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (genericPoint_spec S).def]
  exact closure_mono (Set.singleton_subset_iff.2 (genericPoint_mem_range_of_flat g))

/-- The generic fibre of a flat morphism from a nonempty scheme is nonempty. -/
theorem nonempty_fiber_genericPoint_of_flat [Nonempty X] : Nonempty (g.fiber (genericPoint S)) := by
  obtain ⟨x, hx⟩ := genericPoint_mem_range_of_flat g
  have : x ∈ Set.range (g.fiberι (genericPoint S)) := by
    rw [Scheme.Hom.range_fiberι]
    exact hx
  obtain ⟨z, -⟩ := this
  exact ⟨z⟩

end Dominant

section ClosedFibre

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {X Y : Scheme.{u}}
  (p : Y ⟶ Spec (CommRingCat.of V)) (b : X ⟶ Y)

local notation "s₀" => IsLocalRing.closedPoint V

/-- **`b` contracts exactly the component `Z` of the closed fibre**: a generic point `w` of the
closed fibre `X_{s₀}` is mapped with its closure to a single point by `b_{s₀}` iff `w = Z`. -/
def ContractsExactly (Z : (b ≫ p).fiber s₀) : Prop :=
  ∀ w ∈ genericPoints ((b ≫ p).fiber s₀),
    (Curves.fiberMap b p s₀ '' closure {w}).Subsingleton ↔ w = Z

/-- The image of the closure of a point under a continuous map into a point's preimage. -/
theorem image_closure_subset_singleton {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']
    (f : T → T') (hf : Continuous f) {w : T} {y : T'} (hy : IsClosed ({y} : Set T')) (hw : f w = y) :
    f '' closure {w} ⊆ {y} := by
  rintro _ ⟨z, hz, rfl⟩
  have hsub : closure {w} ⊆ f ⁻¹' {y} :=
    closure_minimal (Set.singleton_subset_iff.2 (show w ∈ f ⁻¹' {y} from hw)) (hy.preimage hf)
  exact hsub hz

variable [IsIntegral Y] [IsIntegral X] [IsModification b] [IsProper p]
  [LocallyOfFinitePresentation p] [Flat p] [DeJong.IsNodalCurve (b ≫ p)]

/-- The contracted point `x = b_{s₀}(Z)` is closed in `Y_{s₀}`. -/
theorem isClosed_contractedPoint {Z : (b ≫ p).fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactly p b Z) : IsClosed ({Curves.fiberMap b p s₀ Z} : Set (p.fiber s₀)) := by
  have himg : Curves.fiberMap b p s₀ '' closure {Z} = {Curves.fiberMap b p s₀ Z} := by
    refine Set.Subsingleton.eq_singleton_of_mem ((hc Z hZ).2 rfl) ?_
    exact ⟨Z, subset_closure rfl, rfl⟩
  rw [← himg]
  exact (Curves.fiberMap b p s₀).isClosedMap _ isClosed_closure

/-- The components of the closed fibre of the nodal `X` are not points. -/
theorem exists_ne_mem_closure_of_mem_genericPoints {Z : (b ≫ p).fiber s₀}
    (hZ : Z ∈ genericPoints _) : ∃ z ∈ closure ({Z} : Set ((b ≫ p).fiber s₀)), z ≠ Z := by
  by_contra h
  push Not at h
  have hcl : closure ({Z} : Set ((b ≫ p).fiber s₀)) = {Z} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨subset_closure rfl, h⟩
  have hZc : IsClosed ({Z} : Set ((b ≫ p).fiber s₀)) := by
    rw [← hcl]
    exact isClosed_closure
  exact not_mem_genericPoints_of_isClosed (pure_fiber_of_nodal (b ≫ p) s₀) hZc hZ

/-- **The contracted point lies in the modification locus.** -/
theorem contractedPoint_mem_center {Z : (b ≫ p).fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactly p b Z) : p.fiberι s₀ (Curves.fiberMap b p s₀ Z) ∈ center b := by
  by_contra hx
  set J : Set (p.fiber s₀) := p.fiberι s₀ ⁻¹' (center b : Set Y) with hJdef
  have hJc : IsClosed J := (center b).isClosed.preimage (p.fiberι s₀).continuous
  let U : (p.fiber s₀).Opens := ⟨Jᶜ, hJc.isOpen_compl⟩
  have hiso : IsIso (Curves.fiberMap b p s₀ ∣_ U) :=
    isIso_fiberMap_restrict_of_center b p s₀ J (fun y => Iff.rfl) U (fun y => Iff.rfl)
  obtain ⟨z, hz, hzZ⟩ := exists_ne_mem_closure_of_mem_genericPoints p b hZ
  have hfz : Curves.fiberMap b p s₀ z = Curves.fiberMap b p s₀ Z :=
    image_closure_subset_singleton _ (Curves.fiberMap b p s₀).continuous
      (isClosed_contractedPoint p b hZ hc) rfl ⟨z, hz, rfl⟩
  have hxU : Curves.fiberMap b p s₀ Z ∈ U := hx
  have hzU : z ∈ Curves.fiberMap b p s₀ ⁻¹ᵁ U := by
    change Curves.fiberMap b p s₀ z ∈ U
    rw [hfz]
    exact hxU
  have hZU : Z ∈ Curves.fiberMap b p s₀ ⁻¹ᵁ U := hxU
  have key : ∀ a : (Curves.fiberMap b p s₀ ⁻¹ᵁ U),
      U.ι ((Curves.fiberMap b p s₀ ∣_ U) a) = Curves.fiberMap b p s₀ a.1 := fun a => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rfl
  have h1 : (Curves.fiberMap b p s₀ ∣_ U) ⟨z, hzU⟩ = (Curves.fiberMap b p s₀ ∣_ U) ⟨Z, hZU⟩ := by
    apply U.ι.isOpenEmbedding.injective
    rw [key, key]
    exact hfz
  have h2 := (Curves.fiberMap b p s₀ ∣_ U).homeomorph.injective h1
  exact hzZ (congrArg Subtype.val h2)

variable [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]

/-- **The points of the closed fibre over the modification locus**: exactly `x = b_{s₀}(Z)`. -/
theorem center_inter_closedFibre (hnormal : IsNormalScheme Y)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1) {Z : (b ≫ p).fiber s₀}
    (hZ : Z ∈ genericPoints _) (hc : ContractsExactly p b Z) (y : p.fiber s₀) :
    p.fiberι s₀ y ∈ center b ↔ y = Curves.fiberMap b p s₀ Z := by
  constructor
  · intro hy
    have hyc := isClosed_singleton_of_mem_center p b s₀ hnormal hcurve y hy
    obtain ⟨v, hvy, hvg⟩ := exists_genericPoints_fiberMap_preimage p b s₀ hnormal
      (topologicalKrullDim_fiber_le_one_of_nodal (b ≫ p) s₀) y hyc hy
    have hsub : (Curves.fiberMap b p s₀ '' closure {v}).Subsingleton :=
      (Set.subsingleton_singleton (a := y)).anti
        (image_closure_subset_singleton _ (Curves.fiberMap b p s₀).continuous hyc hvy)
    rw [(hc v hvg).1 hsub] at hvy
    exact hvy.symm
  · rintro rfl
    exact contractedPoint_mem_center p b hZ hc

/-- The generic points of `X_{s₀}` over `x = b_{s₀}(Z)`: only `Z`. -/
theorem innerPoints_contractedPoint {Z : (b ≫ p).fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactly p b Z) :
    innerPoints (Curves.fiberMap b p s₀) (Curves.fiberMap b p s₀ Z) = {Z} := by
  ext w
  simp only [innerPoints, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hwx⟩
    refine (hc w hw).1 ((Set.subsingleton_singleton (a := Curves.fiberMap b p s₀ Z)).anti ?_)
    exact image_closure_subset_singleton _ (Curves.fiberMap b p s₀).continuous
      (isClosed_contractedPoint p b hZ hc) hwx
  · rintro rfl
    exact ⟨hZ, rfl⟩

section Criterion

variable [Finite (PrimeSpectrum V)] [Infinite (IsLocalRing.ResidueField V)]

open scoped Classical in
/-- **The fibrewise stability criterion at the contracted point** (Temkin Lemma 4.4.2 for the
single point `x = b_{s₀}(Z)`, lane T44A2's `stability_criterion_fibre` and
`stability_criterion_fibre_iff`, with `J = {x}` and `G x = {Z}`, and lane CRV5's
`ordinaryPointCompletion_of_isAlgClosed` for `κ(s₀)`): `b_{s₀}⁻¹(x) = Z`, and if `{Z}` is a
`ℙ¹`-tree with `|∂Z| + m ≤ 2` then `x` is a smooth point or an ordinary double point of `Y_{s₀}`,
`m ≤ 1`, and `x` is smooth if `m = 1`. -/
theorem contractedPoint_criterion
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hp : IsProjectiveOver p) (hbp : DeJong.IsRelativelyProjective p b)
    (hnormal : IsNormalScheme Y) (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1)
    (hη : Curves.IsEtaModification b p) {Z : (b ≫ p).fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactly p b Z)
    (hgZ : 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        ((b ≫ p).fiberToSpecResidueField s₀)) Z)
    (m : ℕ) :
    Curves.fiberMap b p s₀ ⁻¹' {Curves.fiberMap b p s₀ Z} = closure {Z} ∧
    (∀ [Fintype (nodesIn ((b ≫ p).fiberToSpecResidueField s₀) (closure {Z}))],
      (nodalGraph ((b ≫ p).fiberToSpecResidueField s₀)
          (topologicalKrullDim_fiber_le_one_of_nodal (b ≫ p) s₀) (closure {Z})).IsP1Tree
          {Z} →
      ((nodalGraph ((b ≫ p).fiberToSpecResidueField s₀)
          (topologicalKrullDim_fiber_le_one_of_nodal (b ≫ p) s₀)
          (closure {Z})).boundary {Z}).card + m ≤ 2 →
      (DeJong.IsSmoothAt (p.fiberToSpecResidueField s₀) (Curves.fiberMap b p s₀ Z) ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s₀)
          (Curves.fiberMap b p s₀ Z)) ∧
        m ≤ 1 ∧ (m = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s₀)
          (Curves.fiberMap b p s₀ Z))) := by
  set x := Curves.fiberMap b p s₀ Z with hxdef
  have hbir := (inferInstance : IsModification b).birational
  have : IsDominant b := isDominant_of_birationalOver_id b hbir
  have : IsDominant p := isDominant_of_flat p
  have : Nonempty ((b ≫ p).fiber (genericPoint (Spec (CommRingCat.of V)))) :=
    nonempty_fiber_genericPoint_of_flat (b ≫ p)
  have hpure : ∀ W ∈ irreducibleComponents (p.fiber s₀), topologicalKrullDim W = 1 :=
    hasPureFiberDimension_of_isNodalCurve_comp p b
      (one_le_fiberDimension_genericPoint p b hη.isIso_fiberMap) s₀
  have : IsReduced (p.fiber s₀) := isReduced_fiber_closedPoint p b hbp hnormal hbir
  have hdim' := topologicalKrullDim_fiber_le_one_of_nodal (b ≫ p) s₀
  have hp' : IsProjectiveOver (b ≫ p) := DeJong.IsRelativelyProjective.isProjectiveOver hp hbp
  have hps' := isProjectiveOver_fiberToSpecResidueField (b ≫ p) s₀ hp'
  have : CompactSpace X := compactSpace_of_quasiCompact (b ≫ p)
  have : CompactSpace ((b ≫ p).fiber s₀) :=
    compactSpace_of_quasiCompact ((b ≫ p).fiberToSpecResidueField s₀)
  let J : Finset (p.fiber s₀) := {x}
  have hJ : ∀ y, y ∈ J ↔ p.fiberι s₀ y ∈ center b := fun y => by
    rw [Finset.mem_singleton]
    exact (center_inter_closedFibre p b hnormal hcurve hZ hc y).symm
  let G : p.fiber s₀ → Finset ((b ≫ p).fiber s₀) := fun _ => {Z}
  have hG : ∀ y ∈ J, (G y : Set ((b ≫ p).fiber s₀)) = innerPoints (Curves.fiberMap b p s₀) y := by
    intro y hy
    rw [Finset.mem_singleton.1 hy, innerPoints_contractedPoint p b hZ hc]
    simp [G]
  have hg : ∀ y ∈ J, ∀ v ∈ G y, 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        ((b ≫ p).fiberToSpecResidueField s₀)) v := by
    intro y _ v hv
    rw [Finset.mem_singleton.1 hv]
    exact hgZ
  have hJset : Curves.fiberMap b p s₀ ⁻¹' (J : Set (p.fiber s₀)) =
      Curves.fiberMap b p s₀ ⁻¹' {x} := by
    simp [J]
  let hfin : Fintype (nodesIn ((b ≫ p).fiberToSpecResidueField s₀)
      (Curves.fiberMap b p s₀ ⁻¹' (J : Set (p.fiber s₀)))) :=
    (finite_nodesIn _ hdim' hps' _).fintype
  obtain ⟨h1, -, -⟩ := stability_criterion_fibre p b s₀ hsep hp hbp hnormal hcurve hη hpure J hJ G hG
    hdim' hg (fun _ => m)
  -- the contracted fibre is `Z`
  have hset : Curves.fiberMap b p s₀ ⁻¹' {x} = closure {Z} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨v, hv, hzv⟩ := (h1 x (Finset.mem_singleton_self x)).2 z hz
      rw [Finset.mem_singleton.1 hv] at hzv
      exact hzv
    · exact closure_minimal (Set.singleton_subset_iff.2 (show Z ∈ _ from rfl))
        ((isClosed_contractedPoint p b hZ hc).preimage (Curves.fiberMap b p s₀).continuous)
  refine ⟨hset, fun htree hcard => ?_⟩
  have hiff := stability_criterion_fibre_iff p b s₀ hsep hp hbp hnormal hcurve hη hpure J hJ G hG
    hdim' hg (fun _ => m) (CurvesField.OrdinaryGluing.ordinaryPointCompletion_of_isAlgClosed _)
  have hset' : Curves.fiberMap b p s₀ ⁻¹' (J : Set (p.fiber s₀)) = closure {Z} := hJset.trans hset
  have hexc : ∀ y ∈ J, (nodalGraph ((b ≫ p).fiberToSpecResidueField s₀) hdim'
      (Curves.fiberMap b p s₀ ⁻¹' (J : Set (p.fiber s₀)))).IsP1Tree (G y) ∧
      ((nodalGraph ((b ≫ p).fiberToSpecResidueField s₀) hdim'
        (Curves.fiberMap b p s₀ ⁻¹' (J : Set (p.fiber s₀)))).boundary (G y)).card + m ≤ 2 := by
    intro y _
    refine ⟨(nodalGraph_isP1Tree_congr _ hdim' hset' _).2 htree, ?_⟩
    rw [nodalGraph_boundary_card_congr _ hdim' hset']
    exact hcard
  exact hiff.2 hexc x (Finset.mem_singleton_self x)

end Criterion

section Nodal

variable [Finite (PrimeSpectrum V)] [Infinite (IsLocalRing.ResidueField V)]

/-- The closed points of a scheme proper over `Spec V`, `V` local, lie over the closed point. -/
theorem apply_eq_closedPoint_of_isClosed {y : Y} (hy : IsClosed ({y} : Set Y)) :
    p y = IsLocalRing.closedPoint V := by
  have h := p.isClosedMap _ hy
  rw [Set.image_singleton] at h
  have hmax : (p y).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 h
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

/-- **The isomorphism locus of `b` is nodal**: over `isomorphismOpen b`, `Y` is isomorphic to an
open subscheme of the nodal `X`. -/
theorem isNodalCurve_isomorphismOpen :
    DeJong.IsNodalCurve ((isomorphismOpen b).ι ≫ p) := by
  set W := isomorphismOpen b
  have hiso : IsIso (b ∣_ W) := Geometry.ModificationCenter.isIso_restrict_isomorphismOpen b
  have h1 : DeJong.IsNodalCurve ((b ⁻¹ᵁ W).ι ≫ b ≫ p) :=
    Curves.IsNodalCurve.etale_comp (b ⁻¹ᵁ W).ι (b ≫ p)
  have h2 : W.ι ≫ p = inv (b ∣_ W) ≫ (b ⁻¹ᵁ W).ι ≫ b ≫ p := by
    rw [← Category.assoc ((b ⁻¹ᵁ W).ι), ← morphismRestrict_ι, Category.assoc,
      IsIso.inv_hom_id_assoc]
  rw [h2]
  exact Curves.IsNodalCurve.etale_comp (inv (b ∣_ W)) _

open scoped Classical in
/-- **Temkin's Lemma 4.4.5, nodal part** (blueprint `lem:sm-bdg-exceptional-blowdown`): let
`b : X → Y` be a modification of `V`-curves, `Y` integral, normal, projective, flat and of finite
presentation over `V` of relative dimension one, `X` a nodal curve over `V`, `b` projective
relative to `p` and an η-modification, which contracts exactly the component `Z` of the closed
fibre (`ContractsExactly`). If `{Z}` is a `ℙ¹`-tree of the closed fibre with `|∂Z| + m ≤ 2` (an
exceptional component, Temkin's App. B) and its genus is nonnegative, then `Y → Spec V` is a
nodal curve; moreover `m ≤ 1`, and the contracted point is smooth if `m = 1`. -/
theorem isNodalCurve_of_contractsExactly
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hp : IsProjectiveOver p) (hbp : DeJong.IsRelativelyProjective p b)
    (hnormal : IsNormalScheme Y) (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1)
    (hη : Curves.IsEtaModification b p) {Z : (b ≫ p).fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactly p b Z)
    (hgZ : 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        ((b ≫ p).fiberToSpecResidueField s₀)) Z)
    (m : ℕ)
    [Fintype (nodesIn ((b ≫ p).fiberToSpecResidueField s₀) (closure {Z}))]
    (htree : (nodalGraph ((b ≫ p).fiberToSpecResidueField s₀)
      (topologicalKrullDim_fiber_le_one_of_nodal (b ≫ p) s₀) (closure {Z})).IsP1Tree {Z})
    (hcard : ((nodalGraph ((b ≫ p).fiberToSpecResidueField s₀)
      (topologicalKrullDim_fiber_le_one_of_nodal (b ≫ p) s₀)
      (closure {Z})).boundary {Z}).card + m ≤ 2) :
    DeJong.IsNodalCurve p ∧ m ≤ 1 ∧
      (m = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s₀) (Curves.fiberMap b p s₀ Z)) := by
  set x := Curves.fiberMap b p s₀ Z with hxdef
  obtain ⟨-, hcrit⟩ := contractedPoint_criterion p b hsep hp hbp hnormal hcurve hη hZ hc hgZ m
  obtain ⟨hxnode, hm, hm1⟩ := hcrit htree hcard
  refine ⟨?_, hm, hm1⟩
  have hbir := (inferInstance : IsModification b).birational
  have : IsDominant b := isDominant_of_birationalOver_id b hbir
  have : IsDominant p := isDominant_of_flat p
  have : Nonempty ((b ≫ p).fiber (genericPoint (Spec (CommRingCat.of V)))) :=
    nonempty_fiber_genericPoint_of_flat (b ≫ p)
  have hpure := pureOneDimensionalFibres_of_isNodalCurve_comp p b hη.isIso_fiberMap
  have hxc := isClosed_contractedPoint p b hZ hc
  obtain ⟨Ux, hxUx, hUx⟩ := (exists_isNodalCurve_nbhd_iff p s₀ hpure x hxc).2 hxnode
  have : CompactSpace Y := compactSpace_of_quasiCompact p
  apply Curves.IsNodalCurve.of_openCover
  intro y
  obtain ⟨y₀, hy₀, hy₀c⟩ := (isClosed_closure (s := ({y} : Set Y))).exists_closed_singleton
    (Set.singleton_nonempty y).closure
  have hyy₀ : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
  have hps : y₀ ∈ Set.range (p.fiberι s₀) := by
    rw [Scheme.Hom.range_fiberι]
    exact apply_eq_closedPoint_of_isClosed p hy₀c
  obtain ⟨t, rfl⟩ := hps
  by_cases htx : t = x
  · subst htx
    exact ⟨Ux, hyy₀.mem_open Ux.isOpen hxUx, hUx⟩
  · have hiso : p.fiberι s₀ t ∈ isomorphismOpen b := by
      by_contra h
      exact htx ((center_inter_closedFibre p b hnormal hcurve hZ hc t).1 h)
    exact ⟨isomorphismOpen b, hyy₀.mem_open (isomorphismOpen b).isOpen hiso,
      isNodalCurve_isomorphismOpen p b⟩

end Nodal

end ClosedFibre


end

end DeJongAlterations.StableModification.BlowDown
