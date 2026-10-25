/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.StabilityFibre
import DeJongAlterations.StableModification.BlowDown.StabilityTop
import DeJongAlterations.StableModification.BlowDown.NodalReduced
import DeJongAlterations.StableModification.BlowDown.FibreIso
import DeJongAlterations.StableModification.BlowDown.Genus
import DeJongAlterations.StableModification.BlowDown.Normalization
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight
import DeJongAlterations.StableModification.ValCurves.Modifications
import DeJongAlterations.StableModification.BlowDown.Localize

/-!
# The stability criterion, fibrewise form (Temkin, Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Lemma 4.4.2
(`stabcritlem`, T:3106–3133): let `C` be a normal `S`-curve, `S = Spec V`, `f : C′ → C` a
modification and `x ∈ C` such that `Z = f⁻¹(x)` is a curve in the semi-stable locus of `C′`. Then
`(C, D)` is semi-stable at `x` iff `Z` is an exceptional `ℙ¹`-tree.

We prove it in the fibrewise form of blueprint `lem:sm-stability-criterion` (chapter
`sm-blow-down-criterion.tex`): `C` and `C′` projective over `V`, `C′` nodal, and **all points
`x_1, …, x_l` of the modification locus `Z(f)` in a fibre `C_s` at once** (ERRATA DJA-O12,
`rem:sm-bd-literature`(4)). The scheme-level inputs are:

* the fibres `C_s = p.fiber s`, `C′_s` are reduced (`C′_s` by `lem:sm-bd-nodal-reduced`, `C_s` an
  explicit instance hypothesis, discharged at the closed point by
  `isReduced_fiber_closedPoint`: prop:sm-normalization-reduced(3)), projective over the
  algebraically closed `κ(s)`, of dimension at most one, and `p_a(C′_s) = p_a(C_s)` (T44A's
  `arithmeticGenus_fibre_eq_of_isProjectiveOver`);
* the points of `C_s` over `Z(f)` are closed (lane T42's Lemma 4.2.1(ii)), not generic (pure
  dimension one) and `f_s` is an isomorphism off their fibres (`lem:sm-bd-fibre-iso`);
* the contracted fibres `Z_x = f_s⁻¹(x)` are connected (Zariski's connectedness theorem, lane
  COH3E's `isConnected_preimage_singleton_of_isProjectiveOver`) and, being curves (Temkin's
  hypothesis "`Z` is a curve": `Z` contains a component of `C′_s`), unions of components of `C′_s`.

Then the fibre-level criterion `stabdown_finset_exceptional_of_semistable`,
`stabdown_finset_ordinary_of_exceptional`, `stabdown_finset_semistable_iff` applies to
`f_s : C′_s → C_s`.

## Main results

* `stability_criterion_fibre` (blueprint `lem:sm-stability-criterion`): every `Z_x` is a connected
  union of components; if every `x` is a smooth point or an ordinary double point of `C_s` with
  at most one mark, and only a smooth point if it carries one, then every `Z_x` is an exceptional
  `ℙ¹`-tree; conversely, if every `Z_x` is an exceptional `ℙ¹`-tree, then every `x` is an ordinary
  point with at most two branches, at most one mark, and one branch if it carries a mark.
* `stability_criterion_fibre_iff`: the equivalence, assuming `OrdinaryPointCompletion κ(s)` (the
  converse of `lem:sm-ordinary-completion`, not formalized).
* `exists_finset_center`, `exists_innerFinset`, `topologicalKrullDim_fiber_le_one_of_isNodalCurve`:
  the data of the statement exist.
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

universe u

noncomputable section

section FibreInstances

/-! ### Properties of the fibres -/

variable {S C C' : Scheme.{u}} (p : C ⟶ S) (s : S)

/-- The fibre of a separated morphism is separated over the residue field. -/
instance isSeparated_fiberToSpecResidueField [IsSeparated p] :
    IsSeparated (p.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd (P := @IsSeparated) _ _ ‹_›

/-- The fibre of a morphism locally of finite type is locally of finite type over the residue
field. -/
instance locallyOfFiniteType_fiberToSpecResidueField [LocallyOfFiniteType p] :
    LocallyOfFiniteType (p.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ ‹_›

/-- The fibre of a separated morphism has affine diagonal. -/
instance isAffineHom_diagonal_fiber [IsSeparated p] :
    IsAffineHom (pullback.diagonal (terminal.from (p.fiber s))) := by
  have := isSeparated_fiberToSpecResidueField p s
  exact isAffineHom_diagonal_of_isSeparated (p.fiberToSpecResidueField s)

/-- The fibre of a quasi-compact morphism locally of finite type is a Noetherian space. -/
theorem noetherianSpace_fiber [LocallyOfFiniteType p] [QuasiCompact p] :
    NoetherianSpace (p.fiber s) := by
  have : IsLocallyNoetherian (p.fiber s) := inferInstanceAs (IsLocallyNoetherian (pullback _ _))
  have : IsNoetherian (p.fiber s) := {}
  infer_instance

/-- The fibre of a quasi-compact morphism locally of finite type has finitely many generic
points. -/
instance finite_genericPoints_fiber [LocallyOfFiniteType p] [QuasiCompact p] :
    Finite (genericPoints (p.fiber s)) := by
  have := noetherianSpace_fiber p s
  exact (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).to_subtype

/-- The points of `p.fiber s` lie over `s`. -/
theorem apply_fiberι (x : p.fiber s) : p (p.fiberι s x) = s := by
  have : p.fiberι s x ∈ p ⁻¹' {s} := by
    rw [← Scheme.Hom.range_fiberι]
    exact ⟨x, rfl⟩
  exact this

/-- The fibre map of a proper morphism is proper. -/
instance isProper_fiberMap (f : C' ⟶ C) [IsProper f] : IsProper (Curves.fiberMap f p s) := by
  unfold Curves.fiberMap
  rw [Curves.pullbackCompMap_eq]
  infer_instance

/-- The fibre of the fibre map over a point `x` of `C_s` is the set of points of `C'_s` lying
over the image of `x` in `C`. -/
theorem fiberMap_preimage_singleton (f : C' ⟶ C) (x : p.fiber s) :
    Curves.fiberMap f p s ⁻¹' {x} = (f ≫ p).fiberι s ⁻¹' (f ⁻¹' {p.fiberι s x}) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← Scheme.Hom.comp_apply, ← Curves.fiberMap_fiberι, Scheme.Hom.comp_apply]
  exact ⟨fun h => h ▸ rfl, fun h => (p.fiberι s).isEmbedding.injective h⟩

/-- **The contracted fibres in `C'_s` are connected** if the fibres of `f` are: `C'_s → C'` is
an embedding onto the points over `s`. -/
theorem isConnected_fiberMap_preimage (f : C' ⟶ C) (x : p.fiber s)
    (h : _root_.IsConnected (f ⁻¹' {p.fiberι s x})) :
    _root_.IsConnected (Curves.fiberMap f p s ⁻¹' {x}) := by
  rw [fiberMap_preimage_singleton]
  refine isConnected_preimage_of_isEmbedding ((f ≫ p).fiberι s).isEmbedding ?_ h
  intro y hy
  rw [Scheme.Hom.range_fiberι, Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply,
    show f y = p.fiberι s x from hy]
  exact apply_fiberι p s x

/-- **Points of the fibre with algebraic residue field are closed in the fibre.** -/
theorem isClosed_singleton_fiber_of_isAlgebraicAt [IsSeparated p] (x : p.fiber s)
    (h : ValCurves.IsAlgebraicAt p (p.fiberι s x)) : IsClosed ({x} : Set (p.fiber s)) := by
  have hps : p (p.fiberι s x) = s := apply_fiberι p s x
  have h1 := ValCurves.isClosed_singleton_preimage_of_isAlgebraicAt p hps h
  rw [← (p.fiberHomeo s).isClosed_image, Set.image_singleton]
  have : p.fiberHomeo s x = ⟨p.fiberι s x, hps⟩ := Subtype.ext rfl
  rw [this]
  exact h1

end FibreInstances

section Transport

/-! ### Fibres over `Spec κ(s)` and over `Spec.map (V → κ(s))` -/

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- Projectivity of a base change only depends on the base map (transport along `a = a'`). -/
theorem isProjectiveOver_pullback_snd_congr {κ : Type u} [CommRing κ]
    {a a' : Spec (CommRingCat.of κ) ⟶ S} (h : a = a') (hp : IsProjectiveOver (pullback.snd p a)) :
    IsProjectiveOver (pullback.snd p a') := by
  subst h
  exact hp

/-- The arithmetic genus of a base change only depends on the base map (transport along
`a = a'`). -/
theorem arithmeticGenus_pullback_congr {κ : Type u} [Field κ]
    {a a' : Spec (CommRingCat.of κ) ⟶ S} (h : a = a') [CompactSpace ↥(pullback p a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback p a)))]
    [CompactSpace ↥(pullback p a')]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback p a')))] :
    arithmeticGenus (pullback p a) (structureCoeff (pullback.snd p a)) =
      arithmeticGenus (pullback p a') (structureCoeff (pullback.snd p a')) := by
  subst h
  rfl

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C C' : Scheme.{u}}
  (p : C ⟶ Spec (CommRingCat.of V)) (f : C' ⟶ C) (s : Spec (CommRingCat.of V))

omit [IsDomain V] [ValuationRing V] in
/-- **The fibre of a projective `V`-scheme is projective over `κ(s)`.** -/
theorem isProjectiveOver_fiberToSpecResidueField (hp : IsProjectiveOver p) :
    IsProjectiveOver (k := ↑((Spec (CommRingCat.of V)).residueField s))
      (p.fiberToSpecResidueField s) :=
  isProjectiveOver_pullback_snd_congr p (fromSpecResidueField_eq_specMap s).symm
    (Connected.isProjectiveOver_bcSnd (residueFieldPoint s) hp)

/-- **Equal arithmetic genera of the fibres over `s`** (T44A's
`arithmeticGenus_fibre_eq_of_isProjectiveOver` for the residue field point of `s`). -/
theorem arithmeticGenus_fiber_eq [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [CompactSpace C']
    [IsAffineHom (pullback.diagonal (terminal.from C'))] [Flat p] [Flat (f ≫ p)]
    (hp : IsProjectiveOver p) (hp' : IsProjectiveOver (f ≫ p)) (hf : Curves.IsEtaModification f p)
    [CompactSpace ((f ≫ p).fiber s)]
    [IsAffineHom (pullback.diagonal (terminal.from ((f ≫ p).fiber s)))]
    [CompactSpace (p.fiber s)] [IsAffineHom (pullback.diagonal (terminal.from (p.fiber s)))] :
    arithmeticGenus ((f ≫ p).fiber s)
        (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
          ((f ≫ p).fiberToSpecResidueField s)) =
      arithmeticGenus (p.fiber s)
        (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
          (p.fiberToSpecResidueField s)) := by
  have h := arithmeticGenus_fibre_eq_of_isProjectiveOver p f hp hp' hf (residueFieldPoint s)
  have e := (fromSpecResidueField_eq_specMap s).symm
  unfold Scheme.Hom.fiber Scheme.Hom.fiberToSpecResidueField at *
  rw [arithmeticGenus_pullback_congr (f ≫ p) e, arithmeticGenus_pullback_congr p e] at h
  exact h

end Transport

section ClosedPoint

/-! ### The closed fibre -/

/-- Reducedness of a pullback only depends on the base point up to isomorphism. -/
theorem isReduced_pullback_of_iso {X S T T' : Scheme.{u}} (p : X ⟶ S) (a : T ⟶ S) (a' : T' ⟶ S)
    (e : T' ≅ T) (h : e.hom ≫ a = a') [IsReduced (pullback p a)] : IsReduced (pullback p a') := by
  subst h
  have : IsReduced (pullback (pullback.snd p a) e.hom) :=
    isReduced_of_isOpenImmersion (pullback.fst (pullback.snd p a) e.hom)
  exact isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso p a e.hom).inv

variable {V : Type u} [CommRing V] [IsLocalRing V]

omit [IsLocalRing V] in
/-- The residue map of `Spec V` at `x` is the algebra map to `κ(𝔭_x)`, up to the canonical
isomorphism. -/
theorem residueFieldPoint_eq (x : Spec (CommRingCat.of V)) :
    residueFieldPoint x = (Scheme.Spec.residueFieldIso (CommRingCat.of V) x).inv.hom.comp
      (algebraMap V x.asIdeal.ResidueField) := by
  have h := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of V) x
  ext v
  have h' := congrArg (fun φ => φ.hom v) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h'
  rw [RingHom.comp_apply, h']
  rfl

/-- **The residue field of `Spec V` at the closed point is the residue field of `V`**, compatibly
with the maps from `V`. -/
def residueFieldClosedPointEquiv :
    IsLocalRing.ResidueField V ≃+*
      (Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V) := by
  let x : Spec (CommRingCat.of V) := IsLocalRing.closedPoint V
  have hmax : x.asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal V
  have hsurj : Function.Surjective (residueFieldPoint x) := by
    rw [residueFieldPoint_eq]
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (CommRingCat.of V) x).inv).2.comp
      (Ideal.algebraMap_residueField_surjective x.asIdeal)
  have hker : RingHom.ker (residueFieldPoint x) = IsLocalRing.maximalIdeal V := by
    rw [residueFieldPoint_eq, RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.Spec.residueFieldIso (CommRingCat.of V) x).inv).1,
      Ideal.ker_algebraMap_residueField]
    rfl
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

theorem residueFieldClosedPointEquiv_residue (v : V) :
    residueFieldClosedPointEquiv (IsLocalRing.residue V v) =
      residueFieldPoint (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) v :=
  rfl

/-- The residue field morphism of `Spec V` at the closed point factors through
`Spec (V ⧸ 𝔪) → Spec V` by an isomorphism. -/
theorem specMap_residueFieldClosedPointEquiv_comp :
    Spec.map (CommRingCat.ofHom (residueFieldClosedPointEquiv (V := V)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) =
      (Spec (CommRingCat.of V)).fromSpecResidueField (IsLocalRing.closedPoint V) := by
  rw [fromSpecResidueField_eq_specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

end ClosedPoint

section ClosedFibre

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C C' : Scheme.{u}}
  (p : C ⟶ Spec (CommRingCat.of V)) (f : C' ⟶ C)

/-- **The closed fibre of `C` is reduced** (blueprint `prop:sm-normalization-reduced`(3), in the
form of a scheme-theoretic fibre `p.fiber s₀`): `C` normal, integral and of finite presentation
over `V`, dominated by a nodal curve `C'` through a birational `f` projective relative to `p`. -/
theorem isReduced_fiber_closedPoint [IsIntegral C] [IsIntegral C'] [LocallyOfFinitePresentation p]
    [DeJong.IsNodalCurve (f ≫ p)] [QuasiCompact f] [QuasiSeparated f]
    (hfp : DeJong.IsRelativelyProjective p f) (hnormal : IsNormalScheme C)
    (hbir : Scheme.BirationalOver f (𝟙 C)) :
    IsReduced (p.fiber (IsLocalRing.closedPoint V)) := by
  have : IsReduced (pullback (f ≫ p) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) :=
    DeJong.IsNodalCurve.isReduced_pullback (f ≫ p) _ _
  have : IsReduced (pullback p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) :=
    isReduced_closedFibre_of_isNormalScheme f p hfp hnormal hbir
  exact isReduced_pullback_of_iso p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
    ((Spec (CommRingCat.of V)).fromSpecResidueField (IsLocalRing.closedPoint V))
    (Scheme.Spec.mapIso (residueFieldClosedPointEquiv (V := V)).toCommRingCatIso.op)
    specMap_residueFieldClosedPointEquiv_comp

end ClosedFibre

section Criterion

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C C' : Scheme.{u}}
  (p : C ⟶ Spec (CommRingCat.of V)) (f : C' ⟶ C) (s : Spec (CommRingCat.of V))

/-- **The points of `C_s` over the modification locus** form a finite set (lane T42's Temkin
Lemma 4.2.1(ii), `ValCurves.finite_center_inter_preimage`). -/
theorem exists_finset_center [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p]
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1) :
    ∃ J : Finset (p.fiber s), ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f := by
  have hF := ValCurves.finite_center_inter_preimage p hnormal hcurve f s
  have hinj : Set.InjOn (p.fiberι s) (p.fiberι s ⁻¹' ((center f : Set C) ∩ p ⁻¹' {s})) :=
    (p.fiberι s).isEmbedding.injective.injOn
  refine ⟨(hF.preimage hinj).toFinset, fun x => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_preimage]
  exact ⟨fun h => h.1, fun h => ⟨h, apply_fiberι p s x⟩⟩

/-- **The points of `C_s` over the modification locus are closed in `C_s`**: their residue fields
are algebraic over `κ(s)` (Temkin, Lemma 4.2.1(ii),
`ValCurves.fiberTrdeg_eq_zero_of_mem_center`). -/
theorem isClosed_singleton_of_mem_center [IsIntegral C] [IsIntegral C'] [IsModification f]
    [IsSeparated p]
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (x : p.fiber s) (hx : p.fiberι s x ∈ center f) : IsClosed ({x} : Set (p.fiber s)) :=
  isClosed_singleton_fiber_of_isAlgebraicAt p s x
    ((ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero p _).2
      (ValCurves.fiberTrdeg_eq_zero_of_mem_center p hnormal hcurve f hx))

omit [IsDomain V] [ValuationRing V] in
/-- **The fibres of a nodal curve over points with algebraically closed residue field have
dimension at most one.** -/
theorem topologicalKrullDim_fiber_le_one_of_isNodalCurve (g : C' ⟶ Spec (CommRingCat.of V))
    [DeJong.IsNodalCurve g] [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] :
    topologicalKrullDim (g.fiber s) ≤ 1 :=
  topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW =>
    (DeJong.IsNodalCurve.pureGeometricFibers (g := g)
      (↑((Spec (CommRingCat.of V)).residueField s)) _ W hW).le

omit [IsDomain V] [ValuationRing V] in
/-- **The components of the contracted fibres** exist as finsets. -/
theorem exists_innerFinset [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)] :
    ∃ G : p.fiber s → Finset ((f ≫ p).fiber s),
      ∀ x, (G x : Set ((f ≫ p).fiber s)) = innerPoints (Curves.fiberMap f p s) x := by
  have := finite_genericPoints_fiber (f ≫ p) s
  exact ⟨fun x => (Set.toFinite (innerPoints (Curves.fiberMap f p s) x)).toFinset,
    fun x => Set.Finite.coe_toFinset _⟩


omit [IsDomain V] [ValuationRing V] in
/-- **The contracted fibres are curves** (Temkin's hypothesis "`Z` is a curve", lem:sm-bd-localize
(1)): for a point `x` of `C_s` over the modification locus, `Z_x = f_s⁻¹(x)` contains a generic
point of `C'_s`. Otherwise `Z_x` would be a closed set of closed points of the Noetherian curve
`C'_s`, hence finite, so `f⁻¹(x)` would be finite (`not_finite_preimage_of_mem_center`). -/
theorem exists_genericPoints_fiberMap_preimage [IsIntegral C] [IsIntegral C'] [IsModification f]
    [IsProper p] (hnormal : IsNormalScheme C) (hdim' : topologicalKrullDim ((f ≫ p).fiber s) ≤ 1)
    (x : p.fiber s) (hxc : IsClosed ({x} : Set (p.fiber s))) (hx : p.fiberι s x ∈ center f) :
    ∃ v, Curves.fiberMap f p s v = x ∧ v ∈ genericPoints ((f ≫ p).fiber s) := by
  by_contra h
  push Not at h
  have := noetherianSpace_fiber (f ≫ p) s
  have hZ : (Curves.fiberMap f p s ⁻¹' {x}).Finite :=
    CurvesField.Genus.finite_of_isClosed_of_disjoint_genericPoints hdim'
      (hxc.preimage (Curves.fiberMap f p s).continuous) fun v hv => h v hv
  refine not_finite_preimage_of_mem_center f hnormal hx ((hZ.image ((f ≫ p).fiberι s)).subset ?_)
  intro y hy
  have hys : y ∈ Set.range ((f ≫ p).fiberι s) := by
    rw [Scheme.Hom.range_fiberι, Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply,
      show f y = p.fiberι s x from hy]
    exact apply_fiberι p s x
  obtain ⟨y', rfl⟩ := hys
  refine ⟨y', ?_, rfl⟩
  rw [fiberMap_preimage_singleton]
  exact hy

open scoped Classical in
/-- **Temkin's stability criterion, Lemma 4.4.2, fibrewise form** (blueprint
`lem:sm-stability-criterion`, T:3106–3133, for all points of the modification locus in a fibre
at once), for a source semi-stable along the contracted fibres. Let `V` be a valuation ring with
finitely many primes, all `Frac(V/𝔭)` separably closed and infinite residue field,
`p : C → Spec V` projective, flat and of finite presentation with `C` integral, normal, of
relative dimension one and with fibre `C_s` of pure dimension one over a point `s` with
algebraically closed `κ(s)`, and `f : C' → C` a modification, projective relative to `p`, which
is an η-modification, with `C' → Spec V` flat. Assume `C_s` reduced (automatic at the closed
point, `isReduced_fiber_closedPoint`), `C'_s` reduced of dimension at most one, every closed
point of `C'_s` over the points of `J` a smooth point or an ordinary double point (`hnodal`;
for `C'` nodal see `stability_criterion_fibre`), and the components of the contracted fibres
`Z_x = f_s⁻¹(x)`, `x ∈ J`, of nonnegative genus (Temkin's hypothesis "`Z` is a curve" is
automatic, `exists_genericPoints_fiberMap_preimage`). Here `J` is the set of points of `C_s` over
the modification locus `Z(f)`, `G x` the components of `Z_x`, `Γ` the incidence graph of `C'_s`
along `f_s⁻¹(J)`, `x̃` the points of the normalization of `C_s` over `x`, and `m x` any numbers
(the numbers of marks through `x`, `lem:sm-bd-marks`). Then:

1. every `Z_x` is connected and the union of its components;
2. if every `x ∈ J` is a smooth point or an ordinary double point of `C_s`, with `m x ≤ 1`, and
   a smooth point if `m x = 1`, then every `G x` is a `ℙ¹`-tree with `|∂(G x)| + m x ≤ 2` (an
   exceptional `ℙ¹`-tree);
3. if every `G x` is a `ℙ¹`-tree with `|∂(G x)| + m x ≤ 2`, then every `x ∈ J` is an ordinary
   point (`δ(x) + 1 = |x̃|`) with `|x̃| ≤ 2`, `m x ≤ 1` and `|x̃| = 1` if `m x = 1`. -/
theorem stability_criterion_fibre_of_semistableAlong [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] [Flat (f ≫ p)] [IsReduced ((f ≫ p).fiber s)] (hp : IsProjectiveOver p)
    (hfp : DeJong.IsRelativelyProjective p f)
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη : Curves.IsEtaModification f p)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (p.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (J : Finset (p.fiber s)) (hJ : ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f)
    (G : p.fiber s → Finset ((f ≫ p).fiber s))
    (hG : ∀ x ∈ J, (G x : Set ((f ≫ p).fiber s)) = innerPoints (Curves.fiberMap f p s) x)
    (hdim' : topologicalKrullDim ((f ≫ p).fiber s) ≤ 1)
    (hnodal : ∀ y ∈ Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)), IsClosed {y} →
      DeJong.IsSmoothAt ((f ≫ p).fiberToSpecResidueField s) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((f ≫ p).fiberToSpecResidueField s) y)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((f ≫ p).fiberToSpecResidueField s)) v)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((f ≫ p).fiberToSpecResidueField s) (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s))))]
    (m : p.fiber s → ℕ) :
    (∀ x ∈ J, _root_.IsConnected (Curves.fiberMap f p s ⁻¹' {x}) ∧
      ∀ z ∈ Curves.fiberMap f p s ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v}) ∧
    ((∀ x ∈ J, (DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x) ∧
        m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x)) →
      ∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) ∧
    ((∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) →
      ∀ x ∈ J, deltaInvariant (normalizationPointsMap (genericPoints (p.fiber s)))
          (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
            (p.fiberToSpecResidueField s)) x + 1 =
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ∧
        Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ≤ 2 ∧ m x ≤ 1 ∧
        (m x = 1 →
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) = 1)) := by
  have hmod : IsModification f := inferInstance
  -- the points of `C_s` over `Z(f)`: closed, not generic, and `f_s` is an isomorphism off them
  have hJc : ∀ x ∈ (J : Set (p.fiber s)), IsClosed ({x} : Set (p.fiber s)) := fun x hx =>
    isClosed_singleton_of_mem_center p f s hnormal hcurve x ((hJ x).1 hx)
  have hJcl : IsClosed (J : Set (p.fiber s)) := by
    rw [← Set.biUnion_of_singleton (J : Set (p.fiber s))]
    exact isClosed_biUnion_finset fun x hx => hJc x hx
  let U : (p.fiber s).Opens := ⟨(J : Set (p.fiber s))ᶜ, hJcl.isOpen_compl⟩
  have hU : ∀ y, y ∈ U ↔ y ∉ (J : Set (p.fiber s)) := fun y => Iff.rfl
  have hiso : IsIso (Curves.fiberMap f p s ∣_ U) :=
    isIso_fiberMap_restrict_of_center f p s (J : Set (p.fiber s)) (fun y => (hJ y).symm) U hU
  have hXg : ∀ x ∈ (J : Set (p.fiber s)), x ∉ genericPoints (p.fiber s) := fun x hx =>
    not_mem_genericPoints_of_isClosed hpure (hJc x hx)
  -- dimension, projectivity and genus of the fibres
  have hdim : topologicalKrullDim (p.fiber s) ≤ 1 :=
    topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW => (hpure W hW).le
  have hp' : IsProjectiveOver (f ≫ p) := DeJong.IsRelativelyProjective.isProjectiveOver hp hfp
  have hps := isProjectiveOver_fiberToSpecResidueField p s hp
  have hps' := isProjectiveOver_fiberToSpecResidueField (f ≫ p) s hp'
  have : CompactSpace C := compactSpace_of_quasiCompact p
  have : IsAffineHom (pullback.diagonal (terminal.from C)) := isAffineHom_diagonal_of_isSeparated p
  have : CompactSpace C' := compactSpace_of_quasiCompact (f ≫ p)
  have : IsAffineHom (pullback.diagonal (terminal.from C')) :=
    isAffineHom_diagonal_of_isSeparated (f ≫ p)
  have hpa := arithmeticGenus_fiber_eq p f s hp hp' hη
  -- the contracted fibres are connected curves
  have hconn : ∀ x ∈ J, _root_.IsConnected (Curves.fiberMap f p s ⁻¹' {x}) := fun x _ =>
    isConnected_fiberMap_preimage p s f x
      (ConnectedBirationalHeight.isConnected_preimage_singleton_of_isProjectiveOver f p hsep hp hfp
        hnormal hmod.birational hcurve _)
  have := noetherianSpace_fiber (f ≫ p) s
  have hZcur : ∀ x ∈ J, ∀ z ∈ Curves.fiberMap f p s ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v} := by
    intro x hx z hz
    have hZc : IsClosed (Curves.fiberMap f p s ⁻¹' {x}) :=
      (hJc x hx).preimage (Curves.fiberMap f p s).continuous
    obtain ⟨v, hvx, hvg⟩ :=
      exists_genericPoints_fiberMap_preimage p f s hnormal hdim' x (hJc x hx) ((hJ x).1 hx)
    obtain ⟨w, hwZ, hwg, hzw⟩ :=
      exists_mem_genericPoints_of_isConnected hdim' hZc (hconn x hx) ⟨v, hvx, hvg⟩ z hz
    refine ⟨w, ?_, hzw⟩
    have : w ∈ (G x : Set ((f ≫ p).fiber s)) := by
      rw [hG x hx]
      exact ⟨hwg, hwZ⟩
    exact this
  have hfps := Curves.fiberMap_fiberToSpecResidueField f p s
  refine ⟨fun x hx => ⟨hconn x hx, hZcur x hx⟩, ?_, ?_⟩
  · exact stabdown_finset_exceptional_of_semistable
      (k := ↑((Spec (CommRingCat.of V)).residueField s))
      (Curves.fiberMap f p s) (J : Set (p.fiber s)) U hU (p.fiberToSpecResidueField s)
      ((f ≫ p).fiberToSpecResidueField s) hfps J rfl hXg hJc hdim hdim' hps hps' hpa G hG hconn
      hZcur hnodal hg m
  · exact stabdown_finset_ordinary_of_exceptional
      (k := ↑((Spec (CommRingCat.of V)).residueField s))
      (Curves.fiberMap f p s) (J : Set (p.fiber s)) U hU (p.fiberToSpecResidueField s)
      ((f ≫ p).fiberToSpecResidueField s) hfps J rfl hXg hJc hdim hdim' hps hps' hpa G hG hconn
      hZcur hnodal hg m

open scoped Classical in
/-- **Temkin's stability criterion, Lemma 4.4.2, fibrewise form, for a nodal source**
(blueprint `lem:sm-stability-criterion`): `stability_criterion_fibre_of_semistableAlong` with
`C' → Spec V` a nodal curve (`C'_s` is then reduced, `lem:sm-bd-nodal-reduced`, and semi-stable
everywhere). -/
theorem stability_criterion_fibre [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] [DeJong.IsNodalCurve (f ≫ p)] (hp : IsProjectiveOver p)
    (hfp : DeJong.IsRelativelyProjective p f)
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη : Curves.IsEtaModification f p)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (p.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (J : Finset (p.fiber s)) (hJ : ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f)
    (G : p.fiber s → Finset ((f ≫ p).fiber s))
    (hG : ∀ x ∈ J, (G x : Set ((f ≫ p).fiber s)) = innerPoints (Curves.fiberMap f p s) x)
    (hdim' : topologicalKrullDim ((f ≫ p).fiber s) ≤ 1)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((f ≫ p).fiberToSpecResidueField s)) v)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((f ≫ p).fiberToSpecResidueField s) (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s))))]
    (m : p.fiber s → ℕ) :
    (∀ x ∈ J, _root_.IsConnected (Curves.fiberMap f p s ⁻¹' {x}) ∧
      ∀ z ∈ Curves.fiberMap f p s ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v}) ∧
    ((∀ x ∈ J, (DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x) ∧
        m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x)) →
      ∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) ∧
    ((∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) →
      ∀ x ∈ J, deltaInvariant (normalizationPointsMap (genericPoints (p.fiber s)))
          (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
            (p.fiberToSpecResidueField s)) x + 1 =
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ∧
        Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ≤ 2 ∧ m x ≤ 1 ∧
        (m x = 1 →
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) = 1)) := by
  have hnodal : ∀ y ∈ Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)), IsClosed {y} →
      DeJong.IsSmoothAt ((f ≫ p).fiberToSpecResidueField s) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((f ≫ p).fiberToSpecResidueField s) y :=
    fun y _ hy => DeJong.IsNodalCurve.geometricNodes (g := f ≫ p)
      (↑((Spec (CommRingCat.of V)).residueField s))
      ((Spec (CommRingCat.of V)).fromSpecResidueField s) y hy
  exact stability_criterion_fibre_of_semistableAlong p f s hsep hp hfp hnormal hcurve hη hpure J hJ
    G hG hdim' hnodal hg m

open scoped Classical in
/-- **Temkin's stability criterion, fibrewise form, as an equivalence, for a source semi-stable
along the contracted fibres** (blueprint `lem:sm-stability-criterion`), assuming the converse of the
ordinary-completion lemma over
`κ(s)` (`OrdinaryPointCompletion`, not formalized; the "only if" direction does not use it,
`stability_criterion_fibre_of_semistableAlong`): in its situation, every point
`x ∈ J` of `C_s` over the modification locus is a smooth point or an ordinary double point of
`C_s` with at most one mark, and a smooth point if it carries one, **if and only if** every
contracted fibre `Z_x` is an exceptional `ℙ¹`-tree (`|∂Z_x| + m x ≤ 2`). -/
theorem stability_criterion_fibre_iff_of_semistableAlong [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] [Flat (f ≫ p)] [IsReduced ((f ≫ p).fiber s)] (hp : IsProjectiveOver p)
    (hfp : DeJong.IsRelativelyProjective p f)
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη : Curves.IsEtaModification f p)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (p.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (J : Finset (p.fiber s)) (hJ : ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f)
    (G : p.fiber s → Finset ((f ≫ p).fiber s))
    (hG : ∀ x ∈ J, (G x : Set ((f ≫ p).fiber s)) = innerPoints (Curves.fiberMap f p s) x)
    (hdim' : topologicalKrullDim ((f ≫ p).fiber s) ≤ 1)
    (hnodal : ∀ y ∈ Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)), IsClosed {y} →
      DeJong.IsSmoothAt ((f ≫ p).fiberToSpecResidueField s) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((f ≫ p).fiberToSpecResidueField s) y)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((f ≫ p).fiberToSpecResidueField s)) v)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((f ≫ p).fiberToSpecResidueField s) (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s))))]
    (m : p.fiber s → ℕ)
    (hcompl : OrdinaryPointCompletion ↑((Spec (CommRingCat.of V)).residueField s)) :
    (∀ x ∈ J, (DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x) ∧
        m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x)) ↔
      ∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2 := by
  obtain ⟨-, hA, hB⟩ := stability_criterion_fibre_of_semistableAlong p f s hsep hp hfp hnormal
    hcurve hη hpure J hJ G hG hdim' hnodal hg m
  refine ⟨hA, fun hexc x hx => ?_⟩
  obtain ⟨hord, h2, hm, hm1⟩ := hB hexc x hx
  have hxc := isClosed_singleton_of_mem_center p f s hnormal hcurve x ((hJ x).1 hx)
  have hxg := not_mem_genericPoints_of_isClosed hpure hxc
  have hdim : topologicalKrullDim (p.fiber s) ≤ 1 :=
    topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW => (hpure W hW).le
  obtain ⟨hsm, hnode⟩ := hcompl (p.fiber s) (p.fiberToSpecResidueField s) hdim x hxc hxg hord
  have hpos := natCard_fiber_pos (k := ↑((Spec (CommRingCat.of V)).residueField s))
    (p.fiberToSpecResidueField s) x
  refine ⟨?_, hm, fun h => hsm (hm1 h)⟩
  rcases Nat.lt_or_ge (Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x})) 2
    with h | h
  · exact Or.inl (hsm (by omega))
  · exact Or.inr (hnode (by omega))

open scoped Classical in
/-- **Temkin's stability criterion, Lemma 4.4.2, fibrewise form, as an equivalence** (blueprint
`lem:sm-stability-criterion`), assuming the converse of the ordinary-completion lemma over
`κ(s)` (`OrdinaryPointCompletion`, not formalized; the "only if" direction does not use it,
`stability_criterion_fibre`): in the situation of `stability_criterion_fibre`, every point
`x ∈ J` of `C_s` over the modification locus is a smooth point or an ordinary double point of
`C_s` with at most one mark, and a smooth point if it carries one, **if and only if** every
contracted fibre `Z_x` is an exceptional `ℙ¹`-tree (`|∂Z_x| + m x ≤ 2`). -/
theorem stability_criterion_fibre_iff [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] [DeJong.IsNodalCurve (f ≫ p)] (hp : IsProjectiveOver p)
    (hfp : DeJong.IsRelativelyProjective p f)
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη : Curves.IsEtaModification f p)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (p.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (J : Finset (p.fiber s)) (hJ : ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f)
    (G : p.fiber s → Finset ((f ≫ p).fiber s))
    (hG : ∀ x ∈ J, (G x : Set ((f ≫ p).fiber s)) = innerPoints (Curves.fiberMap f p s) x)
    (hdim' : topologicalKrullDim ((f ≫ p).fiber s) ≤ 1)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((f ≫ p).fiberToSpecResidueField s)) v)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((f ≫ p).fiberToSpecResidueField s) (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s))))]
    (m : p.fiber s → ℕ)
    (hcompl : OrdinaryPointCompletion ↑((Spec (CommRingCat.of V)).residueField s)) :
    (∀ x ∈ J, (DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x) ∧
        m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x)) ↔
      ∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2 := by
  have hnodal : ∀ y ∈ Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)), IsClosed {y} →
      DeJong.IsSmoothAt ((f ≫ p).fiberToSpecResidueField s) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((f ≫ p).fiberToSpecResidueField s) y :=
    fun y _ hy => DeJong.IsNodalCurve.geometricNodes (g := f ≫ p)
      (↑((Spec (CommRingCat.of V)).residueField s))
      ((Spec (CommRingCat.of V)).fromSpecResidueField s) y hy
  exact stability_criterion_fibre_iff_of_semistableAlong p f s hsep hp hfp hnormal hcurve hη hpure
    J hJ G hG hdim' hnodal hg m hcompl

end Criterion

end

end DeJongAlterations.StableModification.BlowDown
