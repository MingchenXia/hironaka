/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.DominationGraph
import DeJongAlterations.StableModification.BlowDown.StabilityCriterion
import DeJongAlterations.StableModification.ValCurves.ModificationsUnique

/-!
# Domination of the stable modification (Temkin, Corollary 4.4.3 (1))

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`),
Corollary 4.4.3 (`sepcloscor`, T:3135–3149), part (1): *if a stable modification `(C_st, D_st)`
and a semi-stable modification `(C', D')` of `(C, D)` are both dominated by a semi-stable
modification `(C̄, D̄)`, then `C'` dominates `C_st`.* We prove it for curves projective over a
valuation ring `V` with finitely many primes (blueprint `cor:sm-domination-stable` (1),
chapter `sm-blow-down-domination.tex`).

Notation: `p : C → Spec V` is the base curve, `f' : C' → C` the semi-stable and `fs : Cs → C`
the stable modification, `h' : Cb → C'`, `h : Cb → Cs` the dominations (`h' ≫ f' = h ≫ fs`),
the structure morphism of `Cb` is `h' ≫ f' ≫ p`, and the marks of `Cb` are sections `σ i`
(those of `C'`, `Cs` are their images).

## Temkin's proof, and its formalization

Fix `s ∈ Spec V` (residue field algebraically closed) and consider the incidence data `Γ` of the
fibre `Cb_s` along the locus contracted to points of `C` (`contractedLocus`), marked by the `σ i`.

1. `Γ` is *anchored* (`isAnchored_withMarks`): a nonempty set of contracted components without
   boundary double point would be open and closed in the connected `Cb_s` (Zariski,
   `Cohomology.Connected.isConnected_fiber_of_irreducibleSpace`), hence everything, and `C_s`
   (of pure dimension one) would consist of the finitely many contracted points.
2. By the stability criterion (Lemma 4.4.2, `stability_criterion_fibre`) for the semi-stable
   `C'`, the fibres `G'(x)` of `h'_s` over the modification locus of `h'` are exceptional trees;
   so are the fibres `G(x)` of `h_s` (for `Cs`). They are exceptional trees of `Γ`
   (`isTransfer_nodalGraph`: enlarging the subcurve does not change the double points on them).
3. The fibres `G(x)` are pairwise separated; if they form a *stable family* (`FibresStable`:
   no component outside them has an exceptional star), every exceptional tree lies in one of them
   (Lemma B.3, `exists_superset_of_finite_eligible`). Hence every point of `Cb` contracted by `h'`
   is contracted by `h` (`mem_center_of_mem_center`).
4. A valuation ring of `Γ₀(Cs)` is centred at a generic point `x` of a fibre of `Cs` over a closed
   point of `C`; `h` is an isomorphism over `x` (Lemma 4.2.1,
   `ValCurves.mem_isomorphismOpen_of_mem_fibreGenericSet`), so its centre `x̄` on `Cb` is not
   contracted by `h`, hence not by `h'`, and `h'(x̄)` is a generic point of a fibre of `C'`:
   `Γ₀(Cs) ⊆ Γ₀(C')`, and the normal `C'` dominates `Cs` (Proposition 4.2.3,
   `ValCurves.dominates_of_gammaZeroSet_subset`; `dominates_of_fibresStable`).

That the stability of `Cs` gives the stable-family condition of step 3 (Temkin, App. B,
T:4463–4467) is `DominationStable.lean` (`fibresStable_of_fibreStable`,
`dominates_of_fibreStable`).

## Main results

* `fiberMapOfEq`, `stability_criterion_fibre_of_eq`, `mem_center_of_forall_closure`: fibre maps
  out of a fixed fibre, the stability criterion for them, and "a component contracted by a fibre
  map lies over the modification locus".
* `finite_nodesIn`, `isTransfer_nodalGraph`, `isAnchored_withMarks`: the incidence data.
* `FibresStable`: the stable-family condition for the fibres of `h`.
* `mem_center_of_mem_center_fibre`, `mem_center_of_mem_center`: contracted by `h'` ⇒ contracted
  by `h`.
* `dominates_of_fibresStable`: **Corollary 4.4.3 (1)**, given `FibresStable`.

## Hypotheses of the formalization

As in the stability criterion (`sm-blow-down-criterion.tex`): the residue fields of `V` are
algebraically closed, the components of the fibres of `Cb` have nonnegative genus (ERRATA T60),
and the semi-stability of `(C', h'(σ))` and `(Cs, h(σ))` at the contracted points is used in the
numerical form "at most one mark, at a smooth point" (`hss'`, `hss`). The fibres of `C` are
assumed of pure dimension one (`hpure`; used for the anchoring).
-/

namespace DeJongAlterations.StableModification.BlowDown.Domination

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus
open Geometry.ModificationCenter (isomorphismOpen center)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

section FiberMapOfEq

/-! ### Fibre maps out of a fixed fibre

The stability criterion is stated for the fibre `(f ≫ p).fiber s` of a composite. In
Corollary 4.4.3 three morphisms `h' : C̄ → C'`, `h : C̄ → C_st` and `f̄ : C̄ → C` leave the same
curve `C̄`, whose structure morphism `q` equals `h' ≫ p'`, `h ≫ p_st` and `f̄ ≫ p` only
propositionally; we therefore restate the inputs for an arbitrary `q` with `e : f ≫ p = q`. -/

variable {S C C' : Scheme.{u}} (f : C' ⟶ C) (p : C ⟶ S) (q : C' ⟶ S) (e : f ≫ p = q) (s : S)

/-- The morphism of fibres `q_s ⟶ p_s` induced by `f` when `f ≫ p = q`. For `q = f ≫ p` it is
`Curves.fiberMap f p s` (`fiberMapOfEq_rfl`). -/
def fiberMapOfEq : q.fiber s ⟶ p.fiber s :=
  pullback.map q (S.fromSpecResidueField s) p (S.fromSpecResidueField s) f (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, e]) (by simp)

theorem fiberMapOfEq_rfl : fiberMapOfEq f p (f ≫ p) rfl s = Curves.fiberMap f p s := rfl

@[reassoc (attr := simp)]
theorem fiberMapOfEq_fiberι : fiberMapOfEq f p q e s ≫ p.fiberι s = q.fiberι s ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberMapOfEq_fiberToSpecResidueField :
    fiberMapOfEq f p q e s ≫ p.fiberToSpecResidueField s = q.fiberToSpecResidueField s := by
  simp [fiberMapOfEq, Scheme.Hom.fiberToSpecResidueField]

theorem fiberι_fiberMapOfEq_apply (y : q.fiber s) :
    p.fiberι s (fiberMapOfEq f p q e s y) = f (q.fiberι s y) := by
  rw [← Scheme.Hom.comp_apply, fiberMapOfEq_fiberι, Scheme.Hom.comp_apply]

/-- Composition of fibre maps. -/
theorem fiberMapOfEq_comp {C'' : Scheme.{u}} (g : C'' ⟶ C') (r : C'' ⟶ S) (e' : g ≫ q = r) :
    fiberMapOfEq g q r e' s ≫ fiberMapOfEq f p q e s =
      fiberMapOfEq (g ≫ f) p r (by rw [Category.assoc, e, e']) s := by
  apply pullback.hom_ext <;> simp [fiberMapOfEq]

/-- `f_s` is an isomorphism off the points over the modification locus
(`isIso_fiberMap_restrict_of_center` for `fiberMapOfEq`). -/
theorem isIso_fiberMapOfEq_restrict_of_center (X : Set (p.fiber s))
    (hX : ∀ y, p.fiberι s y ∈ center f ↔ y ∈ X) (U' : (p.fiber s).Opens)
    (hU' : ∀ y, y ∈ U' ↔ y ∉ X) : IsIso (fiberMapOfEq f p q e s ∣_ U') := by
  subst e
  exact isIso_fiberMap_restrict_of_center f p s X hX U' hU'

instance isProper_fiberMapOfEq [IsProper f] : IsProper (fiberMapOfEq f p q e s) := by
  subst e
  exact isProper_fiberMap p s f

/-- **A component contracted by a fibre map lies over the modification locus**: if `w` is a
generic point of the fibre `D_s` of `r = β ≫ p`, of pure dimension one, and the fibre map
`β_s` is constant on the closure of `w`, then `β_s(w)` lies over the modification locus of `β`
(otherwise `β_s` is injective near `β_s(w)`, so the closure of `w` is a point). -/
theorem mem_center_of_forall_closure
    (hpure : ∀ W ∈ irreducibleComponents (q.fiber s), topologicalKrullDim W = 1)
    {w : q.fiber s} (hw : w ∈ genericPoints (q.fiber s))
    (hcon : ∀ z ∈ closure ({w} : Set (q.fiber s)),
      fiberMapOfEq f p q e s z = fiberMapOfEq f p q e s w) :
    p.fiberι s (fiberMapOfEq f p q e s w) ∈ center f := by
  by_contra hn
  set X : Set (p.fiber s) := {x | p.fiberι s x ∈ center f} with hX
  have hXc : IsClosed X := (center f).isClosed.preimage (p.fiberι s).continuous
  let U : (p.fiber s).Opens := ⟨Xᶜ, hXc.isOpen_compl⟩
  have hU : ∀ y, y ∈ U ↔ y ∉ X := fun y => Iff.rfl
  have := isIso_fiberMapOfEq_restrict_of_center f p q e s X (fun y => Iff.rfl) U hU
  have hsub := subsingleton_preimage_of_not_mem (fiberMapOfEq f p q e s) X U hU hn
  have hcl : closure ({w} : Set (q.fiber s)) = {w} :=
    (hsub.anti fun z hz => hcon z hz).eq_singleton_of_mem (subset_closure rfl)
  have : IsClosed ({w} : Set (q.fiber s)) := hcl ▸ isClosed_closure
  exact not_mem_genericPoints_of_isClosed hpure this hw

end FiberMapOfEq

section CriterionOfEq

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C C' : Scheme.{u}}
  (p : C ⟶ Spec (CommRingCat.of V)) (f : C' ⟶ C) (q : C' ⟶ Spec (CommRingCat.of V))
  (e : f ≫ p = q) (s : Spec (CommRingCat.of V))

open scoped Classical in
/-- **Temkin's stability criterion, Lemma 4.4.2, fibrewise form** (`stability_criterion_fibre`),
for a source `C'` with a structure morphism `q` equal to `f ≫ p`. -/
theorem stability_criterion_fibre_of_eq [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] [IsProper q] [DeJong.IsNodalCurve q] (hp : IsProjectiveOver p)
    (hfp : DeJong.IsRelativelyProjective p f)
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη : Curves.IsEtaModification f p)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (p.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (J : Finset (p.fiber s)) (hJ : ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f)
    (G : p.fiber s → Finset (q.fiber s))
    (hG : ∀ x ∈ J, (G x : Set (q.fiber s)) = innerPoints (fiberMapOfEq f p q e s) x)
    (hdim' : topologicalKrullDim (q.fiber s) ≤ 1)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        (q.fiberToSpecResidueField s)) v)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      (q.fiberToSpecResidueField s) (fiberMapOfEq f p q e s ⁻¹' (J : Set (p.fiber s))))]
    (m : p.fiber s → ℕ) :
    (∀ x ∈ J, _root_.IsConnected (fiberMapOfEq f p q e s ⁻¹' {x}) ∧
      ∀ z ∈ fiberMapOfEq f p q e s ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v}) ∧
    ((∀ x ∈ J, (DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x) ∧
        m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x)) →
      ∀ x ∈ J, (nodalGraph (q.fiberToSpecResidueField s) hdim'
          (fiberMapOfEq f p q e s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph (q.fiberToSpecResidueField s) hdim'
          (fiberMapOfEq f p q e s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) ∧
    ((∀ x ∈ J, (nodalGraph (q.fiberToSpecResidueField s) hdim'
          (fiberMapOfEq f p q e s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph (q.fiberToSpecResidueField s) hdim'
          (fiberMapOfEq f p q e s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) →
      ∀ x ∈ J, deltaInvariant (normalizationPointsMap (genericPoints (p.fiber s)))
          (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
            (p.fiberToSpecResidueField s)) x + 1 =
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ∧
        Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ≤ 2 ∧ m x ≤ 1 ∧
        (m x = 1 →
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) = 1)) := by
  subst e
  let : Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((f ≫ p).fiberToSpecResidueField s) (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))) :=
    ‹_›
  exact stability_criterion_fibre p f s hsep hp hfp hnormal hcurve hη hpure J hJ G hG hdim' hg m

end CriterionOfEq

section Graph

/-! ### The incidence graph of a fibre along a closed subcurve -/

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [CompactSpace X] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (hdim : topologicalKrullDim X ≤ 1)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)]
  [CompactSpace X] [IsReduced X] in
/-- Every point of a scheme lies on an irreducible component. -/
theorem exists_mem_genericPoints_mem_closure (z : X) :
    ∃ v ∈ genericPoints X, z ∈ closure ({v} : Set X) := by
  let c : irreducibleComponents X :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  have hv := genericPoints.isGenericPoint_ofComponent c
  refine ⟨(genericPoints.ofComponent c).1, (genericPoints.ofComponent c).2, ?_⟩
  rw [hv.def]
  exact mem_irreducibleComponent

include hdim in
/-- **The ordinary double points of a projective reduced curve are finite in number**: they lie
in the support of the δ-invariant (`δ = 1` there), which is finite by the genus formula. -/
theorem finite_nodesIn (hp : IsProjectiveOver q) (Z : Set X) : (nodesIn q Z).Finite := by
  have h1 := (arithmeticGenus_eq_one_sub_card_add q (genericFinset X) coe_genericFinset hdim hp).1
  have key : ∀ (S : Set X) (_ : Finite S), S = genericPoints X →
      (Function.support (deltaInvariant (normalizationPointsMap S) (structureCoeff q))).Finite →
      (nodesIn q Z).Finite := by
    rintro S _ rfl h
    refine h.subset fun y hy => ?_
    rw [Function.mem_support, (deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint q hdim y
      hy.2.1 hy.2.2.1 hy.2.2.2).1]
    exact one_ne_zero
  exact key _ _ coe_genericFinset h1

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)]
  [CompactSpace X] [IsReduced X] [LocallyOfFiniteType q] in
theorem nodesIn_mono {Z₁ Z₂ : Set X} (h : Z₁ ⊆ Z₂) : nodesIn q Z₁ ⊆ nodesIn q Z₂ :=
  fun _ hy => ⟨h hy.1, hy.2⟩

open scoped Classical in
/-- **Enlarging the subcurve is a transfer of incidence data** along every set `W` of components
whose closures lie in the smaller subcurve `Z₁`: the double points on `W` are the same. -/
theorem isTransfer_nodalGraph {Z₁ Z₂ : Set X} (h : Z₁ ⊆ Z₂) [Fintype (nodesIn q Z₁)]
    [Fintype (nodesIn q Z₂)] {M : Type*} [Fintype M] (mk : M → X) (W : Finset X)
    (hW : ∀ v ∈ W, closure {v} ⊆ Z₁) :
    IsTransfer (nodalGraph q hdim Z₁) (withMarks (nodalGraph q hdim Z₂) mk)
      (Set.inclusion (nodesIn_mono q h)) W where
  injective := Set.inclusion_injective _
  ends_eq _ := rfl
  genus_eq _ _ := rfl
  surj e₂ := by
    rintro ⟨v, hv, hvW⟩
    have hev := ((mem_nodalGraph_ends q hdim e₂ v).1 hv).2
    exact ⟨⟨e₂.1, hW v hvW hev, e₂.2.2⟩, rfl⟩

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)]
  [CompactSpace X] [IsReduced X] in
/-- The components of a closed subcurve whose closures lie in it. -/
theorem closure_subset_of_mem {Z : Set X} (hZ : IsClosed Z) {v : X} (hv : v ∈ Z) :
    closure {v} ⊆ Z :=
  closure_minimal (Set.singleton_subset_iff.2 hv) hZ

open scoped Classical in
include hdim in
/-- **The incidence data along the locus contracted to points of `C` are anchored**
(Temkin, proof of Corollary 4.4.3, and the standing assumptions of App. B: `C̄_s` is connected and
`C̄_s → C_s` is surjective onto a curve). Let `φ : X → Y` (the fibre map `C̄_s → C_s`) be an
isomorphism over the complement `U` of a set `J` of closed points of `Y`, `Y` of pure dimension
one, `X` connected and semi-stable along `Z = φ⁻¹(J)`. Then every nonempty set of components
contracted into `J` has a boundary double point: otherwise the union of their closures would be
open and closed in `X`, hence all of `X`, and `Y` would be contained in `J`. -/
theorem isAnchored_withMarks [ConnectedSpace X] {Y : Scheme.{u}} (φ : X ⟶ Y) (J : Set Y)
    (hJc : ∀ x ∈ J, IsClosed ({x} : Set Y)) (hJ : IsClosed J) (U : Y.Opens)
    (hU : ∀ y, y ∈ U ↔ y ∉ J) [IsIso (φ ∣_ U)]
    (hpure : ∀ W ∈ irreducibleComponents Y, topologicalKrullDim W = 1)
    (hnodal : ∀ y ∈ φ ⁻¹' J, IsClosed {y} →
      DeJong.IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y)
    [Fintype (nodesIn q (φ ⁻¹' J))] {M : Type*} [Fintype M] (mk : M → X) :
    (withMarks (nodalGraph q hdim (φ ⁻¹' J)) mk).IsAnchored := by
  set Γ := withMarks (nodalGraph q hdim (φ ⁻¹' J)) mk with hΓ
  have hZ : IsClosed (φ ⁻¹' J) := hJ.preimage φ.continuous
  intro T hTne hTel
  by_contra hb
  rw [Finset.not_nonempty_iff_eq_empty] at hb
  have hTZ : ∀ v ∈ T, v ∈ φ ⁻¹' J ∧ v ∈ genericPoints X := fun v hv => hTel hv
  -- the union `A` of the closures of the components in `T` is open and closed
  set A : Set X := ⋃ v ∈ T, closure ({v} : Set X) with hA
  have hAc : IsClosed A := isClosed_biUnion_finset fun v _ => isClosed_closure
  set B : Set X := ⋃ v ∈ (genericFinset X).filter (fun v => v ∉ T), closure ({v} : Set X)
    with hB
  have hBc : IsClosed B := isClosed_biUnion_finset fun v _ => isClosed_closure
  have hAB : Aᶜ = B := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hvg, hzv⟩ := exists_mem_genericPoints_mem_closure z
      have hvT : v ∉ T := fun hvT => hz (Set.mem_biUnion hvT hzv)
      exact Set.mem_biUnion (Finset.mem_filter.2 ⟨mem_genericFinset.2 hvg, hvT⟩) hzv
    · intro hz hzA
      obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.1 hzA
      obtain ⟨hug, huT⟩ := Finset.mem_filter.1 hu
      have hug' := mem_genericFinset.1 hug
      obtain ⟨hvZ, hvg⟩ := hTZ v hv
      have hne : v ≠ u := fun h => huT (h ▸ hv)
      have hzZ : z ∈ φ ⁻¹' J := closure_subset_of_mem hZ hvZ hzv
      have hn := mem_nodesIn_of_mem_closure q hdim hnodal hzZ hvg hug' hne hzv hzu
      have hends : Γ.ends ⟨z, hn⟩ = s(v, u) :=
        nodalGraph_ends_eq q hdim ⟨z, hn⟩ hvg hug' hne hzv hzu
      have : (⟨z, hn⟩ : nodesIn q (φ ⁻¹' J)) ∈ Γ.boundary T :=
        (mem_boundary_of_ends hends).2 (Or.inl ⟨hv, huT⟩)
      rw [hb] at this
      exact Finset.notMem_empty _ this
  have hAo : IsOpen A := by
    rw [← isClosed_compl_iff, hAB]
    exact hBc
  obtain ⟨v₀, hv₀⟩ := hTne
  have hAuniv : A = Set.univ :=
    (isClopen_iff.1 ⟨hAc, hAo⟩).resolve_left (Set.nonempty_iff_ne_empty.1
      ⟨v₀, Set.mem_biUnion hv₀ (subset_closure rfl)⟩)
  -- hence `X = φ⁻¹(J)`
  have hall : ∀ z : X, φ z ∈ J := by
    intro z
    have hz : z ∈ A := hAuniv ▸ Set.mem_univ z
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.1 hz
    exact closure_subset_of_mem hZ (hTZ v hv).1 hzv
  -- a generic point of `Y` is not closed, hence lies in `U`, hence is hit by `φ`
  let c : irreducibleComponents Y :=
    ⟨irreducibleComponent (φ v₀), irreducibleComponent_mem_irreducibleComponents _⟩
  set w := (genericPoints.ofComponent c).1
  have hwg : w ∈ genericPoints Y := (genericPoints.ofComponent c).2
  have hwJ : w ∉ J := fun hw => not_mem_genericPoints_of_isClosed hpure (hJc w hw) hwg
  obtain ⟨y, hy⟩ := exists_eq_of_isIso_morphismRestrict φ U ((hU w).2 hwJ)
  exact hwJ (hy ▸ hall y)

end Graph

section NodalFibre

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of V))
  [DeJong.IsNodalCurve g] (s : Spec (CommRingCat.of V))
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)]

/-- The fibres of a nodal curve over points with algebraically closed residue field have pure
dimension one. -/
theorem pure_fiber_of_isNodalCurve :
    ∀ W ∈ irreducibleComponents (g.fiber s), topologicalKrullDim W = 1 :=
  DeJong.IsNodalCurve.pureGeometricFibers (g := g) (↑((Spec (CommRingCat.of V)).residueField s))
    ((Spec (CommRingCat.of V)).fromSpecResidueField s)

/-- The closed points of the fibres of a nodal curve over points with algebraically closed residue
field are smooth points or ordinary double points. -/
theorem nodes_fiber_of_isNodalCurve (y : g.fiber s) (hy : IsClosed ({y} : Set (g.fiber s))) :
    DeJong.IsSmoothAt (g.fiberToSpecResidueField s) y ∨
      Geometry.IsGeometricOrdinaryDoublePoint (g.fiberToSpecResidueField s) y :=
  DeJong.IsNodalCurve.geometricNodes (g := g) (↑((Spec (CommRingCat.of V)).residueField s))
    ((Spec (CommRingCat.of V)).fromSpecResidueField s) y hy

end NodalFibre

section Fibre

/-! ### The fibrewise statement

`p : C → Spec V` is the base curve, `f' : C' → C` the semi-stable and `fs : Cs → C` the stable
modification, dominated by `h' : Cb → C'` and `h : Cb → Cs` with `h' ≫ f' = h ≫ fs`; the structure
morphism of `Cb` is `h' ≫ f' ≫ p`, and the marks of `Cb` are sections `σ i`. -/

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {C C' Cs Cb : Scheme.{u}} (p : C ⟶ Spec (CommRingCat.of V)) (f' : C' ⟶ C) (fs : Cs ⟶ C)
  (h' : Cb ⟶ C') (h : Cb ⟶ Cs)

omit [IsDomain V] [ValuationRing V] in
/-- The two structure morphisms of `Cb` agree. -/
theorem comp_eq_of_comm (hcomm : h' ≫ f' = h ≫ fs) : h ≫ fs ≫ p = h' ≫ f' ≫ p := by
  rw [← Category.assoc, ← hcomm, Category.assoc]

variable (e : h ≫ fs ≫ p = h' ≫ f' ≫ p) {ι : Type*} [Fintype ι]
  (σ : ι → (Spec (CommRingCat.of V) ⟶ Cb)) (s : Spec (CommRingCat.of V))

/-- The locus of `Cb_s` contracted to points of `C` (the fibre over the points of `C_s` in the
modification locus of `h' ≫ f' : Cb → C`). -/
abbrev contractedLocus : Set ((h' ≫ f' ≫ p).fiber s) :=
  fiberMapOfEq (h' ≫ f') p (h' ≫ f' ≫ p) (Category.assoc _ _ _) s ⁻¹'
    {x | p.fiberι s x ∈ center (h' ≫ f')}

open scoped Classical in
/-- **The stable-family condition for the fibres of `h`** (Temkin, App. B, Lemma B.3,
T:4463–4467, in the combinatorial form `CurvesField.IncidenceGraph.IsStableFamily.stable`): in
the incidence data of `Cb_s` along the locus contracted to points of `C`, marked by the sections
`σ i`, no component `v` of `Cb_s` outside the fibres `G x = h_s⁻¹(x)` over the points `x` of the
modification locus of `h` has an exceptional star `{v} ∪ ⋃ {G x : G x meets v}`.

By Temkin's description of the contraction `h_s : Cb_s → Cs_s` (blueprint
`def:sm-stable-family`), the star of `v` is the preimage of the component `h_s(v)` of `Cs_s`,
and it is an exceptional tree exactly when `h_s(v)` is an exceptional component of
`(Cs, h(σ))`; so this condition is the fibrewise stability of `Cs`, read on `Cb`. The data `J`,
`G`, the marking `mk` of the marked points by their components and the instances are universally
quantified; they are determined by their specifications. -/
def FibresStable [IsProper (h' ≫ f' ≫ p)] [DeJong.IsNodalCurve (h' ≫ f' ≫ p)] : Prop :=
  ∀ (hdim : topologicalKrullDim ((h' ≫ f' ≫ p).fiber s) ≤ 1)
    [Fintype (nodesIn ((h' ≫ f' ≫ p).fiberToSpecResidueField s) (contractedLocus p f' h' s))]
    (mk : ι → (h' ≫ f' ≫ p).fiber s),
    (∀ i, mk i ∈ genericPoints ((h' ≫ f' ≫ p).fiber s) ∧
      ∃ y, (h' ≫ f' ≫ p).fiberι s y = σ i s ∧ y ∈ closure {mk i}) →
    ∀ (J : Finset ((fs ≫ p).fiber s)), (∀ x, x ∈ J ↔ (fs ≫ p).fiberι s x ∈ center h) →
    ∀ (G : (fs ≫ p).fiber s → Finset ((h' ≫ f' ≫ p).fiber s)),
    (∀ x ∈ J, (G x : Set ((h' ≫ f' ≫ p).fiber s)) =
      innerPoints (fiberMapOfEq h (fs ≫ p) (h' ≫ f' ≫ p) e s) x) →
    ∀ v ∈ genericPoints ((h' ≫ f' ≫ p).fiber s), (∀ x ∈ J, v ∉ G x) →
      ¬ (withMarks (nodalGraph ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim
          (contractedLocus p f' h' s)) mk).IsExceptionalTree
        ((withMarks (nodalGraph ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim
          (contractedLocus p f' h' s)) mk).star (J.image G) v)

omit [IsDomain V] [ValuationRing V] in
theorem fiberMap_comp_fiberMap :
    Curves.fiberMap h' (f' ≫ p) s ≫ Curves.fiberMap f' p s =
      fiberMapOfEq (h' ≫ f') p (h' ≫ f' ≫ p) (Category.assoc _ _ _) s :=
  fiberMapOfEq_comp f' p (f' ≫ p) rfl s h' (h' ≫ f' ≫ p) rfl

omit [IsDomain V] [ValuationRing V] in
theorem fiberMapOfEq_comp_fiberMap (hcomm : h' ≫ f' = h ≫ fs) :
    fiberMapOfEq h (fs ≫ p) (h' ≫ f' ≫ p) e s ≫ Curves.fiberMap fs p s =
      fiberMapOfEq (h' ≫ f') p (h' ≫ f' ≫ p) (Category.assoc _ _ _) s := by
  rw [← fiberMapOfEq_rfl, fiberMapOfEq_comp]
  apply pullback.hom_ext <;> simp [fiberMapOfEq, hcomm]

open scoped Classical in
/-- **Temkin, proof of Corollary 4.4.3 (1), fibrewise** (T:3145–3149): over a point `s` with
algebraically closed residue field, every point of `Cb_s` in a fibre of `h'_s : Cb_s → C'_s` over
the modification locus of `h'` lies in a fibre of `h_s : Cb_s → Cs_s` over the modification locus
of `h`, provided the fibres of `h_s` form a stable family (`FibresStable`).

The fibres `G'(x)` of `h'_s` are exceptional trees (the stability criterion
`stability_criterion_fibre` for the semi-stable `(C', h'(σ))`), so are the fibres `G(x)` of `h_s`
(for `(Cs, h(σ))`), and all of them lie in the incidence data of `Cb_s` along the locus contracted
to points of `C`, which are anchored (`isAnchored_withMarks`). The fibres of `h_s` are pairwise
separated, so with `FibresStable` they form a stable family, and every exceptional tree, in
particular every `G'(x)`, lies in one of them (Lemma B.3,
`exists_superset_of_finite_eligible`). -/
theorem mem_center_of_mem_center_fibre [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hcomm : h' ≫ f' = h ≫ fs) (hσ : ∀ i, σ i ≫ h' ≫ f' ≫ p = 𝟙 _)
    [IsIntegral C] [IsIntegral C'] [IsIntegral Cs] [IsIntegral Cb]
    [IsModification f'] [IsModification fs] [IsModification h'] [IsModification h]
    [IsProper p] [DeJong.IsNodalCurve (f' ≫ p)] [DeJong.IsNodalCurve (fs ≫ p)]
    [DeJong.IsNodalCurve (h' ≫ f' ≫ p)]
    (hp' : IsProjectiveOver (f' ≫ p)) (hps : IsProjectiveOver (fs ≫ p))
    (hfp' : DeJong.IsRelativelyProjective (f' ≫ p) h')
    (hfps : DeJong.IsRelativelyProjective (fs ≫ p) h)
    (hnormal : IsNormalScheme C) (hnormal' : IsNormalScheme C') (hnormals : IsNormalScheme Cs)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη' : Curves.IsEtaModification h' (f' ≫ p)) (hηs : Curves.IsEtaModification h (fs ≫ p))
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (hg : ∀ v ∈ genericPoints ((h' ≫ f' ≫ p).fiber s), 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((h' ≫ f' ≫ p).fiberToSpecResidueField s)) v)
    (hss' : ∀ x : (f' ≫ p).fiber s, (f' ≫ p).fiberι s x ∈ center h' →
      (Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((f' ≫ p).fiberToSpecResidueField s) x))
    (hss : ∀ x : (fs ≫ p).fiber s, (fs ≫ p).fiberι s x ∈ center h →
      (Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((fs ≫ p).fiberToSpecResidueField s) x))
    (hstab : FibresStable p f' fs h' h e σ s)
    (y : (h' ≫ f' ≫ p).fiber s)
    (hy : (f' ≫ p).fiberι s (Curves.fiberMap h' (f' ≫ p) s y) ∈ center h') :
    (fs ≫ p).fiberι s (fiberMapOfEq h (fs ≫ p) (h' ≫ f' ≫ p) e s y) ∈ center h := by
  classical
  -- instances and data
  have : IsProper (f' ≫ p) := hp'.isProper
  have : IsProper (fs ≫ p) := hps.isProper
  have : IsModification (h' ≫ f') := IsModification.comp h' f'
  have hpq : IsProjectiveOver (h' ≫ f' ≫ p) :=
    DeJong.IsRelativelyProjective.isProjectiveOver hp' hfp'
  have hdim : topologicalKrullDim ((h' ≫ f' ≫ p).fiber s) ≤ 1 :=
    topologicalKrullDim_fiber_le_one_of_isNodalCurve s (h' ≫ f' ≫ p)
  have hpqs := isProjectiveOver_fiberToSpecResidueField (h' ≫ f' ≫ p) s hpq
  have hcurve' : ValuationRing.fiberTrdeg (f' ≫ p) (genericPoint C') ≤ 1 :=
    ValCurves.fiberTrdeg_le_one p hcurve f' _
  have hcurves : ValuationRing.fiberTrdeg (fs ≫ p) (genericPoint Cs) ≤ 1 :=
    ValCurves.fiberTrdeg_le_one p hcurve fs _
  have hpureb := pure_fiber_of_isNodalCurve (h' ≫ f' ≫ p) s
  set φ' := Curves.fiberMap h' (f' ≫ p) s with hφ'
  set φ := fiberMapOfEq h (fs ≫ p) (h' ≫ f' ≫ p) e s with hφ
  set φb := fiberMapOfEq (h' ≫ f') p (h' ≫ f' ≫ p) (Category.assoc _ _ _) s with hφb
  have hφ'b : ∀ z, Curves.fiberMap f' p s (φ' z) = φb z := fun z => by
    rw [← Scheme.Hom.comp_apply, hφ', fiberMap_comp_fiberMap]
  have hφb' : ∀ z, Curves.fiberMap fs p s (φ z) = φb z := fun z => by
    rw [← Scheme.Hom.comp_apply, hφ, fiberMapOfEq_comp_fiberMap p f' fs h' h e s hcomm]
  -- the modification loci
  obtain ⟨J', hJ'⟩ := exists_finset_center (f' ≫ p) h' s hnormal' hcurve'
  obtain ⟨J, hJ⟩ := exists_finset_center (fs ≫ p) h s hnormals hcurves
  have hJ'c : ∀ x ∈ (J' : Set ((f' ≫ p).fiber s)), IsClosed ({x} : Set ((f' ≫ p).fiber s)) :=
    fun x hx => isClosed_singleton_of_mem_center (f' ≫ p) h' s hnormal' hcurve' x ((hJ' x).1 hx)
  have hJc : ∀ x ∈ (J : Set ((fs ≫ p).fiber s)), IsClosed ({x} : Set ((fs ≫ p).fiber s)) :=
    fun x hx => isClosed_singleton_of_mem_center (fs ≫ p) h s hnormals hcurves x ((hJ x).1 hx)
  have hJ'cl : IsClosed (J' : Set ((f' ≫ p).fiber s)) := by
    rw [← Set.biUnion_of_singleton (J' : Set ((f' ≫ p).fiber s))]
    exact isClosed_biUnion_finset fun x hx => hJ'c x hx
  have hJcl : IsClosed (J : Set ((fs ≫ p).fiber s)) := by
    rw [← Set.biUnion_of_singleton (J : Set ((fs ≫ p).fiber s))]
    exact isClosed_biUnion_finset fun x hx => hJc x hx
  set Jb : Set (p.fiber s) := {x | p.fiberι s x ∈ center (h' ≫ f')} with hJb
  have hJbc : ∀ x ∈ Jb, IsClosed ({x} : Set (p.fiber s)) :=
    fun x hx => isClosed_singleton_of_mem_center p (h' ≫ f') s hnormal hcurve x hx
  obtain ⟨Jbf, hJbf⟩ := exists_finset_center p (h' ≫ f') s hnormal hcurve
  have hJbcl : IsClosed Jb := by
    have : Jb = (Jbf : Set (p.fiber s)) := by
      ext x
      exact (hJbf x).symm
    rw [this, ← Set.biUnion_of_singleton (Jbf : Set (p.fiber s))]
    exact isClosed_biUnion_finset fun x hx => hJbc x (this ▸ hx)
  let U : (p.fiber s).Opens := ⟨Jbᶜ, hJbcl.isOpen_compl⟩
  have hU : ∀ y, y ∈ U ↔ y ∉ Jb := fun y => Iff.rfl
  have hiso : IsIso (φb ∣_ U) :=
    isIso_fiberMapOfEq_restrict_of_center (h' ≫ f') p (h' ≫ f' ≫ p) (Category.assoc _ _ _) s Jb
      (fun y => Iff.rfl) U hU
  have hZbc : IsClosed (φb ⁻¹' Jb) := hJbcl.preimage φb.continuous
  -- a component of `Cb_s` contracted by `φb` lies over the modification locus of `h' ≫ f'`
  have hZb : ∀ v ∈ genericPoints ((h' ≫ f' ≫ p).fiber s),
      (∀ z ∈ closure ({v} : Set ((h' ≫ f' ≫ p).fiber s)), φb z = φb v) → v ∈ φb ⁻¹' Jb := by
    intro v hvg hcon
    by_contra hv
    have hsub := subsingleton_preimage_of_not_mem φb Jb U hU hv
    have hcl : closure ({v} : Set ((h' ≫ f' ≫ p).fiber s)) = {v} :=
      (hsub.anti fun z hz => hcon z hz).eq_singleton_of_mem (subset_closure rfl)
    have : IsClosed ({v} : Set ((h' ≫ f' ≫ p).fiber s)) := hcl ▸ isClosed_closure
    exact not_mem_genericPoints_of_isClosed hpureb this hvg
  -- the components of the contracted fibres
  obtain ⟨G', hG'⟩ := exists_innerFinset (f' ≫ p) h' s
  let G : (fs ≫ p).fiber s → Finset ((h' ≫ f' ≫ p).fiber s) := fun x =>
    ((Set.toFinite (genericPoints ((h' ≫ f' ≫ p).fiber s))).subset
      (fun v (hv : v ∈ innerPoints φ x) => hv.1)).toFinset
  have hG : ∀ x, (G x : Set ((h' ≫ f' ≫ p).fiber s)) = innerPoints φ x := fun x =>
    Set.Finite.coe_toFinset _
  have hG'm : ∀ x v, v ∈ G' x → v ∈ genericPoints _ ∧ φ' v = x := fun x v hv => by
    have : v ∈ (G' x : Set ((h' ≫ f' ≫ p).fiber s)) := hv
    rw [hG' x] at this
    exact this
  have hGm : ∀ x v, v ∈ G x → v ∈ genericPoints _ ∧ φ v = x := fun x v hv => by
    have : v ∈ (G x : Set ((h' ≫ f' ≫ p).fiber s)) := hv
    rw [hG x] at this
    exact this
  -- the double points
  have hfinN : ∀ Z, (nodesIn ((h' ≫ f' ≫ p).fiberToSpecResidueField s) Z).Finite :=
    fun Z => finite_nodesIn _ hdim hpqs Z
  let _ : Fintype (nodesIn ((h' ≫ f' ≫ p).fiberToSpecResidueField s)
    (φ' ⁻¹' (J' : Set ((f' ≫ p).fiber s)))) := (hfinN _).fintype
  let _ : Fintype (nodesIn ((h' ≫ f' ≫ p).fiberToSpecResidueField s)
    (φ ⁻¹' (J : Set ((fs ≫ p).fiber s)))) := (hfinN _).fintype
  let _ : Fintype (nodesIn ((h' ≫ f' ≫ p).fiberToSpecResidueField s)
    (contractedLocus p f' h' s)) := (hfinN _).fintype
  -- the marks
  let m' : (f' ≫ p).fiber s → ℕ := fun x =>
    (Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card
  let m : (fs ≫ p).fiber s → ℕ := fun x =>
    (Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card
  have hyi : ∀ i, ∃ y : (h' ≫ f' ≫ p).fiber s, (h' ≫ f' ≫ p).fiberι s y = σ i s := fun i => by
    have : σ i s ∈ (h' ≫ f' ≫ p) ⁻¹' {s} := by
      change (h' ≫ f' ≫ p) (σ i s) = s
      rw [← Scheme.Hom.comp_apply, hσ i]
      rfl
    rw [← Scheme.Hom.range_fiberι] at this
    exact this
  choose yi hyi using hyi
  choose mk hmkg hmkc using fun i => exists_mem_genericPoints_mem_closure (yi i)
  -- the stability criterion for `h'` and for `h`
  obtain ⟨hA', hB', -⟩ := stability_criterion_fibre (f' ≫ p) h' s hsep hp' hfp' hnormal' hcurve' hη'
    (pure_fiber_of_isNodalCurve (f' ≫ p) s) J' hJ' G' (fun x _ => hG' x) hdim
    (fun x _ v hv => hg v (hG'm x v hv).1) m'
  have hexc' := hB' fun x hx => ⟨nodes_fiber_of_isNodalCurve (f' ≫ p) s x (hJ'c x hx),
    (hss' x ((hJ' x).1 hx)).1, (hss' x ((hJ' x).1 hx)).2⟩
  obtain ⟨hA, hB, -⟩ := stability_criterion_fibre_of_eq (fs ≫ p) h (h' ≫ f' ≫ p) e s hsep hps hfps
    hnormals hcurves hηs (pure_fiber_of_isNodalCurve (fs ≫ p) s) J hJ G (fun x _ => hG x) hdim
    (fun x _ v hv => hg v (hGm x v hv).1) m
  have hexc := hB fun x hx => ⟨nodes_fiber_of_isNodalCurve (fs ≫ p) s x (hJc x hx),
    (hss x ((hJ x).1 hx)).1, (hss x ((hJ x).1 hx)).2⟩
  -- the contracted fibres lie in the locus contracted to points of `C`
  have hZ'v : ∀ x ∈ J', ∀ v ∈ G' x, v ∈ φb ⁻¹' Jb := by
    intro x hx v hv
    obtain ⟨hvg, hvx⟩ := hG'm x v hv
    refine hZb v hvg fun z hz => ?_
    rw [← hφ'b, ← hφ'b, eq_of_mem_closure_of_isClosed φ' (hvx ▸ hJ'c x hx) hz]
  have hZv : ∀ x ∈ J, ∀ v ∈ G x, v ∈ φb ⁻¹' Jb := by
    intro x hx v hv
    obtain ⟨hvg, hvx⟩ := hGm x v hv
    refine hZb v hvg fun z hz => ?_
    rw [← hφb', ← hφb', eq_of_mem_closure_of_isClosed φ (hvx ▸ hJc x hx) hz]
  have hZ'sub : φ' ⁻¹' (J' : Set ((f' ≫ p).fiber s)) ⊆ contractedLocus p f' h' s := by
    intro z hz
    obtain ⟨v, hv, hzv⟩ := (hA' (φ' z) hz).2 z rfl
    exact closure_subset_of_mem hZbc (hZ'v _ hz v hv) hzv
  have hZsub : φ ⁻¹' (J : Set ((fs ≫ p).fiber s)) ⊆ contractedLocus p f' h' s := by
    intro z hz
    obtain ⟨v, hv, hzv⟩ := (hA (φ z) hz).2 z rfl
    exact closure_subset_of_mem hZbc (hZv _ hz v hv) hzv
  -- the incidence data `Γ` of `Cb_s` along the contracted locus, with the marks
  set Γ := withMarks (nodalGraph ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim
    (contractedLocus p f' h' s)) mk with hΓ
  have hJ'pre : IsClosed (φ' ⁻¹' (J' : Set ((f' ≫ p).fiber s))) := hJ'cl.preimage φ'.continuous
  have hJpre : IsClosed (φ ⁻¹' (J : Set ((fs ≫ p).fiber s))) := hJcl.preimage φ.continuous
  -- the fibres of `h'` are exceptional trees of `Γ`
  have hexcΓ' : ∀ x ∈ J', Γ.IsExceptionalTree (G' x) := by
    intro x hx
    have htr := isTransfer_nodalGraph ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim hZ'sub mk
      (G' x) fun v hv => closure_subset_of_mem hJ'pre
        (show φ' v ∈ (J' : Set ((f' ≫ p).fiber s)) by rw [(hG'm x v hv).2]; exact hx)
    obtain ⟨htree, hcard⟩ := hexc' x hx
    refine ⟨(isP1Tree_iff_of_transfer htr subset_rfl).2 htree, fun v hv => ⟨hZ'v x hx v hv,
      (hG'm x v hv).1⟩, ?_⟩
    rw [card_boundary_of_transfer htr subset_rfl]
    have hm : (Γ.marks (G' x)).card ≤ m' x := by
      refine Finset.card_le_card fun i hi => ?_
      rw [mem_marks] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨-, hix⟩ := hG'm x (mk i) hi
      have hyx : φ' (yi i) = x := by
        rw [eq_of_mem_closure_of_isClosed φ' (hix ▸ hJ'c x hx) (hmkc i), hix]
      rw [← hyi i, ← hyx, ← Scheme.Hom.comp_apply, ← Curves.fiberMap_fiberι, Scheme.Hom.comp_apply]
    exact le_trans (Nat.add_le_add_right hm _) (by rw [Nat.add_comm]; exact hcard)
  -- the fibres of `h` are exceptional trees of `Γ`
  have hexcΓ : ∀ x ∈ J, Γ.IsExceptionalTree (G x) := by
    intro x hx
    have htr := isTransfer_nodalGraph ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim hZsub mk
      (G x) fun v hv => closure_subset_of_mem hJpre
        (show φ v ∈ (J : Set ((fs ≫ p).fiber s)) by rw [(hGm x v hv).2]; exact hx)
    obtain ⟨htree, hcard⟩ := hexc x hx
    refine ⟨(isP1Tree_iff_of_transfer htr subset_rfl).2 htree, fun v hv => ⟨hZv x hx v hv,
      (hGm x v hv).1⟩, ?_⟩
    rw [card_boundary_of_transfer htr subset_rfl]
    have hm : (Γ.marks (G x)).card ≤ m x := by
      refine Finset.card_le_card fun i hi => ?_
      rw [mem_marks] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨-, hix⟩ := hGm x (mk i) hi
      have hyx : φ (yi i) = x := by
        rw [eq_of_mem_closure_of_isClosed φ (hix ▸ hJc x hx) (hmkc i), hix]
      rw [← hyi i, ← hyx, hφ, fiberι_fiberMapOfEq_apply]
    exact le_trans (Nat.add_le_add_right hm _) (by rw [Nat.add_comm]; exact hcard)
  -- the fibres of `h` form a stable family
  have h𝒯 : Γ.IsStableFamily (J.image G) := by
    refine ⟨fun T hT => ?_, fun T hT T' hT' hne hm => ?_, fun v hv hstar => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hT
      exact hexcΓ x hx
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hT
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hT'
      refine hne (congrArg G ?_)
      rcases hm with ⟨v, hv⟩ | ⟨e, ⟨a, ha, haT⟩, ⟨b, hb, hbT⟩⟩
      · rw [Finset.mem_inter] at hv
        exact (hGm x v hv.1).2.symm.trans (hGm x' v hv.2).2
      · have hea := ((mem_nodalGraph_ends _ hdim e a).1 ha).2
        have heb := ((mem_nodalGraph_ends _ hdim e b).1 hb).2
        obtain ⟨-, hax⟩ := hGm x a haT
        obtain ⟨-, hbx⟩ := hGm x' b hbT
        have h1 := eq_of_mem_closure_of_isClosed φ (hax ▸ hJc x hx) hea
        have h2 := eq_of_mem_closure_of_isClosed φ (hbx ▸ hJc x' hx') heb
        rw [← hax, ← hbx, ← h1, ← h2]
    · by_cases hvg : v ∈ genericPoints ((h' ≫ f' ≫ p).fiber s)
      · exact hstab hdim mk (fun i => ⟨hmkg i, yi i, hyi i, hmkc i⟩) J hJ G (fun x _ => hG x) v
          hvg (fun x hx hvx => hv (G x) (Finset.mem_image_of_mem G hx) hvx) hstar
      · exact hvg (hstar.subset_eligible (self_mem_star _ v)).2
  -- anchoring
  have hconn : ConnectedSpace ((h' ≫ f' ≫ p).fiber s) :=
    ((h' ≫ f' ≫ p).fiberHomeo s).connectedSpace_iff.2 (isConnected_iff_connectedSpace.1
      (Cohomology.Connected.isConnected_fiber_of_irreducibleSpace hsep (h' ≫ f' ≫ p) hpq s))
  have hanch : Γ.IsAnchored :=
    isAnchored_withMarks ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim φb Jb hJbc hJbcl U hU
      hpure (fun y _ hy => nodes_fiber_of_isNodalCurve (h' ≫ f' ≫ p) s y hy) mk
  have hfin : Γ.eligible.Finite :=
    (Set.toFinite (genericPoints ((h' ≫ f' ≫ p).fiber s))).subset Set.inter_subset_right
  -- conclusion: the fibre of `h'` through `y` lies in a fibre of `h`
  have hxJ' : φ' y ∈ J' := (hJ' _).2 hy
  obtain ⟨T, hT, hsub⟩ := exists_superset_of_finite_eligible hanch hfin h𝒯 (hexcΓ' _ hxJ')
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.1 hT
  obtain ⟨v, hv, hyv⟩ := (hA' _ hxJ').2 y rfl
  obtain ⟨-, hvx⟩ := hGm x₁ v (hsub hv)
  have : φ y = x₁ := by
    rw [eq_of_mem_closure_of_isClosed φ (hvx ▸ hJc x₁ hx₁) hyv, hvx]
  exact (hJ _).1 (this ▸ hx₁)

open scoped Classical in
/-- **Temkin, Corollary 4.4.3 (1), pointwise** (T:3145–3149): every point of `Cb` contracted by
`h'` (mapping into the modification locus of `h'`) is contracted by `h`, provided the fibres of
`h` form stable families (`FibresStable`) in all fibres. -/
theorem mem_center_of_mem_center [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hac : ∀ s : Spec (CommRingCat.of V), IsAlgClosed ((Spec (CommRingCat.of V)).residueField s))
    (hcomm : h' ≫ f' = h ≫ fs) (hσ : ∀ i, σ i ≫ h' ≫ f' ≫ p = 𝟙 _)
    [IsIntegral C] [IsIntegral C'] [IsIntegral Cs] [IsIntegral Cb]
    [IsModification f'] [IsModification fs] [IsModification h'] [IsModification h]
    [IsProper p] [DeJong.IsNodalCurve (f' ≫ p)] [DeJong.IsNodalCurve (fs ≫ p)]
    [DeJong.IsNodalCurve (h' ≫ f' ≫ p)]
    (hp' : IsProjectiveOver (f' ≫ p)) (hps : IsProjectiveOver (fs ≫ p))
    (hfp' : DeJong.IsRelativelyProjective (f' ≫ p) h')
    (hfps : DeJong.IsRelativelyProjective (fs ≫ p) h)
    (hnormal : IsNormalScheme C) (hnormal' : IsNormalScheme C') (hnormals : IsNormalScheme Cs)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη' : Curves.IsEtaModification h' (f' ≫ p)) (hηs : Curves.IsEtaModification h (fs ≫ p))
    (hpure : ∀ s, ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (hg : ∀ s, ∀ v ∈ genericPoints ((h' ≫ f' ≫ p).fiber s), 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((h' ≫ f' ≫ p).fiberToSpecResidueField s)) v)
    (hss' : ∀ s, ∀ x : (f' ≫ p).fiber s, (f' ≫ p).fiberι s x ∈ center h' →
      (Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((f' ≫ p).fiberToSpecResidueField s) x))
    (hss : ∀ s, ∀ x : (fs ≫ p).fiber s, (fs ≫ p).fiberι s x ∈ center h →
      (Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((fs ≫ p).fiberToSpecResidueField s) x))
    (hstab : ∀ s, FibresStable p f' fs h' h (comp_eq_of_comm p f' fs h' h hcomm) σ s)
    (xb : Cb) (hx : h' xb ∈ center h') : h xb ∈ center h := by
  set s := (h' ≫ f' ≫ p) xb
  have := hac s
  have hxs : xb ∈ Set.range ((h' ≫ f' ≫ p).fiberι s) := by
    rw [Scheme.Hom.range_fiberι]
    rfl
  obtain ⟨y, hy⟩ := hxs
  have h1 : (f' ≫ p).fiberι s (Curves.fiberMap h' (f' ≫ p) s y) = h' xb := by
    rw [← Scheme.Hom.comp_apply, Curves.fiberMap_fiberι, Scheme.Hom.comp_apply, hy]
  have := mem_center_of_mem_center_fibre p f' fs h' h (comp_eq_of_comm p f' fs h' h hcomm) σ s hsep
    hcomm hσ hp' hps hfp' hfps hnormal hnormal' hnormals hcurve hη' hηs (hpure s) (hg s) (hss' s)
    (hss s) (hstab s) y (h1 ▸ hx)
  rwa [fiberι_fiberMapOfEq_apply, hy] at this

open scoped Classical in
/-- **Temkin, Corollary 4.4.3 (1)** (`sepcloscor`, T:3135–3149), for curves projective over a
valuation ring `V` with finitely many primes (blueprint `cor:sm-domination-stable` (1),
`thm:sm-dom-main`). Let `C` be an integral normal relative curve, projective over `V`, `fs : Cs → C`
and `f' : C' → C` modifications by nodal curves projective over `V` with `Cs`, `C'` normal, both
dominated by a nodal modification `Cb` (`h ≫ fs = h' ≫ f'`) through η-modifications projective
relative to the targets, with marks given by sections `σ i` of `Cb`. Assume that `(C', h'(σ))` and
`(Cs, h(σ))` are semi-stable at the points of the modification loci of `h'`, `h` (numerical form:
at most one mark, at a smooth point), that the fibres of `h` form stable families
(`FibresStable`: the fibrewise stability of `Cs`, read on `Cb`), and the standing hypotheses of
the stability criterion (the residue fields of `V` algebraically closed, the fibres of `C` of pure
dimension one, the components of the fibres of `Cb` of nonnegative genus). Then `C'` dominates
`Cs`: there is `g : C' → Cs` with `g ≫ fs = f'`.

Proof (Temkin): a component of a fibre of `Cb` contracted by `h'` is contracted by `h`
(`mem_center_of_mem_center`); hence every valuation ring of `Γ₀(Cs)` (centred at a generic point
of a fibre of `Cs` over a closed point of `C`) is centred, through `Cb` (where `h` is a local
isomorphism), at a point of `Cb` not contracted by `h'`, hence at a generic point of a fibre of
`C'`: `Γ₀(Cs) ⊆ Γ₀(C')`, and the normal `C'` dominates `Cs` by Proposition 4.2.3
(`ValCurves.dominates_of_gammaZeroSet_subset`). -/
theorem dominates_of_fibresStable [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hac : ∀ s : Spec (CommRingCat.of V), IsAlgClosed ((Spec (CommRingCat.of V)).residueField s))
    (hcomm : h' ≫ f' = h ≫ fs) (hσ : ∀ i, σ i ≫ h' ≫ f' ≫ p = 𝟙 _)
    [IsIntegral C] [IsIntegral C'] [IsIntegral Cs] [IsIntegral Cb]
    [IsModification f'] [IsModification fs] [IsModification h'] [IsModification h]
    [IsProper p] [DeJong.IsNodalCurve (f' ≫ p)] [DeJong.IsNodalCurve (fs ≫ p)]
    [DeJong.IsNodalCurve (h' ≫ f' ≫ p)]
    (hp' : IsProjectiveOver (f' ≫ p)) (hps : IsProjectiveOver (fs ≫ p))
    (hfp' : DeJong.IsRelativelyProjective (f' ≫ p) h')
    (hfps : DeJong.IsRelativelyProjective (fs ≫ p) h)
    (hnormal : IsNormalScheme C) (hnormal' : IsNormalScheme C') (hnormals : IsNormalScheme Cs)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη' : Curves.IsEtaModification h' (f' ≫ p)) (hηs : Curves.IsEtaModification h (fs ≫ p))
    (hpure : ∀ s, ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (hg : ∀ s, ∀ v ∈ genericPoints ((h' ≫ f' ≫ p).fiber s), 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((h' ≫ f' ≫ p).fiberToSpecResidueField s)) v)
    (hss' : ∀ s, ∀ x : (f' ≫ p).fiber s, (f' ≫ p).fiberι s x ∈ center h' →
      (Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((f' ≫ p).fiberToSpecResidueField s) x))
    (hss : ∀ s, ∀ x : (fs ≫ p).fiber s, (fs ≫ p).fiberι s x ∈ center h →
      (Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((fs ≫ p).fiberToSpecResidueField s) x))
    (hstab : ∀ s, FibresStable p f' fs h' h (comp_eq_of_comm p f' fs h' h hcomm) σ s) :
    ValCurves.Dominates f' fs := by
  have : CompactSpace C := compactSpace_of_quasiCompact p
  have : C.IsSeparated := ValCurves.isSeparated_of_isSeparated p
  have : IsModification (h' ≫ f') := IsModification.comp h' f'
  have hcurves : ValuationRing.fiberTrdeg (fs ≫ p) (genericPoint Cs) ≤ 1 :=
    ValCurves.fiberTrdeg_le_one p hcurve fs _
  refine ValCurves.dominates_of_gammaZeroSet_subset p fs f' hnormal' hcurve ?_
  rintro W ⟨⟨x, hx, hW⟩, c, hc, hWc⟩
  have hlift : ValCurves.genericLift (h' ≫ f') ≫ h = ValCurves.genericLift fs :=
    ValCurves.genericLift_comp_of_comp fs (h' ≫ f') h hcomm.symm
  obtain ⟨xb, hWb, hxb⟩ := hW.exists_of_universallyClosed h hlift
  have hxiso : h xb ∈ isomorphismOpen h :=
    hxb ▸ ValCurves.mem_isomorphismOpen_of_mem_fibreGenericSet (fs ≫ p) hnormals hcurves h hx
  have hx'iso : h' xb ∈ isomorphismOpen h' := by
    by_contra hn
    exact (mem_center_of_mem_center p f' fs h' h σ hsep hac hcomm hσ hp' hps hfp' hfps hnormal
      hnormal' hnormals hcurve hη' hηs hpure hg hss' hss hstab xb hn) hxiso
  have : IsIso (h'.stalkMap xb) := ValCurves.isIso_stalkMap_of_mem_isomorphismOpen h' hx'iso
  have : IsIso (h.stalkMap xb) := ValCurves.isIso_stalkMap_of_mem_isomorphismOpen h hxiso
  have z' : ValuationRing.fiberTrdeg h' xb = 0 :=
    (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero _ _).1 ValCurves.isAlgebraicAt_of_isIso_stalkMap
  have z : ValuationRing.fiberTrdeg h xb = 0 :=
    (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero _ _).1 ValCurves.isAlgebraicAt_of_isIso_stalkMap
  have e1 := ValCurves.fiberTrdeg_comp h' (f' ≫ p) xb
  have e2 := ValCurves.fiberTrdeg_comp h (fs ≫ p) xb
  rw [comp_eq_of_comm p f' fs h' h hcomm, e1, z, z', add_zero, add_zero, hxb] at e2
  have hl' : ValCurves.genericLift (h' ≫ f') ≫ h' = ValCurves.genericLift f' :=
    ValCurves.genericLift_comp_of_comp f' (h' ≫ f') h' rfl
  refine ⟨⟨h' xb, ?_, hl' ▸ hWb.comp h'⟩, c, hc, hWc⟩
  rw [ValCurves.mem_fibreGenericSet_iff, e2]
  exact hx

end Fibre

end

end DeJongAlterations.StableModification.BlowDown.Domination
