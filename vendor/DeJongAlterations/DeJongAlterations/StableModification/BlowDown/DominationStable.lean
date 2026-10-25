/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.Domination
import DeJongAlterations.StableModification.DeJong.NodalBaseChange

/-!
# The stable-family condition from the stability of `C_st` (Temkin, App. B, Lemma B.3)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), App. B,
T:4463–4467 and the proof of Corollary 4.4.3 (T:3145–3149): a blow-down `φ : X → Y` of curves
contracting a separated family `𝒯` of exceptional trees maps a component `v ∉ ⋃ 𝒯` to a component
`φ v` of `Y` whose preimage is the star `st(v) = {v} ∪ ⋃ {T ∈ 𝒯 : T meets v}`, and `φ v` is an
exceptional component of `Y` when `st(v)` is an exceptional tree of `X` (blueprint
`def:sm-stable-family`). Hence, if `Y` has no exceptional component, `𝒯` is a stable family.
The combinatorial core (`CurvesField/Trees.lean`) takes this as the definition of a stable
family; here it is proved for the fibre map `h_s : Cb_s → Cs_s` of Corollary 4.4.3, which
completes the proof of Corollary 4.4.3 (1) (`dominates_of_fibreStable`; blueprint
`cor:sm-domination-stable` (1), chapter `sm-blow-down-domination.tex`).

For `w = φ v` (`v` a component of `X` not contracted, whose star `S` is an exceptional tree):

* `w` has the genus of `v`: the normalization of `X` in `Spec κ(v)`, composed with `φ`, is the
  normalization of `Y` in `Spec κ(w)` (`compNormalizationIso`, `componentGenus_comp_eq`;
  adapted from lane T44A3's `normalizationPointsIso`), and the branches of `w` at `z` are the
  branches of `v` over `φ⁻¹(z)` (`branchCount_comp_eq`);
* `w` has no double point of its own (`inner_singleton_image_eq_empty`): off the contracted points
  it would be one of `v`; at a contracted point `x` the branches of `w` are the double points
  joining `v` to the connected fibre `φ⁻¹(x)`, of which there is at most one in the tree `S`
  (`eq_of_ends_of_isTree`);
* the marks and the double points of `w` come from distinct marks and boundary double points of
  `S` (`marks_image_subset`, `card_boundary_image_le`).

So `w` is an exceptional component of `Y` in the combinatorial sense
(`CurvesField.IncidenceGraph.IsExceptional`: contracted to a point of `C`, genus `0`, no double
point of its own, at most two marks and double points). The stability of `Cs` is used in this
form (`FibreStable`); its comparison with `Curves.IsStableModification` (embedded `ℙ¹`) or with the
numerical stability of `PLAN-T5.md` §1.3 (arithmetic genus of the reduced component) is not part
of this file.

## Main results

* `compNormalizationIso`, `componentGenus_comp_eq`, `branchCount_comp_eq`,
  `isFinite_normalizationPointsMap_comp`: components not contracted by `φ`.
* `inner_singleton_image_eq_empty`, `card_boundary_image_le`, `marks_image_subset`: the image of
  a component with exceptional star.
* `FibreStable`: numerical stability of the fibre `Cs_s`; `isExceptional_withMarks_iff` reads an
  exceptional component on the incidence data along its own closure.
* `fibresStable_of_fibreStable`: `FibreStable` gives the stable-family condition `FibresStable`.
* `dominates_of_fibreStable`: **Temkin's Corollary 4.4.3 (1)** for curves projective over `V`;
  `dominates_of_fibreStable_of_marks`: the same with the marks hypotheses in pointwise form
  (`marks_semistable_of_injective`).
* `nonempty_iso_of_fibreStable`: two stable modifications dominated by a common one are isomorphic
  over `C` (Corollary 4.4.3 (1) twice; `PLAN-T5.md` node V3).
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

section ComponentNormalization

/-! ### The normalization of a component not contracted by `φ`

Let `φ : X → Y` be an isomorphism over the complement `U` of a closed set `J`, and `v` a generic
point of `X` with `φ v ∉ J`. The normalization of `X` in `Spec κ(v)`, composed with `φ`, is the
normalization of `Y` in `Spec κ(φ v)` (`compNormalizationIso`): the composite is finite (proper,
with finite fibres) and `κ(v) ≅ κ(φ v)`. (Adapted from lane T44A3's `normalizationPointsIso`
for closed immersions, `BlowDown/ExcSpecializeGenus.lean`.) -/

variable {X Y : Scheme.{u}} (φ : X ⟶ Y)

/-- The residue field isomorphism `Spec κ_Y(φ v) ≅ Spec κ_X(v)` for the point of `{v}`. -/
def compPointsIsoAux (v : X) [IsIso (φ.residueFieldMap v)] : ∀ x : ({v} : Set X),
    Spec (Y.residueField ((Equiv.ofUnique ({v} : Set X) ({φ v} : Set Y)) x).1) ≅
      Spec (X.residueField x.1)
  | ⟨_, rfl⟩ => (asIso (Spec.map (φ.residueFieldMap v))).symm

/-- The points scheme of `{v}` in `X` is that of `{φ v}` in `Y`. -/
def compPointsIso (v : X) [IsIso (φ.residueFieldMap v)] :
    pointsScheme X ({v} : Set X) ≅ pointsScheme Y ({φ v} : Set Y) :=
  Sigma.whiskerEquiv (Equiv.ofUnique _ _) (compPointsIsoAux φ v)

theorem compPointsIso_hom_pointsMap (v : X) [IsIso (φ.residueFieldMap v)] :
    (compPointsIso φ v).hom ≫ pointsMap Y ({φ v} : Set Y) = pointsMap X ({v} : Set X) ≫ φ := by
  refine Sigma.hom_ext _ _ fun w => ?_
  obtain ⟨w, rfl⟩ := w
  simp only [compPointsIso, Sigma.whiskerEquiv_hom, Sigma.ι_comp_map'_assoc, ι_pointsMap,
    ι_pointsMap_assoc]
  change Spec.map (φ.residueFieldMap w) ≫ Y.fromSpecResidueField (φ w) = _
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField φ w

variable [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))]

/-- **The normalization of a component not contracted by `φ`**: the normalization of `X` in
`Spec κ(v)` is that of `Y` in `Spec κ(φ v)`, over `Y`. -/
def compNormalizationIso [QuasiCompact φ] [QuasiSeparated φ] (v : X)
    [IsIso (φ.residueFieldMap v)] [IsIntegralHom (normalizationPointsMap ({v} : Set X) ≫ φ)] :
    normalizationPoints ({v} : Set X) ≅ normalizationPoints ({φ v} : Set Y) :=
  (normalizationCompIso (pointsMap X ({v} : Set X)) φ).symm ≪≫
    normalizationIsoOfIso (pointsMap X ({v} : Set X) ≫ φ) (pointsMap Y ({φ v} : Set Y))
      (compPointsIso φ v) (compPointsIso_hom_pointsMap φ v)

theorem compNormalizationIso_hom_comp [QuasiCompact φ] [QuasiSeparated φ] (v : X)
    [IsIso (φ.residueFieldMap v)] [IsIntegralHom (normalizationPointsMap ({v} : Set X) ≫ φ)] :
    (compNormalizationIso φ v).hom ≫ normalizationPointsMap ({φ v} : Set Y) =
      normalizationPointsMap ({v} : Set X) ≫ φ := by
  simp only [compNormalizationIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [normalizationIsoOfIso_hom_fromNormalization, Iso.inv_comp_eq,
    normalizationCompIso_hom_fromNormalization]

/-- `structureCoeff (f ≫ q) = f^♯ ∘ structureCoeff q`. -/
theorem structureCoeff_comp' {k : Type u} [Field k] {Z W : Scheme.{u}} (q : W ⟶ Spec (.of k))
    (f : Z ⟶ W) : structureCoeff (f ≫ q) = f.appTop.hom.comp (structureCoeff q) := by
  ext a
  simp [structureCoeff]

/-- **The genus of a component not contracted by `φ`** is that of its image. -/
theorem componentGenus_comp_eq [CompactSpace X] [CompactSpace Y] [QuasiCompact φ]
    [QuasiSeparated φ] {k : Type u} [Field k]
    (qY : Y ⟶ Spec (.of k)) (v : X) [IsIso (φ.residueFieldMap v)]
    [IsIntegralHom (normalizationPointsMap ({v} : Set X) ≫ φ)] :
    componentGenus (structureCoeff (φ ≫ qY)) v = componentGenus (structureCoeff qY) (φ v) := by
  unfold componentGenus arithmeticGenus
  congr 1
  rw [← structureCoeff_comp', ← structureCoeff_comp']
  refine BlowDown.eulerChar_eq_of_iso _ _ (compNormalizationIso φ v) ?_
  rw [← Category.assoc, compNormalizationIso_hom_comp, Category.assoc]

/-- **The branches of the image component** at `z` are the branches of `v` over `φ⁻¹(z)`. -/
theorem branchCount_comp_eq [QuasiCompact φ] [QuasiSeparated φ] (v : X)
    [IsIso (φ.residueFieldMap v)] [IsIntegralHom (normalizationPointsMap ({v} : Set X) ≫ φ)]
    (z : Y) :
    branchCount (φ v) z =
      Nat.card ↥(normalizationPointsMap ({v} : Set X) ⁻¹' (φ ⁻¹' {z})) := by
  let e := compNormalizationIso φ v
  have hcomp : ∀ a, normalizationPointsMap ({φ v} : Set Y) (e.hom a) =
      φ (normalizationPointsMap ({v} : Set X) a) := fun a => by
    rw [← Scheme.Hom.comp_apply, compNormalizationIso_hom_comp, Scheme.Hom.comp_apply]
  have hb := ConcreteCategory.bijective_of_isIso e.hom.base
  refine (Nat.card_congr (Equiv.ofBijective
    (fun a : ↥(normalizationPointsMap ({v} : Set X) ⁻¹' (φ ⁻¹' {z})) =>
      (⟨e.hom a.1, by
        change normalizationPointsMap ({φ v} : Set Y) (e.hom a.1) = z
        rw [hcomp]
        exact a.2⟩ : ↥(normalizationPointsMap ({φ v} : Set Y) ⁻¹' {z})))
    ⟨fun a b hab => Subtype.ext (hb.1 (congrArg Subtype.val hab)), fun b => ?_⟩)).symm
  obtain ⟨a, ha⟩ := hb.2 b.1
  refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
  change φ (normalizationPointsMap ({v} : Set X) a) = z
  rw [← hcomp]
  exact (congrArg _ ha).trans b.2

end ComponentNormalization

section Finite

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) (J : Set Y) (U : Y.Opens) (hU : ∀ y, y ∈ U ↔ y ∉ J)
  [IsIso (φ ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from X))] {k : Type u} [Field k]
  (p' : X ⟶ Spec (.of k)) [LocallyOfFiniteType p']

include hU p' in
/-- **The normalization of a component not contracted by `φ`, composed with `φ`, is finite**
(proper with finite fibres; as `isFinite_outerSetMap`). -/
theorem isFinite_normalizationPointsMap_comp [CompactSpace X] [Finite (genericPoints X)]
    [IsProper φ] (hdim : topologicalKrullDim X ≤ 1) (hJ : IsClosed J) {v : X}
    (hv : v ∈ genericPoints X) (hvJ : φ v ∉ J) :
    IsFinite (normalizationPointsMap ({v} : Set X) ≫ φ) := by
  have := isFinite_normalizationPointsMap (S := ({v} : Set X)) p'
  have := isLocallyNoetherian_of_locallyOfFiniteType p'
  have : IsNoetherian X := ⟨⟩
  have hfib : ∀ z : X, ((normalizationPointsMap ({v} : Set X)) ⁻¹' {z}).Finite :=
    fun z => (normalizationPointsMap ({v} : Set X)).finite_preimage_singleton z
  have : LocallyQuasiFinite (normalizationPointsMap ({v} : Set X) ≫ φ) := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    by_cases hy : y ∈ J
    · refine ((finite_closure_outerSet_inter φ J hdim hJ).preimage' fun z _ => hfib z).subset ?_
      intro w hw
      change normalizationPointsMap ({v} : Set X) w ∈ closure (outerSet φ J) ∩ φ ⁻¹' J
      refine ⟨closure_mono (Set.singleton_subset_iff.2 (show v ∈ outerSet φ J from ⟨hv, hvJ⟩))
        (range_normalizationPointsMap_subset _ ⟨w, rfl⟩), ?_⟩
      have : φ (normalizationPointsMap ({v} : Set X) w) = y := hw
      change φ (normalizationPointsMap ({v} : Set X) w) ∈ J
      rw [this]
      exact hy
    · exact ((subsingleton_preimage_of_not_mem φ J U hU hy).finite).preimage' fun z _ => hfib z
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Finite

section Branches

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
  [LocallyOfFiniteType q]

/-- The multiplicity of a component among the branches at `z` is its number of branches. -/
theorem count_branches [DecidableEq X] {v : X} (hv : v ∈ genericPoints X) (z : X) :
    (branches z).count v = branchCount v z := by
  rw [branches, Multiset.count_sum']
  simp only [Multiset.count_nsmul, Multiset.count_singleton]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hwv
    simp [Ne.symm hwv]
  · intro h
    exact absurd (mem_genericFinset.2 hv) h

/-- In a multiset with two elements, a member `u` leaves at most one place to `v ≠ u`. -/
theorem count_le_one_of_card_eq_two {α : Type*} [DecidableEq α] {m : Multiset α}
    (hm : Multiset.card m = 2) {u v : α} (hu : u ∈ m) (huv : u ≠ v) : m.count v ≤ 1 := by
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hm
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  rcases hu with rfl | rfl <;> split_ifs <;> simp_all

include q in
/-- **A smooth point lies on a single component.** -/
theorem eq_of_mem_closure_of_isSmoothAt [IsReduced X] (hdim : topologicalKrullDim X ≤ 1)
    [CompactSpace X] {y v₁ v₂ : X} (hsm : DeJong.IsSmoothAt q y) (h₁ : v₁ ∈ genericPoints X)
    (h₂ : v₂ ∈ genericPoints X) (hy₁ : y ∈ closure {v₁}) (hy₂ : y ∈ closure {v₂}) : v₁ = v₂ := by
  by_cases hyg : y ∈ genericPoints X
  · exact (eq_of_mem_closure_of_mem_genericPoints hyg hy₁).trans
      (eq_of_mem_closure_of_mem_genericPoints hyg hy₂).symm
  by_contra hne
  have : LocallyOfFinitePresentation q := by
    have := isLocallyNoetherian_of_locallyOfFiniteType q
    infer_instance
  have hyc := isClosed_singleton_of_not_mem_genericPoints hdim hyg
  have h2 := two_le_natCard_fiber q h₁ h₂ hne hy₁ hy₂
  rw [natCard_fiber_eq_one_of_isSmoothAt q hdim y hyc hyg hsm] at h2
  omega

end Branches

section TreeEdges

variable {V : Type*} {E : Type*} {M : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype M] [DecidableEq M] {G : IncidenceGraph V E M}

/-- **A tree has at most one double point between a component `v` and a connected subcurve `T`
not containing it** (otherwise `{v} ∪ T` would contain a cycle). -/
theorem eq_of_ends_of_isTree {S T : Finset V} (hS : G.IsTree S) {v : V} (hv : v ∈ S)
    (hTS : T ⊆ S) (hvT : v ∉ T) (hT : G.IsConnected T) {e₁ e₂ : E} {u₁ u₂ : V} (hu₁ : u₁ ∈ T)
    (hu₂ : u₂ ∈ T) (he₁ : G.ends e₁ = s(v, u₁)) (he₂ : G.ends e₂ = s(v, u₂)) : e₁ = e₂ := by
  by_contra hne
  set A := insert v T with hA
  have hAS : A ⊆ S := Finset.insert_subset hv hTS
  have hbound := hS.card_inner_add_one_le hAS (Finset.insert_nonempty v T)
  have hcon := hT.card_le_card_inner_add_one
  have hnotT : ∀ e, G.ends e = s(v, u₁) ∨ G.ends e = s(v, u₂) → e ∉ G.inner T := by
    intro e he hin
    rcases he with he | he <;> exact hvT ((mem_inner_of_ends he).1 hin).1
  have hsub : insert e₁ (insert e₂ (G.inner T)) ⊆ G.inner A := by
    intro e he
    simp only [Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact (mem_inner_of_ends he₁).2 ⟨Finset.mem_insert_self v T, Finset.mem_insert_of_mem hu₁⟩
    · exact (mem_inner_of_ends he₂).2 ⟨Finset.mem_insert_self v T, Finset.mem_insert_of_mem hu₂⟩
    · exact inner_mono (Finset.subset_insert v T) he
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem (hnotT e₂ (Or.inr he₂))] at hcard
  · rw [Finset.card_insert_of_notMem hvT] at hbound
    omega
  · simp only [Finset.mem_insert, not_or]
    exact ⟨hne, hnotT e₁ (Or.inl he₁)⟩

end TreeEdges

section StarImage

/-! ### The image of a component with exceptional star (Temkin, App. B, T:4463–4467)

`φ : X → Y` is a proper morphism of curves over a field (the fibre map `h_s : Cb_s → Cs_s`), an
isomorphism over the complement `U` of a finite set `J` of closed points, whose fibres `G x`
(`x ∈ J`) are unions of components, connected in the incidence data `Γ` of `X` along a closed
subcurve `Z ⊇ φ⁻¹(J)`, semi-stable along `Z`. For a component `v` of `X` outside the fibres whose
star `S = {v} ∪ ⋃ {G x : G x meets v}` is an exceptional tree, the image component `w = φ v` of
`Y` has no double point of its own, and its marks and double points come from distinct marks and
boundary double points of `S`. -/

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)]
  [CompactSpace X] [IsReduced X]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] [Finite (genericPoints Y)]
  [CompactSpace Y] [IsReduced Y]
  (qX : X ⟶ Spec (.of k)) (qY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType qX]
  [LocallyOfFiniteType qY] (φ : X ⟶ Y) [IsProper φ]
  (hdim : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
  (hpureY : ∀ W ∈ irreducibleComponents Y, topologicalKrullDim W = 1)
  (J : Finset Y) (hJc : ∀ x ∈ (J : Set Y), IsClosed ({x} : Set Y)) (U : Y.Opens)
  (hU : ∀ y, y ∈ U ↔ y ∉ (J : Set Y)) [IsIso (φ ∣_ U)]
  (G : Y → Finset X) (hG : ∀ x ∈ J, (G x : Set X) = innerPoints φ x)
  (hA : ∀ x ∈ J, ∀ z, φ z = x → ∃ u ∈ G x, z ∈ closure ({u} : Set X))
  (Z : Set X) (hZc : IsClosed Z) (hZsub : φ ⁻¹' (J : Set Y) ⊆ Z)
  (hnodal : ∀ y ∈ Z, IsClosed ({y} : Set X) →
    DeJong.IsSmoothAt qX y ∨ Geometry.IsGeometricOrdinaryDoublePoint qX y)
  [Fintype (nodesIn qX Z)] {M : Type*} [Fintype M] (mk : M → X)
  {v : X} (hvg : v ∈ genericPoints X) (hvJ : ∀ x ∈ J, v ∉ G x)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)]
  [CompactSpace X] [IsReduced X] [IsAffineHom (pullback.diagonal (terminal.from Y))]
  [Finite (genericPoints Y)] [CompactSpace Y] [IsReduced Y] [IsProper φ] in
include hG in
theorem mem_genericPoints_and_apply_eq {x : Y} (hx : x ∈ J) {u : X} (hu : u ∈ G x) :
    u ∈ genericPoints X ∧ φ u = x := by
  have : u ∈ (G x : Set X) := hu
  rw [hG x hx] at this
  exact this

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)]
  [CompactSpace X] [IsReduced X] [IsAffineHom (pullback.diagonal (terminal.from Y))]
  [Finite (genericPoints Y)] [CompactSpace Y] [IsReduced Y] [IsProper φ] in
include hG hvg hvJ in
theorem apply_notMem_of_forall_notMem : φ v ∉ (J : Set Y) := fun hJv =>
  hvJ (φ v) hJv (by
    have : v ∈ (G (φ v) : Set X) := by
      rw [hG _ hJv]
      exact ⟨hvg, rfl⟩
    exact this)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)]
  [CompactSpace X] [IsReduced X] [IsAffineHom (pullback.diagonal (terminal.from Y))]
  [Finite (genericPoints Y)] [CompactSpace Y] [IsReduced Y] in
/-- The closure of an image point is the image of the closure (`φ` is closed). -/
theorem exists_mem_closure_of_mem_closure (a : X) {y : Y} (hy : y ∈ closure ({φ a} : Set Y)) :
    ∃ z ∈ closure ({a} : Set X), φ z = y := by
  have hc : IsClosed (φ '' closure ({a} : Set X)) := φ.isClosedMap _ isClosed_closure
  have ha : φ a ∈ φ '' closure ({a} : Set X) := ⟨a, subset_closure rfl, rfl⟩
  exact closure_minimal (Set.singleton_subset_iff.2 ha) hc hy

omit [Fintype (nodesIn qX Z)] [Fintype M] in
open scoped Classical in
include hnodal in
/-- A point of `Z` on two distinct components is a double point of `Γ` joining them. -/
theorem exists_mem_nodesIn_ends {z a b : X} (hz : z ∈ Z) (ha : a ∈ genericPoints X)
    (hb : b ∈ genericPoints X) (hab : a ≠ b) (hza : z ∈ closure {a}) (hzb : z ∈ closure {b}) :
    ∃ hz : z ∈ nodesIn qX Z, (withMarks (nodalGraph qX hdim Z) mk).ends ⟨z, hz⟩ = s(a, b) := by
  have hn := mem_nodesIn_of_mem_closure qX hdim hnodal hz ha hb hab hza hzb
  exact ⟨hn, nodalGraph_ends_eq qX hdim ⟨z, hn⟩ ha hb hab hza hzb⟩

omit [IsAffineHom (pullback.diagonal (terminal.from Y))] [Finite (genericPoints Y)]
  [CompactSpace Y] [IsReduced Y] in
open scoped Classical in
include hG hA hZsub hnodal hvg hvJ in
/-- **The fibres over points of the image component lie in the star.** -/
theorem subset_star_of_mem_closure {x : Y} (hx : x ∈ J) (hxw : x ∈ closure ({φ v} : Set Y)) :
    G x ⊆ (withMarks (nodalGraph qX hdim Z) mk).star (J.image G) v := by
  obtain ⟨z, hzv, hzx⟩ := exists_mem_closure_of_mem_closure φ v hxw
  obtain ⟨u, hu, hzu⟩ := hA x hx z hzx
  have hne : v ≠ u := fun h => hvJ x hx (h ▸ hu)
  obtain ⟨hn, hends⟩ := exists_mem_nodesIn_ends qX hdim Z hnodal mk
    (hZsub (show φ z ∈ (J : Set Y) by rw [hzx]; exact hx)) hvg
    (mem_genericPoints_and_apply_eq φ J G hG hx hu).1 hne hzv hzu
  exact subset_star (Finset.mem_image_of_mem G hx)
    (meets_of_ends hends (Finset.mem_singleton_self v) hu)

omit [IsAffineHom (pullback.diagonal (terminal.from Y))] [Finite (genericPoints Y)]
  [CompactSpace Y] [IsReduced Y] [IsProper φ] in
open scoped Classical in
include hG in
/-- The components of the star of `v` other than `v` lie over `J`. -/
theorem notMem_star {v₂ : X} (hv₂J : φ v₂ ∉ (J : Set Y)) (hne : v₂ ≠ v) :
    v₂ ∉ (withMarks (nodalGraph qX hdim Z) mk).star (J.image G) v := by
  intro hv₂S
  rcases mem_star.1 hv₂S with h | ⟨T, hT, -, hv₂T⟩
  · exact hne h
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hT
    exact hv₂J ((mem_genericPoints_and_apply_eq φ J G hG hx hv₂T).2 ▸ hx)

open scoped Classical in
include hdimY hpureY hU hG hA hZc hZsub hnodal hvg hvJ in
/-- **The image component has no double point of its own** (Temkin, App. B, T:4463–4467): off
`J` a double point of `w = φ v` with both branches on `w` would be one of `v`; at a point `x ∈ J`
the branches of `w` correspond to the double points joining `v` to the connected fibre `G x`, and
there is at most one, the star of `v` being a tree. -/
theorem inner_singleton_image_eq_empty
    (hconn : ∀ x ∈ J, (withMarks (nodalGraph qX hdim Z) mk).IsConnected (G x))
    (hexc : (withMarks (nodalGraph qX hdim Z) mk).IsTree
      ((withMarks (nodalGraph qX hdim Z) mk).star (J.image G) v))
    (hvZ : v ∈ Z) (ZY : Set Y) [Fintype (nodesIn qY ZY)] {M' : Type*} [Fintype M']
    (mk' : M' → Y) [IsIso (φ.residueFieldMap v)]
    [IsIntegralHom (normalizationPointsMap ({v} : Set X) ≫ φ)] :
    (withMarks (nodalGraph qY hdimY ZY) mk').inner {φ v} = ∅ := by
  set Γ := withMarks (nodalGraph qX hdim Z) mk with hΓ
  set S := Γ.star (J.image G) v with hS
  have hvS : v ∈ S := self_mem_star _ v
  have hvU := apply_notMem_of_forall_notMem φ J G hG hvg hvJ
  have hwg : φ v ∈ genericPoints Y :=
    (mem_genericPoints_iff_of_isIso_morphismRestrict φ U ((hU _).2 hvU)).1 hvg
  have : IsFinite (normalizationPointsMap ({v} : Set X)) :=
    isFinite_normalizationPointsMap (S := ({v} : Set X)) qX
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  obtain ⟨a, b, hab⟩ := exists_ends (G := withMarks (nodalGraph qY hdimY ZY) mk') e
  obtain ⟨ha, hb⟩ := (mem_inner_of_ends hab).1 he
  rw [Finset.mem_singleton] at ha hb
  rw [ha, hb] at hab
  have hmem : ∀ u, u ∈ (withMarks (nodalGraph qY hdimY ZY) mk').ends e ↔
      u ∈ genericPoints Y ∧ e.1 ∈ closure {u} := fun u => mem_nodalGraph_ends qY hdimY e u
  have hew : e.1 ∈ closure ({φ v} : Set Y) :=
    ((hmem (φ v)).1 (by rw [hab]; exact Sym2.mem_mk_left _ _)).2
  have hall : ∀ u ∈ branches e.1, u = φ v := by
    intro u hu
    have := (hmem u).2 ((mem_branches qY u e.1).1 hu)
    rw [hab] at this
    simpa using this
  have h2 : branchCount (φ v) e.1 = 2 := by
    rw [← count_branches hwg, Multiset.count_eq_card.2 fun u hu => (hall u hu).symm,
      card_branches_of_mem_nodesIn qY hdimY e.2]
  rw [branchCount_comp_eq φ v e.1] at h2
  by_cases heJ : e.1 ∈ (J : Set Y)
  · -- at a contracted point: at most one double point joins `v` to the fibre
    have hGS := subset_star_of_mem_closure qX φ hdim J G hG hA Z hZsub hnodal mk hvg hvJ heJ hew
    have key : ∀ γ ∈ normalizationPointsMap ({v} : Set X) ⁻¹' (φ ⁻¹' {e.1}), ∃ u ∈ G e.1,
        ∃ hz : normalizationPointsMap ({v} : Set X) γ ∈ nodesIn qX Z,
        Γ.ends ⟨_, hz⟩ = s(v, u) ∧ branchCount v (normalizationPointsMap ({v} : Set X) γ) ≤ 1 := by
      intro γ hγ
      have hzv : normalizationPointsMap ({v} : Set X) γ ∈ closure {v} :=
        range_normalizationPointsMap_subset ({v} : Set X) ⟨γ, rfl⟩
      have hzx : φ (normalizationPointsMap ({v} : Set X) γ) = e.1 := hγ
      obtain ⟨u, hu, hzu⟩ := hA e.1 heJ _ hzx
      have hug := (mem_genericPoints_and_apply_eq φ J G hG heJ hu).1
      have hne : v ≠ u := fun h => hvJ _ heJ (h ▸ hu)
      obtain ⟨hn, hends⟩ := exists_mem_nodesIn_ends qX hdim Z hnodal mk
        (hZsub (show φ _ ∈ (J : Set Y) by rw [hzx]; exact heJ)) hvg hug hne hzv hzu
      refine ⟨u, hu, hn, hends, ?_⟩
      rw [← count_branches hvg]
      exact count_le_one_of_card_eq_two (card_branches_of_mem_nodesIn qX hdim hn)
        ((mem_branches qX u _).2 ⟨hug, hzu⟩) hne.symm
    have hsub : (normalizationPointsMap ({v} : Set X) ⁻¹' (φ ⁻¹' {e.1})).Subsingleton := by
      intro α hα β hβ
      obtain ⟨uα, huα, hnα, hendsα, hcα⟩ := key α hα
      obtain ⟨uβ, huβ, hnβ, hendsβ, -⟩ := key β hβ
      have heq := eq_of_ends_of_isTree hexc hvS hGS (hvJ _ heJ) (hconn _ heJ) huα huβ
        hendsα hendsβ
      have hzeq : normalizationPointsMap ({v} : Set X) β = normalizationPointsMap ({v} : Set X) α :=
        (congrArg Subtype.val heq).symm
      have : Finite ↥(normalizationPointsMap ({v} : Set X) ⁻¹'
          {normalizationPointsMap ({v} : Set X) α}) :=
        ((normalizationPointsMap _).finite_preimage_singleton _).to_subtype
      have hsing := Finite.card_le_one_iff_subsingleton.1 hcα
      exact congrArg Subtype.val (hsing.elim ⟨α, rfl⟩ ⟨β, hzeq⟩)
    have : Subsingleton ↥(normalizationPointsMap ({v} : Set X) ⁻¹' (φ ⁻¹' {e.1})) :=
      hsub.coe_sort
    have : Finite ↥(normalizationPointsMap ({v} : Set X) ⁻¹' (φ ⁻¹' {e.1})) :=
      Finite.of_subsingleton
    have := Finite.card_le_one_iff_subsingleton.2 ‹Subsingleton _›
    omega
  · -- off the contracted points: a double point of `w` is one of `v`
    obtain ⟨eb, heb⟩ := exists_eq_of_isIso_morphismRestrict φ U ((hU _).2 heJ)
    have hpre : φ ⁻¹' {e.1} = {eb} := by
      ext z
      constructor
      · intro hz
        have hz' : φ z = e.1 := hz
        exact injOn_of_isIso_morphismRestrict φ U (by rw [hz']; exact (hU _).2 heJ)
          (by rw [heb]; exact (hU _).2 heJ) (hz'.trans heb.symm)
      · rintro rfl
        exact heb
    rw [hpre] at h2
    have hbv : branchCount v eb = 2 := h2
    have hebv : eb ∈ closure ({v} : Set X) :=
      (branchCount_ne_zero_iff qX v eb).1 (by omega)
    have hebne : eb ≠ v := by
      intro h
      apply not_mem_genericPoints_of_isClosed hpureY _ hwg
      rw [← h, heb]
      exact e.2.2.1
    have hebg : eb ∉ genericPoints X := fun hg =>
      hebne (eq_of_mem_closure_of_mem_genericPoints hg hebv).symm
    have hebc := isClosed_singleton_of_not_mem_genericPoints hdim hebg
    have hcount : (branches eb).count v = 2 := by
      rw [count_branches hvg]
      exact hbv
    have hebZ : eb ∈ Z := closure_subset_of_mem hZc hvZ hebv
    rcases hnodal eb hebZ hebc with hsmooth | hode
    · have : LocallyOfFinitePresentation qX := by
        have := isLocallyNoetherian_of_locallyOfFiniteType qX
        infer_instance
      have h1 := natCard_fiber_eq_one_of_isSmoothAt qX hdim eb hebc hebg hsmooth
      have := Multiset.count_le_card v (branches eb)
      rw [hcount, card_branches qX eb, h1] at this
      omega
    · have hn : eb ∈ nodesIn qX Z := ⟨hebZ, hebc, hebg, hode⟩
      have hallv : ∀ u ∈ branches eb, v = u :=
        Multiset.count_eq_card.1 (hcount.trans (card_branches_of_mem_nodesIn qX hdim hn).symm)
      obtain ⟨a', b', hab'⟩ := exists_ends (G := Γ) ⟨eb, hn⟩
      have hmemΓ : ∀ u, u ∈ Γ.ends ⟨eb, hn⟩ → u = v := fun u hu =>
        (hallv u ((mem_branches qX u eb).2 ((mem_nodalGraph_ends qX hdim ⟨eb, hn⟩ u).1 hu))).symm
      have ha' := hmemΓ a' (by rw [hab']; exact Sym2.mem_mk_left _ _)
      have hb' := hmemΓ b' (by rw [hab']; exact Sym2.mem_mk_right _ _)
      rw [ha', hb'] at hab'
      have hin : (⟨eb, hn⟩ : nodesIn qX Z) ∈ Γ.inner S := (mem_inner_of_ends hab').2 ⟨hvS, hvS⟩
      exact hexc.ne_of_mem_inner hin hab' rfl

open scoped Classical in
include hpureY hJc hU hG hA hZc hZsub hnodal hvg hvJ in
/-- **The double points of the image component come from boundary double points of the star**
(Temkin, App. B, T:4463–4467): a double point of `w = φ v` joining it to another component `w₂`
lifts to a double point of `X` joining the star of `v` to the component over `w₂`. -/
theorem card_boundary_image_le (hvZ : v ∈ Z) (ZY : Set Y) [Fintype (nodesIn qY ZY)]
    {M' : Type*} [Fintype M'] (mk' : M' → Y) :
    ((withMarks (nodalGraph qY hdimY ZY) mk').boundary {φ v}).card ≤
      ((withMarks (nodalGraph qX hdim Z) mk).boundary
        ((withMarks (nodalGraph qX hdim Z) mk).star (J.image G) v)).card := by
  set Γ := withMarks (nodalGraph qX hdim Z) mk with hΓ
  set Γs := withMarks (nodalGraph qY hdimY ZY) mk' with hΓs
  set S := Γ.star (J.image G) v with hS
  have hvS : v ∈ S := self_mem_star _ v
  have hvU := apply_notMem_of_forall_notMem φ J G hG hvg hvJ
  have hsub : (Γs.boundary {φ v}).map (Function.Embedding.subtype _) ⊆
      (Γ.boundary S).image (fun b => φ b.1) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.1 hy
    obtain ⟨a, b, hab⟩ := exists_ends (G := Γs) e
    have hmem : ∀ u, u ∈ Γs.ends e ↔ u ∈ genericPoints Y ∧ e.1 ∈ closure {u} := fun u =>
      mem_nodalGraph_ends qY hdimY e u
    obtain ⟨w₂, hw₂ne, hends⟩ : ∃ w₂, w₂ ≠ φ v ∧ Γs.ends e = s(φ v, w₂) := by
      rcases (mem_boundary_of_ends hab).1 he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [Finset.mem_singleton] at ha hb
        exact ⟨b, hb, ha ▸ hab⟩
      · rw [Finset.mem_singleton] at ha hb
        exact ⟨a, ha, hb ▸ hab.trans Sym2.eq_swap⟩
    have hew : e.1 ∈ closure ({φ v} : Set Y) :=
      ((hmem _).1 (by rw [hends]; exact Sym2.mem_mk_left _ _)).2
    obtain ⟨hw₂g, hew₂⟩ := (hmem w₂).1 (by rw [hends]; exact Sym2.mem_mk_right _ _)
    have hw₂J : w₂ ∉ (J : Set Y) := fun h =>
      not_mem_genericPoints_of_isClosed hpureY (hJc _ h) hw₂g
    obtain ⟨v₂, rfl⟩ := exists_eq_of_isIso_morphismRestrict φ U ((hU _).2 hw₂J)
    have hv₂g : v₂ ∈ genericPoints X :=
      (mem_genericPoints_iff_of_isIso_morphismRestrict φ U ((hU _).2 hw₂J)).2 hw₂g
    have hv₂ne : v₂ ≠ v := fun h => hw₂ne (h ▸ rfl)
    have hv₂S := notMem_star qX φ hdim J G hG Z mk hw₂J hv₂ne
    rw [Finset.mem_image]
    by_cases heJ : e.1 ∈ (J : Set Y)
    · obtain ⟨z₂, hz₂, hz₂x⟩ := exists_mem_closure_of_mem_closure φ v₂ hew₂
      obtain ⟨u, hu, hz₂u⟩ := hA _ heJ z₂ hz₂x
      have huS := subset_star_of_mem_closure qX φ hdim J G hG hA Z hZsub hnodal mk hvg hvJ heJ
        hew hu
      have hune : u ≠ v₂ := fun h => hv₂S (h ▸ huS)
      obtain ⟨hn, hends'⟩ := exists_mem_nodesIn_ends qX hdim Z hnodal mk
        (hZsub (show φ z₂ ∈ (J : Set Y) by rw [hz₂x]; exact heJ))
        (mem_genericPoints_and_apply_eq φ J G hG heJ hu).1 hv₂g hune hz₂u hz₂
      exact ⟨⟨z₂, hn⟩, (mem_boundary_of_ends hends').2 (Or.inl ⟨huS, hv₂S⟩), hz₂x⟩
    · obtain ⟨eb, heb⟩ := exists_eq_of_isIso_morphismRestrict φ U ((hU _).2 heJ)
      have hebU : φ eb ∈ U := by rw [heb]; exact (hU _).2 heJ
      have hebv : eb ∈ closure ({v} : Set X) :=
        specializes_iff_mem_closure.1 ((specializes_iff_of_isIso_morphismRestrict φ U
          ((hU _).2 hvU) hebU).1 (specializes_iff_mem_closure.2 (by rw [heb]; exact hew)))
      have hebv₂ : eb ∈ closure ({v₂} : Set X) :=
        specializes_iff_mem_closure.1 ((specializes_iff_of_isIso_morphismRestrict φ U
          ((hU _).2 hw₂J) hebU).1 (specializes_iff_mem_closure.2 (by rw [heb]; exact hew₂)))
      obtain ⟨hn, hends'⟩ := exists_mem_nodesIn_ends qX hdim Z hnodal mk
        (closure_subset_of_mem hZc hvZ hebv) hvg hv₂g hv₂ne.symm hebv hebv₂
      exact ⟨⟨eb, hn⟩, (mem_boundary_of_ends hends').2 (Or.inl ⟨hvS, hv₂S⟩), heb⟩
  calc (Γs.boundary {φ v}).card =
        ((Γs.boundary {φ v}).map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
    _ ≤ ((Γ.boundary S).image (fun b => φ b.1)).card := Finset.card_le_card hsub
    _ ≤ (Γ.boundary S).card := Finset.card_image_le

open scoped Classical in
include hU hG hA hZsub hnodal hvg hvJ in
/-- **The marks of the image component are marks of the star**: a mark `i` lies on `w = φ v`
exactly when its point lies over `w`, i.e. on `v` or on a fibre `G x` meeting `v` (the marked
points of `X` are smooth, hence on a single component). -/
theorem marks_image_subset (yi : M → X) (hyi : ∀ i, yi i ∈ closure {mk i})
    (hmkg : ∀ i, mk i ∈ genericPoints X)
    (hsm : ∀ i, DeJong.IsSmoothAt qX (yi i)) (ZY : Set Y) [Fintype (nodesIn qY ZY)]
    (mk' : M → Y) (hmk' : ∀ i, φ (yi i) ∈ closure {mk' i}) :
    (withMarks (nodalGraph qY hdimY ZY) mk').marks {φ v} ⊆
      (withMarks (nodalGraph qX hdim Z) mk).marks
        ((withMarks (nodalGraph qX hdim Z) mk).star (J.image G) v) := by
  have hvU := apply_notMem_of_forall_notMem φ J G hG hvg hvJ
  intro i hi
  rw [mem_marks, Finset.mem_singleton] at hi
  rw [mem_marks]
  change mk i ∈ _
  change mk' i = φ v at hi
  have hyw : φ (yi i) ∈ closure ({φ v} : Set Y) := hi ▸ hmk' i
  by_cases hyJ : φ (yi i) ∈ (J : Set Y)
  · obtain ⟨u, hu, hyu⟩ := hA _ hyJ (yi i) rfl
    rw [eq_of_mem_closure_of_isSmoothAt qX hdim (hsm i) (hmkg i)
      (mem_genericPoints_and_apply_eq φ J G hG hyJ hu).1 (hyi i) hyu]
    exact subset_star_of_mem_closure qX φ hdim J G hG hA Z hZsub hnodal mk hvg hvJ hyJ hyw hu
  · have hsp : v ⤳ yi i := (specializes_iff_of_isIso_morphismRestrict φ U ((hU _).2 hvU)
      ((hU _).2 hyJ)).1 (specializes_iff_mem_closure.2 hyw)
    rw [eq_of_mem_closure_of_isSmoothAt qX hdim (hsm i) (hmkg i) hvg (hyi i)
      (specializes_iff_mem_closure.1 hsp)]
    exact self_mem_star _ v

end StarImage

section ExceptionalComponent

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [CompactSpace X] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (hdim : topologicalKrullDim X ≤ 1)

open scoped Classical in
/-- **Exceptional components, read on the component itself**: a component `w` is exceptional in
the incidence data along a closed subcurve `Z` (with marks `mk`) iff it lies in `Z` and is a
`ℙ¹`-tree with at most two marks and boundary double points in the incidence data along its own
closure (the comparison with the closed-fibre form of lane T44B, `BlowDown.IsClosedExceptional`). -/
theorem isExceptional_withMarks_iff {Z : Set X} (hZ : IsClosed Z) [Fintype (nodesIn q Z)]
    {w : X} [Fintype (nodesIn q (closure {w}))] {M : Type*} [Fintype M] (mk : M → X) :
    (withMarks (nodalGraph q hdim Z) mk).IsExceptional w ↔
      w ∈ Z ∧ w ∈ genericPoints X ∧ (nodalGraph q hdim (closure {w})).IsP1Tree {w} ∧
        (Finset.univ.filter fun i => mk i = w).card +
          ((nodalGraph q hdim (closure {w})).boundary {w}).card ≤ 2 := by
  have hmarks : (withMarks (nodalGraph q hdim Z) mk).marks {w} =
      Finset.univ.filter fun i => mk i = w := by
    ext i
    simp [mem_marks]
  constructor
  · intro h
    have hel : w ∈ Z ∧ w ∈ genericPoints X := h.subset_eligible (Finset.mem_singleton_self w)
    have htr := isTransfer_nodalGraph q hdim (closure_subset_of_mem hZ hel.1) mk {w}
      (fun v hv => by rw [Finset.mem_singleton.1 hv])
    refine ⟨hel.1, hel.2, (isP1Tree_iff_of_transfer htr subset_rfl).1 h.isP1Tree, ?_⟩
    rw [← card_boundary_of_transfer htr subset_rfl, ← hmarks]
    exact h.card_marks_add_card_boundary_le
  · rintro ⟨hwZ, hwg, htree, hcard⟩
    have htr := isTransfer_nodalGraph q hdim (closure_subset_of_mem hZ hwZ) mk {w}
      (fun v hv => by rw [Finset.mem_singleton.1 hv])
    refine ⟨(isP1Tree_iff_of_transfer htr subset_rfl).2 htree, ?_, ?_⟩
    · intro v hv
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hv
      exact hv ▸ ⟨hwZ, hwg⟩
    · rw [card_boundary_of_transfer htr subset_rfl, hmarks]
      exact hcard

end ExceptionalComponent

section Stable

/-! ### The stable-family condition from the stability of `Cs` -/

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {C C' Cs Cb : Scheme.{u}} (p : C ⟶ Spec (CommRingCat.of V)) (f' : C' ⟶ C) (fs : Cs ⟶ C)
  (h' : Cb ⟶ C') (h : Cb ⟶ Cs) {ι : Type*} [Fintype ι] (s : Spec (CommRingCat.of V))

/-- The locus of `Cs_s` contracted to points of `C` (the fibre over the points of `C_s` in the
modification locus of `fs`). -/
abbrev stContractedLocus : Set ((fs ≫ p).fiber s) :=
  Curves.fiberMap fs p s ⁻¹' {x | p.fiberι s x ∈ center fs}

open scoped Classical in
/-- **Numerical stability of the fibre `Cs_s`** (Temkin, T:1687–1690, in the combinatorial form
of App. B, T:4459–4462): in the incidence data of `Cs_s` along the locus contracted to points of
`C`, marked by the sections `τ i`, no component is exceptional, i.e. no component `w` contracted
to a point of `C` has geometric genus `0`, no double point of its own and at most two marked or
double points (`CurvesField.IncidenceGraph.isExceptional_iff`). The marking `mk` of the marked
points by their components and the instances are universally quantified. -/
def FibreStable (τ : ι → (Spec (CommRingCat.of V) ⟶ Cs)) [IsProper (fs ≫ p)]
    [DeJong.IsNodalCurve (fs ≫ p)] : Prop :=
  ∀ (hdim : topologicalKrullDim ((fs ≫ p).fiber s) ≤ 1)
    [Fintype (nodesIn ((fs ≫ p).fiberToSpecResidueField s) (stContractedLocus p fs s))]
    (mk : ι → (fs ≫ p).fiber s),
    (∀ i, mk i ∈ genericPoints ((fs ≫ p).fiber s) ∧
      ∃ y, (fs ≫ p).fiberι s y = τ i s ∧ y ∈ closure {mk i}) →
    ∀ w, ¬ (withMarks (nodalGraph ((fs ≫ p).fiberToSpecResidueField s) hdim
      (stContractedLocus p fs s)) mk).IsExceptional w

variable (e : h ≫ fs ≫ p = h' ≫ f' ≫ p) (σ : ι → (Spec (CommRingCat.of V) ⟶ Cb))

open scoped Classical in
/-- **The stable-family condition from the stability of `Cs`** (Temkin, App. B, T:4463–4467;
blueprint `def:sm-stable-family`, `lem:sm-dom-star`): if no component of `Cs_s` contracted to a
point of `C` is exceptional, then for every component `v` of `Cb_s` outside the fibres of `h_s`
over the modification locus of `h`, the star of `v` is not an exceptional tree.

Indeed, if the star `S` of `v` is an exceptional tree, then `w = h_s(v)` is an exceptional
component of `Cs_s`: it is contracted to a point of `C` (as `v` is), it has the genus of `v`
(`componentGenus_comp_eq`), it has no double point of its own (a double point off the modification
locus would be one of `v`; at a contracted point `x` the branches of `w` correspond to the double
points joining `v` to the tree `h_s⁻¹(x)`, and there is at most one, `S` being a tree), and its
marks and double points come from distinct marks and boundary double points of `S`. -/
theorem fibresStable_of_fibreStable [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hcomm : h' ≫ f' = h ≫ fs)
    [IsIntegral C] [IsIntegral Cs] [IsIntegral Cb]
    [IsModification f'] [IsModification fs] [IsModification h'] [IsModification h]
    [IsProper p] [DeJong.IsNodalCurve (fs ≫ p)] [DeJong.IsNodalCurve (h' ≫ f' ≫ p)]
    (hps : IsProjectiveOver (fs ≫ p)) (hfps : DeJong.IsRelativelyProjective (fs ≫ p) h)
    (hnormal : IsNormalScheme C) (hnormals : IsNormalScheme Cs)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hηs : Curves.IsEtaModification h (fs ≫ p))
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)]
    (hg : ∀ v ∈ genericPoints ((h' ≫ f' ≫ p).fiber s), 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        ((h' ≫ f' ≫ p).fiberToSpecResidueField s)) v)
    (hss : ∀ x : (fs ≫ p).fiber s, (fs ≫ p).fiberι s x ∈ center h →
      (Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((fs ≫ p).fiberToSpecResidueField s) x))
    (hsm : ∀ i, ∀ y : (h' ≫ f' ≫ p).fiber s, (h' ≫ f' ≫ p).fiberι s y = σ i s →
      DeJong.IsSmoothAt ((h' ≫ f' ≫ p).fiberToSpecResidueField s) y)
    (hst : FibreStable p fs s (fun i => σ i ≫ h)) :
    FibresStable p f' fs h' h e σ s := by
  classical
  intro hdim _ mk hmk J hJ G hG v hvg hvJ hexc
  -- basic facts
  have : IsProper (fs ≫ p) := hps.isProper
  have : IsModification (h' ≫ f') := IsModification.comp h' f'
  have hpq : IsProjectiveOver (h' ≫ f' ≫ p) :=
    e ▸ DeJong.IsRelativelyProjective.isProjectiveOver hps hfps
  have hpqs := isProjectiveOver_fiberToSpecResidueField (h' ≫ f' ≫ p) s hpq
  have hpss := isProjectiveOver_fiberToSpecResidueField (fs ≫ p) s hps
  have hcurves : ValuationRing.fiberTrdeg (fs ≫ p) (genericPoint Cs) ≤ 1 :=
    ValCurves.fiberTrdeg_le_one p hcurve fs _
  have hpureb := pure_fiber_of_isNodalCurve (h' ≫ f' ≫ p) s
  have hpures := pure_fiber_of_isNodalCurve (fs ≫ p) s
  have hdims : topologicalKrullDim ((fs ≫ p).fiber s) ≤ 1 :=
    topologicalKrullDim_fiber_le_one_of_isNodalCurve s (fs ≫ p)
  set φ := fiberMapOfEq h (fs ≫ p) (h' ≫ f' ≫ p) e s with hφ
  set φb := fiberMapOfEq (h' ≫ f') p (h' ≫ f' ≫ p) (Category.assoc _ _ _) s with hφb
  have hφb' : ∀ z, Curves.fiberMap fs p s (φ z) = φb z := fun z => by
    rw [← Scheme.Hom.comp_apply, hφ, fiberMapOfEq_comp_fiberMap p f' fs h' h e s hcomm]
  have hnodalb : ∀ y : (h' ≫ f' ≫ p).fiber s, IsClosed {y} →
      DeJong.IsSmoothAt ((h' ≫ f' ≫ p).fiberToSpecResidueField s) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((h' ≫ f' ≫ p).fiberToSpecResidueField s) y :=
    fun y hy => nodes_fiber_of_isNodalCurve (h' ≫ f' ≫ p) s y hy
  -- the modification locus `J` of `h`
  have hJc : ∀ x ∈ (J : Set ((fs ≫ p).fiber s)), IsClosed ({x} : Set ((fs ≫ p).fiber s)) :=
    fun x hx => isClosed_singleton_of_mem_center (fs ≫ p) h s hnormals hcurves x ((hJ x).1 hx)
  have hJcl : IsClosed (J : Set ((fs ≫ p).fiber s)) := by
    rw [← Set.biUnion_of_singleton (J : Set ((fs ≫ p).fiber s))]
    exact isClosed_biUnion_finset fun x hx => hJc x hx
  let U : ((fs ≫ p).fiber s).Opens := ⟨(J : Set ((fs ≫ p).fiber s))ᶜ, hJcl.isOpen_compl⟩
  have hU : ∀ y, y ∈ U ↔ y ∉ (J : Set ((fs ≫ p).fiber s)) := fun y => Iff.rfl
  have hiso : IsIso (φ ∣_ U) :=
    isIso_fiberMapOfEq_restrict_of_center h (fs ≫ p) (h' ≫ f' ≫ p) e s J (fun y => (hJ y).symm)
      U hU
  have hGm : ∀ x ∈ J, ∀ u, u ∈ G x → u ∈ genericPoints _ ∧ φ u = x := fun x hx u hu => by
    have : u ∈ (G x : Set ((h' ≫ f' ≫ p).fiber s)) := hu
    rw [hG x hx] at this
    exact this
  -- `v` and its image `w`
  have hvU : φ v ∉ (J : Set ((fs ≫ p).fiber s)) := apply_notMem_of_forall_notMem φ J G hG hvg hvJ
  have hwg : φ v ∈ genericPoints ((fs ≫ p).fiber s) :=
    (mem_genericPoints_iff_of_isIso_morphismRestrict φ U hvU).1 hvg
  -- the stability criterion for `h`
  let _ : Fintype (nodesIn ((h' ≫ f' ≫ p).fiberToSpecResidueField s)
    (φ ⁻¹' (J : Set ((fs ≫ p).fiber s)))) := (finite_nodesIn _ hdim hpqs _).fintype
  let m : (fs ≫ p).fiber s → ℕ := fun x =>
    (Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card
  obtain ⟨hA, hB, -⟩ := stability_criterion_fibre_of_eq (fs ≫ p) h (h' ≫ f' ≫ p) e s hsep hps hfps
    hnormals hcurves hηs hpures J hJ G hG hdim (fun x hx u hu => hg u (hGm x hx u hu).1) m
  have hexcB := hB fun x hx => ⟨nodes_fiber_of_isNodalCurve (fs ≫ p) s x (hJc x hx),
    (hss x ((hJ x).1 hx)).1, (hss x ((hJ x).1 hx)).2⟩
  -- the fibres of `h` lie in the contracted locus
  have hZc : IsClosed (contractedLocus p f' h' s) :=
    ((center (h' ≫ f')).isClosed.preimage (p.fiberι s).continuous).preimage φb.continuous
  have hZv : ∀ x ∈ J, ∀ u ∈ G x, u ∈ contractedLocus p f' h' s := by
    intro x hx u hu
    obtain ⟨hug, hux⟩ := hGm x hx u hu
    refine mem_center_of_forall_closure (h' ≫ f') p (h' ≫ f' ≫ p) (Category.assoc _ _ _) s hpureb
      hug fun z hz => ?_
    rw [← hφb', ← hφb', eq_of_mem_closure_of_isClosed φ (hux ▸ hJc x hx) hz]
  have hZsub : φ ⁻¹' (J : Set ((fs ≫ p).fiber s)) ⊆ contractedLocus p f' h' s := by
    intro z hz
    obtain ⟨u, hu, hzu⟩ := (hA (φ z) hz).2 z rfl
    exact closure_subset_of_mem hZc (hZv _ hz u hu) hzu
  -- the incidence data `Γ` of `Cb_s` and the star `S` of `v`
  set Γ := withMarks (nodalGraph ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim
    (contractedLocus p f' h' s)) mk with hΓ
  have hvZ : v ∈ contractedLocus p f' h' s := (hexc.subset_eligible (self_mem_star _ v)).1
  -- the fibres of `h` are connected in `Γ`
  have hJpre : IsClosed (φ ⁻¹' (J : Set ((fs ≫ p).fiber s))) := hJcl.preimage φ.continuous
  have hGconn : ∀ x ∈ J, Γ.IsConnected (G x) := by
    intro x hx
    have htr := isTransfer_nodalGraph ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim hZsub mk
      (G x) fun u hu => closure_subset_of_mem hJpre
        (show φ u ∈ (J : Set ((fs ≫ p).fiber s)) by rw [(hGm x hx u hu).2]; exact hx)
    exact (isConnected_iff_of_transfer htr subset_rfl).2 (hexcB x hx).1.isTree.isConnected
  have hA' : ∀ x ∈ J, ∀ z, φ z = x → ∃ u ∈ G x, z ∈ closure ({u} : Set _) :=
    fun x hx z hz => (hA x hx).2 z hz
  have hnodalZ : ∀ y ∈ contractedLocus p f' h' s, IsClosed ({y} : Set _) →
      DeJong.IsSmoothAt ((h' ≫ f' ≫ p).fiberToSpecResidueField s) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint ((h' ≫ f' ≫ p).fiberToSpecResidueField s) y :=
    fun y _ hy => hnodalb y hy
  -- the marks
  choose yi hyi hyc using fun i => (hmk i).2
  choose mk' hmk'g hmk'c using fun i => exists_mem_genericPoints_mem_closure (φ (yi i))
  have hmk' : ∀ i, mk' i ∈ genericPoints ((fs ≫ p).fiber s) ∧
      ∃ y, (fs ≫ p).fiberι s y = (σ i ≫ h) s ∧ y ∈ closure {mk' i} := fun i =>
    ⟨hmk'g i, φ (yi i), by rw [hφ, fiberι_fiberMapOfEq_apply, hyi i]; rfl, hmk'c i⟩
  -- the incidence data of `Cs_s`: `w = φ v` would be an exceptional component
  let _ : Fintype (nodesIn ((fs ≫ p).fiberToSpecResidueField s) (stContractedLocus p fs s)) :=
    (finite_nodesIn _ hdims hpss _).fintype
  refine hst hdims mk' hmk' (φ v) ?_
  rw [isExceptional_iff]
  have : IsIso (φ.residueFieldMap v) := isIso_residueFieldMap_of_isIso_morphismRestrict φ U v hvU
  have : IsFinite (normalizationPointsMap ({v} : Set ((h' ≫ f' ≫ p).fiber s)) ≫ φ) :=
    isFinite_normalizationPointsMap_comp φ J U hU ((h' ≫ f' ≫ p).fiberToSpecResidueField s) hdim
      hJcl hvg hvU
  refine ⟨⟨?_, hwg⟩, ?_, ?_, ?_⟩
  · -- `w` is contracted to a point of `C`
    have hφbv : IsClosed ({φb v} : Set (p.fiber s)) :=
      isClosed_singleton_of_mem_center p (h' ≫ f') s hnormal hcurve _ hvZ
    refine mem_center_of_forall_closure fs p (fs ≫ p) rfl s hpures hwg fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := exists_mem_closure_of_mem_closure φ v hy
    change Curves.fiberMap fs p s (φ z) = Curves.fiberMap fs p s (φ v)
    rw [hφb', hφb', eq_of_mem_closure_of_isClosed φb hφbv hz]
  · -- `w` has the genus of `v`
    have hgv : Γ.genus v = 0 := hexc.isP1Tree.genus_eq_zero (self_mem_star _ v)
    change (componentGenus (structureCoeff ((fs ≫ p).fiberToSpecResidueField s)) (φ v)).toNat = 0
    rw [← componentGenus_comp_eq φ ((fs ≫ p).fiberToSpecResidueField s) v, hφ,
      fiberMapOfEq_fiberToSpecResidueField]
    exact hgv
  · -- `w` has no double point of its own
    exact inner_singleton_image_eq_empty ((h' ≫ f' ≫ p).fiberToSpecResidueField s)
      ((fs ≫ p).fiberToSpecResidueField s) φ hdim hdims hpures J U hU G hG hA'
      (contractedLocus p f' h' s) hZc hZsub hnodalZ mk hvg hvJ hGconn hexc.isTree hvZ
      (stContractedLocus p fs s) mk'
  · -- the marks and double points of `w` come from marks and boundary points of the star
    refine le_trans (Nat.add_le_add (Finset.card_le_card ?_) ?_)
      hexc.card_marks_add_card_boundary_le
    · exact marks_image_subset ((h' ≫ f' ≫ p).fiberToSpecResidueField s)
        ((fs ≫ p).fiberToSpecResidueField s) φ hdim hdims J U hU G hG hA'
        (contractedLocus p f' h' s) hZsub hnodalZ mk hvg hvJ yi hyc (fun i => (hmk i).1)
        (fun i => hsm i (yi i) (hyi i)) (stContractedLocus p fs s) mk' hmk'c
    · exact card_boundary_image_le ((h' ≫ f' ≫ p).fiberToSpecResidueField s)
        ((fs ≫ p).fiberToSpecResidueField s) φ hdim hdims hpures J hJc U hU G hG hA'
        (contractedLocus p f' h' s) hZc hZsub hnodalZ mk hvg hvJ hvZ (stContractedLocus p fs s)
        mk'

end Stable

section MarksPointwise

/-! ### The semi-stability of the marks, pointwise

The numerical marks hypotheses follow from the pointwise properties of the marks of a
semi-stable pair (blueprint `lem:sm-bdc-marks`): the sections are pairwise disjoint (the marks are
étale over `V`) and pass through smooth points. -/

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of V))
  [LocallyOfFinitePresentation g] {ι : Type*} [Fintype ι] (s : Spec (CommRingCat.of V))

/-- A point of a section through a smooth point is a smooth point of its fibre. -/
theorem isSmoothAt_fiber_of_isSmoothAt {y : g.fiber s} (hy : DeJong.IsSmoothAt g (g.fiberι s y)) :
    DeJong.IsSmoothAt (g.fiberToSpecResidueField s) y :=
  DeJong.isSmoothAt_pullback_snd g _ y hy

open scoped Classical in
/-- **Pairwise disjoint marks through smooth points are semi-stable**: at most one passes
through any point of the fibre, and only at a smooth point. -/
theorem marks_semistable_of_injective (τ : ι → X) (hinj : ∀ i j, τ i = τ j → i = j)
    (hsm : ∀ i, DeJong.IsSmoothAt g (τ i)) (x : g.fiber s) :
    (Finset.univ.filter fun i => τ i = g.fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => τ i = g.fiberι s x).card = 1 →
        DeJong.IsSmoothAt (g.fiberToSpecResidueField s) x) := by
  refine ⟨Finset.card_le_one.2 fun i hi j hj => ?_, fun h1 => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hinj i j (hi.trans hj.symm)
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
    have : i ∈ Finset.univ.filter fun i => τ i = g.fiberι s x := by
      rw [hi]
      exact Finset.mem_singleton_self i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact isSmoothAt_fiber_of_isSmoothAt g s (this ▸ hsm i)

end MarksPointwise

section Main

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {C C' Cs Cb : Scheme.{u}} (p : C ⟶ Spec (CommRingCat.of V)) (f' : C' ⟶ C) (fs : Cs ⟶ C)
  (h' : Cb ⟶ C') (h : Cb ⟶ Cs) {ι : Type*} [Fintype ι]
  (σ : ι → (Spec (CommRingCat.of V) ⟶ Cb))

open scoped Classical in
/-- **Temkin, Corollary 4.4.3 (1)** (`sepcloscor`, T:3135–3149; blueprint
`cor:sm-domination-stable` (1), `thm:sm-dom-main`), for curves projective over a valuation ring
`V` with finitely many primes and algebraically closed residue fields. Let `C` be an integral
normal relative curve, projective over `V` with fibres of pure dimension one, and let
`fs : Cs → C` (the stable modification) and `f' : C' → C` (a semi-stable modification) be
modifications by normal nodal curves projective over `V`, both dominated by a nodal
modification `Cb` (`h ≫ fs = h' ≫ f'`) through η-modifications `h`, `h'` projective relative to
the targets. The marks of `Cb` are sections `σ i` through smooth points of the fibres, those of
`C'` and `Cs` their images. Assume that `(C', h'(σ))` and `(Cs, h(σ))` are semi-stable at the
points of the modification loci of `h'`, `h` (numerical form: at most one mark, at a smooth
point), that `(Cs, h(σ))` is stable (`FibreStable`: no fibre has an exceptional component
contracted to a point of `C`), and that the components of the fibres of `Cb` have nonnegative
genus. Then `C'` dominates `Cs`: there is `g : C' → Cs` with `g ≫ fs = f'`. -/
theorem dominates_of_fibreStable [Finite (PrimeSpectrum V)]
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
    (hsm : ∀ s i, ∀ y : (h' ≫ f' ≫ p).fiber s, (h' ≫ f' ≫ p).fiberι s y = σ i s →
      DeJong.IsSmoothAt ((h' ≫ f' ≫ p).fiberToSpecResidueField s) y)
    (hss' : ∀ s, ∀ x : (f' ≫ p).fiber s, (f' ≫ p).fiberι s x ∈ center h' →
      (Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h' (σ i s) = (f' ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((f' ≫ p).fiberToSpecResidueField s) x))
    (hss : ∀ s, ∀ x : (fs ≫ p).fiber s, (fs ≫ p).fiberι s x ∈ center h →
      (Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h (σ i s) = (fs ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((fs ≫ p).fiberToSpecResidueField s) x))
    (hst : ∀ s, FibreStable p fs s (fun i => σ i ≫ h)) :
    ValCurves.Dominates f' fs := by
  refine dominates_of_fibresStable p f' fs h' h σ hsep hac hcomm hσ hp' hps hfp' hfps hnormal
    hnormal' hnormals hcurve hη' hηs hpure hg hss' hss fun s => ?_
  have := hac s
  exact fibresStable_of_fibreStable p f' fs h' h s (comp_eq_of_comm p f' fs h' h hcomm) σ hsep
    hcomm hps hfps hnormal hnormals hcurve hηs (hg s) (hss s) (hsm s) (hst s)

open scoped Classical in
/-- **Temkin, Corollary 4.4.3 (1), with pointwise marks** (`dominates_of_fibreStable`): the marks
of `C̄` are sections through smooth points of `C̄ → Spec V`, their images in `C'` and in `Cs` are
pairwise disjoint over every point of `Spec V` and pass through smooth points (as for the
transported marks of semi-stable pairs). -/
theorem dominates_of_fibreStable_of_marks [Finite (PrimeSpectrum V)]
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
    (hσsm : ∀ s i, DeJong.IsSmoothAt (h' ≫ f' ≫ p) (σ i s))
    (hinj' : ∀ s i j, h' (σ i s) = h' (σ j s) → i = j)
    (hsm' : ∀ s i, DeJong.IsSmoothAt (f' ≫ p) (h' (σ i s)))
    (hinjs : ∀ s i j, h (σ i s) = h (σ j s) → i = j)
    (hsms : ∀ s i, DeJong.IsSmoothAt (fs ≫ p) (h (σ i s)))
    (hst : ∀ s, FibreStable p fs s (fun i => σ i ≫ h)) :
    ValCurves.Dominates f' fs :=
  dominates_of_fibreStable p f' fs h' h σ hsep hac hcomm hσ hp' hps hfp' hfps hnormal hnormal'
    hnormals hcurve hη' hηs hpure hg
    (fun s i _ hy => isSmoothAt_fiber_of_isSmoothAt (h' ≫ f' ≫ p) s (hy ▸ hσsm s i))
    (fun s x _ => marks_semistable_of_injective (f' ≫ p) s (fun i => h' (σ i s)) (hinj' s)
      (hsm' s) x)
    (fun s x _ => marks_semistable_of_injective (fs ≫ p) s (fun i => h (σ i s)) (hinjs s)
      (hsms s) x) hst

open scoped Classical in
/-- **Uniqueness of the stable modification** (Temkin, Theorem 1.2 over a valuation ring, via
Corollary 4.4.3 (1) applied twice; `PLAN-T5.md` node V3): two stable modifications `f₁ : C₁ → C`,
`f₂ : C₂ → C` dominated by a common nodal modification `Cb` (structure morphism `q`) are
isomorphic over `C`. Each is semi-stable at the points of the modification locus of its
domination and stable in the combinatorial form `FibreStable`; the remaining hypotheses are
those of `dominates_of_fibreStable`. -/
theorem nonempty_iso_of_fibreStable [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hac : ∀ s : Spec (CommRingCat.of V), IsAlgClosed ((Spec (CommRingCat.of V)).residueField s))
    {C₁ C₂ : Scheme.{u}} (f₁ : C₁ ⟶ C) (f₂ : C₂ ⟶ C) (h₁ : Cb ⟶ C₁) (h₂ : Cb ⟶ C₂)
    (q : Cb ⟶ Spec (CommRingCat.of V)) (hcomm : h₁ ≫ f₁ = h₂ ≫ f₂) (hq : h₁ ≫ f₁ ≫ p = q)
    (hσ : ∀ i, σ i ≫ q = 𝟙 _)
    [IsIntegral C] [IsIntegral C₁] [IsIntegral C₂] [IsIntegral Cb]
    [IsModification f₁] [IsModification f₂] [IsModification h₁] [IsModification h₂]
    [IsProper p] [DeJong.IsNodalCurve (f₁ ≫ p)] [DeJong.IsNodalCurve (f₂ ≫ p)] [IsProper q]
    [DeJong.IsNodalCurve q]
    (hp₁ : IsProjectiveOver (f₁ ≫ p)) (hp₂ : IsProjectiveOver (f₂ ≫ p))
    (hfp₁ : DeJong.IsRelativelyProjective (f₁ ≫ p) h₁)
    (hfp₂ : DeJong.IsRelativelyProjective (f₂ ≫ p) h₂)
    (hnormal : IsNormalScheme C) (hnormal₁ : IsNormalScheme C₁) (hnormal₂ : IsNormalScheme C₂)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη₁ : Curves.IsEtaModification h₁ (f₁ ≫ p)) (hη₂ : Curves.IsEtaModification h₂ (f₂ ≫ p))
    (hpure : ∀ s, ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (hg : ∀ s, ∀ v ∈ genericPoints (q.fiber s), 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
        (q.fiberToSpecResidueField s)) v)
    (hsm : ∀ s i, ∀ y : q.fiber s, q.fiberι s y = σ i s →
      DeJong.IsSmoothAt (q.fiberToSpecResidueField s) y)
    (hss₁ : ∀ s, ∀ x : (f₁ ≫ p).fiber s, (f₁ ≫ p).fiberι s x ∈ center h₁ →
      (Finset.univ.filter fun i => h₁ (σ i s) = (f₁ ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h₁ (σ i s) = (f₁ ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((f₁ ≫ p).fiberToSpecResidueField s) x))
    (hss₂ : ∀ s, ∀ x : (f₂ ≫ p).fiber s, (f₂ ≫ p).fiberι s x ∈ center h₂ →
      (Finset.univ.filter fun i => h₂ (σ i s) = (f₂ ≫ p).fiberι s x).card ≤ 1 ∧
      ((Finset.univ.filter fun i => h₂ (σ i s) = (f₂ ≫ p).fiberι s x).card = 1 →
        DeJong.IsSmoothAt ((f₂ ≫ p).fiberToSpecResidueField s) x))
    (hst₁ : ∀ s, FibreStable p f₁ s (fun i => σ i ≫ h₁))
    (hst₂ : ∀ s, FibreStable p f₂ s (fun i => σ i ≫ h₂)) :
    ∃ e : C₁ ≅ C₂, e.hom ≫ f₂ = f₁ := by
  have d₁ : ValCurves.Dominates f₁ f₂ := by
    subst hq
    exact dominates_of_fibreStable p f₁ f₂ h₁ h₂ σ hsep hac hcomm hσ hp₁ hp₂ hfp₁ hfp₂ hnormal
      hnormal₁ hnormal₂ hcurve hη₁ hη₂ hpure hg hsm hss₁ hss₂ hst₂
  have d₂ : ValCurves.Dominates f₂ f₁ := by
    have hq₂ : h₂ ≫ f₂ ≫ p = q := by
      rw [← hq, ← Category.assoc, ← hcomm, Category.assoc]
    subst hq₂
    exact dominates_of_fibreStable p f₂ f₁ h₂ h₁ σ hsep hac hcomm.symm hσ hp₂ hp₁ hfp₂ hfp₁
      hnormal hnormal₂ hnormal₁ hcurve hη₂ hη₁ hpure hg hsm hss₂ hss₁ hst₁
  obtain ⟨g₁, hg₁⟩ := d₁
  obtain ⟨g₂, hg₂⟩ := d₂
  refine ⟨⟨g₁, g₂, ?_, ?_⟩, hg₁⟩
  · exact ValCurves.Dominates.unique f₁ f₁ (by rw [Category.assoc, hg₂, hg₁])
      (Category.id_comp f₁)
  · exact ValCurves.Dominates.unique f₂ f₂ (by rw [Category.assoc, hg₁, hg₂])
      (Category.id_comp f₂)

end Main

end

end DeJongAlterations.StableModification.BlowDown.Domination
