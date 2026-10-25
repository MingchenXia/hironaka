/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.StabilityCount
import DeJongAlterations.StableModification.BlowDown.Criterion

/-!
# Corollary B.2 for all contracted points of a fibre, scheme level (Temkin, Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (`stabcritlem`, T:3125–3133) with Corollary B.2 (`stabdowncor`, T:4435–4467). Let `k`
be algebraically closed and `f : C′ → C` a proper morphism of reduced projective curves over `k`
with `p_a(C′) = p_a(C)`, which is an isomorphism off the fibres `Z_x = f⁻¹(x)` over a finite set
`X` of closed points `x` of `C` (in Lemma 4.4.2: the fibre map `f_s` and the points of the
modification locus in `C_s`). Assume every `Z_x` is a connected curve in the semi-stable locus of
`C′`. Then (blueprint `lem:sm-bdc-stabdown-fibre-scheme`, chapter `sm-blow-down-criterion.tex`):

* `|x̃| = |∂Z_x|` for every `x ∈ X` (`x̃` the points of the normalization of `C` over `x`, `∂Z_x`
  the boundary double points of `Z_x` in the incidence graph of `C′` along `f⁻¹X`), and every
  `Z_x` is connected in the incidence graph;
* **all `x ∈ X` are ordinary points (`δ(x) = |x̃| − 1`) if and only if all `Z_x` are
  `ℙ¹`-trees** (`stabdown_finset`): the δ-count of `StabilityCount` gives
  `∑_x δ(x) = ∑_x δ♭(Z_x)`, and T44A's `stabdown_numerical_finset` compares the non-negative
  defects.

With the marks this gives the fibre form of the stability criterion
(`stabdown_finset_semistable`, `stabdown_finset_exceptional`): if every `x ∈ X` is a smooth point
or an ordinary double point of `C`, with at most one mark through it and a mark only at a smooth
point, then every `Z_x` is a `ℙ¹`-tree with `|∂Z_x| + m_x ≤ 2`; conversely, if every `Z_x` is such
a tree, every `x ∈ X` is an ordinary `|x̃|`-fold point with `|x̃| ≤ 2`, `m_x ≤ 1` and `|x̃| = 1`
if `m_x = 1`. That such a point is smooth (`|x̃| = 1`) or an ordinary double point (`|x̃| = 2`)
in the completed-local sense is the converse of blueprint `lem:sm-ordinary-completion`, which is
not formalized; it is the named hypothesis `OrdinaryPointCompletion k`
(`stabdown_finset_semistable_of_ordinaryPointCompletion`).
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus

set_option autoImplicit false

universe u

noncomputable section

section Subcurve

/-! ### A union of fibres inside the subcurve `Z`

`Z` is closed, `G` the finset of generic points of `X` in `Z`, `O` the other generic points;
`Y ⊆ Z` is closed with components `GY`, and a component in `G` through a point of `Y` lies in `GY`
(for `Z = f⁻¹(X)`, `Y = f⁻¹(x)`: components of different fibres do not meet). -/

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [CompactSpace X] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (hdim : topologicalKrullDim X ≤ 1)
  {Z : Set X} {G : Finset X} (hG : (G : Set X) = genericPoints X ∩ Z)
  {O : Set X} [Finite O] (hO : O = genericPoints X \ Z)
  (hcurve : ∀ z ∈ Z, ∃ v ∈ G, z ∈ closure {v})
  (hnodal : ∀ y ∈ Z, IsClosed {y} →
    DeJong.IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y)
  {Y : Set X} {GY : Finset X} (hGY : (GY : Set X) = genericPoints X ∩ Y) (hYc : IsClosed Y)
  (hYZ : Y ⊆ Z) (hsep : ∀ v ∈ G, ∀ z ∈ Y, z ∈ closure {v} → v ∈ GY)

open scoped Classical in
include hG hO hcurve hGY hYc hYZ hsep in
/-- **Boundary double points of a union of fibres**: a double point `e ∈ Z` is a boundary point of
`GY` iff it lies on `Y` and the normalization `X̃_O → X` of the components not in `Z` has a point
over it. -/
lemma mem_boundary_nodalGraph_iff_of_subset [Fintype (nodesIn q Z)] (e : nodesIn q Z) :
    e ∈ (nodalGraph q hdim Z).boundary GY ↔
      e.1 ∈ Y ∧ (normalizationPointsMap O ⁻¹' {e.1}).Nonempty := by
  rw [mem_boundary, nonempty_fiber_iff q O e.1]
  constructor
  · rintro ⟨⟨v, hv, hvGY⟩, w, hw, hwGY⟩
    obtain ⟨-, hev⟩ := (mem_nodalGraph_ends q hdim e v).1 hv
    obtain ⟨hwg, hew⟩ := (mem_nodalGraph_ends q hdim e w).1 hw
    have hvY : v ∈ Y := by
      have : v ∈ (GY : Set X) := hvGY
      rw [hGY] at this
      exact this.2
    have heY : e.1 ∈ Y := closure_minimal (Set.singleton_subset_iff.2 hvY) hYc hev
    refine ⟨heY, w, ?_, hew⟩
    rw [hO]
    refine ⟨hwg, fun hwZ => hwGY ?_⟩
    have hwG : w ∈ G := by
      have : w ∈ (G : Set X) := by rw [hG]; exact ⟨hwg, hwZ⟩
      exact this
    exact hsep w hwG e.1 heY hew
  · rintro ⟨heY, w, hwO, hew⟩
    obtain ⟨v, hvG, hev⟩ := hcurve e.1 (hYZ heY)
    have hvg : v ∈ genericPoints X := by
      have : v ∈ (G : Set X) := hvG
      rw [hG] at this
      exact this.1
    have hwg : w ∈ genericPoints X := by rw [hO] at hwO; exact hwO.1
    refine ⟨⟨v, (mem_nodalGraph_ends q hdim e v).2 ⟨hvg, hev⟩, hsep v hvG e.1 heY hev⟩,
      w, (mem_nodalGraph_ends q hdim e w).2 ⟨hwg, hew⟩, fun hwGY => ?_⟩
    have : w ∈ (GY : Set X) := hwGY
    rw [hGY] at this
    rw [hO] at hwO
    exact hwO.2 (hYZ this.2)

open scoped Classical in
include hdim hG hO hcurve hnodal hGY hYc hYZ hsep in
/-- **The branch count of a union of fibres** (Temkin, Cor. B.2, l. 4446–4447, for one of several
contracted points): the points of the normalization `X̃_O → X` of the components not in `Z`
lying over `Y` correspond to the boundary double points of `GY`. -/
lemma natCard_preimage_eq_card_boundary_of_subset [Fintype (nodesIn q Z)] :
    Nat.card ↥(normalizationPointsMap O ⁻¹' Y) = ((nodalGraph q hdim Z).boundary GY).card := by
  let φ : ↥(normalizationPointsMap O ⁻¹' Y) → ↥((nodalGraph q hdim Z).boundary GY) := fun w =>
    ⟨⟨normalizationPointsMap O w.1, (outer_fiber q hdim hG hO hcurve hnodal (hYZ w.2)
        ⟨w.1, rfl⟩).1⟩,
      (mem_boundary_nodalGraph_iff_of_subset q hdim hG hO hcurve hGY hYc hYZ hsep _).2
        ⟨w.2, w.1, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun w₁ w₂ h => ?_, fun e => ?_⟩
    · have h' : normalizationPointsMap O w₁.1 = normalizationPointsMap O w₂.1 :=
        congrArg (fun e : ↥((nodalGraph q hdim Z).boundary GY) => e.1.1) h
      have h1 := (outer_fiber q hdim hG hO hcurve hnodal (hYZ w₁.2) ⟨w₁.1, rfl⟩).2
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h1
      have : (⟨w₁.1, rfl⟩ : ↥(normalizationPointsMap O ⁻¹' {normalizationPointsMap O w₁.1})) =
          ⟨w₂.1, h'.symm⟩ := Subsingleton.elim _ _
      have h'' := congrArg Subtype.val this
      exact Subtype.ext h''
    · obtain ⟨heY, w, hw⟩ :=
        (mem_boundary_nodalGraph_iff_of_subset q hdim hG hO hcurve hGY hYc hYZ hsep e.1).1 e.2
      have hwY : w ∈ normalizationPointsMap O ⁻¹' Y := by
        change normalizationPointsMap O w ∈ Y
        rw [show normalizationPointsMap O w = e.1.1 from hw]
        exact heY
      exact ⟨⟨w, hwY⟩, Subtype.ext (Subtype.ext hw)⟩
  rw [Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_coe]

end Subcurve

section Ordinary

variable {C : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from C))]
  [Finite (genericPoints C)] [IsReduced C] {k : Type u} [Field k] (p : C ⟶ Spec (.of k))
  [LocallyOfFiniteType p]

/-- **Temkin's inequality `|x̃| ≤ g(x) + 1`** at a closed point of a reduced curve over an
algebraically closed field (App. B, l. 4388–4391), in terms of the normalization
`π : C̃ → C`: `|π⁻¹(x)| ≤ δ(x) + 1`. -/
theorem natCard_fiber_le_deltaInvariant_add_one [IsAlgClosed k]
    (hdim : topologicalKrullDim C ≤ 1) (x : C) (hx : IsClosed {x}) :
    Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) ≤
      deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x + 1 := by
  have : IsFinite (normalizationPointsMap (genericPoints C)) :=
    isFinite_normalizationPointsMap (S := genericPoints C) p
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let _ := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
    (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
      normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints C)) p x hx V hV hxV
      (normalizationPoints_app_injective rfl V hV)
      (normalizationPoints_isFiniteCoker p rfl hdim V hV)
  rw [hdelta, ← hcard]
  exact card_le_delta_add_one_of_isLocalRing _ hres

omit [IsReduced C] in
include p in
/-- Every point of `C` lies on a component, so the normalization has a point over it. -/
theorem natCard_fiber_pos (x : C) :
    0 < Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) := by
  have : IsFinite (normalizationPointsMap (genericPoints C)) :=
    isFinite_normalizationPointsMap (S := genericPoints C) p
  have hfin : Finite ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) :=
    ((normalizationPointsMap (genericPoints C)).finite_preimage_singleton x).to_subtype
  let c : irreducibleComponents C :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hv := genericPoints.isGenericPoint_ofComponent c
  have hne : (normalizationPointsMap (genericPoints C) ⁻¹' {x}).Nonempty := by
    refine (nonempty_fiber_iff p (genericPoints C) x).2
      ⟨(genericPoints.ofComponent c).1, (genericPoints.ofComponent c).2, ?_⟩
    rw [hv.def]
    exact mem_irreducibleComponent
  exact Nat.card_pos_iff.2 ⟨hne.to_subtype, hfin⟩

end Ordinary

section Fibre

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (X : Set C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ∉ X)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

omit [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))]
  [Finite (genericPoints C')] in
/-- A component through a point of `f⁻¹(x)` with `f v` closed maps to `x`. -/
lemma eq_of_mem_closure_of_isClosed {v z : C'} (hv : IsClosed {f v}) (hz : z ∈ closure {v}) :
    f z = f v := by
  have : z ∈ f ⁻¹' {f v} :=
    closure_minimal (Set.singleton_subset_iff.2 (show v ∈ f ⁻¹' {f v} from rfl))
      (hv.preimage f.continuous) hz
  exact this

open scoped Classical in
include hU in
/-- **Corollary B.2 for all contracted points of a fibre, scheme level** (blueprint
`lem:sm-bdc-stabdown-fibre-scheme`; Temkin, Lemma 4.4.2 with Corollary B.2). Let `k` be
algebraically closed and `f : C' → C` a proper morphism of reduced projective curves over `k`
(`f ≫ p = p'`) with `p_a(C') = p_a(C)`, an isomorphism over `U = C ∖ X` for a finite set
`X = J` of closed points which are not generic. For `x ∈ J` let `G x` be the components of
`Z_x = f⁻¹(x)`, and assume every `Z_x` is a connected curve (`hZ`, `hcurve`) along which `C'` is
semi-stable (`hnodal`), with nonnegative component genera (`hg`). Let `Γ` be the incidence graph
of `C'` along `f⁻¹(X)` and `π : C̃ → C` the normalization of `C`. Then

* `|π⁻¹(x)| = |∂_Γ (G x)|` and `G x` is connected in `Γ`, for every `x ∈ J`, and
* every `x ∈ J` is an ordinary point (`δ(x) + 1 = |π⁻¹(x)|`) if and only if every `G x` is a
  `ℙ¹`-tree in `Γ`. -/
theorem stabdown_finset [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p') (J : Finset C)
    (hJ : (J : Set C) = X) (hXg : ∀ x ∈ X, x ∉ genericPoints C)
    (hXc : ∀ x ∈ X, IsClosed ({x} : Set C)) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : C → Finset C') (hG : ∀ x ∈ J, (G x : Set C') = innerPoints f x)
    (hZ : ∀ x ∈ J, _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ x ∈ J, ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' X, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' X))] :
    (∀ x ∈ J, Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) =
        ((nodalGraph p' hdim' (f ⁻¹' X)).boundary (G x)).card) ∧
      (∀ x ∈ J, (nodalGraph p' hdim' (f ⁻¹' X)).IsConnected (G x)) ∧
      ((∀ x ∈ J, deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x +
          1 = Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x})) ↔
        ∀ x ∈ J, (nodalGraph p' hdim' (f ⁻¹' X)).IsP1Tree (G x)) := by
  have : LocallyOfFinitePresentation p' := by
    have := isLocallyNoetherian_of_locallyOfFiniteType p'
    infer_instance
  set Γ := nodalGraph p' hdim' (f ⁻¹' X) with hΓ
  -- the closed set `X` and the subcurve `f⁻¹(X)`
  have hXcl : IsClosed X := by
    rw [← hJ, ← Set.biUnion_of_singleton (J : Set C)]
    exact isClosed_biUnion_finset fun x hx => hXc x (hJ ▸ hx)
  have hZc : IsClosed (f ⁻¹' X) := hXcl.preimage f.continuous
  have hmemX : ∀ x ∈ J, x ∈ X := fun x hx => hJ ▸ hx
  -- `f v = x` for `v ∈ G x`
  have hfG : ∀ x ∈ J, ∀ v ∈ G x, v ∈ genericPoints C' ∧ f v = x := fun x hx v hv => by
    have : v ∈ (G x : Set C') := hv
    rw [hG x hx] at this
    exact this
  -- all components of the contracted fibres
  let Gt : Finset C' := J.biUnion G
  have hGt : (Gt : Set C') = innerSet f X := by
    ext v
    simp only [Gt, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, hv⟩
      obtain ⟨hvg, hvx⟩ := hfG x hx v hv
      exact ⟨hvg, hvx ▸ hmemX x hx⟩
    · rintro ⟨hvg, hvX⟩
      have hx : f v ∈ J := by rw [← Finset.mem_coe, hJ]; exact hvX
      refine ⟨f v, hx, ?_⟩
      have : v ∈ innerPoints f (f v) := ⟨hvg, rfl⟩
      rw [← hG (f v) hx] at this
      exact this
  have hGt' : (Gt : Set C') = genericPoints C' ∩ f ⁻¹' X := hGt
  have hO : outerSet f X = genericPoints C' \ f ⁻¹' X := rfl
  have hcurveZ : ∀ z ∈ f ⁻¹' X, ∃ v ∈ Gt, z ∈ closure {v} := by
    intro z hz
    have hx : f z ∈ J := by rw [← Finset.mem_coe, hJ]; exact hz
    obtain ⟨v, hv, hzv⟩ := hcurve (f z) hx z rfl
    exact ⟨v, Finset.mem_biUnion.2 ⟨f z, hx, hv⟩, hzv⟩
  have hGsub : ∀ x ∈ J, G x ⊆ Gt := fun x hx => Finset.subset_biUnion_of_mem G hx
  -- components of different fibres
  have hsepx : ∀ x ∈ J, ∀ v ∈ Gt, ∀ z ∈ f ⁻¹' {x}, z ∈ closure {v} → v ∈ G x := by
    intro x hx v hv z hz hzv
    obtain ⟨y, hy, hvy⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨-, hfv⟩ := hfG y hy v hvy
    have hfz := eq_of_mem_closure_of_isClosed f (hfv ▸ hXc y (hmemX y hy)) hzv
    have hxy : x = y := by
      rw [← hfv, ← hfz]
      exact hz.symm
    exact hxy ▸ hvy
  have hGne : ∀ x ∈ J, (G x).Nonempty := by
    intro x hx
    obtain ⟨z, hz⟩ := (hZ x hx).nonempty
    obtain ⟨v, hv, -⟩ := hcurve x hx z hz
    exact ⟨v, hv⟩
  -- the outer normalization `b` and the normalization of `C`
  have hfin := isFinite_outerSetMap f X U hU p' hdim' hXcl
  have hδb : ∀ y, deltaInvariant (outerSetMap f X) (structureCoeff p) y =
      deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) y :=
    deltaInvariant_outerSetMap_eq f X U hU hXg (structureCoeff p)
  have hbr : ∀ y, Nat.card ↥(outerSetMap f X ⁻¹' {y}) =
      Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {y}) :=
    natCard_outerSetMap_fiber_eq f X U hU hXg
  -- (1) the branch count
  have hcount : ∀ x ∈ J, Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) =
      (Γ.boundary (G x)).card := by
    intro x hx
    rw [← hbr x]
    have hfib : outerSetMap f X ⁻¹' {x} = normalizationPointsMap (outerSet f X) ⁻¹' (f ⁻¹' {x}) :=
      rfl
    rw [hfib]
    have hxX := hmemX x hx
    exact natCard_preimage_eq_card_boundary_of_subset p' hdim' hGt' hO hcurveZ hnodal
      (Y := f ⁻¹' {x}) (hG x hx) ((hXc x hxX).preimage f.continuous)
      (fun z hz => by rw [Set.mem_preimage, Set.mem_singleton_iff.1 hz]; exact hxX)
      (fun v hv z hz hzv => hsepx x hx v hv z hz hzv)
  -- (2) connectedness in the incidence graph
  have hconn : ∀ x ∈ J, Γ.IsConnected (G x) := by
    intro x hx
    have hunion : (⋃ v ∈ G x, closure ({v} : Set C')) = f ⁻¹' {x} := by
      refine Set.Subset.antisymm (Set.iUnion₂_subset fun v hv => ?_) fun z hz => ?_
      · obtain ⟨-, hfv⟩ := hfG x hx v hv
        exact closure_minimal (Set.singleton_subset_iff.2 hfv)
          ((hXc x (hmemX x hx)).preimage f.continuous)
      · obtain ⟨v, hv, hzv⟩ := hcurve x hx z hz
        exact Set.mem_biUnion hv hzv
    exact isConnected_nodalGraph p' hdim' hZc hGt' hnodal (hGsub x hx) (hGne x hx)
      (hunion ▸ (hZ x hx).isPreconnected)
  -- (3) the δ-sum
  have hdisj : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → Disjoint (G x) (G y) := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro v hvx hvy
    exact hxy ((hfG x hx v hvx).2.symm.trans (hfG y hy v hvy).2)
  have hinj : ∀ x ∈ J, ∀ y ∈ J, G x = G y → x = y := by
    intro x hx y hy hxy
    obtain ⟨v, hv⟩ := hGne x hx
    exact (hfG x hx v hv).2.symm.trans (hfG y hy v (hxy ▸ hv)).2
  have hcount_nodes : ∑ x ∈ J, ((Γ.boundary (G x)).card + (Γ.inner (G x)).card) =
      Fintype.card (nodesIn p' (f ⁻¹' X)) := by
    rw [← Finset.sum_image (f := fun Y => (Γ.boundary Y).card + (Γ.inner Y).card) hinj]
    refine sum_card_boundary_add_card_inner Γ (G := Gt) ?_ ?_ ?_
    · intro v hv
      obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.1 hv
      exact ⟨G x, Finset.mem_image_of_mem G hx, hvx⟩
    · intro e Y hY Y' hY' hvY hwY'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hY
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hY'
      obtain ⟨v, hv, hvx⟩ := hvY
      obtain ⟨w, hw, hwy⟩ := hwY'
      obtain ⟨-, hev⟩ := (mem_nodalGraph_ends p' hdim' e v).1 hv
      obtain ⟨-, hew⟩ := (mem_nodalGraph_ends p' hdim' e w).1 hw
      have h1 := eq_of_mem_closure_of_isClosed f
        ((hfG x hx v hvx).2 ▸ hXc x (hmemX x hx)) hev
      have h2 := eq_of_mem_closure_of_isClosed f
        ((hfG y hy w hwy).2 ▸ hXc y (hmemX y hy)) hew
      rw [(hfG x hx v hvx).2] at h1
      rw [(hfG y hy w hwy).2] at h2
      rw [← h1, ← h2]
    · intro e
      obtain ⟨v, hv, hev⟩ := hcurveZ e.1 e.2.1
      have hvg : v ∈ genericPoints C' := by
        have : v ∈ (Gt : Set C') := hv
        rw [hGt'] at this
        exact this.1
      exact ⟨v, (mem_nodalGraph_ends p' hdim' e v).2 ⟨hvg, hev⟩, hv⟩
  have hsum : ∑ x ∈ J,
      (deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x : ℤ) =
      ∑ x ∈ J, contractedDelta Γ (G x) := by
    obtain ⟨-, -, hδ⟩ := deltaInvariant_contraction_finset f X U hU p p' hfp J hJ hXg hXcl hdim
      hdim' hp hp' Gt hGt
    rw [hpa, sub_self, add_zero, finsum_deltaInvariant_eq_ncard_nodes p' hdim' _ hnodal] at hδ
    have hpd : (J : Set C).PairwiseDisjoint G := fun x hx y hy hxy => hdisj x hx y hy hxy
    have hgsum : ∑ v ∈ Gt, componentGenus (structureCoeff p') v =
        ∑ x ∈ J, ∑ v ∈ G x, (Γ.genus v : ℤ) := by
      rw [Finset.sum_biUnion hpd]
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun v hv => ?_
      rw [hΓ, nodalGraph_genus, Int.toNat_of_nonneg (hg x hx v hv)]
    have hcard : (Gt.card : ℤ) = ∑ x ∈ J, ((G x).card : ℤ) := by
      rw [Finset.card_biUnion hpd]
      push_cast
      rfl
    have hncard : ((nodesIn p' (f ⁻¹' X)).ncard : ℤ) =
        ∑ x ∈ J, (((Γ.boundary (G x)).card : ℤ) + (Γ.inner (G x)).card) := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      exact_mod_cast hcount_nodes.symm
    simp only [← hδb]
    rw [show (∑ x ∈ J, (deltaInvariant (outerSetMap f X) (structureCoeff p) x : ℤ)) =
      ((∑ x ∈ J, deltaInvariant (outerSetMap f X) (structureCoeff p) x : ℕ) : ℤ) by push_cast; rfl,
      hδ, hncard, hgsum, hcard]
    simp only [contractedDelta, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- (4) Temkin's inequality and the comparison of defects
  have hle : ∀ x ∈ J, (Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) : ℤ) - 1 ≤
      deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x := by
    intro x hx
    have := natCard_fiber_le_deltaInvariant_add_one p hdim x (hXc x (hmemX x hx))
    omega
  have key := stabdown_numerical_finset J G hconn
    (fun x => (deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x : ℤ))
    (fun x => (Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) : ℤ))
    (fun x hx => by simp only [hcount x hx]) hle hsum
  refine ⟨hcount, hconn, ?_⟩
  rw [← key]
  refine forall₂_congr fun x _ => ?_
  omega

open scoped Classical in
include hU in
/-- **The stability criterion over an algebraically closed field, "only if" direction**
(blueprint `lem:sm-bdc-stabdown-fibre-scheme`; Temkin, Lemma 4.4.2, T:3131–3132). In the situation
of `stabdown_finset`, let `m x` be the number of marks through `x` (in Lemma 4.4.2, the number of
sections `P̄ᵢ` through `x`, equal to the number of marks of `C'_s` on `Z_x`,
`lem:sm-bd-marks`). If every `x ∈ J` is a smooth point or an ordinary double point of `C`
carrying at most one mark, and a mark only at a smooth point (`(C, D)` semi-stable at `x`), then
every `Z_x` is an exceptional tree: a `ℙ¹`-tree with `|∂Z_x| + m x ≤ 2`. -/
theorem stabdown_finset_exceptional_of_semistable [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p') (J : Finset C)
    (hJ : (J : Set C) = X) (hXg : ∀ x ∈ X, x ∉ genericPoints C)
    (hXc : ∀ x ∈ X, IsClosed ({x} : Set C)) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : C → Finset C') (hG : ∀ x ∈ J, (G x : Set C') = innerPoints f x)
    (hZ : ∀ x ∈ J, _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ x ∈ J, ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' X, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' X))] (m : C → ℕ)
    (hss : ∀ x ∈ J, (DeJong.IsSmoothAt p x ∨ Geometry.IsGeometricOrdinaryDoublePoint p x) ∧
      m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt p x)) :
    ∀ x ∈ J, (nodalGraph p' hdim' (f ⁻¹' X)).IsP1Tree (G x) ∧
      ((nodalGraph p' hdim' (f ⁻¹' X)).boundary (G x)).card + m x ≤ 2 := by
  have : LocallyOfFinitePresentation p := by
    have := isLocallyNoetherian_of_locallyOfFiniteType p
    infer_instance
  obtain ⟨hcount, -, hiff⟩ := stabdown_finset f X U hU p p' hfp J hJ hXg hXc hdim hdim' hp hp'
    hpa G hG hZ hcurve hnodal hg
  have hmemX : ∀ x ∈ J, x ∈ X := fun x hx => hJ ▸ hx
  -- smooth points and double points are ordinary, with one resp. two branches
  have hord : ∀ x ∈ J, deltaInvariant (normalizationPointsMap (genericPoints C))
      (structureCoeff p) x + 1 = Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) ∧
      Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) ≤ 2 ∧
      (DeJong.IsSmoothAt p x →
        Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) = 1) := by
    intro x hx
    have hxc := hXc x (hmemX x hx)
    have hxg := hXg x (hmemX x hx)
    have hsm1 : DeJong.IsSmoothAt p x →
        Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) = 1 := fun hsm =>
      natCard_fiber_eq_one_of_isSmoothAt p hdim x hxc hxg hsm
    refine ⟨?_, ?_, hsm1⟩ <;> rcases (hss x hx).1 with hsm | hnode
    · rw [(deltaInvariant_eq_zero_of_isSmoothAt p hdim x hxc hxg hsm).1, hsm1 hsm]
    · rw [(deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint p hdim x hxc hxg hnode).1,
        natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint p hdim x hxc hxg hnode]
    · rw [hsm1 hsm]
      omega
    · rw [natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint p hdim x hxc hxg hnode]
  have htree := hiff.1 fun x hx => (hord x hx).1
  intro x hx
  refine ⟨htree x hx, ?_⟩
  rw [← hcount x hx]
  obtain ⟨-, h2, h1⟩ := hord x hx
  obtain ⟨-, hm, hm1⟩ := hss x hx
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with h0 | h0
  · omega
  · have := h1 (hm1 h0)
    omega

open scoped Classical in
include hU in
/-- **The stability criterion over an algebraically closed field, "if" direction, ordinary
form** (blueprint `lem:sm-bdc-stabdown-fibre-scheme`; Temkin, Lemma 4.4.2, T:3131–3132). In the
situation of `stabdown_finset`, if every `Z_x` is an exceptional tree (a `ℙ¹`-tree with
`|∂Z_x| + m x ≤ 2`), then every `x ∈ J` is an ordinary point (`δ(x) + 1 = |x̃|`) with at most
two branches, at most one mark, and only one branch if it carries a mark. -/
theorem stabdown_finset_ordinary_of_exceptional [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p') (J : Finset C)
    (hJ : (J : Set C) = X) (hXg : ∀ x ∈ X, x ∉ genericPoints C)
    (hXc : ∀ x ∈ X, IsClosed ({x} : Set C)) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : C → Finset C') (hG : ∀ x ∈ J, (G x : Set C') = innerPoints f x)
    (hZ : ∀ x ∈ J, _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ x ∈ J, ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' X, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' X))] (m : C → ℕ)
    (hexc : ∀ x ∈ J, (nodalGraph p' hdim' (f ⁻¹' X)).IsP1Tree (G x) ∧
      ((nodalGraph p' hdim' (f ⁻¹' X)).boundary (G x)).card + m x ≤ 2) :
    ∀ x ∈ J, deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x + 1 =
        Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) ∧
      Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) ≤ 2 ∧ m x ≤ 1 ∧
      (m x = 1 → Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) = 1) := by
  obtain ⟨hcount, -, hiff⟩ := stabdown_finset f X U hU p p' hfp J hJ hXg hXc hdim hdim' hp hp'
    hpa G hG hZ hcurve hnodal hg
  have hord := hiff.2 fun x hx => (hexc x hx).1
  intro x hx
  have hpos := natCard_fiber_pos p x
  have h2 := (hexc x hx).2
  rw [← hcount x hx] at h2
  refine ⟨hord x hx, by omega, by omega, fun h => by omega⟩

end Fibre

section Completion

/-- **The converse of the ordinary-completion lemma for `n ≤ 2`** (blueprint
`lem:sm-ordinary-completion`, directions "gluing ⇒ completed" for `n = 1, 2`; Temkin, App. B,
l. 4381–4397): over the field `k`, a closed point `x` of a reduced curve `C`, not a generic point,
which is ordinary (`δ(x) + 1 = |x̃|`, `x̃` the points of the normalization over `x`) is a smooth
point if `|x̃| = 1` and an ordinary double point (`𝒪̂_{C,x} ≅ k[[u, v]]/(uv)`) if `|x̃| = 2`.
For `k` algebraically closed this is true (for `|x̃| = 1`, `𝒪_{C,x}` is integrally closed, hence a
discrete valuation ring, regular, hence smooth over the perfect `k`; for `|x̃| = 2`,
`𝒪̂_{C,x} ≅ {(a, b) ∈ k[[t]]² : a(0) = b(0)}`), but it is **not proved here**: it is the remaining
input of the "if" direction of the stability criterion in the completed-local form
(`stabdown_finset_semistable_of_exceptional`). -/
def OrdinaryPointCompletion (k : Type u) [Field k] : Prop :=
  ∀ (C : Scheme.{u}) [IsAffineHom (pullback.diagonal (terminal.from C))]
    [Finite (genericPoints C)] [IsReduced C] [CompactSpace C] (p : C ⟶ Spec (.of k))
    [LocallyOfFiniteType p], topologicalKrullDim C ≤ 1 → ∀ x : C, IsClosed ({x} : Set C) →
    x ∉ genericPoints C →
    deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x + 1 =
      Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) →
    (Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) = 1 → DeJong.IsSmoothAt p x) ∧
      (Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) = 2 →
        Geometry.IsGeometricOrdinaryDoublePoint p x)

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (X : Set C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ∉ X)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

open scoped Classical in
include hU in
/-- **The stability criterion over an algebraically closed field** (blueprint
`lem:sm-bdc-stabdown-fibre-scheme`; Temkin, Lemma 4.4.2 at all contracted points of a fibre),
assuming the converse of the ordinary-completion lemma (`OrdinaryPointCompletion k`, not proved
here): in the situation of `stabdown_finset`, every `x ∈ J` is a smooth point or an ordinary double
point of `C` with at most one mark, and a mark only at a smooth point, **if and only if** every
`Z_x` is an exceptional tree (a `ℙ¹`-tree with `|∂Z_x| + m x ≤ 2`). The "only if" direction
(`stabdown_finset_exceptional_of_semistable`) does not use `OrdinaryPointCompletion`. -/
theorem stabdown_finset_semistable_iff [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p') (J : Finset C)
    (hJ : (J : Set C) = X) (hXg : ∀ x ∈ X, x ∉ genericPoints C)
    (hXc : ∀ x ∈ X, IsClosed ({x} : Set C)) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : C → Finset C') (hG : ∀ x ∈ J, (G x : Set C') = innerPoints f x)
    (hZ : ∀ x ∈ J, _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ x ∈ J, ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' X, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ x ∈ J, ∀ v ∈ G x, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' X))] (m : C → ℕ) (hcompl : OrdinaryPointCompletion k) :
    (∀ x ∈ J, (DeJong.IsSmoothAt p x ∨ Geometry.IsGeometricOrdinaryDoublePoint p x) ∧
      m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt p x)) ↔
    ∀ x ∈ J, (nodalGraph p' hdim' (f ⁻¹' X)).IsP1Tree (G x) ∧
      ((nodalGraph p' hdim' (f ⁻¹' X)).boundary (G x)).card + m x ≤ 2 := by
  refine ⟨stabdown_finset_exceptional_of_semistable f X U hU p p' hfp J hJ hXg hXc hdim hdim' hp
    hp' hpa G hG hZ hcurve hnodal hg m, fun hexc x hx => ?_⟩
  obtain ⟨hord, h2, hm, hm1⟩ := stabdown_finset_ordinary_of_exceptional f X U hU p p' hfp J hJ hXg
    hXc hdim hdim' hp hp' hpa G hG hZ hcurve hnodal hg m hexc x hx
  have hxX : x ∈ X := hJ ▸ hx
  obtain ⟨hsm, hnode⟩ := hcompl C p hdim x (hXc x hxX) (hXg x hxX) hord
  have hpos := natCard_fiber_pos p x
  refine ⟨?_, hm, fun h => hsm (hm1 h)⟩
  rcases Nat.lt_or_ge (Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x})) 2 with h | h
  · exact Or.inl (hsm (by omega))
  · exact Or.inr (hnode (by omega))

end Completion

end

end DeJongAlterations.StableModification.BlowDown
