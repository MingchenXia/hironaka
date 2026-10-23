/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ComponentGenusSplit

/-!
# The genus of a component of a nodal curve meeting the others only in double points

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), App. B: for
a reduced projective curve `Y` over `k = k̄` whose closed points are smooth points or ordinary
double points, and a component `Z = closure {v}` such that every double point of `Y` on `Z` also
lies on another component, the reduced curve `Z` has arithmetic genus `p_a(Z) = g(v)`, the genus of
its normalization (`nodalComponentGenus`, the named hypothesis
`BlowDown.NoClosedExc.NodalComponentGenus` of lane T44A3). This is how a combinatorially exceptional
component (genus `0` normalization, no self-intersection) is recognized as numerically exceptional
(`p_a = 0`) in Temkin's Lemma 4.4.4 (T:3158–3176).

## The argument

By Temkin's genus formula for the integral curve `Z` (Lemma B.1, T:4413–4433,
`CurvesField.Genus.arithmeticGenus_eq_one_sub_card_add`) `p_a(Z) = g(v) + ∑ᶠ_x δ_Z(x)`, so it
suffices that `δ_Z` vanishes. At the generic point this is
`CurvesField.Genus.deltaInvariant_eq_zero_of_mem_genericPoints`. At a closed point `x` with image
`y ∈ Y`, the normalization of `Z` is that of `Y` in `Spec κ(v)` (`ExcSpecialize.normalizationPointsIso`),
so `δ_Z(x) = δ_{Ỹ_v}(y)` (`deltaInvariant_closureScheme_eq`); and since the normalization `Ỹ` of
`Y` is `Ỹ_v ⊔ Ỹ_{≠ v}`, `δ_{Ỹ_v}(y) ≤ δ_Y(y)`, with `δ_{Ỹ_v}(y) + 1 ≤ δ_Y(y)` when `y` lies on
another component (`ComponentGenus.deltaInvariant_normalizationPoints_add_one_le`). Now `δ_Y(y) = 0`
at a smooth point and `δ_Y(y) = 1` at a double point
(`CurvesField.Genus.deltaInvariant_eq_zero_of_isSmoothAt`,
`deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint`), and by hypothesis every double point on
`Z` lies on another component.

## Main results

* `deltaInvariant_comp_of_isClosedImmersion`: the δ-invariant of `N → T` at `x` is that of
  `N → T → X` at `j x` for a closed immersion `j`.
* `deltaInvariant_normalizationPoints_le`, `deltaInvariant_normalizationPoints_add_one_le`: the
  comparison of the normalizations of a reduced curve in a subset of its generic points.
* `deltaInvariant_closureScheme_eq`: `δ_Z(x) = δ_{Ỹ_v}(y)`.
* `nodalComponentGenus`: **`NoClosedExc.NodalComponentGenus`**.

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-component-genus`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.ComponentGenus

universe u

open Cohomology CurvesField CurvesField.Genus ClosureComponent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Transfer

variable {k : Type u} [Field k]

/-- **The δ-invariant is computed in an ambient scheme**: for a closed immersion `j : T → X` and an
affine `π : N → T`, `δ_π(x) = δ_{π ≫ j}(j x)` (constants pulled back along `j`). On an affine
chart `V ∋ j x` this is `deltaAt_comp_surjective` for the surjection `Γ(V, 𝒪_X) → Γ(j⁻¹V, 𝒪_T)`. -/
theorem deltaInvariant_comp_of_isClosedImmersion {N T X : Scheme.{u}} (π : N ⟶ T) (j : T ⟶ X)
    [IsClosedImmersion j] [IsAffineHom π] [IsAffineHom (π ≫ j)] (c : k →+* Γ(X, ⊤)) (x : T) :
    deltaInvariant π (j.appTop.hom.comp c) x = deltaInvariant (π ≫ j) c (j x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j x)) isOpen_univ
  have hV' : IsAffineOpen (j ⁻¹ᵁ V) := hV.preimage j
  have hxV' : x ∈ j ⁻¹ᵁ V := hxV
  rw [← chartDelta_eq_deltaInvariant (π := π ≫ j) V hV (j x) hxV,
    ← chartDelta_eq_deltaInvariant (π := π) (j ⁻¹ᵁ V) hV' x hxV']
  have hsurj : Function.Surjective (j.app V).hom := j.app_surjective V hV
  have key := deltaAt_comp_surjective (sectionsRingHom c (le_top : V ≤ ⊤)) (j.app V).hom hsurj
    (π.app (j ⁻¹ᵁ V)).hom (hV'.primeIdealOf ⟨x, hxV'⟩)
  have hc : (j.app V).hom.comp (sectionsRingHom c (le_top : V ≤ ⊤)) =
      sectionsRingHom (j.appTop.hom.comp c) (le_top : j ⁻¹ᵁ V ≤ ⊤) := by
    have := j.naturality (homOfLE (le_top : V ≤ ⊤)).op
    ext a
    exact congrArg (fun φ => φ.hom (c a)) this
  have hq : (⟨(hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal.comap (j.app V).hom,
      Ideal.comap_isPrime _ _⟩ : PrimeSpectrum Γ(X, V)) = hV.primeIdealOf ⟨j x, hxV⟩ := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := j) V hV (j ⁻¹ᵁ V) hV' le_rfl hxV'
    rw [Scheme.Hom.appLE_eq_app] at h
    rw [← h]
    rfl
  unfold chartDelta
  rw [hc, hq] at key
  exact key

/-- The δ-invariant is unchanged by an isomorphism of the source. -/
theorem deltaInvariant_iso_comp {N N' X : Scheme.{u}} (e : N' ≅ N) (π : N ⟶ X) [IsAffineHom π]
    [IsAffineHom (e.hom ≫ π)] (c : k →+* Γ(X, ⊤)) (x : X) :
    deltaInvariant (e.hom ≫ π) c x = deltaInvariant π c x := by
  refine deltaInvariant_eq_of_isOpenImmersion π e.hom _ rfl c x ⊤ trivial ?_
  intro z _
  exact ⟨e.inv z, by rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl⟩

end Transfer

section Normalization

variable {C : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from C))] {k : Type u}
  [Field k] (q : C ⟶ Spec (.of k)) [LocallyOfFiniteType q]

/-- **The normalization in fewer points has smaller δ-invariant**: for `S = S₁ ⊔ S₂` finite,
`δ_{C̃_{S₁}}(y) ≤ δ_{C̃_S}(y)` when `π_*𝒪_{C̃_S}/𝒪_C` is finite-dimensional on affine opens. -/
theorem deltaInvariant_normalizationPoints_le (S S₁ S₂ : Set C) [Finite S] [Finite S₁]
    [Finite S₂] (hS : S = S₁ ∪ S₂) (hd : Disjoint S₁ S₂)
    (hfin : ∀ (W : C.Opens) (hW : IsAffineOpen W),
      IsFiniteCoker (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤))
        ((normalizationPointsMap S).app W).hom) (y : C) :
    deltaInvariant (normalizationPointsMap S₁) (structureCoeff q) y ≤
      deltaInvariant (normalizationPointsMap S) (structureCoeff q) y := by
  subst hS
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_opensRange_pointsIncl hd)
  have : IsFinite (normalizationPointsMap (S₁ ∪ S₂)) := isFinite_normalizationPointsMap q
  have : IsFinite (normalizationPointsMap S₁) := isFinite_normalizationPointsMap q
  exact deltaInvariant_le_of_coprod (pointsMap C (S₁ ∪ S₂)) e (structureCoeff q)
    (pointsIncl_pointsMap _) hfin y

/-- **Splitting off the other components lowers the δ-invariant** (blueprint
`lem:sm-bdu-delta-split`): for a reduced `C` (`𝒪_C → π_*𝒪_{C̃_S}` injective on affine opens),
`S = S₁ ⊔ S₂` finite and a point `y` lying on the closure of a point of `S₁` and on the closure of a
point of `S₂`, `δ_{C̃_{S₁}}(y) + 1 ≤ δ_{C̃_S}(y)`. -/
theorem deltaInvariant_normalizationPoints_add_one_le (S S₁ S₂ : Set C) [Finite S] [Finite S₁]
    [Finite S₂] (hS : S = S₁ ∪ S₂) (hd : Disjoint S₁ S₂)
    (hinj : ∀ (W : C.Opens), IsAffineOpen W →
      Function.Injective ((normalizationPointsMap S).app W).hom)
    (hfin : ∀ (W : C.Opens) (hW : IsAffineOpen W),
      IsFiniteCoker (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤))
        ((normalizationPointsMap S).app W).hom) (y : C)
    (h₁ : ∃ v ∈ S₁, y ∈ closure {v}) (h₂ : ∃ w ∈ S₂, y ∈ closure {w}) :
    deltaInvariant (normalizationPointsMap S₁) (structureCoeff q) y + 1 ≤
      deltaInvariant (normalizationPointsMap S) (structureCoeff q) y := by
  obtain ⟨a, ha⟩ := (nonempty_fiber_iff q S₁ y).2 h₁
  obtain ⟨b, hb⟩ := (nonempty_fiber_iff q S₂ y).2 h₂
  subst hS
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_opensRange_pointsIncl hd)
  have : IsFinite (normalizationPointsMap (S₁ ∪ S₂)) := isFinite_normalizationPointsMap q
  have : IsFinite (normalizationPointsMap S₁) := isFinite_normalizationPointsMap q
  exact deltaInvariant_add_one_le_of_coprod (pointsMap C (S₁ ∪ S₂)) e (structureCoeff q)
    (pointsIncl_pointsMap _) (pointsIncl_pointsMap _) hinj hfin y ⟨a, ha⟩ ⟨b, hb⟩

end Normalization

section Closure

variable {Y : Scheme.{u}} [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
  {k : Type u} [Field k] (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]

/-- **The δ-invariant of a component is computed by the normalization of the ambient curve in
its generic point**: for `Z = closure {v}` with the reduced structure (`closureScheme v`) and
`S = {closurePt v}` its generic point, `δ_Z(x) = δ_{Ỹ_v}(x)` where `Ỹ_v → Y` is the normalization
of `Y` in `Spec κ(v)` (`ExcSpecialize.normalizationPointsIso`). -/
theorem deltaInvariant_closureScheme_eq (v : Y) (S : Set (closureScheme v)) [Finite S]
    (hS : S = {closurePt v}) (x : closureScheme v) :
    deltaInvariant (normalizationPointsMap S) (structureCoeff (closureι v ≫ q)) x =
      deltaInvariant (normalizationPointsMap ({v} : Set Y)) (structureCoeff q) (closureι v x) := by
  subst hS
  have : IsFinite (normalizationPointsMap ({closurePt v} : Set (closureScheme v))) :=
    isFinite_normalizationPointsMap (closureι v ≫ q)
  have : IsFinite (normalizationPointsMap ({closureι v (closurePt v)} : Set Y)) :=
    isFinite_normalizationPointsMap q
  have h₁ := deltaInvariant_comp_of_isClosedImmersion
    (normalizationPointsMap ({closurePt v} : Set (closureScheme v))) (closureι v)
    (structureCoeff q) x
  have h₂ := ExcSpecialize.normalizationPointsIso_hom_comp q (closureι v) (closurePt v)
  have h₃ := deltaInvariant_iso_comp (ExcSpecialize.normalizationPointsIso q (closureι v) (closurePt v))
    (normalizationPointsMap ({closureι v (closurePt v)} : Set Y)) (structureCoeff q) (closureι v x)
  have h₄ : ∀ (a b : Y), a = b →
      deltaInvariant (normalizationPointsMap ({a} : Set Y)) (structureCoeff q) (closureι v x) =
        deltaInvariant (normalizationPointsMap ({b} : Set Y)) (structureCoeff q) (closureι v x) := by
    rintro a b rfl
    rfl
  rw [ExcSpecialize.structureCoeff_comp, h₁, ← h₂, h₃]
  exact h₄ _ _ (closureι_closurePt v)

end Closure

section Main

/-- **The genus of a component of a nodal curve meeting the others only in double points**
(`BlowDown.NoClosedExc.NodalComponentGenus`; blueprint `lem:sm-bdu-component-genus`). Let `Y` be
a reduced curve, projective over `k = k̄`, whose closed points are smooth points or ordinary double
points, and `v` a generic point such that every double point of `Y` on `closure {v}` lies on
another component. Then the reduced component `closure {v}` has arithmetic genus `g(v)`: by
Temkin's genus formula for the integral curve `Z = closure {v}` it suffices that `δ_Z = 0`, and at a
closed point `y` of `Z`, `δ_Z(y) ≤ δ_Y(y) = 0` if `y` is smooth and `δ_Z(y) + 1 ≤ δ_Y(y) = 1` if `y` is
a double point (`deltaInvariant_normalizationPoints_le`,
`deltaInvariant_normalizationPoints_add_one_le`). -/
theorem nodalComponentGenus : NoClosedExc.NodalComponentGenus.{u} := by
  intro k _ _ Y q _ _ _ _ hdim hp hnodal v hv hbd
  have : Finite (genericPoints Y) := finite_genericPoints q
  have hpZ : IsProjectiveOver (closureι v ≫ q) :=
    DeJong.IsProjectiveOver.comp_isClosedImmersion hp _
  have hdimZ : topologicalKrullDim (closureScheme v) ≤ 1 :=
    (closureι v).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hgen : genericPoint (closureScheme v) = closurePt v := by
    have hg : IsGenericPoint (closurePt v) (⊤ : Set (closureScheme v)) := by
      rw [isGenericPoint_iff_specializes]
      exact fun x => ⟨fun _ => trivial, fun _ => closurePt_specializes v x⟩
    exact (genericPoint_spec (closureScheme v)).eq hg
  have hGZ : genericPoints (closureScheme v) = {closurePt v} := by
    rw [genericPoints_eq_singleton, hgen]
  obtain ⟨G, hGdef⟩ : ∃ G : Finset (closureScheme v), G = {closurePt v} := ⟨_, rfl⟩
  have hGs : (G : Set (closureScheme v)) = {closurePt v} := by
    rw [hGdef, Finset.coe_singleton]
  have hG : (G : Set (closureScheme v)) = genericPoints (closureScheme v) := by rw [hGs, hGZ]
  obtain ⟨-, hpa⟩ := arithmeticGenus_eq_one_sub_card_add (closureι v ≫ q) G hG hdimZ hpZ
  -- the δ-invariants of `Z` vanish
  have hzero : ∀ x : closureScheme v, deltaInvariant
      (normalizationPointsMap (G : Set (closureScheme v))) (structureCoeff (closureι v ≫ q)) x =
        0 := by
    intro x
    by_cases hxg : x ∈ genericPoints (closureScheme v)
    · have h := @deltaInvariant_eq_zero_of_mem_genericPoints (closureScheme v) inferInstance k _
        (G : Set _) inferInstance hG (structureCoeff (closureι v ≫ q)) x hxg
      exact h
    have hcl := @deltaInvariant_closureScheme_eq Y _ _ k _ q _ v (G : Set _) inferInstance hGs x
    rw [hcl]
    have hxc : IsClosed ({x} : Set (closureScheme v)) :=
      isClosed_singleton_of_not_mem_genericPoints hdimZ hxg
    have hyc : IsClosed ({closureι v x} : Set Y) := by
      have := (closureι v).isClosedEmbedding.isClosedMap _ hxc
      rwa [Set.image_singleton] at this
    have hyv : closureι v x ∈ closure {v} := by
      rw [← range_closureι]
      exact ⟨x, rfl⟩
    have hyg : closureι v x ∉ genericPoints Y := by
      intro hyg
      have hvy := eq_of_mem_closure_of_mem_genericPoints hyg hyv
      apply hxg
      rw [hGZ, Set.mem_singleton_iff]
      apply (closureι v).isClosedEmbedding.injective
      rw [closureι_closurePt]
      exact hvy.symm
    have hS : genericPoints Y = ({v} : Set Y) ∪ (genericPoints Y \ {v}) :=
      (Set.union_diff_cancel (Set.singleton_subset_iff.mpr hv)).symm
    have hd : Disjoint ({v} : Set Y) (genericPoints Y \ {v}) := Set.disjoint_sdiff_right
    have hfin := normalizationPoints_isFiniteCoker q (rfl : genericPoints Y = genericPoints Y) hdim
    have hinj := normalizationPoints_app_injective (C := Y) (S := genericPoints Y) rfl
    rcases hnodal (closureι v x) hyc with hsm | hnode
    · have h0 := (deltaInvariant_eq_zero_of_isSmoothAt q hdim _ hyc hyg hsm).1
      have hle := deltaInvariant_normalizationPoints_le q (genericPoints Y) {v}
        (genericPoints Y \ {v}) hS hd hfin (closureι v x)
      omega
    · obtain ⟨w, hw, hwv, hyw⟩ := hbd _ hyv hyc hnode
      have h1 := (deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint q hdim _ hyc hyg
        hnode).1
      have hle := deltaInvariant_normalizationPoints_add_one_le q (genericPoints Y) {v}
        (genericPoints Y \ {v}) hS hd hinj hfin (closureι v x) ⟨v, rfl, hyv⟩
        ⟨w, ⟨hw, hwv⟩, hyw⟩
      omega
  rw [hpa, finsum_eq_zero_of_forall_eq_zero hzero, hGdef, Finset.card_singleton,
    Finset.sum_singleton, ExcSpecialize.componentGenus_eq q (closureι v), closureι_closurePt]
  simp

end Main

end DeJongAlterations.StableModification.BlowDown.ComponentGenus
