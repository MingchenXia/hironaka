/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NumericalDescentSmooth

/-!
# Components and genera under an extension of algebraically closed fields

Let `k` be an algebraically closed field, `Y` a scheme locally of finite type over `k`, `K / k` a
field extension and `π : P → Y`, `P → Spec K` a pullback square of `Y → Spec k` along
`Spec K → Spec k`. For a point `v` of `Y` the base change `W = closure{v} ×_k K` of the reduced
closure of `v` (`ClosureComponent.closureScheme`) is a closed subscheme of `P` with support
`π⁻¹(closure {v})` (`closureBCι`, `range_closureBCι`). Since `W` is integral
(`irreducibleSpace_baseChange`, `isReduced_baseChange`):

* `isIrreducible_preimage_closure`: `π⁻¹(closure {v})` is irreducible;
* `exists_eq_preimage_of_mem_irreducibleComponents`: every irreducible component of `P` is the
  preimage of an irreducible component of `Y`;
* `arithmeticGenus_preimage_closure`: the reduced induced subscheme on `π⁻¹(closure {v})` is `W`,
  so its arithmetic genus is that of the reduced closure of `v` (`eulerChar_baseChange_field`).

Further, `exists_isClosed_singleton_and_eq` lifts closed points of `Y` to closed points of a
quasi-compact `P`, and `three_le_encard_inter_closedPoints` counts closed points of closed subsets
of Jacobson spaces.

These are the inputs of `BlowDown.NoClosedExc.NumericalDescent` (Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), §1.2): the notions of `p_a`, components and
special points of the fibres are compatible with extension of the algebraically closed ground
field.

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-components-base-change`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.NumericalDescent

universe u

open Cohomology CurvesField.Genus ClosureComponent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Counting

/-- **A closed subset of a Jacobson space with at least three points has at least three closed
points**: if it had finitely many closed points, it would be their closure, hence equal to the
finite set of them. -/
theorem three_le_encard_inter_closedPoints {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {F : Set X} (hF : IsClosed F) (h : 3 ≤ F.encard) : 3 ≤ (F ∩ closedPoints X).encard := by
  by_cases hfin : (F ∩ closedPoints X).Finite
  · have hcl : IsClosed (F ∩ closedPoints X) := by
      rw [← Set.biUnion_of_singleton (F ∩ closedPoints X)]
      exact hfin.isClosed_biUnion fun x hx => hx.2
    have h1 := JacobsonSpace.closure_inter_closedPoints_eq_closure hF.isLocallyClosed
    rw [hcl.closure_eq, hF.closure_eq] at h1
    rw [h1]
    exact h
  · rw [Set.Infinite.encard_eq hfin]
    exact le_top

end Counting

section Factor

variable {V : Type u} [CommRing V]

/-- **A field point of `Spec V` over `t` factors through `Spec κ(t)`.** -/
theorem exists_comp_residuePt_eq (t : PrimeSpectrum V) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ Spec (.of V)) (ha : ∀ x, a x = t) :
    ∃ ψ : t.asIdeal.ResidueField →+* K, Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t = a := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = a := ⟨Spec.preimage a, Spec.map_preimage a⟩
  obtain ⟨x⟩ : Nonempty (Spec (.of K)) := inferInstance
  have hker : RingHom.ker φ.hom = t.asIdeal := by
    have h := congrArg PrimeSpectrum.asIdeal (ha x)
    have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    change Ideal.comap φ.hom x.asIdeal = t.asIdeal at h
    rw [hx, ← RingHom.ker_eq_comap_bot] at h
    exact h
  refine ⟨Ideal.ResidueField.lift t.asIdeal φ.hom hker.ge ?_, ?_⟩
  · intro r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    refine isUnit_iff_ne_zero.mpr fun h0 => hr ?_
    rw [← hker]
    exact h0
  · rw [residuePt, ← Spec.map_comp]
    congr 1
    ext r
    simp

end Factor

section BaseChange

variable {k K : Type u} [Field k] [Field K] (ψ : k →+* K) {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of k)) {P : Scheme.{u}} {π : P ⟶ Y}
  {snd : P ⟶ Spec (CommRingCat.of K)} (H : IsPullback π snd q (Spec.map (CommRingCat.ofHom ψ)))

include H in
/-- **Closed points lift along `π`** when `P` is quasi-compact. -/
theorem exists_isClosed_singleton_and_eq [CompactSpace P] (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ∃ x : P, IsClosed ({x} : Set P) ∧ π x = y := by
  obtain ⟨x₀, hx₀⟩ := surjective_fst_of_isPullback ψ q H y
  obtain ⟨x, hx, hxc⟩ := (isClosed_closure (s := ({x₀} : Set P))).exists_closed_singleton
    ⟨x₀, subset_closure rfl⟩
  refine ⟨x, hxc, ?_⟩
  have hsp : π x₀ ⤳ π x := (specializes_iff_mem_closure.mpr hx).map π.continuous
  rw [hx₀, specializes_iff_mem_closure, hy.closure_eq] at hsp
  exact hsp

/-- The base change `closure{v} ×_k K` of the reduced closure of `v`. -/
abbrev closureBC (v : Y) : Scheme.{u} :=
  pullback (C := Scheme.{u}) (closureι v ≫ q) (Spec.map (CommRingCat.ofHom ψ))

include H in
/-- The closed immersion `closure{v} ×_k K → P`. -/
def closureBCι (v : Y) : closureBC ψ q v ⟶ P :=
  H.lift (bcFst ψ (closureι v ≫ q) ≫ closureι v) (bcSnd ψ (closureι v ≫ q)) (by
    rw [Category.assoc]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem closureBCι_fst (v : Y) :
    closureBCι ψ q H v ≫ π = bcFst ψ (closureι v ≫ q) ≫ closureι v :=
  H.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem closureBCι_snd (v : Y) :
    closureBCι ψ q H v ≫ snd = bcSnd ψ (closureι v ≫ q) :=
  H.lift_snd _ _ _

/-- `closure{v} ×_k K` is the preimage of `closure{v}` under `π`. -/
theorem isPullback_closureBCι (v : Y) :
    IsPullback (bcFst ψ (closureι v ≫ q)) (closureBCι ψ q H v) (closureι v) π := by
  refine IsPullback.of_bot ?_ (closureBCι_fst ψ q H v).symm H
  rw [closureBCι_snd]
  exact IsPullback.of_hasPullback _ _

instance isClosedImmersion_closureBCι (v : Y) : IsClosedImmersion (closureBCι ψ q H v) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_closureBCι ψ q H v)
    inferInstance

/-- The support of `closure{v} ×_k K` is `π⁻¹(closure {v})`. -/
theorem range_closureBCι (v : Y) : Set.range (closureBCι ψ q H v) = π ⁻¹' closure {v} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rw [Set.mem_preimage, ← range_closureι]
    exact ⟨bcFst ψ (closureι v ≫ q) w, by
      rw [← Scheme.Hom.comp_apply, ← closureBCι_fst ψ q H v, Scheme.Hom.comp_apply]⟩
  · intro hx
    rw [Set.mem_preimage, ← range_closureι] at hx
    obtain ⟨z, hz⟩ := hx
    let H' := isPullback_closureBCι ψ q H v
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    refine ⟨H'.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_snd, hw₂]

instance isReduced_closureBC [IsAlgClosed k] [LocallyOfFiniteType q] (v : Y) :
    IsReduced (closureBC ψ q v) :=
  isReduced_baseChange ψ (closureι v ≫ q)

include H in
/-- **The preimage of an irreducible closed subset is irreducible**: it is the support of the
integral scheme `closure{v} ×_k K` (`irreducibleSpace_baseChange`). -/
theorem isIrreducible_preimage_closure [IsAlgClosed k] [LocallyOfFiniteType q] (v : Y) :
    IsIrreducible (π ⁻¹' closure {v}) := by
  have : IrreducibleSpace (closureBC ψ q v) := irreducibleSpace_baseChange ψ (closureι v ≫ q)
  rw [← range_closureBCι ψ q H v, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    (closureBCι ψ q H v).continuous.continuousOn

include H in
/-- **Irreducible components of `P` are preimages of irreducible components of `Y`.** -/
theorem exists_eq_preimage_of_mem_irreducibleComponents [IsAlgClosed k] [LocallyOfFiniteType q]
    {Z : Set P} (hZ : Z ∈ irreducibleComponents P) :
    ∃ v : Y, closure {v} ∈ irreducibleComponents Y ∧ Z = π ⁻¹' closure {v} := by
  have hirr : IsIrreducible (closure (π '' Z)) := (hZ.1.image _ π.continuous.continuousOn).closure
  obtain ⟨T, hT, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  obtain ⟨v, hv⟩ := QuasiSober.sober hT.1 (isClosed_of_mem_irreducibleComponents T hT)
  have hv' : closure {v} = T := hv
  subst hv'
  refine ⟨v, hT, ?_⟩
  have hZsub : Z ⊆ π ⁻¹' closure {v} := fun x hx => hsub (subset_closure ⟨x, hx, rfl⟩)
  exact hZsub.antisymm (hZ.2 (isIrreducible_preimage_closure ψ q H v) hZsub)

/-- The kernel of the closed immersion `closure{v} ×_k K → P` is the vanishing ideal of
`π⁻¹(closure {v})`. -/
theorem ker_closureBCι [IsAlgClosed k] [LocallyOfFiniteType q] (v : Y) :
    (closureBCι ψ q H v).ker = Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩ := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext x
  simp only [Closeds.coe_closure, Closeds.coe_top, Set.image_univ, range_closureBCι ψ q H v,
    (isClosed_closure.preimage π.continuous).closure_eq]
  rfl

/-- **The reduced induced subscheme on `π⁻¹(closure {v})` is `closure{v} ×_k K`.** -/
def closureBCIso [IsAlgClosed k] [LocallyOfFiniteType q] (v : Y) :
    closureBC ψ q v ≅ (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subscheme :=
  asIso (closureBCι ψ q H v).toImage ≪≫
    { hom := Scheme.IdealSheafData.inclusion (ker_closureBCι ψ q H v).ge
      inv := Scheme.IdealSheafData.inclusion (ker_closureBCι ψ q H v).le
      hom_inv_id := by
        rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id]
      inv_hom_id := by
        rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id] }

@[reassoc (attr := simp)]
theorem closureBCIso_hom_ι [IsAlgClosed k] [LocallyOfFiniteType q] (v : Y) :
    (closureBCIso ψ q H v).hom ≫ (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subschemeι =
        closureBCι ψ q H v := by
  simp [closureBCIso, Scheme.IdealSheafData.inclusion_subschemeι]

include H in
/-- **The arithmetic genus of a reduced closure is invariant under `K / k`** (blueprint
`lem:sm-bdu-components-base-change`): `p_a(π⁻¹(closure {v})_red) = p_a(closure{v})`. -/
theorem arithmeticGenus_preimage_closure [IsAlgClosed k] [LocallyOfFiniteType q] [CompactSpace Y]
    (v : Y)
    [CompactSpace (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subscheme]
    [IsAffineHom (pullback.diagonal (terminal.from (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subscheme))]
    [IsAffineHom (pullback.diagonal (terminal.from (closureScheme v)))] :
    arithmeticGenus (Scheme.IdealSheafData.vanishingIdeal
        ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subscheme
        (structureCoeff ((Scheme.IdealSheafData.vanishingIdeal
          ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subschemeι ≫ snd)) =
      arithmeticGenus (closureScheme v) (structureCoeff (closureι v ≫ q)) := by
  unfold arithmeticGenus
  congr 1
  have he : (closureBCIso ψ q H v).hom ≫ (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subschemeι ≫ snd =
        bcSnd ψ (closureι v ≫ q) := by
    rw [closureBCIso_hom_ι_assoc, closureBCι_snd]
  rw [← BlowDown.eulerChar_eq_of_iso _ _ (closureBCIso ψ q H v) he]
  exact eulerChar_baseChange_field ψ (closureι v ≫ q)

end BaseChange

end DeJongAlterations.StableModification.BlowDown.NumericalDescent
