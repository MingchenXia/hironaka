/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusReduced

/-!
# Topological preliminaries for contractions of curves

Two kinds of facts used in the scheme-level form of Temkin's Corollary B.2
(M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4435–4467):

* **Generic points.** In a quasi-sober `T₀` space a point is the generic point of an irreducible
  component iff it has no proper generization (`mem_genericPoints_iff`). In a noetherian space of
  dimension `≤ 1`, a closed set containing no generic point is finite
  (`finite_of_isClosed_of_disjoint_genericPoints`).
* **Morphisms which are isomorphisms over an open.** If `f : C' ⟶ C` restricts to an isomorphism
  `f⁻¹(U) ≅ U`, then `f` is injective on `f⁻¹(U)`, surjective onto `U`, preserves and reflects
  specialization and generic points there (`specializes_iff_of_isIso_morphismRestrict`,
  `mem_genericPoints_iff_of_isIso_morphismRestrict`), induces isomorphisms of residue fields
  (`isIso_residueFieldMap_of_isIso_morphismRestrict`), and is an isomorphism over every open
  `V ⊆ U` (`isIso_morphismRestrict_of_le`, `isIso_app_of_le`, `isAffineOpen_preimage_of_le`).

Blueprint: `sm-curves-fields-genus-reduced.tex`, `lem:sm-generic-points-specialization`,
`lem:sm-closed-without-generic-points`, `lem:sm-iso-over-open`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

set_option autoImplicit false

universe u

section GenericPoints

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

/-- **Generic points are the points without proper generization.** -/
theorem mem_genericPoints_iff (η : X) : η ∈ genericPoints X ↔ ∀ ξ : X, ξ ⤳ η → ξ = η := by
  constructor
  · intro hη ξ hξ
    have h1 : closure {η} ⊆ closure {ξ} := specializes_iff_closure_subset.1 hξ
    have h2 : closure {ξ} ⊆ closure {η} := hη.2 isIrreducible_singleton.closure h1
    exact ((specializes_iff_closure_subset.2 h2).antisymm hξ).eq.symm
  · intro h
    let T := irreducibleComponent η
    have hT : T ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents η
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hT.1 (isClosed_of_mem_irreducibleComponents T hT)
    have hξη : ξ ⤳ η := by
      rw [specializes_iff_mem_closure, hξ.def]
      exact mem_irreducibleComponent
    have := h ξ hξη
    change closure {η} ∈ irreducibleComponents X
    rw [← this, hξ.def]
    exact hT

/-- A point which is not generic has a proper generization. -/
theorem exists_ne_specializes_of_not_mem_genericPoints {η : X} (hη : η ∉ genericPoints X) :
    ∃ ξ : X, ξ ⤳ η ∧ ξ ≠ η := by
  rw [mem_genericPoints_iff] at hη
  push Not at hη
  exact hη

/-- **In a noetherian space of dimension `≤ 1`, a closed set without generic points is finite.**
Each irreducible component of such a set is a point: its generic point has a proper generization,
and a further proper specialization would give a chain of length two. -/
theorem finite_of_isClosed_of_disjoint_genericPoints [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {F : Set X} (hF : IsClosed F)
    (hgen : ∀ η ∈ F, η ∉ genericPoints X) : F.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  refine Set.Finite.sUnion hSf fun t ht => ?_
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  have hζt : ζ ∈ t := hζ.mem
  obtain ⟨ξ, hξζ, hne⟩ := exists_ne_specializes_of_not_mem_genericPoints
    (hgen ζ (Set.mem_sUnion_of_mem hζt ht))
  refine Set.Subsingleton.finite fun w hw w' hw' => ?_
  have key : ∀ v ∈ t, v = ζ := by
    intro v hv
    by_contra hvζ
    have hζv : ζ ⤳ v := by
      rw [specializes_iff_mem_closure, hζ.def]
      exact hv
    let a : IrreducibleCloseds X := ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
    let b : IrreducibleCloseds X := ⟨closure {ζ}, isIrreducible_singleton.closure, isClosed_closure⟩
    let c : IrreducibleCloseds X := ⟨closure {ξ}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hab : a < b := by
      refine lt_of_le_of_ne (show closure {v} ⊆ closure {ζ} from
        specializes_iff_closure_subset.1 hζv) fun h => hvζ ?_
      have h' : closure {v} = closure {ζ} := congrArg IrreducibleCloseds.carrier h
      exact (inseparable_iff_closure_eq.2 h').eq
    have hbc : b < c := by
      refine lt_of_le_of_ne (show closure {ζ} ⊆ closure {ξ} from
        specializes_iff_closure_subset.1 hξζ) fun h => hne ?_
      have h' : closure {ζ} = closure {ξ} := congrArg IrreducibleCloseds.carrier h
      exact (inseparable_iff_closure_eq.2 h').eq.symm
    rcases (Order.krullDim_le_one_iff.1 hdim) b with hmin | hmax
    · exact hmin.not_lt hab
    · exact hmax.not_lt hbc
  rw [key w hw, key w' hw']

end GenericPoints

section IsoOverOpen

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (U : C.Opens) [IsIso (f ∣_ U)]

omit [IsIso (f ∣_ U)] in
lemma morphismRestrict_apply_val (y : C') (hy : f y ∈ U) :
    ((f ∣_ U) ⟨y, hy⟩).1 = f y :=
  morphismRestrict_base_coe f U ⟨y, hy⟩

/-- `f` is injective on `f⁻¹(U)`. -/
theorem injOn_of_isIso_morphismRestrict {y z : C'} (hy : f y ∈ U) (hz : f z ∈ U)
    (h : f y = f z) : y = z := by
  have : (f ∣_ U) ⟨y, hy⟩ = (f ∣_ U) ⟨z, hz⟩ := Subtype.ext (by
    rw [morphismRestrict_apply_val, morphismRestrict_apply_val, h])
  exact congrArg Subtype.val ((f ∣_ U).homeomorph.injective this)

/-- `f` maps `f⁻¹(U)` onto `U`. -/
theorem exists_eq_of_isIso_morphismRestrict {y : C} (hy : y ∈ U) : ∃ y' : C', f y' = y := by
  obtain ⟨y', hy'⟩ := (f ∣_ U).homeomorph.surjective ⟨y, hy⟩
  refine ⟨y'.1, ?_⟩
  have := congrArg Subtype.val hy'
  rwa [Scheme.Hom.homeomorph_apply, morphismRestrict_base_coe] at this

/-- `f` preserves and reflects specialization on `f⁻¹(U)`. -/
theorem specializes_iff_of_isIso_morphismRestrict {y z : C'} (hy : f y ∈ U) (hz : f z ∈ U) :
    f y ⤳ f z ↔ y ⤳ z := by
  constructor
  · intro h
    have h1 : (f ∣_ U) ⟨y, hy⟩ ⤳ (f ∣_ U) ⟨z, hz⟩ := by
      rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff]
      change ((f ∣_ U) ⟨y, hy⟩).1 ⤳ ((f ∣_ U) ⟨z, hz⟩).1
      rw [morphismRestrict_apply_val, morphismRestrict_apply_val]
      exact h
    have h2 := (f ∣_ U).homeomorph.isInducing.specializes_iff.1 h1
    have h3 := h2.map (f ⁻¹ᵁ U).ι.continuous
    exact h3
  · exact fun h => h.map f.continuous

/-- `f` preserves and reflects generic points on `f⁻¹(U)`. -/
theorem mem_genericPoints_iff_of_isIso_morphismRestrict {y : C'} (hy : f y ∈ U) :
    y ∈ genericPoints C' ↔ f y ∈ genericPoints C := by
  rw [mem_genericPoints_iff, mem_genericPoints_iff]
  constructor
  · intro h ξ hξ
    have hξU : ξ ∈ U := hξ.mem_open U.2 hy
    obtain ⟨ξ', rfl⟩ := exists_eq_of_isIso_morphismRestrict f U hξU
    rw [h ξ' ((specializes_iff_of_isIso_morphismRestrict f U hξU hy).1 hξ)]
  · intro h ξ hξ
    have hξU : f ξ ∈ U := (hξ.map f.continuous).mem_open U.2 hy
    exact injOn_of_isIso_morphismRestrict f U hξU hy (h _ (hξ.map f.continuous))

set_option backward.isDefEq.respectTransparency.types false in
/-- `f` induces isomorphisms of stalks on `f⁻¹(U)`. -/
theorem isIso_stalkMap_of_isIso_morphismRestrict (y : C') (hy : f y ∈ U) :
    IsIso (f.stalkMap y) := by
  have : IsOpenImmersion (f ∣_ U) := inferInstance
  have : IsIso ((f ∣_ U).stalkMap ⟨y, hy⟩) := inferInstance
  have e := morphismRestrictStalkMap f U ⟨y, hy⟩
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff e).1 this

/-- `f` induces isomorphisms of residue fields on `f⁻¹(U)`. -/
theorem isIso_residueFieldMap_of_isIso_morphismRestrict (y : C') (hy : f y ∈ U) :
    IsIso (f.residueFieldMap y) := by
  have := isIso_stalkMap_of_isIso_morphismRestrict f U y hy
  exact (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

/-- `f` is an isomorphism over every open `V ⊆ U`. -/
theorem isIso_morphismRestrict_of_le {V : C.Opens} (hV : V ≤ U) : IsIso (f ∣_ V) := by
  let W : (U : Scheme.{u}).Opens := U.ι ⁻¹ᵁ V
  have hW : U.ι ''ᵁ W = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hV
  have h1 : IsIso (f ∣_ U ∣_ W) := inferInstance
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U W)).1 h1
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictEq f hW)).1 h2

/-- `f⁻¹(V)` is affine for every affine open `V ⊆ U`. -/
theorem isAffineOpen_preimage_of_le {V : C.Opens} (hV : V ≤ U) (hVa : IsAffineOpen V) :
    IsAffineOpen (f ⁻¹ᵁ V) := by
  have := isIso_morphismRestrict_of_le f U hV
  have : IsAffine V := hVa
  exact IsAffine.of_isIso (f ∣_ V)

/-- `f^♯ : Γ(V, 𝒪_C) → Γ(f⁻¹V, 𝒪_{C'})` is an isomorphism for every open `V ⊆ U`. -/
theorem isIso_app_of_le {V : C.Opens} (hV : V ≤ U) : IsIso (f.app V) := by
  have := isIso_morphismRestrict_of_le f U hV
  have h : IsIso ((f ∣_ V).app ⊤) := inferInstance
  change IsIso ((f ∣_ V).appTop) at h
  rw [morphismRestrict_appTop] at h
  have hV' : V.ι ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hiso : IsIso (C'.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op) := by
    rw [eqToHom_op, eqToHom_map]
    infer_instance
  have h' := @IsIso.of_isIso_comp_right _ _ _ _ _ (f.app (V.ι ''ᵁ ⊤)) _ hiso h
  rw [hV'] at h'
  exact h'

end IsoOverOpen

end DeJongAlterations.StableModification.CurvesField.Genus
