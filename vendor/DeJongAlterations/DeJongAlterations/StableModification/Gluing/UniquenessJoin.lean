/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45F)
-/
import DeJongAlterations.StableModification.Gluing.UniquenessValSetup
import DeJongAlterations.StableModification.Gluing.RefinementProjective
import DeJongAlterations.StableModification.Projectivity.Reduction
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricNormalization
import DeJongAlterations.Geometry.AffineBlowupBirational

/-!
# The join of two modifications and the normalization of the base

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Thm 1.2 over a valuation ring (§4.5, T:3233–3266, and Cor. 4.4.3 (1), T:3135–3149; `PLAN-T5.md`
§2.2 step 11): two stable modifications `β₁ : C₁ → C`, `β₂ : C₂ → C` are compared through a
curve dominating both, a semi-stable model of their *join* `J ⊆ C₁ ×_C C₂` (the closure of the
part of the fibre product over a dense open `U` of `C` over which both are isomorphisms), and
Temkin's Corollary 4.4.3 (1) is applied over the normalization `N` of `C` (it needs a normal
base).

## The join

For an open `U ⊆ C` over which `β₁, β₂` are isomorphisms, `pr₁ : C₁ ×_C C₂ → C₁` is an
isomorphism over `β₁⁻¹(U)` (base change), so `pr₁⁻¹(β₁⁻¹ U)` is irreducible with generic point
`ξ` over the generic point of `C₁` (`joinPoint`). The join is the reduced closure
`J = closure {ξ}` (`join`, lane T44A3's `ClosureComponent.closureScheme`):

* `isIso_joinι_restrict`: `J → C₁ ×_C C₂` is an isomorphism over `pr₁⁻¹(β₁⁻¹ U)` (a surjective
  closed immersion onto a reduced scheme);
* `isModification_joinFst`, `isModification_joinSnd`: `J → C₁` and `J → C₂` are modifications;
* `isProjectiveOver_join`: `J` is projective over the base when `C₁, C₂` are.

## Lifting to the normalization

* `liftToNormalization`: for `π = a ≫ b : X → X' → Y` with `a.fromNormalization` an isomorphism
  (e.g. `X'` normal and `a` birational, lane T44A's `isIso_fromNormalization_of_isNormalScheme`),
  `b` lifts to the normalization `Nor_X(Y)` of `Y` in `X`, compatibly with `π.toNormalization`
  (`liftToNormalization_fromNormalization`, `comp_liftToNormalization`). This is the universal
  property of the normalization of `C` used for the base `N` of Corollary 4.4.3 (1).

Blueprint: `sm-gluing-uniqueness.tex`, `lem:sm-gu-join`, `lem:sm-gu-normalization`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.UniquenessVal

open BlowDown.ClosureComponent (closureScheme closureι closurePt closureι_closurePt range_closureι)

set_option backward.isDefEq.respectTransparency false

section Restrict

variable {X Y : Scheme.{u}}

/-- A morphism which is an isomorphism over `W` hits every point of `W`. -/
theorem exists_eq_of_isIso_restrict (f : X ⟶ Y) (W : Y.Opens) [IsIso (f ∣_ W)] {y : Y}
    (hy : y ∈ W) : ∃ x, f x = y := by
  refine ⟨(inv (f ∣_ W) ⟨y, hy⟩).1, ?_⟩
  have h := congrArg (fun g => (g ⟨y, hy⟩ : Y))
    (show inv (f ∣_ W) ≫ (f ∣_ W) ≫ W.ι = W.ι by rw [IsIso.inv_hom_id_assoc])
  rw [morphismRestrict_ι] at h
  exact h

/-- A morphism to an irreducible scheme which is an isomorphism over a nonempty open is dominant. -/
theorem isDominant_of_isIso_restrict (f : X ⟶ Y) [IrreducibleSpace Y] (W : Y.Opens)
    (hW : (W : Set Y).Nonempty) [IsIso (f ∣_ W)] : IsDominant f := by
  refine ⟨Dense.mono (fun y hy => exists_eq_of_isIso_restrict f W hy) ?_⟩
  exact W.isOpen.dense hW

/-- **A proper morphism of integral schemes which is an isomorphism over a nonempty open is a
modification.** -/
theorem isModification_of_isIso_restrict (f : X ⟶ Y) [IsProper f] [IsIntegral X] [IsIntegral Y]
    (W : Y.Opens) (hW : (W : Set Y).Nonempty) [IsIso (f ∣_ W)] : IsModification f := by
  have := isDominant_of_isIso_restrict f W hW
  exact
    { toIsProper := inferInstance
      sourceIntegral := inferInstance
      targetIntegral := inferInstance
      birational := birationalOver_id_of_isIso_morphismRestrict f W hW }

end Restrict

section Join

variable {C C₁ C₂ : Scheme.{u}} (β₁ : C₁ ⟶ C) (β₂ : C₂ ⟶ C) (U : C.Opens)

/-- The part of `C₁ ×_C C₂` over `β₁⁻¹(U)`. -/
abbrev joinOpen : (pullback β₁ β₂).Opens := pullback.fst β₁ β₂ ⁻¹ᵁ (β₁ ⁻¹ᵁ U)

/-- `pr₁ : C₁ ×_C C₂ → C₁` is an isomorphism over `β₁⁻¹(U)` if `β₂` is one over `U`. -/
theorem isIso_fst_restrict [IsIso (β₂ ∣_ U)] : IsIso (pullback.fst β₁ β₂ ∣_ (β₁ ⁻¹ᵁ U)) :=
  Limits.SpreadModification.isIso_morphismRestrict_of_isPullback'
    (IsPullback.of_hasPullback β₁ β₂).flip U

/-- `pr₂ : C₁ ×_C C₂ → C₂` is an isomorphism over `β₂⁻¹(U)` if `β₁` is one over `U`. -/
theorem isIso_snd_restrict [IsIso (β₁ ∣_ U)] : IsIso (pullback.snd β₁ β₂ ∣_ (β₂ ⁻¹ᵁ U)) :=
  Limits.SpreadModification.isIso_morphismRestrict_of_isPullback'
    (IsPullback.of_hasPullback β₁ β₂) U

theorem snd_preimage_eq :
    pullback.snd β₁ β₂ ⁻¹ᵁ (β₂ ⁻¹ᵁ U) = pullback.fst β₁ β₂ ⁻¹ᵁ (β₁ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

variable [IsIntegral C₁] [IsIso (β₂ ∣_ U)] (hU : genericPoint C₁ ∈ β₁ ⁻¹ᵁ U)

/-- **The generic point of the join**: the point of `C₁ ×_C C₂` over the generic point of `C₁`
in the part over `U`. -/
def joinPoint : pullback (C := Scheme.{u}) β₁ β₂ :=
  have := isIso_fst_restrict β₁ β₂ U
  (joinOpen β₁ β₂ U).ι (inv (pullback.fst β₁ β₂ ∣_ (β₁ ⁻¹ᵁ U)) ⟨genericPoint C₁, hU⟩)

theorem joinPoint_mem : joinPoint β₁ β₂ U hU ∈ joinOpen β₁ β₂ U := by
  have := isIso_fst_restrict β₁ β₂ U
  exact (inv (pullback.fst β₁ β₂ ∣_ (β₁ ⁻¹ᵁ U)) ⟨genericPoint C₁, hU⟩).2

theorem fst_joinPoint : pullback.fst β₁ β₂ (joinPoint β₁ β₂ U hU) = genericPoint C₁ := by
  have := isIso_fst_restrict β₁ β₂ U
  have h := congrArg (fun g => (g ⟨genericPoint C₁, hU⟩ : C₁))
    (show inv (pullback.fst β₁ β₂ ∣_ (β₁ ⁻¹ᵁ U)) ≫ (pullback.fst β₁ β₂ ∣_ (β₁ ⁻¹ᵁ U)) ≫
      (β₁ ⁻¹ᵁ U).ι = (β₁ ⁻¹ᵁ U).ι by rw [IsIso.inv_hom_id_assoc])
  rw [morphismRestrict_ι] at h
  exact h

/-- The part of the fibre product over `U` lies in the closure of `joinPoint`. -/
theorem joinOpen_subset_closure :
    (joinOpen β₁ β₂ U : Set (pullback (C := Scheme.{u}) β₁ β₂)) ⊆ closure {joinPoint β₁ β₂ U hU} := by
  have := isIso_fst_restrict β₁ β₂ U
  intro y hy
  rw [← specializes_iff_mem_closure]
  set F := pullback.fst β₁ β₂ ∣_ (β₁ ⁻¹ᵁ U)
  let y' : (joinOpen β₁ β₂ U).toScheme := ⟨y, hy⟩
  have h1 : (⟨genericPoint C₁, hU⟩ : (β₁ ⁻¹ᵁ U).toScheme) ⤳ F y' := by
    rw [← (β₁ ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing.specializes_iff]
    exact (genericPoint_spec C₁).specializes (Set.mem_univ _)
  have h2 := h1.map (inv F).continuous
  have h3 : (inv F) (F y') = y' := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  rw [h3] at h2
  exact h2.map (joinOpen β₁ β₂ U).ι.continuous

/-- **The join** `J ⊆ C₁ ×_C C₂`: the reduced closure of `joinPoint`. -/
abbrev join : Scheme.{u} := closureScheme (joinPoint β₁ β₂ U hU)

/-- The closed immersion `J → C₁ ×_C C₂`. -/
abbrev joinι : join β₁ β₂ U hU ⟶ pullback β₁ β₂ := closureι (joinPoint β₁ β₂ U hU)

/-- `J → C₁`. -/
abbrev joinFst : join β₁ β₂ U hU ⟶ C₁ := joinι β₁ β₂ U hU ≫ pullback.fst β₁ β₂

/-- `J → C₂`. -/
abbrev joinSnd : join β₁ β₂ U hU ⟶ C₂ := joinι β₁ β₂ U hU ≫ pullback.snd β₁ β₂

theorem joinFst_comp : joinFst β₁ β₂ U hU ≫ β₁ = joinSnd β₁ β₂ U hU ≫ β₂ := by
  simp only [Category.assoc, pullback.condition]

/-- **The join is an isomorphism onto the fibre product over `U`**: `J → C₁ ×_C C₂` restricted
over `pr₁⁻¹(β₁⁻¹ U)` is a surjective closed immersion onto a reduced scheme. -/
theorem isIso_joinι_restrict : IsIso (joinι β₁ β₂ U hU ∣_ joinOpen β₁ β₂ U) := by
  have := isIso_fst_restrict β₁ β₂ U
  have : IsReduced (joinOpen β₁ β₂ U).toScheme :=
    isReduced_of_isOpenImmersion (pullback.fst β₁ β₂ ∣_ (β₁ ⁻¹ᵁ U))
  have : Surjective (joinι β₁ β₂ U hU ∣_ joinOpen β₁ β₂ U) := by
    refine ⟨fun y => ?_⟩
    have hy : y.1 ∈ Set.range (joinι β₁ β₂ U hU) := by
      rw [range_closureι]
      exact joinOpen_subset_closure β₁ β₂ U hU y.2
    obtain ⟨z, hz⟩ := hy
    have hz' : z ∈ joinι β₁ β₂ U hU ⁻¹ᵁ joinOpen β₁ β₂ U := by
      change joinι β₁ β₂ U hU z ∈ joinOpen β₁ β₂ U
      rw [hz]
      exact y.2
    refine ⟨⟨z, hz'⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hz
  exact isIso_of_isClosedImmersion_of_surjective _

instance : IsIntegral (join β₁ β₂ U hU) :=
  BlowDown.ClosureComponent.isIntegral_closureScheme _

theorem isIso_joinFst_restrict : IsIso (joinFst β₁ β₂ U hU ∣_ (β₁ ⁻¹ᵁ U)) := by
  have := isIso_fst_restrict β₁ β₂ U
  have := isIso_joinι_restrict β₁ β₂ U hU
  rw [morphismRestrict_comp]
  infer_instance

theorem isIso_joinSnd_restrict [IsIso (β₁ ∣_ U)] : IsIso (joinSnd β₁ β₂ U hU ∣_ (β₂ ⁻¹ᵁ U)) := by
  have := isIso_snd_restrict β₁ β₂ U
  have : IsIso (joinι β₁ β₂ U hU ∣_ (pullback.snd β₁ β₂ ⁻¹ᵁ (β₂ ⁻¹ᵁ U))) := by
    rw [snd_preimage_eq]
    exact isIso_joinι_restrict β₁ β₂ U hU
  rw [morphismRestrict_comp]
  infer_instance

/-- **`J → C₁` is a modification.** -/
theorem isModification_joinFst [IsProper β₂] : IsModification (joinFst β₁ β₂ U hU) := by
  have := isIso_joinFst_restrict β₁ β₂ U hU
  exact isModification_of_isIso_restrict _ (β₁ ⁻¹ᵁ U) ⟨_, hU⟩

/-- **`J → C₂` is a modification.** -/
theorem isModification_joinSnd [IsIntegral C₂] [IsProper β₁] [IsIso (β₁ ∣_ U)] :
    IsModification (joinSnd β₁ β₂ U hU) := by
  have := isIso_joinSnd_restrict β₁ β₂ U hU
  refine isModification_of_isIso_restrict _ (β₂ ⁻¹ᵁ U) ⟨pullback.snd β₁ β₂
    (joinPoint β₁ β₂ U hU), ?_⟩
  have h : joinPoint β₁ β₂ U hU ∈ pullback.snd β₁ β₂ ⁻¹ᵁ (β₂ ⁻¹ᵁ U) := by
    rw [snd_preimage_eq]
    exact joinPoint_mem β₁ β₂ U hU
  exact h

/-- **The join is projective** over the base `V` when `C₁` and `C₂` are (Segre; `J` is closed in
`C₁ ×_C C₂ ⊆ C₁ ×_V ℙⁿ_V`). -/
theorem isProjectiveOver_join {R : Type u} [CommRing R] (φ : C ⟶ Spec (.of R)) [IsSeparated φ]
    (hp₁ : IsProjectiveOver (β₁ ≫ φ)) (hp₂ : IsProjectiveOver (β₂ ≫ φ)) :
    IsProjectiveOver (joinFst β₁ β₂ U hU ≫ β₁ ≫ φ) := by
  have h₂ : DeJong.IsRelativelyProjective φ β₂ :=
    Projectivity.isRelativelyProjective_of_isProjectiveOver φ β₂ hp₂
  have hfst : DeJong.IsRelativelyProjective (β₁ ≫ φ) (pullback.fst β₁ β₂) :=
    Gluing.IsRelativelyProjective.pullback_fst h₂ β₁
  have hj : DeJong.IsRelativelyProjective (β₁ ≫ φ) (joinFst β₁ β₂ U hU) :=
    Projectivity.isRelativelyProjective_closedImmersion_comp hfst _
  exact DeJong.IsRelativelyProjective.isProjectiveOver hp₁ hj

end Join

section Lift

variable {X X' Y : Scheme.{u}} (π : X ⟶ Y) [QuasiCompact π] [QuasiSeparated π] (a : X ⟶ X')
  (b : X' ⟶ Y) (H : a ≫ b = π)

/-- The factorization `X → Nor_X(Y) ×_Y X' → X'` of `a`. -/
abbrev liftAux : X ⟶ pullback π.fromNormalization b :=
  pullback.lift π.toNormalization a (by rw [π.toNormalization_fromNormalization, H])

theorem liftAux_snd : a = liftAux π a b H ≫ pullback.snd π.fromNormalization b :=
  (pullback.lift_snd _ _ _).symm

/-- **Lifting to the normalization**: for `π = a ≫ b` with `a.fromNormalization` an isomorphism,
the morphism `b : X' → Y` lifts to the normalization `Nor_X(Y)` of `Y` in `X`. It is
`X' ≅ a.normalization → Nor_X(Y)`, the universal property of `a.normalization` applied to the
integral `Nor_X(Y) ×_Y X' → X'`. -/
def liftToNormalization [QuasiCompact a] [QuasiSeparated a] [IsIso a.fromNormalization] :
    X' ⟶ π.normalization :=
  inv a.fromNormalization ≫
    a.normalizationDesc (liftAux π a b H) (pullback.snd π.fromNormalization b)
      (liftAux_snd π a b H) ≫ pullback.fst _ _

@[reassoc]
theorem liftToNormalization_fromNormalization [QuasiCompact a] [QuasiSeparated a]
    [IsIso a.fromNormalization] :
    liftToNormalization π a b H ≫ π.fromNormalization = b := by
  rw [liftToNormalization, Category.assoc, Category.assoc, pullback.condition,
    Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]

@[reassoc]
theorem comp_liftToNormalization [QuasiCompact a] [QuasiSeparated a]
    [IsIso a.fromNormalization] :
    a ≫ liftToNormalization π a b H = π.toNormalization := by
  have h : a ≫ inv a.fromNormalization = a.toNormalization := by
    rw [IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]
  rw [liftToNormalization, ← Category.assoc, h, ← Category.assoc,
    Scheme.Hom.toNormalization_normalizationDesc, pullback.lift_fst]

end Lift

section Normalization

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C Cb C₁ C₂ : Scheme.{u}} (φ : C ⟶ Spec (.of V))

/-- **The normalization of the base dominated by a common normal model** (`PLAN-T5.md` §2.2
step 11; the base of Temkin's Corollary 4.4.3 (1) must be normal). Let `Cb` be integral and
normal with modifications `hᵢ : Cb → Cᵢ` to normal integral `Cᵢ` and `h₁ ≫ β₁ = h₂ ≫ β₂ : Cb → C`
an η-modification projective over `V`. The normalization `N = Nor_{Cb}(C)` of `C` in `Cb`
(lane T44B's blow-down API `BlowDown.isEtaModification_blowDown_base`,
`BlowDown.isProjectiveOver_blowDown`) is normal, `N → C` is an η-modification projective over
`V`, and both `βᵢ` lift to `N` (`liftToNormalization`), compatibly with `Cb → N`. -/
theorem exists_normalization_lifts [IsIntegral C] [Flat φ] [IsSeparated φ]
    [LocallyOfFinitePresentation φ] (hφ : IsProjectiveOver φ) [IsIntegral Cb]
    (hb : IsNormalScheme Cb) [IsIntegral C₁] [IsIntegral C₂] (h₁ : Cb ⟶ C₁) (h₂ : Cb ⟶ C₂)
    [IsModification h₁] [IsModification h₂] (β₁ : C₁ ⟶ C) (β₂ : C₂ ⟶ C) [IsProper β₁]
    (hn₁ : IsNormalScheme C₁) (hn₂ : IsNormalScheme C₂) (hcomm : h₁ ≫ β₁ = h₂ ≫ β₂)
    [Flat (h₁ ≫ β₁ ≫ φ)] (hη : Curves.IsEtaModification (h₁ ≫ β₁) φ)
    (hp : IsProjectiveOver (h₁ ≫ β₁ ≫ φ)) :
    ∃ (N : Scheme.{u}) (_ : IsIntegral N) (ν : N ⟶ C) (f₁ : C₁ ⟶ N) (f₂ : C₂ ⟶ N),
      IsNormalScheme N ∧ Curves.IsEtaModification ν φ ∧ IsProjectiveOver (ν ≫ φ) ∧
        f₁ ≫ ν = β₁ ∧ f₂ ≫ ν = β₂ ∧ h₁ ≫ f₁ = h₂ ≫ f₂ := by
  set g := h₁ ≫ β₁ with hg
  have : IsSeparated (𝟙 C ≫ φ) := by rw [Category.id_comp]; infer_instance
  have : LocallyOfFinitePresentation (𝟙 C ≫ φ) := by rw [Category.id_comp]; infer_instance
  have : Flat (g ≫ φ) := by rw [hg, Category.assoc]; infer_instance
  have hP : IsProjectiveOver (𝟙 C ≫ φ) := by rw [Category.id_comp]; exact hφ
  have hY : IsProjectiveOver (g ≫ φ) := by rw [hg, Category.assoc]; exact hp
  have hgg : g ≫ 𝟙 C = g := Category.comp_id g
  have hνη := BlowDown.isEtaModification_blowDown_base φ (𝟙 C) g g hP hgg hY hη
  have hνp := BlowDown.isProjectiveOver_blowDown φ (𝟙 C) g g hP hgg hY
  rw [Category.comp_id] at hνη hνp
  have : IsIso h₁.fromNormalization :=
    BlowDown.isIso_fromNormalization_of_isNormalScheme h₁ hn₁ IsModification.birational
  have : IsIso h₂.fromNormalization :=
    BlowDown.isIso_fromNormalization_of_isNormalScheme h₂ hn₂ IsModification.birational
  refine ⟨g.normalization, inferInstance, g.fromNormalization,
    liftToNormalization g h₁ β₁ rfl, liftToNormalization g h₂ β₂ hcomm.symm,
    BlowDown.isNormalScheme_normalization g hb, hνη, hνp,
    liftToNormalization_fromNormalization _ _ _ _, liftToNormalization_fromNormalization _ _ _ _,
    ?_⟩
  rw [comp_liftToNormalization, comp_liftToNormalization]

end Normalization

end DeJongAlterations.StableModification.Gluing.UniquenessVal
