/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL-GLOBAL)
-/
import DeJongAlterations.StableModification.Perfection.GlobalAlgebra
import DeJongAlterations.StableModification.Perfection.GlobalChart

/-!
# Local rings of the generic fibre after a purely inseparable base change

Blueprint chapter `sm-dj-perfection-global`, node `lem:sm-dj-perfection-global-local-rings` (new
route, not in de Jong 1996; this is step (d) of the route of `thm:sm-dj-perfection-global`).

Let `X` be an integral scheme, `M` a field containing `K(X)` and a field `K`, `E ⊆ M` an
algebraic extension of `K`, and `L = K(X)(E) ⊆ M`, finite and purely inseparable over `K(X)`.
For a nonempty affine open `U ⊆ X` let `A_U = K[Γ(X, U)] ⊆ M` (`chartAlgebra`) and let
`B_E(A_U) ⊆ M` be the image of the normalization of `E ⊗_K A_U` (PL's
`normalizationImage (chartAlgebra K M U) E`). Let `X₁ = normalization X L` and let `x₁ ∈ X₁` lie in
the chart `Spec C_U` of `U`, `C_U` the integral closure of `Γ(X, U)` in `L`.

* `closureRing_mem_normalizationImage`: `C_U ⊆ B_E(A_U)`.
* `normalizationImage_subset_range` (**`B_E(A_U) ⊆ O_{X₁,x₁}`**): if the image `T` of the local
  ring `O_{X₁,x₁}` in `M` contains `E` (which is the case when `x₁` lies over the generic point
  of the base, see `Perfection/Global.lean`), then it contains `B_E(A_U)`. Indeed `T ⊇ C_U` and
  `T ⊇ E` contain `A_U`, every element of `B_E(A_U) ⊆ L = Frac C_U` is a fraction of elements of
  `T` integral over `T`, and `T ≅ O_{X₁,x₁}` is integrally closed (`X₁` is normal).
* `exists_mul_mem_normalizationImage`: every element of `T` is `b / c` with `b, c ∈ C_U` and `c`
  a unit of `T` (Codex's charts: `T = (C_U)_P`). Together with the previous point, `T` is a
  localization of `B_E(A_U)` (`GlobalAlgebra.isLocalization_of_le`).
* `chartIdeal`: for a point `x ∈ U` whose local ring contains `K`, the contraction to `A_U` of
  the maximal ideal of the image of `O_{X,x}` in `M`; `chartIdeal_ne_bot` for `x` not the generic
  point; `isUnit_of_isUnit_stalkToAmbient`: units of `O_{X₁,x₁}` in `A_U` are units of
  `O_{X,x}`, `x` the image of `x₁` (the local ring map is local).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Perfection

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Geometry Geometry.NormalizationInExtension

/-- An injective ring map is an isomorphism onto its range. -/
def rangeEquivOfInjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) : R ≃+* f.range :=
  RingEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩

@[simp]
theorem coe_rangeEquivOfInjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) (r : R) : (rangeEquivOfInjective f hf r : S) = f r := rfl

variable {X : Scheme.{u}} [IsIntegral X] {K M : Type u} [Field K] [Field M]
  [Algebra X.functionField M] [Algebra K M]

section ChartAlgebra

variable (M) in
/-- The ring map `Γ(X, U) → K(X) → M`. -/
def sectionsToField (U : NonemptyAffineOpen X) : Γ(X, U.1.1) →+* M :=
  (algebraMap X.functionField M).comp (algebraMap Γ(X, U.1.1) X.functionField)

variable (K M) in
/-- The `K`-subalgebra `A_U = K[Γ(X, U)]` of `M`. -/
def chartAlgebra (U : NonemptyAffineOpen X) : Subalgebra K M :=
  Algebra.adjoin K (Set.range (sectionsToField M U))

theorem sectionsToField_mem_chartAlgebra (U : NonemptyAffineOpen X) (a : Γ(X, U.1.1)) :
    sectionsToField M U a ∈ chartAlgebra K M U :=
  Algebra.subset_adjoin ⟨a, rfl⟩

/-- `A_U` lies in every subring of `M` containing the images of `K` and `Γ(X, U)`. -/
theorem chartAlgebra_le_of_subring (U : NonemptyAffineOpen X) (R : Subring M)
    (hK : ∀ c : K, algebraMap K M c ∈ R) (hΓ : ∀ a, sectionsToField M U a ∈ R) {m : M}
    (hm : m ∈ chartAlgebra K M U) : m ∈ R := by
  have hle : (chartAlgebra K M U).toSubring ≤ R := by
    rw [chartAlgebra, Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨a, rfl⟩)
    exacts [hK c, hΓ a]
  exact hle hm

/-- Every element of `K(X)` lies in `E(A_U)`: `K(X)` is the fraction field of `Γ(X, U)`. -/
theorem algebraMap_mem_baseField (U : NonemptyAffineOpen X) (E : IntermediateField K M)
    (y : X.functionField) : algebraMap X.functionField M y ∈ baseField (chartAlgebra K M U) E := by
  have : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective Γ(X, U.1.1) y
  rw [map_div₀]
  exact div_mem (subset_baseField _ E (sectionsToField_mem_chartAlgebra U a))
    (subset_baseField _ E (sectionsToField_mem_chartAlgebra U b))

variable (L : IntermediateField X.functionField M) (E : IntermediateField K M)

/-- `L = K(X)(E)` lies in `E(A_U)`. -/
theorem mem_baseField_of_mem (hL : L = IntermediateField.adjoin X.functionField (E : Set M))
    (U : NonemptyAffineOpen X) {m : M} (hm : m ∈ L) : m ∈ baseField (chartAlgebra K M U) E := by
  subst hL
  have hle : (IntermediateField.adjoin X.functionField (E : Set M)).toSubfield ≤
      (baseField (chartAlgebra K M U) E).toSubfield := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨y, rfl⟩ | he)
    · exact algebraMap_mem_baseField U E y
    · exact (baseField (chartAlgebra K M U) E).algebraMap_mem ⟨_, he⟩
  exact hle hm

/-- `E(A_U)` lies in `L` when `E ⊆ L`. -/
theorem mem_of_mem_baseField (hEL : ∀ e ∈ E, e ∈ L) (U : NonemptyAffineOpen X) {m : M}
    (hm : m ∈ baseField (chartAlgebra K M U) E) : m ∈ L := by
  have hle : (baseField (chartAlgebra K M U) E).toSubfield ≤ L.toSubfield := by
    rw [baseField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨e, rfl⟩ | ha)
    · exact hEL _ e.2
    · exact chartAlgebra_le_of_subring U L.toSubfield.toSubring
        (fun c => hEL _ (E.algebraMap_mem c)) (fun a => L.algebraMap_mem _) ha
  exact hle hm

end ChartAlgebra

section Crux

variable (L : IntermediateField X.functionField M) [FiniteDimensional X.functionField L]
  (E : IntermediateField K M)

/-- The local ring of the normalization `X₁ = normalization X L` at `x`, embedded into `M`. -/
def stalkToAmbient (x : NormalizationInExtension.normalization X L) :
    (NormalizationInExtension.normalization X L).presheaf.stalk x →+* M :=
  L.val.toRingHom.comp (stalkToField L x)

theorem stalkToAmbient_injective (x : NormalizationInExtension.normalization X L) :
    Function.Injective (stalkToAmbient L x) :=
  L.val.injective.comp (stalkToField_injective L x)

attribute [local instance] sectionsAlgebra

omit [FiniteDimensional X.functionField L] in
theorem sectionsToField_eq_closureRing (U : NonemptyAffineOpen X) (a : Γ(X, U.1.1)) :
    sectionsToField M U a = ((algebraMap Γ(X, U.1.1) (closureRing L U) a : L) : M) := rfl

variable (hL : L = IntermediateField.adjoin X.functionField (E : Set M))
  (hEL : ∀ e ∈ E, e ∈ L) (hEalg : ∀ e ∈ E, IsIntegral K e)
include hL hEalg

omit [FiniteDimensional X.functionField L] in
/-- `C_U ⊆ B_E(A_U)`. -/
theorem closureRing_mem_normalizationImage (U : NonemptyAffineOpen X) (c : closureRing L U) :
    ((c : L) : M) ∈ normalizationImage (chartAlgebra K M U) E := by
  rw [mem_range_normalizationι_iff hEalg]
  refine ⟨mem_baseField_of_mem L E hL U (c : L).2, ?_⟩
  let φ : Γ(X, U.1.1) →+* chartAlgebra K M U :=
    { toFun := fun a => ⟨_, sectionsToField_mem_chartAlgebra U a⟩
      map_one' := Subtype.ext (map_one (sectionsToField M U))
      map_mul' := fun _ _ => Subtype.ext (map_mul (sectionsToField M U) _ _)
      map_zero' := Subtype.ext (map_zero (sectionsToField M U))
      map_add' := fun _ _ => Subtype.ext (map_add (sectionsToField M U) _ _) }
  have hc : IsIntegral Γ(X, U.1.1) (c : L) := c.2
  exact hc.map_of_comp_eq φ L.val.toRingHom (RingHom.ext fun _ => rfl)

variable [IsPurelyInseparable X.functionField L]
include hEL

omit hL in
/-- **`B_E(A_U)` lies in the local ring.** If the image `T ⊆ M` of the local ring of `X₁` at a
point `x₁` of the chart `U` contains `E`, then it contains `B_E(A_U)`. -/
theorem normalizationImage_subset_range (U : NonemptyAffineOpen X)
    (P : Spec (.of (closureRing L U)))
    (hET : ∀ e ∈ E, e ∈ (stalkToAmbient L (chartInclusion X L U P)).range) {b : M}
    (hb : b ∈ normalizationImage (chartAlgebra K M U) E) :
    b ∈ (stalkToAmbient L (chartInclusion X L U P)).range := by
  set R := (stalkToAmbient L (chartInclusion X L U P)).range
  have hCR : ∀ c : closureRing L U, ((c : L) : M) ∈ R := fun c => by
    obtain ⟨t, ht⟩ := exists_stalkToField_eq L U P c
    exact ⟨t, by simp [stalkToAmbient, ht]⟩
  rw [mem_range_normalizationι_iff hEalg] at hb
  obtain ⟨hbF, hbA⟩ := hb
  have hbL : b ∈ L := mem_of_mem_baseField L E hEL U hbF
  -- `A_U ⊆ R`
  have hAR : ∀ a : chartAlgebra K M U, (a : M) ∈ R := fun a =>
    chartAlgebra_le_of_subring U R (fun c => hET _ (E.algebraMap_mem c))
      (fun a => by rw [sectionsToField_eq_closureRing L U a]; exact hCR _) a.2
  have hbR : IsIntegral R b := by
    refine isIntegral_of_range_le Subtype.val_injective ?_ hbA
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, hAR a⟩, rfl⟩
  -- `R ≅ O_{X₁,x₁}` is integrally closed
  have hnormal :=
    NormalizationInExtension.normalization_isNormalScheme (X := X) L (chartInclusion X L U P)
  have : IsIntegrallyClosed
      ((NormalizationInExtension.normalization X L).presheaf.stalk (chartInclusion X L U P)) :=
    hnormal.2
  have : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_equiv (rangeEquivOfInjective _ (stalkToAmbient_injective L _))
  -- `b` is a fraction of elements of `C_U`
  have := closureRing_isFractionRing L U
  obtain ⟨c₁, c₂, hc₂, hc⟩ := IsFractionRing.div_surjective (closureRing L U) (⟨b, hbL⟩ : L)
  have hc₂0 : ((c₂ : L) : M) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨c₂, hc₂⟩ (Subtype.ext (Subtype.ext h))
  refine mem_of_isIntegral_of_isIntegrallyClosed R hbR (hCR c₁) (hCR c₂) hc₂0 ?_
  have hc' := congrArg (fun y : L => (y : M)) hc
  simp only [IntermediateField.coe_div] at hc'
  rw [← hc']
  change ((c₁ : L) : M) / ((c₂ : L) : M) * ((c₂ : L) : M) = ((c₁ : L) : M)
  rw [div_mul_cancel₀ _ hc₂0]

omit hEL in
/-- **The local ring is a localization of `C_U`.** Every element of the image `T` of the local ring
at a point of the chart `U` is `b / c` with `b, c ∈ C_U ⊆ B_E(A_U)` and `c` a unit of `T`. -/
theorem exists_mul_mem_normalizationImage (U : NonemptyAffineOpen X)
    (P : Spec (.of (closureRing L U))) {m : M}
    (hm : m ∈ (stalkToAmbient L (chartInclusion X L U P)).range) :
    ∃ c ∈ normalizationImage (chartAlgebra K M U) E,
      (∃ v ∈ (stalkToAmbient L (chartInclusion X L U P)).range, v * c = 1) ∧
      m * c ∈ normalizationImage (chartAlgebra K M U) E := by
  obtain ⟨t, rfl⟩ := hm
  obtain ⟨c, s, hs, hcs⟩ := exists_stalkToField_mul_eq L U P t
  obtain ⟨v, hv⟩ := exists_stalkToField_mul_eq_one L U P s hs
  refine ⟨((s : L) : M), closureRing_mem_normalizationImage L E hL hEalg U s,
    ⟨stalkToAmbient L _ v, ⟨v, rfl⟩, ?_⟩, ?_⟩
  · change ((stalkToField L _ v : L) : M) * ((s : L) : M) = 1
    rw [← IntermediateField.coe_mul, hv, IntermediateField.coe_one]
  · change ((stalkToField L _ t : L) : M) * ((s : L) : M) ∈ _
    rw [← IntermediateField.coe_mul, hcs]
    exact closureRing_mem_normalizationImage L E hL hEalg U c

end Crux

section ChartIdeal

/-- The local ring `O_{X,x}` embedded into `M` through `K(X)`. -/
def stalkToAmbientBase (M : Type u) [Field M] [Algebra X.functionField M] (x : X) :
    X.presheaf.stalk x →+* M :=
  (algebraMap X.functionField M).comp (algebraMap _ X.functionField)

theorem stalkToAmbientBase_injective (x : X) :
    Function.Injective (stalkToAmbientBase M x) :=
  (algebraMap X.functionField M).injective.comp (IsFractionRing.injective _ X.functionField)

theorem sectionsToField_eq_stalkToAmbientBase (U : NonemptyAffineOpen X) {x : X} (hx : x ∈ U.1.1)
    (a : Γ(X, U.1.1)) :
    sectionsToField M U a = stalkToAmbientBase M x (X.presheaf.germ U.1.1 x hx a) := by
  simp only [sectionsToField, stalkToAmbientBase, RingHom.comp_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField]
  rfl

instance isLocalRing_stalkToAmbientBase_range (x : X) :
    IsLocalRing (stalkToAmbientBase M x).range :=
  (rangeEquivOfInjective _ (stalkToAmbientBase_injective x)).isLocalRing

variable (K) in
/-- The inclusion `A_U ⊆ O_{X,x}` inside `M`, for `x ∈ U` with `K ⊆ O_{X,x}`. -/
def chartToStalk (U : NonemptyAffineOpen X) {x : X} (hx : x ∈ U.1.1)
    (hK : ∀ c : K, algebraMap K M c ∈ (stalkToAmbientBase M x).range) :
    chartAlgebra K M U →+* (stalkToAmbientBase M x).range where
  toFun a := ⟨a, chartAlgebra_le_of_subring U _ hK
    (fun b => ⟨_, (sectionsToField_eq_stalkToAmbientBase U hx b).symm⟩) a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (K) in
/-- The ideal of `A_U` of the point `x ∈ U`: the contraction of the maximal ideal of `O_{X,x}`. -/
def chartIdeal (U : NonemptyAffineOpen X) {x : X} (hx : x ∈ U.1.1)
    (hK : ∀ c : K, algebraMap K M c ∈ (stalkToAmbientBase M x).range) :
    Ideal (chartAlgebra K M U) :=
  (maximalIdeal (stalkToAmbientBase M x).range).comap (chartToStalk K U hx hK)

theorem mem_chartIdeal (U : NonemptyAffineOpen X) {x : X} (hx : x ∈ U.1.1)
    (hK : ∀ c : K, algebraMap K M c ∈ (stalkToAmbientBase M x).range) (a : chartAlgebra K M U) :
    a ∈ chartIdeal K U hx hK ↔
      ¬ ∃ v ∈ (stalkToAmbientBase M x).range, v * (a : M) = 1 := by
  rw [chartIdeal, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨((u⁻¹ : Units _) : (stalkToAmbientBase M x).range), (u⁻¹ : Units _).1.2, ?_⟩
    have := congrArg Subtype.val (Units.inv_mul u)
    rw [hu] at this
    exact this
  · rintro ⟨v, hv, hva⟩
    exact isUnit_iff_exists_inv'.mpr ⟨⟨v, hv⟩, Subtype.ext hva⟩

instance (U : NonemptyAffineOpen X) {x : X} (hx : x ∈ U.1.1)
    (hK : ∀ c : K, algebraMap K M c ∈ (stalkToAmbientBase M x).range) :
    (chartIdeal K U hx hK).IsPrime :=
  Ideal.comap_isPrime _ _

/-- The ideal of a point which is not the generic point is nonzero: there is a section `g` on
`U` vanishing at `x` but not at the generic point. -/
theorem chartIdeal_ne_bot (U : NonemptyAffineOpen X) {x : X} (hx : x ∈ U.1.1)
    (hK : ∀ c : K, algebraMap K M c ∈ (stalkToAmbientBase M x).range)
    (hxη : x ≠ genericPoint X) : chartIdeal K U hx hK ≠ ⊥ := by
  -- the generic point avoids the closure of `x`
  let V : X.Opens := ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩
  have hηV : genericPoint X ∈ V := by
    intro h
    have hsp : x ⤳ genericPoint X := specializes_iff_mem_closure.mpr h
    exact hxη (hsp.antisymm ((genericPoint_spec X).specializes (Set.mem_univ x))).eq.symm.symm
  have hηU : genericPoint X ∈ U.1.1 := by
    obtain ⟨y⟩ := U.2
    exact ((genericPoint_spec X).specializes (Set.mem_univ y.1)).mem_open U.1.1.isOpen y.2
  obtain ⟨g, hgV, hgη⟩ := U.1.2.exists_basicOpen_le (V := V) ⟨genericPoint X, hηV⟩ hηU
  have hgx : x ∉ X.basicOpen g := fun h => hgV h (subset_closure rfl)
  intro hbot
  have hmem : (⟨_, sectionsToField_mem_chartAlgebra U g⟩ : chartAlgebra K M U) ∈
      chartIdeal K U hx hK := by
    rw [mem_chartIdeal]
    rintro ⟨v, ⟨w, rfl⟩, hw⟩
    apply hgx
    rw [Scheme.mem_basicOpen X g x hx]
    refine isUnit_iff_exists_inv'.mpr ⟨w, stalkToAmbientBase_injective (M := M) x ?_⟩
    rw [map_mul, map_one, ← hw]
    exact congrArg _ (sectionsToField_eq_stalkToAmbientBase U hx g).symm
  rw [hbot, Ideal.mem_bot] at hmem
  have h0 : sectionsToField M U g = 0 := congrArg Subtype.val hmem
  have hunit : IsUnit (X.presheaf.germ U.1.1 (genericPoint X) hηU g) :=
    (Scheme.mem_basicOpen X g _ hηU).mp hgη
  rw [sectionsToField_eq_stalkToAmbientBase U hηU g] at h0
  exact hunit.ne_zero ((stalkToAmbientBase_injective (M := M) _) (h0.trans (map_zero _).symm))

end ChartIdeal

section Units

variable (L : IntermediateField X.functionField M) [FiniteDimensional X.functionField L]

/-- The local ring map of `X₁ ⟶ X` is the inclusion of the images in `M`. -/
theorem stalkToAmbient_stalkMap (x₁ : NormalizationInExtension.normalization X L)
    (a : X.presheaf.stalk (normalizationStructure X L x₁)) :
    stalkToAmbient L x₁ ((normalizationStructure X L).stalkMap x₁ a) =
      stalkToAmbientBase M _ a := by
  simp only [stalkToAmbient, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply, stalkToField_comp_stalkMap]
  rfl

/-- **Units descend along `O_{X,x} ⟶ O_{X₁,x₁}`.** An element of the image of `O_{X,x}` in `M`
which is a unit in the image of `O_{X₁,x₁}` is a unit in the image of `O_{X,x}`, `x` the image
of `x₁`: the local ring map is local. -/
theorem exists_inv_of_exists_inv (x₁ : NormalizationInExtension.normalization X L) {a : M}
    (ha : a ∈ (stalkToAmbientBase M (normalizationStructure X L x₁)).range)
    (hu : ∃ v ∈ (stalkToAmbient L x₁).range, v * a = 1) :
    ∃ v ∈ (stalkToAmbientBase M (normalizationStructure X L x₁)).range, v * a = 1 := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hu
  have hunit : IsUnit ((normalizationStructure X L).stalkMap x₁ s) := by
    refine isUnit_iff_exists_inv'.mpr ⟨w, stalkToAmbient_injective L x₁ ?_⟩
    rw [map_mul, map_one, stalkToAmbient_stalkMap, hw]
  have hs : IsUnit s := isUnit_of_map_unit ((normalizationStructure X L).stalkMap x₁).hom s hunit
  obtain ⟨u, rfl⟩ := hs
  refine ⟨stalkToAmbientBase M _ (u⁻¹ : Units _).1, ⟨_, rfl⟩, ?_⟩
  rw [← map_mul, Units.inv_mul, map_one]

end Units

end DeJongAlterations.StableModification.Perfection

end
