/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL)
-/
import DeJongAlterations.Algebra.IntegralClosureFiniteType
import DeJongAlterations.Algebra.RegularSmoothConverseFormalSmooth
import DeJongAlterations.StableModification.Perfection.Field

/-!
# Normalizations of a curve after a base change of the ground field

Blueprint chapter `sm-dj-perfection` (new route, not in de Jong 1996; it replaces de Jong 4.11
(c), (d) when generic étaleness is not needed).

## The perfect case (`m = 0`)

`smooth_integralClosure_of_perfectField`: if `k` is a perfect field and `D` is a finitely
generated `k`-domain of dimension at most one with fraction field `L`, then the integral closure of
`D` in `L` is smooth over `k`. Indeed it is finite over `D` (Codex,
`Algebra.IntegralClosureFiniteType.finite_integralClosure`, valid over any field), hence a
Noetherian integrally closed domain of dimension at most one, i.e. a Dedekind domain, hence a
regular ring, hence smooth over the perfect field `k` (Codex,
`Algebra.RegularSmoothConverseFormalSmooth.smooth_of_isRegularRing`, de Jong 2.10). In
characteristic zero this is the whole statement of the blueprint lemma, with `m = 0`.

## The model inside a big field

Fix a field `M`, a subfield `K` (via `[Algebra K M]`) and a finitely generated `K`-subalgebra
`A ⊆ M`; write `F = K(A)` for its fraction field inside `M`. For an intermediate field `E` of
`M / K` we set

* `baseRing A E = E[A] ⊆ M`, the image of `E ⊗_K A`;
* `baseField A E = E(A) ⊆ M`, the image of `E ⊗_K F` (when `E / K` is algebraic and `E`, `F` are
  linearly disjoint, `E ⊗_K F ≅ E(A)`);
* `normalization A E`, the integral closure of `E[A]` in `E(A)`.

The comparison between different `E` is done through the embeddings
`normalizationι A E : normalization A E →ₐ[E] M`, whose range is described by
`mem_range_normalizationι_iff`: if `E / K` is algebraic, an element of `M` lies in the image of
`normalization A E` iff it lies in `E(A)` and is integral over `A`.

`smooth_normalization_of_perfectField`: if `E / K` is algebraic, `E` is perfect and `A` is a
finitely generated `K`-algebra of dimension at most one, `normalization A E` is smooth over `E`.
This is the statement "`B_∞` is smooth over `K^{perf}`" of the blueprint.
-/

noncomputable section

open IntermediateField

namespace DeJongAlterations.StableModification.Perfection

universe u v

section Integrality

/-- Integrality transfers along an inclusion of the images of the two coefficient rings. -/
theorem isIntegral_of_range_le {R₁ R₂ M : Type*} [CommRing R₁] [CommRing R₂] [CommRing M]
    [Algebra R₁ M] [Algebra R₂ M] (hinj : Function.Injective (algebraMap R₂ M))
    (hle : (algebraMap R₁ M).range ≤ (algebraMap R₂ M).range) {x : M} (hx : IsIntegral R₁ x) :
    IsIntegral R₂ x := by
  let e : R₂ ≃+* (algebraMap R₂ M).range := RingEquiv.ofLeftInverse
    (f := (algebraMap R₂ M)) (g := fun y => Function.invFun (algebraMap R₂ M) y)
    (Function.leftInverse_invFun hinj)
  let φ : R₁ →+* R₂ := (e.symm.toRingHom).comp ((algebraMap R₁ M).codRestrict _
    fun r => hle ⟨r, rfl⟩)
  let : Algebra R₁ R₂ := φ.toAlgebra
  have hφ : ∀ r, algebraMap R₂ M (φ r) = algebraMap R₁ M r := by
    intro r
    have := e.apply_symm_apply ⟨algebraMap R₁ M r, hle ⟨r, rfl⟩⟩
    exact congrArg Subtype.val this
  have : IsScalarTower R₁ R₂ M := IsScalarTower.of_algebraMap_eq fun r => (hφ r).symm
  exact hx.tower_top

/-- If every element of the image of `R` is integral over `S`, an element integral over `R` is
integral over `S`. -/
theorem isIntegral_trans_of_range {S R M : Type*} [CommRing S] [CommRing R] [CommRing M]
    [Algebra S M] [Algebra R M] (hR : ∀ r : R, IsIntegral S (algebraMap R M r)) {x : M}
    (hx : IsIntegral R x) : IsIntegral S x := by
  have hle : (algebraMap R M).range ≤ (algebraMap (integralClosure S M) M).range := by
    rintro _ ⟨r, rfl⟩
    exact ⟨⟨_, hR r⟩, rfl⟩
  have : IsIntegral (integralClosure S M) x :=
    isIntegral_of_range_le Subtype.val_injective hle hx
  exact isIntegral_trans x this

end Integrality

section Perfect

variable (k D L : Type u) [Field k] [CommRing D] [IsDomain D] [Algebra k D]
  [Algebra.FiniteType k D] [Ring.DimensionLEOne D] [Field L] [Algebra D L] [IsFractionRing D L]

include k in
/-- The integral closure of a finitely generated domain of dimension at most one over a field `k`
in its fraction field is a Dedekind domain (any field `k`). -/
theorem isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure D L) := by
  have : Module.Finite D (integralClosure D L) :=
    Algebra.IntegralClosureFiniteType.finite_integralClosure k D L
  have : IsNoetherianRing (integralClosure D L) :=
    Algebra.IntegralClosureFiniteType.isNoetherianRing_integralClosure k D L
  have : IsIntegrallyClosed (integralClosure D L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension L
  have : Ring.DimensionLEOne (integralClosure D L) := inferInstance
  have : IsDedekindRing (integralClosure D L) := .mk
  exact .mk

/-- **The perfect case.** Over a perfect field `k`, the integral closure of a finitely generated
domain of dimension at most one in its fraction field is smooth over `k`. In characteristic zero
this is the blueprint lemma `lem:sm-dj-perfection-smooth-curve` with `m = 0`. -/
theorem smooth_integralClosure_of_perfectField [Algebra k L] [IsScalarTower k D L]
    [PerfectField k] :
    Algebra.Smooth k (integralClosure D L) := by
  have := isDedekindDomain_integralClosure k D L
  have : Algebra.FiniteType k (integralClosure D L) :=
    Algebra.IntegralClosureFiniteType.finiteType_integralClosure k D L
  exact Algebra.RegularSmoothConverseFormalSmooth.smooth_of_isRegularRing k (integralClosure D L)

end Perfect

section Model

variable {K : Type u} {M : Type u} [Field K] [Field M] [Algebra K M] (A : Subalgebra K M)

/-- `E[A] ⊆ M`: the image of `E ⊗_K A`. -/
def baseRing (E : IntermediateField K M) : Subalgebra E M := Algebra.adjoin E (A : Set M)

/-- `E(A) ⊆ M`: the image of `E ⊗_K K(A)`, the fraction field of `baseRing A E`. -/
def baseField (E : IntermediateField K M) : IntermediateField E M :=
  IntermediateField.adjoin E (A : Set M)

variable (E : IntermediateField K M)

open IntermediateField.algebraAdjoinAdjoin in
instance : Algebra (baseRing A E) (baseField A E) :=
  inferInstanceAs (Algebra (Algebra.adjoin E (A : Set M)) (IntermediateField.adjoin E (A : Set M)))

open IntermediateField.algebraAdjoinAdjoin in
instance : IsScalarTower E (baseRing A E) (baseField A E) :=
  inferInstanceAs
    (IsScalarTower E (Algebra.adjoin E (A : Set M)) (IntermediateField.adjoin E (A : Set M)))

open IntermediateField.algebraAdjoinAdjoin in
instance : IsScalarTower (baseRing A E) (baseField A E) M :=
  inferInstanceAs
    (IsScalarTower (Algebra.adjoin E (A : Set M)) (IntermediateField.adjoin E (A : Set M)) M)

open IntermediateField.algebraAdjoinAdjoin in
instance : IsFractionRing (baseRing A E) (baseField A E) :=
  inferInstanceAs
    (IsFractionRing (Algebra.adjoin E (A : Set M)) (IntermediateField.adjoin E (A : Set M)))

theorem algebraMap_baseRing_baseField_apply (x : baseRing A E) :
    ((algebraMap (baseRing A E) (baseField A E) x : baseField A E) : M) = x := rfl

theorem subset_baseRing : (A : Set M) ⊆ baseRing A E := Algebra.subset_adjoin

theorem subset_baseField : (A : Set M) ⊆ baseField A E := IntermediateField.subset_adjoin _ _

theorem baseRing_le_baseField : (baseRing A E : Set M) ⊆ baseField A E :=
  IntermediateField.algebra_adjoin_le_adjoin E (A : Set M)

/-- `B_E`: the integral closure of `E[A]` in `E(A)`, i.e. the normalization of `E ⊗_K A`. -/
abbrev normalization : Subalgebra (baseRing A E) (baseField A E) :=
  integralClosure (baseRing A E) (baseField A E)

/-- The embedding of `B_E` into the ambient field `M`, as an `E`-algebra map. -/
def normalizationι : normalization A E →ₐ[E] M where
  toFun x := ((x : baseField A E) : M)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem normalizationι_apply (x : normalization A E) :
    normalizationι A E x = ((x : baseField A E) : M) := rfl

theorem normalizationι_injective : Function.Injective (normalizationι A E) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

variable {A E}

/-- The restriction of scalars of `E(A)` to `K` is the compositum `E ⊔ K(A)`. -/
theorem restrictScalars_baseField :
    (baseField A E).restrictScalars K = E ⊔ IntermediateField.adjoin K (A : Set M) :=
  IntermediateField.restrictScalars_adjoin_eq_sup K E (A : Set M)

/-- `E(A)` is monotone in `E`. -/
theorem baseField_mono {E E' : IntermediateField K M} (h : E ≤ E') {x : M}
    (hx : x ∈ baseField A E) : x ∈ baseField A E' := by
  have hx' : x ∈ (baseField A E).restrictScalars K := hx
  have : x ∈ (baseField A E').restrictScalars K := by
    rw [restrictScalars_baseField] at hx' ⊢
    exact sup_le_sup_right h _ hx'
  exact this

/-- If `E / K` is integral, every element of `E[A]` is integral over `A`. -/
theorem isIntegral_of_mem_baseRing (hE : ∀ x ∈ E, IsIntegral K x) {x : M}
    (hx : x ∈ baseRing A E) : IsIntegral A x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact isIntegral_algebraMap (R := A) (A := M) (x := ⟨x, hx⟩)
  | algebraMap e => exact (hE e e.2).tower_top
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/-- If `E / K` is integral, integrality over `E[A]` and over `A` agree for elements of `M`. -/
theorem isIntegral_baseRing_iff (hE : ∀ x ∈ E, IsIntegral K x) {x : M} :
    IsIntegral (baseRing A E) x ↔ IsIntegral A x := by
  refine ⟨fun h => isIntegral_trans_of_range (fun r => isIntegral_of_mem_baseRing hE r.2) h,
    fun h => isIntegral_of_range_le Subtype.val_injective ?_ h⟩
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨a, subset_baseRing A E a.2⟩, rfl⟩

/-- Membership in `B_E` for an element of `E(A)`: integrality over `A`. -/
theorem mem_normalization_iff (hE : ∀ x ∈ E, IsIntegral K x) (y : baseField A E) :
    y ∈ normalization A E ↔ IsIntegral A (y : M) := by
  rw [mem_integralClosure_iff, ← isIntegral_baseRing_iff hE]
  have := isIntegral_algebraMap_iff (R := baseRing A E) (A := baseField A E) (B := M)
    (x := y) Subtype.val_injective
  exact this.symm

/-- The image of `B_E` in `M`: the elements of `E(A)` integral over `A`. -/
theorem mem_range_normalizationι_iff (hE : ∀ x ∈ E, IsIntegral K x) {x : M} :
    x ∈ (normalizationι A E).range ↔ x ∈ baseField A E ∧ IsIntegral A x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : baseField A E).2, (mem_normalization_iff hE _).1 y.2⟩
  · rintro ⟨hx, hint⟩
    exact ⟨⟨⟨x, hx⟩, (mem_normalization_iff hE ⟨x, hx⟩).2 hint⟩, rfl⟩

/-- Elements of `A` lie in the image of `B_E`. -/
theorem mem_range_normalizationι_of_mem (hE : ∀ x ∈ E, IsIntegral K x) {a : M} (ha : a ∈ A) :
    a ∈ (normalizationι A E).range :=
  (mem_range_normalizationι_iff hE).2
    ⟨subset_baseField A E ha, isIntegral_algebraMap (R := A) (A := M) (x := ⟨a, ha⟩)⟩

/-- `A ⊆ E[A]` as a ring map. -/
def toBaseRing (A : Subalgebra K M) (E : IntermediateField K M) : A →+* baseRing A E where
  toFun a := ⟨a, subset_baseRing A E a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A finitely generated `K`-subalgebra `A ⊆ M` is generated by a finite subset of `M`. -/
theorem exists_finset_adjoin_eq (A : Subalgebra K M) [Algebra.FiniteType K A] :
    ∃ G : Finset M, Algebra.adjoin K (G : Set M) = A := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra K A).FG)
  refine ⟨s.image A.val, ?_⟩
  rw [Finset.coe_image, Algebra.adjoin_image, hs, Algebra.map_top, Subalgebra.range_val]

/-- If `A = K[G]`, then `E[A] = E[G]`. -/
theorem baseRing_eq_adjoin {G : Set M} (hG : Algebra.adjoin K G = A) :
    baseRing A E = Algebra.adjoin E G := by
  rw [baseRing]
  conv_lhs => rw [← hG]
  rw [Algebra.adjoin_adjoin_of_tower]

/-- If `A` is finitely generated over `K`, then `E[A]` is finitely generated over `E`. -/
theorem finiteType_baseRing [Algebra.FiniteType K A] : Algebra.FiniteType E (baseRing A E) := by
  obtain ⟨G, hG⟩ := exists_finset_adjoin_eq A
  rw [baseRing_eq_adjoin (E := E) hG]
  exact (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset _)

/-- If `E / K` is integral and `A` has dimension at most one, so has `E[A]`. -/
theorem dimensionLEOne_baseRing [Ring.DimensionLEOne A] (hE : ∀ x ∈ E, IsIntegral K x) :
    Ring.DimensionLEOne (baseRing A E) := by
  let : Algebra A (baseRing A E) := (toBaseRing A E).toAlgebra
  have : IsScalarTower A (baseRing A E) M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral A (baseRing A E) := ⟨fun x => by
    rw [← isIntegral_algebraMap_iff (B := M) Subtype.val_injective]
    exact isIntegral_of_mem_baseRing hE x.2⟩
  exact Ring.DimensionLEOne.of_isIntegral A (baseRing A E)

/-- **`B_∞` is smooth.** If `E / K` is integral and `E` is perfect, and `A` is a finitely
generated `K`-algebra of dimension at most one, the normalization `B_E` of `E ⊗_K A` is smooth over
`E`. -/
theorem smooth_normalization_of_perfectField [Algebra.FiniteType K A] [Ring.DimensionLEOne A]
    [PerfectField E] (hE : ∀ x ∈ E, IsIntegral K x) : Algebra.Smooth E (normalization A E) := by
  have := finiteType_baseRing (A := A) (E := E)
  have := dimensionLEOne_baseRing (A := A) hE
  exact smooth_integralClosure_of_perfectField E (baseRing A E) (baseField A E)

end Model

end DeJongAlterations.StableModification.Perfection

end
