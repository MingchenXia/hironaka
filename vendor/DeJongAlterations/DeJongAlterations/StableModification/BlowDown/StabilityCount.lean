/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricNormalization

/-!
# The δ-count of a contraction of several points (Temkin, proof of Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (`stabcritlem`, T:3125–3133) and Corollary B.2 (`stabdowncor`, T:4442–4444). In the
de Jong route the stability criterion is applied to the fibre map `f_s : C′_s → C_s` of a
modification of projective curves, which is an isomorphism off the fibres over **all** points
`x_1, …, x_l` of the modification locus in `C_s` (blueprint `lem:sm-stability-criterion`,
`rem:sm-bd-literature`(4)). This file generalizes lane CRV3/CRV4's δ-count for one contracted point
(`CurvesField.Genus.deltaInvariant_contraction`) to a set `X` of contracted points:

  `∑_{x ∈ X} δ_C(x) = ∑ᶠ_{z ∈ f⁻¹X} δ_{C′}(z) + ∑_{v ∈ G} g(v) − |G| + (p_a(C) − p_a(C′))`,

where `G` is the set of generic points of `C′` mapping into `X` (`innerSet`), `δ_C`, `δ_{C′}` are
the δ-invariants of the normalizations, and `g(v) = p_a(C̃′_v)`. The proofs follow CRV3/CRV4's,
with `x` replaced by `X`.

## Main results

* `outerSet f X`, `innerSet f X`: the generic points of `C′` outside / inside `f⁻¹X`.
* `isFinite_outerSetMap`: `b : N → C`, `N` the normalization of `C′` in its outer generic points,
  is finite (Zariski's main theorem).
* `outerSetMap_app_injective`, `outerSetMap_isFiniteCoker`: the hypotheses of the δ-formula.
* `outerSetNormalizationIso`, `deltaInvariant_outerSetMap_eq`, `natCard_outerSetMap_fiber_eq`:
  `N` is the normalization of `C`; hence `δ_b = δ_C` and `b⁻¹(y) ≅ π⁻¹(y)`.
* `deltaInvariant_contraction_finset` (blueprint `lem:sm-bdc-count`): the δ-count above.
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.Genus

set_option autoImplicit false

universe u

noncomputable section

section Outer

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (X : Set C)

/-- The generic points of `C'` outside `f⁻¹(X)`. -/
def outerSet : Set C' := {η | η ∈ genericPoints C' ∧ f η ∉ X}

/-- The generic points of `C'` in `f⁻¹(X)` (the components of the contracted fibres). -/
def innerSet : Set C' := {η | η ∈ genericPoints C' ∧ f η ∈ X}

instance [Finite (genericPoints C')] : Finite (outerSet f X) :=
  Set.Finite.subset (Set.toFinite (genericPoints C')) fun _ h => h.1

instance [Finite (genericPoints C')] : Finite (innerSet f X) :=
  Set.Finite.subset (Set.toFinite (genericPoints C')) fun _ h => h.1

lemma outerSet_union_innerSet : outerSet f X ∪ innerSet f X = genericPoints C' := by
  ext η
  simp only [outerSet, innerSet, Set.mem_union, Set.mem_ofPred_eq]
  tauto

lemma disjoint_outerSet_innerSet : Disjoint (outerSet f X) (innerSet f X) :=
  Set.disjoint_left.2 fun _ h h' => h.2 h'.2

/-- **The outer components meet the contracted fibres in finitely many points.** -/
theorem finite_closure_outerSet_inter [NoetherianSpace C'] [Finite (genericPoints C')]
    (hdim : topologicalKrullDim C' ≤ 1) (hX : IsClosed X) :
    (closure (outerSet f X) ∩ f ⁻¹' X).Finite := by
  refine finite_of_isClosed_of_disjoint_genericPoints hdim
    (isClosed_closure.inter (hX.preimage f.continuous)) fun η hη hgen => ?_
  obtain ⟨hcl, hfib⟩ := hη
  rw [← Set.biUnion_of_singleton (outerSet f X),
    (Set.toFinite (outerSet f X)).closure_biUnion] at hcl
  obtain ⟨η'', hη'', hηcl⟩ := Set.mem_iUnion₂.1 hcl
  have hsp : η'' ⤳ η := specializes_iff_mem_closure.2 hηcl
  have heq := (mem_genericPoints_iff η).1 hgen η'' hsp
  exact hη''.2 (heq ▸ hfib)

variable (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ∉ X) [IsIso (f ∣_ U)]
  [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p']

omit [IsAffineHom (pullback.diagonal (terminal.from C'))] in
include hU in
/-- Over `y ∉ X` the fibre of `f` has at most one point. -/
lemma subsingleton_preimage_of_not_mem {y : C} (hy : y ∉ X) : (f ⁻¹' {y}).Subsingleton := by
  intro z₁ h₁ z₂ h₂
  have hy' : y ∈ U := (hU y).2 hy
  exact injOn_of_isIso_morphismRestrict f U (h₁ ▸ hy') (h₂ ▸ hy') (h₁.trans h₂.symm)

/-- The morphism `b = π'' ≫ f : N = C̃'_{S''} → C`, `S''` the generic points of `C'` outside
`f⁻¹(X)`. -/
abbrev outerSetMap [Finite (genericPoints C')] : normalizationPoints (outerSet f X) ⟶ C :=
  normalizationPointsMap (outerSet f X) ≫ f

include hU p' in
/-- **The normalization of `C'` in its outer generic points is finite over `C`**: `b = π'' ≫ f`
is proper with finite fibres, hence finite (Zariski's main theorem). -/
theorem isFinite_outerSetMap [CompactSpace C'] [Finite (genericPoints C')] [IsProper f]
    (hdim : topologicalKrullDim C' ≤ 1) (hX : IsClosed X) : IsFinite (outerSetMap f X) := by
  have := isFinite_normalizationPointsMap (S := outerSet f X) p'
  have := isLocallyNoetherian_of_locallyOfFiniteType p'
  have : IsNoetherian C' := ⟨⟩
  have hfib : ∀ z : C', ((normalizationPointsMap (outerSet f X)) ⁻¹' {z}).Finite :=
    fun z => (normalizationPointsMap (outerSet f X)).finite_preimage_singleton z
  have : LocallyQuasiFinite (outerSetMap f X) := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    by_cases hy : y ∈ X
    · refine ((finite_closure_outerSet_inter f X hdim hX).preimage' fun z _ => hfib z).subset ?_
      intro w hw
      refine ⟨range_normalizationPointsMap_subset _ ⟨w, rfl⟩, ?_⟩
      have : f (normalizationPointsMap (outerSet f X) w) = y := hw
      change f (normalizationPointsMap (outerSet f X) w) ∈ X
      rw [this]
      exact hy
    · exact ((subsingleton_preimage_of_not_mem f X U hU hy).finite).preimage' fun z _ => hfib z
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

omit [IsAffineHom (pullback.diagonal (terminal.from C'))] in
include hU in
/-- **The outer generic points form a generic family of every affine open of `C`**, through `f`
(provided no point of `X` is a generic point of `C`). -/
theorem isGenericFamily_outerSet {V : C.Opens} (hV : IsAffineOpen V)
    (hXg : ∀ x ∈ X, x ∉ genericPoints C) :
    letI : ∀ i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
    IsGenericFamily (fun i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V) =>
        (hV.primeIdealOf ⟨f i.1.1, i.2⟩).asIdeal) (fun i => C'.residueField i.1.1) := by
  let _ : ∀ i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
  have hmemU : ∀ i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V), f i.1.1 ∈ U := fun i =>
    (hU _).2 i.1.2.2
  refine IsGenericFamily.mk ⟨fun i => ?_, fun i z => ?_⟩ (fun i j hij => ?_) (fun q hq => ?_)
  · ext a
    rw [RingHom.mem_ker, ← residueAt_eq_zero_iff hV (f i.1.1) i.2 a]
    change pullbackResidue f V i.1.1 i.2 a = 0 ↔ _
    rw [pullbackResidue_eq]
    exact map_eq_zero_iff _ (f.residueFieldMap i.1.1).hom.injective
  · have := isIso_residueFieldMap_of_isIso_morphismRestrict f U i.1.1 (hmemU i)
    obtain ⟨z₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.residueFieldMap i.1.1)).2 z
    obtain ⟨a, t, ht, hta⟩ := exists_residueAt_mul_eq hV (f i.1.1) i.2 z₀
    refine ⟨a, t, ht, ?_⟩
    change pullbackResidue f V i.1.1 i.2 t * _ = pullbackResidue f V i.1.1 i.2 a
    rw [pullbackResidue_eq, pullbackResidue_eq, ← map_mul, hta]
  · have hne : f i.1.1 ≠ f j.1.1 := fun h => hij (Subtype.ext (Subtype.ext
      (injOn_of_isIso_morphismRestrict f U (hmemU i) (hmemU j) h)))
    exact not_primeIdealOf_le hV i.2 j.2
      ((mem_genericPoints_iff_of_isIso_morphismRestrict f U (hmemU j)).1 j.1.2.1) hne
  · let q₀ : PrimeSpectrum Γ(C, V) := ⟨q, hq.1.1⟩
    have hgen := fromSpec_mem_genericPoints hV q₀ hq
    have hyV : hV.fromSpec q₀ ∈ V := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact Set.mem_range_self q₀
    have hyx : hV.fromSpec q₀ ∉ X := fun h => hXg _ h hgen
    obtain ⟨η, hη⟩ := exists_eq_of_isIso_morphismRestrict f U ((hU _).2 hyx)
    have hηU : f η ∈ U := hη ▸ (hU _).2 hyx
    have hηgen : η ∈ genericPoints C' :=
      (mem_genericPoints_iff_of_isIso_morphismRestrict f U hηU).2 (hη ▸ hgen)
    refine ⟨⟨⟨η, hηgen, hη ▸ hyx⟩, show f η ∈ V from hη ▸ hyV⟩, ?_⟩
    have : hV.primeIdealOf ⟨f η, hη ▸ hyV⟩ = q₀ := by
      apply hV.fromSpec.isOpenEmbedding.injective
      rw [hV.fromSpec_primeIdealOf]
      exact hη
    exact congrArg PrimeSpectrum.asIdeal this

variable [Finite (genericPoints C')]

omit [IsIso (f ∣_ U)] in
lemma le_pointsι_preimage_outerSet (V : C.Opens) (i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V)) :
    (⊤ : (Spec (C'.residueField i.1.1)).Opens) ≤ pointsι i.1 ⁻¹ᵁ
      ((pointsMap C' (outerSet f X)).toNormalization ⁻¹ᵁ
        (normalizationPointsMap (outerSet f X) ⁻¹ᵁ (f ⁻¹ᵁ V))) := by
  intro y _
  change ((pointsMap C' (outerSet f X)).toNormalization ≫
    (pointsMap C' (outerSet f X)).fromNormalization) (pointsι i.1 y) ∈ f ⁻¹ᵁ V
  rw [Scheme.Hom.toNormalization_fromNormalization, pointsMap_ι_apply]
  exact i.2

/-- The values at the outer generic points of the sections of `𝒪_N` over `b⁻¹(V)`. -/
def outerSetEval (V : C.Opens) :
    Γ(normalizationPoints (outerSet f X), outerSetMap f X ⁻¹ᵁ V) →+*
      ∀ i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V), C'.residueField i.1.1 :=
  RingHom.pi fun i => (pointsEvalOn ((pointsMap C' (outerSet f X)).toNormalization ⁻¹ᵁ
      (normalizationPointsMap (outerSet f X) ⁻¹ᵁ (f ⁻¹ᵁ V))) i.1
      (le_pointsι_preimage_outerSet f X V i)).hom.comp
    ((pointsMap C' (outerSet f X)).toNormalization.app
      (normalizationPointsMap (outerSet f X) ⁻¹ᵁ (f ⁻¹ᵁ V))).hom

omit [IsIso (f ∣_ U)] in
lemma outerSetEval_comp (V : C.Opens) :
    (outerSetEval f X V).comp ((outerSetMap f X).app V).hom =
      RingHom.pi fun i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V) =>
        pullbackResidue f V i.1.1 i.2 := by
  ext a i
  have h := app_pointsEvalOn (pointsMap C' (outerSet f X)).toNormalization
    (normalizationPointsMap (outerSet f X))
    (Scheme.Hom.toNormalization_fromNormalization _) (f ⁻¹ᵁ V) i.1 i.2
    (le_pointsι_preimage_outerSet f X V i)
  have h' := congrArg (fun φ => φ.hom (f.app V a)) h
  simp only at h'
  change (pointsEvalOn _ i.1 _).hom (((pointsMap C' (outerSet f X)).toNormalization.app _).hom
    (((normalizationPointsMap (outerSet f X)).app (f ⁻¹ᵁ V)).hom ((f.app V).hom a))) = _
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply] at h'
  exact h'

omit [IsIso (f ∣_ U)] in
lemma outerSetEval_injective (V : C.Opens) : Function.Injective (outerSetEval f X V) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h0 : ((pointsMap C' (outerSet f X)).toNormalization.app
      (normalizationPointsMap (outerSet f X) ⁻¹ᵁ (f ⁻¹ᵁ V))).hom s = 0 := by
    refine pointsEvalOn_injective (f ⁻¹ᵁ V) _ ?_ _ fun η hη h => ?_
    · intro w hw
      change ((pointsMap C' (outerSet f X)).toNormalization ≫
        (pointsMap C' (outerSet f X)).fromNormalization) w ∈ f ⁻¹ᵁ V at hw
      rwa [Scheme.Hom.toNormalization_fromNormalization] at hw
    · exact congrFun hs ⟨η, hη⟩
  exact toNormalization_app_injective (pointsMap C' (outerSet f X)) (f ⁻¹ᵁ V)
    (h0.trans (map_zero _).symm)

include hU in
/-- **`𝒪_C → b_*𝒪_N` is injective** on affine opens, for `C` reduced. -/
theorem outerSetMap_app_injective [IsReduced C] (hXg : ∀ x ∈ X, x ∉ genericPoints C)
    (V : C.Opens) (hV : IsAffineOpen V) : Function.Injective ((outerSetMap f X).app V).hom := by
  let _ : ∀ i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
  have h := isGenericFamily_outerSet f X U hU hV hXg
  refine Function.Injective.of_comp (f := outerSetEval f X V) ?_
  rw [← RingHom.coe_comp, outerSetEval_comp]
  exact h.injective_algebraMap

include hU p' in
/-- **`b_*𝒪_N / 𝒪_C` is a finite-dimensional skyscraper** on affine opens. -/
theorem outerSetMap_isFiniteCoker [CompactSpace C'] [IsProper f]
    (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p] (hXg : ∀ x ∈ X, x ∉ genericPoints C)
    (hdim : topologicalKrullDim C ≤ 1) (hdim' : topologicalKrullDim C' ≤ 1) (hX : IsClosed X)
    (V : C.Opens) (hV : IsAffineOpen V) :
    IsFiniteCoker (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))
      ((outerSetMap f X).app V).hom := by
  have := isFinite_outerSetMap f X U hU p' hdim' hX
  let ψ := sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)
  let _ : Algebra k Γ(C, V) := ψ.toAlgebra
  have : Algebra.FiniteType k Γ(C, V) :=
    Geometry.NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
  have : Ring.KrullDimLE 1 Γ(C, V) :=
    Geometry.NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
  let _ : ∀ i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
  have h := isGenericFamily_outerSet f X U hU hV hXg
  have : Finite (GenericIn C' (outerSet f X) (f ⁻¹ᵁ V)) := Subtype.finite
  let φ := ((outerSetMap f X).app V).hom
  let B := Γ(normalizationPoints (outerSet f X), outerSetMap f X ⁻¹ᵁ V)
  let _ : Algebra Γ(C, V) B := φ.toAlgebra
  let _ : Algebra k B := (φ.comp ψ).toAlgebra
  have : IsScalarTower k Γ(C, V) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral Γ(C, V) B :=
    algebraMap_isIntegral_iff.1 ((outerSetMap f X).isIntegral_app V hV)
  let Φ : B →ₐ[Γ(C, V)] ∀ i : GenericIn C' (outerSet f X) (f ⁻¹ᵁ V), C'.residueField i.1.1 :=
    { toRingHom := outerSetEval f X V
      commutes' := fun a => by
        have := congrArg (fun ρ => ρ a) (outerSetEval_comp f X V)
        exact this }
  unfold IsFiniteCoker
  exact h.finiteDimensional_coker k Φ (outerSetEval_injective f X V)

end Outer

section Normalization

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (X : Set C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ∉ X)
  [IsIso (f ∣_ U)]

omit [IsIso (f ∣_ U)] in
include hU in
lemma mem_U_of_mem_outerSet {η : C'} (hη : η ∈ outerSet f X) : f η ∈ U :=
  (hU _).2 hη.2

include hU in
/-- **The outer generic points of `C'` are the generic points of `C`**, through `f`. -/
lemma bijective_outerSet (hXg : ∀ x ∈ X, x ∉ genericPoints C) :
    Function.Bijective (fun η : outerSet f X => (⟨f η.1,
      (mem_genericPoints_iff_of_isIso_morphismRestrict f U
        (mem_U_of_mem_outerSet f X U hU η.2)).1 η.2.1⟩ : genericPoints C)) := by
  refine ⟨fun η η' h => Subtype.ext (injOn_of_isIso_morphismRestrict f U
    (mem_U_of_mem_outerSet f X U hU η.2) (mem_U_of_mem_outerSet f X U hU η'.2)
    (congrArg Subtype.val h)), fun ξ => ?_⟩
  have hξx : ξ.1 ∉ X := fun h => hXg _ h ξ.2
  obtain ⟨η, hη⟩ := exists_eq_of_isIso_morphismRestrict f U ((hU _).2 hξx)
  have hηU : f η ∈ U := hη ▸ (hU _).2 hξx
  have hηg : η ∈ genericPoints C' :=
    (mem_genericPoints_iff_of_isIso_morphismRestrict f U hηU).2 (hη ▸ ξ.2)
  exact ⟨⟨η, hηg, hη ▸ hξx⟩, Subtype.ext hη⟩

/-- The bijection `η ↦ f η` from the outer generic points of `C'` to the generic points of `C`. -/
abbrev outerSetEquiv (hXg : ∀ x ∈ X, x ∉ genericPoints C) : outerSet f X ≃ genericPoints C where
  toFun η := ⟨f η.1, (mem_genericPoints_iff_of_isIso_morphismRestrict f U
    (mem_U_of_mem_outerSet f X U hU η.2)).1 η.2.1⟩
  invFun := (Equiv.ofBijective _ (bijective_outerSet f X U hU hXg)).symm
  left_inv := (Equiv.ofBijective _ (bijective_outerSet f X U hU hXg)).symm_apply_apply
  right_inv := (Equiv.ofBijective _ (bijective_outerSet f X U hU hXg)).apply_symm_apply

/-- **The points schemes agree**: `∐_{η} Spec κ(η) ≅ ∐_{ξ} Spec κ(ξ)`. -/
def outerSetPointsIso (hXg : ∀ x ∈ X, x ∉ genericPoints C) :
    pointsScheme C' (outerSet f X) ≅ pointsScheme C (genericPoints C) :=
  Sigma.whiskerEquiv (outerSetEquiv f X U hU hXg) fun η =>
    haveI := isIso_residueFieldMap_of_isIso_morphismRestrict f U η.1
      (mem_U_of_mem_outerSet f X U hU η.2)
    (asIso (Spec.map (f.residueFieldMap η.1))).symm

lemma outerSetPointsIso_hom_pointsMap (hXg : ∀ x ∈ X, x ∉ genericPoints C) :
    (outerSetPointsIso f X U hU hXg).hom ≫ pointsMap C (genericPoints C) =
      pointsMap C' (outerSet f X) ≫ f := by
  refine Sigma.hom_ext _ _ fun η => ?_
  have h1 : Sigma.ι (fun η : outerSet f X => Spec (C'.residueField η.1)) η ≫
      (outerSetPointsIso f X U hU hXg).hom = Spec.map (f.residueFieldMap η.1) ≫
        Sigma.ι (fun ξ : genericPoints C => Spec (C.residueField ξ.1))
          (outerSetEquiv f X U hU hXg η) :=
    Sigma.ι_comp_map' _ _ η
  have h2 : Sigma.ι (fun ξ : genericPoints C => Spec (C.residueField ξ.1))
      (outerSetEquiv f X U hU hXg η) ≫ pointsMap C (genericPoints C) =
        C.fromSpecResidueField (f η.1) :=
    ι_pointsMap _ _ _
  rw [← Category.assoc, h1, Category.assoc, h2, ι_pointsMap_assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

variable [IsAffineHom (pullback.diagonal (terminal.from C'))] [Finite (genericPoints C')]
  [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)]

/-- **The outer normalization is the normalization of `C`**: if `b : N → C` is integral (e.g.
finite), then `N ≅ C̃` over `C`. -/
def outerSetNormalizationIso [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom (outerSetMap f X)]
    (hXg : ∀ x ∈ X, x ∉ genericPoints C) :
    normalizationPoints (outerSet f X) ≅ normalizationPoints (genericPoints C) :=
  (normalizationCompIso (pointsMap C' (outerSet f X)) f).symm ≪≫
    normalizationIsoOfIso _ _ (outerSetPointsIso f X U hU hXg)
      (outerSetPointsIso_hom_pointsMap f X U hU hXg)

lemma outerSetNormalizationIso_hom_comp [QuasiCompact f] [QuasiSeparated f]
    [IsIntegralHom (outerSetMap f X)] (hXg : ∀ x ∈ X, x ∉ genericPoints C) :
    (outerSetNormalizationIso f X U hU hXg).hom ≫ normalizationPointsMap (genericPoints C) =
      outerSetMap f X := by
  rw [outerSetNormalizationIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    normalizationIsoOfIso_hom_fromNormalization, ← normalizationCompIso_hom_fromNormalization,
    Iso.inv_hom_id_assoc]

include hU in
/-- **`δ_b = δ_C`**: the δ-invariant of `b : N → C` at any point is that of the normalization of
`C`. -/
theorem deltaInvariant_outerSetMap_eq {k : Type u} [Field k] [QuasiCompact f] [QuasiSeparated f]
    [IsFinite (outerSetMap f X)] (hXg : ∀ x ∈ X, x ∉ genericPoints C) (c : k →+* Γ(C, ⊤))
    (y : C) :
    deltaInvariant (outerSetMap f X) c y =
      deltaInvariant (normalizationPointsMap (genericPoints C)) c y := by
  have : IsAffineHom (normalizationPointsMap (genericPoints C)) := inferInstance
  refine deltaInvariant_eq_of_isOpenImmersion (normalizationPointsMap (genericPoints C))
    (outerSetNormalizationIso f X U hU hXg).hom (outerSetMap f X)
    (outerSetNormalizationIso_hom_comp f X U hU hXg) c y ⊤ trivial ?_
  intro w _
  obtain ⟨w', rfl⟩ := ((ConcreteCategory.bijective_of_isIso
    (outerSetNormalizationIso f X U hU hXg).hom.base).2 w)
  exact ⟨w', rfl⟩

include hU in
/-- **`b⁻¹(y)` is the set of branches `π⁻¹(y)` of `C` at `y`.** -/
theorem natCard_outerSetMap_fiber_eq [QuasiCompact f] [QuasiSeparated f]
    [IsIntegralHom (outerSetMap f X)] (hXg : ∀ x ∈ X, x ∉ genericPoints C) (y : C) :
    Nat.card ↥(outerSetMap f X ⁻¹' {y}) =
      Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {y}) := by
  let e := outerSetNormalizationIso f X U hU hXg
  have hb := ConcreteCategory.bijective_of_isIso e.hom.base
  have hcomp : ∀ w, normalizationPointsMap (genericPoints C) (e.hom w) = outerSetMap f X w := by
    intro w
    rw [← Scheme.Hom.comp_apply, outerSetNormalizationIso_hom_comp]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨e.hom w.1, by
    change normalizationPointsMap (genericPoints C) (e.hom w.1) = y
    rw [hcomp]
    exact w.2⟩) ⟨fun w w' h => Subtype.ext (hb.1 (congrArg Subtype.val h)), fun w => ?_⟩)
  obtain ⟨w', hw'⟩ := hb.2 w.1
  refine ⟨⟨w', ?_⟩, Subtype.ext hw'⟩
  change outerSetMap f X w' = y
  rw [← hcomp, show e.hom w' = w.1 from hw']
  exact w.2

end Normalization

section Contraction

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (X : Set C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ∉ X)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

include hU in
/-- **The local comparison off `f⁻¹(X)`**: for `S = S'' ∪ T` with `T` a finite set of points of
`f⁻¹(X)`, and `f y' ∉ X`, the δ-invariant of `C̃'_S → C'` at `y'` equals that of `b : N → C` at
`f y'`. -/
theorem deltaInvariant_normalizationPoints_eq_outerSet (S T : Set C') [Finite S] [Finite T]
    (hS : S = outerSet f X ∪ T) (hd : Disjoint (outerSet f X) T) (hT : ∀ v ∈ T, f v ∈ X)
    (hX : IsClosed X) [IsAffineHom (outerSetMap f X)] (c : k →+* Γ(C, ⊤)) (y : C')
    (hy : f y ∉ X) :
    deltaInvariant (normalizationPointsMap S) (f.appTop.hom.comp c) y =
      deltaInvariant (outerSetMap f X) c (f y) := by
  subst hS
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_opensRange_pointsIncl hd)
  obtain ⟨jU, jV, _, _, hjU, hjV, -, hcov⟩ := exists_normalization_split
    (pointsMap C' (outerSet f X ∪ T)) _ _ (pointsMap C' (outerSet f X)) (pointsMap C' T)
    (pointsIncl_pointsMap _) (pointsIncl_pointsMap _) e
  have hyU : f y ∈ U := (hU _).2 hy
  refine (deltaInvariant_eq_of_isOpenImmersion _ jU _ hjU _ y (f ⁻¹ᵁ U) hyU ?_).symm.trans
    (deltaInvariant_comp_of_isIso (normalizationPointsMap (outerSet f X)) f U c y hyU)
  intro z hz
  have hz' : z ∈ jU.opensRange ⊔ jV.opensRange := by
    rw [hcov]
    trivial
  rcases Opens.mem_sup.1 hz' with h | ⟨w, rfl⟩
  · exact h
  · exfalso
    have hcl : closure T ⊆ f ⁻¹' X :=
      closure_minimal (fun v hv => hT v hv) (hX.preimage f.continuous)
    have hw : normalizationPointsMap T w ∈ closure T :=
      range_normalizationPointsMap_subset T ⟨w, rfl⟩
    have h0 : normalizationPointsMap (outerSet f X ∪ T) (jV w) = normalizationPointsMap T w := by
      rw [show normalizationPointsMap T = jV ≫ normalizationPointsMap (outerSet f X ∪ T) from
        hjV.symm]
      exact (Scheme.Hom.comp_apply _ _ _).symm
    have h1 : f (normalizationPointsMap (outerSet f X ∪ T) (jV w)) ∈ X := by
      rw [h0]
      exact hcl hw
    exact (hU _).1 hz h1

include hU in
/-- **The δ-count of a contraction of finitely many points** (blueprint `lem:sm-bdc-count`;
Temkin, Corollary B.2, `semi-stable.tex` l. 4442–4444, for all contracted points at once). Let
`f : C' → C` be a proper morphism of reduced curves (dimension `≤ 1`), projective over a field `k`
compatibly (`f ≫ p = p'`), which is an isomorphism over `U = C ∖ X` for a finite set `X` of closed
points that are not generic points of `C`. Let `G` be the set of generic points of `C'` mapping
into `X`, `δ'` the δ-invariant of the normalization `C̃' → C'` and `δ_b` that of
`b : N → C`. Then both δ-invariants have finite support and
`∑_{x ∈ X} δ_b(x) = ∑ᶠ_{z ∈ f⁻¹X} δ'(z) + ∑_{v ∈ G} g(v) - |G| + (p_a(C) - p_a(C'))`. -/
theorem deltaInvariant_contraction_finset [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p') (J : Finset C)
    (hJ : (J : Set C) = X) (hXg : ∀ x ∈ X, x ∉ genericPoints C) (hX : IsClosed X)
    (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (G : Finset C') (hG : (G : Set C') = innerSet f X) :
    (Function.support (deltaInvariant (outerSetMap f X) (structureCoeff p))).Finite ∧
      (Function.support (deltaInvariant (normalizationPointsMap (genericPoints C'))
        (structureCoeff p'))).Finite ∧
      ((∑ x ∈ J, deltaInvariant (outerSetMap f X) (structureCoeff p) x : ℕ) : ℤ) =
        ((∑ᶠ y ∈ f ⁻¹' X, deltaInvariant (normalizationPointsMap (genericPoints C'))
            (structureCoeff p') y : ℕ) : ℤ) +
          ∑ v ∈ G, componentGenus (structureCoeff p') v - G.card +
            (arithmeticGenus C (structureCoeff p) - arithmeticGenus C' (structureCoeff p')) := by
  subst hfp
  have hc : structureCoeff (f ≫ p) = f.appTop.hom.comp (structureCoeff p) := rfl
  have := isFinite_outerSetMap f X U hU (f ≫ p) hdim' hX
  have hXC : ∀ i, FiniteDimensional k
      (cohomology (SheafOfModules.unit C.ringCatSheaf) (structureCoeff p) i) := fun i =>
    finite_cohomology_of_isProjectiveOver hp (SheafOfModules.unit C.ringCatSheaf)
      (fun V _ => Module.Finite.self Γ(C, V)) i
  obtain ⟨-, hsuppb, hb⟩ := eulerChar_eq_add_finsum_delta (outerSetMap f X) (structureCoeff p)
    (fun V hV => outerSetMap_app_injective f X U hU hXg V hV)
    (fun V hV => outerSetMap_isFiniteCoker f X U hU (f ≫ p) p hXg hdim hdim' hX V hV) hXC
  obtain ⟨hfin', hsupp', hpa'⟩ :=
    arithmeticGenus_eq_normalizationPoints (f ≫ p) (genericPoints C') rfl hdim' hp'
  have hS : genericPoints C' = outerSet f X ∪ (G : Set C') := by
    rw [hG, outerSet_union_innerSet]
  have hd : Disjoint (outerSet f X) (G : Set C') := hG ▸ disjoint_outerSet_innerSet f X
  rw [hc] at hfin' hsupp' hpa' ⊢
  obtain ⟨-, hfinG, hsplit⟩ := eulerChar_normalizationPoints_union (genericPoints C')
    (outerSet f X) (G : Set C') hS hd (f.appTop.hom.comp (structureCoeff p)) hfin'
  obtain ⟨-, hsum⟩ := eulerChar_normalizationPoints_eq_sum G
    (f.appTop.hom.comp (structureCoeff p)) hfinG
  have hloc : ∀ y : C', f y ∉ X →
      deltaInvariant (normalizationPointsMap (genericPoints C'))
          (f.appTop.hom.comp (structureCoeff p)) y =
        deltaInvariant (outerSetMap f X) (structureCoeff p) (f y) := fun y hy =>
    deltaInvariant_normalizationPoints_eq_outerSet f X U hU (genericPoints C') (G : Set C') hS hd
      (fun v hv => by rw [hG] at hv; exact hv.2) hX (structureCoeff p) y hy
  set δ' := deltaInvariant (normalizationPointsMap (genericPoints C'))
    (f.appTop.hom.comp (structureCoeff p)) with hδ'
  set δb := deltaInvariant (outerSetMap f X) (structureCoeff p) with hδb
  have h1 : ∑ᶠ y, δ' y = (∑ᶠ y ∈ f ⁻¹' X, δ' y) + ∑ᶠ y ∈ (f ⁻¹' X)ᶜ, δ' y := by
    rw [← finsum_mem_univ, ← Set.union_compl_self (f ⁻¹' X)]
    exact finsum_mem_union' disjoint_compl_right (hsupp'.subset Set.inter_subset_right)
      (hsupp'.subset Set.inter_subset_right)
  have h2 : ∑ᶠ y, δb y = (∑ x ∈ J, δb x) + ∑ᶠ y ∈ Xᶜ, δb y := by
    rw [← finsum_mem_univ, ← Set.union_compl_self X,
      finsum_mem_union' disjoint_compl_right (hsuppb.subset Set.inter_subset_right)
        (hsuppb.subset Set.inter_subset_right), ← hJ, finsum_mem_coe_finset]
  have h3 : ∑ᶠ y ∈ (f ⁻¹' X)ᶜ, δ' y = ∑ᶠ y ∈ Xᶜ, δb y := by
    refine finsum_mem_eq_of_bijOn f ⟨fun y hy => hy, fun y₁ h₁ y₂ h₂ h => ?_, fun y hy => ?_⟩
      fun y hy => hloc y hy
    · exact injOn_of_isIso_morphismRestrict f U ((hU _).2 h₁) ((hU _).2 h₂) h
    · obtain ⟨y', hy'⟩ := exists_eq_of_isIso_morphismRestrict f U ((hU _).2 hy)
      exact ⟨y', show f y' ∉ X from hy' ▸ hy, hy'⟩
  have hb' : eulerChar (normalizationPoints (outerSet f X))
      ((normalizationPointsMap (outerSet f X)).appTop.hom.comp
        (f.appTop.hom.comp (structureCoeff p))) =
      eulerChar C (structureCoeff p) + ((∑ᶠ y, δb y : ℕ) : ℤ) := hb
  refine ⟨hsuppb, hsupp', ?_⟩
  rw [h1, h3] at hpa'
  rw [h2] at hb'
  simp only [arithmeticGenus] at hpa' ⊢
  rw [hsplit, hsum] at hpa'
  simp only [componentGenus, arithmeticGenus, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  push_cast at hpa' hb' ⊢
  linarith

end Contraction

end

end DeJongAlterations.StableModification.BlowDown
