/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownScheme
import DeJongAlterations.StableModification.CurvesField.StableDown

/-!
# The δ-count of a contraction (Temkin, Corollary B.2, first step)

Let `f : C' → C` be a proper morphism of reduced projective curves over a field `k` which is an
isomorphism over `U = C ∖ {x}`, for a closed point `x` of `C` which is not a generic point, and let
`Z = f⁻¹(x)`. Let `N = C̃'_{S''}` be the normalization of `C'` in its generic points outside `Z`,
and `b : N → C` the composite with `f` (`outerMap`, finite by `isFinite_outerNormalization`). Then

  `δ_b(x) = ∑ᶠ_{z ∈ Z} δ_{C'}(z) + ∑_{v ∈ Z⁰} g(v) - |Z⁰| + (p_a(C) - p_a(C'))`

(`deltaInvariant_contraction`), where `δ_{C'}` is the δ-invariant of the normalization
`C̃' → C'`, `Z⁰` the set of generic points of `C'` in `Z` and `g(v) = p_a(C̃'_v)` the genus of the
normalization of the component of `v`. In particular, if `p_a(C') = p_a(C)`, this is Temkin's
identity `g(x) = ∑_{z ∈ Z} g(z) - |Z⁰|` (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification/source/semi-stable.tex`,
l. 4442–4444), with `g(z) = δ_{C'}(z)` at the closed points of `Z` and `g(v)` at its generic points
(`deltaInvariant_contraction_of_arithmeticGenus_eq`).

## The argument

Compare the δ-formulas for `b : N → C` and `π' : C̃' → C'`, using `C̃' = N ⊔ C̃'_{Z⁰}`
(`eulerChar_normalizationPoints_union`) and the local comparison `δ_{C'}(y') = δ_b(f y')` for
`y' ∉ Z` (`deltaInvariant_normalizationPoints_eq_outer`): over `C ∖ {x}`, `f` is an isomorphism
(`deltaInvariant_comp_of_isIso`) and `N ⊆ C̃'` is an open subscheme containing the preimage of
`C' ∖ Z` (`deltaInvariant_eq_of_isOpenImmersion`). Both local statements reduce to the invariance of
`dim_k (B / A)_𝔭` under ring isomorphisms (`deltaAt_eq_of_ringEquiv`, `deltaAt_comp_bijective`).

Blueprint: `sm-curves-fields-genus-reduced.tex`, `lem:sm-stabdown-count-scheme`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology

set_option autoImplicit false

universe u

noncomputable section

section Invariance

variable {k : Type u} [Field k]

/-- **The local contribution `dim_k (B / A)_𝔭` is invariant under isomorphisms of `B`**: for a
ring isomorphism `e : B₁ ≃ B₂` with `e ∘ φ₁ = φ₂`, `δ_{φ₁}(𝔭) = δ_{φ₂}(𝔭)`. -/
theorem deltaAt_eq_of_ringEquiv {A B₁ B₂ : Type*} [CommRing A] [CommRing B₁] [CommRing B₂]
    (ψ : k →+* A) (φ₁ : A →+* B₁) (φ₂ : A →+* B₂) (e : B₁ ≃+* B₂) (h : ∀ a, e (φ₁ a) = φ₂ a)
    (q : PrimeSpectrum A) : deltaAt ψ φ₁ q = deltaAt ψ φ₂ q := by
  have hcomm : φ₂.comp (RingHom.id A) = (e : B₁ →+* B₂).comp φ₁ := by
    ext a
    exact (h a).symm
  have hρ : letI := (RingHom.id A).toAlgebra; IsLocalization.Away (1 : A) A := by
    let := (RingHom.id A).toAlgebra
    exact IsLocalization.away_of_isUnit_of_bijective A isUnit_one Function.bijective_id
  have hσ : letI := (e : B₁ →+* B₂).toAlgebra; IsLocalization.Away (φ₁ 1) B₂ := by
    let := (e : B₁ →+* B₂).toAlgebra
    exact IsLocalization.away_of_isUnit_of_bijective B₂ (by rw [map_one]; exact isUnit_one)
      e.bijective
  have key := deltaAt_away ψ φ₁ (RingHom.id A) (e : B₁ →+* B₂) φ₂ hcomm 1 hρ hσ q
  rw [RingHom.id_comp] at key
  rw [key]
  exact congrArg _ (PrimeSpectrum.ext (Ideal.comap_id _).symm)

/-- **The local contribution is invariant under isomorphisms of `A`**: for a ring isomorphism
`α : A → A'` and a prime `𝔮` of `A'`, `δ_{φ}(𝔮) = δ_{φ ∘ α}(α⁻¹𝔮)` (with the constants
transported along `α`). -/
theorem deltaAt_comp_bijective {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    (ψ : k →+* A) (α : A →+* A') (hα : Function.Bijective α) (φ : A' →+* B)
    (q : PrimeSpectrum A') :
    deltaAt (α.comp ψ) φ q =
      deltaAt ψ (φ.comp α) ⟨q.asIdeal.comap α, Ideal.comap_isPrime α q.asIdeal⟩ := by
  have hρ : letI := α.toAlgebra; IsLocalization.Away (1 : A) A' := by
    let := α.toAlgebra
    exact IsLocalization.away_of_isUnit_of_bijective A' isUnit_one hα
  have hσ : letI := (RingHom.id B).toAlgebra; IsLocalization.Away ((φ.comp α) 1) B := by
    let := (RingHom.id B).toAlgebra
    exact IsLocalization.away_of_isUnit_of_bijective B (by rw [map_one]; exact isUnit_one)
      Function.bijective_id
  exact deltaAt_away ψ (φ.comp α) α (RingHom.id B) φ (RingHom.id_comp _).symm 1 hρ hσ q

/-- **The δ-invariant only sees an open subscheme containing the preimage**: if `j : Y' → Y` is
an open immersion and `π⁻¹(W) ⊆ j(Y')` for an open `W ∋ x`, then `δ_{j ≫ π}(x) = δ_π(x)`. -/
theorem deltaInvariant_eq_of_isOpenImmersion {X Y Y' : Scheme.{u}} (π : Y ⟶ X) (j : Y' ⟶ Y)
    [IsOpenImmersion j] (π₂ : Y' ⟶ X) (hj : j ≫ π = π₂) [IsAffineHom π] [IsAffineHom π₂]
    (c : k →+* Γ(X, ⊤)) (x : X) (W : X.Opens) (hxW : x ∈ W) (hW : π ⁻¹ᵁ W ≤ j.opensRange) :
    deltaInvariant π₂ c x = deltaInvariant π c x := by
  subst hj
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  rw [← chartDelta_eq_deltaInvariant (π := j ≫ π) V hV x hxV,
    ← chartDelta_eq_deltaInvariant (π := π) V hV x hxV]
  have hle : π ⁻¹ᵁ V ≤ j.opensRange := (π.preimage_mono hVW).trans hW
  have : IsIso (j.app (π ⁻¹ᵁ V)) := Scheme.Hom.isIso_app j _ hle
  exact (deltaAt_eq_of_ringEquiv _ _ _ (asIso (j.app (π ⁻¹ᵁ V))).commRingCatIsoToRingEquiv
    (fun _ => rfl) _).symm

/-- **The δ-invariant is unchanged by an isomorphism over an open**: if `f : C' → C` is an
isomorphism over `U` and `f y ∈ U`, then `δ_π(y) = δ_{π ≫ f}(f y)` (constants pulled back along
`f`). -/
theorem deltaInvariant_comp_of_isIso {N C' C : Scheme.{u}} (π : N ⟶ C') (f : C' ⟶ C)
    (U : C.Opens) [IsIso (f ∣_ U)] [IsAffineHom π] [IsAffineHom (π ≫ f)] (c : k →+* Γ(C, ⊤))
    (y : C') (hy : f y ∈ U) :
    deltaInvariant π (f.appTop.hom.comp c) y = deltaInvariant (π ≫ f) c (f y) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  have hVU' : V ≤ U := hVU
  have hV' : IsAffineOpen (f ⁻¹ᵁ V) := isAffineOpen_preimage_of_le f U hVU' hV
  have hyV' : y ∈ f ⁻¹ᵁ V := hyV
  rw [← chartDelta_eq_deltaInvariant (π := π ≫ f) V hV (f y) hyV,
    ← chartDelta_eq_deltaInvariant (π := π) (f ⁻¹ᵁ V) hV' y hyV']
  have := isIso_app_of_le f U hVU'
  have hbij : Function.Bijective (f.app V).hom := ConcreteCategory.bijective_of_isIso _
  have key := deltaAt_comp_bijective (sectionsRingHom c (le_top : V ≤ ⊤)) (f.app V).hom hbij
    (π.app (f ⁻¹ᵁ V)).hom (hV'.primeIdealOf ⟨y, hyV'⟩)
  have hc : (f.app V).hom.comp (sectionsRingHom c (le_top : V ≤ ⊤)) =
      sectionsRingHom (f.appTop.hom.comp c) (le_top : f ⁻¹ᵁ V ≤ ⊤) := by
    have := f.naturality (homOfLE (le_top : V ≤ ⊤)).op
    ext a
    exact congrArg (fun φ => φ.hom (c a)) this
  have hq : (⟨(hV'.primeIdealOf ⟨y, hyV'⟩).asIdeal.comap (f.app V).hom,
      Ideal.comap_isPrime _ _⟩ : PrimeSpectrum Γ(C, V)) = hV.primeIdealOf ⟨f y, hyV⟩ := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) V hV (f ⁻¹ᵁ V) hV' le_rfl hyV'
    rw [Scheme.Hom.appLE_eq_app] at h
    rw [← h]
    rfl
  unfold chartDelta
  rw [hc, hq] at key
  exact key

end Invariance

section Contraction

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (x : C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ≠ x)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

include hU in
/-- **The local comparison off `Z = f⁻¹(x)`**: for `S = S'' ∪ T` with `T` a finite set of points
of `Z` (e.g. the generic points of `C'` in `Z`), and `y' ∉ Z`, the δ-invariant of
`C̃'_S → C'` at `y'` equals that of `b : N → C` at `f y'`. -/
theorem deltaInvariant_normalizationPoints_eq_outer (S T : Set C') [Finite S] [Finite T]
    (hS : S = outerPoints f x ∪ T) (hd : Disjoint (outerPoints f x) T) (hT : ∀ v ∈ T, f v = x)
    (hx : IsClosed {x}) [IsAffineHom (outerMap f x)] (c : k →+* Γ(C, ⊤)) (y : C')
    (hy : f y ≠ x) :
    deltaInvariant (normalizationPointsMap S) (f.appTop.hom.comp c) y =
      deltaInvariant (outerMap f x) c (f y) := by
  subst hS
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_opensRange_pointsIncl hd)
  obtain ⟨jU, jV, _, _, hjU, hjV, -, hcov⟩ := exists_normalization_split
    (pointsMap C' (outerPoints f x ∪ T)) _ _ (pointsMap C' (outerPoints f x)) (pointsMap C' T)
    (pointsIncl_pointsMap _) (pointsIncl_pointsMap _) e
  have hyU : f y ∈ U := (hU _).2 hy
  refine (deltaInvariant_eq_of_isOpenImmersion _ jU _ hjU _ y (f ⁻¹ᵁ U) hyU ?_).symm.trans
    (deltaInvariant_comp_of_isIso (normalizationPointsMap (outerPoints f x)) f U c y hyU)
  intro z hz
  have hz' : z ∈ jU.opensRange ⊔ jV.opensRange := by
    rw [hcov]
    trivial
  rcases Opens.mem_sup.1 hz' with h | ⟨w, rfl⟩
  · exact h
  · exfalso
    have hcl : closure T ⊆ f ⁻¹' {x} :=
      closure_minimal (fun v hv => hT v hv) (hx.preimage f.continuous)
    have hw : normalizationPointsMap T w ∈ closure T :=
      range_normalizationPointsMap_subset T ⟨w, rfl⟩
    have h0 : normalizationPointsMap (outerPoints f x ∪ T) (jV w) = normalizationPointsMap T w := by
      rw [show normalizationPointsMap T = jV ≫ normalizationPointsMap (outerPoints f x ∪ T) from
        hjV.symm]
      exact (Scheme.Hom.comp_apply _ _ _).symm
    have h1 : f (normalizationPointsMap (outerPoints f x ∪ T) (jV w)) = x := by
      rw [h0]
      exact hcl hw
    exact (hU _).1 hz h1

include hU in
/-- **The δ-count of a contraction** (Temkin, Corollary B.2, `semi-stable.tex` l. 4442–4444, at
the scheme level). Let `f : C' → C` be a proper morphism of reduced curves (dimension `≤ 1`),
projective over a field `k` compatibly (`f ≫ p = p'`), which is an isomorphism over
`U = C ∖ {x}` for a closed point `x` that is not a generic point of `C`. Let `G` be the set of
generic points of `C'` mapping to `x` (the components of `Z = f⁻¹(x)`), `δ'` the δ-invariant of
the normalization `C̃' → C'` and `δ_b` that of `b : N → C`, `N` the normalization of `C'` in its
other generic points. Then both δ-invariants have finite support and
`δ_b(x) = ∑ᶠ_{z ∈ Z} δ'(z) + ∑_{v ∈ G} g(v) - |G| + (p_a(C) - p_a(C'))`. -/
theorem deltaInvariant_contraction [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) :
    (Function.support (deltaInvariant (outerMap f x) (structureCoeff p))).Finite ∧
      (Function.support (deltaInvariant (normalizationPointsMap (genericPoints C'))
        (structureCoeff p'))).Finite ∧
      (deltaInvariant (outerMap f x) (structureCoeff p) x : ℤ) =
        ((∑ᶠ y ∈ f ⁻¹' {x}, deltaInvariant (normalizationPointsMap (genericPoints C'))
            (structureCoeff p') y : ℕ) : ℤ) +
          ∑ v ∈ G, componentGenus (structureCoeff p') v - G.card +
            (arithmeticGenus C (structureCoeff p) - arithmeticGenus C' (structureCoeff p')) := by
  subst hfp
  have hc : structureCoeff (f ≫ p) = f.appTop.hom.comp (structureCoeff p) := rfl
  have := isFinite_outerNormalization f x U hU (f ≫ p) hdim' hx
  have hXC : ∀ i, FiniteDimensional k
      (cohomology (SheafOfModules.unit C.ringCatSheaf) (structureCoeff p) i) := fun i =>
    finite_cohomology_of_isProjectiveOver hp (SheafOfModules.unit C.ringCatSheaf)
      (fun V _ => Module.Finite.self Γ(C, V)) i
  obtain ⟨-, hsuppb, hb⟩ := eulerChar_eq_add_finsum_delta (outerMap f x) (structureCoeff p)
    (fun V hV => outerMap_app_injective f x U hU hxg V hV)
    (fun V hV => outerMap_isFiniteCoker f x U hU (f ≫ p) p hxg hdim hdim' hx V hV) hXC
  obtain ⟨hfin', hsupp', hpa'⟩ :=
    arithmeticGenus_eq_normalizationPoints (f ≫ p) (genericPoints C') rfl hdim' hp'
  have hS : genericPoints C' = outerPoints f x ∪ (G : Set C') := by
    rw [hG, outerPoints_union_innerPoints]
  have hd : Disjoint (outerPoints f x) (G : Set C') := hG ▸ disjoint_outerPoints_innerPoints f x
  rw [hc] at hfin' hsupp' hpa' ⊢
  obtain ⟨-, hfinG, hsplit⟩ := eulerChar_normalizationPoints_union (genericPoints C')
    (outerPoints f x) (G : Set C') hS hd (f.appTop.hom.comp (structureCoeff p)) hfin'
  obtain ⟨-, hsum⟩ := eulerChar_normalizationPoints_eq_sum G
    (f.appTop.hom.comp (structureCoeff p)) hfinG
  have hloc : ∀ y : C', f y ≠ x →
      deltaInvariant (normalizationPointsMap (genericPoints C'))
          (f.appTop.hom.comp (structureCoeff p)) y =
        deltaInvariant (outerMap f x) (structureCoeff p) (f y) := fun y hy =>
    deltaInvariant_normalizationPoints_eq_outer f x U hU (genericPoints C') (G : Set C') hS hd
      (fun v hv => by rw [hG] at hv; exact hv.2) hx (structureCoeff p) y hy
  set δ' := deltaInvariant (normalizationPointsMap (genericPoints C'))
    (f.appTop.hom.comp (structureCoeff p)) with hδ'
  set δb := deltaInvariant (outerMap f x) (structureCoeff p) with hδb
  have h1 : ∑ᶠ y, δ' y = (∑ᶠ y ∈ f ⁻¹' {x}, δ' y) + ∑ᶠ y ∈ (f ⁻¹' {x})ᶜ, δ' y := by
    rw [← finsum_mem_univ, ← Set.union_compl_self (f ⁻¹' {x})]
    exact finsum_mem_union' disjoint_compl_right (hsupp'.subset Set.inter_subset_right)
      (hsupp'.subset Set.inter_subset_right)
  have h2 : ∑ᶠ y, δb y = δb x + ∑ᶠ y ∈ ({x} : Set C)ᶜ, δb y := by
    rw [← finsum_mem_univ, ← Set.union_compl_self ({x} : Set C),
      finsum_mem_union' disjoint_compl_right (hsuppb.subset Set.inter_subset_right)
        (hsuppb.subset Set.inter_subset_right), finsum_mem_singleton]
  have h3 : ∑ᶠ y ∈ (f ⁻¹' {x})ᶜ, δ' y = ∑ᶠ y ∈ ({x} : Set C)ᶜ, δb y := by
    refine finsum_mem_eq_of_bijOn f ⟨fun y hy => hy, fun y₁ h₁ y₂ h₂ h => ?_, fun y hy => ?_⟩
      fun y hy => hloc y hy
    · exact injOn_of_isIso_morphismRestrict f U ((hU _).2 h₁) ((hU _).2 h₂) h
    · obtain ⟨y', hy'⟩ := exists_eq_of_isIso_morphismRestrict f U ((hU _).2 hy)
      exact ⟨y', show f y' ≠ x from hy' ▸ hy, hy'⟩
  have hb' : eulerChar (normalizationPoints (outerPoints f x))
      ((normalizationPointsMap (outerPoints f x)).appTop.hom.comp
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

include hU in
/-- **Temkin's identity `g(x) = ∑_{z ∈ Z} g(z) - |Z⁰|`** (Corollary B.2, `semi-stable.tex`
l. 4442–4444): under the hypotheses of `deltaInvariant_contraction` and `p_a(C') = p_a(C)`,
`δ_b(x) = ∑ᶠ_{z ∈ Z} δ'(z) + ∑_{v ∈ Z⁰} g(v) - |Z⁰|` (`δ'` vanishes at the generic points
`v ∈ Z⁰`, `deltaInvariant_eq_zero_of_mem_genericPoints`, so the first sum runs over the closed
points of `Z`). -/
theorem deltaInvariant_contraction_of_arithmeticGenus_eq [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) :
    (deltaInvariant (outerMap f x) (structureCoeff p) x : ℤ) =
      ((∑ᶠ y ∈ f ⁻¹' {x}, deltaInvariant (normalizationPointsMap (genericPoints C'))
          (structureCoeff p') y : ℕ) : ℤ) +
        ∑ v ∈ G, componentGenus (structureCoeff p') v - G.card := by
  rw [(deltaInvariant_contraction f x U hU p p' hfp hxg hx hdim hdim' hp hp' G hG).2.2, hpa,
    sub_self, add_zero]

include hU in
/-- **The δ-count in incidence-graph form**: under the hypotheses of
`deltaInvariant_contraction_of_arithmeticGenus_eq`, if the components of `Z` correspond to the
vertices `Y` of an incidence graph `Γ` with the same genera, and the δ-invariants of `C'` at the
points of `Z` add up to the number of double points of `Γ` meeting `Y` (as for `C'` semi-stable
along `Z`: `δ' = 1` at the double points, `0` at the smooth points), then `δ_b(x)` is the
contracted δ-count `#∂Y + #inner(Y) + ∑_{v ∈ Y} g(v) - #Y` of `Γ` along `Y`
(`contractedDelta`, the hypothesis `hδ` of `stabdown_gluing_iff_of_isAlgClosed` and
`stabdown_iff`). -/
theorem deltaInvariant_contraction_eq_contractedDelta [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) {V E M : Type*} [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M] (Γ : IncidenceGraph V E M)
    (Y : Finset V) (hcard : G.card = Y.card)
    (hgen : ∑ v ∈ G, componentGenus (structureCoeff p') v = ∑ w ∈ Y, (Γ.genus w : ℤ))
    (hpts : ((∑ᶠ y ∈ f ⁻¹' {x}, deltaInvariant (normalizationPointsMap (genericPoints C'))
        (structureCoeff p') y : ℕ) : ℤ) = (Γ.boundary Y).card + (Γ.inner Y).card) :
    (deltaInvariant (outerMap f x) (structureCoeff p) x : ℤ) = contractedDelta Γ Y := by
  rw [deltaInvariant_contraction_of_arithmeticGenus_eq f x U hU p p' hfp hxg hx hdim hdim' hp hp'
    hpa G hG, hpts, hgen, hcard, contractedDelta]

end Contraction

end

end DeJongAlterations.StableModification.CurvesField.Genus
