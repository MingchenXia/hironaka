/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# The charts of a proper curve are finite over the affine line

Let `p : X → Spec R` be universally closed and let `U₀`, `U₁` be affine opens covering `X`, with
`t ∈ Γ(X, U₀)`, `s ∈ Γ(X, U₁)` such that `D(t) = U₀ ∩ U₁ = D(s)` and `t s = 1` on `U₀ ∩ U₁` (the
charts of the map `X → ℙ¹_R` given by `t`; no such map is constructed). Then `Γ(X, U₀)` is
integral over `R[t]`: the map `R[T] → Γ(X, U₀)`, `T ↦ t`, is integral
(`isIntegral_eval₂_of_universallyClosed`).

The proof is the valuative criterion: `Spec Γ(X, U₀) → Spec R[T]` is affine, so it is integral
iff it is universally closed (`IsIntegralHom.iff_universallyClosed_and_isAffineHom`), which is
checked on valuation rings (`UniversallyClosed.of_valuativeCriterion`). A valuative square for it
gives one for `p`, with a lift `ℓ : Spec O → X`; the lift lands in `U₀`, since if the closed point
lands in `U₁` then `ℓ^♯ s` is inverse to the image `β(T)` of `T` in `O` (the generic point lands in
`U₀ ∩ U₁`, where `t s = 1`), hence a unit, so the closed point lands in `D(s) ⊆ U₀`.

This replaces the finiteness of `X → ℙ¹` (proper and quasi-finite) in the classical construction
of the two-chart presentation of a smooth projective curve (blueprint `sm-omega-degree-scheme.tex`,
`lem:sm-chart-integral`; M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), Thm 1.1, `references/temkin10-stable-modification/source/
semi-stable.tex`, lines 1717–1741, the degree of `ω`).
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.StableModification.CurvesField.DualityScheme

noncomputable section

section Valuative

variable {X : Scheme.{u}}

/-- Every point of `Spec O` maps into an open `U` if the closed point does (`O` local). -/
lemma range_subset_of_closedPoint_mem {O : Type u} [CommRing O] [IsLocalRing O]
    (ℓ : Spec (CommRingCat.of O) ⟶ X) {U : X.Opens}
    (hm : ℓ (IsLocalRing.closedPoint O) ∈ U) : Set.range ℓ ⊆ U := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map ℓ.continuous).mem_open U.isOpen hm

end Valuative

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
  [UniversallyClosed p] {U₀ U₁ W : X.Opens} (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
  (h : U₀ ⊔ U₁ = ⊤) (hW₀ : W ≤ U₀) (hW₁ : W ≤ U₁) (hW : U₀ ⊓ U₁ ≤ W) (t : Γ(X, U₀))
  (s : Γ(X, U₁))
  (ht : X.basicOpen t = W) (hs : X.basicOpen s = W)
  (hts : X.presheaf.map (homOfLE hW₀).op t * X.presheaf.map (homOfLE hW₁).op s = 1)
  (ψ : R →+* Γ(X, U₀)) (hψ : h₀.fromSpec ≫ p = Spec.map (CommRingCat.ofHom ψ))

include h₁ h hW₁ hW ht hs hts hψ in
/-- **The valuative criterion for the chart map** `Spec Γ(X, U₀) → Spec R[T]`. -/
theorem valuativeCriterion_existence_chart :
    ValuativeCriterion.Existence
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom ψ t))) := by
  set φ := CommRingCat.ofHom (Polynomial.eval₂RingHom ψ t) with hφ
  intro S
  -- the valuative criterion for `p`
  have Hp : ValuativeCriterion.Existence p := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact this.1
  let C : CommRingCat.of R ⟶ CommRingCat.of (Polynomial R) := CommRingCat.ofHom Polynomial.C
  have hCφ : C ≫ φ = CommRingCat.ofHom ψ := by
    ext r
    simp [C, φ]
  have hsq : (S.i₁ ≫ h₀.fromSpec) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ (S.i₂ ≫ Spec.map C) := by
    rw [Category.assoc, hψ, ← hCφ, Spec.map_comp, ← Category.assoc, S.commSq.w,
      Category.assoc]
  let S' : ValuativeCommSq p :=
    { R := S.R
      K := S.K
      i₁ := S.i₁ ≫ h₀.fromSpec
      i₂ := S.i₂ ≫ Spec.map C
      commSq := ⟨hsq⟩ }
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ := (Hp S').exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ ℓ = S.i₁ ≫ h₀.fromSpec at hℓ₁
  -- ring maps of the given square
  let alg : CommRingCat.of S.R ⟶ CommRingCat.of S.K := CommRingCat.ofHom (algebraMap S.R S.K)
  have halg : Function.Injective alg.hom := IsFractionRing.injective S.R S.K
  obtain ⟨χ, hχ⟩ : ∃ χ, Spec.map χ = S.i₁ := ⟨_, Spec.map_preimage _⟩
  obtain ⟨β, hβ⟩ : ∃ β, Spec.map β = S.i₂ := ⟨_, Spec.map_preimage _⟩
  have hχβ : φ ≫ χ = β ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hχ, hβ]
    exact S.commSq.w
  -- the lift lands in `U₀`
  have hWa : IsAffineOpen W := ht ▸ h₀.basicOpen t
  have hm : ℓ (IsLocalRing.closedPoint S.R) ∈ U₀ := by
    by_contra hm
    have hm₁ : ℓ (IsLocalRing.closedPoint S.R) ∈ U₁ := by
      have : ℓ (IsLocalRing.closedPoint S.R) ∈ U₀ ⊔ U₁ := by rw [h]; trivial
      exact (Opens.mem_sup.mp this).resolve_left hm
    have hr₁ : Set.range ℓ ⊆ Set.range h₁.fromSpec := by
      rw [h₁.range_fromSpec]
      exact range_subset_of_closedPoint_mem ℓ hm₁
    have hℓ₁fac : IsOpenImmersion.lift h₁.fromSpec ℓ hr₁ ≫ h₁.fromSpec = ℓ :=
      IsOpenImmersion.lift_fac _ _ _
    obtain ⟨β₁, hβ₁⟩ : ∃ β₁, Spec.map β₁ = IsOpenImmersion.lift h₁.fromSpec ℓ hr₁ :=
      ⟨_, Spec.map_preimage _⟩
    rw [← hβ₁] at hℓ₁fac
    -- the generic point lands in `U₀ ∩ U₁`
    have heW : Set.range (S.i₁ ≫ h₀.fromSpec) ⊆ Set.range hWa.fromSpec := by
      rw [hWa.range_fromSpec]
      rintro _ ⟨y, rfl⟩
      have hy₀ : (S.i₁ ≫ h₀.fromSpec) y ∈ (U₀ : Set X) := by
        rw [← h₀.range_fromSpec]
        exact ⟨S.i₁ y, rfl⟩
      have hy₁ : (S.i₁ ≫ h₀.fromSpec) y ∈ (U₁ : Set X) := by
        rw [← h₁.range_fromSpec, ← hℓ₁, ← hℓ₁fac]
        exact ⟨Spec.map β₁ (Spec.map alg y), rfl⟩
      exact hW ⟨hy₀, hy₁⟩
    have he'fac : IsOpenImmersion.lift hWa.fromSpec _ heW ≫ hWa.fromSpec = S.i₁ ≫ h₀.fromSpec :=
      IsOpenImmersion.lift_fac _ _ _
    obtain ⟨ω, hω⟩ : ∃ ω, Spec.map ω = IsOpenImmersion.lift hWa.fromSpec _ heW :=
      ⟨_, Spec.map_preimage _⟩
    rw [← hω] at he'fac
    have hres₀ : X.presheaf.map (homOfLE hW₀).op ≫ ω = χ := by
      apply Spec.map_injective
      rw [← cancel_mono h₀.fromSpec, Spec.map_comp, Category.assoc,
        h₀.map_fromSpec hWa (homOfLE hW₀).op, he'fac, hχ]
    have hres₁ : X.presheaf.map (homOfLE hW₁).op ≫ ω = β₁ ≫ alg := by
      apply Spec.map_injective
      rw [← cancel_mono h₁.fromSpec, Spec.map_comp, Category.assoc,
        h₁.map_fromSpec hWa (homOfLE hW₁).op, he'fac, Spec.map_comp,
        Category.assoc, hℓ₁fac, hℓ₁]
    -- `β(T) · ℓ^♯(s) = 1`
    have hunit : IsUnit (β₁.hom s) := by
      have key : alg.hom (β.hom Polynomial.X * β₁.hom s) = alg.hom 1 := by
        rw [map_mul, map_one]
        have e1 : alg.hom (β.hom Polynomial.X) = ω.hom
            (X.presheaf.map (homOfLE hW₀).op t) := by
          rw [← CommRingCat.comp_apply, ← hχβ, ← hres₀]
          simp [φ]
        have e2 : alg.hom (β₁.hom s) = ω.hom
            (X.presheaf.map (homOfLE hW₁).op s) := by
          rw [← CommRingCat.comp_apply, ← hres₁, CommRingCat.comp_apply]
        rw [e1, e2, ← map_mul, hts, map_one]
      exact isUnit_iff_exists_inv.mpr ⟨β.hom Polynomial.X, by rw [mul_comm]; exact halg key⟩
    -- so the closed point lands in `D(s) ⊆ U₀`
    apply hm
    have hmem : Spec.map β₁ (IsLocalRing.closedPoint S.R) ∈ PrimeSpectrum.basicOpen s := by
      change s ∉ (PrimeSpectrum.comap β₁.hom (IsLocalRing.closedPoint S.R)).asIdeal
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, IsLocalRing.closedPoint,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact hunit
    have h' : h₁.fromSpec (Spec.map β₁ (IsLocalRing.closedPoint S.R)) ∈ X.basicOpen s := by
      rw [← Scheme.Hom.mem_preimage, IsAffineOpen.fromSpec_preimage_basicOpen]
      exact hmem
    have : ℓ (IsLocalRing.closedPoint S.R) ∈ X.basicOpen s := by
      rw [← hℓ₁fac]
      exact h'
    rw [hs] at this
    exact hW₀ this
  -- the lift factors through `Spec Γ(X, U₀)`
  have hr₀ : Set.range ℓ ⊆ Set.range h₀.fromSpec := by
    rw [h₀.range_fromSpec]
    exact range_subset_of_closedPoint_mem ℓ hm
  have hℓ'fac : IsOpenImmersion.lift h₀.fromSpec ℓ hr₀ ≫ h₀.fromSpec = ℓ :=
    IsOpenImmersion.lift_fac _ _ _
  have hleft : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫
      IsOpenImmersion.lift h₀.fromSpec ℓ hr₀ = S.i₁ := by
    rw [← cancel_mono h₀.fromSpec, Category.assoc, hℓ'fac, hℓ₁]
  refine ⟨⟨⟨IsOpenImmersion.lift h₀.fromSpec ℓ hr₀, hleft, ?_⟩⟩⟩
  -- `ℓ' ≫ Spec φ = i₂`: the ring maps agree after the injection `O → K`
  obtain ⟨lam, hlam⟩ : ∃ lam, Spec.map lam = IsOpenImmersion.lift h₀.fromSpec ℓ hr₀ :=
    ⟨_, Spec.map_preimage _⟩
  rw [← hlam] at hleft ⊢
  have hlamχ : lam ≫ alg = χ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ]
    exact hleft
  rw [← hβ, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => halg ?_)
  change ((φ ≫ lam) ≫ alg).hom x = (β ≫ alg).hom x
  rw [Category.assoc, hlamχ, hχβ]

include h₁ h hW₁ hW ht hs hts hψ in
/-- **Integrality of a chart over the affine line** (blueprint `lem:sm-chart-integral`): for
`p : X → Spec R` universally closed and charts `U₀`, `U₁` with `D(t) = U₀ ∩ U₁ = D(s)`,
`t s = 1`, the map `R[T] → Γ(X, U₀)`, `T ↦ t`, extending the structure map `ψ` is integral. -/
theorem isIntegral_eval₂_of_universallyClosed : (Polynomial.eval₂RingHom ψ t).IsIntegral := by
  have hU : UniversallyClosed (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom ψ t))) :=
    UniversallyClosed.of_valuativeCriterion _
      (valuativeCriterion_existence_chart p h₀ h₁ h hW₀ hW₁ hW t s ht hs hts ψ hψ)
  have := IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hU, inferInstance⟩
  exact IsIntegralHom.SpecMap_iff.mp this

end

end DeJongAlterations.StableModification.CurvesField.DualityScheme
