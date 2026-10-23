/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL-GLOBAL)
-/
import DeJongAlterations.StableModification.Perfection.GlobalLocal

/-!
# Smoothness and separability at the points over the generic point of the base

Blueprint chapter `sm-dj-perfection-global`, node `lem:sm-dj-perfection-global-points` (new route,
not in de Jong 1996; step (d) of the route of `thm:sm-dj-perfection-global`).

Setting: `X` integral, `M ⊇ K(X)` and `K ⊆ M` fields, `E ⊆ M` algebraic over `K`,
`L = K(X)(E) ⊆ M` finite and purely inseparable over `K(X)`, `X₁ = normalization X L`. Let
`Y₁` be an integral scheme with an identification `e_Y : K(Y₁) ≅ E`, and `g : X₁ ⟶ Y₁` a dominant
morphism inducing the inclusion `E ⊆ L` on function fields (`hg`). In the application `Y₁` is
the normalization of the base in `E` and `g` is Codex's Stein normalization factor.

For a point `x₁ ∈ X₁` with `g x₁` the generic point of `Y₁`, lying in the chart `U` of `X₁`:

* `formallySmooth_stalkMap_of_smooth`: if the normalization `B_E(A_U)` of `E ⊗_K A_U`
  (`A_U = K[Γ(X, U)]`) is smooth over `E`, then `O_{Y₁, g x₁} ⟶ O_{X₁, x₁}` is formally smooth.
* `isSeparable_residueFieldMap_of_isSeparable`: if moreover `B_E(A_U) / P` is separable over `E`
  for the maximal ideals `P` over the ideal `J` of `A_U` of the image `x` of `x₁` in `X`, and `J`
  is maximal, then the residue field extension `κ(g x₁) ⊆ κ(x₁)` is separable.

Proof: the image `T ⊆ M` of `O_{X₁,x₁}` contains `E` (by `hg`, `g x₁` is the generic point), hence
`B_E(A_U)` (`GlobalLocal.normalizationImage_subset_range`), and is a localization of it
(`GlobalLocal.exists_mul_mem_normalizationImage`, `GlobalAlgebra.isLocalization_of_le`);
formal smoothness and separability of residue fields pass to the localization and back to the
local ring map through `T ≅ O_{X₁,x₁}` and `O_{Y₁, g x₁} = K(Y₁) ≅ E`
(`GlobalAlgebra.formallySmooth_of_range`, `isSeparable_residueField_map_of_range`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Perfection

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Geometry Geometry.NormalizationInExtension

/-- At the generic point the local ring is the function field. -/
theorem algebraMap_stalk_bijective_of_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y] {y : Y}
    (hy : y = genericPoint Y) :
    Function.Bijective (algebraMap (Y.presheaf.stalk y) Y.functionField) := by
  have hfield : IsField (Y.presheaf.stalk y) := by
    rw [hy]
    exact Field.toIsField Y.functionField
  exact ⟨IsFractionRing.injective _ _,
    (IsFractionRing.surjective_iff_isField (R := Y.presheaf.stalk y)).mpr hfield⟩

variable {X : Scheme.{u}} [IsIntegral X] {K M : Type u} [Field K] [Field M]
  [Algebra X.functionField M] [Algebra K M]
  (L : IntermediateField X.functionField M) [FiniteDimensional X.functionField L]
  (E : IntermediateField K M)
  {Y₁ : Scheme.{u}} [IsIntegral Y₁] (eY : Y₁.functionField ≃+* E)
  (g : NormalizationInExtension.normalization X L ⟶ Y₁) [IsDominant g]
  (hg : ∀ y, ((normalizationFunctionFieldEquiv (X := X) L ((functionFieldMap g).hom y) : L) : M) =
    (eY y : M))

include hg in
/-- The local ring map of `g` is the inclusion of `E` into the image of the local ring. -/
theorem stalkToAmbient_stalkMap_eq (x₁ : NormalizationInExtension.normalization X L)
    (b : Y₁.presheaf.stalk (g x₁)) :
    stalkToAmbient L x₁ ((g.stalkMap x₁).hom b) =
      (eY (algebraMap (Y₁.presheaf.stalk (g x₁)) Y₁.functionField b) : M) := by
  rw [← hg]
  have h := congrArg (fun φ => φ.hom b) (functionFieldMap_stalk g x₁)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [h]
  rfl

include hg in
theorem stalkToAmbient_comp_stalkMap (x₁ : NormalizationInExtension.normalization X L) :
    (stalkToAmbient L x₁).comp (g.stalkMap x₁).hom =
      (algebraMap E M).comp (eY.toRingHom.comp
        (algebraMap (Y₁.presheaf.stalk (g x₁)) Y₁.functionField)) := by
  ext b
  exact stalkToAmbient_stalkMap_eq L E eY g hg x₁ b

omit [FiniteDimensional X.functionField L] [IsDominant g] in
theorem bijective_eY_comp_algebraMap (x₁ : NormalizationInExtension.normalization X L)
    (hx₁ : g x₁ = genericPoint Y₁) :
    Function.Bijective (eY.toRingHom.comp
      (algebraMap (Y₁.presheaf.stalk (g x₁)) Y₁.functionField)) :=
  eY.bijective.comp (algebraMap_stalk_bijective_of_eq_genericPoint hx₁)

/-- The image in `M` of the local ring of `X₁` at a point over the generic point of `Y₁`, as an
`E`-subalgebra. -/
abbrev localImage (x₁ : NormalizationInExtension.normalization X L) (hx₁ : g x₁ = genericPoint Y₁) :
    Subalgebra E M :=
  rangeSubalgebra (stalkToAmbient L x₁)
    (algebraMap_mem_range_of_comp (g.stalkMap x₁).hom _ _
      (bijective_eY_comp_algebraMap L E eY g x₁ hx₁) (stalkToAmbient_comp_stalkMap L E eY g hg x₁))

theorem mem_localImage (x₁ : NormalizationInExtension.normalization X L)
    (hx₁ : g x₁ = genericPoint Y₁) {m : M} :
    m ∈ localImage L E eY g hg x₁ hx₁ ↔ m ∈ (stalkToAmbient L x₁).range := Iff.rfl

instance (x₁ : NormalizationInExtension.normalization X L) (hx₁ : g x₁ = genericPoint Y₁) :
    IsLocalRing (localImage L E eY g hg x₁ hx₁) :=
  (rangeSubalgebraEquiv (stalkToAmbient L x₁) (stalkToAmbient_injective L x₁) _).isLocalRing

theorem algebraMap_mem_localImage (x₁ : NormalizationInExtension.normalization X L)
    (hx₁ : g x₁ = genericPoint Y₁) {e : M} (he : e ∈ E) :
    e ∈ localImage L E eY g hg x₁ hx₁ :=
  (localImage L E eY g hg x₁ hx₁).algebraMap_mem ⟨e, he⟩

variable [IsPurelyInseparable X.functionField L]

theorem normalizationImage_le_localImage
    (hL : L = IntermediateField.adjoin X.functionField (E : Set M))
    (hEalg : ∀ e ∈ E, IsIntegral K e) (U : NonemptyAffineOpen X)
    (P : Spec (.of (closureRing L U)))
    (hx₁ : g (chartInclusion X L U P) = genericPoint Y₁) :
    normalizationImage (chartAlgebra K M U) E ≤ localImage L E eY g hg _ hx₁ := by
  have hEL : ∀ e ∈ E, e ∈ L := fun e he => by
    rw [hL]
    exact IntermediateField.subset_adjoin _ _ he
  exact fun b hb => normalizationImage_subset_range L E hEL hEalg U P
    (fun e he => algebraMap_mem_localImage L E eY g hg _ hx₁ he) hb

theorem exists_isUnit_mul_mem
    (hL : L = IntermediateField.adjoin X.functionField (E : Set M))
    (hEalg : ∀ e ∈ E, IsIntegral K e) (U : NonemptyAffineOpen X)
    (P : Spec (.of (closureRing L U)))
    (hx₁ : g (chartInclusion X L U P) = genericPoint Y₁)
    (t : localImage L E eY g hg _ hx₁) :
    ∃ c : normalizationImage (chartAlgebra K M U) E,
      IsUnit (Subalgebra.inclusion
        (normalizationImage_le_localImage L E eY g hg hL hEalg U P hx₁) c) ∧
        (t : M) * c ∈ normalizationImage (chartAlgebra K M U) E := by
  obtain ⟨c, hc, ⟨v, hv, hvc⟩, hmem⟩ := exists_mul_mem_normalizationImage L E hL hEalg U P t.2
  exact ⟨⟨c, hc⟩, isUnit_iff_exists_inv'.mpr ⟨⟨v, hv⟩, Subtype.ext hvc⟩, hmem⟩

omit [IsPurelyInseparable X.functionField L] in
theorem formallySmooth_normalizationImage (A : Subalgebra K M)
    [Algebra.Smooth E (Perfection.normalization A E)] :
    Algebra.FormallySmooth E (normalizationImage A E) := by
  let e : Perfection.normalization A E ≃ₐ[E] normalizationImage A E :=
    AlgEquiv.ofInjective (normalizationι A E) (normalizationι_injective _ E)
  have : Algebra.Smooth E (normalizationImage A E) :=
    Algebra.Smooth.of_equiv (A := Perfection.normalization A E) e
  infer_instance

include hg in
/-- **Formal smoothness at the points over the generic point.** If `x₁` lies in the chart `U`
and over the generic point of `Y₁`, and `B_E(A_U)` is smooth over `E`, then the local ring map of
`g` at `x₁` is formally smooth. -/
theorem formallySmooth_stalkMap_of_smooth
    (hL : L = IntermediateField.adjoin X.functionField (E : Set M))
    (hEalg : ∀ e ∈ E, IsIntegral K e) (x₁ : NormalizationInExtension.normalization X L)
    (hx₁ : g x₁ = genericPoint Y₁) (U : NonemptyAffineOpen X)
    (hU : normalizationStructure X L x₁ ∈ U.1.1)
    [Algebra.Smooth E (Perfection.normalization (chartAlgebra K M U) E)] :
    (g.stalkMap x₁).hom.FormallySmooth := by
  have hx₁U : x₁ ∈ (chartInclusion X L U).opensRange := by
    rw [chartInclusion_opensRange]
    exact hU
  obtain ⟨P, rfl⟩ := hx₁U
  have := formallySmooth_normalizationImage E (chartAlgebra K M U)
  have := formallySmooth_of_le (normalizationImage_le_localImage L E eY g hg hL hEalg U P hx₁)
    (exists_isUnit_mul_mem L E eY g hg hL hEalg U P hx₁)
  exact formallySmooth_of_range (g.stalkMap _).hom _ (stalkToAmbient_injective L _) _
    (bijective_eY_comp_algebraMap L E eY g _ hx₁) (stalkToAmbient_comp_stalkMap L E eY g hg _)

omit [IsPurelyInseparable X.functionField L] in
/-- The contraction to `A_U` of the maximal ideal of the local ring at `x₁` is the ideal of the
image point of `x₁` in `X`. -/
theorem comap_contraction_eq_chartIdeal (U : NonemptyAffineOpen X)
    (P : Spec (.of (closureRing L U)))
    (hx₁ : g (chartInclusion X L U P) = genericPoint Y₁)
    (hU : normalizationStructure X L (chartInclusion X L U P) ∈ U.1.1)
    (hK : ∀ c : K, algebraMap K M c ∈
      (stalkToAmbientBase M (normalizationStructure X L (chartInclusion X L U P))).range)
    (hBT : normalizationImage (chartAlgebra K M U) E ≤ localImage L E eY g hg _ hx₁) :
    (contraction hBT).comap (toNormalizationImage (chartAlgebra K M U) E) =
      chartIdeal K U hU hK := by
  ext a
  rw [Ideal.mem_comap, mem_chartIdeal, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_exists_inv']
  have ha : (a : M) ∈ (stalkToAmbientBase M (normalizationStructure X L
      (chartInclusion X L U P))).range := (chartToStalk K U hU hK a).2
  constructor
  · rintro hna ⟨v, hv, hva⟩
    obtain ⟨s, rfl⟩ := hv
    exact hna ⟨⟨_, ⟨_, stalkToAmbient_stalkMap L _ s⟩⟩, Subtype.ext hva⟩
  · rintro hna ⟨⟨v, hv⟩, hva⟩
    exact hna (exists_inv_of_exists_inv L _ ha ⟨v, hv, congrArg Subtype.val hva⟩)

include hg in
/-- **Separable residue fields at the points over the generic point.** If `x₁` lies in the chart
`U` and over the generic point of `Y₁`, the ideal `J` of `A_U` of its image `x ∈ X` is maximal,
and `B_E(A_U) / P` is separable over `E` for the maximal ideals `P` over `J`, then the residue
field extension of `g` at `x₁` is separable. -/
theorem isSeparable_residueFieldMap_of_isSeparable
    (hL : L = IntermediateField.adjoin X.functionField (E : Set M))
    (hEalg : ∀ e ∈ E, IsIntegral K e) (x₁ : NormalizationInExtension.normalization X L)
    (hx₁ : g x₁ = genericPoint Y₁) (U : NonemptyAffineOpen X)
    (hU : normalizationStructure X L x₁ ∈ U.1.1)
    (hK : ∀ c : K, algebraMap K M c ∈
      (stalkToAmbientBase M (normalizationStructure X L x₁)).range)
    (hmax : (chartIdeal K U hU hK).IsMaximal)
    (hsep : ∀ P : Ideal (normalizationImage (chartAlgebra K M U) E), P.IsMaximal →
      P.comap (toNormalizationImage (chartAlgebra K M U) E) = chartIdeal K U hU hK →
      Algebra.IsSeparable E (normalizationImage (chartAlgebra K M U) E ⧸ P)) :
    letI := (g.residueFieldMap x₁).hom.toAlgebra
    Algebra.IsSeparable (Y₁.residueField (g x₁))
      ((NormalizationInExtension.normalization X L).residueField x₁) := by
  have hx₁U : x₁ ∈ (chartInclusion X L U).opensRange := by
    rw [chartInclusion_opensRange]
    exact hU
  obtain ⟨P, rfl⟩ := hx₁U
  have hBT := normalizationImage_le_localImage L E eY g hg hL hEalg U P hx₁
  have hsurj := exists_isUnit_mul_mem L E eY g hg hL hEalg U P hx₁
  have hQA := comap_contraction_eq_chartIdeal L E eY g hg U P hx₁ hU hK hBT
  -- the contraction is maximal: `B_E(A_U)` is integral over `A_U`
  have hQmax : (contraction hBT).IsMaximal := by
    let := (toNormalizationImage (chartAlgebra K M U) E).toAlgebra
    have : Algebra.IsIntegral (chartAlgebra K M U) (normalizationImage (chartAlgebra K M U) E) :=
      ⟨fun b => by
        let j : normalizationImage (chartAlgebra K M U) E →ₐ[chartAlgebra K M U] M :=
          { ((normalizationImage (chartAlgebra K M U) E).val :
              normalizationImage (chartAlgebra K M U) E →+* M) with commutes' := fun _ => rfl }
        rw [← isIntegral_algHom_iff j Subtype.val_injective]
        exact ((mem_range_normalizationι_iff hEalg).1 b.2).2⟩
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := chartAlgebra K M U) _ ?_
    change ((contraction hBT).comap (toNormalizationImage (chartAlgebra K M U) E)).IsMaximal
    rw [hQA]
    exact hmax
  have : Algebra.IsSeparable E (normalizationImage (chartAlgebra K M U) E ⧸ contraction hBT) :=
    hsep _ hQmax hQA
  have := isSeparable_residueField_of_le hBT hsurj
  have : IsLocalRing (localImage L E eY g hg _ hx₁) :=
    (rangeSubalgebraEquiv (stalkToAmbient L _) (stalkToAmbient_injective L _) _).isLocalRing
  exact isSeparable_residueField_map_of_range (g.stalkMap _).hom _ (stalkToAmbient_injective L _) _
    (bijective_eY_comp_algebraMap L E eY g _ hx₁) (stalkToAmbient_comp_stalkMap L E eY g hg _)

end DeJongAlterations.StableModification.Perfection

end
