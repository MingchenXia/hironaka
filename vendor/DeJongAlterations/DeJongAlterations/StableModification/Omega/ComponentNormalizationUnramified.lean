/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.ComponentNormalization
import DeJongAlterations.StableModification.Omega.PoleChart
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricCor
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The normalization of a nodal curve over `k = k̄` is unramified

Let `C` be a reduced curve over an algebraically closed field `k` whose closed points are smooth
points or ordinary double points (a geometric fibre of a nodal curve). Then the normalization
`π : C̃ → C` (Codex's `normalizationPoints (genericPoints C)`) is formally unramified
(`formallyUnramified_normalizationPointsMap`), and so is the normalization `C̃_η → C` of each
irreducible component (`formallyUnramified_normalizationPointsMap_singleton`).

The algebraic input is CRV4's gluing form of a node and of a smooth point
(`CurvesField.eq_gluing_of_isGeometricOrdinaryDoublePoint`, `CurvesField.eq_gluing_of_isSmoothAt`;
Temkin, `semi-stable.tex`, App. B, l. 4381–4397): at a closed point `x` with maximal ideal `P` of
`R = Γ(V, 𝒪_C)`, the image `A` of `R_P` in the semilocal ring `B_P` of the normalization is the
gluing ring `k + J(B_P)`. Hence `P A = J(B_P)` and, at each maximal ideal `M` of `B` over `P`,
`P B_M = M B_M` (`map_eq_maximalIdeal_of_eq_gluing`): the residue fields being `k`, `R → B` is
unramified at `M`.

Blueprint: `sm-omega-component-degree.tex`, `lem:sm-omega-cd-unramified`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

noncomputable section

namespace DeJongAlterations.StableModification.Omega.ComponentNormalization

section Ring

open CurvesField CurvesField.OrdinaryCompletion

variable {k : Type u} [Field k] {R B : Type u} [CommRing R] [CommRing B] [Algebra k R]
  [Algebra R B] [Algebra k B] [IsScalarTower k R B] (P : Ideal R) [P.IsMaximal]

local notation "Rₚ" => Localization.AtPrime P
local notation "Bₚ" => Localization (Algebra.algebraMapSubmonoid B P.primeCompl)

/-- **Gluing form implies `P B_M = M B_M`, elementwise.** If the image of `R_P` in the semilocal
ring `B_P` (finitely many maximal ideals) is the gluing ring of `B_P`, then for every maximal
ideal `M` of `B` over `P` and `x ∈ M`, the image of `x` in `B_M` lies in `P B_M`. -/
theorem algebraMap_mem_map_of_eq_gluing [Finite (MaximalSpectrum Bₚ)]
    (hglue : rangeIn k Rₚ Bₚ = gluing k Bₚ) (M : Ideal B) [M.IsMaximal]
    (hM : M.comap (algebraMap R B) = P) {x : B} (hx : x ∈ M) :
    algebraMap B (Localization.AtPrime M) x ∈ P.map (algebraMap R (Localization.AtPrime M)) := by
  classical
  set S := Algebra.algebraMapSubmonoid B P.primeCompl with hSdef
  have hMS : Disjoint (S : Set B) (M : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrM
    exact hr (by rw [← hM]; exact hrM)
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint S Bₚ M inferInstance hMS
  -- for each maximal ideal `N` of `B_P` not over `M`, an element of `N ∩ B` outside `M`
  have hsep : ∀ N : MaximalSpectrum Bₚ, N.asIdeal.comap (algebraMap B Bₚ) ≠ M →
      ∃ s ∈ N.asIdeal.comap (algebraMap B Bₚ), s ∉ M := by
    intro N hN
    by_contra h
    push Not at h
    apply hN
    have hle : N.asIdeal ≤ M.map (algebraMap B Bₚ) := by
      intro n hn
      obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective S n
      dsimp only at hn ⊢
      have hb : b ∈ N.asIdeal.comap (algebraMap B Bₚ) := by
        rw [Ideal.mem_comap, ← IsLocalization.mk'_spec Bₚ b t]
        exact N.asIdeal.mul_mem_right _ hn
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h b hb))
    have heq : N.asIdeal = M.map (algebraMap B Bₚ) := N.isMaximal.eq_of_le hprime.ne_top hle
    rw [heq]
    exact IsLocalization.under_map_of_isPrime_disjoint S Bₚ inferInstance hMS
  choose s hsN hsM using hsep
  let T := {N : MaximalSpectrum Bₚ // N.asIdeal.comap (algebraMap B Bₚ) ≠ M}
  let : Fintype T := Fintype.ofFinite T
  obtain ⟨σ, hσdef⟩ : ∃ σ : B, σ = ∏ N : T, s N.1 N.2 := ⟨_, rfl⟩
  have hσM : σ ∉ M := by
    rw [hσdef]
    intro h
    obtain ⟨N, -, hN⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hsM N.1 N.2 hN
  have hσx : ∀ N : MaximalSpectrum Bₚ, algebraMap B Bₚ (σ * x) ∈ N.asIdeal := by
    intro N
    rw [map_mul]
    by_cases hN : N.asIdeal.comap (algebraMap B Bₚ) = M
    · apply Ideal.mul_mem_left
      rw [← Ideal.mem_comap, hN]
      exact hx
    · apply Ideal.mul_mem_right
      rw [← Ideal.mem_comap, hσdef, ← Finset.mul_prod_erase Finset.univ _
        (Finset.mem_univ (⟨N, hN⟩ : T))]
      exact Ideal.mul_mem_right _ _ (hsN N hN)
  -- so `σ x` comes from `R_P`
  have hglu : algebraMap B Bₚ (σ * x) ∈ gluing k Bₚ :=
    ⟨0, fun N => by rw [map_zero, sub_zero]; exact hσx N⟩
  rw [← hglue] at hglu
  obtain ⟨a, ha⟩ := hglu
  change algebraMap Rₚ Bₚ a = _ at ha
  obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
  dsimp only at ha
  have hσxM : algebraMap B Bₚ (σ * x) ∈ M.map (algebraMap B Bₚ) :=
    Ideal.mem_map_of_mem _ (M.mul_mem_left σ hx)
  -- `r ∈ P`
  have hr : r ∈ P := by
    rw [← IsLocalization.AtPrime.mk'_mem_maximal_iff Rₚ P r u]
    by_contra hnot
    have hunit : IsUnit (IsLocalization.mk' Rₚ r u) := IsLocalRing.notMem_maximalIdeal.mp hnot
    have := hunit.map (algebraMap Rₚ Bₚ)
    rw [ha] at this
    exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hσxM this)
  -- the equation in `B`
  rw [IsLocalization.algebraMap_mk' B Rₚ Bₚ, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul,
    IsLocalization.eq_iff_exists S Bₚ] at ha
  obtain ⟨⟨_, w, hw, rfl⟩, hw'⟩ := ha
  -- invert in `B_M`
  have hunitB : ∀ b : B, b ∉ M → IsUnit (algebraMap B (Localization.AtPrime M) b) := fun b hb =>
    IsLocalization.map_units (Localization.AtPrime M) (⟨b, hb⟩ : M.primeCompl)
  have hRM : ∀ c : R, c ∉ P → algebraMap R B c ∉ M := fun c hc h => hc (by rw [← hM]; exact h)
  have hvM : algebraMap R B w * σ * algebraMap R B u ∉ M := by
    intro h
    rcases (inferInstance : M.IsPrime).mem_or_mem h with h | h
    · rcases (inferInstance : M.IsPrime).mem_or_mem h with h | h
      · exact hRM w hw h
      · exact hσM h
    · exact hRM u u.2 h
  obtain ⟨v, hv⟩ := hunitB _ hvM
  have key : (v : Localization.AtPrime M) * algebraMap B (Localization.AtPrime M) x =
      algebraMap B (Localization.AtPrime M) (algebraMap R B w) *
        algebraMap R (Localization.AtPrime M) r := by
    rw [hv, IsScalarTower.algebraMap_apply R B (Localization.AtPrime M) r, ← map_mul, ← map_mul]
    congr 1
    change algebraMap R B w * algebraMap R B r =
      algebraMap R B w * (σ * x * algebraMap R B u) at hw'
    linear_combination -hw'
  have hx' : algebraMap B (Localization.AtPrime M) x = ↑v⁻¹ *
      (algebraMap B (Localization.AtPrime M) (algebraMap R B w) *
        algebraMap R (Localization.AtPrime M) r) := by
    rw [← key, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hx']
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr))

/-- **Gluing form implies `P B_M = M B_M`.** -/
theorem map_eq_maximalIdeal_of_eq_gluing [Finite (MaximalSpectrum Bₚ)]
    (hglue : rangeIn k Rₚ Bₚ = gluing k Bₚ) (M : Ideal B) [M.IsMaximal]
    (hM : M.comap (algebraMap R B) = P) :
    P.map (algebraMap R (Localization.AtPrime M)) = maximalIdeal (Localization.AtPrime M) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R B,
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ M, ← Ideal.mem_comap, hM]
    exact hr
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    exact algebraMap_mem_map_of_eq_gluing P hglue M hM hx

/-- **Gluing form implies unramified** at the maximal ideals over `P`, for `B` of finite type over
`k = k̄`. -/
theorem isUnramifiedAt_of_eq_gluing [IsAlgClosed k] [Algebra.FiniteType k B]
    [Algebra.EssFiniteType R B] [Finite (MaximalSpectrum Bₚ)]
    (hglue : rangeIn k Rₚ Bₚ = gluing k Bₚ) (M : Ideal B) [M.IsMaximal]
    (hM : M.comap (algebraMap R B) = P) : Algebra.IsUnramifiedAt R M := by
  have : M.LiesOver P := ⟨hM.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver P M
  rw [Algebra.isUnramifiedAt_iff_map_eq R P M]
  refine ⟨?_, map_eq_maximalIdeal_of_eq_gluing P hglue M hM⟩
  let := Ideal.Quotient.field P
  let := Ideal.Quotient.field M
  rw [Algebra.isSeparable_residueField_iff]
  have hq := (PoleChart.bijective_algebraMap_quotient (K := k) M).2
  have hsurj : Function.Surjective (algebraMap (R ⧸ P) (B ⧸ M)) := by
    intro z
    obtain ⟨c, hc⟩ := hq z
    refine ⟨Ideal.Quotient.mk P (algebraMap k R c), ?_⟩
    rw [← hc]
    change Ideal.Quotient.mk M (algebraMap R B (algebraMap k R c)) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  exact ⟨fun z => by obtain ⟨a, rfl⟩ := hsurj z; exact isSeparable_algebraMap a⟩

omit [Algebra k R] [Algebra k B] [IsScalarTower k R B] in
/-- **Unramified at all maximal ideals implies formally unramified** (the support of `Ω_{B/R}` is
stable under specialization). -/
theorem formallyUnramified_of_forall_isMaximal
    (h : ∀ (M : Ideal B) [M.IsMaximal], Algebra.IsUnramifiedAt R M) :
    Algebra.FormallyUnramified R B := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro p
  by_contra hp
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff, not_not] at hp
  obtain ⟨M, hM, hpM⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  have hM' : (⟨M, hM.isPrime⟩ : PrimeSpectrum B) ∈ Module.support B Ω[B⁄R] :=
    Module.mem_support_mono (q := ⟨M, hM.isPrime⟩) hpM hp
  have hMu : (⟨M, hM.isPrime⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus R B := h M
  rw [Algebra.unramifiedLocus_eq_compl_support] at hMu
  exact hMu hM'

end Ring

section Scheme

open CurvesField CurvesField.Genus CurvesField.OrdinaryCompletion Cohomology

variable {C : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from C))]
  [Finite (genericPoints C)] [IsReduced C] {k : Type u} [Field k] [IsAlgClosed k]
  (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

omit [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
  [IsAlgClosed k] in
include p in
/-- A maximal ideal of `Γ(V, 𝒪_C)` (`V` affine) is a closed point of `C`, for `C` locally of finite
type over a field. -/
theorem isClosed_fromSpec_of_isMaximal {V : C.Opens} (hV : IsAffineOpen V)
    (P : PrimeSpectrum Γ(C, V)) (hP : P.asIdeal.IsMaximal) :
    IsClosed ({hV.fromSpec P} : Set C) := by
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  refine isClosed_singleton_of_isLocallyClosed_singleton ?_
  have h1 : IsClosed ({P} : Set (PrimeSpectrum Γ(C, V))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mpr hP
  have h2 : IsLocallyClosed (hV.fromSpec '' ({P} : Set (Spec Γ(C, V)))) :=
    IsLocallyClosed.image h1.isLocallyClosed hV.fromSpec.isOpenEmbedding.isInducing
      hV.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
  convert h2 using 1
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_image]
  exact ⟨fun h => ⟨P, rfl, h.symm⟩, fun ⟨_, h, h'⟩ => h ▸ h'.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The normalization of a nodal curve over `k = k̄` is unramified, on sections**: for `V ⊆ C`
affine, `Γ(V, 𝒪_C) → Γ(π⁻¹ V, 𝒪_{C̃})` is formally unramified. -/
theorem formallyUnramified_app_normalizationPointsMap (hdim : topologicalKrullDim C ≤ 1)
    (hgen : ∀ z : C, IsClosed ({z} : Set C) → z ∉ genericPoints C)
    (hnodes : ∀ z : C, IsClosed ({z} : Set C) →
      z ∈ p.smoothLocus ∨ Geometry.IsGeometricOrdinaryDoublePoint p z)
    {V : C.Opens} (hV : IsAffineOpen V) :
    ((normalizationPointsMap (genericPoints C)).app V).hom.FormallyUnramified := by
  have : IsFinite (normalizationPointsMap (genericPoints C)) :=
    isFinite_normalizationPointsMap (S := genericPoints C) p
  let := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
  let := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
    (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
      normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite Γ(C, V) Γ(normalizationPoints (genericPoints C),
      normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
    IsFinite.finite_app (normalizationPointsMap (genericPoints C)) V hV
  have : Algebra.FiniteType k Γ(C, V) :=
    Geometry.NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
  have : Algebra.FiniteType k Γ(normalizationPoints (genericPoints C),
      normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
    Algebra.FiniteType.trans (S := Γ(C, V)) inferInstance inferInstance
  change Algebra.FormallyUnramified Γ(C, V) Γ(normalizationPoints (genericPoints C),
    normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
  refine formallyUnramified_of_forall_isMaximal fun M _ => ?_
  have hPmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := Γ(C, V)) M
  let z := hV.fromSpec ⟨_, hPmax.isPrime⟩
  have hzV : z ∈ V := by
    have := Set.mem_range_self (f := hV.fromSpec) ⟨_, hPmax.isPrime⟩
    rwa [hV.range_fromSpec] at this
  have hPz : (hV.primeIdealOf ⟨z, hzV⟩).asIdeal = M.comap (algebraMap _ _) := by
    rw [hV.primeIdealOf_fromSpec]
  have hzc : IsClosed ({z} : Set C) := isClosed_fromSpec_of_isMaximal p hV _ hPmax
  have hzg := hgen z hzc
  have : (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.IsMaximal := by rw [hPz]; exact hPmax
  rcases hnodes z hzc with hsm | hnode
  · obtain ⟨hcard, hglue⟩ := eq_gluing_of_isSmoothAt p hdim z hzc hzg hsm V hV hzV
    have : Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl))) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact one_ne_zero)
    exact isUnramifiedAt_of_eq_gluing (k := k) _ hglue M hPz.symm
  · obtain ⟨hcard, hglue⟩ :=
      eq_gluing_of_isGeometricOrdinaryDoublePoint p hdim z hzc hzg hnode V hV hzV
    have : Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl))) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact two_ne_zero)
    exact isUnramifiedAt_of_eq_gluing (k := k) _ hglue M hPz.symm

/-- **The normalization of a nodal curve over `k = k̄` is formally unramified** (blueprint
`lem:sm-omega-cd-unramified`): for a reduced curve `C` over `k = k̄` whose closed points are not
generic and are smooth points or ordinary double points, `π : C̃ → C` is formally unramified. -/
theorem formallyUnramified_normalizationPointsMap (hdim : topologicalKrullDim C ≤ 1)
    (hgen : ∀ z : C, IsClosed ({z} : Set C) → z ∉ genericPoints C)
    (hnodes : ∀ z : C, IsClosed ({z} : Set C) →
      z ∈ p.smoothLocus ∨ Geometry.IsGeometricOrdinaryDoublePoint p z) :
    FormallyUnramified (normalizationPointsMap (genericPoints C)) := by
  have hstable : RingHom.StableUnderCompositionWithLocalizationAwaySource
      RingHom.FormallyUnramified := fun _ S _ _ _ _ _ r _ f hf =>
    RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.holdsForLocalizationAway S r) hf
  rw [HasRingHomProperty.iff_exists_appLE (P := @FormallyUnramified) hstable]
  intro y
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (normalizationPointsMap (genericPoints C) y)) isOpen_univ
  have : IsFinite (normalizationPointsMap (genericPoints C)) :=
    isFinite_normalizationPointsMap (S := genericPoints C) p
  refine ⟨⟨V, hV⟩, ⟨_, hV.preimage (normalizationPointsMap (genericPoints C))⟩, hyV, le_rfl, ?_⟩
  rw [← Scheme.Hom.app_eq_appLE]
  exact formallyUnramified_app_normalizationPointsMap p hdim hgen hnodes hV

/-- **The normalization of a component of a nodal curve over `k = k̄` is formally unramified**:
`C̃_η → C` is the restriction of `π : C̃ → C` to the open and closed subscheme `C̃_η` of
`C̃ = ∐_η C̃_η` (`exists_normalization_split`). -/
theorem formallyUnramified_normalizationPointsMap_singleton (hdim : topologicalKrullDim C ≤ 1)
    (hgen : ∀ z : C, IsClosed ({z} : Set C) → z ∉ genericPoints C)
    (hnodes : ∀ z : C, IsClosed ({z} : Set C) →
      z ∈ p.smoothLocus ∨ Geometry.IsGeometricOrdinaryDoublePoint p z)
    {η : C} (hη : η ∈ genericPoints C) :
    FormallyUnramified (normalizationPointsMap ({η} : Set C)) := by
  have hfull := formallyUnramified_normalizationPointsMap p hdim hgen hnodes
  have hS : genericPoints C = {η} ∪ (genericPoints C \ {η}) :=
    (Set.union_sdiff_cancel (Set.singleton_subset_iff.mpr hη)).symm
  have hd : Disjoint ({η} : Set C) (genericPoints C \ {η}) := Set.disjoint_sdiff_right
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_opensRange_pointsIncl hd)
  obtain ⟨jU, -, _, -, hjU, -⟩ := exists_normalization_split
    (pointsMap C ({η} ∪ (genericPoints C \ {η}))) _ _ (pointsMap C ({η} : Set C))
    (pointsMap C (genericPoints C \ {η})) (pointsIncl_pointsMap _) (pointsIncl_pointsMap _) e
  have hfull' : FormallyUnramified
      (pointsMap C ({η} ∪ (genericPoints C \ {η}))).fromNormalization := by
    have h : ∀ S' : Set C, S' = genericPoints C → ∀ [Finite S'],
        FormallyUnramified (normalizationPointsMap S') := by
      rintro _ rfl _
      exact hfull
    exact h _ hS.symm
  have : FormallyUnramified (jU ≫ (pointsMap C ({η} ∪ (genericPoints C \ {η}))).fromNormalization) :=
    MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hfull'
  rw [hjU] at this
  exact this

end Scheme

end DeJongAlterations.StableModification.Omega.ComponentNormalization
