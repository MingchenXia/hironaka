/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.PoleChartEtale
import DeJongAlterations.Geometry.RegularCurve
import DeJongAlterations.Geometry.NormalizationFinite
import DeJongAlterations.StableModification.Curves.SemistableNormalAlgebra
import DeJongAlterations.StableModification.CurvesField.OrdinaryCompletionLocalization
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Pole charts at the points over the nodes

Blueprint `sm-omega-component-degree.tex`, `lem:sm-omega-cd-pole-chart` (=
`lem:sm-omega-bcf-pole-chart` of `sm-omega-base-change-fibre.tex`): the named hypothesis
`RosenlichtComponent.HasPoleCharts` of lane OM1D holds for every `ν : Y ⟶ X` from a normal,
locally Noetherian integral curve `Y` smooth of relative dimension one over `K = K̄`, lying over a
geometric point of a nodal curve `X ⟶ S` (integral, normal, locally Noetherian base, smooth over
the generic point), provided `ν` is unramified relative to the base change at the points of
`E = ν⁻¹(X ∖ Sm f)` (`hasPoleCharts`).

## Proof

At `y ∈ E`, `x = ν(y)` carries étale node data (`PoleChart.nonempty_nodePoleData`). Near `y`
choose an affine `V` on which `Ω¹_{Y/K}` is free and spanned by the differentials of the image of
`Γ(X, W)` (unramifiedness), a uniformizer `t` of `𝒪_{Y,y}` (`B_𝔫` is a discrete valuation ring,
`isDiscreteValuationRing_localization`) and shrink `V` so that `𝔫 = (t)`, `V ∩ E = {y}` and
`V ∩ ν⁻¹ Sm f = D(t)` (`exists_away_mul_mem_span`). The local algebra
(`PoleChart.exists_mul_eq_of_node`) gives `e₂ t θ(σ) = e₁ β₀` on `D(t)` with `e₁, e₂` units at `y`;
on `D(e₁ e₂)` this is a comparison chart with local equation `t`, and
`Γ(D(e₁e₂), 𝒪)/(t) ≅ B/𝔫 = K` (`finrank_quotient_span_eq_one`).

The Kähler differentials of the scheme are taken over `Γ(Spec K, ⊤)`; they are identified with
those over `K` by `bijective_map_of_surjective`.

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2 (b) and
proof of Thm 1.1 (`semi-stable.tex`, T:1700–1704, T:1735–1737).
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace IsLocalRing Module
open DeJongAlterations.Algebra.NodeBlowupChart

namespace DeJongAlterations.StableModification.Omega.PoleChart

section KaehlerBase

/-- **Kähler differentials over isomorphic bases**: if `R → R'` is surjective, then
`Ω_{B/R} → Ω_{B/R'}` is bijective (its kernel is the image of `B ⊗ Ω_{R'/R} = 0`). -/
theorem bijective_map_of_surjective {R R' B : Type*} [CommRing R] [CommRing R'] [CommRing B]
    [Algebra R R'] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
    (h : Function.Surjective (algebraMap R R')) :
    Function.Bijective (KaehlerDifferential.map R R' B B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective R R' B⟩
  have : Algebra.FormallyUnramified R R' :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R R') h
  rw [← LinearMap.ker_eq_bot, ← KaehlerDifferential.range_mapBaseChange, LinearMap.range_eq_bot]
  exact Subsingleton.elim _ _

end KaehlerBase

section Quotient

variable {K : Type*} [Field K] [IsAlgClosed K] {R : Type*} [CommRing R] [Algebra K R]
  [Algebra.FiniteType K R]

/-- **The residue field of a closed point of a curve over `K = K̄` is `K`.** -/
theorem bijective_algebraMap_quotient (𝔪 : Ideal R) [𝔪.IsMaximal] :
    Function.Bijective (algebraMap K (R ⧸ 𝔪)) := by
  let := Ideal.Quotient.field 𝔪
  have : Module.Finite K (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ 𝔪)
  have : Algebra.IsIntegral K (R ⧸ 𝔪) := Algebra.IsIntegral.of_finite K _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- **A local equation of a closed point.** Let `𝔪 = (t)` be a maximal ideal of a finite type
`K`-algebra `R`, `K = K̄`, and `h ∉ 𝔪`. Then `R_h / (t) ≅ R/𝔪 ≅ K` is one-dimensional. -/
theorem finrank_quotient_span_eq_one (𝔪 : Ideal R) [𝔪.IsMaximal] {t : R}
    (ht : 𝔪 = Ideal.span {t}) {h : R} (hh : h ∉ 𝔪) (Rh : Type*) [CommRing Rh] [Algebra R Rh]
    [IsLocalization.Away h Rh] [Algebra K Rh] [IsScalarTower K R Rh] :
    FiniteDimensional K (Rh ⧸ Ideal.span {algebraMap R Rh t}) ∧
      finrank K (Rh ⧸ Ideal.span {algebraMap R Rh t}) = 1 := by
  set th := algebraMap R Rh t
  let ρ : R →ₐ[K] Rh ⧸ Ideal.span {th} :=
    (Ideal.Quotient.mkₐ K _).comp (IsScalarTower.toAlgHom K R Rh)
  have hρ : ∀ r, ρ r = Ideal.Quotient.mk _ (algebraMap R Rh r) := fun _ => rfl
  -- `h` is invertible modulo `t`
  obtain ⟨h', hh'⟩ : ∃ h' : R, h * h' - 1 ∈ 𝔪 := by
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := 𝔪) (a := Ideal.Quotient.mk 𝔪 h)
      (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨h', rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨h', ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
  have hker : RingHom.ker ρ = 𝔪 := by
    ext r
    rw [RingHom.mem_ker, hρ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.mk'_surjective (Submonoid.powers h) z
      simp only at hb
      have h1 : algebraMap R Rh (r * h ^ k) = algebraMap R Rh (b * t) := by
        rw [map_mul, map_mul, ← hz, ← hb, mul_assoc, mul_comm th, ← mul_assoc,
          IsLocalization.mk'_spec]
      obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) Rh).mp h1
      simp only at hm
      have h2 : h ^ m * (r * h ^ k) ∈ 𝔪 := by
        rw [hm, ht]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t))
      have hpow : ∀ n : ℕ, h ^ n ∉ 𝔪 := fun n hn =>
        hh ((inferInstance : 𝔪.IsMaximal).isPrime.mem_of_pow_mem n hn)
      rcases (inferInstance : 𝔪.IsMaximal).isPrime.mem_or_mem h2 with h3 | h3
      · exact absurd h3 (hpow m)
      · rcases (inferInstance : 𝔪.IsMaximal).isPrime.mem_or_mem h3 with h4 | h4
        · exact h4
        · exact absurd h4 (hpow k)
    · intro hr
      rw [ht, Ideal.mem_span_singleton'] at hr
      obtain ⟨c, rfl⟩ := hr
      exact ⟨algebraMap R Rh c, by rw [map_mul]⟩
  have hsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.mk'_surjective (Submonoid.powers h) z
    simp only at hb
    have hz : z * algebraMap R Rh (h ^ k) = algebraMap R Rh b := by
      rw [← hb]; exact IsLocalization.mk'_spec Rh b _
    have hpow : (h * h') ^ k - 1 ∈ 𝔪 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one]
      have : Ideal.Quotient.mk 𝔪 (h * h') = 1 := by
        rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk 𝔪), ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem]
        exact hh'
      rw [this, one_pow, sub_self]
    rw [ht, Ideal.mem_span_singleton'] at hpow
    obtain ⟨c, hc⟩ := hpow
    refine ⟨b * h' ^ k, ?_⟩
    rw [hρ, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨z * algebraMap R Rh c, ?_⟩
    have : algebraMap R Rh (b * h' ^ k) - z = z * algebraMap R Rh ((h * h') ^ k - 1) := by
      rw [map_mul, ← hz]; simp only [map_mul, map_pow, map_sub, map_one]; ring
    rw [this, ← hc, map_mul]; ring
  let e : (R ⧸ 𝔪) ≃ₐ[K] Rh ⧸ Ideal.span {th} :=
    (Ideal.quotientEquivAlgOfEq K hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have hb := bijective_algebraMap_quotient (K := K) 𝔪
  let eK : K ≃ₗ[K] R ⧸ 𝔪 := LinearEquiv.ofBijective (Algebra.linearMap K _) hb
  have h1 : finrank K (R ⧸ 𝔪) = 1 := by rw [← eK.finrank_eq, finrank_self]
  exact ⟨LinearEquiv.finiteDimensional (eK.trans e.toLinearEquiv), by
    rw [← e.toLinearEquiv.finrank_eq, h1]⟩

end Quotient

section DVR

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- **Local rings of a normal curve at closed points are discrete valuation rings**: for an
integral, normal, locally Noetherian scheme of dimension `≤ 1` and a non-generic point `y` of an
affine open `V`, `Γ(V, 𝒪)` localized at `y` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_localization (hnormal : IsNormalScheme Y)
    (hdim : topologicalKrullDim Y ≤ 1) {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V)
    (hyg : y ≠ genericPoint Y) :
    ∃ _ : IsDomain (Localization.AtPrime (hV.primeIdealOf ⟨y, hy⟩).asIdeal),
      IsDiscreteValuationRing (Localization.AtPrime (hV.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  set 𝔫 := (hV.primeIdealOf ⟨y, hy⟩).asIdeal with h𝔫
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  have : IsDomain Γ(Y, V) := IsIntegral.component_integral V
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨y, hy⟩
  let e := IsLocalization.algEquiv 𝔫.primeCompl (Localization.AtPrime 𝔫)
    (Y.presheaf.stalk (⟨y, hy⟩ : V))
  obtain ⟨-, hic⟩ := Curves.SemistableNormal.isDomain_isIntegrallyClosed_of_ringEquiv
    e.symm.toRingEquiv (hnormal y)
  have : Ring.KrullDimLE 1 Γ(Y, V) :=
    Geometry.NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔫) :=
    CurvesField.OrdinaryCompletion.krullDimLE_localization 𝔫
  -- `𝔫 ≠ 0` since `y` is not the generic point
  have hne : 𝔫 ≠ ⊥ := by
    intro h0
    apply hyg
    have h1 : hV.primeIdealOf ⟨y, hy⟩ = hV.primeIdealOf ⟨genericPoint Y,
        ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩⟩ := by
      rw [hV.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext h0
    have h2 := congrArg hV.fromSpec h1
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at h2
  have hinj : Function.Injective (algebraMap Γ(Y, V) (Localization.AtPrime 𝔫)) :=
    IsLocalization.injective (Localization.AtPrime 𝔫) 𝔫.primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime 𝔫) := by
    intro hf
    apply hne
    have hm := (isField_iff_maximalIdeal_eq).mp hf
    rw [← Localization.AtPrime.under_maximalIdeal (I := 𝔫), Ideal.under, hm, eq_bot_iff]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_bot] at hb
    exact (Ideal.mem_bot).mpr (hinj (hb.trans (map_zero _).symm))
  have key := (IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔫) hnf).out 0 3
  refine ⟨inferInstance, key.2
    ⟨hic, maximalIdeal _, ⟨fun h => hnf ((isField_iff_maximalIdeal_eq).mpr h), inferInstance⟩,
      ?_⟩⟩
  rintro P ⟨hP, hPp⟩
  exact IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)

end DVR

section Uniformizer

/-- **A local equation of a closed point**: if `B` is a Noetherian domain and `B_𝔫` a discrete
valuation ring, there are `0 ≠ t ∈ 𝔫` and `s ∉ 𝔫` with `s 𝔫 ⊆ (t)`; so `𝔫 = (t)` on `D(s)`. -/
theorem exists_away_mul_mem_span {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] [IsDiscreteValuationRing (Localization.AtPrime 𝔫)] :
    ∃ t ∈ 𝔫, t ≠ 0 ∧ ∃ s ∉ 𝔫, ∀ n ∈ 𝔫, s * n ∈ Ideal.span {t} := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔫)
  obtain ⟨⟨t, s₀⟩, hts⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl ϖ
  simp only at hts
  have hBD : Function.Injective (algebraMap B (Localization.AtPrime 𝔫)) :=
    IsLocalization.injective (Localization.AtPrime 𝔫) 𝔫.primeCompl_le_nonZeroDivisors
  have htD : algebraMap B (Localization.AtPrime 𝔫) t = ϖ * algebraMap B _ s₀ := by
    rw [← hts, IsLocalization.mk'_spec]
  have hs₀u : IsUnit (algebraMap B (Localization.AtPrime 𝔫) s₀) :=
    IsLocalization.map_units _ s₀
  have hm : maximalIdeal (Localization.AtPrime 𝔫) = Ideal.span {algebraMap B _ t} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, htD,
      Ideal.span_singleton_mul_right_unit hs₀u]
  have ht𝔫 : t ∈ 𝔫 := by
    rw [← Localization.AtPrime.under_maximalIdeal (I := 𝔫), Ideal.under, Ideal.mem_comap, hm]
    exact Ideal.mem_span_singleton_self _
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hϖ.ne_zero
    have : ϖ * algebraMap B _ s₀ = 0 := by rw [← htD, map_zero]
    exact (hs₀u.mul_left_eq_zero).mp this
  -- each element of `𝔫` is a multiple of `t` after multiplying by some `s ∉ 𝔫`
  have hloc : ∀ n ∈ 𝔫, ∃ s ∉ 𝔫, s * n ∈ Ideal.span {t} := by
    intro n hn
    have h1 : algebraMap B (Localization.AtPrime 𝔫) n ∈ maximalIdeal (Localization.AtPrime 𝔫) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hn
    rw [hm, Ideal.mem_span_singleton'] at h1
    obtain ⟨d, hd⟩ := h1
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl d
    simp only at hbs
    refine ⟨s.1, fun h => s.2 h, Ideal.mem_span_singleton'.mpr ⟨b, hBD ?_⟩⟩
    rw [map_mul, map_mul, ← hd, ← hbs, ← IsLocalization.mk'_spec (Localization.AtPrime 𝔫) b s]
    ring
  -- finitely many generators
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian 𝔫 : 𝔫.FG)
  choose! sg hsg hsgt using fun g (hg : g ∈ G) => hloc g (hG ▸ Ideal.subset_span hg)
  refine ⟨t, ht𝔫, ht0, ∏ g ∈ G, sg g, ?_, fun n hn => ?_⟩
  · intro hmem
    obtain ⟨g, hg, hgm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hsg g hg hgm
  · rw [← hG] at hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase G sg hx, mul_comm (sg x), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hsgt x hx)
    | zero => rw [mul_zero]; exact Ideal.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hx

end Uniformizer

section KaehlerSections

open DeJongAlterations.StableModification.Cohomology

variable {Y : Scheme.{u}} {K : Type u} [Field K] (q : Y ⟶ Spec (.of K))

/-- The `K`-algebra structure on the sections over `V` (through `Γ(Spec K, ⊤) ≅ K`). -/
abbrev sectionsAlgebra (V : Y.Opens) : Algebra K Γ(Y, V) :=
  (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- **Sections of `Ω¹_{Y/K}` over an affine open are the Kähler differentials over `K`.** -/
def kaehlerEquiv {V : Y.Opens} (hV : IsAffineOpen V) :
    letI := sectionsAlgebra q V
    Ω[Γ(Y, V)⁄K] ≃ₗ[Γ(Y, V)] Γ(relativeDifferentials q, V) :=
  letI := sectionsAlgebra q V
  letI : Algebra K Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(Y, V) := (q.appLE ⊤ V le_top).hom.toAlgebra
  haveI : IsScalarTower K Γ(Spec (.of K), ⊤) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  (LinearEquiv.ofBijective (KaehlerDifferential.map K Γ(Spec (.of K), ⊤) Γ(Y, V) Γ(Y, V))
    (bijective_map_of_surjective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)).trans
    (sectionsEquiv q hV (isAffineOpen_top _) le_top)

set_option backward.isDefEq.respectTransparency false in
theorem kaehlerEquiv_D {V : Y.Opens} (hV : IsAffineOpen V) (b : Γ(Y, V)) :
    letI := sectionsAlgebra q V
    kaehlerEquiv q hV (KaehlerDifferential.D K Γ(Y, V) b) = (universalDerivation q).d b := by
  let := sectionsAlgebra q V
  let : Algebra K Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  let : Algebra Γ(Spec (.of K), ⊤) Γ(Y, V) := (q.appLE ⊤ V le_top).hom.toAlgebra
  have : IsScalarTower K Γ(Spec (.of K), ⊤) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change sectionsEquiv q hV (isAffineOpen_top _) le_top
    (KaehlerDifferential.map K Γ(Spec (.of K), ⊤) Γ(Y, V) Γ(Y, V)
      (KaehlerDifferential.D K Γ(Y, V) b)) = _
  rw [KaehlerDifferential.map_D]
  exact sectionsEquiv_d q hV (isAffineOpen_top _) le_top b

theorem sectionsAlgebra_isScalarTower {V U : Y.Opens} (hUV : U ≤ V) :
    letI := sectionsAlgebra q V
    letI := sectionsAlgebra q U
    letI := (res hUV).toAlgebra
    IsScalarTower K Γ(Y, V) Γ(Y, U) := by
  let := sectionsAlgebra q V
  let := sectionsAlgebra q U
  let := (res hUV).toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  change sectionsRingHom (structureCoeff q) (le_top : U ≤ ⊤) k =
    res hUV (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤) k)
  simp only [sectionsRingHom, RingHom.comp_apply]
  exact (res_res (le_top : V ≤ ⊤) hUV _).symm

set_option backward.isDefEq.respectTransparency false in
/-- `kaehlerEquiv` is compatible with restriction (the Kähler map along `Γ(V) → Γ(U)`). -/
theorem kaehlerEquiv_map {V U : Y.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ V) (ω : letI := sectionsAlgebra q V; Ω[Γ(Y, V)⁄K]) :
    letI := sectionsAlgebra q V
    letI := sectionsAlgebra q U
    letI := (res hUV).toAlgebra
    haveI := sectionsAlgebra_isScalarTower q hUV
    kaehlerEquiv q hU (KaehlerDifferential.map K K Γ(Y, V) Γ(Y, U) ω) =
      (relativeDifferentials q).presheaf.map (homOfLE hUV).op (kaehlerEquiv q hV ω) := by
  let := sectionsAlgebra q V
  let := sectionsAlgebra q U
  let := (res hUV).toAlgebra
  have := sectionsAlgebra_isScalarTower q hUV
  have hω : ω ∈ Submodule.span Γ(Y, V) (Set.range (KaehlerDifferential.D K Γ(Y, V))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [KaehlerDifferential.map_D, kaehlerEquiv_D, kaehlerEquiv_D]
    exact ((universalDerivation q).d_map (homOfLE hUV) b)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
    rw [LinearMap.map_smul_of_tower, ← algebraMap_smul Γ(Y, U) c, LinearEquiv.map_smul,
      LinearEquiv.map_smul, Ω_map_res_smul, hx]
    rfl

end KaehlerSections

section ComparisonRelation

open RosenlichtComponent

variable {X S Y T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (q : Y ⟶ T)
  (ν : Y ⟶ X) (h : T ⟶ S) (sq : ν ≫ f = q ≫ h)

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison of `da = c σ`**: on an open `U ⊆ ν⁻¹(W ∩ Sm f)`, the image `θ(σ)` of `σ`
satisfies `d(ν^♯ a) = ν^♯ c · θ(σ)`. -/
theorem sec_eq_smul_comparison {W : X.Opens} (σ : Γ(dualizingSheaf f, W)) (a c : Γ(X, W))
    (hc : c • σ = (toDualizingSheaf f).app W ((universalDerivation f).sec W a)) {U : Y.Opens}
    (hU : U ≤ (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ W))) (hUW : U ≤ ν ⁻¹ᵁ W) :
    (universalDerivation q).sec U (ν.appLE W U hUW a) =
      ν.appLE W U hUW c • (relativeDifferentials q).presheaf.map (homOfLE hU).op
        (show Γ(relativeDifferentials q, (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ W)))
          from (dualizingComparison f q ν h sq).app W σ) := by
  set O := f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W)
  have hOW : O ≤ W := f.smoothLocus.ι.image_preimage_le W
  have hPO := image_preimage_le_preimage f ν W
  let σO : Γ(relativeDifferentials f, O) := σ
  let c' : Γ(X, O) :=
    (f.smoothLocus.ι.appIso (f.smoothLocus.ι ⁻¹ᵁ W)).inv (f.smoothLocus.ι.app W c)
  have hc'res : c' = res hOW c := by
    change (f.smoothLocus.ι.app W ≫ (f.smoothLocus.ι.appIso _).inv) c = _
    rw [Scheme.Hom.app_appIso_inv]
    rfl
  have hc' : c' • σO = (universalDerivation f).sec O (res hOW a) := by
    rw [sec_res]
    exact hc
  have h1 := congrArg (baseChangeSecMap f q ν h sq O) hc'
  rw [baseChangeSecMap_smul, baseChangeSecMap_sec] at h1
  have hUO : U ≤ ν ⁻¹ᵁ O := hU.trans hPO
  have h2 := congrArg ((relativeDifferentials q).presheaf.map (homOfLE hUO).op) h1
  rw [Ω_map_res_smul, ← sec_res] at h2
  have e1 : ∀ b : Γ(X, W), res hUO (ν.app O (res hOW b)) = ν.appLE W U hUW b := by
    intro b
    exact res_app_res_eq ν hOW (le_refl (ν ⁻¹ᵁ W)) hUO hUW b |>.trans (by
      change (ν.appLE W (ν ⁻¹ᵁ W) le_rfl ≫ Y.presheaf.map _) b = _
      rw [Scheme.Hom.appLE_map])
  rw [e1, hc'res, e1] at h2
  rw [← h2]
  congr 1
  change _ = (relativeDifferentials q).presheaf.map (homOfLE hU).op
    ((relativeDifferentials q).presheaf.map (homOfLE hPO).op (baseChangeSecMap f q ν h sq O σO))
  rw [map_map_eq]

end ComparisonRelation

section AffineChoice

open RosenlichtComponent

variable {X S Y T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (q : Y ⟶ T)
  (ν : Y ⟶ X)

omit [LocallyOfFinitePresentation f] in
set_option backward.isDefEq.respectTransparency false in
/-- **An affine neighbourhood adapted to an unramified point**: if `ν` is unramified relative to the
base change at `y` and `Ω¹_{Y/T}` is invertible at `y`, then inside any open `O ∋ y` there is an
affine `V ∋ y`, `V ⊆ ν⁻¹ W`, on which `Ω¹_{Y/T}` is free and spanned by the `d(ν^♯ a)`. -/
theorem exists_affine_free_span [(relativeDifferentials q).IsQuasicoherent] {y : Y}
    (hΩ : IsInvertibleAt (relativeDifferentials q) y) {V_S : S.Opens} {W : X.Opens}
    (hV_S : IsAffineOpen V_S) (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V_S) (hyW : ν y ∈ W)
    (hun : IsUnramifiedAt f q ν y) {O : Y.Opens} (hyO : y ∈ O) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ O ∧ ∃ hVW : V ≤ ν ⁻¹ᵁ W,
      (∃ β : Γ(relativeDifferentials q, V), Function.Bijective fun c : Γ(Y, V) => c • β) ∧
      Submodule.span Γ(Y, V)
        (Set.range fun a : Γ(X, W) => (universalDerivation q).sec V (ν.appLE W V hVW a)) = ⊤ := by
  obtain ⟨V₁, hV₁, hyV₁, hV₁W, hspan₁⟩ := hun V_S W hV_S hW hWV hyW
  obtain ⟨W₁, hW₁, hyW₁, hW₁O, β₁, hβ₁⟩ :=
    exists_generator (relativeDifferentials q) hΩ (O := V₁ ⊓ O) ⟨hyV₁, hyO⟩
  obtain ⟨g, g₁, hgg₁, hyg⟩ := exists_basicOpen_le_affine_inter hV₁ hW₁ y ⟨hyV₁, hyW₁⟩
  have hgV₁ : Y.basicOpen g ≤ V₁ := Y.basicOpen_le g
  have hgW₁ : Y.basicOpen g ≤ W₁ := hgg₁.le.trans (Y.basicOpen_le g₁)
  refine ⟨Y.basicOpen g, hV₁.basicOpen g, hyg, hgW₁.trans (hW₁O.trans inf_le_right),
    hgV₁.trans hV₁W, ⟨_, bijective_smul_of_eq _ hgg₁ hgW₁ (Y.basicOpen_le g₁) β₁
      (bijective_smul_restrict_basicOpen _ hW₁ β₁ hβ₁ g₁)⟩, ?_⟩
  have h := span_restrict_basicOpen (relativeDifferentials q) hV₁ _ hspan₁ g
  have hres : ∀ a : Γ(X, W), res hgV₁ (ν.appLE W V₁ hV₁W a) = ν.appLE W _ (hgV₁.trans hV₁W) a :=
    fun a => by
      change (ν.appLE W V₁ hV₁W ≫ Y.presheaf.map _) a = _
      rw [Scheme.Hom.appLE_map]
  have hset : (relativeDifferentials q).presheaf.map (homOfLE (Y.basicOpen_le g)).op ''
      Set.range (fun a : Γ(X, W) => (universalDerivation q).sec V₁ (ν.appLE W V₁ hV₁W a)) =
      Set.range (fun a : Γ(X, W) =>
        (universalDerivation q).sec _ (ν.appLE W _ (hgV₁.trans hV₁W) a)) := by
    rw [← Set.range_comp]
    congr 1
    funext a
    simp only [Function.comp_apply]
    rw [← sec_res, hres]
  rw [hset] at h
  exact h

end AffineChoice

section Points

variable {Y : Scheme.{u}}

/-- The prime of a closed point is maximal. -/
theorem isMaximal_primeIdealOf {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V)
    (hyc : IsClosed ({y} : Set Y)) : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.IsMaximal := by
  rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  have : ({hV.primeIdealOf ⟨y, hy⟩} : Set (PrimeSpectrum Γ(Y, V))) = hV.fromSpec ⁻¹' {y} := by
    ext p
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro rfl; exact hV.fromSpec_primeIdealOf ⟨y, hy⟩
    · intro hp
      apply hV.fromSpec.isOpenEmbedding.injective
      rw [hp, hV.fromSpec_primeIdealOf]
  rw [this]
  exact hyc.preimage hV.fromSpec.continuous

/-- Membership of a restriction in the prime of a point. -/
theorem mem_primeIdealOf_res_iff {U U' : Y.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (h : U' ≤ U) {y : Y} (hy : y ∈ U') (b : Γ(Y, U)) :
    res h b ∈ (hU'.primeIdealOf ⟨y, hy⟩).asIdeal ↔ b ∈ (hU.primeIdealOf ⟨y, h hy⟩).asIdeal := by
  rw [← not_iff_not, ← mem_basicOpen_iff_notMem, ← mem_basicOpen_iff_notMem, Scheme.basicOpen_res]
  exact ⟨fun h' => h'.2, fun h' => ⟨hy, h'⟩⟩

end Points

section LogSmul

open RosenlichtComponent

variable {X S Y T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (q : Y ⟶ T)
  (ν : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- The module structure of `j_*(Ω¹|_{ν⁻¹ Sm f})` on sections over `V`: `t • s = t|_{V ∩ ν⁻¹ Sm f} • s`. -/
theorem logDifferentials_smul (V : Y.Opens) (c : Γ(Y, V)) (m : Γ(logDifferentials f q ν, V)) :
    (show Γ(relativeDifferentials q, (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ V)) from
      c • m) = res ((fibreLocus f ν).ι.image_preimage_le V) c •
        (show Γ(relativeDifferentials q, (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ V)) from
          m) := by
  change (((fibreLocus f ν).ι.appIso ((fibreLocus f ν).ι ⁻¹ᵁ V)).inv
    ((fibreLocus f ν).ι.app V c)) •
      (show Γ(relativeDifferentials q, (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ V)) from
        m) = _
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_appIso_inv]
  rfl

end LogSmul

section ChartAux

open DeJongAlterations.StableModification.Cohomology

variable {Y : Scheme.{u}} {K : Type u} [Field K] (q : Y ⟶ Spec (.of K))

/-- The sections of `𝒪_Y` over an affine open are a finite type `K`-algebra. -/
theorem finiteType_sectionsAlgebra [LocallyOfFiniteType q] {V : Y.Opens} (hV : IsAffineOpen V) :
    letI := sectionsAlgebra q V
    Algebra.FiniteType K Γ(Y, V) := by
  have h : (q.appLE ⊤ V le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have h' : (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).FiniteType := by
    have e : sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤) =
        (q.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
      ext k
      rfl
    rw [e]
    exact h.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  exact h'

/-- **The local equation of the chart.** If `𝔪 = (t)` is a maximal ideal of `Γ(Y, V₃)` and
`h ∉ 𝔪`, then `Γ(D(h), 𝒪)/(t)` is one-dimensional over `K = K̄`. -/
theorem finrank_quotient_basicOpen [IsAlgClosed K] [LocallyOfFiniteType q] {V₃ : Y.Opens}
    (hV₃ : IsAffineOpen V₃) (𝔪 : Ideal Γ(Y, V₃)) [𝔪.IsMaximal] {t : Γ(Y, V₃)}
    (ht : 𝔪 = Ideal.span {t}) {h : Γ(Y, V₃)} (hh : h ∉ 𝔪) :
    letI := sectionsAlgebra q (Y.basicOpen h)
    FiniteDimensional K (Γ(Y, Y.basicOpen h) ⧸ Ideal.span {res (Y.basicOpen_le h) t}) ∧
      finrank K (Γ(Y, Y.basicOpen h) ⧸ Ideal.span {res (Y.basicOpen_le h) t}) = 1 := by
  let := sectionsAlgebra q V₃
  let := sectionsAlgebra q (Y.basicOpen h)
  let := (res (Y.basicOpen_le h)).toAlgebra
  have : IsLocalization.Away h Γ(Y, Y.basicOpen h) := hV₃.isLocalization_basicOpen h
  have := sectionsAlgebra_isScalarTower q (Y.basicOpen_le h)
  have := finiteType_sectionsAlgebra q hV₃
  exact finrank_quotient_span_eq_one (K := K) 𝔪 ht hh Γ(Y, Y.basicOpen h)

/-- **The chart equation from the local identity.** From `e₂ t ζ = e₁ β` on `B_t ⊆ V₃` and
`e₂ w = e₁` on `V ⊆ V₃`, deduce `t ζ = w β` on `P ⊆ B_t ∩ V` (where `e₂` is a unit). -/
theorem smul_eq_of_mul_eq {N : Y.Modules} {V₃ Bt V P : Y.Opens} (hBt : Bt ≤ V₃) (hV : V ≤ V₃)
    (hPB : P ≤ Bt) (hPV : P ≤ V) {e₁ e₂ t : Γ(Y, V₃)} {w : Γ(Y, V)} (ζ : Γ(N, Bt))
    (β : Γ(N, V₃)) (hw : res hV e₂ * w = res hV e₁) (hu : IsUnit (res hPV (res hV e₂)))
    (hid : res hBt e₂ • res hBt t • ζ = res hBt e₁ • N.presheaf.map (homOfLE hBt).op β) :
    res hPV (res hV t) • N.presheaf.map (homOfLE hPB).op ζ =
      N.presheaf.map (homOfLE hPV).op (w • N.presheaf.map (homOfLE hV).op β) := by
  apply hu.smul_left_cancel.mp
  have h := congrArg (N.presheaf.map (homOfLE hPB).op) hid
  simp only [Ω_map_res_smul, map_map_eq, smul_smul, ← map_mul, res_res] at h
  simp only [Ω_map_res_smul, map_map_eq, smul_smul, ← map_mul, hw]
  simp only [res_res, map_mul] at h ⊢
  exact h

end ChartAux

section Assembly

open RosenlichtComponent Cohomology
open DeJong (IsNodalCurve IsSmoothAt)

variable {X S Y : Scheme.{u}} (f : X ⟶ S) {K : Type u} [Field K] [IsAlgClosed K]
  (q : Y ⟶ Spec (.of K)) (ν : Y ⟶ X) (a : Spec (.of K) ⟶ S) (sq : ν ≫ f = q ≫ a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **A comparison chart at a point over a node** (blueprint `lem:sm-omega-cd-pole-chart`). -/
theorem exists_poleChart [IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S) (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x)
    [IsIntegral Y] [IsLocallyNoetherian Y] [SmoothOfRelativeDimension 1 q]
    (hnormal : IsNormalScheme Y) (hdim : topologicalKrullDim Y ≤ 1) (E : Finset Y)
    (hE : ∀ z, z ∈ E ↔ ν z ∉ f.smoothLocus) (hEc : ∀ z ∈ E, IsClosed ({z} : Set Y)) {y : Y}
    (hyE : y ∈ E) (hyg : y ≠ genericPoint Y) (hun : IsUnramifiedAt f q ν y) :
    ∃ C : CompChart f q ν a sq, y ∈ C.V ∧ (∀ z ∈ E, z ∈ C.V → z = y) ∧
      letI := (sectionsRingHom (structureCoeff q) (le_top : C.V ≤ ⊤)).toAlgebra
      FiniteDimensional K (Γ(Y, C.V) ⧸ Ideal.span {C.t}) ∧
        finrank K (Γ(Y, C.V) ⧸ Ideal.span {C.t}) = 1 := by
  classical
  have hx : ν y ∉ f.smoothLocus := (hE y).mp hyE
  obtain ⟨D⟩ := nonempty_nodePoleData f hS hgen hx
  have hω := isInvertibleModule_dualizingSheaf_of_isNodalCurve f hS hgen
  have : (dualizingSheaf f).IsQuasicoherent := isQuasicoherent_of_isInvertibleModule _ hω
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have hΩ := isInvertibleModule_relativeDifferentials q
  have : (relativeDifferentials q).IsQuasicoherent := isQuasicoherent_of_isInvertibleModule _ hΩ
  -- an open avoiding the other points of `E`
  let OE : Y.Opens := ⟨((E.erase y : Finset Y) : Set Y)ᶜ,
    (isClosed_finset (E.erase y) (fun z hz => hEc z (Finset.mem_of_mem_erase hz))).isOpen_compl⟩
  have hyOE : y ∈ OE := by
    change y ∉ ((E.erase y : Finset Y) : Set Y)
    simp
  have hOE : ∀ z ∈ OE, z ∈ E → z = y := by
    intro z hz hzE
    by_contra hne
    exact hz (Finset.mem_erase.mpr ⟨hne, hzE⟩)
  -- an affine `V₂ ∋ y` with `Ω¹` free and spanned by `d(ν^♯ a)`
  obtain ⟨V₂, hV₂, hyV₂, hV₂O, hV₂W, ⟨β₂, hβ₂⟩, hspan₂⟩ := exists_affine_free_span f q ν (hΩ y)
    D.isAffineOpen_V D.isAffineOpen_W D.le D.mem hun hyOE
  have : Nonempty V₂ := ⟨⟨y, hyV₂⟩⟩
  have : IsDomain Γ(Y, V₂) := IsIntegral.component_integral V₂
  have : IsNoetherianRing Γ(Y, V₂) := IsLocallyNoetherian.component_noetherian ⟨V₂, hV₂⟩
  have : (hV₂.primeIdealOf ⟨y, hyV₂⟩).asIdeal.IsMaximal :=
    isMaximal_primeIdealOf hV₂ hyV₂ (hEc y hyE)
  obtain ⟨_, _⟩ := isDiscreteValuationRing_localization hnormal hdim hV₂ hyV₂ hyg
  obtain ⟨t, ht𝔫, ht0, s, hs, hst⟩ :=
    exists_away_mul_mem_span (hV₂.primeIdealOf ⟨y, hyV₂⟩).asIdeal
  -- `V₃ = D(s)`: there `𝔫 = (t)`
  have hyV₃ : y ∈ Y.basicOpen s := (mem_basicOpen_iff_notMem hV₂ hyV₂ s).mpr hs
  have hV₃ : IsAffineOpen (Y.basicOpen s) := hV₂.basicOpen s
  have hV₃V₂ : Y.basicOpen s ≤ V₂ := Y.basicOpen_le s
  have : Nonempty (Y.basicOpen s) := ⟨⟨y, hyV₃⟩⟩
  have : IsDomain Γ(Y, Y.basicOpen s) := IsIntegral.component_integral _
  have : IsNoetherianRing Γ(Y, Y.basicOpen s) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hV₃⟩
  have : (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal.IsMaximal :=
    isMaximal_primeIdealOf hV₃ hyV₃ (hEc y hyE)
  obtain ⟨_, _⟩ := isDiscreteValuationRing_localization hnormal hdim hV₃ hyV₃ hyg
  obtain ⟨t', ht'def⟩ : ∃ t' : Γ(Y, Y.basicOpen s), t' = res hV₃V₂ t := ⟨_, rfl⟩
  have hsu : IsUnit (res hV₃V₂ s) := isUnit_map_of_le_basicOpen s le_rfl hV₃V₂
  have h𝔫' : (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal = Ideal.span {t'} := by
    apply le_antisymm
    · intro n' hn'
      let := (res hV₃V₂).toAlgebra
      have hloc : IsLocalization.Away s Γ(Y, Y.basicOpen s) := hV₂.isLocalization_basicOpen s
      obtain ⟨⟨n, ⟨_, k, rfl⟩⟩, hn⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) n'
      simp only at hn
      have hnspec : n' * res hV₃V₂ (s ^ k) = res hV₃V₂ n := by
        rw [← hn]; exact IsLocalization.mk'_spec _ n _
      have hn𝔫 : n ∈ (hV₂.primeIdealOf ⟨y, hyV₂⟩).asIdeal := by
        rw [← mem_primeIdealOf_res_iff hV₂ hV₃ hV₃V₂ hyV₃, ← hnspec]
        exact Ideal.mul_mem_right _ _ hn'
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hst n hn𝔫)
      rw [Ideal.mem_span_singleton']
      refine ⟨((hsu.pow (k + 1)).unit⁻¹ : (Γ(Y, Y.basicOpen s))ˣ) * res hV₃V₂ c, ?_⟩
      apply (hsu.pow (k + 1)).mul_left_cancel
      rw [← mul_assoc, ← mul_assoc, IsUnit.mul_val_inv, one_mul, ht'def, ← map_mul, hc,
        map_mul, ← hnspec, map_pow, pow_succ]
      ring
    · rw [Ideal.span_le, Set.singleton_subset_iff, ht'def]
      exact (mem_primeIdealOf_res_iff hV₂ hV₃ hV₃V₂ hyV₃ t).mpr ht𝔫
  -- on `V₃` the preimage of the smooth locus is `D(t)`
  have hfib : Y.basicOpen s ⊓ fibreLocus f ν = Y.basicOpen t' := by
    apply le_antisymm
    · rintro z ⟨hzs, hzU⟩
      have hzV₂ : z ∈ V₂ := hV₃V₂ hzs
      rw [ht'def, Scheme.basicOpen_res]
      refine ⟨hzs, (mem_basicOpen_iff_notMem hV₂ hzV₂ t).mpr fun htz => ?_⟩
      have hle : (hV₂.primeIdealOf ⟨y, hyV₂⟩).asIdeal ≤ (hV₂.primeIdealOf ⟨z, hzV₂⟩).asIdeal := by
        intro n hn
        have h1 : s * n ∈ (hV₂.primeIdealOf ⟨z, hzV₂⟩).asIdeal :=
          (Ideal.span_singleton_le_iff_mem _).mpr htz (hst n hn)
        rcases (hV₂.primeIdealOf ⟨z, hzV₂⟩).isPrime.mem_or_mem h1 with h2 | h2
        · exact absurd h2 ((mem_basicOpen_iff_notMem hV₂ hzV₂ s).mp hzs)
        · exact h2
      have heq := (inferInstance : (hV₂.primeIdealOf ⟨y, hyV₂⟩).asIdeal.IsMaximal).eq_of_le
        (hV₂.primeIdealOf ⟨z, hzV₂⟩).isPrime.ne_top hle
      have hzy : z = y := by
        have := congrArg hV₂.fromSpec (PrimeSpectrum.ext heq)
        rwa [hV₂.fromSpec_primeIdealOf, hV₂.fromSpec_primeIdealOf, eq_comm] at this
      subst hzy
      exact hx hzU
    · intro z hz
      rw [ht'def, Scheme.basicOpen_res] at hz
      obtain ⟨hzs, hzt⟩ := hz
      refine ⟨hzs, ?_⟩
      by_contra hzU
      have hzy := hOE z (hV₂O (hV₃V₂ hzs)) ((hE z).mpr hzU)
      subst hzy
      exact (mem_basicOpen_iff_notMem hV₂ hyV₂ t).mp hzt ht𝔫
  -- the restricted generator and spanning set on `V₃`
  have hV₃W : Y.basicOpen s ≤ ν ⁻¹ᵁ D.W := hV₃V₂.trans hV₂W
  have hβ₃ := bijective_smul_restrict_basicOpen _ hV₂ β₂ hβ₂ s
  set β₃ := (relativeDifferentials q).presheaf.map (homOfLE (Y.basicOpen_le s)).op β₂ with hβ₃def
  have hres : ∀ b : Γ(X, D.W), res hV₃V₂ (ν.appLE D.W V₂ hV₂W b) = ν.appLE D.W _ hV₃W b :=
    fun b => by
      change (ν.appLE D.W V₂ hV₂W ≫ Y.presheaf.map _) b = _
      rw [Scheme.Hom.appLE_map]
  have hspan₃ : Submodule.span Γ(Y, Y.basicOpen s) (Set.range fun b : Γ(X, D.W) =>
      (universalDerivation q).sec _ (ν.appLE D.W _ hV₃W b)) = ⊤ := by
    have h := span_restrict_basicOpen (relativeDifferentials q) hV₂ _ hspan₂ s
    have hset : (relativeDifferentials q).presheaf.map (homOfLE (Y.basicOpen_le s)).op ''
        Set.range (fun b : Γ(X, D.W) => (universalDerivation q).sec V₂ (ν.appLE D.W V₂ hV₂W b)) =
        Set.range (fun b : Γ(X, D.W) =>
          (universalDerivation q).sec _ (ν.appLE D.W _ hV₃W b)) := by
      rw [← Set.range_comp]
      congr 1
      funext b
      simp only [Function.comp_apply]
      rw [← sec_res, hres]
    rw [hset] at h
    exact h
  -- Kähler differentials over `K` on `B = Γ(V₃)`
  let := sectionsAlgebra q (Y.basicOpen s)
  have hβ₀ : Function.Bijective fun c : Γ(Y, Y.basicOpen s) => c • (kaehlerEquiv q hV₃).symm β₃ := by
    have : (fun c : Γ(Y, Y.basicOpen s) => c • (kaehlerEquiv q hV₃).symm β₃) =
        (kaehlerEquiv q hV₃).symm ∘ (fun c => c • β₃) := by
      funext c
      simp only [Function.comp_apply, LinearEquiv.map_smul]
    rw [this]
    exact (kaehlerEquiv q hV₃).symm.bijective.comp hβ₃
  let : Algebra Γ(X, D.W) Γ(Y, Y.basicOpen s) := (ν.appLE D.W _ hV₃W).hom.toAlgebra
  have hsymmD : ∀ b, (kaehlerEquiv q hV₃).symm ((universalDerivation q).sec _ b) =
      KaehlerDifferential.D K Γ(Y, Y.basicOpen s) b := fun b =>
    (LinearEquiv.symm_apply_eq _).mpr (kaehlerEquiv_D q hV₃ b).symm
  have hun' : Submodule.span Γ(Y, Y.basicOpen s) (Set.range fun b : Γ(X, D.W) =>
      KaehlerDifferential.D K Γ(Y, Y.basicOpen s)
        (algebraMap Γ(X, D.W) Γ(Y, Y.basicOpen s) b)) = ⊤ := by
    have h := congrArg (Submodule.map (kaehlerEquiv q hV₃).symm.toLinearMap) hspan₃
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr
      (kaehlerEquiv q hV₃).symm.surjective, ← Set.range_comp] at h
    have hfun : (fun b : Γ(X, D.W) => KaehlerDifferential.D K Γ(Y, Y.basicOpen s)
        (algebraMap Γ(X, D.W) Γ(Y, Y.basicOpen s) b)) =
        (⇑(kaehlerEquiv q hV₃).symm.toLinearMap ∘ fun b : Γ(X, D.W) =>
          (universalDerivation q).sec _ (ν.appLE D.W _ hV₃W b)) := by
      funext b
      exact (hsymmD _).symm
    rw [hfun]
    exact h
  -- `Bt = Γ(D(t))` and the differential `ζ = θ(σ)|_{D(t)}`
  have hBt : IsAffineOpen (Y.basicOpen t') := hV₃.basicOpen t'
  let : Algebra Γ(Y, Y.basicOpen s) Γ(Y, Y.basicOpen t') := (res (Y.basicOpen_le t')).toAlgebra
  have : IsLocalization.Away t' Γ(Y, Y.basicOpen t') := hV₃.isLocalization_basicOpen t'
  let := sectionsAlgebra q (Y.basicOpen t')
  have := sectionsAlgebra_isScalarTower q (Y.basicOpen_le t')
  have htW : Y.basicOpen t' ≤ ν ⁻¹ᵁ D.W := (Y.basicOpen_le t').trans hV₃W
  have hP : Y.basicOpen t' ≤ (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ D.W)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, ← hfib]
    exact fun z hz => ⟨hz.2, hV₃W hz.1⟩
  set ζs := (relativeDifferentials q).presheaf.map (homOfLE hP).op
    (show Γ(relativeDifferentials q, (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ D.W)))
      from (dualizingComparison f q ν a sq).app D.W D.σ) with hζs
  set ζ := (kaehlerEquiv q hBt).symm ζs with hζdef
  choose coef hcoef using fun b : Γ(X, D.W) =>
    D.bijective_σ.surjective ((toDualizingSheaf f).app D.W ((universalDerivation f).sec D.W b))
  have hresW : ∀ b : Γ(X, D.W), res (Y.basicOpen_le t') (ν.appLE D.W _ hV₃W b) =
      ν.appLE D.W _ htW b := fun b => by
    change (ν.appLE D.W _ hV₃W ≫ Y.presheaf.map _) b = _
    rw [Scheme.Hom.appLE_map]
  have hζ : ∀ b : Γ(X, D.W), KaehlerDifferential.D K Γ(Y, Y.basicOpen t')
      (algebraMap Γ(Y, Y.basicOpen s) Γ(Y, Y.basicOpen t')
        (algebraMap Γ(X, D.W) Γ(Y, Y.basicOpen s) b)) =
      algebraMap Γ(Y, Y.basicOpen s) Γ(Y, Y.basicOpen t')
        (algebraMap Γ(X, D.W) Γ(Y, Y.basicOpen s) (coef b)) • ζ := by
    intro b
    apply (kaehlerEquiv q hBt).injective
    rw [kaehlerEquiv_D, LinearEquiv.map_smul, hζdef, LinearEquiv.apply_symm_apply]
    change (universalDerivation q).d (res (Y.basicOpen_le t') (ν.appLE D.W _ hV₃W b)) =
      res (Y.basicOpen_le t') (ν.appLE D.W _ hV₃W (coef b)) • ζs
    rw [hresW, hresW]
    exact sec_eq_smul_comparison f q ν a sq D.σ b (coef b) (hcoef b) hP htW
  -- the base `R = Γ(S, V)` and its maps
  have haV : (⊤ : (Spec (.of K)).Opens) ≤ a ⁻¹ᵁ D.V := by
    intro z _
    have hz : z = q y := Subsingleton.elim _ _
    subst hz
    change (q ≫ a) y ∈ D.V
    rw [← sq]
    exact D.le D.mem
  let φRK : Γ(S, D.V) →+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (a.appLE D.V ⊤ haV).hom
  let : Algebra Γ(S, D.V) K := φRK.toAlgebra
  let : Algebra Γ(S, D.V) Γ(X, D.W) := (f.appLE D.V D.W D.le).hom.toAlgebra
  have hV₃S : Y.basicOpen s ≤ (ν ≫ f) ⁻¹ᵁ D.V := fun z hz => D.le (hV₃W hz)
  let : Algebra Γ(S, D.V) Γ(Y, Y.basicOpen s) := ((ν ≫ f).appLE D.V _ hV₃S).hom.toAlgebra
  have : IsScalarTower Γ(S, D.V) Γ(X, D.W) Γ(Y, Y.basicOpen s) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (ν ≫ f).appLE D.V _ hV₃S r = (f.appLE D.V D.W D.le ≫ ν.appLE D.W _ hV₃W) r
      rw [Scheme.Hom.appLE_comp_appLE]
  have hcongr : ∀ (g₁ g₂ : Y ⟶ S) (_ : g₁ = g₂) (e₁ : Y.basicOpen s ≤ g₁ ⁻¹ᵁ D.V)
      (e₂ : Y.basicOpen s ≤ g₂ ⁻¹ᵁ D.V), g₁.appLE D.V _ e₁ = g₂.appLE D.V _ e₂ := by
    rintro _ _ rfl _ _; rfl
  have : IsScalarTower Γ(S, D.V) K Γ(Y, Y.basicOpen s) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (ν ≫ f).appLE D.V _ hV₃S r = sectionsRingHom (structureCoeff q) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (a.appLE D.V ⊤ haV r))
      simp only [sectionsRingHom, structureCoeff, RingHom.comp_apply]
      rw [Iso.hom_inv_id_apply]
      rw [hcongr _ _ sq hV₃S (fun z hz => haV trivial),
        ← Scheme.Hom.appLE_comp_appLE q a D.V ⊤ _ haV le_top]
      rfl
  have := D.isScalarTower
  -- the primes of `T` over `y` contain `u, v`
  have hnode : ∀ P : Ideal D.T, P.IsPrime →
      P.comap (algebraMap Γ(X, D.W) D.T) = (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal.comap
        (algebraMap Γ(X, D.W) Γ(Y, Y.basicOpen s)) →
      algebraMap (Node D.O D.c) D.T (coordinate D.c 0) ∈ P ∧
        algebraMap (Node D.O D.c) D.T (coordinate D.c 1) ∈ P := by
    intro P hP hPp
    have hcomap := IsAffineOpen.comap_primeIdealOf_appLE D.W D.isAffineOpen_W _ hV₃ hV₃W hyV₃
    refine D.node (D.isAffineOpen_W.primeIdealOf ⟨ν y, hV₃W hyV₃⟩) ?_ P hP ?_
    · rw [D.isAffineOpen_W.fromSpec_primeIdealOf]; exact hx
    · rw [hPp]; exact congrArg PrimeSpectrum.asIdeal hcomap
  -- `t` is a uniformizer at `y`
  have ht' : Irreducible (algebraMap Γ(Y, Y.basicOpen s)
      (Localization.AtPrime (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal) t') := by
    have hm : maximalIdeal (Localization.AtPrime (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal) =
        Ideal.span {algebraMap _ _ t'} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      have e := congrArg (Ideal.map (algebraMap Γ(Y, Y.basicOpen s)
        (Localization.AtPrime (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal))) h𝔫'
      rw [e, Ideal.map_span, Set.image_singleton]
    refine IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ hm
    intro h0
    rw [h0, Ideal.span_singleton_zero] at hm
    exact IsDiscreteValuationRing.not_a_field _ hm
  -- the local algebra
  obtain ⟨e₁, e₂, he₁, he₂, heq⟩ := exists_mul_eq_of_node (K := K) (R := Γ(S, D.V))
    (A := Γ(X, D.W)) (T := D.T) (B := Γ(Y, Y.basicOpen s)) D.c
    (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal ht' hnode hβ₀ hun' coef D.isUnit_g D.Tu
    (fun b => D.rel_u b (coef b) (hcoef b)) D.Tv (fun b => D.rel_v b (coef b) (hcoef b))
    Γ(Y, Y.basicOpen t') ζ hζ
  -- the identity `e₂ t ζ = e₁ β₃` on `D(t)`, as sections
  have hid : res (Y.basicOpen_le t') e₂ • res (Y.basicOpen_le t') t' • ζs =
      res (Y.basicOpen_le t') e₁ • (relativeDifferentials q).presheaf.map
        (homOfLE (Y.basicOpen_le t')).op β₃ := by
    have h := congrArg (kaehlerEquiv q hBt) heq
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.map_smul, hζdef,
      LinearEquiv.apply_symm_apply, kaehlerEquiv_map q hV₃ hBt (Y.basicOpen_le t'),
      LinearEquiv.apply_symm_apply] at h
    exact h
  -- the final chart `V = D(e₁ e₂) ⊆ V₃`
  have he : e₁ * e₂ ∉ (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal := fun h =>
    ((inferInstance : (hV₃.primeIdealOf ⟨y, hyV₃⟩).asIdeal.IsMaximal).isPrime.mem_or_mem
      h).elim he₁ he₂
  have hyV : y ∈ Y.basicOpen (e₁ * e₂) := (mem_basicOpen_iff_notMem hV₃ hyV₃ _).mpr he
  have hV : IsAffineOpen (Y.basicOpen (e₁ * e₂)) := hV₃.basicOpen _
  have hVV₃ : Y.basicOpen (e₁ * e₂) ≤ Y.basicOpen s := Y.basicOpen_le _
  have hVW : Y.basicOpen (e₁ * e₂) ≤ ν ⁻¹ᵁ D.W := hVV₃.trans hV₃W
  have hu₁ : IsUnit (res hVV₃ e₁) := isUnit_map_of_le_basicOpen e₁
    (by rw [Scheme.basicOpen_mul]; exact inf_le_left) hVV₃
  have hu₂ : IsUnit (res hVV₃ e₂) := isUnit_map_of_le_basicOpen e₂
    (by rw [Scheme.basicOpen_mul]; exact inf_le_right) hVV₃
  obtain ⟨w, hwdef⟩ : ∃ w : Γ(Y, Y.basicOpen (e₁ * e₂)), w =
      res hVV₃ e₁ * ((hu₂.unit⁻¹ : (Γ(Y, Y.basicOpen (e₁ * e₂)))ˣ) : Γ(Y, Y.basicOpen (e₁ * e₂))) :=
    ⟨_, rfl⟩
  have hwu : IsUnit w := hwdef ▸ hu₁.mul (Units.isUnit _)
  have hw : res hVV₃ e₂ * w = res hVV₃ e₁ := by
    rw [hwdef, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have hβV : Function.Bijective fun c : Γ(Y, Y.basicOpen (e₁ * e₂)) =>
      c • (w • (relativeDifferentials q).presheaf.map (homOfLE hVV₃).op β₃) := by
    have h1 := bijective_smul_restrict_basicOpen _ hV₃ β₃ hβ₃ (e₁ * e₂)
    have : (fun c : Γ(Y, Y.basicOpen (e₁ * e₂)) =>
        c • (w • (relativeDifferentials q).presheaf.map (homOfLE hVV₃).op β₃)) =
        (fun c : Γ(Y, Y.basicOpen (e₁ * e₂)) =>
          c • (relativeDifferentials q).presheaf.map (homOfLE hVV₃).op β₃) ∘ (fun c => c * w) := by
      funext c
      simp only [Function.comp_apply, mul_smul]
    rw [this]
    obtain ⟨wu, hwu'⟩ := hwu
    rw [← hwu']
    exact h1.comp (Units.mulRight wu).bijective
  -- the opens
  have hPV : (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ Y.basicOpen (e₁ * e₂)) ≤
      Y.basicOpen t' := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, ← hfib]
    exact fun z hz => ⟨hVV₃ hz.2, hz.1⟩
  have hPVV := (fibreLocus f ν).ι.image_preimage_le (Y.basicOpen (e₁ * e₂))
  refine ⟨{
    W := D.W
    isAffineOpen_W := D.isAffineOpen_W
    σ := D.σ
    bijective_σ := D.bijective_σ
    V := Y.basicOpen (e₁ * e₂)
    isAffineOpen_V := hV
    le := hVW
    β := w • (relativeDifferentials q).presheaf.map (homOfLE hVV₃).op β₃
    bijective_β := hβV
    t := res hVV₃ t'
    eq := ?_ }, hyV, fun z hz hzV => hOE z (hV₂O (hV₃V₂ (hVV₃ hzV))) hz, ?_⟩
  · -- the chart equation `t θ(σ) = β` on `V ∩ ν⁻¹ Sm f`
    refine (logDifferentials_smul f q ν _ _ _).trans ?_
    rw [toLogDifferentials_app]
    change res hPVV (res hVV₃ t') • (relativeDifferentials q).presheaf.map
        (homOfLE (hPV.trans hP)).op
        (show Γ(relativeDifferentials q, (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ
          (ν ⁻¹ᵁ D.W))) from (dualizingComparison f q ν a sq).app D.W D.σ) = _
    have hu₂P : IsUnit (res hPVV (res hVV₃ e₂)) := hu₂.map _
    have key := smul_eq_of_mul_eq (Y.basicOpen_le t') hVV₃ hPV hPVV ζs β₃ hw hu₂P hid
    rw [hζs, map_map_eq] at key
    exact key
  · -- `Γ(V, 𝒪)/(t) ≅ K`
    exact finrank_quotient_basicOpen q hV₃ _ h𝔫' he

/-- **Pole charts at the points over the nodes** (blueprint `lem:sm-omega-bcf-pole-chart`,
`lem:sm-omega-cd-pole-chart`). Let `f : X ⟶ S` be a nodal curve over an integral, normal, locally
Noetherian scheme, smooth over the generic point, `K = K̄`, and `ν : Y ⟶ X`, `q : Y ⟶ Spec K`,
`ν ≫ f = q ≫ a`, with `Y` integral, locally Noetherian, normal, smooth of relative dimension one over
`K`, of dimension at most one and not a point. Let `E = ν⁻¹(X ∖ Sm f)` be a finite set of closed
points at which `ν` is unramified relative to the base change. Then every `y ∈ E` has a comparison
chart in which `ν^* ω` has a simple pole at `y` relative to `Ω¹_{Y/K}`. -/
theorem hasPoleCharts [IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S) (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x)
    [IsIntegral Y] [IsLocallyNoetherian Y] [SmoothOfRelativeDimension 1 q]
    (hnormal : IsNormalScheme Y) (hdim : topologicalKrullDim Y ≤ 1)
    (hpt : ∃ y : Y, y ≠ genericPoint Y) (E : Finset Y)
    (hE : ∀ z, z ∈ E ↔ ν z ∉ f.smoothLocus) (hEc : ∀ z ∈ E, IsClosed ({z} : Set Y))
    (hun : ∀ y ∈ E, IsUnramifiedAt f q ν y) :
    HasPoleCharts f q ν a sq E := by
  intro y hy
  have hyg : y ≠ genericPoint Y := by
    intro hyg
    obtain ⟨z, hz⟩ := hpt
    have h1 : z ∈ closure ({genericPoint Y} : Set Y) := by
      rw [genericPoint_closure]; trivial
    rw [← hyg, (hEc y hy).closure_eq, Set.mem_singleton_iff] at h1
    exact hz (h1.trans hyg)
  exact exists_poleChart f q ν a sq hS hgen hnormal hdim E hE hEc hy hyg (hun y hy)

end Assembly

end DeJongAlterations.StableModification.Omega.PoleChart
