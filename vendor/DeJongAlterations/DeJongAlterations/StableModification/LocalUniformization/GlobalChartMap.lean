import DeJongAlterations.StableModification.LocalUniformization.GlobalField
import DeJongAlterations.StableModification.LocalUniformization.GlobalTransport

/-!
# Valuations through étale charts

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (T:2976–2983): "Let `𝔵̄` be the image of `𝔵` in `RZ_{k(C̄)}(C̄)`, that is
`𝒪_{𝔵̄} = 𝒪_𝔵 ∩ k(C̄)`". For a valuation `vL` of `L = K(C)` centred at a point `y` of an open `Y`
of `C` with an étale chart `e : Y → Spec N`, the ring map `ι : N → L` of the generic point is
injective, `ι(N) ⊆ 𝒪_{vL}` and `e(y) = ι⁻¹(𝔪_{vL})` (`exists_chartRingHom`). Over the
localized base `B = 𝒪_{vL} ∩ K`, the ring map is a `B`-algebra map (`chartRingHom_algebraMap`).
Together with `GlobalField` and `GlobalResidue` these are the inputs of T43M's model stages.
Blueprint `lem:sm-cofinal-chart-valuation` (`sm-local-uniformization.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {Γ₁ : Type u}
  [LinearOrderedCommGroupWithZero Γ₁] (vL : Valuation L Γ₁)

local notation "K₀" => Valuation.valuationSubring (Valuation.comap (algebraMap K L) vL)
local notation "L₀" => Valuation.valuationSubring vL

/-- The valuation ring of `vL`, seen as a point of the Riemann–Zariski space. -/
abbrev rzOf : RiemannZariskiSpace L := ⟨L₀⟩

/-- Every point of the Riemann–Zariski space is `rzOf` of its valuation. -/
theorem rzOf_eq (V : RiemannZariskiSpace L) : rzOf V.valuationSubring.valuation = V :=
  RiemannZariskiSpace.ext (ValuationSubring.valuationSubring_valuation _)

/-- `vL` and the valuation of its valuation ring have the same integers. -/
theorem valuationSubring_valuation_le_one_iff (x : L) :
    vL.valuationSubring.valuation x ≤ 1 ↔ vL x ≤ 1 :=
  (Valuation.isEquiv_valuation_valuationSubring vL).le_one_iff_le_one.symm

/-- `vL` and the valuation of its valuation ring have the same maximal ideal. -/
theorem valuationSubring_valuation_lt_one_iff (x : L) :
    vL.valuationSubring.valuation x < 1 ↔ vL x < 1 :=
  (Valuation.isEquiv_valuation_valuationSubring vL).lt_one_iff_lt_one.symm

variable {O : ValuationSubring K}

/-- **The valuation ring `𝒪_{vL} ∩ K` contains `O`** when `vL` is centred on an `O`-scheme. -/
theorem le_of_isCentre {X : Scheme.{u}} {η : Spec (.of L) ⟶ X} (q : X ⟶ Spec (.of O))
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype))) {y : X}
    (hy : IsCentre η (rzOf vL) y) : O ≤ K₀ := by
  intro o ho
  have h := (hy.ringHom q _ hq ⟨o, ho⟩).1
  rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply]
  exact (valuationSubring_valuation_le_one_iff vL _).mp h

/-- **The centre lies over `𝔭 = 𝔪_{vL} ∩ O`.** -/
theorem asIdeal_eq_idealOfLE {X : Scheme.{u}} {η : Spec (.of L) ⟶ X} (q : X ⟶ Spec (.of O))
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype))) {y : X}
    (hy : IsCentre η (rzOf vL) y) :
    (q y).asIdeal = O.idealOfLE K₀ (le_of_isCentre vL q hq hy) := by
  ext o
  rw [(hy.ringHom q _ hq o).2, valuationSubring_valuation_lt_one_iff]
  change _ ↔ ValuationSubring.inclusion O K₀ _ o ∈ maximalIdeal K₀
  rw [ValuationSubring.valuation_lt_one_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  rfl

/-- **Ring maps of charts.** Let `η : Spec L → X` hit the generic point of the integral `X`,
`j : Y → X` an open immersion, `e : Y → Spec N` flat with `N` a domain, and `vL` centred at
`j y`. Then `η` lifts to `ηY : Spec L → Y`, the ring map `ι : N → L` of `ηY ≫ e` is injective,
`ι(N) ⊆ 𝒪_{vL}`, and `e(y) = ι⁻¹(𝔪_{vL})`. -/
theorem exists_chartRingHom {X : Scheme.{u}} [IsIntegral X] {η : Spec (.of L) ⟶ X}
    (hη : ∀ z, η z = genericPoint X) {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {N : Type u} [CommRing N] [IsDomain N] (e : Y ⟶ Spec (.of N)) [Flat e] {y : Y}
    (hy : IsCentre η (rzOf vL) (j y)) :
    ∃ (ηY : Spec (.of L) ⟶ Y) (ι : N →+* L), ηY ≫ j = η ∧
      Spec.map (CommRingCat.ofHom ι) = ηY ≫ e ∧ Function.Injective ι ∧
      IsCentre ηY (rzOf vL) y ∧ ∀ n, vL (ι n) ≤ 1 ∧ (n ∈ (e y).asIdeal ↔ vL (ι n) < 1) := by
  have : Nonempty Y := ⟨y⟩
  have : IsIntegral Y := isIntegral_of_isOpenImmersion j
  have hjgen : j (genericPoint Y) = genericPoint X := genericPoint_eq_of_isOpenImmersion j
  have hrange : Set.range η ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact ⟨genericPoint Y, by rw [hjgen, hη]⟩
  let ηY := IsOpenImmersion.lift j η hrange
  have hηY : ηY ≫ j = η := IsOpenImmersion.lift_fac _ _ _
  have hηYgen : ∀ z, ηY z = genericPoint Y := fun z ↦ j.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hηY, hη, hjgen])
  let ι : N →+* L := (Spec.preimage (ηY ≫ e)).hom
  have hι : Spec.map (CommRingCat.ofHom ι) = ηY ≫ e := Spec.map_preimage _
  have hcen : IsCentre ηY (rzOf vL) y := IsCentre.of_isOpenImmersion j hηY hy
  refine ⟨ηY, ι, hηY, hι, injective_of_flat hηYgen e ι hι.symm, hcen, fun n ↦ ?_⟩
  have h := hcen.ringHom e ι hι.symm n
  rw [valuationSubring_valuation_le_one_iff, valuationSubring_valuation_lt_one_iff] at h
  exact h

end DeJongAlterations.StableModification.LocalUniformization
