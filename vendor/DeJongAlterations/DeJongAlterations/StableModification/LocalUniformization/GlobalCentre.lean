import DeJongAlterations.StableModification.ValCurves.ModificationsGamma

/-!
# Centres of valuations along affine maps and open immersions

Tools for passing the centre of a valuation ring `V` of a field `L` (`ValCurves.IsCentre`) between
schemes, used in the global form of M. Temkin, *Stable modification of relative curves*, J.
Algebraic Geom. 19 (2010), Proposition 4.3.1 (T:2976–2983: "Let `𝔵̄` be the image of `𝔵` in
`RZ_{k(C̄)}(C̄)` ... `C' := C̄' ×_C̄ C`"). Blueprint `lem:sm-cofinal-centres`
(`sm-local-uniformization.tex`).

* `IsCentre.specializes`: the image of `η` specializes to the centre.
* `IsCentre.ringHom`: for a morphism `q : X → Spec N` with `η ≫ q = Spec θ`, the centre of `V`
  maps to `θ⁻¹(𝔪_V)`, and `θ(N) ⊆ V`.
* `IsCentre.of_isOpenImmersion`: centres pass to open subschemes containing them.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace DeJongAlterations.StableModification.ValCurves

open RiemannZariskiSpace

variable {L : Type u} [Field L] {X : Scheme.{u}} {η : Spec (.of L) ⟶ X}

/-- The image of `η` specializes to every centre. -/
theorem IsCentre.specializes {V : RiemannZariskiSpace L} {y : X} (h : IsCentre η V y)
    (z : Spec (.of L)) : η z ⤳ y := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  rw [← hψ, Scheme.Hom.comp_apply]
  exact (specializes_closedPoint _).map ψ.continuous

/-- **Centres along an affine map.** If `η ≫ q = Spec θ` for `q : X → Spec N` and `V` is centred
at `y`, then `θ(N) ⊆ V` and the point `q y` is the prime `θ⁻¹(𝔪_V)`. -/
theorem IsCentre.ringHom {V : RiemannZariskiSpace L} {y : X} (h : IsCentre η V y)
    {N : Type u} [CommRing N] (q : X ⟶ Spec (.of N)) (θ : N →+* L)
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom θ)) (r : N) :
    V.valuationSubring.valuation (θ r) ≤ 1 ∧
      (r ∈ (q y).asIdeal ↔ V.valuationSubring.valuation (θ r) < 1) := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  let θ' : CommRingCat.of N ⟶ CommRingCat.of V.valuationSubring := Spec.preimage (ψ ≫ q)
  have hθ' : Spec.map θ' = ψ ≫ q := Spec.map_preimage _
  have hcomp : θ' ≫ CommRingCat.ofHom (algebraMap V.valuationSubring L) = CommRingCat.ofHom θ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ', ← hq, ← hψ, Category.assoc]
  have hr : ((θ' r : V.valuationSubring) : L) = θ r := by
    have h2 : (CommRingCat.ofHom θ).hom r = θ r := rfl
    rw [← h2, ← hcomp]
    rfl
  refine ⟨hr ▸ (V.valuationSubring.valuation_le_one (θ' r)), ?_⟩
  have hy : (q (ψ (specClosedPoint V))).asIdeal = Ideal.comap θ'.hom (maximalIdeal _) := by
    rw [← Scheme.Hom.comp_apply, ← hθ']
    rfl
  rw [hy, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hr]

/-- **Centres on open subschemes.** If `η` factors through an open immersion `j : Y → X` as
`η' ≫ j` and `V` is centred at `j y`, then `V` is centred at `y` with respect to `η'`. -/
theorem IsCentre.of_isOpenImmersion {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {η' : Spec (.of L) ⟶ Y} (hη : η' ≫ j = η) {V : RiemannZariskiSpace L} {y : Y}
    (h : IsCentre η V (j y)) : IsCentre η' V y := by
  obtain ⟨ψ, hψ, hψy⟩ := h
  have hrange : Set.range ψ ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    have hw : ψ w ⤳ ψ (specClosedPoint V) :=
      (specializes_closedPoint w).map ψ.continuous
    rw [hψy] at hw
    exact hw.mem_open j.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  let ψ' := IsOpenImmersion.lift j ψ hrange
  have hψ' : ψ' ≫ j = ψ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨ψ', ?_, ?_⟩
  · rw [← cancel_mono j, Category.assoc, hψ', hψ, hη]
  · apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hψ', hψy]

end DeJongAlterations.StableModification.ValCurves
