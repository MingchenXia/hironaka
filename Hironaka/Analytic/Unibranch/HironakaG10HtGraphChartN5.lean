import Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation

/-!
# N5 for any ring map isomorphic to an analytic graph chart of a blowup

Lane G10HT, run 0081 (N5 of `G10HT/hT-route-decision.md`; Hironaka 1975, p. 532).  The algebraic strict ideal is
transported by isomorphic commutative squares (`strictIdeal_eq_powerSat_transport`), so the analytic chart result
`HironakaG10HtChartSaturation.analyticChart_strictIdeal_eq_powerSat` gives:

* **`strictIdeal_eq_powerSat_of_graphChart`** — for a ring map `φ : A → R` isomorphic (rings `A ≅ H_d ⧸ IX`,
  `R ≅ H_{d+r+1} ⧸ (evPoly(L) : X_j^∞)`) to the chart map of a graph chart of a blowup, with the centre `D` of `A`
  corresponding to `(g)` and a regular `G ∈ R` generating the same principal ideal as `X_j`: for EVERY ideal
  `I` of `A`, `strictIdeal φ I D G = powerSat (I R) G`.

The native N5 (G10HT's form in `G10HT/STATUS.md`) follows once the native stalk map of a blowup step is exhibited
in this form at every point (sub-item N5.b: the ring isomorphisms `α`, `ρ` and the square).

Pure algebra on top of the proved chart result; no named input.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartN5

open MvPolynomial Hironaka Hironaka
open Hironaka.HironakaG10ChowArtinReesCentre
  Hironaka.HironakaG10StrictIdealGenerator
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10HtStrictSaturation
  Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation

noncomputable section

/-- **Transport of "strict ideal = saturation"** along an isomorphic commutative square, with a change of the
regular generator inside the same principal ideal. -/
theorem strictIdeal_eq_powerSat_transport {A R A₂ R₂ : Type*} [CommRing A] [CommRing R] [CommRing A₂]
    [CommRing R₂] (φ : A →+* R) (φ₂ : A₂ →+* R₂) (α : A ≃+* A₂) (ρ : R ≃+* R₂)
    (hsq : ∀ a, ρ (φ a) = φ₂ (α a)) (I D : Ideal A) (G : R) (G₂ : R₂) (hG : IsRegular G)
    (hGG : Ideal.span {ρ G} = Ideal.span {G₂})
    (h₂ : powerSat (Ideal.map φ₂ (Ideal.map (α : A →+* A₂) I)) G₂ ≤
      strictIdeal φ₂ (Ideal.map (α : A →+* A₂) I) (Ideal.map (α : A →+* A₂) D) G₂) :
    strictIdeal φ I D G = powerSat (Ideal.map φ I) G := by
  refine le_antisymm (strictIdeal_le_powerSat φ I D G) ?_
  have hρG : IsRegular ((ρ : R →+* R₂) G) := by
    refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      obtain ⟨y, rfl⟩ := ρ.surjective y
      dsimp only at hxy
      rw [RingEquiv.coe_toRingHom, ← map_mul, ← map_mul] at hxy
      exact congrArg ρ (hG.left (ρ.injective hxy))
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      obtain ⟨y, rfl⟩ := ρ.surjective y
      dsimp only at hxy
      rw [RingEquiv.coe_toRingHom, ← map_mul, ← map_mul] at hxy
      exact congrArg ρ (hG.right (ρ.injective hxy))
  have hGG' : Ideal.span {(ρ : R →+* R₂) G} = Ideal.span {G₂} := hGG
  have hsq' : ∀ b, ρ.symm (φ₂ b) = φ (α.symm b) := by
    intro b
    apply ρ.injective
    rw [RingEquiv.apply_symm_apply, hsq, RingEquiv.apply_symm_apply]
  have htot : Ideal.map (ρ : R →+* R₂) (Ideal.map φ I) =
      Ideal.map φ₂ (Ideal.map (α : A →+* A₂) I) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact hsq a
  have hmodel := h₂
  rw [← powerSat_eq_of_regular_span_eq _ hρG hGG', ← strictIdeal_eq_of_regular_span_eq _ _ _ hρG hGG']
    at hmodel
  intro a ha
  have h1 : (ρ : R →+* R₂) a ∈
      powerSat (Ideal.map (ρ : R →+* R₂) (Ideal.map φ I)) ((ρ : R →+* R₂) G) :=
    map_powerSat_le (ρ : R →+* R₂) _ G (Ideal.mem_map_of_mem _ ha)
  rw [htot] at h1
  have h2 := map_strictIdeal_le φ₂ φ (α.symm : A₂ →+* A) (ρ.symm : R₂ →+* R) hsq'
    (Ideal.map (α : A →+* A₂) I) (Ideal.map (α : A →+* A₂) D) ((ρ : R →+* R₂) G)
    (Ideal.mem_map_of_mem _ (hmodel h1))
  have hIα : ∀ J : Ideal A, Ideal.map (α.symm : A₂ →+* A) (Ideal.map (α : A →+* A₂) J) = J := by
    intro J
    rw [Ideal.map_map]
    convert Ideal.map_id J
    ext x
    exact α.symm_apply_apply x
  simp only [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h2
  rwa [hIα, hIα] at h2

/-- **N5 on anything isomorphic to an analytic graph chart of a blowup.** -/
theorem strictIdeal_eq_powerSat_of_graphChart {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R)
    (d r : ℕ) (b : Fin (r + 1) → ℂ) (j : Fin (r + 1)) (g : Fin (r + 1) → HolGerm (ComplexModel d))
    (IX : Ideal (HolGerm (ComplexModel d)))
    (α : A ≃+* HolGerm (ComplexModel d) ⧸ IX)
    (ρ : R ≃+* HolGerm (ComplexModel (d + (r + 1))) ⧸ chartIdeal (evPoly d (r + 1) b) j g IX)
    (hsq : ∀ a, ρ (φ a) = chartMap (evPoly d (r + 1) b) j g IX (α a))
    (D : Ideal A)
    (hD : Ideal.map (α : A →+* HolGerm (ComplexModel d) ⧸ IX) D =
      Ideal.map (Ideal.Quotient.mk IX) (Ideal.span (Set.range g)))
    (G : R) (hG : IsRegular G)
    (hGe : Ideal.span {ρ G} =
      Ideal.span {Ideal.Quotient.mk (chartIdeal (evPoly d (r + 1) b) j g IX) (evPoly d (r + 1) b (X j))})
    (I : Ideal A) :
    strictIdeal φ I D G = powerSat (Ideal.map φ I) G := by
  set Ĩ := Ideal.comap (Ideal.Quotient.mk IX) (Ideal.map (α : A →+* HolGerm (ComplexModel d) ⧸ IX) I)
  have hXI : IX ≤ Ĩ := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  have hĨ : Ideal.map (Ideal.Quotient.mk IX) Ĩ = Ideal.map (α : A →+* HolGerm (ComplexModel d) ⧸ IX) I :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  refine strictIdeal_eq_powerSat_transport φ (chartMap (evPoly d (r + 1) b) j g IX) α ρ hsq I D G _ hG hGe ?_
  have hchart := (analyticChart_strictIdeal_eq_powerSat d r b j g IX Ĩ hXI).ge
  rwa [hĨ, ← hD] at hchart

end

end Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartN5
