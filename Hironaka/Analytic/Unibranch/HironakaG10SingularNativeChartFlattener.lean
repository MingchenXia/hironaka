import Hironaka.Resolution.HironakaG10HirChartFlattener

/-! The whole-ideal analytic chart flattener descends to a singular base. -/
set_option autoImplicit false
open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaChowPresentationIndependentFlattener HironakaG10HirFlatQuotient HironakaG10HirChartFlattener
namespace Hironaka.Analytic.Unibranch.HironakaG10SingularNativeChartFlattener
noncomputable section

/-- The original joint ideal contains the pullback of the base ideal, so
its actual chart map descends to the original singular base. -/
theorem chartMap_kills_baseIdeal (d t : ℕ)
    (J : Ideal (HolGerm (ComplexModel d))) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hJI : J.map (tangentPullback d t).toRingHom ≤ I) :
    ∀ a ∈ J, chartMap d t I a = 0 := by
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact hJI (Ideal.mem_map_of_mem _ ha)

/-- The actual ring map from the singular base to the original joint quotient. -/
def singularChartMap (d t : ℕ)
    (J : Ideal (HolGerm (ComplexModel d))) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hJI : J.map (tangentPullback d t).toRingHom ≤ I) :
    HolGerm (ComplexModel d) ⧸ J →+* HolGerm (ComplexModel (d+t)) ⧸ I :=
  Ideal.Quotient.lift J (chartMap d t I) (chartMap_kills_baseIdeal d t J I hJI)

/-- The whole joint ideal gives an actual flattener for the singular chart
map, with all further closed base germs, including nonreduced tests. -/
theorem isFlattenerIdeal_singularChartMap (d t : ℕ)
    (J : Ideal (HolGerm (ComplexModel d))) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hJI : J.map (tangentPullback d t).toRingHom ≤ I) :
    IsFlattenerIdeal (singularChartMap d t J I hJI)
      ((canonicalFlattenerIdeal d t I).map (Ideal.Quotient.mk J)) :=
  (isFlattenerIdeal_chartMap d t I).quotient_base J (chartMap_kills_baseIdeal d t J I hJI)
/-- A literal base-compatible pair of native stalk ring isomorphisms transfers
this whole-ideal flattener to the actual native stalk map. -/
theorem isFlattenerIdeal_of_chart_stalk_square (d t : ℕ)
    (J : Ideal (HolGerm (ComplexModel d))) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hJI : J.map (tangentPullback d t).toRingHom ≤ I)
    {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (e : (HolGerm (ComplexModel d) ⧸ J) ≃+* A)
    (f : (HolGerm (ComplexModel (d+t)) ⧸ I) ≃+* B)
    (hsq : ψ.comp e.toRingHom = f.toRingHom.comp (singularChartMap d t J I hJI)) :
    IsFlattenerIdeal ψ (((canonicalFlattenerIdeal d t I).map (Ideal.Quotient.mk J)).map e.toRingHom) := by
  have h := ((isFlattenerIdeal_singularChartMap d t J I hJI).ringEquiv_comp f).comp_ringEquiv e.symm
  have hcomp : (f.toRingHom.comp (singularChartMap d t J I hJI)).comp e.symm.toRingHom = ψ := by
    rw [← hsq]
    ext x
    simp
  rw [hcomp] at h
  have heq : ((canonicalFlattenerIdeal d t I).map (Ideal.Quotient.mk J)).map e.toRingHom =
      ((canonicalFlattenerIdeal d t I).map (Ideal.Quotient.mk J)).comap e.symm.toRingHom :=
    Ideal.map_comap_of_equiv e
  rw [heq]
  exact h

/-- Two actual smooth-product chart presentations of the same native stalk
map give the same ideal in the original base stalk. -/
theorem chart_flattener_independent_of_native_stalk
    (d₁ t₁ d₂ t₂ : ℕ)
    (J₁ : Ideal (HolGerm (ComplexModel d₁))) (I₁ : Ideal (HolGerm (ComplexModel (d₁+t₁))))
    (J₂ : Ideal (HolGerm (ComplexModel d₂))) (I₂ : Ideal (HolGerm (ComplexModel (d₂+t₂))))
    (h₁ : J₁.map (tangentPullback d₁ t₁).toRingHom ≤ I₁)
    (h₂ : J₂.map (tangentPullback d₂ t₂).toRingHom ≤ I₂)
    {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (e₁ : (HolGerm (ComplexModel d₁) ⧸ J₁) ≃+* A)
    (f₁ : (HolGerm (ComplexModel (d₁+t₁)) ⧸ I₁) ≃+* B)
    (e₂ : (HolGerm (ComplexModel d₂) ⧸ J₂) ≃+* A)
    (f₂ : (HolGerm (ComplexModel (d₂+t₂)) ⧸ I₂) ≃+* B)
    (hs₁ : ψ.comp e₁.toRingHom = f₁.toRingHom.comp (singularChartMap d₁ t₁ J₁ I₁ h₁))
    (hs₂ : ψ.comp e₂.toRingHom = f₂.toRingHom.comp (singularChartMap d₂ t₂ J₂ I₂ h₂)) :
    ((canonicalFlattenerIdeal d₁ t₁ I₁).map (Ideal.Quotient.mk J₁)).map e₁.toRingHom =
      ((canonicalFlattenerIdeal d₂ t₂ I₂).map (Ideal.Quotient.mk J₂)).map e₂.toRingHom :=
  (isFlattenerIdeal_of_chart_stalk_square d₁ t₁ J₁ I₁ h₁ ψ e₁ f₁ hs₁).unique
    (isFlattenerIdeal_of_chart_stalk_square d₂ t₂ J₂ I₂ h₂ ψ e₂ f₂ hs₂)

end
end Hironaka.Analytic.Unibranch.HironakaG10SingularNativeChartFlattener
