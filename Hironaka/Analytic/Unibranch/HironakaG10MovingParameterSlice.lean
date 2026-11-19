import Hironaka.Resolution.HironakaRelativeNormalNormalPowerSpread
import Hironaka.Resolution.HironakaActualJointBaseFibre

/-! # Moving parameter slices of actual normal-power quotient identities -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10MovingParameterSlice
open Hironaka Hironaka
  OkaRelationSheaf HironakaRelativeNormalIdeal HironakaActualJointBaseFibre
  HironakaRelativeNormalNormalPowerSpread HironakaHolomorphicJetRankLoci
  HironakaRelativeNormalCoherentTranslatedJets

/-- An actual whole normal-power quotient identity remains an equality
after the normal slice and any parameter quotient killing the same power. -/
theorem parameterSlice_eq_of_normal_power_quotient
    {Q : Type*} [CommRing Q] [Algebra ℂ Q] (t d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q ≤
      RingHom.ker φ.toRingHom)
    {f g : HolGerm (ComplexModel (t+d))}
    (h : Ideal.Quotient.mk (normalIdeal t d ^ q) f =
      Ideal.Quotient.mk (normalIdeal t d ^ q) g) :
    φ (jointBaseZeroTrace t d f) = φ (jointBaseZeroTrace t d g) := by
  have hmem : f-g ∈ normalIdeal t d ^ q := Ideal.Quotient.eq.mp h
  have himage := Ideal.mem_map_of_mem (jointBaseZeroTrace t d).toRingHom hmem
  rw [Ideal.map_pow, map_jointNormalIdeal_eq_maximalIdeal] at himage
  have hz := hφ himage
  change φ (jointBaseZeroTrace t d (f-g)) = 0 at hz
  simpa only [map_sub, sub_eq_zero] using hz

/-- An actual normal-power quotient identity at the original joint point
gives the same parameter-slice quotient value at every nearby point of the
same original fibre plane, on one genuinely open neighborhood. -/
theorem exists_nearby_parameterSlice_identity
    {Q : Type*} [CommRing Q] [Algebra ℂ Q] (t d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q ≤
      RingHom.ker φ.toRingHom)
    {f g : ComplexModel (t+d) → ℂ} (hf : HolAt f 0) (hg : HolAt g 0)
    (h : Ideal.Quotient.mk (normalIdeal t d ^ q) (HolGerm.mk f hf) =
      Ideal.Quotient.mk (normalIdeal t d ^ q) (HolGerm.mk g hg)) :
    ∃ U : Set (ComplexModel (t+d)), IsOpen U ∧ 0 ∈ U ∧
      ∃ hF : ∀ a ∈ U, HolAt (f ∘ actualAffineTranslation (t+d) a) 0,
      ∃ hG : ∀ a ∈ U, HolAt (g ∘ actualAffineTranslation (t+d) a) 0,
      ∀ a (ha : a ∈ U), a ∈ complexCoordinatePlane (t+d) t →
        φ (jointBaseZeroTrace t d (HolGerm.mk (f ∘ actualAffineTranslation (t+d) a) (hF a ha))) =
        φ (jointBaseZeroTrace t d (HolGerm.mk (g ∘ actualAffineTranslation (t+d) a) (hG a ha))) := by
  obtain ⟨U,hU,h0,hF,hG,hquot⟩ := exists_actual_nearby_whole_quotient_identity t d q hf hg h
  refine ⟨U,hU,h0,hF,hG,?_⟩
  intro a ha hp
  exact parameterSlice_eq_of_normal_power_quotient t d q φ hφ (hquot a ha hp)

end Hironaka.Analytic.Unibranch.HironakaG10MovingParameterSlice
