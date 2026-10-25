import DeJongAlterations.Geometry.CartierDominantPullback
import DeJongAlterations.Geometry.SNCSubdivisorTopology
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Actual Cartier supports have pure codimension one

Actual support components determine minimal primes of the full coordinate
ideal. Krull's principal ideal theorem and native affine stalk heights then
prove the pure-codimension input to source 4.9.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CartierPureCodimension

open SpecIdealSheaf ReducedClosedSubscheme

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R]

/-- The actual generic point of a support component represents a minimal prime. -/
theorem mem_minimalPrimes_of_component_genericPoint (I : Ideal R)
    (C : Set (specIdealSheaf R I).support)
    (hC : C ∈ irreducibleComponents (specIdealSheaf R I).support)
    (x : Spec (CommRingCat.of R)) (hx : IsGenericPoint x (Subtype.val '' C)) :
    x.asIdeal ∈ I.minimalPrimes := by
  let D := specIdealSheaf R I
  let C₀ := divisorComponentOf D C hC
  have hxD : x ∈ D.support := by
    obtain ⟨z, _, hzx⟩ := hx.mem
    exact hzx ▸ z.property
  have hIx : I ≤ x.asIdeal := by
    change x ∈ PrimeSpectrum.zeroLocus (I : Set R)
    rwa [← specIdealSheaf_support R I]
  refine ⟨⟨x.isPrime, hIx⟩, ?_⟩
  intro Q hQ hQP
  let : Q.IsPrime := hQ.1
  let q : PrimeSpectrum R := ⟨Q, inferInstance⟩
  have hCsub : (C₀.val : Set (Spec (CommRingCat.of R))) ⊆
      PrimeSpectrum.zeroLocus (Q : Set R) := by
    change (Subtype.val '' C) ⊆ _
    rw [← hx.def]
    exact (PrimeSpectrum.isClosed_zeroLocus (Q : Set R)).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hQP)
  have hT : IsIrreducible (PrimeSpectrum.zeroLocus (Q : Set R)) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _
      hQ.1.isRadical).mpr hQ.1
  have hTD : PrimeSpectrum.zeroLocus (Q : Set R) ⊆
      (D.support : Set (Spec (CommRingCat.of R))) := by
    rw [specIdealSheaf_support]
    exact PrimeSpectrum.zeroLocus_anti_mono_ideal hQ.2
  have hTC := SNCSubdivisorTopology.component_maximal D C₀ _ hT hCsub hTD
  have hqC : q ∈ Subtype.val '' C := hTC (show q ∈
      PrimeSpectrum.zeroLocus (Q : Set R) from le_refl Q)
  exact (PrimeSpectrum.le_iff_specializes x q).mpr (hx.specializes hqC)

/-- A nonzero principal coordinate ideal has actual pure codimension one. -/
theorem hasPureCodimension_span [IsDomain R] [IsNoetherianRing R]
    (t : R) (ht : t ≠ 0) :
    HasPureCodimension (specIdealSheaf R (Ideal.span {t})).support 1 := by
  intro C hC x hx
  have hp := mem_minimalPrimes_of_component_genericPoint (Ideal.span {t}) C hC x hx
  have hle : x.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp
  have htmem : t ∈ x.asIdeal := hp.le (by simp)
  have hpne : x.asIdeal ≠ ⊥ := by
    intro h
    exact ht (by simpa only [h, Ideal.mem_bot] using htmem)
  have hge : 1 ≤ x.asIdeal.height :=
    Order.one_le_iff_ne_zero.mpr fun h => hpne (Ideal.height_eq_zero_iff_eq_bot.mp h)
  have hheight : x.asIdeal.height = 1 := le_antisymm hle hge
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
  exact_mod_cast hheight

variable {X Y : Scheme.{u}}

/-- Every actual Cartier support on a locally Noetherian integral scheme has pure codimension one. -/
theorem hasPureCodimension (D : X.IdealSheafData)
    [IsIntegral X] [IsLocallyNoetherian X] (hD : IsEffectiveCartierDivisor D) :
    HasPureCodimension D.support 1 := by
  intro C hC x hx
  obtain ⟨U, hxU, t, ht, hDt⟩ := hD x
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have ht0 : t ≠ 0 := by
    intro h
    exact zero_ne_one (ht.left (by simp [h]))
  have hlocal : HasPureCodimension (D.comap U.2.fromSpec).support 1 := by
    rw [BlowupCartier.comap_fromSpec, hDt]
    exact hasPureCodimension_span t ht0
  exact SNCLocality.krullDim_at_genericPoint_of_comap U.2.fromSpec D hlocal C hC x hx
    (U.2.primeIdealOf ⟨x, hxU⟩) (U.2.fromSpec_primeIdealOf ⟨x, hxU⟩)

/-- Dominant integral pullback retains actual pure codimension of the full Cartier inverse ideal. -/
theorem hasPureCodimension_comap (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsLocallyNoetherian X]
    (D : Y.IdealSheafData) (hD : IsEffectiveCartierDivisor D) :
    HasPureCodimension (D.comap f).support 1 :=
  hasPureCodimension _ (CartierDominantPullback.isEffectiveCartierDivisor_comap f D hD)

end DeJongAlterations.Geometry.CartierPureCodimension
