import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeHeights
import Hironaka.Geometry.SNCSubdivisorTopology

/-! Native pure stalk codimension of the actual full mixed node boundary intersections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeCodimension

open SpecIdealSheaf ReducedClosedSubscheme Scheme.IdealSheafData
open Algebra.NodeBlowupChart MonomialBlowupRegularBaseSNCIntersection
open MonomialBlowupRegularBaseSNCNodeIntersections MonomialBlowupRegularBaseSNCNodeHeights

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

/-- Actual minimal-prime heights compute native ambient stalk codimension, even for reducible intersections. -/
theorem hasPureCodimension_of_minimalPrime_height (I : Ideal A) (r : ℕ)
    (hI : ∀ q ∈ I.minimalPrimes, q.height = r) :
    HasPureCodimension (specIdealSheaf A I).support r := by
  let E := specIdealSheaf A I
  intro S hS x hx
  let C : DivisorComponent E := divisorComponentOf E S hS
  have hC : (C.val : Set (Spec (CommRingCat.of A))) =
      (Subtype.val : E.support → Spec (CommRingCat.of A)) '' S := rfl
  have hxC : IsGenericPoint x (C.val : Set (Spec (CommRingCat.of A))) := by
    rw [hC]
    exact hx
  have hIp : I ≤ (show PrimeSpectrum A from x).asIdeal := by
    have hxE := SNCSubdivisorComponent.component_le_support E C hxC.mem
    change x ∈ ((specIdealSheaf A I).support : Set (Spec (CommRingCat.of A))) at hxE
    rw [specIdealSheaf_support] at hxE
    exact hxE
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hIp
  let : q.IsPrime := hq.isPrime
  let y : Spec (CommRingCat.of A) := (⟨q, inferInstance⟩ : PrimeSpectrum A)
  have hTirr : IsIrreducible (PrimeSpectrum.zeroLocus (q : Set A)) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical q ‹q.IsPrime›.isRadical).mpr inferInstance
  have hCT : (C.val : Set (Spec (CommRingCat.of A))) ⊆ PrimeSpectrum.zeroLocus (q : Set A) :=
    hxC.mem_closed_set_iff (PrimeSpectrum.isClosed_zeroLocus _ ) |>.mp hqp
  have hTE : PrimeSpectrum.zeroLocus (q : Set A) ⊆ (E.support : Set (Spec (CommRingCat.of A))) := by
    rw [specIdealSheaf_support]
    exact PrimeSpectrum.zeroLocus_anti_mono hq.le
  have hTC := SNCSubdivisorTopology.component_maximal E C _ hTirr hCT hTE
  have hyC : y ∈ (C.val : Set (Spec (CommRingCat.of A))) := hTC (show q ≤ q from le_rfl)
  have hpq : (show PrimeSpectrum A from x).asIdeal ≤ q :=
    (PrimeSpectrum.le_iff_specializes (show PrimeSpectrum A from x) y).mpr (hxC.specializes hyC)
  have heq : (show PrimeSpectrum A from x).asIdeal = q := le_antisymm hpq hqp
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight, heq, hI q hq]
  rfl

local instance componentDecidableEq (D : (Spec (CommRingCat.of A)).IdealSheafData) :
    DecidableEq (DivisorComponent D) := Classical.typeDecidableEq _

/-- Actual original SNC data gives exact native pure codimension for each full mixed node intersection. -/
theorem mixed_support_hasPureCodimension [IsNoetherianRing A]
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (a : J → A)
    (ha : ∀ j, specIdealSheaf A (Ideal.span {a j}) = vanishingIdeal j.val.val)
    (C : DivisorComponent D) (hC : C ∉ J) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) (s : Finset (Fin 2)) :
    HasPureCodimension (specIdealSheaf (Node A t)
      (mixedIdeal (intersectionIdeal D J) t s)).support (J.card + s.card) :=
  hasPureCodimension_of_minimalPrime_height _ _
    (fun P hP ↦ mixed_minimalPrime_height D hD J a ha C hC t heq s P hP)

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeCodimension
