import Hironaka.Geometry.MonomialBlowupRegularBaseSNCIntersection
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCCotangent

/-! Genuine distinct SNC component equations are simultaneous actual local cotangent parameters. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCIndependence

open SpecIdealSheaf Scheme.IdealSheafData MonomialBlowupRegularBaseSNCIntersection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {A : Type u} [CommRing A]

local instance componentDecidableEq (D : (Spec (CommRingCat.of A)).IdealSheafData) :
    DecidableEq (DivisorComponent D) := Classical.typeDecidableEq _

/-- The actual intersection ideal is the span of the specified original component equations. -/
theorem intersectionIdeal_eq_span {ι : Type v} [Fintype ι]
    (D : (Spec (CommRingCat.of A)).IdealSheafData)
    (C : ι → DivisorComponent D) (t : ι → A)
    (heq : ∀ i, specIdealSheaf A (Ideal.span {t i}) = vanishingIdeal (C i).val) :
    intersectionIdeal D (Finset.univ.image C) = Ideal.span (Set.range t) := by
  classical
  apply (specIdealSheafEquiv A).symm.injective
  change specIdealSheaf A (intersectionIdeal D (Finset.univ.image C)) =
    specIdealSheaf A (Ideal.span (Set.range t))
  rw [intersectionIdeal_spec]
  have hcomp : componentIntersection D (Finset.univ.image C) = ⨆ i, vanishingIdeal (C i).val := by
    apply le_antisymm
    · refine iSup_le fun C' ↦ iSup_le fun hC' ↦ ?_
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC'
      exact le_iSup (fun i ↦ vanishingIdeal (C i).val) i
    · refine iSup_le fun i ↦ ?_
      exact le_iSup_of_le (C i) (le_iSup_of_le (Finset.mem_image_of_mem C (Finset.mem_univ i)) le_rfl)
  calc
    componentIntersection D (Finset.univ.image C) = ⨆ i, vanishingIdeal (C i).val := hcomp
    _ = ⨆ i, specIdealSheaf A (Ideal.span {t i}) := iSup_congr fun i ↦ (heq i).symm
    _ = specIdealSheaf A (⨆ i, Ideal.span {t i}) := ((specIdealSheafEquiv A).symm.map_iSup _).symm
    _ = specIdealSheaf A (Ideal.span (Set.range t)) := by rw [Ideal.span_range_eq_iSup]

variable [IsRegularRing A]

/-- The original equations of distinct genuine SNC components have independent actual cotangent classes.
The full native SNC intersection hypotheses supply the actual localized height internally. -/
theorem original_equations_independent {ι : Type v} [Fintype ι]
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : ι → DivisorComponent D) (hC : Function.Injective C) (t : ι → A)
    (heq : ∀ i, specIdealSheaf A (Ideal.span {t i}) = vanishingIdeal (C i).val)
    (p : Ideal A) [p.IsPrime] (ht : ∀ i, t i ∈ p) :
    LinearIndependent (ResidueField (Localization.AtPrime p))
      (fun i ↦ (maximalIdeal (Localization.AtPrime p)).toCotangent
        ⟨algebraMap A (Localization.AtPrime p) (t i),
          (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p _).mpr (ht i)⟩) := by
  classical
  by_cases hι : Nonempty ι
  · let := hι
    let J := Finset.univ.image C
    have hJ : J.Nonempty := Finset.univ_nonempty.image C
    let I := Ideal.span (Set.range t)
    have hIp : I ≤ p := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ht i)
    have hI : intersectionIdeal D J = I := intersectionIdeal_eq_span D C t heq
    have hdata := intersection_local_data D hD J hJ p (by rw [hI]; exact hIp)
    rw [hI] at hdata
    let L := Localization.AtPrime p
    let tL : ι → maximalIdeal L := fun i ↦
      ⟨algebraMap A L (t i), (IsLocalization.AtPrime.to_map_mem_maximal_iff L p _).mpr (ht i)⟩
    have hmap : I.map (algebraMap A L) = Ideal.span (Set.range fun i ↦ (tL i : L)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let : IsRegularLocalRing (L ⧸ Ideal.span (Set.range fun i ↦ (tL i : L))) := by
      rw [← hmap]
      exact hdata.1
    have hheight : (Fintype.card ι : ℕ∞) ≤
        (Ideal.span (Set.range fun i ↦ (tL i : L))).height := by
      rw [← hmap, hdata.2]
      have hc : J.card = Fintype.card ι :=
        (Finset.card_image_of_injective _ hC).trans Finset.card_univ
      rw [hc]
    exact MonomialBlowupRegularBaseSNCCotangent.original_generators_independent tL hheight
  · let : IsEmpty ι := not_nonempty_iff.mp hι
    exact linearIndependent_empty_type

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCIndependence
