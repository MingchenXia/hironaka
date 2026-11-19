import Hironaka.Resolution.Algebraic.ActualPaddedEnvelopeNativeTranslations
import Hironaka.Scheme.BlowUpSequence.Pullback

/-!
# Actual SAME-tail transport through a genuine geometric first-blowup lift

Source-first proof: `actual-native-tail-translation-transport-20261102.tex`.
No new resolution run, clock reset or deletion of empty positions occurs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualNativeTailTranslationTransport

noncomputable section

private theorem sequence_eq_pullback_cast {E F : Scheme.{u}} (h : E = F)
    (T : E.BlowUpSequence) (T' : F.BlowUpSequence) (ht : HEq T T') :
    T = T'.pullback (eqToHom h) := by
  subst F
  simpa only [eqToHom_refl, pullback_id] using eq_of_heq ht

private theorem geometric_lift_unique {E : Scheme.{u}} (D : E.IdealSheafData)
    (τ : E ⟶ E) (hD : D = D.comap τ) (t : D.blowUp ⟶ D.blowUp)
    (ht : t ≫ D.blowUpπ = D.blowUpπ ≫ τ) :
    t = eqToHom (congrArg Scheme.IdealSheafData.blowUp hD) ≫ Scheme.Hom.blowUpMap τ D := by
  let c := eqToHom (congrArg Scheme.IdealSheafData.blowUp hD)
  have hc : inv c ≫ D.blowUpπ = (D.comap τ).blowUpπ := by
    rw [← eqToHom_comp_blowUpπ hD, IsIso.inv_hom_id_assoc]
  have hg : inv c ≫ t = Scheme.Hom.blowUpMap τ D := by
    apply eq_blowUpMap
    rw [Category.assoc, ht, ← Category.assoc, hc]
  calc
    t = c ≫ (inv c ≫ t) := (IsIso.hom_inv_id_assoc c t).symm
    _ = c ≫ Scheme.Hom.blowUpMap τ D := by rw [hg]

/-- Exact WHOLE-sequence invariance produces the actual lifted automorphism
and equality for the SAME entire remaining tail. -/
theorem exists_same_tail_lift {E : Scheme.{u}} (D : E.IdealSheafData)
    (T : D.blowUp.BlowUpSequence) (τ : E ⟶ E) [IsIso τ]
    (h : Scheme.BlowUpSequence.cons E D T = (Scheme.BlowUpSequence.cons E D T).pullback τ) :
    ∃ t : D.blowUp ⟶ D.blowUp, IsIso t ∧ t ≫ D.blowUpπ = D.blowUpπ ≫ τ ∧ T = T.pullback t := by
  obtain ⟨hD,hT⟩ := Scheme.BlowUpSequence.cons.inj h
  let c := eqToHom (congrArg Scheme.IdealSheafData.blowUp hD)
  let t := c ≫ Scheme.Hom.blowUpMap τ D
  have : IsIso (Scheme.Hom.blowUpMap τ D) := (isPullback_blowUpMap τ D).isIso_fst_of_isIso
  have ht : T = (T.pullback (Scheme.Hom.blowUpMap τ D)).pullback c :=
    sequence_eq_pullback_cast (congrArg Scheme.IdealSheafData.blowUp hD) _ _ hT
  refine ⟨t,inferInstance,?_,?_⟩
  · rw [Category.assoc, blowUpMap_π, ← Category.assoc, eqToHom_comp_blowUpπ hD]
  · simpa only [← pullback_comp] using ht

/-- An actual geometric lift is identified by the actual blowup universal
property; the desired SAME-tail equality is derived, not supplied. -/
theorem same_tail_eq_pullback_of_geometric_lift {E : Scheme.{u}} (D : E.IdealSheafData)
    (T : D.blowUp.BlowUpSequence) (τ : E ⟶ E) [IsIso τ]
    (h : Scheme.BlowUpSequence.cons E D T = (Scheme.BlowUpSequence.cons E D T).pullback τ)
    (t : D.blowUp ⟶ D.blowUp) (ht : t ≫ D.blowUpπ = D.blowUpπ ≫ τ) : T = T.pullback t := by
  obtain ⟨hD,hT⟩ := Scheme.BlowUpSequence.cons.inj h
  have htail : T = (T.pullback (Scheme.Hom.blowUpMap τ D)).pullback
      (eqToHom (congrArg Scheme.IdealSheafData.blowUp hD)) :=
    sequence_eq_pullback_cast (congrArg Scheme.IdealSheafData.blowUp hD) _ _ hT
  rw [geometric_lift_unique D τ hD t ht, pullback_comp]
  exact htail

/-- The literal constructor-by-constructor SAME-tail law, with no inserted
stage in the empty case. -/
def TailLiftCompatibility {E : Scheme.{u}} (τ : E ⟶ E) : E.BlowUpSequence → Prop
  | .nil _ => True
  | .cons _ D T => ∀ t : D.blowUp ⟶ D.blowUp,
      t ≫ D.blowUpπ = D.blowUpπ ≫ τ → T = T.pullback t

theorem tailLiftCompatibility_of_eq_pullback {E : Scheme.{u}} (S : E.BlowUpSequence)
    (τ : E ⟶ E) [IsIso τ] (h : S = S.pullback τ) : TailLiftCompatibility τ S := by
  cases S with
  | nil _ => trivial
  | cons _ D T => exact same_tail_eq_pullback_of_geometric_lift D T τ h

open ActualDimensionGroupBlowup ActualDimensionGroupPaddedCover ActualPaddedEnvelopeNativeTranslations

/-- The actual original padded history internally supplies the WHOLE-sequence
comparison consumed by the SAME-tail lift law; no future-history certificate. -/
theorem nativePaddedHistory_tail_lift_compatibility
    (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
    [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    TailLiftCompatibility (envelopeTranslation R k v) (nativePaddedHistory R k) :=
  tailLiftCompatibility_of_eq_pullback _ _ (nativePaddedHistory_eq_pullback_translation R k v)

end
end Hironaka.Resolution.Algebraic.ActualNativeTailTranslationTransport
