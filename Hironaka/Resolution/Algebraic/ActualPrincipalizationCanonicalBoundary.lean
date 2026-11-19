import Hironaka.Resolution.Algebraic.ActualPrincipalizedEndpointGeometry
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Basic
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary

/-!
# The actual canonical BP boundary has the genuine ORIGINAL support

Source-first proof: `actual-principalization-canonical-boundary-20261102.tex`.
This specifies the REAL downstairs family whose pullback is SNC; its own
downstairs SNC condition is left to genuine fixed-family reflection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualPrincipalizationCanonicalBoundary

noncomputable section

/-- Actual chronological cumulative exceptional ideal, with every original native position. -/
def cumulativeExceptionalIdeal : {X : Scheme.{u}} → (S : X.BlowUpSequence) → S.last.IdealSheafData
  | _, .nil _ => ⊤
  | _, .cons _ D T => (D.exceptionalDivisor.comap T.composite) * cumulativeExceptionalIdeal T

private theorem firstExceptionalFactor {X : Scheme.{u}} (D : X.IdealSheafData)
    (T : D.blowUp.BlowUpSequence) :
    (((Scheme.BlowUpSequence.cons X D T).exceptionalAt ⟨0,Nat.succ_pos _⟩).comap
      ((Scheme.BlowUpSequence.cons X D T).stageMapBetween (Fin.last _) (Fin.succ ⟨0,Nat.succ_pos _⟩)
        (Fin.le_last _))) = D.exceptionalDivisor.comap T.composite := by
  rw [exceptionalAt_cons_zero,← comap_comp]
  apply congrArg D.exceptionalDivisor.comap
  change T.stageMapBetween (Fin.last _) 0 _ ≫ eqToHom (stage_zero T) = T.composite
  cases T with
  | nil Y => rfl
  | cons Y D' T' =>
    simp only [eqToHom_refl,Category.comp_id]
    exact stageMapBetween_zero_cons D' T' (Fin.last _)

/-- The recursive actual ideal equals the full native product of total exceptional pullbacks. -/
theorem cumulativeExceptionalIdeal_eq_prod : ∀ {X : Scheme.{u}} (S : X.BlowUpSequence),
    cumulativeExceptionalIdeal S = ∏ j : Fin S.length,
      (S.exceptionalAt j).comap (S.stageMapBetween (Fin.last _) j.succ (Fin.le_last _)) := by
  intro X S
  induction S with
  | nil X => simp [cumulativeExceptionalIdeal,Scheme.BlowUpSequence.length,← one_eq_top]
  | cons X D T ih =>
    change (D.exceptionalDivisor.comap T.composite) * cumulativeExceptionalIdeal T = _
    unfold Scheme.BlowUpSequence.last at ih ⊢
    change (D.exceptionalDivisor.comap T.composite) * cumulativeExceptionalIdeal T =
      ∏ j : Fin (T.length + 1), _
    rw [ih,Fin.prod_univ_succ]
    refine congrArg₂ (fun I J : T.last.IdealSheafData => I * J)
      (firstExceptionalFactor D T).symm ?_
    apply Finset.prod_congr rfl
    intro j _
    rfl

private theorem reducedTransform_support {X : Scheme.{u}} (E D : X.IdealSheafData) :
    (E.reducedTransform D).support = E.support.preimage D.blowUpπ.continuous ⊔ D.exceptionalDivisor.support := by
  change (vanishingIdeal (E.support.preimage D.blowUpπ.continuous ⊔
    D.support.preimage D.blowUpπ.continuous)).support = _
  rw [support_vanishingIdeal_eq]
  change _ = E.support.preimage D.blowUpπ.continuous ⊔ (D.comap D.blowUpπ).support
  rw [support_comap]

/-- Genuine support recursion for the native reduced boundary and actual total exceptional ideal. -/
theorem boundarySeq_support : ∀ {X : Scheme.{u}} (S : X.BlowUpSequence) (E : X.IdealSheafData),
    (S.boundarySeq E (Fin.last _)).support =
      (E.comap S.composite).support ⊔ (cumulativeExceptionalIdeal S).support := by
  intro X S
  induction S with
  | nil X =>
    intro E
    change E.support = (E.comap (𝟙 X)).support ⊔ (⊤ : X.IdealSheafData).support
    rw [comap_id,support_top,sup_bot_eq]
  | cons X D T ih =>
    intro E
    change (T.boundarySeq (E.reducedTransform D) (Fin.last _)).support =
      (E.comap (T.composite ≫ D.blowUpπ)).support ⊔
        ((D.exceptionalDivisor.comap T.composite) * cumulativeExceptionalIdeal T).support
    rw [ih]
    simp only [support_comap,support_mul,reducedTransform_support]
    apply Closeds.ext
    ext x
    simp only [Closeds.coe_sup,Closeds.coe_preimage,Set.mem_union,Set.mem_preimage,
      Scheme.Hom.comp_apply]
    tauto

/-- The specified actual canonical boundary of ONE native BP. -/
def principalizationBoundary {k : Type u} [Field k] [CharZero k] (T : Triple k) :
    Scheme.DivisorFamily (BP T).last := (BP T).totalTransformSeq T.E (Fin.last _)

/-- Native smooth-centre/SNC geometry proves this FIXED canonical family SNC. -/
theorem principalizationBoundary_snc {k : Type u} [Field k] [CharZero k] (T : Triple k) :
    (principalizationBoundary T).IsSnc := by
  obtain ⟨n,hn⟩ := T.smoothOfRelativeDimension
  have : SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k)) := hn
  exact IsOrderGeSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) n
    (BP_isOrderGeSeq_zero T) T.isSnc (Fin.last _)

/-- For an empty actual starting boundary, this FIXED canonical family has the actual original ideal support. -/
theorem principalizationBoundary_original_support {k : Type u} [Field k] [CharZero k]
    (T : Triple k) (hE : IsEmpty T.E.ι) :
    (principalizationBoundary T).support = (T.I.comap (BP T).composite).support := by
  let : IsEmpty T.E.ι := hE
  let f : T.X.left ⟶ Spec (.of k) := T.X.hom
  have : FiniteType f := T.X.prop.1
  have : IsLocallyNoetherian T.X.left := LocallyOfFiniteType.isLocallyNoetherian f
  let P : T.X.left.BlowUpSequence → Prop := fun S =>
    (S.totalTransformSeq T.E (Fin.last _)).support = (T.I.comap S.composite).support
  let S := (Hironaka.Stage.BMO_m 1 k).seq ⟨T,1⟩ ⟨le_rfl,rfl⟩
  have hS : P S := by
    have hI : T.I.comap S.composite = cumulativeExceptionalIdeal S := by
      rw [cumulativeExceptionalIdeal_eq_prod]
      exact BMO_one_comap_composite_eq_prod ⟨T,1⟩ ⟨le_rfl,rfl⟩
    have he : T.E.unionIdeal = ⊤ := by
      simp [Scheme.DivisorFamily.unionIdeal,Scheme.DivisorFamily.support]
    have hboundary := boundarySeq_eq_unionIdeal_totalTransformSeq S T.E (Fin.last _)
    rw [he] at hboundary
    have hc : (S.boundarySeq ⊤ (Fin.last _)).support = (cumulativeExceptionalIdeal S).support := by
      simpa only [comap_top,support_top,bot_sup_eq] using boundarySeq_support S ⊤
    change (S.totalTransformSeq T.E (Fin.last _)).support = _
    rw [hI,← hc,hboundary,AlgebraicGeometry.support_unionIdeal]
  change P (BP T)
  exact Eq.mpr (congrArg P (BP_of_isEmpty T hE)) hS

private theorem family_comap_comp {X Y Z : Scheme.{u}} (E : Scheme.DivisorFamily Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) : E.comap (f ≫ g) = (E.comap g).comap f := by
  cases E
  simp only [Scheme.DivisorFamily.comap,Scheme.IdealSheafData.comap_comp]

/-- Actual final total-family flat naturality, with the native last-index transport retained. -/
theorem totalBoundary_pullback_last {X Y : Scheme.{u}} (S : X.BlowUpSequence) (h : Y ⟶ X) [Flat h]
    (E : Scheme.DivisorFamily X) :
    (S.pullback h).totalTransformSeq (E.comap h) (Fin.last _) =
      (S.totalTransformSeq E (Fin.last _)).comap (S.pullbackLastHom h) := by
  refine (totalTransformSeq_eq_idx (S.pullback h) (E.comap h) (pullbackStageIdx_last S h)).trans ?_
  refine Eq.trans (congrArg (fun F : Scheme.DivisorFamily ((S.pullback h).stage _) =>
      F.comap (eqToHom (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm)))
    (totalTransformSeq_pullback S h E (Fin.last _))) ?_
  exact (family_comap_comp _ _ _).symm

private theorem totalBoundary_transport {X : Scheme.{u}} (S S' : X.BlowUpSequence)
    (E : Scheme.DivisorFamily X) (h : S = S') :
    S.totalTransformSeq E (Fin.last _) = (S'.totalTransformSeq E (Fin.last _)).comap
      (eqToHom (congrArg Scheme.BlowUpSequence.last h)) := by
  subst h
  change S.totalTransformSeq E (Fin.last _) = (S.totalTransformSeq E (Fin.last _)).comap
    (𝟙 (S.stage (Fin.last _)))
  exact (Scheme.DivisorFamily.comap_id _).symm

open ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualPaddedNativePrincipalizationInput ActualOriginalSingPrincipalizationHistoryDescent
  ActualPrincipalizedEndpointGeometry

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- The specified actual canonical boundary on the SAME descended principalized endpoint. -/
def nativeBaseBoundary : Scheme.DivisorFamily (nativeBasePrincipalizationHistory R k).last :=
  (nativeBasePrincipalizationHistory R k).totalTransformSeq
    (Scheme.DivisorFamily.empty (nativeBaseHistory R k).last) (Fin.last _)

/-- Native flat total-family naturality gives equality of the TWO actual fixed boundaries. -/
theorem nativeBaseBoundary_pullback :
    (nativeBaseBoundary R k).comap (nativePrincipalizedProjection R k) =
      principalizationBoundary (nativeOriginalSingPrincipalizationTriple R k) := by
  have : Smooth (paddedFinalProjection R k) := paddedFinalProjection_smooth R k
  change ((nativeBasePrincipalizationHistory R k).totalTransformSeq
      (Scheme.DivisorFamily.empty (nativeBaseHistory R k).last) (Fin.last _)).comap
    (eqToHom (congrArg Scheme.BlowUpSequence.last (nativePrincipalization_canonical_history_descends R k)) ≫
      (nativeBasePrincipalizationHistory R k).pullbackLastHom (paddedFinalProjection R k)) = _
  rw [family_comap_comp,← totalBoundary_pullback_last,empty_comap]
  exact (totalBoundary_transport (nativeOriginalSingPrincipalizationHistory R k)
    ((nativeBasePrincipalizationHistory R k).pullback (paddedFinalProjection R k))
    (Scheme.DivisorFamily.empty (nativePaddedHistory R k).last)
      (nativePrincipalization_canonical_history_descends R k)).symm

/-- This specified downstairs family has the genuine native canonical SNC family as actual pullback. -/
theorem nativeBaseBoundary_snc_pullback :
    ((nativeBaseBoundary R k).comap (nativePrincipalizedProjection R k)).IsSnc := by
  rw [nativeBaseBoundary_pullback]
  exact principalizationBoundary_snc (nativeOriginalSingPrincipalizationTriple R k)

/-- The specified genuine downstairs family has EXACT support of the ORIGINAL terminal singular ideal. -/
theorem nativeBaseBoundary_original_support :
    (nativeBaseBoundary R k).support = (nativePrincipalizedOriginalIdeal R k).support := by
  have hu : ((nativeBaseBoundary R k).comap (nativePrincipalizedProjection R k)).support =
      ((nativePrincipalizedOriginalIdeal R k).comap (nativePrincipalizedProjection R k)).support := by
    rw [nativeBaseBoundary_pullback,nativePrincipalizedOriginalIdeal_pullback]
    exact principalizationBoundary_original_support (nativeOriginalSingPrincipalizationTriple R k)
      (inferInstanceAs (IsEmpty PEmpty))
  apply Closeds.ext
  ext x
  have hx := congrArg (fun Z : Closeds (nativeOriginalSingPrincipalizationHistory R k).last =>
    nativePrincipalizedSection R k x ∈ Z) hu
  have hsupp : ((nativeBaseBoundary R k).comap (nativePrincipalizedProjection R k)).support =
      (nativeBaseBoundary R k).support.preimage (nativePrincipalizedProjection R k).continuous := by
    simp only [Scheme.DivisorFamily.support,Scheme.DivisorFamily.comap,support_comap]
    apply Closeds.ext
    ext y
    simp only [← Finset.sup_univ_eq_iSup]
    rw [Closeds.coe_finset_sup,Closeds.coe_preimage,Closeds.coe_finset_sup]
    simp only [Finset.sup_eq_iSup,Finset.mem_univ,iSup_pos,Set.iSup_eq_iUnion,Set.mem_iUnion,
      Function.comp_apply,Closeds.coe_preimage,Set.mem_preimage]
  rw [hsupp,support_comap] at hx
  change ((nativePrincipalizedProjection R k) (nativePrincipalizedSection R k x) ∈
    (nativeBaseBoundary R k).support) =
    ((nativePrincipalizedProjection R k) (nativePrincipalizedSection R k x) ∈
    (nativePrincipalizedOriginalIdeal R k).support) at hx
  have hpoint : nativePrincipalizedProjection R k (nativePrincipalizedSection R k x) = x :=
    congrArg (fun f => f x) (nativePrincipalizedSection_projection R k)
  rw [hpoint] at hx
  exact hx.to_iff
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualPrincipalizationCanonicalBoundary
