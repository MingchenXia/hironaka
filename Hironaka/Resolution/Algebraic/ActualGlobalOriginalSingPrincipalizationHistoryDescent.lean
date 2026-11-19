import Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingPrincipalizationInput

/-!
# Exact SAME-clock descent of ONE global ORIGINAL-singular principalization

Source-first proof: `actual-global-original-sing-principalization-history-descent-20261102.tex`.
Actual current product geometry produces translations fixing the original map.
Native whole BP functoriality and ALG8 give actual own-section descent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingPrincipalizationHistoryDescent

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalOriginalSingPrincipalizationInput ActualFinalClopenProductPresentation
  ActualRelativeAffineHistoryDescent ActualPaddedEnvelopeNativeTranslations
  ActualGlobalDimensionClopenPartition

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

private abbrev basePiece (d : dimensionIndex X) : Scheme.{u} :=
  restrictedEndpoint (dimensionPartOpen X) (baseHistory p V N hN) d

private abbrev productSource : Scheme.{u} := ∐ fun d => AffineSpace (V d) (basePiece p V N hN d)

private abbrev baseDesc : (∐ basePiece p V N hN) ⟶ (baseHistory p V N hN).last :=
  restrictedEndpointsDesc (dimensionPartOpen X) (baseHistory p V N hN)

private instance baseDesc_isIso : IsIso (baseDesc p V N hN) :=
  restrictedEndpointsDesc_isIso (dimensionPartOpen X) (baseHistory p V N hN)
    (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X)

private theorem currentProductExists : ∃ e : productSource p V N hN ≅ (history p V N hN).last,
    e.hom ≫ endpointProjection p V N hN =
      finalProductProjection (dimensionPartOpen X) V (baseHistory p V N hN) ∧
    e.hom ≫ (history p V N hN).composite =
      finalProductOriginalMap (dimensionPartOpen X) V (baseHistory p V N hN) := by
  have : Smooth (clopenPaddedProjection (dimensionPartOpen X) V) := projection_smooth X V
  obtain ⟨e, he₁, he₂⟩ := exists_finalClopenProductIso (dimensionPartOpen X) V (baseHistory p V N hN)
    (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X)
  let c := eqToIso (congrArg Scheme.BlowUpSequence.last (history_descends p V N hN))
  refine ⟨e ≪≫ c.symm, ?_, ?_⟩
  · change (e.hom ≫ c.inv) ≫ (c.hom ≫ (baseHistory p V N hN).pullbackLastHom (projection X V)) = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact he₁
  · change (e.hom ≫ c.inv) ≫ (history p V N hN).composite = _
    have hc : c.inv ≫ (history p V N hN).composite =
        ((baseHistory p V N hN).pullback (projection X V)).composite :=
      eqToHom_comp_composite_of_eq (history_descends p V N hN).symm
    rw [Category.assoc, hc]
    exact he₂

def currentProductIso : productSource p V N hN ≅ (history p V N hN).last :=
  (currentProductExists p V N hN).choose

theorem currentProductIso_projection : (currentProductIso p V N hN).hom ≫ endpointProjection p V N hN =
    finalProductProjection (dimensionPartOpen X) V (baseHistory p V N hN) :=
  (currentProductExists p V N hN).choose_spec.1

theorem currentProductIso_original : (currentProductIso p V N hN).hom ≫ (history p V N hN).composite =
    finalProductOriginalMap (dimensionPartOpen X) V (baseHistory p V N hN) :=
  (currentProductExists p V N hN).choose_spec.2

def originalMap : (history p V N hN).last ⟶ X :=
  (history p V N hN).composite ≫ projection X V ≫ separationProjection X

theorem principalization_eq_pullback_of_original_projection
    (g : (history p V N hN).last ⟶ (history p V N hN).last) [IsIso g]
    (hg : g ≫ originalMap p V N hN = originalMap p V N hN) :
    principalizationHistory p V N hN = (principalizationHistory p V N hN).pullback g := by
  let T := originalTriple p V N hN
  have hfield : g ≫ (T.X.left ↘ Spec (.of k)) = T.X.left ↘ Spec (.of k) := by
    change g ≫ ((history p V N hN).composite ≫ projection X V ≫ separationProjection X ≫ p) =
      (history p V N hN).composite ≫ projection X V ≫ separationProjection X ≫ p
    simpa only [originalMap, Category.assoc] using congrArg (fun f => f ≫ p) hg
  have hI : T.I = T.I.comap g := by
    change originalIdeal p V N hN = (originalIdeal p V N hN).comap g
    change X.singIdeal.comap (originalMap p V N hN) = (X.singIdeal.comap (originalMap p V N hN)).comap g
    rw [← comap_comp, hg]
  have hE : T.E = T.E.comap g := by
    change Scheme.DivisorFamily.empty _ = (Scheme.DivisorFamily.empty _).comap g
    exact (empty_comap g).symm
  exact BP_pullback_of_surjective T T g (surjective_of_isIso g) ⟨hfield, hI, hE⟩

private theorem productTranslation_projection (v : ∀ d, V d → ℤ) :
    clopenTranslation V (basePiece p V N hN) v ≫ clopenProjection V (basePiece p V N hN) =
      clopenProjection V (basePiece p V N hN) := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc, clopenTranslation, Sigma.ι_map, Category.assoc, clopenProjection,
    Sigma.ι_map, ← Category.assoc, affineTranslation_projection]

def productPrincipalizationHistory : (productSource p V N hN).BlowUpSequence :=
  (principalizationHistory p V N hN).pullback (currentProductIso p V N hN).hom

theorem productPrincipalizationHistory_invariant (v : ∀ d, V d → ℤ) :
    productPrincipalizationHistory p V N hN = (productPrincipalizationHistory p V N hN).pullback
      (clopenTranslation V (basePiece p V N hN) v) := by
  let e := currentProductIso p V N hN
  let t := clopenTranslation V (basePiece p V N hN) v
  have : IsIso t := by
    change IsIso (Limits.Sigma.map (fun d => (affineTranslation (V d) (basePiece p V N hN d) (v d)).hom))
    infer_instance
  let g := e.inv ≫ t ≫ e.hom
  have : IsIso g := by dsimp only [g]; infer_instance
  have hgq : g ≫ endpointProjection p V N hN = endpointProjection p V N hN := by
    apply (cancel_epi e.hom).mp
    calc
      e.hom ≫ (g ≫ endpointProjection p V N hN) = t ≫ e.hom ≫ endpointProjection p V N hN := by
        simp [g, Category.assoc]
      _ = t ≫ clopenProjection V (basePiece p V N hN) ≫ baseDesc p V N hN := by
        rw [currentProductIso_projection]
        rfl
      _ = clopenProjection V (basePiece p V N hN) ≫ baseDesc p V N hN := by
        rw [← Category.assoc, productTranslation_projection]
      _ = e.hom ≫ endpointProjection p V N hN := (currentProductIso_projection p V N hN).symm
  have hq : endpointProjection p V N hN ≫ ((baseHistory p V N hN).composite ≫ separationProjection X) =
      originalMap p V N hN := by
    simpa only [originalMap, Category.assoc] using
      congrArg (fun f => f ≫ separationProjection X) (endpointProjection_over p V N hN)
  have hg : g ≫ originalMap p V N hN = originalMap p V N hN := by
    rw [← hq, ← Category.assoc, hgq]
  have hBP := principalization_eq_pullback_of_original_projection p V N hN g hg
  have ht : e.hom ≫ g = t ≫ e.hom := by simp [g]
  have h := congrArg (fun S => S.pullback e.hom) hBP
  rw [← pullback_comp, ht, pullback_comp] at h
  exact h

private theorem clopenZeroSection_projection :
    clopenZeroSection V (basePiece p V N hN) ≫ clopenProjection V (basePiece p V N hN) =
      𝟙 (∐ basePiece p V N hN) := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc, clopenZeroSection, Sigma.ι_map, Category.assoc, clopenProjection,
    Sigma.ι_map, ← Category.assoc, AffineSpace.homOfVector_over, Category.id_comp, Category.comp_id]

private def productSection : (baseHistory p V N hN).last ⟶ (history p V N hN).last :=
  inv (baseDesc p V N hN) ≫ clopenZeroSection V (basePiece p V N hN) ≫ (currentProductIso p V N hN).hom

private theorem productSection_projection : productSection p V N hN ≫ endpointProjection p V N hN = 𝟙 _ := by
  rw [productSection, Category.assoc, Category.assoc, currentProductIso_projection]
  change inv (baseDesc p V N hN) ≫ clopenZeroSection V (basePiece p V N hN) ≫
    clopenProjection V (basePiece p V N hN) ≫ baseDesc p V N hN = _
  rw [← Category.assoc (clopenZeroSection _ _), clopenZeroSection_projection, Category.id_comp,
    IsIso.inv_hom_id]

def basePrincipalizationHistory : (baseHistory p V N hN).last.BlowUpSequence :=
  (principalizationHistory p V N hN).pullback (endpointSection p V N hN)

theorem principalizationHistory_descends : principalizationHistory p V N hN =
    (basePrincipalizationHistory p V N hN).pullback (endpointProjection p V N hN) := by
  let e := currentProductIso p V N hN
  let q := clopenProjection V (basePiece p V N hN)
  let s := clopenZeroSection V (basePiece p V N hN)
  have hcan := clopen_relative_history_descends V (basePiece p V N hN) k
    (fun d => ((baseHistory p V N hN).pullback (dimensionPartOpen X d).ι).composite ≫ pieceStructure p d)
    (productPrincipalizationHistory p V N hN) (productPrincipalizationHistory_invariant p V N hN)
  have hep : e.hom ≫ endpointProjection p V N hN = q ≫ baseDesc p V N hN :=
    currentProductIso_projection p V N hN
  have hinv : e.inv ≫ q = endpointProjection p V N hN ≫ inv (baseDesc p V N hN) := by
    symm
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.hom_inv_id, Category.comp_id] using
      congrArg (fun h => e.inv ≫ h ≫ inv (baseDesc p V N hN)) hep
  let C := (principalizationHistory p V N hN).pullback (productSection p V N hN)
  have hwhole : principalizationHistory p V N hN = C.pullback (endpointProjection p V N hN) := by
    calc
      principalizationHistory p V N hN = (productPrincipalizationHistory p V N hN).pullback e.inv := by
        rw [productPrincipalizationHistory, ← pullback_comp, Iso.inv_hom_id, pullback_id]
      _ = (((productPrincipalizationHistory p V N hN).pullback s).pullback q).pullback e.inv :=
        congrArg (fun S => S.pullback e.inv) hcan
      _ = C.pullback (endpointProjection p V N hN) := by
        simp only [C, productSection, productPrincipalizationHistory, ← pullback_comp]
        apply congrArg ((principalizationHistory p V N hN).pullback)
        change e.inv ≫ q ≫ s ≫ e.hom = endpointProjection p V N hN ≫ inv (baseDesc p V N hN) ≫ s ≫ e.hom
        rw [← Category.assoc e.inv q, hinv, Category.assoc]
  have hown : basePrincipalizationHistory p V N hN = C := by
    rw [basePrincipalizationHistory, hwhole, ← pullback_comp, endpointSection_projection, pullback_id]
  rw [hown]
  exact hwhole

theorem basePrincipalizationHistory_length :
    (basePrincipalizationHistory p V N hN).length = (principalizationHistory p V N hN).length :=
  length_pullback _ _

end
end Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingPrincipalizationHistoryDescent
