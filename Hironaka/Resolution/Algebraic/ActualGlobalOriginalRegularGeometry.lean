import Hironaka.Resolution.Algebraic.ActualGlobalNativeHistoryDescent
import Hironaka.Resolution.Algebraic.ActualHistoryOriginalRegularIsomorphism
import Hironaka.Algebra.RegularSmooth.SingularLocus

/-!
# Genuine global original-regular support and same-history isomorphisms

Source-first proof: `actual-global-original-regular-geometry-20261102.tex`.
The actual original singular ideal, exact affine separation comparison and
actual cartesian own-section geometry preserve the ENTIRE original regular
open.  Original-singular BP and smooth/field compatibility remain open.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalOriginalRegularGeometry

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

omit [IsReduced X] in
include p in
theorem singIdeal_open {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    X.singIdeal.comap j = Y.singIdeal := by
  rw [Scheme.singIdeal_eq_vanishingIdeal_closure_singularLocus,
    Hironaka.Smooth.comap_vanishingIdeal_of_smooth,
    Scheme.singIdeal_eq_vanishingIdeal_closure_singularLocus]
  congr 1
  apply Closeds.ext
  change j ⁻¹' closure X.singularLocus = closure Y.singularLocus
  rw [(Scheme.isClosed_singularLocus p).closure_eq,
    (Scheme.isClosed_singularLocus (j ≫ p)).closure_eq,
    Scheme.singularLocus_eq_compl_smoothLocus p,
    Scheme.singularLocus_eq_compl_smoothLocus (j ≫ p)]
  change ((j ⁻¹ᵁ p.smoothLocus : Y.Opens) : Set Y)ᶜ = ((j ≫ p).smoothLocus : Set Y)ᶜ
  rw [j.preimage_smoothLocus_eq p]

private theorem smoothLocus_congr {A B : Scheme.{u}} (f g : A ⟶ B)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  subst h
  rfl

theorem separationIdeal_avoids_original_regular (x : X) (hx : x ∈ p.smoothLocus) :
    x ∉ (ActualGlobalDimensionSeparationIdeal.separationIdeal X).support := by
  obtain ⟨U, hxU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem x
  obtain ⟨y, hy⟩ : x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    exact hxU
  let := (Hironaka.Algebra.FiniteTypePoint.affineBaseMap p U.2).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := RingHom.finiteType_algebraMap.mp
    (Hironaka.Algebra.FiniteTypePoint.affineBaseMap_finiteType p U.2)
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let f := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))
  have hf : f = U.2.fromSpec ≫ p := Hironaka.Algebra.FiniteTypePoint.affineBaseMap_spec p U.2
  have : LocallyOfFiniteType f := by rw [hf]; infer_instance
  have hySmooth : y ∈ f.smoothLocus := by
    rw [smoothLocus_congr f (U.2.fromSpec ≫ p) hf, ← U.2.fromSpec.preimage_smoothLocus_eq p]
    change U.2.fromSpec y ∈ p.smoothLocus
    rwa [hy]
  have : IsRegularLocalRing (Localization.AtPrime y.asIdeal) :=
    (ActualDimensionGroupRegularLocus.mem_smoothLocus_iff_regular_localization Γ(X, U) k y).mp hySmooth
  intro hJ
  have hyJ : y ∈ ((ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap U.2.fromSpec).support := by
    rw [support_comap]
    change U.2.fromSpec y ∈ (ActualGlobalDimensionSeparationIdeal.separationIdeal X).support
    rwa [hy]
  rw [ActualGlobalDimensionIdealAffineComparison.separationIdeal_open_spectrum Γ(X, U) p U.2.fromSpec] at hyJ
  change y ∈ ((Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf Γ(X, U)
    (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U))).support : Set (Spec (.of Γ(X, U)))) at hyJ
  rw [Hironaka.Geometry.ReducedClosedSubscheme.specIdealSheaf_support] at hyJ
  exact (ActualDimensionGroupRegularLocus.regular_prime_avoids_separation Γ(X, U) y) hyJ

include p in
theorem separation_support_le_original_singular :
    (ActualGlobalDimensionSeparationIdeal.separationIdeal X).support ≤ X.singIdeal.support := by
  intro x hx
  change x ∈ (X.singIdeal.support : Set X)
  rw [Scheme.coe_support_singIdeal_eq_singularLocus p, Scheme.singularLocus_eq_compl_smoothLocus p]
  exact fun hreg => separationIdeal_avoids_original_regular p x hreg hx

theorem separationIdeal_unit_original_regular :
    (ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap p.smoothLocus.ι = ⊤ := by
  rw [← support_eq_bot_iff, support_comap]
  ext x
  change p.smoothLocus.ι x ∈ (ActualGlobalDimensionSeparationIdeal.separationIdeal X).support ↔ False
  exact ⟨separationIdeal_avoids_original_regular p x.val x.property, False.elim⟩

private theorem identity_isBlowUp_top (B : Scheme.{u}) : IsBlowUp (⊤ : B.IdealSheafData) (𝟙 B) where
  admissible := by simpa only [comap_id] using (isInvertible_top (X := B))
  existsUnique_lift f _ := by
    refine ⟨f, Category.comp_id _, ?_⟩
    intro g hg
    simpa only [Category.comp_id] using hg

theorem separation_isIso_original_regular :
    IsIso (ActualGlobalDimensionClopenPartition.separationProjection X ∣_ p.smoothLocus) := by
  let J := ActualGlobalDimensionSeparationIdeal.separationIdeal X
  have hid : IsBlowUp (J.comap p.smoothLocus.ι) (𝟙 p.smoothLocus.toScheme) := by
    rw [separationIdeal_unit_original_regular p]
    exact identity_isBlowUp_top _
  obtain ⟨φ, H⟩ := (blowUp.isBlowUp J).exists_isPullback_of_flat p.smoothLocus.ι hid
  obtain ⟨e, he⟩ := exists_restrictIso_of_isPullback p.smoothLocus H
  have hEq : (ActualGlobalDimensionClopenPartition.separationProjection X ∣_ p.smoothLocus) = e.inv := by
    rw [← cancel_epi e.hom, he, e.hom_inv_id]
  rw [hEq]
  infer_instance

variable [IsSeparated p] (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

private instance inputStructure_finiteType : FiniteType ((variableEnvelope p V N hN).obj.hom) :=
  (variableEnvelope p V N hN).obj.prop.1

private instance inputStructure_finitePresentation :
    LocallyOfFinitePresentation ((variableEnvelope p V N hN).obj.hom) := by
  change LocallyOfFinitePresentation (envelopeStructure p V)
  infer_instance

theorem paddedOriginalRegular_le_smoothLocus :
    (projection X V ≫ ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹ᵁ p.smoothLocus ≤
      ((variableEnvelope p V N hN).obj.hom).smoothLocus := by
  let U := p.smoothLocus
  let g := projection X V ≫ ActualGlobalDimensionClopenPartition.separationProjection X
  let W := g ⁻¹ᵁ U
  have : Smooth (projection X V) := projection_smooth X V
  have : IsIso (ActualGlobalDimensionClopenPartition.separationProjection X ∣_ U) :=
    separation_isIso_original_regular p
  have : Smooth (U.ι ≫ p) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact U.ι_preimage_self
  have hcomp : Smooth (g ∣_ U ≫ U.ι ≫ p) := by
    rw [show g ∣_ U = projection X V ∣_
        (ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹ᵁ U ≫
        ActualGlobalDimensionClopenPartition.separationProjection X ∣_ U from morphismRestrict_comp _ _ _]
    infer_instance
  have : Smooth (W.ι ≫ (variableEnvelope p V N hN).obj.hom) := by
    have he : g ∣_ U ≫ U.ι ≫ p = W.ι ≫ (variableEnvelope p V N hN).obj.hom := by
      rw [← Category.assoc, morphismRestrict_ι]
      rfl
    exact he ▸ hcomp
  intro x hx
  exact ((variableEnvelope p V N hN).obj.hom.mem_smoothLocus_iff_exists_smooth).mpr ⟨W, hx, inferInstance⟩

theorem baseHistory_isIso_original_regular :
    IsIso ((baseHistory p V N hN).composite ∣_
      (ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹ᵁ p.smoothLocus) := by
  have : Smooth (projection X V) := projection_smooth X V
  have : IsIso ((history p V N hN).composite ∣_ ((variableEnvelope p V N hN).obj.hom).smoothLocus) :=
    (history_isStrongResolution p V N hN).isIso_restrict_smoothLocus
  have : IsIso ((history p V N hN).composite ∣_ (projection X V) ⁻¹ᵁ
      (ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹ᵁ p.smoothLocus) :=
    isIso_restrict_of_le _ (paddedOriginalRegular_le_smoothLocus p V N hN)
  exact ActualHistoryOriginalRegularIsomorphism.isIso_restrict_of_split_cartesian
    (ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq (baseHistory p V N hN)
      (projection X V) (history p V N hN) (history_descends p V N hN))
    (zeroSection X V) (zeroSection_projection X V) _

theorem canonicalBaseHistory_isIso_original_regular :
    IsIso ((canonicalBaseHistory p).composite ∣_
      (ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹ᵁ p.smoothLocus) :=
  baseHistory_isIso_original_regular p (paddingVariables p) (commonDimension p) (padding_rank p)

end
end Hironaka.Resolution.Algebraic.ActualGlobalOriginalRegularGeometry
