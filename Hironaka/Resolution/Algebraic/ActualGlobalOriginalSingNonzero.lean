import Hironaka.Resolution.Algebraic.ActualGlobalOriginalRegularGeometry

/-!
# Genuine ORIGINAL singular-ideal nonvanishing on actual global histories

Source-first proof: `actual-global-original-sing-nonzero-20261102.tex`.
Local actual Cartier subideals suffice; no global Cartier ideal is assumed.
The actual complete native clock, including nil and internal empties, is retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData Scheme.BlowUpSequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingNonzero

noncomputable section

/-- Actual local invertible subideals survive any complete actual native history. -/
theorem nonzero_comap_history_of_locally_invertible {X : Scheme.{u}}
    (S : X.BlowUpSequence) (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ K : U.toScheme.IdealSheafData,
      K.IsInvertible ∧ K ≤ I.comap U.ι) : (I.comap S.composite).IsNonzeroEverywhere := by
  intro y hy
  obtain ⟨U, hyU, K, hK, hKI⟩ := hI (S.composite y)
  let H := ActualFinalClopenProductPresentation.lastStage_isPullback S U.ι
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback H y
    (⟨S.composite y, hyU⟩ : U.toScheme) rfl
  subst y
  have hKfinal := ActualOriginalSingIdealNonzero.invertible_comap_composite
    (S.pullback U.ι) K hK
  have hle : K.comap (S.pullback U.ι).composite ≤
      (I.comap S.composite).comap (S.pullbackLastHom U.ι) := by
    rw [← comap_comp, H.w, comap_comp]
    exact comap_mono _ hKI
  apply Hironaka.BMO.isNonzeroEverywhere_of_isInvertible hKfinal z
  apply le_bot_iff.mp
  refine (stalkIdeal_mono hle z).trans ?_
  rw [stalkIdeal_comap, hy, Ideal.map_bot]

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include p in
theorem originalSing_locally_contains_invertible (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ K : U.toScheme.IdealSheafData,
      K.IsInvertible ∧ K ≤ X.singIdeal.comap U.ι := by
  obtain ⟨U, hxU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem x
  let := (Hironaka.Algebra.FiniteTypePoint.affineBaseMap p U.2).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := RingHom.finiteType_algebraMap.mp
    (Hironaka.Algebra.FiniteTypePoint.affineBaseMap_finiteType p U.2)
  obtain ⟨K, hK, hKJ⟩ := ActualOriginalSingIdealNonzero.exists_invertible_le_original_singIdeal Γ(X, U) k
  refine ⟨U.1, hxU, K.comap U.2.isoSpec.hom,
    IsInvertible.comap_of_isOpenImmersion U.2.isoSpec.hom hK, ?_⟩
  have hlocal := ActualGlobalOriginalRegularGeometry.singIdeal_open p U.2.fromSpec
  have hle := comap_mono U.2.isoSpec.hom hKJ
  change K.comap U.2.isoSpec.hom ≤ (Spec Γ(X, U)).singIdeal.comap U.2.isoSpec.hom at hle
  rw [← hlocal, ← comap_comp, U.2.isoSpec_hom_fromSpec] at hle
  exact hle

include p in
theorem originalSing_comap_history_nonzero (S : X.BlowUpSequence) :
    (X.singIdeal.comap S.composite).IsNonzeroEverywhere :=
  nonzero_comap_history_of_locally_invertible S X.singIdeal
    (originalSing_locally_contains_invertible p)

open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent

variable [IsSeparated p] (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

/-- The actual ORIGINAL global singular ideal on the SAME descended endpoint. -/
def baseOriginalIdeal : (baseHistory p V N hN).last.IdealSheafData :=
  X.singIdeal.comap ((baseHistory p V N hN).composite ≫
    ActualGlobalDimensionClopenPartition.separationProjection X)

theorem baseOriginalIdeal_nonzero : (baseOriginalIdeal p V N hN).IsNonzeroEverywhere := by
  let S : X.BlowUpSequence := .cons X (ActualGlobalDimensionSeparationIdeal.separationIdeal X)
    (baseHistory p V N hN)
  exact originalSing_comap_history_nonzero p S

theorem baseOriginalIdeal_support :
    ((baseOriginalIdeal p V N hN).support : Set (baseHistory p V N hN).last) =
      ((baseHistory p V N hN).composite ≫
        ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹' X.singularLocus := by
  rw [baseOriginalIdeal, support_comap, Closeds.coe_preimage,
    Scheme.coe_support_singIdeal_eq_singularLocus p]

theorem canonicalBaseOriginalIdeal_nonzero :
    (baseOriginalIdeal p (paddingVariables p) (commonDimension p) (padding_rank p)).IsNonzeroEverywhere :=
  baseOriginalIdeal_nonzero p (paddingVariables p) (commonDimension p) (padding_rank p)

end
end Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingNonzero
