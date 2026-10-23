import DeJongAlterations.StableModificationBridge.LocalPolarizationMap

/-!
# A finite native relative section map from natural original fibre hypotheses

The actual two-affine cover and fibre ampleness are produced internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace DeJongAlterations.StableModificationBridge.FibrePolarizationFinite

open StableModification.Projectivity Geometry.ProjectiveIdeal LocalPolarizationMap

universe u

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- Natural original good-fibre-section hypotheses internally produce the entire actual finite
relative section map above a base subneighborhood, on a positive power of the same line bundle. -/
theorem exists_finite_sectionMap_of_hasFiberSection
    (β : X ⟶ Y) [IsProper β] (p : Y ⟶ Spec (.of R))
    [IsLocallyNoetherian Y] (hloc : LocallyRelativelyProjective p β)
    (L : LineBundleData X) {y : Y} (hy : IsClosed ({y} : Set Y))
    [Infinite (Y.residueField y)] (hdim : topologicalKrullDim (β.fiber y) ≤ 1)
    (hsec : HasFiberSection β L y) :
    ∃ (O : Y.Opens) (hyO : y ∈ O), ∃ M : ℕ, 0 < M ∧
      ∃ (N : ℕ) (T : Fin (N + 1) →
        (L.pullback (β ⁻¹ᵁ O).ι).Sections (M : ℤ) ⊤)
        (hT : LineBundleData.Generates T) (E : O.toScheme.Opens),
        (⟨y, hyO⟩ : O.toScheme) ∈ E ∧
        IsFinite (sectionMap (β ∣_ O) (O.ι ≫ p) hT ∣_
          (pullback.fst (O.ι ≫ p) (projectiveSpaceStructure R N) ⁻¹ᵁ E)) := by
  obtain ⟨D, hyW⟩ := exists_twoAffineCover_of_noetherian p hloc L hy hdim
  have hL := fiberAmple_of_hasFiberSection hloc L y hdim hsec
  obtain ⟨n, s, hn, hgen, hzero⟩ := hsec
  obtain ⟨O, hyO, _, M, hM, N, T, hT, E, hyE, hfin⟩ :=
    exists_finite_sectionMap β p D hyW hy hdim hL hn s hgen hzero
  exact ⟨O, hyO, M, hM, N, T, hT, E, hyE, hfin⟩

end DeJongAlterations.StableModificationBridge.FibrePolarizationFinite
