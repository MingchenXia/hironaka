import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingProduct
import DeJongAlterations.Geometry.Segre
import DeJongAlterations.Geometry.BoundaryAlteration

/-!
# Projectivity of the native global blowup

Compose the actual closed product embedding with the actual Segre closed
immersion. In particular the canonical Cartier-boundary alteration preserves
projectivity over the original field (de Jong 4.8).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjective

open BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {n : ℕ}

/-- Base change of an actual projective closed embedding, with its native pasted source. -/
def productClosedEmbedding (j : X ⟶ projectiveSpace R n) (m : ℕ) :
    pullback (j ≫ projectiveSpaceStructure R n) (projectiveSpaceStructure R m) ⟶
      Segre.projectiveProduct R n m :=
  (pullbackRightPullbackFstIso (projectiveSpaceStructure R n)
      (projectiveSpaceStructure R m) j).inv ≫
    pullback.snd j (pullback.fst (projectiveSpaceStructure R n)
      (projectiveSpaceStructure R m))

@[reassoc (attr := simp)]
theorem productClosedEmbedding_fst (j : X ⟶ projectiveSpace R n) (m : ℕ) :
    productClosedEmbedding j m ≫
      pullback.fst (projectiveSpaceStructure R n) (projectiveSpaceStructure R m) =
    pullback.fst (j ≫ projectiveSpaceStructure R n) (projectiveSpaceStructure R m) ≫ j := by
  exact pullbackRightPullbackFstIso_inv_snd_fst (projectiveSpaceStructure R n)
    (projectiveSpaceStructure R m) j

instance productClosedEmbedding_isClosedImmersion (j : X ⟶ projectiveSpace R n)
    [IsClosedImmersion j] (m : ℕ) : IsClosedImmersion (productClosedEmbedding j m) := by
  unfold productClosedEmbedding
  infer_instance

/-- The actual native ideal-sheaf blowup of a projective scheme is projective
over the original Noetherian coefficient ring. -/
theorem blowupStructure_comp_isProjective [IsNoetherianRing R] (D : X.IdealSheafData)
    (p : X ⟶ Spec (CommRingCat.of R)) (hp : IsProjectiveOver p) :
    IsProjectiveOver (blowupStructure D ≫ p) := by
  obtain ⟨n, j, hj, hbase⟩ := hp
  let := hj
  subst p
  obtain ⟨m, q, e, he, hefst, _hesnd⟩ :=
    BlowupProjectiveEmbedding.exists_closedProductEmbedding
      (j ≫ projectiveSpaceStructure R n) j D
  let := he
  refine ⟨Algebra.Segre.dimension n m,
    e ≫ productClosedEmbedding j m ≫ Segre.segre R n m, inferInstance, ?_⟩
  simp only [Category.assoc, Segre.segre_structure,
    productClosedEmbedding_fst_assoc, reassoc_of% hefst]

/-- The canonical boundary blowup retains projectivity, generic etaleness,
and the full Cartier inverse-image ideal simultaneously. -/
theorem canonical_projective_blowup_boundary {k : Type u} [Field k]
    [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveOver p)
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    IsProjectiveOver (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z) ≫ p) ∧
      IsAlteration (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)) ∧
      IsGenericallyEtale (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)) ∧
      IsEffectiveCartierDivisor ((Scheme.IdealSheafData.vanishingIdeal Z).comap
        (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z))) ∧
      ((Scheme.IdealSheafData.vanishingIdeal Z).comap
        (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z))).support =
          Z.preimage (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)).continuous := by
  obtain ⟨hf, hE, hs⟩ := BoundaryAlteration.canonical_blowup_boundary Z hZ
  exact ⟨blowupStructure_comp_isProjective _ p hp, hf,
    BoundaryAlteration.canonical_blowup_boundary_genericallyEtale Z hZ, hE, hs⟩

/-- Source 4.8: a projective integral scheme admits an actual projective
generically etale alteration with the prescribed full Cartier boundary. -/
theorem exists_projective_genericallyEtale_alteration_cartierPreimage
    {k : Type u} [Field k] [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveOver p)
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (E : Y.IdealSheafData),
      IsProjectiveOver (f ≫ p) ∧ IsAlteration f ∧ IsGenericallyEtale f ∧
        IsEffectiveCartierDivisor E ∧ E.support = Z.preimage f.continuous := by
  exact ⟨blowup (Scheme.IdealSheafData.vanishingIdeal Z),
    blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z),
    (Scheme.IdealSheafData.vanishingIdeal Z).comap
      (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)),
    canonical_projective_blowup_boundary p hp Z hZ⟩

end DeJongAlterations.Geometry.BlowupProjective
