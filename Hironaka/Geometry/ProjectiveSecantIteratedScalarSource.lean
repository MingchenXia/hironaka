import Hironaka.Geometry.ProjectiveSecantProjectionScalarComparison

/-!
# Actual iterated original scalar sources and whole independently constructed embedding triangles
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveSpaceBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L K : Type u) [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] (χ : L →ₐ[k] K)

/-- The entire actual original coefficient spectrum triangle is literal. -/
theorem originalTowerSpec_composition :
    Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) =
    Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun a => χ.commutes a

variable (n : ℕ) {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1))

local notation "scalarKL" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "scalarLK" => Spec.map (CommRingCat.ofHom χ.toRingHom)
local notation "scalarKK" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "pX" => i ≫ projectiveSpaceStructure k (n + 1)
local notation "iL" => scalarClosedInclusion k L (algebraMap k L) n i
local notation "pL" => iL ≫ projectiveSpaceStructure L (n + 1)

/-- The actual whole original first scalar structure triangle and actual second native pullback internally paste to the SAME original direct scalar square. -/
theorem iteratedOriginalScalar_isPullback :
    IsPullback (pullback.fst pL scalarLK ≫ pullback.fst pX scalarKL)
      (pullback.snd pL scalarLK) pX scalarKK := by
  have hfirst : IsPullback (pullback.fst pX scalarKL) pL pX scalarKL := by
    rw [scalarClosedInclusion_structure]
    exact IsPullback.of_hasPullback _ _
  have h := (IsPullback.of_hasPullback pL scalarLK).paste_horiz hfirst
  rwa [originalTowerSpec_composition] at h

/-- The actual native universal property constructs the SAME iterated original source isomorphism, rather than assuming one. -/
def iteratedOriginalScalarSourceIso : pullback pL scalarLK ≅ pullback pX scalarKK :=
  (iteratedOriginalScalar_isPullback k L K χ n i).isoPullback

/-- The entire actual original source projection is retained. -/
theorem iteratedOriginalScalarSourceIso_hom_fst :
    (iteratedOriginalScalarSourceIso k L K χ n i).hom ≫ pullback.fst pX scalarKK =
      pullback.fst pL scalarLK ≫ pullback.fst pX scalarKL :=
  (iteratedOriginalScalar_isPullback k L K χ n i).isoPullback_hom_fst

/-- The entire actual new coefficient structure projection is retained. -/
theorem iteratedOriginalScalarSourceIso_hom_snd :
    (iteratedOriginalScalarSourceIso k L K χ n i).hom ≫ pullback.snd pX scalarKK =
      pullback.snd pL scalarLK :=
  (iteratedOriginalScalar_isPullback k L K χ n i).isoPullback_hom_snd

/-- The actual independently constructed original scalar closed embeddings retain their WHOLE literal scheme-map triangle under the internally produced actual source isomorphism. -/
theorem iteratedOriginalScalarSourceIso_embedding :
    (iteratedOriginalScalarSourceIso k L K χ n i).hom ≫
      scalarClosedInclusion k K (algebraMap k K) n i =
    scalarClosedInclusion L K χ.toRingHom n iL := by
  let e := iteratedOriginalScalarSourceIso k L K χ n i
  have hχ : χ.toRingHom.comp (algebraMap k L) = algebraMap k K :=
    RingHom.ext fun a => χ.commutes a
  have hcoef := projectiveCoefficientMap_comp (algebraMap k L) χ.toRingHom (n + 1)
  rw [hχ] at hcoef
  apply (isPullback_projectiveCoefficientMap (algebraMap k K) (n + 1)).hom_ext
  · have hr : scalarClosedInclusion L K χ.toRingHom n iL ≫
        projectiveCoefficientMap (algebraMap k K) (n + 1) =
        (pullback.fst pL scalarLK ≫ pullback.fst pX scalarKL) ≫ i := by
      rw [← hcoef, ← Category.assoc, scalarClosedInclusion_original,
        Category.assoc, scalarClosedInclusion_original, ← Category.assoc]
    rw [Category.assoc, scalarClosedInclusion_original, ← Category.assoc,
      iteratedOriginalScalarSourceIso_hom_fst, hr]
  · calc
      (e.hom ≫ scalarClosedInclusion k K (algebraMap k K) n i) ≫
          projectiveSpaceStructure K (n + 1) =
        e.hom ≫ (scalarClosedInclusion k K (algebraMap k K) n i ≫
          projectiveSpaceStructure K (n + 1)) := Category.assoc _ _ _
      _ = e.hom ≫ pullback.snd pX scalarKK :=
        congrArg (fun g => e.hom ≫ g) (scalarClosedInclusion_structure k K (algebraMap k K) n i)
      _ = pullback.snd pL scalarLK := iteratedOriginalScalarSourceIso_hom_snd k L K χ n i
      _ = scalarClosedInclusion L K χ.toRingHom n iL ≫ projectiveSpaceStructure K (n + 1) :=
        (scalarClosedInclusion_structure L K χ.toRingHom n iL).symm

end Hironaka.Geometry.ProjectiveSecant
