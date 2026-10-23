import DeJongAlterations.StableModification.Global.MainModel
import DeJongAlterations.Geometry.ProjectiveReduction
import DeJongAlterations.Geometry.NormalizationProjective

/-!
# From local and comparison pieces to a locally projective stable modification

Node G8 of `PLAN-T5.md` (§2.1 steps 5–6; Temkin, *Stable modification of relative curves*,
`semi-stable.tex`, proof of Theorem 1.5, T:3379–3399), conditional on the local inputs.

Let `S` be a projective variety over the field `k`, `(C, D)` a multipointed `S`-curve with
`C ⟶ S` projective, and `L = K(S)ᵃ` (decision D-DJ9). If local stable pieces cover `RZ_L(S)` and
comparison pieces cover the overlaps (`LocalStablePiece`, `ComparisonPiece`), then
`HasLocallyProjectiveStableModification k pS g D`
(`hasLocallyProjectiveStableModification_of_pieces`):

1. glue the base changes of the pieces over a refinement `p : S'' ⟶ S`
   (`exists_glued_model`, nodes G5–G7);
2. make the base projective and normal (obligation E1): a Chow modification
   `π : Y ⟶ S''` with `Y` projective over `k`
   (`ProjectiveReduction.exists_projective_modification_of_isProper`),
   followed by the normalization `ν : N ⟶ Y`, which is finite and birational, with `N` normal
   and projective over `k` (`NormalizationProjective.normalization_isProjectiveOver`); the
   composite `ψ = ν ≫ π ≫ p` is an alteration;
3. base change the glued model along `ν ≫ π` (`IsLocallyProjectiveStableModel.pullback`) and
   identify `(C ×_S S'') ×_{S''} N = C ×_S N`. This gives E2 (a stable η-modification), E3
   (local projectivity over a finite open cover), E4 (numerical stability), finite marks (proper
   and étale) and an isomorphism over a nonempty open of `N`.

With lane OM3D's projectivity theorem (`StableModificationProjectivity k`) and the integrated
bridge `Curves.hasStableModification_of_isStableModification`, this gives
`DeJong.TemkinStableModification k` (`temkinStableModification_of_hasLocallyProjective`).

Blueprint: `sm-global.tex`, `thm:sm-global-locally-projective-of-pieces`,
`thm:sm-global-tsm-of-locally-projective`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective IsMultipointedCurve)
open Curves (pullbackCompMap IsStableModification)
open RiemannZariskiSpace
open Geometry.NormalizationGluing (normalization normalizationStructure)

variable {k : Type u} [Field k] {S C : Scheme.{u}}

/-- **A locally projective stable modification from local and comparison pieces**
(`PLAN-T5.md` §2.1 steps 3–6, nodes G5–G8). Let `S` be a projective variety over `k`, `(C, D)` a
multipointed `S`-curve, `L ⊇ K(S)` algebraic (e.g. `K(S)ᵃ`). If every valuation ring of `RZ_L(S)`
lies in `RZ_L(T)` for a local stable piece `T` and for any two local stable pieces every
valuation ring of `RZ_L(T₁) ∩ RZ_L(T₂)` lies in `RZ_L(T')` for a comparison piece `T'`, then
`(C, D)` has a locally projective stable modification after a normal alteration projective over
`k`. -/
theorem hasLocallyProjectiveStableModification_of_pieces (pS : S ⟶ Spec (.of k))
    [IsVariety pS] (hSp : IsProjectiveOver pS) (g : C ⟶ S) (D : C.IdealSheafData)
    (hC : IsProjectiveOver (g ≫ pS)) (hD : IsMultipointedCurve g D)
    (L : Type u) [Field L] [Algebra S.functionField L] [Algebra.IsAlgebraic S.functionField L]
    (hpiece : ∀ W ∈ ofScheme (functionFieldPoint S L),
      ∃ P : LocalStablePiece pS g D L, W ∈ ofScheme P.ηT)
    (hcomp : ∀ (P₁ P₂ : LocalStablePiece pS g D L) (W : RiemannZariskiSpace L),
      W ∈ ofScheme P₁.ηT → W ∈ ofScheme P₂.ηT → ∃ Q : ComparisonPiece P₁ P₂, W ∈ ofScheme Q.η) :
    HasLocallyProjectiveStableModification k pS g D := by
  -- the base `S`
  have : IsProper pS := hSp.isProper
  have : S.IsSeparated := ⟨by rw [← terminal.comp_from pS]; infer_instance⟩
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace pS
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian pS
  have : Flat g := hD.flat
  have : IsProper (g ≫ pS) := hC.isProper
  have : IsProper g := IsProper.of_comp g pS
  -- steps 1–2: the glued model over a refinement
  obtain ⟨S'', _, p, η'', X, β, D', ι, hι, U, hAlt, hRef, hβp, hss, hgm, hns, hU, hproj, hiso⟩ :=
    exists_glued_model (pS := pS) (g := g) (D := D) (L := L) hpiece hcomp
  have hm : IsLocallyProjectiveStableModel (p ≫ pS) (pullback.snd g p)
      (D.comap (pullback.fst g p)) β D' :=
    { flat := inferInstance
      isProper := hβp
      isSemistablePair := hss
      genericMarks := hgm
      isNumericallyStable := hns
      locallyRelativelyProjective := ⟨ι, hι, fun i ↦ (pullback.snd g p) ⁻¹ᵁ U i, by
        rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top], hproj⟩
      isoLocus := hiso }
  -- step 3: a Chow modification and the normalization
  have : IsProper p := hRef.isProper
  have : IsVariety (p ≫ pS) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance }
  obtain ⟨Y, π, hπ, hYv, hYp⟩ :=
    Geometry.ProjectiveReduction.exists_projective_modification_of_isProper (p ≫ pS)
  have : IsVariety (π ≫ p ≫ pS) := hYv
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsIntegral (normalization Y) :=
    Geometry.NormalizationFinite.isIntegral_normalization
  have : IsAlteration (normalizationStructure Y) :=
    Geometry.NormalizationFiniteArbitraryField.normalizationStructure_isAlteration (π ≫ p ≫ pS)
  have : IsAlteration π := inferInstance
  let r : normalization Y ⟶ S'' := normalizationStructure Y ≫ π
  have : IsAlteration r := IsAlteration.comp _ _
  have : IsAlteration (r ≫ p) := IsAlteration.comp _ _
  have hNn : IsNormalScheme (normalization Y) :=
    Geometry.NormalizationGluing.normalization_isNormalScheme Y
  have hNp : IsProjectiveOver ((r ≫ p) ≫ pS) := by
    simpa only [r, Category.assoc] using
      Geometry.NormalizationProjective.normalization_isProjectiveOver (π ≫ p ≫ pS) hYp
  have hη : r (genericPoint (normalization Y)) = genericPoint S'' :=
    genericPoint_map_of_isDominant r
  -- step 4: base change of the glued model and identification of the target
  have hm2 := hm.pullback r hη
  let e := pullbackLeftPullbackSndIso g p r
  have hD : (D.comap (pullback.fst g (r ≫ p))).comap e.hom =
      (D.comap (pullback.fst g p)).comap (pullback.fst (pullback.snd g p) r) := by
    simp only [← Scheme.IdealSheafData.comap_comp, e, pullbackLeftPullbackSndIso_hom_fst]
  have hm3 := hm2.comp_iso e.hom (pullbackLeftPullbackSndIso_hom_snd g p r) hD
  have hpT : r ≫ p ≫ pS = (r ≫ p) ≫ pS := (Category.assoc _ _ _).symm
  rw [hpT] at hm3
  have : IsProper (pullbackCompMap β (pullback.snd g p) r ≫ e.hom) := hm3.isProper
  obtain ⟨U₀, hU₀, -, hiso₀⟩ := hm3.isoLocus
  refine ⟨normalization Y, inferInstance, r ≫ p, _, _,
    pullbackCompMap β (pullback.snd g p) r ≫ e.hom, inferInstance, hNn, hNp,
    hm3.isStableModification, hm3.locallyRelativelyProjective, hm3.isNumericallyStable,
    isFinite_marks_of_isProper hm3.isSemistablePair, U₀, ⟨⟨hU₀.some, hU₀.some_mem⟩⟩, hiso₀⟩

/-- **Temkin's stable modification theorem from the locally projective one** (node G8, final
step; PLAN-OM3 §4). Given lane OM3D's projectivity theorem `StableModificationProjectivity k` and
a locally projective stable modification for every family of `DeJong.TemkinStableModification`,
the integrated bridge `Curves.hasStableModification_of_isStableModification` gives
`DeJong.TemkinStableModification k`. -/
theorem temkinStableModification_of_hasLocallyProjective [IsAlgClosed k]
    (hP : StableModificationProjectivity k)
    (h : ∀ (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) (_ : IsVariety pS), IsNormalScheme S →
      IsProjectiveOver pS →
      ∀ (C : Scheme.{u}) (g : C ⟶ S) (D : C.IdealSheafData),
        IsProjectiveOver (g ≫ pS) → IsMultipointedCurve g D →
        Smooth (g.fiberToSpecResidueField (genericPoint S)) →
        IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
          (DeJong.fiberMarks g D (genericPoint S)) →
        GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)) →
        HasLocallyProjectiveStableModification k pS g D) :
    DeJong.TemkinStableModification k := by
  intro S pS hv hSn hSp C g D hC hD hsm hss hgi
  obtain ⟨S', _, ψ, C', D', β, hAlt, hn, hproj, hβ, hloc, hnum, hfin, U, hU, hiso⟩ :=
    h S pS hv hSn hSp C g D hC hD hsm hss hgi
  have : IsAlteration ψ := hAlt
  have hrp := hP S pS hv hSn hSp C g D hC hD hsm hss hgi S' hn ψ hproj C' β D' hβ hnum hloc
  exact Curves.hasStableModification_of_isStableModification pS g D hD ψ β D' hβ hfin hrp U hU
    hiso

end DeJongAlterations.StableModification.Global
