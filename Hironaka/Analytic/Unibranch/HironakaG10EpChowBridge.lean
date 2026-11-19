import Hironaka.Analytic.Unibranch.HironakaG10GenChow
import Hironaka.Analytic.Unibranch.HironakaG11NativeTowerRepresentation

/-!
# G10-05: the general Chow endpoint, its single remaining input and its manifold contract

Run 0081 lane G10EP (delivery task G10-05; research item G10-05-01 and the Hironaka consumer contract
G10-05-01.sgpt).  Blueprint: `hironaka-g10ep-chow-bridge.tex`.

1. **The single remaining input.**  Goal G11 is proved
   (`HironakaG11PresUnconditional.compactSingularCentreResolution`), so the general Chow lemma
   `HironakaChowLemmaGeneral` (`chow:general`, book `thm:HironakaChow`) follows from Hironaka's
   flattening theorem alone (`hironakaChowLemmaGeneral_of_hironakaFlattening`).
2. **Lifting through a finite smooth-centre modification** (unconditional).  A compact complex
   manifold mapping to the base of a finite composition `σ` of smooth-centre blowups, by a map which
   is open off a thin set, lifts through `σ` after a finite blowup sequence of the manifold
   (`exists_blowupSequence_lift_of_isModification`): `σ` is represented over its base by a tower of
   native ideal blowups (G11, `exists_nativeTower_representation`), and manifolds lift through such
   towers by principalization (`exists_lift_of_isNativeBlowupTower`).
3. **The manifold contract.**  Over the whole model of a compact complex manifold `M`, domination by
   a finite smooth-centre modification is equivalent to domination by a manifold blowup sequence
   of `M` (`isDominatedByModification_iff_exists_blowupSequence`).  Hence the general Chow lemma
   implies the manifold Chow lemma `HironakaChowLemmaManifold` consumed by the Hironaka book
   (`hironakaChowLemmaManifold_of_hironakaChowLemmaGeneral`), and its form for an arbitrary reduced
   source over a manifold base (`exists_blowupSequence_domination`), which is what the book's
   `thm:liftableflag` uses.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10EpChowBridge

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaChowLemma AnalyticModificationLocalDiscrepancy
  SourceReducedComplexSpace SmoothCentreModification OriginalNativeModification
  OriginalProperBimeromorphicNative HironakaG10ChowTowerDomination
  HironakaG10ChowFlatteningReduction HironakaG10GenStatement HironakaG10GenChow
  HironakaG11NativeTowerRepresentation

noncomputable section

/-! ### The single remaining input -/

/-- **The general Chow lemma from flattening alone.**  With the proved compact resolution of
singularities by smooth-centre blowups (goal G11), Hironaka's flattening theorem implies Hironaka's
Chow lemma for compact reduced complex spaces. -/
theorem hironakaChowLemmaGeneral_of_hironakaFlattening (H₀ : HironakaFlattening) :
    HironakaChowLemmaGeneral :=
  hironakaChowLemmaGeneral_of_flattening_of_resolution H₀
    HironakaG11PresUnconditional.compactSingularCentreResolution

/-! ### Lifting manifolds through finite smooth-centre modifications -/

/-- The identity of a reduced complex space is open off a thin set. -/
theorem isOpenOffThin_id (X : SourceReducedComplexSpace) :
    IsOpenOffThin (𝟙 X : X ⟶ X).hom.left.base := by
  refine IsOpenOffThin.of_isOpenMap (fun U hU => ?_)
  convert hU
  exact image_id U

variable {n : ℕ}

/-- **Lifting through a finite smooth-centre modification.**  Let `σ : X' ⟶ X` be a finite
composition of blowups with smooth nowhere dense centres, `W` a compact complex manifold and
`γ₀ : wholeModel W ⟶ X` open off a thin set.  Then there are a finite blowup sequence
`ρ : W' → W` along nowhere dense closed submanifolds and a morphism `γ : wholeModel W' ⟶ X'`
with `γ ≫ σ = ρ ≫ γ₀`. -/
theorem exists_blowupSequence_lift_of_isModification {X X' : SourceReducedComplexSpace}
    {σ : X' ⟶ X} (hσ : IsModification σ) {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W] [CompactSpace W]
    (γ₀ : wholeModel (n := n) W ⟶ X) (hγ₀ : IsOpenOffThin γ₀.hom.left.base) :
    ∃ (W' : Type) (_ : TopologicalSpace W') (_ : ChartedSpace (ComplexModel n) W')
      (_ : IsComplexManifold n W') (ρ : W' → W) (hρ : IsBlowupSequence n W W' ρ)
      (γ : wholeModel (n := n) W' ⟶ X'),
      γ ≫ σ = nativeMorphism hρ.contMDiff ≫ γ₀ := by
  obtain ⟨Z, a, τ, hτ, ha⟩ := exists_nativeTower_representation hσ
  obtain ⟨W', tW', cW', mW', ρ, hρ, γ, hγ, -⟩ := exists_lift_of_isNativeBlowupTower hτ γ₀ hγ₀
  let := tW'
  let := cW'
  let := mW'
  refine ⟨W', tW', cW', mW', ρ, hρ, γ ≫ a.hom, ?_⟩
  rw [Category.assoc, ha, hγ]

/-! ### The manifold contract -/

section Manifold

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Domination over a manifold base by a manifold blowup sequence.**  If `f : Y ⟶ wholeModel M`,
`M` a compact complex manifold and `Y` an arbitrary reduced complex space, is dominated by a finite
composition of smooth-centre blowups, then it is dominated by a finite blowup sequence
`ρ : W → M` of complex manifolds: `G ≫ f = ρ` for a morphism `G : wholeModel W ⟶ Y`. -/
theorem exists_blowupSequence_domination_of_isDominatedByModification [CompactSpace M]
    {Y : SourceReducedComplexSpace} {f : Y ⟶ wholeModel (n := n) M}
    (hf : IsDominatedByModification f) :
    ∃ (W : Type) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (ρ : W → M) (hρ : IsBlowupSequence n M W ρ)
      (G : wholeModel (n := n) W ⟶ Y), G ≫ f = nativeMorphism hρ.contMDiff := by
  obtain ⟨X', σ, g, hσ, hg⟩ := hf
  obtain ⟨W, tW, cW, mW, ρ, hρ, γ, hγ⟩ :=
    exists_blowupSequence_lift_of_isModification hσ (𝟙 (wholeModel (n := n) M))
      (isOpenOffThin_id _)
  let := tW
  let := cW
  let := mW
  refine ⟨W, tW, cW, mW, ρ, hρ, γ ≫ g, ?_⟩
  rw [Category.assoc, hg, hγ, Category.comp_id]

/-- **The manifold contract is exactly domination by a modification.**  Over the whole model of a
compact complex manifold, a morphism is dominated by a finite composition of native smooth-centre
blowups iff it is dominated by a finite blowup sequence of complex manifolds. -/
theorem isDominatedByModification_iff_exists_blowupSequence [CompactSpace M]
    {Y : SourceReducedComplexSpace} (f : Y ⟶ wholeModel (n := n) M) :
    IsDominatedByModification f ↔
      ∃ (W : Type) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
        (_ : IsComplexManifold n W) (ρ : W → M) (hρ : IsBlowupSequence n M W ρ)
        (G : wholeModel (n := n) W ⟶ Y), G ≫ f = nativeMorphism hρ.contMDiff := by
  constructor
  · exact exists_blowupSequence_domination_of_isDominatedByModification
  · rintro ⟨W, tW, cW, mW, ρ, hρ, G, hG⟩
    let := tW
    let := cW
    let := mW
    exact ⟨wholeModel (n := n) W, nativeMorphism hρ.contMDiff, G,
      HironakaG10GenBlowupBridge.isModification_nativeMorphism hρ, hG⟩

/-- **Chow domination of a singular source over a manifold base.**  Given the general Chow lemma,
every proper bimeromorphic morphism `f : Y ⟶ wholeModel M` from an arbitrary reduced complex space
to (the whole model of) a compact complex manifold is dominated by a finite blowup sequence of `M`
along nowhere dense closed submanifolds. -/
theorem exists_blowupSequence_domination (H : HironakaChowLemmaGeneral) [CompactSpace M]
    {Y : SourceReducedComplexSpace} (f : Y ⟶ wholeModel (n := n) M)
    (hf : IsProperBimeromorphic f) :
    ∃ (W : Type) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (ρ : W → M) (hρ : IsBlowupSequence n M W ρ)
      (G : wholeModel (n := n) W ⟶ Y), G ≫ f = nativeMorphism hρ.contMDiff := by
  have hcpt : CompactSpace (wholeModel (n := n) M).obj.left :=
    (Homeomorph.Set.univ M).symm.compactSpace
  exact exists_blowupSequence_domination_of_isDominatedByModification (H _ _ f hcpt hf)

end Manifold

/-- **The general Chow lemma implies the manifold Chow lemma** consumed by the Hironaka book
(`HironakaChowLemmaManifold`, TN goal G10a, in the universe of the native category). -/
theorem hironakaChowLemmaManifold_of_hironakaChowLemmaGeneral (H : HironakaChowLemmaGeneral) :
    HironakaChowLemmaManifold.{0} := by
  intro n X _ _ _ _ Y _ _ _ f hf
  obtain ⟨W, tW, cW, mW, ρ, hρ, G, hG⟩ :=
    exists_blowupSequence_domination H (nativeMorphism hf.1)
      (nativeMorphism_isProperBimeromorphic hf)
  let := tW
  let := cW
  let := mW
  refine ⟨W, tW, cW, mW, ρ, nativePointMap G, hρ, nativePointMap_contMDiff G, ?_⟩
  funext w
  exact congrArg (fun K : wholeModel (n := n) W ⟶ wholeModel (n := n) X =>
    (K.hom.left.base ⟨w, mem_univ w⟩).val) hG

end

end Hironaka.Analytic.Unibranch.HironakaG10EpChowBridge
