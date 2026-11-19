import Hironaka.Analytic.Unibranch.HironakaG10GenChow
import Hironaka.Analytic.Unibranch.HironakaG11PresPresentation

/-!
# Embedded resolutions with centres in the singular loci of the strict transforms

Bierstone–Milman 1997 (Invent. Math. 128), Theorem 1.6, condition (1): an embedded resolution
`X = X₀ ⊂ M₀ ← M₁ ← ⋯ ← M_r` of a closed analytic subset of a manifold whose every centre `C_j` lies
in the singular locus of the current strict transform `X_j` (until `X_j` is smooth).  This file
shows that such an ambient tower induces, on the reduced closed subspaces, a finite composition of
blowups with smooth centres in the singular loci of the successive spaces:

* `CentresInSingular W T` — every centre of the tower `T` lies in the embedded singular set of the
  strict transform of `W` at its stage; it implies `CentresContainedDense W T`
  (`centresContainedDense_of_centresInSingular`);
* `strictTransformMorphism_isSingularCentreStep` — one ambient blowup along a centre inside the
  singular set of `W` restricts to a singular-centre step of `(W, 𝒪/𝓘_W)`;
* **`isSingularCentreModification_projectionMorphism`** — the native projection of the final strict
  transform is an `IsSingularCentreModification`;
* `HasSingularCentreEmbeddedResolution W` (a property of ONE given `W`, not a named input), and
  **`hasSingularCentreResolution_ofClosedAnalytic`**: it gives the G11 per-space endpoint
  `HasSingularCentreResolution (W, 𝒪/𝓘_W)`, hence the book's `thm:res`
  (`hasModificationResolution_ofClosedAnalytic`) and, with Hironaka's flattening theorem, the Chow
  lemma over the compact embedded space (`isDominatedByModification_ofClosedAnalytic`);
* `SingularCentreEmbeddedResolution` — the statement of BM97 Thm 1.6 (1) for compact ambient
  manifolds, as a `Prop` (NOT proved here, and used only in the last corollary).

The existing embedded resolution of the library (`Hironaka.exists_embeddedResolution_analytic`,
`HironakaResolutionSpace.IsStrictTransformResolution`) has centres over `W_sing` only, not inside
the strict transforms, so it does not provide `CentresInSingular` (see the module docstring of
`HironakaEmbeddedAnalytic` and Włodarczyk 2005, Theorem 2.0.2 (2)).

Blueprint: `hironaka-g1-r-singular-centre-embedded.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1RSingularCentreEmbedded

open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers SourceReducedComplexSpace SmoothCentreModification
  ContainedCentreModificationSequence HironakaG11SingularCentreModification
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG10GenStatement HironakaG10GenChow
  HironakaG10ChowFlatteningReduction
open Hironaka.HironakaEmbeddedAnalytic (singularSet singularSet_subset)

noncomputable section

/-! ### One ambient blowup -/

section Step

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C W : Set M} {π : Y → M}

/-- A subset of the singular set of an analytic set is nowhere dense in it. -/
theorem subset_closure_diff_of_subset_singularSet (hWa : IsComplexAnalyticSubset (n := n) W)
    (hC : C ⊆ singularSet (n := n) W) : W ⊆ closure (W \ C) :=
  (HironakaResolutionSpace.subset_closure_diff_singularSet hWa).trans
    (closure_mono (sdiff_subset_sdiff_right hC))

/-- **One ambient blowup along a centre in the singular set of `W`** restricts to a blowup of the
reduced space `(W, 𝒪/𝓘_W)` along a smooth centre contained in its intrinsic singular locus. -/
theorem strictTransformMorphism_isSingularCentreStep (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hC : C ⊆ singularSet (n := n) W) :
    IsSingularCentreStep (EmbeddedBlowup.strictTransformMorphism hπ hWa) := by
  have hCW : C ⊆ W := hC.trans (singularSet_subset W)
  refine ⟨_, _, strictTransformMorphism_isSmoothCentreBlowup hπ hWa hπ.1 hCW
    (subset_closure_diff_of_subset_singularSet hWa hC), ?_⟩
  rintro _ ⟨c, rfl⟩
  exact (HironakaG11PresPresentation.mem_intrinsicSingularLocus_ofClosedAnalytic_iff hWa _).mpr
    (hC c.2)

end Step

/-! ### Towers -/

section Tower

variable {n : ℕ} {X : CMfd.{0} n}

/-- **Centres in the singular loci of the strict transforms** (BM97 Thm 1.6 (1)): every centre of
the tower lies in the embedded singular set of the strict transform of `W` at its stage. -/
def CentresInSingular (W : Set X) : {Y : CMfd.{0} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ =>
      CentresInSingular W T ∧ C ⊆ singularSet (n := n) (strictTransform n T.proj W)

/-- Centres in the singular loci are contained, and nowhere dense, in the strict transforms. -/
theorem centresContainedDense_of_centresInSingular {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresInSingular W T → CentresContainedDense W T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
    obtain ⟨hT, hC⟩ := h
    have hN := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform
      T.isBlowupSequence hW
    exact ⟨centresContainedDense_of_centresInSingular hW T hT,
      hC.trans (singularSet_subset _), subset_closure_diff_of_subset_singularSet hN hC⟩

private theorem object_eq {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) (hAB : A = B) :
    ofClosedAnalytic A hA = ofClosedAnalytic B hB := by
  cases hAB
  rfl

private theorem object_eqToHom_base {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) (hAB : A = B) (a : A) :
    ((eqToHom (object_eq hA hB hAB)).hom.left.base a).val = a.val := by
  cases hAB
  rfl

private theorem precomp_eqToHom {A B Z : SourceReducedComplexSpace}
    (hAB : A = B) {p : B ⟶ Z} (hp : IsSingularCentreModification p) :
    IsSingularCentreModification (eqToHom hAB ≫ p) := by
  cases hAB
  simpa only [eqToHom_refl, Category.id_comp] using hp

/-- The strict transform along the empty tower is the closed set itself. -/
theorem strictTransform_refl {W : Set X} (hW : IsClosed W) :
    strictTransform n (BlowupTower.refl : BlowupTower X X).proj W = W := by
  change strictTransform n (id : X → X) W = W
  rw [strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id]
  exact hW.closure_eq

-- The successive strict transforms, one blowup at a time (the construction of
-- `ContainedCentreModificationSequence`, whose helpers are private there).
private def iteratedCarrier (W : Set X) : {Y : CMfd.{0} n} → BlowupTower X Y → Set Y
  | _, .refl => W
  | _, .step T _ π _ => strictTransform n π (iteratedCarrier W T)

private theorem iterated_analytic {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    IsComplexAnalyticSubset (n := n) (iteratedCarrier W T) := by
  induction T with
  | refl => exact hW
  | step T C π hπ ih =>
    exact HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ ih

private theorem iterated_eq_native {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    iteratedCarrier W T = strictTransform n T.proj W := by
  induction T with
  | refl =>
    symm
    change strictTransform n (id : X → X) W = W
    rw [strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id]
    exact hW.isClosed.closure_eq
  | step T C π hπ ih =>
    change strictTransform n π (iteratedCarrier W T) = strictTransform n (T.proj ∘ π) W
    rw [ih, StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]

private theorem iterated_landing {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) : iteratedCarrier W T ⊆ T.proj ⁻¹' W := by
  rw [iterated_eq_native hW T]
  exact HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous
    hW.isClosed

private def iteratedProjection {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    ofClosedAnalytic (iteratedCarrier W T) (iterated_analytic hW T) ⟶ ofClosedAnalytic W hW :=
  ObjectProperty.homMk (Over.homMk
    (HironakaActualAnalyticSubspaceMaps.actualSubspaceMap T.contMDiff_proj
      (fun _ hy => iterated_landing hW T hy))
    (HironakaReducedComplexAnalyticSpaces.actualSubspaceMap_point T.contMDiff_proj
      (fun _ hy => iterated_landing hW T hy)))

private theorem iteratedProjection_refl {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    iteratedProjection hW (.refl : BlowupTower X X) = 𝟙 (ofClosedAnalytic W hW) := by
  apply morphism_eq_of_pointwise_eq
  intro x
  rfl

private theorem iteratedProjection_step {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {Y Z : CMfd.{0} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    iteratedProjection hW (.step T C π hπ) =
      EmbeddedBlowup.strictTransformMorphism hπ (iterated_analytic hW T) ≫
        iteratedProjection hW T := by
  apply morphism_eq_of_pointwise_eq
  intro x
  apply Subtype.ext
  rfl

private theorem iterated_isSingularCentreModification {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hT : CentresInSingular W T) :
    IsSingularCentreModification (iteratedProjection hW T) := by
  induction T with
  | refl =>
    rw [iteratedProjection_refl]
    exact .id _
  | step T C π hπ ih =>
    obtain ⟨hT, hC⟩ := hT
    have hC' : C ⊆ singularSet (n := n) (iteratedCarrier W T) := by
      rwa [iterated_eq_native hW T]
    rw [iteratedProjection_step]
    exact .cons _ _ (strictTransformMorphism_isSingularCentreStep hπ (iterated_analytic hW T) hC')
      (ih hT)

/-- **The native projection of a tower with centres in the singular loci of the strict transforms
is a finite composition of blowups with smooth centres in the singular loci** of the successive
reduced spaces (`IsSingularCentreModification`, the sequences of `g11:general`). -/
theorem isSingularCentreModification_projectionMorphism {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : CentresInSingular W T) : IsSingularCentreModification (projectionMorphism hW T) := by
  let hN := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
  let hI := iterated_analytic hW T
  have hsets : iteratedCarrier W T = strictTransform n T.proj W := iterated_eq_native hW T
  have hobj : ofClosedAnalytic (iteratedCarrier W T) hI =
      ofClosedAnalytic (strictTransform n T.proj W) hN := object_eq hI hN hsets
  have hm := precomp_eqToHom hobj.symm (iterated_isSingularCentreModification hW T hT)
  have hfull : eqToHom hobj.symm ≫ iteratedProjection hW T = projectionMorphism hW T := by
    apply morphism_eq_of_pointwise_eq
    intro y
    apply Subtype.ext
    change T.proj ((eqToHom hobj.symm).hom.left.base y).val = T.proj y.val
    exact congrArg T.proj (object_eqToHom_base hN hI hsets.symm y)
  rw [hfull] at hm
  exact hm

/-! ### Resolutions of embedded spaces -/

/-- **An embedded resolution of `W` with centres in the singular loci of the strict transforms**
(BM97 Thm 1.6 (1)–(2) for ONE given `W`, truncated when the strict transform becomes smooth): a tower
whose every centre lies in the singular set of the current strict transform and whose final strict
transform is a closed submanifold. A property of the given `W`, not an assumed theorem. -/
def HasSingularCentreEmbeddedResolution (W : Set X) : Prop :=
  ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y), CentresInSingular W T ∧
    IsClosedSubmanifold n (strictTransform n T.proj W)

/-- A closed submanifold is its own embedded resolution (the empty tower). -/
theorem hasSingularCentreEmbeddedResolution_of_isClosedSubmanifold {W : Set X}
    (h : IsClosedSubmanifold n W) : HasSingularCentreEmbeddedResolution W := by
  refine ⟨X, BlowupTower.refl, trivial, ?_⟩
  rw [strictTransform_refl h.1]
  exact h

/-- **The G11 per-space endpoint for an embedded space.** An embedded resolution of `W` with
centres in the singular loci of the strict transforms gives a resolution of the reduced space
`(W, 𝒪/𝓘_W)` by finitely many blowups with smooth centres in the singular loci of the successive
spaces. -/
theorem hasSingularCentreResolution_ofClosedAnalytic {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (h : HasSingularCentreEmbeddedResolution W) :
    HasSingularCentreResolution (ofClosedAnalytic W hW) := by
  obtain ⟨Y, T, hT, hsm⟩ := h
  exact ⟨_, projectionMorphism hW T, isSingularCentreModification_projectionMorphism hW T hT,
    isSmooth_ofClosedAnalytic_of_isClosedSubmanifold hsm⟩

/-- The book's `thm:res` for an embedded space with such an embedded resolution. -/
theorem hasModificationResolution_ofClosedAnalytic {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (h : HasSingularCentreEmbeddedResolution W) :
    HasModificationResolution (ofClosedAnalytic W hW) :=
  hasModificationResolution_of_hasSingularCentreResolution
    (hasSingularCentreResolution_ofClosedAnalytic hW h)

/-- The reduced closed subspace on a closed subset of a compact manifold is compact. -/
theorem compactSpace_ofClosedAnalytic [CompactSpace X] {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    CompactSpace (ofClosedAnalytic W hW).obj.left := by
  change CompactSpace W
  exact isCompact_iff_compactSpace.mp hW.isClosed.isCompact

/-- **The Chow lemma over a compact embedded space with a singular-centre embedded resolution**
(from Hironaka's flattening theorem): every proper bimeromorphic morphism to `(W, 𝒪/𝓘_W)`, `W` a
closed analytic subset of a compact complex manifold having an embedded resolution with centres in
the singular loci of the strict transforms, is dominated by a finite composition of blowups with
smooth centres. -/
theorem isDominatedByModification_ofClosedAnalytic (H₀ : HironakaFlattening) [CompactSpace X]
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (h : HasSingularCentreEmbeddedResolution W) {Y : SourceReducedComplexSpace}
    (f : Y ⟶ ofClosedAnalytic W hW) (hf : IsProperBimeromorphic f) :
    IsDominatedByModification f :=
  isDominatedByModification_of_hasModificationResolution H₀ f (compactSpace_ofClosedAnalytic hW) hf
    (hasModificationResolution_ofClosedAnalytic hW h)

end Tower

/-! ### The statement of BM97 Theorem 1.6 (1) for compact ambient manifolds -/

/-- **Embedded resolution with centres in the singular loci of the strict transforms**
(Bierstone–Milman 1997, Theorem 1.6, conditions (1) and (2), truncated at the first smooth strict
transform), for closed analytic subsets of compact complex manifolds, as a proposition. It is NOT
proved here; it is the precise missing input for `HasSingularCentreResolution` of embedded compact
spaces (the library's own embedded resolution only has centres OVER the singular set). -/
def SingularCentreEmbeddedResolution : Prop :=
  ∀ (n : ℕ) (X : CMfd.{0} n), CompactSpace X → ∀ W : Set X, IsComplexAnalyticSubset (n := n) W →
    HasSingularCentreEmbeddedResolution W

/-- With Hironaka's flattening theorem, BM97 Thm 1.6 (1) gives the Chow lemma over every compact
embedded space `(W, 𝒪/𝓘_W)`, `W` closed analytic in a compact complex manifold. -/
theorem isDominatedByModification_ofClosedAnalytic_of_singularCentreEmbeddedResolution
    (H₀ : HironakaFlattening) (H : SingularCentreEmbeddedResolution) {n : ℕ} {X : CMfd.{0} n}
    [CompactSpace X] {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : SourceReducedComplexSpace} (f : Y ⟶ ofClosedAnalytic W hW) (hf : IsProperBimeromorphic f) :
    IsDominatedByModification f :=
  isDominatedByModification_ofClosedAnalytic H₀ hW (H n X inferInstance W hW) f hf

end

end Hironaka.Analytic.Unibranch.HironakaG1RSingularCentreEmbedded
