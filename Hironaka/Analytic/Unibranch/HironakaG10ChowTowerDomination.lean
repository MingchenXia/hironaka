import Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion
import Hironaka.Analytic.Unibranch.HironakaG10ChowNativeDominationLift
import Hironaka.Resolution.HironakaG10ChowGermIdealDictionary
import Hironaka.Resolution.HironakaG10ChowStrictSquare
import Hironaka.Resolution.HironakaChowLemma

/-!
# Domination by a tower of native ideal blowups

The second step of the assembly of Hironaka's Chow lemma for manifolds (goal G10a,
blueprint `hironaka-g10-chowside-tower-domination.tex`).  A finite tower of native blowups
of finite-type ideals with dense unit loci over the whole model of a compact complex manifold
`X`, carrying a native morphism to the whole model of `Y` over `X`, gives stable domination
of `f : Y → X` by blowup sequences with smooth centres.  The proof lifts a manifold through
the tower one blowup at a time: the pulled-back ideal of the next centre is a coherent ideal
sheaf of germs with thin zero locus (`HironakaG10ChowGermIdealDictionary`), principalization
makes it invertible, and the native universal property of the blowup lifts the manifold.  No
composite-blowup theorem (`chow:blowup-composite`) is used.

Main declarations:

* `IsNativeBlowupTower` — finite towers of native ideal blowups with dense unit loci.
* `IsOpenOffThin` and its calculus — maps which are open off a closed set with empty
  interior; the invariant which keeps the pulled-back centres thin.
* `exists_lift_of_isNativeBlowupTower` — lifting a manifold through a tower after a blowup
  sequence.
* `hasStableBlowupDomination_of_isNativeBlowupTower`,
  `hasBlowupDomination_of_isNativeBlowupTower` — native tower domination gives stable
  domination by blowup sequences.
* `isDominatingIdeal_modelGermIdeal_of_native_domination` — a single native blowup over `Y`
  gives a dominating ideal (`IsDominatingIdeal`).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowTowerDomination

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaG10ChowGermIdealDictionary HironakaG10ChowStrictSquare HironakaChowLemma
  AnalyticModificationLocalDiscrepancy HironakaAdmissibleSequence
  SourceReducedComplexSpace OriginalNativeModification OriginalProperBimeromorphicNative
  OriginalFiniteIdealBlowup OriginalFiniteIdealBlowupUniversal HironakaG10ChowNativeIsoCriterion

noncomputable section

/-! ### Maps which are open off a closed thin set -/

section Topology

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- `g` maps open subsets of the complement of some closed set with empty interior to open
sets. -/
def IsOpenOffThin (g : α → β) : Prop :=
  ∃ E : Set α, IsClosed E ∧ interior E = ∅ ∧
    ∀ U : Set α, IsOpen U → U ⊆ Eᶜ → IsOpen (g '' U)

theorem IsOpenOffThin.of_isOpenMap {g : α → β} (hg : IsOpenMap g) : IsOpenOffThin g :=
  ⟨∅, isClosed_empty, interior_empty, fun U hU _ => hg U hU⟩

/-- Thin sets pull back to thin sets. -/
theorem IsOpenOffThin.interior_preimage_eq_empty {g : α → β} (hg : IsOpenOffThin g)
    {S : Set β} (hS : interior S = ∅) : interior (g ⁻¹' S) = ∅ := by
  obtain ⟨E, hEc, hEi, hopen⟩ := hg
  exact interior_preimage_eq_empty_of_isOpen_image hEc hEi hopen hS

theorem IsOpenOffThin.comp {g : α → β} {h : β → γ} (hgc : Continuous g)
    (hg : IsOpenOffThin g) (hh : IsOpenOffThin h) : IsOpenOffThin (h ∘ g) := by
  obtain ⟨E₁, hE₁c, hE₁i, hopen₁⟩ := hg
  obtain ⟨E₂, hE₂c, hE₂i, hopen₂⟩ := hh
  exact ⟨E₁ ∪ g ⁻¹' E₂, hE₁c.union (hE₂c.preimage hgc),
    interior_union_preimage_eq_empty hE₁c hE₁i hopen₁ hE₂i,
    isOpen_image_comp_of_isOpen_image hopen₁ hopen₂⟩

/-- **Lifting generic openness.**  If `π ∘ g = q` with `q` continuous and open off a thin
set, and `π` is continuous and injective over the complement of a closed thin set `T`, then
`g` is open off a thin set. -/
theorem IsOpenOffThin.of_comp_injOn {g : α → β} {π : β → γ} {q : α → γ}
    (hπ : Continuous π) {T : Set γ} (hTc : IsClosed T) (hTi : interior T = ∅)
    (hinj : InjOn π (π ⁻¹' Tᶜ)) (hq : IsOpenOffThin q) (hqc : Continuous q)
    (hfac : ∀ a, π (g a) = q a) : IsOpenOffThin g := by
  obtain ⟨E, hEc, hEi, hopen⟩ := hq
  refine ⟨E ∪ q ⁻¹' T, hEc.union (hTc.preimage hqc),
    interior_union_preimage_eq_empty hEc hEi hopen hTi, ?_⟩
  intro U hU hUE
  have hUE₁ : U ⊆ Eᶜ := fun u hu hu' => hUE hu (Or.inl hu')
  have hUT : ∀ u ∈ U, q u ∉ T := fun u hu hu' => hUE hu (Or.inr hu')
  have himg : g '' U = π ⁻¹' (q '' U) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (hfac u).symm⟩
    · rintro ⟨u, hu, hzu⟩
      refine ⟨u, hu, hinj ?_ ?_ ?_⟩
      · change π (g u) ∈ Tᶜ
        rw [hfac u]
        exact hUT u hu
      · change π z ∈ Tᶜ
        rw [← hzu]
        exact hUT u hu
      · rw [hfac u, hzu]
  rw [himg]
  exact (hopen U hU hUE₁).preimage hπ

end Topology

/-! ### Generic openness of modifications and native blowups -/

section Generic

variable {n : ℕ}

/-- A proper modification of complex manifolds is open off its exceptional set. -/
theorem isOpenOffThin_of_isAnalyticModification {X Y : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) : IsOpenOffThin f := by
  obtain ⟨_, _, A, B, s, hAc, _, hAi, hBc, _, _, hpre, hs, hfs, hsf⟩ := hf
  refine ⟨A, hAc, hAi, ?_⟩
  intro U hU hUA
  have himg : f '' U = Bᶜ ∩ s ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyA : y ∉ A := hUA hy
      have hfy : f y ∉ B := by
        intro h
        have h' : y ∈ f ⁻¹' B := h
        rw [hpre] at h'
        exact hyA h'
      refine ⟨hfy, ?_⟩
      change s (f y) ∈ U
      rw [hsf y hyA]
      exact hy
    · rintro ⟨hxB, hsx⟩
      exact ⟨s x, hsx, hfs x hxB⟩
  rw [himg]
  exact hs.continuousOn.isOpen_inter_preimage hBc.isOpen_compl hU

/-- The native morphism of a proper modification is open off a thin set. -/
theorem isOpenOffThin_nativeMorphism {X Y : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) :
    IsOpenOffThin (nativeMorphism hf.1).hom.left.base := by
  show IsOpenOffThin ((Homeomorph.Set.univ X).symm ∘ f ∘ (Homeomorph.Set.univ Y))
  exact ((IsOpenOffThin.of_isOpenMap (Homeomorph.Set.univ Y).isOpenMap).comp
    (Homeomorph.Set.univ Y).continuous (isOpenOffThin_of_isAnalyticModification hf)).comp
    (hf.1.continuous.comp (Homeomorph.Set.univ Y).continuous)
    (IsOpenOffThin.of_isOpenMap (Homeomorph.Set.univ X).symm.isOpenMap)

/-- The bad set of an isomorphism over its complement is closed. -/
theorem isClosed_of_isIsoOver {X Y : SourceReducedComplexSpace} {π : Y ⟶ X}
    {T : Set X.obj.left} (h : IsIsoOver π Tᶜ) : IsClosed T := by
  obtain ⟨V, j, _, _, hjp, hr⟩ := h
  rw [← isOpen_compl_iff, ← hr]
  exact hjp.base_open.isOpen_range

end Generic

/-! ### Towers of native ideal blowups -/

/-- `p : Z ⟶ X` is a finite tower of native blowups of finite-type ideals with dense unit
loci (`OriginalFiniteIdealBlowup`). -/
inductive IsNativeBlowupTower (X : SourceReducedComplexSpace) :
    (Z : SourceReducedComplexSpace) → (Z ⟶ X) → Prop
  | refl : IsNativeBlowupTower X X (𝟙 X)
  | step {Z : SourceReducedComplexSpace} (p : Z ⟶ X)
      (B : SheafOfModules.{0} (forgetRing Z.obj.left.toSheafedSpace.sheaf))
      (b : B ⟶ SheafOfModules.unit (forgetRing Z.obj.left.toSheafedSpace.sheaf))
      [B.IsFiniteType]
      (hDense : Dense {z : Z.obj.left |
        LinearMap.range (stalkInclusionLinearMap Z.obj.left.toSheafedSpace.sheaf B b z) = ⊤}) :
      IsNativeBlowupTower X Z p →
        IsNativeBlowupTower X (sourceObject B b hDense) (projectionMorphism B b hDense ≫ p)

section Lift

variable {n : ℕ}

/-- The nonunit locus of an ideal with dense unit locus has empty interior. -/
theorem interior_nonunitLocus_eq_empty {Z : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Z.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Z.obj.left.toSheafedSpace.sheaf))
    (hDense : Dense {z : Z.obj.left |
      LinearMap.range (stalkInclusionLinearMap Z.obj.left.toSheafedSpace.sheaf B b z) = ⊤}) :
    interior {z : Z.obj.left |
      LinearMap.range (stalkInclusionLinearMap Z.obj.left.toSheafedSpace.sheaf B b z) ≠ ⊤} = ∅ := by
  apply interior_eq_empty_iff_dense_compl.mpr
  convert hDense using 1
  ext z
  simp only [mem_compl_iff, mem_ofPred_eq, not_not]

/-- The model germ ideal of a native ideal with dense unit locus, pulled back along a map which
is open off a thin set, has a zero locus with empty interior. -/
theorem interior_zeroLocus_modelGermIdeal_eq_empty {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W] {Z : SourceReducedComplexSpace}
    (γ : wholeModel (n := n) W ⟶ Z) (hγ : IsOpenOffThin γ.hom.left.base)
    (B : SheafOfModules.{0} (forgetRing Z.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Z.obj.left.toSheafedSpace.sheaf))
    (hDense : Dense {z : Z.obj.left |
      LinearMap.range (stalkInclusionLinearMap Z.obj.left.toSheafedSpace.sheaf B b z) = ⊤}) :
    interior (modelGermIdeal B b γ.hom.left).zeroLocus = ∅ := by
  have h1 := hγ.interior_preimage_eq_empty (interior_nonunitLocus_eq_empty B b hDense)
  have hset : (modelGermIdeal B b γ.hom.left).zeroLocus =
      (Homeomorph.Set.univ W).symm ⁻¹' (γ.hom.left.base ⁻¹' {z : Z.obj.left |
        LinearMap.range (stalkInclusionLinearMap Z.obj.left.toSheafedSpace.sheaf B b z) ≠ ⊤}) :=
    (zeroLocus_modelGermIdeal B b γ.hom.left).trans rfl
  rw [hset, ← (Homeomorph.Set.univ W).symm.preimage_interior]
  exact eq_empty_of_forall_notMem fun x hx => (Set.ext_iff.mp h1 _).mp hx

/-- **Lifting through a tower.**  Let `W` be a compact complex manifold and `γ₀` a native
morphism from its whole model to `X` which is open off a thin set.  For every tower
`p : Z ⟶ X` of native ideal blowups there are a blowup sequence `σ : W' → W` and a native
lift `γ : W' ⟶ Z` of `γ₀ ∘ σ`, again open off a thin set. -/
theorem exists_lift_of_isNativeBlowupTower {X Z : SourceReducedComplexSpace} {p : Z ⟶ X}
    (hp : IsNativeBlowupTower X Z p) {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W] [CompactSpace W]
    (γ₀ : wholeModel (n := n) W ⟶ X) (hγ₀ : IsOpenOffThin γ₀.hom.left.base) :
    ∃ (W' : Type) (_ : TopologicalSpace W') (_ : ChartedSpace (ComplexModel n) W')
      (_ : IsComplexManifold n W') (σ : W' → W) (hσ : IsBlowupSequence n W W' σ)
      (γ : wholeModel (n := n) W' ⟶ Z),
      γ ≫ p = nativeMorphism hσ.contMDiff ≫ γ₀ ∧ IsOpenOffThin γ.hom.left.base := by
  induction hp with
  | refl =>
    refine ⟨W, inferInstance, inferInstance, inferInstance, id, IsBlowupSequence.refl, γ₀, ?_, hγ₀⟩
    have hid : nativeMorphism (IsBlowupSequence.refl (n := n) (X := W)).contMDiff =
        𝟙 (wholeModel (n := n) W) :=
      morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
    rw [Category.comp_id, hid, Category.id_comp]
  | @step Z p B b _ hDense _ ih =>
    obtain ⟨W', tW', cW', mW', σ, hσ, γ, hγp, hγo⟩ := ih
    let := tW'
    let := cW'
    let := mW'
    have : CompactSpace W' := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hσ).1
    let 𝔟 : GermIdeal n W' := modelGermIdeal B b γ.hom.left
    have h𝔟 : 𝔟.IsCoherent := isCoherent_modelGermIdeal B b γ.hom.left
    have hthin : interior 𝔟.zeroLocus = ∅ :=
      interior_zeroLocus_modelGermIdeal_eq_empty γ hγo B b hDense
    obtain ⟨W'', t'', c'', m'', σ', D, E, hadm, hpb, -, -, -, -⟩ :=
      exists_principalization_admissible h𝔟
        (PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty h𝔟 hthin)
    let := t''
    let := c''
    let := m''
    have hσ' : IsBlowupSequence n W' W'' σ' := hadm.isBlowupSequence
    have hinv : (GermIdeal.pullback (m := n) σ' 𝔟).IsInvertible := by
      rw [hpb]
      exact D.isInvertible
    obtain ⟨q, hq, huniq⟩ :=
      exists_locallyFreeData_of_pullback_isInvertible B b γ.hom.left hσ'.contMDiff hinv
    let q' : (nativePulledIdealModule (nativeMorphism hσ'.contMDiff ≫ γ).hom.left
      B b).LocalGeneratorsData.{0} := q
    let : q'.IsLocallyFreeData := hq
    let : ∀ i, Unique (q'.generators i).I := fun i => Classical.choice (huniq i)
    obtain ⟨L, hL, -⟩ := exists_unique_lift_of_locallyFreeData B b hDense
      (wholeModel (n := n) W'') (nativeMorphism hσ'.contMDiff ≫ γ) q'
    have hσσ' : IsBlowupSequence n W W'' (σ ∘ σ') := isBlowupSequence_comp hσ hσ'
    have hcomp : nativeMorphism hσσ'.contMDiff =
        nativeMorphism hσ'.contMDiff ≫ nativeMorphism hσ.contMDiff :=
      morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
    refine ⟨W'', t'', c'', m'', σ ∘ σ', hσσ', L, ?_, ?_⟩
    · calc
        L ≫ (projectionMorphism B b hDense ≫ p) = (L ≫ projectionMorphism B b hDense) ≫ p :=
          (Category.assoc _ _ _).symm
        _ = (nativeMorphism hσ'.contMDiff ≫ γ) ≫ p := by rw [hL]
        _ = nativeMorphism hσ'.contMDiff ≫ (γ ≫ p) := Category.assoc _ _ _
        _ = nativeMorphism hσ'.contMDiff ≫ (nativeMorphism hσ.contMDiff ≫ γ₀) := by rw [hγp]
        _ = (nativeMorphism hσ'.contMDiff ≫ nativeMorphism hσ.contMDiff) ≫ γ₀ :=
          (Category.assoc _ _ _).symm
        _ = nativeMorphism hσσ'.contMDiff ≫ γ₀ := by rw [hcomp]
    · obtain ⟨-, T, -, hTi, -, hiso⟩ := projection_isProperBimeromorphic B b hDense
      have hTc : IsClosed T := isClosed_of_isIsoOver hiso
      have hqo : IsOpenOffThin (nativeMorphism hσ'.contMDiff ≫ γ).hom.left.base := by
        show IsOpenOffThin (γ.hom.left.base ∘ (nativeMorphism hσ'.contMDiff).hom.left.base)
        exact (isOpenOffThin_nativeMorphism (isAnalyticModification_of_isBlowupSequence hσ')).comp
          (nativeMorphism hσ'.contMDiff).hom.left.base.hom.continuous hγo
      exact IsOpenOffThin.of_comp_injOn
        (projectionMorphism B b hDense).hom.left.base.hom.continuous hTc hTi
        (injOn_of_isIsoOver hiso) hqo
        (nativeMorphism hσ'.contMDiff ≫ γ).hom.left.base.hom.continuous
        (fun a => congrArg (fun H : wholeModel (n := n) W'' ⟶ Z => H.hom.left.base a) hL)

end Lift

section Domination

variable {n : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Native tower domination gives stable domination by blowup sequences.**  Let `X` be a
compact complex manifold, `f : Y → X` holomorphic and `p : Z ⟶ X` a tower of native ideal
blowups of the whole model of `X` with a native morphism `β : Z ⟶ Y` over `X`.  Then `f`
has stable blowup domination. -/
theorem hasStableBlowupDomination_of_isNativeBlowupTower [CompactSpace X] {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {Z : SourceReducedComplexSpace} {p : Z ⟶ wholeModel (n := n) X}
    (hp : IsNativeBlowupTower (wholeModel (n := n) X) Z p)
    (β : Z ⟶ wholeModel (n := n) Y) (hβ : β ≫ nativeMorphism hf = p) :
    HasStableBlowupDomination n f := by
  intro V _ _ _ c hc
  have : CompactSpace V := AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc
  obtain ⟨W, tW, cW, mW, σ, hσ, γ, hγp, -⟩ :=
    exists_lift_of_isNativeBlowupTower hp (nativeMorphism hc.1) (isOpenOffThin_nativeMorphism hc)
  let := tW
  let := cW
  let := mW
  refine ⟨W, tW, cW, mW, σ, nativePointMap (γ ≫ β), hσ, nativePointMap_contMDiff _, ?_⟩
  funext t
  have hG : (γ ≫ β) ≫ nativeMorphism hf = nativeMorphism hσ.contMDiff ≫ nativeMorphism hc.1 := by
    rw [Category.assoc, hβ, hγp]
  exact congrArg (fun H : wholeModel (n := n) W ⟶ wholeModel (n := n) X =>
    (H.hom.left.base ⟨t, mem_univ t⟩).val) hG

/-- Native tower domination gives domination by a blowup sequence. -/
theorem hasBlowupDomination_of_isNativeBlowupTower [CompactSpace X] {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {Z : SourceReducedComplexSpace} {p : Z ⟶ wholeModel (n := n) X}
    (hp : IsNativeBlowupTower (wholeModel (n := n) X) Z p)
    (β : Z ⟶ wholeModel (n := n) Y) (hβ : β ≫ nativeMorphism hf = p) :
    HasBlowupDomination n f :=
  (hasStableBlowupDomination_of_isNativeBlowupTower hf hp β hβ).hasBlowupDomination

/-- **A single native blowup over `Y` gives a dominating ideal.**  If the native blowup of a
finite-type ideal `(B, b)` with dense unit locus of the whole model of `X` factors through
`f : Y → X`, the model germ ideal of `(B, b)` dominates `f` (`IsDominatingIdeal`). -/
theorem isDominatingIdeal_modelGermIdeal_of_native_domination {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (B : SheafOfModules.{0} (forgetRing (wholeModel (n := n) X).obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit
      (forgetRing (wholeModel (n := n) X).obj.left.toSheafedSpace.sheaf))
    [B.IsFiniteType]
    (hDense : Dense {x : (wholeModel (n := n) X).obj.left |
      LinearMap.range (stalkInclusionLinearMap
        (wholeModel (n := n) X).obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (β : sourceObject B b hDense ⟶ wholeModel (n := n) Y)
    (hβ : β ≫ nativeMorphism hf = projectionMorphism B b hDense) :
    IsDominatingIdeal n f (modelGermIdeal B b (𝟙 (wholeModel (n := n) X).obj.left)) := by
  have hzero : interior (modelGermIdeal B b (𝟙 (wholeModel (n := n) X).obj.left)).zeroLocus =
      ∅ := by
    have hset : (modelGermIdeal B b (𝟙 (wholeModel (n := n) X).obj.left)).zeroLocus =
        (Homeomorph.Set.univ X).symm ⁻¹' {z : (wholeModel (n := n) X).obj.left |
          LinearMap.range (stalkInclusionLinearMap
            (wholeModel (n := n) X).obj.left.toSheafedSpace.sheaf B b z) ≠ ⊤} :=
      (zeroLocus_modelGermIdeal B b (𝟙 (wholeModel (n := n) X).obj.left)).trans rfl
    rw [hset, ← (Homeomorph.Set.univ X).symm.preimage_interior]
    exact eq_empty_of_forall_notMem fun x hx =>
      (Set.ext_iff.mp (interior_nonunitLocus_eq_empty B b hDense) _).mp hx
  refine ⟨isCoherent_modelGermIdeal B b _, hzero, ?_⟩
  intro m T _ _ _ h hh hinv
  have hmap : ∀ x : (univ : Set T),
      Ideal.map ((HironakaActualAnalyticSubspace.actualSubspaceInclusion (n := m)
        (univ : Set T)).stalkMap x).hom
        (HironakaSmoothCentreRealDomainActualSheafStalk.actualWholeSheafStalkIdeal
          (GermIdeal.pullback (m := m) h
            (modelGermIdeal B b (𝟙 (wholeModel (n := n) X).obj.left))) x.val) =
        nativePulledIdealStalkIdeal (nativeMorphism hh).hom.left B b x := fun x =>
    (map_wholeIdeal_pullback_modelGermIdeal B b (𝟙 (wholeModel (n := n) X).obj.left) hh x).trans
      (congrArg (fun G : HironakaActualAnalyticSubspace.actualSubspaceLocallyRingedSpace (n := m)
          (univ : Set T) ⟶ (wholeModel (n := n) X).obj.left =>
        nativePulledIdealStalkIdeal G B b x) (Category.comp_id _))
  obtain ⟨q, hq, huniq⟩ := exists_locallyFreeData_of_isInvertible B b
    (nativeMorphism hh).hom.left _ hinv hmap
  exact HironakaG10ChowNativeDominationLift.exists_holomorphic_factor_of_native_domination
    hf B b hDense β hβ hh q hq huniq

end Domination

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowTowerDomination
