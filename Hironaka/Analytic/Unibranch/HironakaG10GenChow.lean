import Hironaka.Analytic.Unibranch.HironakaG10GenStatement
import Hironaka.Analytic.Unibranch.HironakaG10GenBlowupBridge
import Hironaka.Analytic.Unibranch.HironakaG10GenDisjointModification
import Hironaka.Analytic.Unibranch.HironakaG10GenRiemannExtension
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatOpen
import Hironaka.Analytic.Unibranch.OriginalSmoothComponentPairing

/-!
# Hironaka's Chow lemma for compact reduced complex spaces

Goal G10 general (`chow:general`): `HironakaChowLemmaGeneral` follows from Hironaka's flattening
theorem (`HironakaFlattening`) and resolution of singularities of compact reduced complex spaces by
blowups with smooth centres in the singular locus (`CompactSingularCentreResolution`, goal G11);
both are hypotheses, not axioms (`hironakaChowLemmaGeneral_of_flattening_of_resolution`).  In fact
only the source's `thm:res` is needed besides flattening — a finite composition of smooth-centre
blowups with smooth source, centres anywhere (`HasModificationResolution`,
`isDominatedByModification_of_hasModificationResolution`) — so smooth compact bases need flattening
alone (`isDominatedByModification_of_isSmooth`), and the empty base nothing.

Proof (blueprint `hironaka-g10-gen-chow-general.tex`).  Let `f : Y ⟶ X` be proper bimeromorphic,
`X` compact, an isomorphism over the complement of a thin analytic set `T`.

1. Resolve `X`: `τ : X₁ ⟶ X` a finite composition of smooth-centre blowups with `X₁` smooth and
   compact; `τ` is open off a thin set (each step is proper bimeromorphic).
2. Flatten `f`: a tower `σ : X' ⟶ X` of native ideal blowups and a flat strict transform
   `(Y', p, q)`; `p` is open (flat maps are open), hence a homeomorphism.
3. For each connected component `X₁ᶜ` of `X₁` (a compact complex manifold `M` of its own
   dimension), lift `M` through the tower after a blowup sequence `ρ : W → M`
   (`exists_lift_of_isNativeBlowupTower`: principalization of the pulled-back centres) to
   `γ : W ⟶ X'`; the map `q ∘ p⁻¹ ∘ γ : W → Y` is continuous and, off the preimage of `T`, equal to
   `f⁻¹ ∘ τ ∘ ρ`; by Riemann extension into the reduced space `Y` it is a morphism `g`
   (`exists_piece`).  The blowup sequence `ρ` is a native finite modification.
4. The modifications of the finitely many components assemble to one modification
   `ρ' : X₂ ⟶ X₁` (`HironakaG10GenDisjointModification`), the morphisms `g` glue to `G : X₂ ⟶ Y`,
   and `G ≫ f = ρ' ≫ τ` with `ρ' ≫ τ` a finite composition of smooth-centre blowups.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GenChow

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaChowLemma HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification OriginalNativeModification
  OriginalSmoothSourceAnalytic HironakaG10ChowTowerDomination HironakaG10ChowFlatteningReduction
  HironakaG10ChowFlatteningOpenReduction HironakaG10ChowFlatOpen HironakaG10ChowNativeIsoCriterion
  HironakaG11SingularCentreModification HironakaG10GenStatement HironakaG10GenDisjointModification

noncomputable section

/-- A morphism which is an isomorphism over `U`, with thin preimage of the complement of `U`, is
open off a thin set. -/
theorem isOpenOffThin_of_isIsoOver {X Y : SourceReducedComplexSpace} {F : Y ⟶ X}
    {U : Set X.obj.left} (hF : IsIsoOver F U)
    (hthin : interior (F.hom.left.base ⁻¹' Uᶜ) = ∅) : IsOpenOffThin F.hom.left.base := by
  have hU : IsOpen U := hF.isOpen
  refine ⟨F.hom.left.base ⁻¹' Uᶜ, hU.isClosed_compl.preimage F.hom.left.base.hom.continuous,
    hthin, ?_⟩
  intro O hO hOE
  obtain ⟨V, j, hj, hjr, hjF, -⟩ := hF
  have hOj : O ⊆ range j.base := by
    rw [hjr]
    intro y hy
    by_contra h
    exact hOE hy h
  have himg : F.hom.left.base '' O = (j ≫ F.hom.left).base '' (j.base ⁻¹' O) := by
    rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, image_comp,
      image_preimage_eq_of_subset hOj]
  rw [himg]
  exact hjF.base_open.isOpenMap _ (hO.preimage j.base.hom.continuous)

/-- A finite composition of blowups with centres in the singular locus is open off a thin set. -/
theorem isOpenOffThin_of_isSingularCentreModification {X X₁ : SourceReducedComplexSpace}
    {τ : X₁ ⟶ X} (hτ : IsSingularCentreModification τ) : IsOpenOffThin τ.hom.left.base :=
  isOpenOffThin_of_isIsoOver hτ.isIsoOver_intrinsicRegularLocus
    hτ.interior_preimage_intrinsicSingularLocus

/-- **The Chow lemma on one compact manifold piece.**  Let `f : Y ⟶ X` be proper bimeromorphic,
`σ : X' ⟶ X` a tower of native blowups with a strict transform `(Y', p, q)` of `f` whose point map
`p` is a homeomorphism, and `γ₀ : wholeModel M ⟶ X` a morphism from a compact complex manifold,
open off a thin set.  Then a finite composition of smooth-centre blowups `ρ` of `wholeModel M`
carries a morphism `g` to `Y` with `g ≫ f = ρ ≫ γ₀`. -/
theorem exists_piece {X Y X' Y' : SourceReducedComplexSpace} {f : Y ⟶ X}
    (hf : IsProperBimeromorphic f) {σ : X' ⟶ X} (hσ : IsNativeBlowupTower X X' σ)
    {p : Y' ⟶ X'} {q : Y' ⟶ Y} (hcomm : q ≫ f = p ≫ σ) (hhom : IsHomeomorph p.hom.left.base)
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] (γ₀ : wholeModel (n := n) M ⟶ X)
    (hγ₀ : IsOpenOffThin γ₀.hom.left.base) :
    ∃ (A : SourceReducedComplexSpace) (ρ : A ⟶ wholeModel (n := n) M) (g : A ⟶ Y),
      IsModification ρ ∧ g ≫ f = ρ ≫ γ₀ := by
  obtain ⟨-, T, hTa, hTi, -, hiso⟩ := hf
  obtain ⟨W, tW, cW, mW, ρ, hρ, γ, hγ, -⟩ := exists_lift_of_isNativeBlowupTower hσ γ₀ hγ₀
  let := tW
  let := cW
  let := mW
  let ep := hhom.homeomorph
  let K₀ : wholeModel (n := n) W ⟶ X := nativeMorphism (n := n) (m := n) hρ.contMDiff ≫ γ₀
  let φ : W → Y.obj.left := fun w => q.hom.left.base (ep.symm (γ.hom.left.base ⟨w, mem_univ w⟩))
  have hφc : Continuous φ :=
    q.hom.left.base.hom.continuous.comp (ep.symm.continuous.comp
      (γ.hom.left.base.hom.continuous.comp (continuous_id.subtype_mk (fun w => mem_univ w))))
  have hfφ : ∀ w, f.hom.left.base (φ w) = pointMap K₀ w := by
    intro w
    have h1 : p.hom.left.base (ep.symm (γ.hom.left.base ⟨w, mem_univ w⟩)) =
        γ.hom.left.base ⟨w, mem_univ w⟩ := ep.apply_symm_apply _
    have h2 := congrArg (fun H : Y' ⟶ X =>
      H.hom.left.base (ep.symm (γ.hom.left.base ⟨w, mem_univ w⟩))) hcomm
    have h3 := congrArg (fun H : wholeModel (n := n) W ⟶ X => H.hom.left.base ⟨w, mem_univ w⟩) hγ
    simp only [comp_base_apply] at h2 h3
    change f.hom.left.base (q.hom.left.base _) = K₀.hom.left.base ⟨w, mem_univ w⟩
    rw [h2, h1]
    exact h3
  -- the exceptional set
  let A : Set W := pointMap K₀ ⁻¹' T
  have hAa : IsComplexAnalyticSubset (n := n) A := isComplexAnalyticSubset_preimage K₀ hTa
  have hAc : IsClosed A := hTa.isClosed.preimage (continuous_pointMap K₀)
  have hK₀o : IsOpenOffThin (pointMap K₀) := by
    show IsOpenOffThin (γ₀.hom.left.base ∘
      (nativeMorphism (n := n) (m := n) hρ.contMDiff).hom.left.base ∘
        (Homeomorph.Set.univ W).symm)
    exact ((IsOpenOffThin.of_isOpenMap (Homeomorph.Set.univ W).symm.isOpenMap).comp
      (Homeomorph.Set.univ W).symm.continuous
      (isOpenOffThin_nativeMorphism (isAnalyticModification_of_isBlowupSequence hρ))).comp
      ((nativeMorphism (n := n) (m := n) hρ.contMDiff).hom.left.base.hom.continuous.comp
        (Homeomorph.Set.univ W).symm.continuous) hγ₀
  have hAi : interior A = ∅ := hK₀o.interior_preimage_eq_empty hTi
  -- off the exceptional set the map is native
  have hloc : ∀ w, w ∉ A → ∃ (O : Opens W) (_ : w ∈ O) (F : wholeModel (n := n) O ⟶ Y),
      ∀ u : O, pointMap F u = φ u := by
    intro w hw
    let O : Opens W := ⟨Aᶜ, hAc.isOpen_compl⟩
    let K : wholeModel (n := n) O ⟶ X := HironakaG10GenRiemannExtension.openInclusion O ≫ K₀
    have hK : range K.hom.left.base ⊆ Tᶜ := by
      rintro _ ⟨u, rfl⟩
      exact u.val.2
    obtain ⟨K', hK', -, -⟩ := IsIsoOver.exists_lift hiso K hK
    refine ⟨O, hw, K', fun u => ?_⟩
    have hK'u : f.hom.left.base (pointMap K' u) = pointMap K₀ u := by
      exact congrArg (fun H : wholeModel (n := n) O ⟶ X => H.hom.left.base ⟨u, mem_univ u⟩) hK'
    apply injOn_of_isIsoOver hiso
    · change f.hom.left.base (pointMap K' u) ∈ Tᶜ
      rw [hK'u]
      exact u.2
    · change f.hom.left.base (φ u) ∈ Tᶜ
      rw [hfφ]
      exact u.2
    · rw [hK'u, hfφ]
  obtain ⟨g, hg⟩ :=
    HironakaG10GenRiemannExtension.exists_hom_of_continuous_of_thin φ hφc hAa hAc hAi hloc
  refine ⟨wholeModel (n := n) W, nativeMorphism (n := n) (m := n) hρ.contMDiff, g,
    HironakaG10GenBlowupBridge.isModification_nativeMorphism hρ, ?_⟩
  apply morphism_eq_of_pointwise_eq
  intro a
  rw [comp_base_apply]
  have ha : g.hom.left.base a = φ a.val := hg a.val
  rw [ha, hfφ]
  rfl

/-! ### Components of a compact smooth space -/

section Components

open OriginalSmoothComponents OriginalSmoothComponentPairing

variable {X₁ : SourceReducedComplexSpace} [CompactSpace X₁.obj.left]

/-- The whole manifold model of a connected component of a compact smooth space. -/
def compModel (h : X₁.IsSmooth) (c : ConnectedComponents X₁.obj.left) :
    SourceReducedComplexSpace :=
  letI := componentChartedSpace h c
  letI := componentIsComplexManifold h c
  wholeModel (n := componentDimension h c) (componentObject h c).obj.left

/-- The embedding of the model of a component. -/
def compEmb (h : X₁.IsSmooth) (c : ConnectedComponents X₁.obj.left) : compModel h c ⟶ X₁ :=
  (componentNativeIso h c).hom ≫ componentInclusion h c

theorem compEmb_isOpenImmersion (h : X₁.IsSmooth) (c : ConnectedComponents X₁.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (compEmb h c).hom.left := by
  have : IsIso (componentNativeIso h c).hom.hom.left :=
    (Functor.mapIso (ObjectProperty.ι _ ⋙ Over.forget _) (componentNativeIso h c)).isIso_hom
  change LocallyRingedSpace.IsOpenImmersion
    ((componentNativeIso h c).hom.hom.left ≫ (componentInclusion h c).hom.left)
  infer_instance

theorem compEmb_range (h : X₁.IsSmooth) (c : ConnectedComponents X₁.obj.left) :
    range (compEmb h c).hom.left.base = componentSet c := by
  rw [← componentInclusion_range h c]
  apply subset_antisymm
  · rintro _ ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨⟨y, mem_univ y⟩, ?_⟩
    change (componentInclusion h c).hom.left.base
      ((componentNativeIso h c).hom.hom.left.base ⟨y, mem_univ y⟩) = _
    exact congrArg _ (componentNativeIso_point h c ⟨y, mem_univ y⟩)

end Components

/-! ### Resolutions by finite modifications -/

/-- A proper bimeromorphic morphism is open off a thin set. -/
theorem isOpenOffThin_of_isProperBimeromorphic {X Y : SourceReducedComplexSpace} {F : Y ⟶ X}
    (hF : IsProperBimeromorphic F) : IsOpenOffThin F.hom.left.base := by
  obtain ⟨-, Z, -, -, hZpre, hiso⟩ := hF
  exact isOpenOffThin_of_isIsoOver hiso (by rw [compl_compl]; exact hZpre)

/-- A finite composition of smooth-centre blowups is open off a thin set. -/
theorem isOpenOffThin_of_isModification {X Y : SourceReducedComplexSpace} {τ : Y ⟶ X}
    (hτ : IsModification τ) : IsOpenOffThin τ.hom.left.base := by
  induction hτ with
  | id =>
    refine IsOpenOffThin.of_isOpenMap (fun U hU => ?_)
    convert hU
    exact image_id U
  | cons f g hf _ ih =>
    show IsOpenOffThin (g.hom.left.base ∘ f.hom.left.base)
    exact (isOpenOffThin_of_isProperBimeromorphic hf.isProperBimeromorphic).comp
      f.hom.left.base.hom.continuous ih

/-- The book's resolution theorem `thm:res` for one space: a finite composition of blowups with
smooth nowhere dense centres whose source is smooth. -/
def HasModificationResolution (X : SourceReducedComplexSpace) : Prop :=
  ∃ (X₁ : SourceReducedComplexSpace) (τ : X₁ ⟶ X), IsModification τ ∧ X₁.IsSmooth

/-- The G11 endpoint gives the book's resolution. -/
theorem hasModificationResolution_of_hasSingularCentreResolution {X : SourceReducedComplexSpace}
    (h : HasSingularCentreResolution X) : HasModificationResolution X := by
  obtain ⟨X₁, τ, hτ, hX₁⟩ := h
  exact ⟨X₁, τ, hτ.toIsModification, hX₁⟩

/-- The book's resolution theorem `thm:res` for all compact reduced complex spaces: weaker than goal
G11 (`CompactSingularCentreResolution`), as the centres need not lie in the singular locus. -/
def CompactModificationResolution : Prop :=
  ∀ X : SourceReducedComplexSpace, CompactSpace X.obj.left → HasModificationResolution X

theorem compactModificationResolution_of_compactSingularCentreResolution
    (H₁ : CompactSingularCentreResolution) : CompactModificationResolution :=
  fun X hX => hasModificationResolution_of_hasSingularCentreResolution (H₁ X hX)

/-- **The Chow lemma over a base with a resolution.**  If the compact reduced complex space `X`
has a resolution by finitely many blowups with smooth centres (`thm:res` for `X`), then, given
Hironaka's flattening theorem, every proper bimeromorphic morphism to `X` is dominated by a finite
composition of smooth-centre blowups. -/
theorem isDominatedByModification_of_hasModificationResolution (H₀ : HironakaFlattening)
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (hX : CompactSpace X.obj.left)
    (hf : IsProperBimeromorphic f) (hres : HasModificationResolution X) :
    IsDominatedByModification f := by
  obtain ⟨X₁, τ, hτ, hX₁⟩ := hres
  have hX₁c : CompactSpace X₁.obj.left := hτ.source_compact
  obtain ⟨X', σ, E, hσ, hEc, hEi, hσE, Y', p, q, hst, hflat⟩ := H₀ X Y f hX hf.1
  have hhom : IsHomeomorph p.hom.left.base := by
    obtain ⟨-, T, -, hTi, -, hiso⟩ := hf
    exact isHomeomorph_of_isStrictTransform_of_isOpenMap hst hEc hEi hσE hTi hiso
      (flatMorphismsAreOpen _ _ p hflat)
  have hτo := isOpenOffThin_of_isModification hτ
  have : Finite (ConnectedComponents X₁.obj.left) :=
    OriginalSmoothComponents.finite_connectedComponents hX₁
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (ConnectedComponents X₁.obj.left)
  have hpiece : ∀ i : Fin N, ∃ (A : SourceReducedComplexSpace)
      (ρ : A ⟶ compModel hX₁ (e.symm i)) (g : A ⟶ Y),
      IsModification ρ ∧ g ≫ f = ρ ≫ compEmb hX₁ (e.symm i) ≫ τ := by
    intro i
    let := OriginalSmoothComponentPairing.componentChartedSpace hX₁ (e.symm i)
    let := OriginalSmoothComponentPairing.componentIsComplexManifold hX₁ (e.symm i)
    have := OriginalSmoothComponents.compactSpace_componentObject hX₁ (e.symm i)
    have hγ₀ : IsOpenOffThin (compEmb hX₁ (e.symm i) ≫ τ).hom.left.base := by
      show IsOpenOffThin (τ.hom.left.base ∘ (compEmb hX₁ (e.symm i)).hom.left.base)
      exact (IsOpenOffThin.of_isOpenMap
        (compEmb_isOpenImmersion hX₁ (e.symm i)).base_open.isOpenMap).comp
        (compEmb hX₁ (e.symm i)).hom.left.base.hom.continuous hτo
    exact exists_piece hf hσ hst.comm hhom
      (M := (OriginalSmoothComponents.componentObject hX₁ (e.symm i)).obj.left)
      (compEmb hX₁ (e.symm i) ≫ τ) hγ₀
  choose A ρ g hρ hg using hpiece
  have hdisj : Pairwise (fun i k : Fin N => Disjoint (range (compEmb hX₁ (e.symm i)).hom.left.base)
      (range (compEmb hX₁ (e.symm k)).hom.left.base)) := by
    intro i k hik
    rw [compEmb_range, compEmb_range]
    exact OriginalSmoothComponents.componentSet_pairwise_disjoint
      (fun h => hik (e.symm.injective h))
  obtain ⟨X₂, ρ', L, hρ', hL, hLc, hcov⟩ := exists_isModification_of_cover
    (fun i => compEmb hX₁ (e.symm i)) (fun i => compEmb_isOpenImmersion hX₁ (e.symm i))
    (fun i => by
      rw [compEmb_range]
      exact (OriginalSmoothComponents.component_isClopen hX₁ (e.symm i)).1)
    hdisj
    (fun z => ⟨e (ConnectedComponents.mk z), by
      rw [compEmb_range, Equiv.symm_apply_apply]
      rfl⟩)
    ρ hρ
  have hcompat : ∀ i k (u : (A i).obj.left) (v : (A k).obj.left),
      (L i).hom.left.base u = (L k).hom.left.base v →
        (g i).hom.left.base u = (g k).hom.left.base v := by
    intro i k u v huv
    by_cases hik : i = k
    · subst hik
      rw [(hL i).base_open.injective huv]
    · exfalso
      have h1 : ρ'.hom.left.base ((L i).hom.left.base u) ∈
          range (compEmb hX₁ (e.symm i)).hom.left.base := by
        rw [← comp_base_apply, hLc i]
        exact ⟨_, rfl⟩
      have h2 : ρ'.hom.left.base ((L k).hom.left.base v) ∈
          range (compEmb hX₁ (e.symm k)).hom.left.base := by
        rw [← comp_base_apply, hLc k]
        exact ⟨_, rfl⟩
      rw [huv] at h1
      exact Set.disjoint_left.mp (hdisj hik) h1 h2
  obtain ⟨G, hG⟩ := HironakaG10GenGluing.exists_hom_of_cover L hL hcov g hcompat
  refine isDominatedByModification_of_comp G hτ hρ' ?_
  apply morphism_eq_of_pointwise_eq
  intro x
  obtain ⟨i, u, rfl⟩ := hcov x
  have h1 := congrArg (fun H : A i ⟶ Y => f.hom.left.base (H.hom.left.base u)) (hG i)
  have h2 := congrArg (fun H : A i ⟶ X => H.hom.left.base u) (hg i)
  have h3 := congrArg (fun H : A i ⟶ X₁ => τ.hom.left.base (H.hom.left.base u)) (hLc i)
  simp only [comp_base_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3]

/-- **The Chow lemma over a base with a singular-centre resolution** (the conclusion of goal G11
for `X`). -/
theorem isDominatedByModification_of_hasSingularCentreResolution (H₀ : HironakaFlattening)
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (hX : CompactSpace X.obj.left)
    (hf : IsProperBimeromorphic f) (hres : HasSingularCentreResolution X) :
    IsDominatedByModification f :=
  isDominatedByModification_of_hasModificationResolution H₀ f hX hf
    (hasModificationResolution_of_hasSingularCentreResolution hres)

/-- **Hironaka's Chow lemma from flattening and the book's resolution theorem** `thm:res`. -/
theorem hironakaChowLemmaGeneral_of_flattening_of_modificationResolution
    (H₀ : HironakaFlattening) (H₁ : CompactModificationResolution) : HironakaChowLemmaGeneral :=
  fun X _ f hX hf => isDominatedByModification_of_hasModificationResolution H₀ f hX hf (H₁ X hX)

/-- **Hironaka's Chow lemma for compact reduced complex spaces** (`chow:general`), from Hironaka's
flattening theorem and resolution of singularities by blowups with smooth centres (goal G11),
both taken as hypotheses. -/
theorem hironakaChowLemmaGeneral_of_flattening_of_resolution (H₀ : HironakaFlattening)
    (H₁ : CompactSingularCentreResolution) : HironakaChowLemmaGeneral :=
  hironakaChowLemmaGeneral_of_flattening_of_modificationResolution H₀
    (compactModificationResolution_of_compactSingularCentreResolution H₁)

/-- **Smooth compact bases need only flattening.**  Every proper bimeromorphic morphism (from an
arbitrary, possibly singular, reduced complex space) to a compact SMOOTH reduced complex space,
whose connected components may have different dimensions, is dominated by a finite composition of
smooth-centre blowups, given Hironaka's flattening theorem alone. -/
theorem isDominatedByModification_of_isSmooth (H₀ : HironakaFlattening)
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (hX : CompactSpace X.obj.left)
    (hXs : X.IsSmooth) (hf : IsProperBimeromorphic f) : IsDominatedByModification f :=
  isDominatedByModification_of_hasSingularCentreResolution H₀ f hX hf
    (hasSingularCentreResolution_of_isSmooth hXs)

/-- **The empty base, unconditionally**: a morphism to an empty space is dominated by the
identity (the source is empty too, and a morphism out of the empty space exists). -/
theorem isDominatedByModification_of_isEmpty {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hX : IsEmpty X.obj.left) : IsDominatedByModification f := by
  obtain ⟨G, -⟩ := HironakaG10GenGluing.exists_hom_of_local' (A := X) (B := Y)
    (fun x => IsEmpty.elim hX x) (fun x => IsEmpty.elim hX x)
  exact isDominatedByModification_of_section G
    (morphism_eq_of_pointwise_eq _ _ (fun x => IsEmpty.elim hX x))

end

end Hironaka.Analytic.Unibranch.HironakaG10GenChow
