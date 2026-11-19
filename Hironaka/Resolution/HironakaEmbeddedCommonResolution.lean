import Hironaka.Resolution.HironakaEmbeddedCommonComponent
import Hironaka.Resolution.EmbeddedResolution
import Hironaka.Analytic.SubmanifoldCodRestrict
import Hironaka.Analytic.AnalyticModelDomination

/-!
# Compact smooth common resolutions over an embedded singular image

Ordinary original open-isomorphism data construct a compact native smooth
common model and BOTH genuine analytic-modification projections. The maps to
the ambient target may have different source and target dimensions, and no
smoothness is assumed on their common image.

Blueprint: `hironaka-embedded-common.tex`. Abstract complex-space morphism
descent and smooth-centre factorization are separate obligations.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
  Hironaka.ProductComplexManifold

universe u

namespace Hironaka.HironakaEmbeddedCommon

open Hironaka.BlowupSequences Hironaka.NonKahlerLocus ProductComplexManifold
  AnalyticModificationLocalDiscrepancy

noncomputable section

section Inverses

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The already accepted local-inverse argument of
`Hironaka.Okounkov.contMDiffOn_invOver_of_isIsomorphismOver`, reproduced privately
here to keep the native TN dependency direction. It receives no new
source-theorem credit. -/
private theorem contMDiffOn_invOver [Nonempty Y] {f : Y → X} {O : Set X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hO : IsOpen O) (hiso : IsIsomorphismOver n f O) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (ModificationMassInvariance.invOver f O) O := by
  intro x hx
  obtain ⟨hyO, hyx⟩ := ModificationMassInvariance.invOver_mem hiso hx
  have hy : ModificationMassInvariance.invOver f O x ∉ exceptionalLocus n f :=
    fun h => disjoint_left.mp hiso.2 hyO h
  obtain ⟨U, s, hU, hxU, _, hfs, hs, _⟩ :=
    HolomorphicLocalInverse.exists_localInverse hf hy
  rw [hyx] at hxU
  have heq : s =ᶠ[𝓝 x] ModificationMassInvariance.invOver f O := by
    filter_upwards [hU.mem_nhds hxU, hO.mem_nhds hx] with y hyU hyO
    have hsy : s y ∈ f ⁻¹' O := by
      change f (s y) ∈ O
      rwa [hfs y hyU]
    calc
      s y = ModificationMassInvariance.invOver f O (f (s y)) :=
        (ModificationMassInvariance.invOver_apply hiso hsy).symm
      _ = ModificationMassInvariance.invOver f O y := by rw [hfs y hyU]
  exact ((hs x hxU).congr_of_eventuallyEq heq.symm).contMDiffWithinAt

private theorem isAnalyticModification_of_open_inverse [Nonempty X] [ConnectedSpace Y]
    {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hproper : IsProperMap f) {D : Set X}
    (hDa : IsComplexAnalyticSubset (n := n) D) (hDi : interior D = ∅)
    (s : (⟨Dᶜ, hDa.isClosed.isOpen_compl⟩ : Opens X) → Y)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s)
    (hright : ∀ x, f (s x) = x.val)
    (hleft : ∀ y (hy : f y ∉ D), s ⟨f y, hy⟩ = y) :
    IsAnalyticModification (n := n) f := by
  let O : Opens X := ⟨Dᶜ, hDa.isClosed.isOpen_compl⟩
  have hsubrange : Dᶜ ⊆ range f := fun x hx => ⟨s ⟨x, hx⟩, hright ⟨x, hx⟩⟩
  have hdense : Dense (range f) :=
    (interior_eq_empty_iff_dense_compl.mp hDi).mono hsubrange
  have hrange : range f = univ :=
    hproper.isClosed_range.closure_eq.symm.trans hdense.closure_eq
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x ∈ range f := by rw [hrange]; exact mem_univ x
    exact hx
  let t : X → Y := fun x => Classical.choose (hsurj x)
  have ht (x : X) : f (t x) = x := Classical.choose_spec (hsurj x)
  have heq : (fun x : O => t x.val) = s := by
    funext x
    have hnot : f (t x.val) ∉ D := by rw [ht]; exact x.property
    calc
      t x.val = s ⟨f (t x.val), hnot⟩ := (hleft _ hnot).symm
      _ = s x := congrArg s (Subtype.ext (ht x.val))
  have htsmooth : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ t Dᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : O => t x.val) := heq.symm ▸ hs
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest ⟨x, hx⟩)).contMDiffWithinAt
  let A : Set Y := f ⁻¹' D
  have hAc : IsClosed A := hDa.isClosed.preimage hf.continuous
  have hAa : IsComplexAnalyticSubset (n := n) A :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hDa
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hDi).nonempty
  have hsx : s ⟨x, hx⟩ ∉ A := by
    change f (s ⟨x, hx⟩) ∉ D
    rwa [hright]
  have hAne : A ≠ univ := fun h => hsx (h.symm ▸ mem_univ _)
  have hAi : interior A = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    exact fun h => hAne (hAa.eq_univ_of_interior_nonempty h)
  refine ⟨hf, hproper, A, D, t, hAc, hAa, hAi, hDa.isClosed, hDa, hDi,
    rfl, htsmooth, (fun x _ => ht x), ?_⟩
  intro y hy
  exact (congrFun heq (⟨f y, hy⟩ : O)).trans (hleft y hy)

end Inverses

variable {m n : ℕ} {M Y₀ Y₁ : Type u}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [CompactSpace Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [CompactSpace Y₁] [ConnectedSpace Y₁]
  {c₀ : Y₀ → M} {c₁ : Y₁ → M} {B : Set M}

/-- The two original maps with a common open-isomorphism locus internally
produce a compact connected smooth common model with both full modification
maps. No common component, resolution or inverse-lift certificate is supplied. -/
theorem exists_compact_smooth_common_model
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₁)
    (hBa : IsComplexAnalyticSubset (n := m) B)
    (hthin₀ : interior (c₀ ⁻¹' B) = ∅) (hthin₁ : interior (c₁ ⁻¹' B) = ∅)
    (e : goodOpen c₁ hc₁ B hBa.isClosed ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBa.isClosed)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ)) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (g₀ : Z → Y₀) (g₁ : Z → Y₁),
      IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
      c₀ ∘ g₀ = c₁ ∘ g₁ := by
  classical
  obtain ⟨V, hVdim, _, hVclosure, hVF, hGreg⟩ :=
    exists_mainComponent_of_open_transition hc₀ hc₁ hBa hthin₁ e he hinj
  obtain ⟨Xt, instTop, instChart, instMfd, μ, hμ, hiso, hW⟩ :=
    EmbeddedResolution.exists_embeddedResolution V
  let W : Set Xt := strictTransform (n + n) μ V.carrier
  have hWn : IsClosedConnectedSubmanifold (n + n) W n := by
    simpa only [hVdim] using hW
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_add_right n n) hWn.2.2
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_add_right n n) hWn.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWn.2.1
  have : CompactSpace Xt :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hμ).1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWn.1.isCompact
  have : Nonempty Xt := ⟨hWn.2.1.nonempty.choose⟩
  have hinc := SubmanifoldChartedSpace.contMDiff_val (Nat.le_add_right n n) hWn.2.2
  let g₀ : W → Y₀ := fun w => (μ w.val).1
  let g₁ : W → Y₁ := fun w => (μ w.val).2
  have hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀ :=
    (ProductComplexManifold.contMDiff_fst.comp hμ.contMDiff).comp hinc
  have hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ :=
    (ProductComplexManifold.contMDiff_snd.comp hμ.contMDiff).comp hinc
  have hWpre : W ⊆ μ ⁻¹' V.carrier :=
    closure_minimal sdiff_subset (V.isClosed_carrier.preimage hμ.contMDiff.continuous)
  have hbase (w : W) : c₀ (g₀ w) = c₁ (g₁ w) := hVF (hWpre w.property)
  let U₁ := goodOpen c₁ hc₁ B hBa.isClosed
  let U₀ := goodOpen c₀ hc₀ B hBa.isClosed
  let γ : U₁ → Y₀ × Y₁ := fun y => ((e y).val, y.val)
  have hγ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ γ :=
    ProductComplexManifold.contMDiff_prodMk
      (contMDiff_subtype_val.comp e.contMDiff) contMDiff_subtype_val
  have hγG (y : U₁) : c₀ (γ y).1 = c₁ (γ y).2 ∧ c₀ (γ y).1 ∉ B :=
    ⟨he y, (e y).property⟩
  have hGoff {p : Y₀ × Y₁} (hp : c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B) :
      p ∉ singularLocus V := by
    intro hs
    apply hs.2
    change RegularAtDim (n := n + n) V.carrier p V.dim
    rw [hVdim]
    exact hGreg p hp
  have hSingc : IsClosed (singularLocus V) := EmbeddedFromResolution.isClosed_singularLocus V
  let O : Opens (Y₀ × Y₁) := ⟨(singularLocus V)ᶜ, hSingc.isOpen_compl⟩
  let R : Y₀ × Y₁ → Xt := ModificationMassInvariance.invOver μ (singularLocus V)ᶜ
  have hR := contMDiffOn_invOver hμ.contMDiff hSingc.isOpen_compl hiso
  have hRO : ContMDiff 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞
      (fun x : O => R x.val) := by
    intro x
    exact (hR.contMDiffAt (hSingc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  let k : U₁ → O := fun y => ⟨γ y, hGoff (hγG y)⟩
  have hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ k :=
    BlowupRestrictOpen.contMDiff_opens_mk hγ (fun y => hGoff (hγG y))
  have hμR (p : Y₀ × Y₁) (hp : p ∉ singularLocus V) : μ (R p) = p :=
    (ModificationMassInvariance.invOver_mem hiso hp).2
  have hland (y : U₁) : R (γ y) ∈ W := by
    apply subset_closure
    refine ⟨?_, ?_⟩
    · change μ (R (γ y)) ∈ V.carrier
      rw [hμR _ (k y).property, hVclosure]
      exact subset_closure (hγG y)
    · exact fun h => disjoint_left.mp hiso.2
        (ModificationMassInvariance.invOver_mem hiso (k y).property).1 h
  let s₁ : U₁ → W := fun y => ⟨R (γ y), hland y⟩
  have hs₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₁ :=
    SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_add_right n n) hWn.2.2
      (hRO.comp hk) hland
  have hμs (y : U₁) : μ (s₁ y).val = γ y := hμR _ (k y).property
  have hright₁ (y : U₁) : g₁ (s₁ y) = y.val := congrArg Prod.snd (hμs y)
  have hμGraph (w : W) (hw : c₁ (g₁ w) ∉ B) : μ w.val = γ ⟨g₁ w, hw⟩ := by
    apply Prod.ext
    · exact hinj (by change c₀ (g₀ w) ∉ B; rwa [hbase w])
        (e ⟨g₁ w, hw⟩).property ((hbase w).trans (he ⟨g₁ w, hw⟩).symm)
    · rfl
  have hleft₁ (w : W) (hw : c₁ (g₁ w) ∉ B) : s₁ ⟨g₁ w, hw⟩ = w := by
    apply Subtype.ext
    apply hiso.1.injOn
    · change μ (s₁ ⟨g₁ w, hw⟩).val ∉ singularLocus V
      rw [hμs]
      exact hGoff (hγG _)
    · change μ w.val ∉ singularLocus V
      rw [hμGraph w hw]
      exact hGoff (hγG _)
    · rw [hμs, hμGraph w hw]
  let s₀ : U₀ → W := fun y => s₁ (e.symm y)
  have hs₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₀ :=
    hs₁.comp e.symm.contMDiff
  have hright₀ (y : U₀) : g₀ (s₀ y) = y.val := by
    have h := congrArg Prod.fst (hμs (e.symm y))
    simpa only [γ, e.apply_symm_apply] using h
  have hleft₀ (w : W) (hw : c₀ (g₀ w) ∉ B) : s₀ ⟨g₀ w, hw⟩ = w := by
    have hw₁ : c₁ (g₁ w) ∉ B := by rwa [← hbase w]
    have heq : e.symm (⟨g₀ w, hw⟩ : U₀) = ⟨g₁ w, hw₁⟩ := by
      have hforward : (⟨g₀ w, hw⟩ : U₀) = e ⟨g₁ w, hw₁⟩ :=
        Subtype.ext (congrArg Prod.fst (hμGraph w hw₁))
      exact (congrArg (fun z : U₀ => e.symm z) hforward).trans (e.symm_apply_apply _)
    change s₁ (e.symm ⟨g₀ w, hw⟩) = w
    rw [heq]
    exact hleft₁ w hw₁
  have hE₀a := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hc₀ hBa
  have hE₁a := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hc₁ hBa
  obtain ⟨y, hy⟩ := (interior_eq_empty_iff_dense_compl.mp hthin₁).nonempty
  have : Nonempty Y₀ := ⟨(e ⟨y, hy⟩).val⟩
  have hmod₀ : IsAnalyticModification (n := n) g₀ :=
    isAnalyticModification_of_open_inverse hg₀ hg₀.continuous.isProperMap
      hE₀a hthin₀ s₀ hs₀ hright₀ hleft₀
  have hmod₁ : IsAnalyticModification (n := n) g₁ :=
    isAnalyticModification_of_open_inverse hg₁ hg₁.continuous.isProperMap
      hE₁a hthin₁ s₁ hs₁ hright₁ hleft₁
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g₀, g₁, hmod₀, hmod₁, funext hbase⟩

end

end Hironaka.HironakaEmbeddedCommon
