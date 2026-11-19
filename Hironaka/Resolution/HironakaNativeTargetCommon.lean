import Hironaka.Resolution.HironakaEmbeddedCommonResolution

/-! Native common component/resolution over an ARBITRARY topological target.
Only literal K and native Ai analytic/good biholomorphism data replace the
old ambient-target hypotheses; the ORIGINAL Hironaka consumer derives them.
Literal native product/K/V and actual EmbeddedResolution engine retained.
Same-n compact native sources/ConnectedSpaceY1 scope is explicit.
Blueprint FIRST: hironaka-native-target-common.tex. Reused graph/inverse
arguments have zero separate new proof credit; no supplied common packet. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
  Hironaka.ProductComplexManifold
universe u
namespace Hironaka.HironakaNativeTargetCommon
open Hironaka.BlowupSequences Hironaka.NonKahlerLocus ProductComplexManifold
  RegularLocusComponent GlobalComponents AnalyticModificationLocalDiscrepancy
noncomputable section
section Graph

variable {n₀ n₁ : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n₀) X] [IsComplexManifold n₀ X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n₁) Y] [IsComplexManifold n₁ Y]

private theorem regularAtDim_of_prodOpen {O : Opens Y} {F : Set (X × Y)}
    {q : X × O} {d : ℕ}
    (h : RegularAtDim (n := n₀ + n₁) {p : X × O | (p.1, p.2.val) ∈ F} q d) :
    RegularAtDim (n := n₀ + n₁) F (q.1, q.2.val) d := by
  let Q : Opens (X × Y) := ⟨Prod.snd ⁻¹' (O : Set Y), O.isOpen.preimage continuous_snd⟩
  let φ : Q → X × O := fun u => (u.val.1, ⟨u.val.2, u.property⟩)
  let ψ : X × O → Q := fun p => ⟨(p.1, p.2.val), p.2.property⟩
  have hφ : ContMDiff 𝓘(ℂ, ComplexModel (n₀ + n₁))
      𝓘(ℂ, ComplexModel (n₀ + n₁)) ∞ φ :=
    ProductComplexManifold.contMDiff_prodMk
      (ProductComplexManifold.contMDiff_fst.comp contMDiff_subtype_val)
      (BlowupRestrictOpen.contMDiff_opens_mk
        (ProductComplexManifold.contMDiff_snd.comp contMDiff_subtype_val)
        (fun u => u.property))
  have hψ : ContMDiff 𝓘(ℂ, ComplexModel (n₀ + n₁))
      𝓘(ℂ, ComplexModel (n₀ + n₁)) ∞ ψ :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (ProductComplexManifold.contMDiff_prodMk ProductComplexManifold.contMDiff_fst
        (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_snd))
      (fun p => p.2.property)
  let z : Q := ψ q
  have hz : z ∉ exceptionalLocus (n₀ + n₁) φ :=
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse hφ hψ
      (fun _ => rfl) (fun _ => rfl) z
  have hQ : RegularAtDim (n := n₀ + n₁)
      ((Subtype.val : Q → X × Y) ⁻¹' F) z d :=
    RegularAtDimTransport.regularAtDim_of_preimage (g := φ) hφ hz
      (A := {p : X × O | (p.1, p.2.val) ∈ F}) isOpen_univ (mem_univ z)
      (fun _ _ => Iff.rfl) h
  exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hQ

private theorem regularAtDim_of_eq_graph {O : Opens Y} {g : O → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n₁) 𝓘(ℂ, ComplexModel n₀) ∞ g)
    {F : Set (X × Y)}
    (hF : ∀ (p : X × Y) (hp : p.2 ∈ O), p ∈ F ↔ p.1 = g ⟨p.2, hp⟩)
    (b : O) : RegularAtDim (n := n₀ + n₁) F (g b, b.val) n₁ := by
  have hΓ := HironakaAuxiliaryGraphGeometry.regularAtDim_graph hg
    (AnalyticIrreducibleComponents.regularAtDim_univ b)
  have heq : {p : X × O | (p.1, p.2.val) ∈ F} =
      HironakaAuxiliaryGraphGeometry.graphOn g univ := by
    ext p
    change ((p.1, p.2.val) ∈ F) ↔ p.2 ∈ univ ∧ p.1 = g p.2
    simp only [mem_univ, true_and]
    exact hF (p.1, p.2.val) p.2.property
  rw [← heq] at hΓ
  exact regularAtDim_of_prodOpen (q := (g b, b)) hΓ

end Graph


section MainComponent

variable {n : ℕ} {S Y₀ Y₁ : Type u}
  [TopologicalSpace S]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  {c₀ : Y₀ → S} {c₁ : Y₁ → S} {B : Set S}

/-- The original open of a resolution lying over the complement of `B`. -/
def goodOpen (c : Y₁ → S)
    (hc : Continuous c)
    (B : Set S) (hB : IsClosed B) : Opens Y₁ :=
  ⟨c ⁻¹' Bᶜ, hB.isOpen_compl.preimage hc⟩

/-- An ordinary open transition makes the literal equalizer regular at every
point of the original good graph, even if the common image is singular. -/
theorem regularAtDim_equalizer
    (hc₀ : Continuous c₀)
    (hc₁ : Continuous c₁)
    (hBc : IsClosed B)
    (e : goodOpen c₁ hc₁ B hBc ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBc)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ))
    {p : Y₀ × Y₁} (hp : c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B) :
    RegularAtDim (n := n + n) {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2} p n := by
  let g : goodOpen c₁ hc₁ B hBc → Y₀ := fun y => (e y).val
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g :=
    contMDiff_subtype_val.comp e.contMDiff
  have hF (q : Y₀ × Y₁) (hq : q.2 ∈ goodOpen c₁ hc₁ B hBc) :
      c₀ q.1 = c₁ q.2 ↔ q.1 = g ⟨q.2, hq⟩ := by
    constructor
    · intro hqF
      apply hinj
      · change c₀ q.1 ∉ B
        rwa [hqF]
      · exact (e ⟨q.2, hq⟩).property
      · exact hqF.trans (he ⟨q.2, hq⟩).symm
    · intro hqg
      rw [hqg]
      exact he ⟨q.2, hq⟩
  have hpO : p.2 ∈ goodOpen c₁ hc₁ B hBc := by
    change c₁ p.2 ∉ B
    rw [← hp.1]
    exact hp.2
  have heq : p = (g ⟨p.2, hpO⟩, p.2) := Prod.ext ((hF p hpO).mp hp.1) rfl
  rw [heq]
  exact regularAtDim_of_eq_graph hg hF ⟨p.2, hpO⟩

/-- Actual continuous maps, analytic native equalizer/bad preimages and the
native open transition construct the literal main irreducible component. -/
theorem exists_mainComponent_of_open_transition [ConnectedSpace Y₁]
    (hc₀ : Continuous c₀)
    (hc₁ : Continuous c₁)
    (hBc : IsClosed B)
    (hK : IsComplexAnalyticSubset (n := n+n) {p : Y₀ × Y₁ | c₀ p.1=c₁ p.2})
    (hA₀ : IsComplexAnalyticSubset (n := n) (c₀ ⁻¹' B))
    (hA₁ : IsComplexAnalyticSubset (n := n) (c₁ ⁻¹' B))
    (hthin : interior (c₁ ⁻¹' B) = ∅)
    (e : goodOpen c₁ hc₁ B hBc ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBc)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ)) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
      V.dim = n ∧
      V.carrier ∈ globalComponents (n := n + n) {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
      V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
      V.carrier ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
      (∀ p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B},
        RegularAtDim (n := n + n) V.carrier p n) := by
  classical
  let U := goodOpen c₁ hc₁ B hBc
  have hEa : IsComplexAnalyticSubset (n := n) (c₁ ⁻¹' B) := hA₁
  have hUne : (c₁ ⁻¹' B)ᶜ.Nonempty :=
    (interior_eq_empty_iff_dense_compl.mp hthin).nonempty
  have hEne : c₁ ⁻¹' B ≠ univ := by
    intro h
    obtain ⟨y, hy⟩ := hUne
    exact hy (h.symm ▸ mem_univ y)
  have hUconn : IsPreconnected (U : Set Y₁) :=
    AnalyticComplementConnected.isPreconnected_compl hEa hEne
  have : PreconnectedSpace U := Subtype.preconnectedSpace hUconn
  let F : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2}
  let S : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B}
  let γ : U → Y₀ × Y₁ := fun y => ((e y).val, y.val)
  have hSimage : S = γ '' univ := by
    ext p
    constructor
    · rintro ⟨hpF, hpB⟩
      have hpO : p.2 ∈ U := by change c₁ p.2 ∉ B; rwa [← hpF]
      refine ⟨⟨p.2, hpO⟩, mem_univ _, ?_⟩
      apply Prod.ext
      · exact hinj (e ⟨p.2, hpO⟩).property hpB ((he ⟨p.2, hpO⟩).trans hpF.symm)
      · rfl
    · rintro ⟨y, -, rfl⟩
      exact ⟨he y, (e y).property⟩
  have hγ : Continuous γ :=
    (continuous_subtype_val.comp e.continuous).prodMk continuous_subtype_val
  have hSconn : IsPreconnected S := by
    rw [hSimage]
    exact isPreconnected_univ.image γ hγ.continuousOn
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hUne
    rw [hSimage]
    exact ⟨γ ⟨y, hy⟩, ⟨⟨y, hy⟩, mem_univ _, rfl⟩⟩
  have hSreg (p : Y₀ × Y₁) (hp : p ∈ S) : RegularAtDim (n := n + n) F p n :=
    regularAtDim_equalizer hc₀ hc₁ hBc e he hinj hp
  obtain ⟨a, ha⟩ := hSne
  have hreg : RegularAtDim (n := n + n) F a n := hSreg a ha
  let C : Set (Y₀ × Y₁) := component (n := n + n) F a
  have hSC : S ⊆ C := subset_component_of_isPreconnected hSconn
    (fun p hp => ⟨n, hSreg p hp⟩) ⟨a, ha, mem_component_self hreg⟩
  have hFa : IsComplexAnalyticSubset (n := n + n) F := hK
  let T : Set (Y₀ × Y₁) := (fun p => c₀ p.1) ⁻¹' B
  have hTa : IsComplexAnalyticSubset (n := n + n) T :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      ProductComplexManifold.contMDiff_fst hA₀
  have hCT : ¬ C ⊆ T := fun h => ha.2 (h (mem_component_self hreg))
  have hCS : C \ T ⊆ S := fun p hp => ⟨component_subset F a hp.1, hp.2⟩
  have hCdense := (ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
    hFa hTa hreg hCT).2
  have hclosure : closure C = closure S := by
    apply Set.Subset.antisymm
    · exact closure_minimal (hCdense.trans (closure_mono hCS)) isClosed_closure
    · exact closure_mono hSC
  let V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁) :=
    { carrier := closure C
      isClosed_carrier := isClosed_closure
      irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hFa hreg
      dim := n
      dim_le := Nat.le_add_right n n
      regularLocus_nonempty := ⟨a, regularAtDim_closure_component hreg (mem_component_self hreg)⟩ }
  exact ⟨V, rfl, closure_component_mem_globalComponents hreg, hclosure,
    closure_minimal (component_subset F a) hFa.isClosed,
    fun p hp => regularAtDim_closure_component hreg (hSC hp)⟩


end MainComponent

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


variable {n : ℕ} {S Y₀ Y₁ : Type u}
  [TopologicalSpace S]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [CompactSpace Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [CompactSpace Y₁] [ConnectedSpace Y₁]
  {c₀ : Y₀ → S} {c₁ : Y₁ → S} {B : Set S}

/-- The two original maps with a common open-isomorphism locus internally
produce a compact connected smooth common model with both full modification
maps. No common component, resolution or inverse-lift certificate is supplied. -/
theorem exists_compact_smooth_common_model
    (hc₀ : Continuous c₀)
    (hc₁ : Continuous c₁)
    (hBc : IsClosed B)
    (hK : IsComplexAnalyticSubset (n := n+n) {p : Y₀ × Y₁ | c₀ p.1=c₁ p.2})
    (hA₀ : IsComplexAnalyticSubset (n := n) (c₀ ⁻¹' B))
    (hA₁ : IsComplexAnalyticSubset (n := n) (c₁ ⁻¹' B))
    (hthin₀ : interior (c₀ ⁻¹' B) = ∅) (hthin₁ : interior (c₁ ⁻¹' B) = ∅)
    (e : goodOpen c₁ hc₁ B hBc ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBc)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ)) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (g₀ : Z → Y₀) (g₁ : Z → Y₁),
      IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
      c₀ ∘ g₀ = c₁ ∘ g₁ := by
  classical
  obtain ⟨V, hVdim, _, hVclosure, hVF, hGreg⟩ :=
    exists_mainComponent_of_open_transition hc₀ hc₁ hBc hK hA₀ hA₁ hthin₁ e he hinj
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
  let U₁ := goodOpen c₁ hc₁ B hBc
  let U₀ := goodOpen c₀ hc₀ B hBc
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
  have hE₀a := hA₀
  have hE₁a := hA₁
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
end Hironaka.HironakaNativeTargetCommon
