import Hironaka.Resolution.HironakaActualNonregularCompanionNaturality
import Hironaka.Invariant.CompanionRebase
import Hironaka.Resolution.HironakaActualNoncanonicalAnalyticTransformLocality
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualRawCompanionNaturality
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers MarkedIdealBiholomorphism
open RelativePrincipalizationSpan GermIdealPullbackCalculus MarkedIdeals MarkedIdeals.MarkedIdeal
open HadamardBridge DerivativeIdealAlongEtale MonomialPartEtale MonomialPartAlong
open RestrictedIdealExtension RestrictedIdealQuotient InvertibleIdealQuotient
open CompanionRebase CompanionReductionAlong IdealWeightPowers
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
 {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
 {φ : M' → M} {ψ : M → M'} {y : M'}

theorem mem_restrictOn_pullback_iff {𝔟 : GermIdeal n M}
 (hIhol : ∀ x g,𝔟.mem x g → HolomorphicAt n g x)
 (hIcl : ∀ x g,IsInSpanAt (n := n) (𝔟.mem x) x g → 𝔟.mem x g)
 (hψ : IsLocalInverseAt n φ ψ y) {W : Set M} {F : M' → ℂ} :
 (restrictOn n (φ ⁻¹' W) (GermIdeal.pullback (m := n) φ 𝔟)).mem y F ↔
   (restrictOn n W 𝔟).mem (φ y) (F ∘ ψ) := by
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  constructor
  · rintro ⟨hF, K, s, a, hs, ha, hsum⟩
    refine ⟨holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact hF), K, fun k => s k ∘ ψ, fun k => a k ∘ ψ,
      fun k => (HironakaActualNonregularCompanionNaturality.mem_pullback_iff_of_span_closed hIhol hIcl hψ).mp (hs k),
      fun k => holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact ha k), ?_⟩
    have hsum' : ∀ᶠ p in 𝓝 (ψ (φ y)), p ∈ φ ⁻¹' W → F p = ∑ k, a k p * s k p := by rw [hψy]; exact hsum
    filter_upwards [hψ.mdiff_inv.self_of_nhds.continuousAt.eventually hsum', hψ.right_inv] with q hq hqr hqW
    exact hq (show φ (ψ q) ∈ W by rw [hqr]; exact hqW)
  · rintro ⟨hF, K, s, a, hs, ha, hsum⟩
    have hFψφ : (F ∘ ψ) ∘ φ =ᶠ[𝓝 y] F := by
      filter_upwards [hψ.left_inv] with p hp
      simp [hp]
    refine ⟨(holomorphicAt_comp_map hψ.mdiff hF).congr hFψφ, K, fun k => s k ∘ φ, fun k => a k ∘ φ,
      fun k => comp_mem_pullback hψ.mdiff (hs k)
        (hIhol _ _ (hs k)),
      fun k => holomorphicAt_comp_map hψ.mdiff (ha k), ?_⟩
    filter_upwards [hψ.mdiff.self_of_nhds.continuousAt.eventually hsum, hψ.left_inv] with p hp hpl hpW
    have := hp hpW
    simp only [Function.comp_apply, hpl] at this
    simpa using this

omit [IsComplexManifold n M] in
private theorem colon_span_closed {I L : GermIdeal n M} {N : Set M}
 (hL : ∀ x g, L.mem x g → HolomorphicAt n g x) {x : M} {f : M → ℂ}
 (hf : IsInSpanAt (n := n) ((colonAlong n N I L).mem x) x f) :
 (colonAlong n N I L).mem x f := by
 obtain ⟨hfhol,K,s,a,hs,ha,hsum⟩ := hf
 refine ⟨hfhol,fun g hg => ?_⟩
 refine restrictOn_of_isInSpanAt (𝔞 := I) ⟨(hL _ _ hg).mul hfhol,K,
   fun i w => g w*s i w,a,fun i => (hs i).2 g hg,ha,?_⟩
 filter_upwards [hsum] with w hw
 show g w*f w = ∑ i,a i w*(g w*s i w)
 rw [hw,Finset.mul_sum]
 exact Finset.sum_congr rfl fun i _ => by ring

theorem pullback_colonAlong
 (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
 {𝔟 𝔩 : GermIdeal n M} (hIhol : ∀ x g,𝔟.mem x g → HolomorphicAt n g x)
 (hIcl : ∀ x g,IsInSpanAt (n := n) (𝔟.mem x) x g → 𝔟.mem x g)
 (hhol : ∀ x g, 𝔩.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g, IsInSpanAt (n := n) (𝔩.mem x) x g → 𝔩.mem x g) {W : Set M} :
 colonAlong n (φ ⁻¹' W) (GermIdeal.pullback (m := n) φ 𝔟) (GermIdeal.pullback (m := n) φ 𝔩) =
   GermIdeal.pullback (m := n) φ (colonAlong n W 𝔟 𝔩) := by
  refine GermIdeal.ext (funext fun y => funext fun f => propext ?_)
  obtain ⟨ψ, hψ⟩ := hloc y
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  rw [HironakaActualNonregularCompanionNaturality.mem_pullback_iff_of_span_closed (𝔠 := colonAlong n W 𝔟 𝔩) (fun _ _ hg => hg.1)
    (fun _ _ hf => colon_span_closed hhol hf) hψ]
  constructor
  · rintro ⟨hf, hcol⟩
    refine ⟨holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact hf), fun g' hg' => ?_⟩
    have h1 := hcol (g' ∘ φ) (comp_mem_pullback hψ.mdiff hg'
      (hhol _ _ hg'))
    have h2 := (mem_restrictOn_pullback_iff hIhol hIcl hψ).mp h1
    refine restrictOn_mem_congr h2 ?_
    filter_upwards [hψ.right_inv] with q hq
    simp [hq]
  · rintro ⟨hf, hcol⟩
    have hfψφ : (f ∘ ψ) ∘ φ =ᶠ[𝓝 y] f := by
      filter_upwards [hψ.left_inv] with p hp
      simp [hp]
    refine ⟨(holomorphicAt_comp_map hψ.mdiff hf).congr hfψφ, fun g hg => ?_⟩
    have h1 := hcol (g ∘ ψ) ((HironakaActualNonregularCompanionNaturality.mem_pullback_iff_of_span_closed hhol hcl hψ).mp hg)
    exact (mem_restrictOn_pullback_iff hIhol hIcl hψ).mpr h1

section Companion
variable {X Y : CMfd.{u} n}

private theorem pullback_factor_companion {f : Y → X}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (I L : GermIdeal n X)
 (hI : ∀ x g, I.mem x g → HolomorphicAt n g x)
 (hL : ∀ x g, L.mem x g → HolomorphicAt n g x)
 (N : Set X) (E : List (Set X)) (o d : ℕ) :
 MarkedIdeal.pullback f (companionAlong N E I L o d) =
   companionAlong (f ⁻¹' N) (E.map (f ⁻¹' ·))
     (GermIdeal.pullback (m := n) f I) (GermIdeal.pullback (m := n) f L) o d := by
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_
 · simp [MarkedIdeal.pullback]
 · simp [MarkedIdeal.pullback]
 · show GermIdeal.pullback (m := n) f (companionAlong N E I L o d).ideal = _
   rw [companionAlong_ideal,companionAlong_ideal]
   split_ifs
   · rw [MarkedIdealOperationsTransform.pullback_sumIdeal hf
       (fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
       (fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg),
       HironakaActualNonregularCoefficientNaturality.pullback_idealPow hf (fun {_ _} hg => hI _ _ hg),
       HironakaActualNonregularCoefficientNaturality.pullback_idealPow hf (fun {_ _} hg => hL _ _ hg)]
   · rfl
 · show (companionAlong N E I L o d).d = _
   rw [companionAlong_d,companionAlong_d]

theorem pullback_companionOf {f : Y → X}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hloc : ∀ y : Y, ∃ ψ : X → Y, IsLocalInverseAt n f ψ y)
 (M : MarkedIdeal n X)
 (hIhol : ∀ x g,M.ideal.mem x g → HolomorphicAt n g x)
 (hIcl : ∀ x g,IsInSpanAt (n := n) (M.ideal.mem x) x g → M.ideal.mem x g) (o : ℕ) :
 MarkedIdeal.pullback f (companionOf n M o) =
   companionOf n (MarkedIdeal.pullback f M) o := by
 have hhI : ∀ x g,M.ideal.mem x g → HolomorphicAt n g x := hIhol
 have hMonHol : ∀ x g, (monomialPartAlong n M.N M.ideal M.E).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hNNHol : ∀ x g, (nonmonomialPartAlong n M.N M.ideal M.E).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hMon := MonomialPartEtale.pullback_monomialPartAlong hloc hhI (N := M.N) (E := M.E)
 have hNN : GermIdeal.pullback (m := n) f (nonmonomialPartAlong n M.N M.ideal M.E) =
     nonmonomialPartAlong n (f ⁻¹' M.N) (GermIdeal.pullback (m := n) f M.ideal) (M.E.map (f ⁻¹' ·)) := by
   unfold nonmonomialPartAlong
   rw [←hMon]
   exact (pullback_colonAlong hloc hIhol hIcl hMonHol
     (fun _ _ hg => monomialPartAlong_mem_of_isInSpanAt hg)).symm
 unfold companionOf
 rw [pullback_factor_companion hf _ _ hNNHol hMonHol,hNN,hMon]
 rfl

end Companion
end
end Hironaka.HironakaActualRawCompanionNaturality
