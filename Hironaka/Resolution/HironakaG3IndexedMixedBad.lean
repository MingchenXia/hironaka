import Hironaka.Resolution.HironakaG3IndexedMixedNonerasure
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedBad
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaEmbeddedAnalyticLocal
  HironakaG3FiniteMixedBadLocus HironakaG3MixedOrderedSupport HironakaG3IndexedMixedNonerasure
  HironakaG3IndexedMixedGluing HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaBaseChange RestrictEmptyTower HironakaActualLocallyFiniteBoundary

/-- All original singular points and intersections of distinct components. -/
def indexedMixedBad {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X) : Set X :=
  (⋃ i, ((V i).carrier \ regularLocus (n := n) (V i).carrier (V i).dim)) ∪
  ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), ((V i).carrier ∩ (V j).carrier)

/-- A finite injectively indexed window's bad locus lies inside the original
indexed bad support. -/
theorem finite_bad_subset_indexed {n k : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (e : Fin k ↪ ι) :
    mixedBadLocus (fun j => V (e j)) ⊆ indexedMixedBad V := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨H,hH,hxH⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hH
    left
    exact Set.mem_iUnion.mpr ⟨e i,hxH⟩
  · obtain ⟨H,hH,hxH⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hH
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
    right
    exact Set.mem_iUnion.mpr ⟨e p.1,Set.mem_iUnion.mpr ⟨e p.2,
      Set.mem_iUnion.mpr ⟨fun he => (ne_of_lt hp') (e.injective he),hxH⟩⟩⟩
/-- All global exceptional points of an indexed glued separator lie over the
original indexed singular/intersection support. -/
theorem glued_indexed_exceptional_subset {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P) :
    exceptionalLocus n P ⊆ P ⁻¹' indexedMixedBad V := by
  intro z hz
  obtain ⟨c,hc⟩ := h.2.2.2 (P z)
  obtain ⟨s,r,Ef,hs,hr,hTree,hOver,hAdm,hSNC,hDis⟩ := c.mem
  let l := s.sort (· ≤ ·)
  let e : Fin l.length ↪ ι := ⟨l.get,(s.sort_nodup (· ≤ ·)).injective_get⟩
  exact finite_bad_subset_indexed V e
    (indexed_chart_exceptional_subset V hDim hDistinct D h c s hOver hc hz)

/-- A glued indexed separator is an isomorphism outside the original indexed
singular/intersection support. -/
theorem glued_indexed_isIsomorphismOver {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P) :
    IsIsomorphismOver n P (indexedMixedBad V)ᶜ := by
  have hExc := glued_indexed_exceptional_subset V hDim hDistinct D h
  refine ⟨⟨fun z hz => hz,fun z₁ hz₁ z₂ hz₂ he => ?_,fun x hx => ?_⟩,?_⟩
  · obtain ⟨c,hc⟩ := h.2.2.2 (P z₁)
    have hz₁V : z₁ ∈ c.V := c.mem_V hc
    let y₁ := c.φ.symm ⟨z₁,hz₁V⟩
    have hy₁ : chartIncl c y₁ = z₁ := chartIncl_symm c ⟨z₁,hz₁V⟩
    have hz₂V : z₂ ∈ c.V := c.mem_V (by rw [← he]; exact hc)
    let y₂ := c.φ.symm ⟨z₂,hz₂V⟩
    have hy₂ : chartIncl c y₂ = z₂ := chartIncl_symm c ⟨z₂,hz₂V⟩
    obtain ⟨s,r,Ef,hs,hr,hTree,hOver,hAdm,hSNC,hDis⟩ := c.mem
    let l := s.sort (· ≤ ·)
    let e : Fin l.length ↪ ι := ⟨l.get,(s.sort_nodup (· ≤ ·)).injective_get⟩
    let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (e j)
    have hData := mixedBadLocus_closed_and_good W (fun i => hDim (e i))
      (fun i j hij => hDistinct (e i) (e j) (fun heq => hij (e.injective heq)))
    have hBad : mixedBadLocus W ⊆ indexedMixedBad V := finite_bad_subset_indexed V e
    let G := (Subtype.val : c.U → X) ⁻¹' mixedBadLocus W
    let O : Opens (CMfd.of (n := n) c.U) :=
      ⟨Gᶜ,(hData.1.preimage continuous_subtype_val).isOpen_compl⟩
    have hAvoid : CentresAvoid O c.T := centresAvoid_of_centresOver O disjoint_compl_left c.T hOver
    have hImage : c.T.proj '' exceptionalLocus n c.T.proj ⊆ G := by
      have h1 := EmbeddedFromResolution.image_exceptionalLocus_subset_compl O c.T hAvoid
      change c.T.proj '' exceptionalLocus n c.T.proj ⊆ (Gᶜ)ᶜ at h1
      simpa only [compl_compl] using h1
    have hLocal := HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      c.T.isBlowupSequence hImage
    have hy₁O : c.T.proj y₁ ∈ Gᶜ := by
      change ((c.T.proj y₁ : c.U) : X) ∉ mixedBadLocus W
      rw [← proj_chartIncl c y₁,hy₁]
      exact fun hh => hz₁ (hBad hh)
    have hy₂O : c.T.proj y₂ ∈ Gᶜ := by
      change ((c.T.proj y₂ : c.U) : X) ∉ mixedBadLocus W
      rw [← proj_chartIncl c y₂,hy₂]
      exact fun hh => hz₂ (hBad hh)
    have hproj : c.T.proj y₁ = c.T.proj y₂ := by
      apply Subtype.ext
      rw [← proj_chartIncl c y₁,← proj_chartIncl c y₂,hy₁,hy₂]
      exact he
    have hEq : y₁ = y₂ := hLocal.1.2.1 hy₁O hy₂O hproj
    exact hy₁.symm.trans ((congrArg (chartIncl c) hEq).trans hy₂)
  · obtain ⟨z,rfl⟩ := h.2.2.1 x
    exact ⟨z,hx,rfl⟩
  · exact Set.disjoint_left.mpr fun z hz hz' => hz (hExc hz')
/-- Indexed mixed components admit one actual glued separator that preserves
all labels, separates them, and is an isomorphism off the original indexed
singular/intersection support. -/
theorem exists_glued_indexed_separator_with_good_iso {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (indexedMixedClass V D) Z P ∧
      IsIsomorphismOver n P (indexedMixedBad V)ᶜ ∧
      (∀ a b, a ≠ b → Disjoint (strictTransform n P (V a).carrier) (strictTransform n P (V b).carrier)) ∧
      ∀ a, P '' strictTransform n P (V a).carrier = (V a).carrier := by
  obtain ⟨Z,P,h,hDis,hProj⟩ := exists_glued_indexed_separator_with_nonerasure V hV hDim hDistinct D hD
  exact ⟨Z,P,h,glued_indexed_isIsomorphismOver V hDim hDistinct D h,hDis,hProj⟩
end
end Hironaka.HironakaG3IndexedMixedBad
