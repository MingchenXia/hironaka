import Hironaka.Resolution.HironakaG3IndexedMixedGluing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedNonerasure
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaBaseChange HironakaAdmissibleCalculus HironakaAdmissibleSequence RestrictEmptyTower
  HironakaG3RTowerClass HironakaG3FiniteMixedBadLocus HironakaEmbeddedAnalyticLocal HironakaG3RPureEmbedded
  HironakaG3IndexedMixedGluing HironakaActualLocallyFiniteBoundary

/-- On a chart, every global exceptional point projects to that chart's
finite mixed bad locus. -/
theorem indexed_chart_exceptional_subset {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P)
    (c : TowerChart (indexedMixedClass V D) Z P) (s : Finset ι)
    (hOver : CentresOver ((Subtype.val : c.U → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s.sort (· ≤ ·)).length => V ((s.sort (· ≤ ·)).get j))) c.T)
    {z : Z} (hzU : P z ∈ c.U) (hz : z ∈ exceptionalLocus n P) :
    P z ∈ mixedBadLocus (fun j : Fin (s.sort (· ≤ ·)).length => V ((s.sort (· ≤ ·)).get j)) := by
  let l := s.sort (· ≤ ·)
  let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
  have he : Injective l.get := (s.sort_nodup (· ≤ ·)).injective_get
  have hData := mixedBadLocus_closed_and_good W (fun a => hDim (l.get a))
    (fun a b hab => hDistinct (l.get a) (l.get b) (fun heq => hab (he heq)))
  have hzV : z ∈ c.V := c.mem_V hzU
  let y := c.φ.symm ⟨z,hzV⟩
  have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
  have hy : y ∈ exceptionalLocus n c.T.proj := by
    rw [exceptionalLocus_chart c h.1]
    change chartIncl c y ∈ exceptionalLocus n P
    rwa [hyz]
  let O : Opens (CMfd.of (n := n) c.U) :=
    ⟨((Subtype.val : c.U → X) ⁻¹' mixedBadLocus W)ᶜ,
      (hData.1.preimage continuous_subtype_val).isOpen_compl⟩
  have hAvoid : CentresAvoid O c.T := centresAvoid_of_centresOver O disjoint_compl_left c.T hOver
  have hExc := EmbeddedFromResolution.image_exceptionalLocus_subset_compl O c.T hAvoid ⟨y,hy,rfl⟩
  change c.T.proj y ∈ (((Subtype.val : c.U → X) ⁻¹' mixedBadLocus W)ᶜ)ᶜ at hExc
  simp only [compl_compl] at hExc
  change ((c.T.proj y : c.U) : X) ∈ mixedBadLocus W at hExc
  have hProj : P z = ((c.T.proj y : c.U) : X) :=
    (congrArg P hyz.symm).trans (proj_chartIncl c y)
  change P z ∈ mixedBadLocus W
  rwa [hProj]

/-- No indexed component is erased by a glued indexed mixed separator. -/
theorem glued_indexed_mixed_projects {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P) (a : ι) :
    P '' strictTransform n P (V a).carrier = (V a).carrier := by
  have hClosed : IsClosed (P '' strictTransform n P (V a).carrier) := h.2.1.isClosedMap _ isClosed_closure
  apply Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage h.1.continuous (V a).isClosed_carrier hz
  · intro x hx
    obtain ⟨c,hc⟩ := h.2.2.2 x
    obtain ⟨s,r,Ef,hs,_hr,_hTree,hOver,_hAdm,_hSNC,_hDis⟩ := c.mem
    let l := s.sort (· ≤ ·)
    let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
    have he : Injective l.get := (s.sort_nodup (· ≤ ·)).injective_get
    have hData := mixedBadLocus_closed_and_good W (fun i => hDim (l.get i))
      (fun i j hij => hDistinct (l.get i) (l.get j) (fun heq => hij (he heq)))
    have ha : a ∈ s := hs a ⟨x,hx,hc⟩
    have ha' : a ∈ l := by simpa [l] using ha
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha'
    have hDense : (V a).carrier ⊆ closure ((V a).carrier \ mixedBadLocus W) := by
      simpa only [W,hi] using (hData.2 i).2.2.2.2
    have hClose : x ∈ closure (((V a).carrier \ mixedBadLocus W) ∩ (c.U : Set X)) :=
      c.U.isOpen.closure_inter ⟨hDense hx,hc⟩
    apply closure_minimal _ hClosed hClose
    rintro q ⟨⟨hqV,hqG⟩,hqU⟩
    obtain ⟨z,rfl⟩ := h.2.2.1 q
    refine ⟨z,subset_closure ⟨hqV,?_⟩,rfl⟩
    intro hzExc
    exact hqG (indexed_chart_exceptional_subset V hDim hDistinct D h c s hOver hqU hzExc)
/-- The same globally glued indexed separator separates and preserves every
labelled component under projection. -/
theorem exists_glued_indexed_separator_with_nonerasure {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (indexedMixedClass V D) Z P ∧
      (∀ a b, a ≠ b → Disjoint (strictTransform n P (V a).carrier) (strictTransform n P (V b).carrier)) ∧
      ∀ a, P '' strictTransform n P (V a).carrier = (V a).carrier := by
  obtain ⟨Z,P,h,hDis⟩ := exists_glued_indexed_mixed_separation_disjoint V hV hDim hDistinct D hD
  exact ⟨Z,P,h,hDis,fun a => glued_indexed_mixed_projects V hDim hDistinct D h a⟩
end
end Hironaka.HironakaG3IndexedMixedNonerasure
