import Hironaka.Resolution.HironakaG3IndexedMixedOverlap
import Hironaka.Resolution.HironakaG3RTowerClass
import Hironaka.Resolution.HironakaG3RPureEmbedded
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedGluing
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaAdmissibleSequence
  RestrictEmptyTower HironakaG3RTowerClass HironakaEmbeddedAnalyticLocal HironakaG3FiniteMixedBadLocus
  HironakaG3MixedOrderedSeparation HironakaG3IndexedMixedLocalCover HironakaG3IndexedMixedOverlap
  HironakaActualLocallyFiniteBoundary HironakaG3RPureEmbedded HironakaAdmissibleCalculus

/-- Actual local mixed trees on complete finite sorted windows of the indexed
component and boundary families. -/
def indexedMixedClass {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (D : κ → Set X) : LocalTowerClass X :=
  fun U Y T => ∃ (s : Finset ι) (r : Finset κ) (Ef : List (Set Y)),
    (∀ i, ((V i).carrier ∩ (U : Set X)).Nonempty → i ∈ s) ∧
    (∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ r) ∧
    let l := s.sort (· ≤ ·)
    let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
    CanonicalMixedSeparation (((r.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·))
      (l.map (fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim))) T Ef ∧
    CentresOver ((Subtype.val : U → X) ⁻¹' mixedBadLocus W) T ∧
    IsAdmissibleBlowupSequence n U (((r.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·))
      ((Subtype.val : U → X) ⁻¹' mixedBadLocus W) Y T.proj Ef ∧ IsSNCDivisor n Ef ∧
    (List.finRange l.length).Pairwise (fun a c =>
      Disjoint (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' (W a).carrier))
        (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' (W c).carrier)))

/-- Actual mixed histories on complete finite windows compare over overlaps. -/
theorem indexed_mixed_comparisons {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) : HasComparisons (indexedMixedClass V D) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  obtain ⟨s₁,r₁,Ef₁,hs₁,hr₁,hTree₁,hOver₁,_hAdm₁,_hSNC₁,_hDis₁⟩ := h₁
  obtain ⟨s₂,r₂,Ef₂,hs₂,hr₂,hTree₂,hOver₂,_hAdm₂,_hSNC₂,_hDis₂⟩ := h₂
  exact indexed_mixed_trees_overlap V hDim hDistinct D s₁ s₂ r₁ r₂ U₁ U₂
    hs₁ hs₂ hr₁ hr₂ T₁ T₂ Ef₁ Ef₂ hTree₁ hTree₂ hOver₁ hOver₂

/-- Local finite sorted canonical trees glue for locally finite indexed
component and SNC-boundary families, without boundary avoidance. -/
theorem exists_glued_indexed_mixed_separation {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (indexedMixedClass V D) Z P := by
  have hCover : Covers (indexedMixedClass V D) := by
    intro x
    obtain ⟨U,s,r,hx,hs,hr,Y,T,Ef,hTree,hOver,hAdm,hSNC,hDis⟩ :=
      indexed_mixed_local_cover V hV hDim hDistinct D hD x
    exact ⟨U,hx,Y,T,s,r,Ef,hs,hr,hTree,hOver,hAdm,hSNC,hDis⟩
  exact exists_isGluedFrom hCover (indexed_mixed_comparisons V hDim hDistinct D)
/-- The conventional strict transforms of different indexed components are
globally disjoint in any glued indexed mixed-separation atlas. -/
theorem glued_indexed_mixed_disjoint {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (D : κ → Set X) {P : Z → X}
    (h : IsGluedFrom (indexedMixedClass V D) Z P) {a b : ι} (hab : a ≠ b) :
    Disjoint (strictTransform n P (V a).carrier) (strictTransform n P (V b).carrier) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨c,hc⟩ := h.2.2.2 (P z)
  have hzV : z ∈ c.V := c.mem_V hc
  let y := c.φ.symm ⟨z,hzV⟩
  have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
  have hy₁ : y ∈ strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V a).carrier) := by
    rw [strictTransform_chart c h.1]
    change chartIncl c y ∈ strictTransform n P (V a).carrier
    rwa [hyz]
  have hy₂ : y ∈ strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V b).carrier) := by
    rw [strictTransform_chart c h.1]
    change chartIncl c y ∈ strictTransform n P (V b).carrier
    rwa [hyz]
  obtain ⟨s,r,Ef,hs,_hr,_hTree,_hOver,_hAdm,_hSNC,hDis⟩ := c.mem
  have hp₁ : P z ∈ (V a).carrier :=
    HironakaAdmissibleCalculus.strictTransform_subset_preimage h.1.continuous (V a).isClosed_carrier hz₁
  have hp₂ : P z ∈ (V b).carrier :=
    HironakaAdmissibleCalculus.strictTransform_subset_preimage h.1.continuous (V b).isClosed_carrier hz₂
  have ha : a ∈ s := hs a ⟨P z,hp₁,hc⟩
  have hb : b ∈ s := hs b ⟨P z,hp₂,hc⟩
  have ha' : a ∈ s.sort (· ≤ ·) := by simpa using ha
  have hb' : b ∈ s.sort (· ≤ ·) := by simpa using hb
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha'
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hb'
  have hij : i ≠ j := by
    intro he
    apply hab
    rw [← hi,← hj,he]
  have hlocal : Disjoint
      (strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V a).carrier))
      (strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V b).carrier)) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hrel := hDis.rel_get_of_lt (show
        (⟨i.val,by simpa only [List.length_finRange] using i.isLt⟩ : Fin (List.finRange (s.sort (· ≤ ·)).length).length) <
        ⟨j.val,by simpa only [List.length_finRange] using j.isLt⟩ from hlt)
      simp only [List.get_eq_getElem,List.getElem_finRange] at hrel
      change Disjoint
        (strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V ((s.sort (· ≤ ·)).get i)).carrier))
        (strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V ((s.sort (· ≤ ·)).get j)).carrier)) at hrel
      simpa only [hi,hj] using hrel
    · have hrel := hDis.rel_get_of_lt (show
        (⟨j.val,by simpa only [List.length_finRange] using j.isLt⟩ : Fin (List.finRange (s.sort (· ≤ ·)).length).length) <
        ⟨i.val,by simpa only [List.length_finRange] using i.isLt⟩ from hgt)
      have hrel' := hrel.symm
      simp only [List.get_eq_getElem,List.getElem_finRange] at hrel'
      change Disjoint
        (strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V ((s.sort (· ≤ ·)).get i)).carrier))
        (strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' (V ((s.sort (· ≤ ·)).get j)).carrier)) at hrel'
      simpa only [hi,hj] using hrel'
  exact Set.disjoint_left.mp hlocal hy₁ hy₂
/-- Locally finite indexed components admit a proper glued separator with
pairwise disjoint conventional strict transforms. -/
theorem exists_glued_indexed_mixed_separation_disjoint {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (indexedMixedClass V D) Z P ∧
      ∀ a b, a ≠ b → Disjoint (strictTransform n P (V a).carrier) (strictTransform n P (V b).carrier) := by
  obtain ⟨Z,P,h⟩ := exists_glued_indexed_mixed_separation V hV hDim hDistinct D hD
  exact ⟨Z,P,h,fun _ _ hab => glued_indexed_mixed_disjoint V D h hab⟩
end
end Hironaka.HironakaG3IndexedMixedGluing
