import Hironaka.Resolution.HironakaG3ProperFibreTowerIdentification
import Hironaka.Resolution.HironakaG3RestrictedTowerIdentification
import Hironaka.Resolution.HironakaG3RestrictTowerChart
import Hironaka.Resolution.HironakaG3CompositeTowerChart
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3CompositeGeometricAtlas
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3RigidOverLocalGlue HironakaG3ProperFibreTowerIdentification
  HironakaG3RestrictedTowerIdentification HironakaG3RestrictTowerChart HironakaG3CompositeTowerChart
  MaxLocusLocal RestrictEmptyTower HironakaG3FiniteVisibleAtlas HironakaG3DisjointLocalTowerAtlas

theorem composite_geometric_atlas {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
    {𝒞 : LocalTowerClass X} {P : Z → X} (hP : IsGluedFrom 𝒞 Z P)
    (C : ι → Set Z) (hClosed : ∀ i, IsClosed (C i)) (hLF : LocallyFinite C)
    (W : ι → Opens Z) (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set Z))
    (K : ι → LocalTowerClass Z) (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens Z) (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B),
      K i U B T → CentresOver ((Subtype.val : U → Z) ⁻¹' C i) T)
    (hCompact : ∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
      ∃ (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B), K i U B T)
    (D : κ → Set Z) (hD : LocallyFinite D) {Q : Y → Z}
    (hQ : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Y Q) :
    IsGluedFrom (fun _ _ _ => True) Y (P ∘ Q) := by
  classical
  refine ⟨hP.1.comp hQ.1, hP.2.1.comp hQ.2.1, hP.2.2.1.comp hQ.2.2.1,?_⟩
  intro x
  obtain ⟨c,hxc⟩ := hP.2.2.2 x
  obtain ⟨U,hx,B,M,Φ,hΦ,_⟩ := proper_fibre_tower_identification C hClosed hLF W hCW hWindow K hCompare hCentres hCompact D hD hP.2.1 hQ x
  let U' : Opens X := U ⊓ c.U
  have hx' : x ∈ U' := ⟨hx,hxc⟩
  have hU' : U' ≤ c.U := inf_le_right
  obtain ⟨c',hc'U,hc'V⟩ := restrict_tower_chart hP.1.continuous c U' hU'
  let A : Opens Z := window P hP.1.continuous U
  let A' : Opens Z := window P hP.1.continuous U'
  have hAA' : A' ≤ A := fun z hz => hz.1
  obtain ⟨B',M',Φ',hΦ'⟩ := restrict_tower_identification Q hQ.1.continuous A A' hAA' M Φ hΦ
  have hInputs : ∃ (B₁ : CMfd.{0} n) (M₁ : BlowupTower (CMfd.of (n := n) c'.V) B₁)
      (Φ₁ : B₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ.1.continuous c'.V)),
      ∀ z, restrictedBaseMap Q hQ.1.continuous c'.V (Φ₁ z) = M₁.proj z := by
    rw [hc'V]
    exact ⟨B',M',Φ',hΦ'⟩
  obtain ⟨B₁,M₁,Φ₁,hΦ₁⟩ := hInputs
  obtain ⟨B'',T,V,hV,e,he⟩ := composite_tower_chart hQ.1.continuous c' M₁ Φ₁ hΦ₁
  refine ⟨⟨c'.U,B'',T,True.intro,V,hV,e,he⟩,?_⟩
  rw [hc'U]
  exact hx'
end
end Hironaka.HironakaG3CompositeGeometricAtlas
