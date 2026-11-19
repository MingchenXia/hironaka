import Hironaka.Resolution.HironakaG3IndexedMixedCompactWindow
import Hironaka.Resolution.HironakaG3IndexedMixedChartGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedGlobalSNC
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  RestrictEmptyTower HironakaG3FiniteMixedBadLocus HironakaG3MixedOrderedSeparation
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG3REmbeddedGlobalSNC HironakaG3IndexedMixedGluing
  HironakaG3IndexedMixedCompactWindow HironakaG3IndexedMixedChartBoundary
  HironakaG3IndexedMixedChartGeometry

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
variable (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (D : κ → Set X)

def MixedBoundaryWitness (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)) : Prop :=
  ∃ (s : Finset ι) (r : Finset κ),
    (∀ i, ((V i).carrier ∩ (c.U : Set X)).Nonempty → i ∈ s) ∧
    (∀ i, (D i ∩ (c.U : Set X)).Nonempty → i ∈ r) ∧
    CanonicalMixedSeparation (((r.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·))
      ((s.sort (· ≤ ·)).map (fun a => ((Subtype.val : c.U → X) ⁻¹' (V a).carrier,(V a).dim))) c.T Ef ∧
    CentresOver ((Subtype.val : c.U → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s.sort (· ≤ ·)).length => V ((s.sort (· ≤ ·)).get j))) c.T ∧
    IsSNCDivisor n Ef

theorem mixed_chart_exists_boundary_witness (c : TowerChart (indexedMixedClass V D) Z P) :
    ∃ Ef, MixedBoundaryWitness V D c Ef := by
  obtain ⟨s,r,Ef,hs,hr,hTree,hOver,_hAdm,hSNC,_hDis⟩ := c.mem
  exact ⟨Ef,s,r,hs,hr,hTree,hOver,hSNC⟩

theorem mixed_witness_chart_boundary_overlap
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (c₁ c₂ : TowerChart (indexedMixedClass V D) Z P)
    (Ef₁ : List (Set c₁.Y)) (Ef₂ : List (Set c₂.Y))
    (h₁ : MixedBoundaryWitness V D c₁ Ef₁) (h₂ : MixedBoundaryWitness V D c₂ Ef₂) :
    ((mixedChartBoundary V D c₁ Ef₁).map
      (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) =
    ((mixedChartBoundary V D c₂ Ef₂).map
      (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) := by
  obtain ⟨s₁,r₁,hs₁,hr₁,hT₁,hO₁,_⟩ := h₁
  obtain ⟨s₂,r₂,hs₂,hr₂,hT₂,hO₂,_⟩ := h₂
  exact mixed_chart_boundary_overlap V D hDim hDistinct c₁ c₂ s₁ s₂ r₁ r₂ Ef₁ Ef₂
    hs₁ hs₂ hr₁ hr₂ hT₁ hT₂ hO₁ hO₂

/-- The actual mixed-separation charts have one locally finite global SNC
boundary with a single nested exhaustion carrying the full actual local lists. -/
theorem indexed_mixed_exists_global_boundary
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hG : IsGluedFrom (indexedMixedClass V D) Z P) :
    ∃ Ex : SNCExhaustion Z,
      (∀ k, ∃ (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)),
        MixedBoundaryWitness V D c Ef ∧ Ex.W k = c.V ∧ Ex.B k = mixedChartBoundary V D c Ef) ∧
      ∃ (ρ : Type) (B : ρ → Set Z), IsLocallyFiniteSNCDivisor n B ∧
        (∀ i, (B i).Nonempty) ∧ (⋃ i, B i) = ⋃ k, ⋃ H ∈ Ex.B k, H := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let K := CompactExhaustion.choice X
  have hU : ∀ k : ℕ, ∃ c : TowerChart (indexedMixedClass V D) Z P,
      c.U = ⟨interior (K (k+1)),isOpen_interior⟩ := fun k =>
    indexed_mixed_chart_over_compact_window V hV hDim hDistinct D hD hG _ (K (k+1))
      (K.isCompact (k+1)) interior_subset
  choose c hc using hU
  choose Ef hEf using fun k => mixed_chart_exists_boundary_witness V D (c k)
  have hUmono : ∀ {j k : ℕ}, j ≤ k → (c j).U ≤ (c k).U := fun {j k} hjk => by
    rw [hc,hc]
    exact interior_mono (K.subset (by omega))
  have hVmono : ∀ {j k : ℕ}, j ≤ k → ((c j).V : Set Z) ⊆ (c k).V := fun {j k} hjk y hy => by
    have h' : y ∈ ((c j).V : Set Z) := hy
    rw [(c j).V_eq] at h'
    exact (c k).mem_V (hUmono hjk h')
  have hcover : ∀ y : Z, ∃ k, y ∈ (c k).V := fun y => by
    obtain ⟨k,hk⟩ := K.exists_mem (P y)
    refine ⟨k,(c k).mem_V ?_⟩
    rw [hc]
    exact K.subset_interior_succ k hk
  have hnested : ∀ {j k : ℕ}, j ≤ k →
      ((mixedChartBoundary V D (c k) (Ef k)).map (· ∩ ((c j).V : Set Z))).filter
        (fun H => decide H.Nonempty) = (mixedChartBoundary V D (c j) (Ef j)).filter
          (fun H => decide H.Nonempty) := fun {j k} hjk => by
    have hov := mixed_witness_chart_boundary_overlap V D hDim hDistinct (c j) (c k) (Ef j) (Ef k) (hEf j) (hEf k)
    have hpre : P ⁻¹' (((c j).U ⊓ (c k).U : Opens X) : Set X) = ((c j).V : Set Z) := by
      rw [(c j).V_eq]
      ext y
      exact ⟨fun h => h.1,fun h => ⟨h,hUmono hjk h⟩⟩
    rw [hpre] at hov
    have hself : (mixedChartBoundary V D (c j) (Ef j)).map (· ∩ ((c j).V : Set Z)) =
        mixedChartBoundary V D (c j) (Ef j) := by
      conv_rhs => rw [← List.map_id (mixedChartBoundary V D (c j) (Ef j))]
      exact List.map_congr_left fun H hH => inter_eq_left.mpr (mixed_chart_boundary_subset V D (c j) (Ef j) hH)
    rw [hself] at hov
    exact hov.symm
  let Ex : SNCExhaustion Z := {
    W := fun k => (c k).V
    B := fun k => mixedChartBoundary V D (c k) (Ef k)
    mono := hVmono
    cover := hcover
    sub := fun {k} {H} hH => mixed_chart_boundary_subset V D (c k) (Ef k) hH
    snc := fun k => mixed_chart_boundary_snc V D (c k) (Ef k) (hEf k).choose_spec.choose_spec.2.2.2.2
    nested := hnested }
  exact ⟨Ex,fun k => ⟨c k,Ef k,hEf k,rfl,rfl⟩,{B : Set Z // Ex.IsGlobalMember B},fun i => i.1,
    ⟨Ex.locallyFinite_globalMember,fun i => Ex.isClosed_globalMember i.2,Ex.coordinates_globalMember⟩,
    fun i => i.2.1,Ex.iUnion_globalMember⟩
end
end Hironaka.HironakaG3IndexedMixedGlobalSNC
