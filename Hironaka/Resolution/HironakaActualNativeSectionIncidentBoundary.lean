import Hironaka.Resolution.HironakaActualNativeSectionFiniteHistory
import Hironaka.Invariant.InvDomainMemberRestriction

/-! Actual SNC/transversality prevents an incident old/born selection
collision under native trace. Global injectivity of all traces, including
empty ones, is neither assumed nor asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionIncidentBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts NormalCrossings SimultaneousNormalCrossings
  BlowupSNCTransform
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X} {E : List (Set X)}

theorem incident_trace_indices_injective (hn : 0<n) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n W E) (p : W) {i j : Fin E.length}
    (hi : p.val∈E.get i) (hj : p.val∈E.get j)
    (hTrace : (Subtype.val : W→X) ⁻¹' E.get i=(Subtype.val : W→X) ⁻¹' E.get j) : i=j := by
  classical
  by_contra hne
  obtain ⟨kC,kN,Φ,s,hΦt,hslt,hsinj,hflat⟩:=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.rfl : W⊆W) hE hT hT.hasNormalCrossings p.property
  have hst : s i≠s j:=fun he=>hne (hsinj hi hj he)
  let e:=chartAt (ComplexModel n) p.val
  let w₀:=Φ.toFun (e p.val)
  have h0t : w₀∈Φ.target:=Φ.mapsTo_toFun Φ.center_mem_source
  have hflat0:=hflat (mem_chart_source _ p.val) Φ.center_mem_source
  have h0W : w₀∈complexCoordinatePlane n kN:=hflat0.2.1.mp p.property
  have h0i : w₀ (s i)=0:=(hflat0.2.2 i hi).mp hi
  have h0j : w₀ (s j)=0:=(hflat0.2.2 j hj).mp hj
  let v : ComplexModel n:=EuclideanSpace.single (s j) (1 : ℂ)
  have hlin : Tendsto (fun τ : ℂ=>w₀+τ • v) (𝓝[≠] 0) (𝓝 w₀):=by
    have h : Tendsto (fun τ : ℂ=>w₀+τ • v) (𝓝 0) (𝓝 (w₀+(0 : ℂ) • v)):=
      (continuous_const.add (continuous_id.smul continuous_const) : Continuous fun τ : ℂ=>w₀+τ • v).tendsto 0
    rw [zero_smul,add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨τ,hτt,hτ⟩:=((hlin.eventually (Φ.isOpen_target.mem_nhds h0t)).and self_mem_nhdsWithin).exists
  have hwΦ : Φ.invFun (w₀+τ • v)∈Φ.source:=Φ.mapsTo_invFun hτt
  have hwe : Φ.invFun (w₀+τ • v)∈e.target:=hΦt hwΦ
  let y:=e.symm (Φ.invFun (w₀+τ • v))
  have hy : y∈e.source:=e.map_target hwe
  have hey : e y=Φ.invFun (w₀+τ • v):=e.right_inv hwe
  have hyΦ : e y∈Φ.source:=by rw [hey];exact hwΦ
  have hflatY:=hflat hy hyΦ
  have hφy : Φ.toFun (chartAt (ComplexModel n) p.val y)=w₀+τ • v:=by
    change Φ.toFun (e y)=_
    rw [hey,Φ.right_inv _ hτt]
  have hyW : y∈W:=by
    apply hflatY.2.1.mpr
    rw [hφy]
    intro a ha
    have hneA : a≠s j:=by intro he;have hh:=hslt j hj;omega
    have h0a:=h0W a ha
    simp [v,hneA,h0a]
  have h1:=hflatY.2.2 i hi
  have h2:=hflatY.2.2 j hj
  rw [hφy] at h1 h2
  have hvi : (w₀+τ • v) (s i)=0:=by simp [v,hst,h0i]
  have hvj : (w₀+τ • v) (s j)≠0:=by simpa [v,h0j] using hτ
  have hiY : y∈E.get i:=h1.mpr hvi
  have hiff : y∈E.get i ↔ y∈E.get j:=
    Iff.of_eq (congrArg (fun S : Set W=>(⟨y,hyW⟩ : W)∈S) hTrace)
  exact hvj (h2.mp (hiff.mp hiY))

theorem incident_member_selection (hn : 0<n) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n W E) (p : W) (E₀ : List (Set X))
    (hE₀ : ∀H∈E₀,H∈E) (H : Set X) (hH : H∈E) (hp : p.val∈H) :
    (Subtype.val : W→X) ⁻¹' H∈E₀.map ((Subtype.val : W→X) ⁻¹' ·) ↔ H∈E₀ := by
  constructor
  · intro ht
    obtain ⟨K,hK,hTrace⟩:=List.mem_map.mp ht
    obtain ⟨i,rfl⟩:=List.mem_iff_get.mp hH
    obtain ⟨j,hj⟩:=List.mem_iff_get.mp (hE₀ K hK)
    have hpK : p.val∈K:=by
      have heq:=congrArg (fun S : Set W=>p∈S) hTrace
      exact (Iff.of_eq heq).mpr hp
    rw [←hj] at hTrace hpK
    have hij:=incident_trace_indices_injective hn hE hT p hp hpK hTrace.symm
    simpa only [hij,hj] using hK
  · exact fun h=>List.mem_map_of_mem h

end
end Hironaka.HironakaActualNativeSectionIncidentBoundary
