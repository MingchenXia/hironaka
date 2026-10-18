/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveLocallyFiniteBoundary

/-! Actual whole ordered boundary decomposition and genuine adapted
coordinates for ALL zero-extended positions before global SNC descent. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalBoundaryCoordinates
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualCurveBirthBoundaryOverlaps HironakaSharpActualCurveLocallyFiniteBoundary
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveStrictSetOverlaps HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveLocalRangeBiholomorphism HironakaSharpActualCurveGluedStrictSets
  HironakaSharpActualCurveTopologicalGluing NormalCrossings NormalCrossingsInvariance
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A genuine finite tower gives the ENTIRE ordered original-plus-birth
equation, independently of carriers, ideals or TEST certificates. -/
theorem boundary_geoTransformAlong_decomposition (M K : MarkedIdeal n X) (hK : K.E=[]) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong M T).E=M.E.map (strictAlong T) ++ (geoTransformAlong K T).E
  | _,.refl => by
    simp only [geoTransformAlong_refl,hK,List.append_nil]
    exact (List.map_id' _).symm
  | _,.step T C π hπ => by
    simp only [geoTransformAlong_step,geoTransform_E,
      boundary_geoTransformAlong_decomposition M K hK T,List.map_append,List.map_map,List.append_assoc]
    rfl

private theorem readout_index_lt {Z : Type u} {E : List (Set Z)} {x : Z} {k : ℕ}
    (hx : x∈boundaryReadout E k) : k<E.length := by
  by_contra hk
  rw [boundaryReadout,List.getD_eq_default E ∅ (Nat.le_of_not_gt hk)] at hx
  exact hx

private theorem readout_eq_get {Z : Type u} (E : List (Set Z)) (k : ℕ) (hk : k<E.length) :
    boundaryReadout E k=E.get ⟨k,hk⟩ := List.getD_eq_get E ∅ ⟨k,hk⟩

/-- The actual finite SNC frame extends to ALL natural positions. Empty
births/defaults have no incidence and are never erased from the index type. -/
theorem exists_readout_snc_coordinates (E : List (Set X)) (hE : IsSNCDivisor n E) (x : X) :
    ∃ S : ℕ → Finset (Fin n),
      IsCoordinateFamilyAt n (fun k => boundaryReadout E k) S x ∧
        (∀ k,x∈boundaryReadout E k → (S k).card=1) ∧
          Set.InjOn S {k | x∈boundaryReadout E k} := by
  obtain ⟨s,hcoord,hcard,hinj⟩ := hE.2 x
  let S : ℕ → Finset (Fin n) := fun k => if hk : k<E.length then s ⟨k,hk⟩ else ∅
  refine ⟨S,?_,?_,?_⟩
  · obtain ⟨Φ,hsrc,h0,hfamily⟩ := hcoord
    refine ⟨Φ,hsrc,h0,?_⟩
    intro k hx y hy hyΦ
    have hk := readout_index_lt hx
    have hxGet : x∈E.get ⟨k,hk⟩ := by rwa [←readout_eq_get E k hk]
    change (y∈boundaryReadout E k ↔ Φ.toFun ((complexChartAt (n := n) x).val y)∈coordSubspace (S k))
    rw [readout_eq_get E k hk]
    simpa only [S,dif_pos hk] using hfamily ⟨k,hk⟩ hxGet hy hyΦ
  · intro k hx
    have hk := readout_index_lt hx
    simp only [S,dif_pos hk]
    exact hcard ⟨k,hk⟩ (by rwa [←readout_eq_get E k hk])
  · intro a ha b hb hab
    have hA := readout_index_lt ha
    have hB := readout_index_lt hb
    have ha' : x∈E.get ⟨a,hA⟩ := by rwa [←readout_eq_get E a hA]
    have hb' : x∈E.get ⟨b,hB⟩ := by rwa [←readout_eq_get E b hB]
    have hs : s ⟨a,hA⟩=s ⟨b,hB⟩ := by simpa only [S,dif_pos hA,dif_pos hB] using hab
    exact congrArg Fin.val (hinj ha' hb' hs)

/-- The SAME real finite transverse frame supplies the curve-normal set
and every incident natural-position hyperplane/disjointness assertion. -/
theorem exists_readout_transverse_coordinates (N : Set X) (E : List (Set X))
    (hT : IsTransverse n N E) (x : X) (hx : x∈N) :
    ∃ (S₀ : Finset (Fin n)) (S : ℕ → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ℕ => o.elim N (fun k => boundaryReadout E k))
        (fun o => o.elim S₀ S) x ∧
      ∀ k,x∈boundaryReadout E k → (S k).card=1 ∧ Disjoint (S k) S₀ := by
  obtain ⟨S₀,s,hcoord,hsets⟩ := hT x hx
  let S : ℕ → Finset (Fin n) := fun k => if hk : k<E.length then s ⟨k,hk⟩ else ∅
  refine ⟨S₀,S,?_,?_⟩
  · obtain ⟨Φ,hsrc,h0,hfamily⟩ := hcoord
    refine ⟨Φ,hsrc,h0,?_⟩
    rintro (_|k) hx' y hy hyΦ
    · exact hfamily none hx' hy hyΦ
    · have hk : k<E.length := readout_index_lt hx'
      have hxGet : x∈E.get ⟨k,hk⟩ := by rwa [←readout_eq_get E k hk]
      change (y∈boundaryReadout E k ↔ Φ.toFun ((complexChartAt (n := n) x).val y)∈coordSubspace (S k))
      rw [readout_eq_get E k hk]
      simpa only [S,dif_pos hk,Option.elim_some] using hfamily (some ⟨k,hk⟩) hxGet hy hyΦ
  · intro k hx'
    have hk := readout_index_lt hx'
    simp only [S,dif_pos hk]
    exact hsets ⟨k,hk⟩ (by rwa [←readout_eq_get E k hk])

/-- True inverse holomorphicity and both inverse laws transport a genuine
adapted frame, preserving its actual index assignment. -/
theorem coordinateFamilyAt_diffeomorph {ι : Type*}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    {A : ι → Set X} {B : ι → Set Y} {S : ι → Finset (Fin n)} (x : X)
    (hAB : ∀ i y,y∈A i ↔ e y∈B i) (hA : IsCoordinateFamilyAt n A S x) :
    IsCoordinateFamilyAt n B S (e x) := by
  have hInv := MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
    e.symm.contMDiff e.contMDiff e.symm_apply_apply e.apply_symm_apply (e x)
  apply isCoordinateFamilyAt_of_preimage e.symm.contMDiff hInv isOpen_univ (mem_univ _)
  · intro i y _hy
    have h := hAB i (e.symm y)
    rw [e.apply_symm_apply] at h
    exact h.symm
  · simpa only [e.symm_apply_apply] using hA

attribute [local instance] endpointChartedSpace

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- The retained ORIGINAL sharp geometry gives true local transversality
to the ENTIRE actual ambient ledger, using the whole list equation first. -/
theorem original_localBoundary_transverse (i : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let M := geometricTemplate (univ : Set (A.openSet i)) (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·))
    IsTransverse n (localStrictSet A W i) (geoTransformAlong M ((A.prefixTower i).append (A.tail i))).E := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let T := (A.prefixTower i).append (A.tail i)
  let M := geometricTemplate (X := CMfd.of (n := n) U) univ EU
  let K := geometricTemplate (X := CMfd.of (n := n) U) WU []
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,_hTest,_hZ,_hD,_hProper,_hDom,_hSNC,hTrans,_hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr i
  have hEq := boundary_geoTransformAlong_decomposition M K rfl T
  change IsTransverse n (strictAlong T WU) (geoTransformAlong M T).E
  rw [hEq]
  rw [N_geoTransformAlong] at hTrans
  exact hTrans

theorem original_localBoundary_snc_coordinates (i : X)
    (z : (originalEndpointHistories hn hW hE hdense hr).finalSpace i) :
    ∃ S : ℕ → Finset (Fin n),
      IsCoordinateFamilyAt n
        (fun k => localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k) S z ∧
      (∀ k,z∈localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k → (S k).card=1) ∧
        Set.InjOn S {k | z∈localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k} :=
  exists_readout_snc_coordinates _ (original_localBoundary_ambient_geometry hn hW hE hdense hr i).2 z

theorem original_localBoundary_transverse_coordinates (i : X)
    (z : (originalEndpointHistories hn hW hE hdense hr).finalSpace i)
    (hz : z∈localStrictSet (originalEndpointHistories hn hW hE hdense hr) W i) :
    ∃ (S₀ : Finset (Fin n)) (S : ℕ → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ℕ => o.elim
        (localStrictSet (originalEndpointHistories hn hW hE hdense hr) W i)
        (fun k => localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k))
        (fun o => o.elim S₀ S) z ∧
      ∀ k,z∈localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k →
        (S k).card=1 ∧ Disjoint (S k) S₀ :=
  exists_readout_transverse_coordinates _ _
    (original_localBoundary_transverse hn hW hE hdense hr i) z hz

/-- Actual chart representatives and the whole readout pullback dictionary
construct global adapted coordinates, with no supplied coordinate certificate. -/
theorem original_globalBoundary_snc_coordinates
    (q : originalEndpointManifold hn hW hE hdense hr) :
    ∃ S : ℕ → Finset (Fin n),
      IsCoordinateFamilyAt n (originalGluedBoundaryReadout hn hW hE hdense hr) S q ∧
      (∀ k,q∈originalGluedBoundaryReadout hn hW hE hdense hr k → (S k).card=1) ∧
        Set.InjOn S {k | q∈originalGluedBoundaryReadout hn hW hE hdense hr k} := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
  obtain ⟨S,hcoord,hcard,hinj⟩ := original_localBoundary_snc_coordinates hn hW hE hdense hr i z
  let e := localBiholomorphism A hc i
  have hAB : ∀ k w,w∈localBoundaryReadout A E i k ↔
      e w∈((Subtype.val : localRangeOpen A hc i → originalEndpointManifold hn hW hE hdense hr) ⁻¹'
        originalGluedBoundaryReadout hn hW hE hdense hr k) := by
    intro k w
    exact (mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i k w).symm
  have hRange := coordinateFamilyAt_diffeomorph e z hAB hcoord
  have hGlobal := isCoordinateFamilyAt_preimage_val_iff.mp hRange
  refine ⟨S,hGlobal,?_,?_⟩
  · intro k hk
    exact hcard k ((mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i k z).mp hk)
  · intro a ha b hb hab
    exact hinj ((mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i a z).mp ha)
      ((mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i b z).mp hb) hab

/-- The genuine global curve and ENTIRE indexed boundary have one actual
simultaneous holomorphic frame at every point of that same curve. -/
theorem original_globalBoundary_transverse_coordinates
    (q : originalEndpointManifold hn hW hE hdense hr)
    (hq : q∈originalGluedStrictSet hn hW hE hdense hr W) :
    ∃ (S₀ : Finset (Fin n)) (S : ℕ → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ℕ => o.elim
        (originalGluedStrictSet hn hW hE hdense hr W)
        (originalGluedBoundaryReadout hn hW hE hdense hr)) (fun o => o.elim S₀ S) q ∧
      ∀ k,q∈originalGluedBoundaryReadout hn hW hE hdense hr k →
        (S k).card=1 ∧ Disjoint (S k) S₀ := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
  have hz : z∈localStrictSet A W i := (mem_gluedStrictSet_iff A W hW.1 i z).mp hq
  obtain ⟨S₀,S,hcoord,hsets⟩ := original_localBoundary_transverse_coordinates hn hW hE hdense hr i z hz
  let e := localBiholomorphism A hc i
  have hAB : ∀ (o : Option ℕ) w,
      w∈o.elim (localStrictSet A W i) (fun k => localBoundaryReadout A E i k) ↔
      e w∈((Subtype.val : localRangeOpen A hc i → originalEndpointManifold hn hW hE hdense hr) ⁻¹'
        o.elim (originalGluedStrictSet hn hW hE hdense hr W)
          (originalGluedBoundaryReadout hn hW hE hdense hr)) := by
    rintro (_|k) w
    · exact (mem_gluedStrictSet_iff A W hW.1 i w).symm
    · exact (mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i k w).symm
  have hRange := coordinateFamilyAt_diffeomorph e z hAB hcoord
  have hGlobal := isCoordinateFamilyAt_preimage_val_iff.mp hRange
  refine ⟨S₀,S,hGlobal,?_⟩
  intro k hk
  exact hsets k ((mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i k z).mp hk)

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalBoundaryCoordinates
