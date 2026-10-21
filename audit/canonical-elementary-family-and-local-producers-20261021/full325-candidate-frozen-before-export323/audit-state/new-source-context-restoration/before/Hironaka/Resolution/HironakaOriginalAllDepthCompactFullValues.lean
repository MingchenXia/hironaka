/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullHistorySuperlevelsAnalytic
import Hironaka.Analytic.AnalyticDescendingChain
import Mathlib.Order.OrderIsoNat
/-! Actual original FULL compact/local/historical finite spectra at EVERY depth.
True analytic Noetherian stationarity and actual attained increasing values supply
finiteness internally; no caller value bound, finite spectrum or ambient compactness. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalAllDepthCompactFullValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HironakaOriginalFullHistorySuperlevelsAnalytic
  HironakaOriginalCompactUpperCutGlobalPhase ResolutionInvariantSegments StepOneLowerDomain
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual local analytic chain stationarity gives a real uniform cutoff on
ANY genuine compact K, without CompactSpace for the ambient manifold. -/
theorem analytic_descending_chain_stable_on_compact {A : ℕ → Set M}
    (hA : ∀ i,IsComplexAnalyticSubset (n := n) (A i)) (hanti : Antitone A)
    {K : Set M} (hK : IsCompact K) :
    ∃ N,∀ i,N ≤ i → A i ∩ K=A N ∩ K := by
  choose N U hU hpU hstab using AnalyticDescendingChain.exists_local_stable hA hanti
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover U hU (fun p _ => mem_iUnion.mpr ⟨p,hpU p⟩)
  refine ⟨t.sup N,fun i hi => ?_⟩
  ext x
  constructor
  · rintro ⟨hx,hxK⟩
    obtain ⟨p,hpt,hxp⟩ := mem_iUnion₂.mp (ht hxK)
    have hle : N p ≤ t.sup N := Finset.le_sup hpt
    have h1 := hstab p i (hle.trans hi)
    have h2 := hstab p (t.sup N) hle
    have hh : x ∈ A (N p) ∩ U p := h1 ▸ (show x ∈ A i ∩ U p from ⟨hx,hxp⟩)
    exact ⟨(h2.symm ▸ hh : x ∈ A (t.sup N) ∩ U p).1,hxK⟩
  · rintro ⟨hx,hxK⟩
    obtain ⟨p,hpt,hxp⟩ := mem_iUnion₂.mp (ht hxK)
    have hle : N p ≤ t.sup N := Finset.le_sup hpt
    have h1 := hstab p i (hle.trans hi)
    have h2 := hstab p (t.sup N) hle
    have hh : x ∈ A (N p) ∩ U p := h2 ▸ (show x ∈ A (t.sup N) ∩ U p from ⟨hx,hxp⟩)
    exact ⟨(h1.symm ▸ hh : x ∈ A i ∩ U p).1,hxK⟩

/-- Real analytic full cuts and the true well-founded value order force actual
compact finite spectra; neither a bound nor finite values is input. -/
theorem finite_image_of_actual_analytic_full_cuts {Λ : Type v} [LinearOrder Λ] [WellFoundedLT Λ]
    (f : M → Λ) (C : Set M)
    (hA : ∀ b,IsComplexAnalyticSubset (n := n) {x | x ∈ C ∧ b ≤ f x})
    {K : Set M} (hK : IsCompact K) : (f '' (K ∩ C)).Finite := by
  by_contra hno
  let : Infinite (f '' (K ∩ C)) := infinite_coe_iff.mpr hno
  obtain ⟨a,ha | ha⟩ := Infinite.exists_strictMono_or_strictAnti (f '' (K ∩ C))
  · let b : ℕ → Λ := fun i => (a i : Λ)
    have hmono : StrictMono b := fun i j hij => ha hij
    let A : ℕ → Set M := fun i => {x | x ∈ C ∧ b i ≤ f x}
    have hanti : Antitone A := fun i j hij _ hx => ⟨hx.1,(hmono.monotone hij).trans hx.2⟩
    obtain ⟨N,hN⟩ := analytic_descending_chain_stable_on_compact (fun i => hA (b i)) hanti hK
    obtain ⟨x,hx,hfx⟩ : ∃ x ∈ K ∩ C,f x=b N := (a N).property
    have hxN : x ∈ A N := ⟨hx.2,by rw [hfx]⟩
    have hxNext : x ∈ A (N+1) ∩ K := (hN (N+1) (Nat.le_succ N)).symm ▸ ⟨hxN,hx.1⟩
    exact (not_le_of_gt (hmono (Nat.lt_succ_self N))) (hxNext.1.2.trans_eq hfx)
  · exact not_strictAnti_of_wellFoundedLT (fun i => (a i : Λ)) (fun i j hij => ha hij)

variable {X Y : CMfd.{u} n}

/-- ONLY original domain and actual ORIGINAL canonical history give true FULL
finite spectra at EVERY depth on ANY genuine compact window. -/
theorem original_all_depth_full_compact_values (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) {K : Set Y} (hK : IsCompact K) :
    (((invFamily hn d).inv m T) '' (K ∩ (geoTransformAlong m T).cosupp)).Finite :=
  finite_image_of_actual_analytic_full_cuts ((invFamily hn d).inv m T) (geoTransformAlong m T).cosupp
    (fun b => original_all_depth_full_history_global_analytic hn d m h T hc b) hK

/-- Genuine local compactness internally supplies an actual open finite spectrum. -/
theorem original_all_depth_full_local_finite_values (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (p : Y) :
    ∃ U : Set Y,IsOpen U ∧ p ∈ U ∧
      (((invFamily hn d).inv m T) '' (U ∩ (geoTransformAlong m T).cosupp)).Finite := by
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel n) Y
  obtain ⟨K,hK,hpK⟩ := exists_compact_mem_nhds p
  exact ⟨interior K,isOpen_interior,mem_interior_iff_mem_nhds.mpr hpK,
    (original_all_depth_full_compact_values hn d m h T hc hK).subset
      (image_mono (inter_subset_inter_left _ interior_subset))⟩

/-- Every actual historical head value is read on the SAME compact current
carrier via its REAL tail projection, retaining all empty positions. -/
theorem original_all_depth_historical_full_compact_values (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) {K : Set Y} (hK : IsCompact K) (j : ℕ) :
    ((fun p : Y => (invFamily hn d).inv m (head T j) ((tail T j).proj p)) ''
      (K ∩ (geoTransformAlong m T).cosupp)).Finite := by
  have ht := (invFamily hn d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hCS := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hKc := hK.inter_right hCS.isClosed
  have hhead := isCanonical_head m ((invFamily hn d).inv m) T j hc
  have hsplit := (isGeoTestTower_iff_head_tail m T j).mp ht
  have hH := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T j) hsplit.1
  have hmaps : MapsTo (tail T j).proj (K ∩ (geoTransformAlong m T).cosupp)
      (geoTransformAlong m (head T j)).cosupp := by
    intro p hp
    apply proj_mem_cosupp_of_mem_cosupp hH.isWellFormed.isClosedSubmanifold_N
      hH.isWellFormed.isCoherent (tail T j) hsplit.2
    rw [← geoTransformAlong_append,head_append_tail]
    exact hp.2
  have hfinite := original_all_depth_full_compact_values hn d m h (head T j) hhead
    (hKc.image (tail T j).contMDiff_proj.continuous)
  refine hfinite.subset ?_
  rintro a ⟨p,hp,rfl⟩
  exact ⟨(tail T j).proj p,⟨⟨p,hp,rfl⟩,hmaps hp⟩,rfl⟩

/-- ALL actual historical original full-value tuples have a genuine finite image. -/
theorem original_all_depth_historical_full_tuple_compact_values (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) {K : Set Y} (hK : IsCompact K) :
    ((fun p : Y => fun j : Fin (T.length+1) =>
      (invFamily hn d).inv m (head T j) ((tail T j).proj p)) ''
        (K ∩ (geoTransformAlong m T).cosupp)).Finite := by
  let P : Fin (T.length+1) → Set (ValTy d) := fun j =>
    (fun p : Y => (invFamily hn d).inv m (head T j) ((tail T j).proj p)) ''
      (K ∩ (geoTransformAlong m T).cosupp)
  have hP : ∀ j,(P j).Finite := fun j => original_all_depth_historical_full_compact_values hn d m h T hc hK j
  refine (Set.Finite.pi hP).subset ?_
  rintro a ⟨p,hp,rfl⟩
  intro j _
  exact ⟨p,hp,rfl⟩

end
end Hironaka.HironakaOriginalAllDepthCompactFullValues
