/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpSingleBoundaryTraceCentre
import Hironaka.Blowup.NormalCrossingsInvariance

set_option autoImplicit false

/-!
# Genuine open recognition of the original pointwise normal-crossings locus

The original adapted-coordinate witnesses are transported to actual nearby preferred
charts. Closed finite families prevent new incident members from appearing. The
result identifies the literal original good locus with the already constructed union
of actual NC neighborhoods, and hence upgrades the same sharp first trace blowup.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSharpNormalCrossingsOpenLocus

open Hironaka.BlowupSequences Hironaka.RegularPatchNeighborhood NormalCrossings BlowupTowers
  Hironaka.HolomorphicIdealSheaves MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpSingleBoundaryTraceCentre

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem sub_mem_coordSubspace_iff {S : Finset (Fin n)} {c z : ComplexModel n}
    (hc : c ∈ coordSubspace S) : z - c ∈ coordSubspace S ↔ z ∈ coordSubspace S := by
  constructor
  · intro h j hj
    have hz := h j hj
    simpa only [PiLp.sub_apply, hc j hj, sub_zero] using hz
  · intro h j hj
    simp only [PiLp.sub_apply, h j hj, hc j hj, sub_zero]

/-- The genuine original flattening, transported through the actual nearby chart and
translated by its actual value, flattens every member incident at the new point. -/
theorem coordinateFamilyAt_of_flattening {ι : Type*} {A : ι → Set M}
    {S : ι → Finset (Fin n)} {x y : M}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hflat : ∀ i, x ∈ A i → ∀ {z : M},
      z ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val z ∈ Φ.source →
      (z ∈ A i ↔ Φ.toFun ((complexChartAt (n := n) x).val z) ∈ coordSubspace (S i)))
    (hy : y ∈ (complexChartAt (n := n) x).val.source)
    (hyΦ : (complexChartAt (n := n) x).val y ∈ Φ.source)
    (hseen : ∀ i, y ∈ A i → x ∈ A i) : IsCoordinateFamilyAt n A S y := by
  set ey := (complexChartAt (n := n) y).val with hey
  set T := chartTransition (complexChartAt (n := n) y) (complexChartAt (n := n) x) with hT
  set c := Φ.toFun ((complexChartAt (n := n) x).val y) with hc
  have hTsource :
      T.source = ey.target ∩ ey.symm ⁻¹' (complexChartAt (n := n) x).val.source := by
    simp [hT, chartTransition, hey]
  have hTapply : ∀ z, T z = (complexChartAt (n := n) x).val (ey.symm z) := fun _ => rfl
  have hTholo := differentiableOn_chartTransition (complexChartAt (n := n) y)
    (complexChartAt (n := n) x)
  have hTsymmholo := differentiableOn_chartTransition_symm (complexChartAt (n := n) y)
    (complexChartAt (n := n) x)
  have hyey : y ∈ ey.source := mem_complexChartAt_source y
  let Ψ : LocalHolomorphicEquivAt (n := n) (ey y) :=
    { source := T.source ∩ T ⁻¹' Φ.source
      target := (fun v => v + c) ⁻¹' (Φ.target ∩ Φ.invFun ⁻¹' T.target)
      isOpen_source := T.isOpen_inter_preimage Φ.isOpen_source
      isOpen_target :=
        (Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target
          T.open_target).preimage (continuous_id.add continuous_const)
      center_mem_source := by
        refine ⟨?_, ?_⟩
        · rw [hTsource]
          exact ⟨ey.map_source hyey, by simpa [ey.left_inv hyey] using hy⟩
        · simpa [mem_preimage, hTapply, ey.left_inv hyey] using hyΦ
      toFun := fun z => Φ.toFun (T z) - c
      invFun := fun v => T.symm (Φ.invFun (v + c))
      toFun_holomorphic :=
        (Φ.toFun_holomorphic.comp (hTholo.mono inter_subset_left)
          (fun _ hz => hz.2)).sub_const c
      invFun_holomorphic :=
        hTsymmholo.comp
          (Φ.invFun_holomorphic.comp (differentiableOn_id.add_const c) (fun _ hv => hv.1))
          (fun _ hv => hv.2)
      mapsTo_toFun := by
        intro z hz
        refine ⟨?_, ?_⟩
        · simpa using Φ.mapsTo_toFun hz.2
        · simp only [mem_preimage, sub_add_cancel, Φ.left_inv _ hz.2]
          exact T.map_source hz.1
      mapsTo_invFun := by
        intro v hv
        refine ⟨T.map_target hv.2, ?_⟩
        simp only [mem_preimage, T.right_inv hv.2]
        exact Φ.mapsTo_invFun hv.1
      left_inv := by
        intro z hz
        simp only [sub_add_cancel, Φ.left_inv _ hz.2]
        exact T.left_inv hz.1
      right_inv := by
        intro v hv
        simp only [T.right_inv hv.2, Φ.right_inv _ hv.1, add_sub_cancel_right] }
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro z hz
    have := hz.1
    rw [hTsource] at this
    exact this.1
  · change Φ.toFun (T (ey y)) - c = 0
    rw [hTapply, ey.left_inv hyey, sub_self]
  · intro i hyi z hz hzΨ
    change ey z ∈ T.source ∩ T ⁻¹' Φ.source at hzΨ
    change z ∈ A i ↔ Φ.toFun (T (ey z)) - c ∈ coordSubspace (S i)
    have hTz : T (ey z) = (complexChartAt (n := n) x).val z := by
      rw [hTapply, ey.left_inv hz]
    have hsrc := hzΨ.1
    rw [hTsource] at hsrc
    have hzx : z ∈ (complexChartAt (n := n) x).val.source := by
      simpa [mem_preimage, ey.left_inv hz] using hsrc.2
    have hzΦ : (complexChartAt (n := n) x).val z ∈ Φ.source := by
      simpa [mem_preimage, hTz] using hzΨ.2
    have hcSi : c ∈ coordSubspace (S i) := (hflat i (hseen i hyi) hy hyΦ).mp hyi
    rw [hTz, sub_mem_coordSubspace_iff hcSi]
    exact hflat i (hseen i hyi) hzx hzΦ

theorem eventually_incident_subset {ι : Type*} [Fintype ι] (A : ι → Set M)
    (hclosed : ∀ i, IsClosed (A i)) (x : M) :
    ∀ᶠ y in 𝓝 x, ∀ i, y ∈ A i → x ∈ A i := by
  classical
  apply eventually_all.mpr
  intro i
  by_cases hx : x ∈ A i
  · exact Eventually.of_forall fun _ _ => hx
  · filter_upwards [(hclosed i).isOpen_compl.mem_nhds hx] with y hy hyA
    exact False.elim (hy hyA)

/-- True closed finite original families have actual stable adapted neighborhoods. -/
theorem eventually_coordinateFamilyAt {ι : Type*} [Fintype ι] {A : ι → Set M}
    {S : ι → Finset (Fin n)} {x : M} (hclosed : ∀ i, IsClosed (A i))
    (hx : IsCoordinateFamilyAt n A S x) : ∀ᶠ y in 𝓝 x, IsCoordinateFamilyAt n A S y := by
  obtain ⟨Φ, -, -, hflat⟩ := hx
  have hopen : IsOpen ((complexChartAt (n := n) x).val.source ∩
      (complexChartAt (n := n) x).val ⁻¹' Φ.source) :=
    (complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source Φ.isOpen_source
  have hxD : x ∈ (complexChartAt (n := n) x).val.source ∩
      (complexChartAt (n := n) x).val ⁻¹' Φ.source :=
    ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩
  filter_upwards [hopen.mem_nhds hxD, eventually_incident_subset A hclosed x] with y hy hseen
  exact coordinateFamilyAt_of_flattening Φ hflat hy.1 hy.2 hseen

/-- The literal pointwise integrand of the original normal-crossings definition. -/
def normalCrossingsAt (W : Set M) (E : List (Set M)) (x : M) : Prop :=
  ∃ (S₀ : Finset (Fin n)) (S : Fin E.length → Finset (Fin n)),
    IsCoordinateFamilyAt n (fun o : Option (Fin E.length) => o.elim W fun i => E.get i)
      (fun o => o.elim S₀ S) x ∧
      ∀ i, x ∈ E.get i → (S i).card = 1

/-- The actual original boundary cardinalities propagate with their real incident sets. -/
theorem eventually_normalCrossingsAt {W : Set M} {E : List (Set M)} {x : M}
    (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H) (hx : normalCrossingsAt (n := n) W E x) :
    ∀ᶠ y in 𝓝 x, normalCrossingsAt (n := n) W E y := by
  classical
  obtain ⟨S₀,S,hfamily,hcard⟩ := hx
  let A : Option (Fin E.length) → Set M := fun o => o.elim W fun i => E.get i
  have hclosed : ∀ i, IsClosed (A i) := by
    intro i
    cases i with
    | none => exact hW
    | some i => exact hE _ (List.get_mem E i)
  filter_upwards [eventually_coordinateFamilyAt hclosed hfamily,
    eventually_incident_subset A hclosed x] with y hy hseen
  exact ⟨S₀,S,hy,fun i hi => hcard i (hseen (some i) hi)⟩

/-- True open inclusions retain the original pointwise carrier and singleton boundary. -/
theorem normalCrossingsAt_singleton_preimage_val_iff {U : TopologicalSpace.Opens M}
    {W H : Set M} {x : U} :
    normalCrossingsAt (n := n) ((Subtype.val : U → M) ⁻¹' W) [((Subtype.val : U → M) ⁻¹' H)] x ↔
      normalCrossingsAt (n := n) W [H] (x : M) := by
  have hA : (fun o : Option (Fin 1) => (Subtype.val : U → M) ⁻¹' (o.elim W fun i => [H].get i)) =
      (fun o : Option (Fin 1) => o.elim ((Subtype.val : U → M) ⁻¹' W)
        fun i => [((Subtype.val : U → M) ⁻¹' H)].get i) := by
    funext o
    cases o <;> simp
  unfold normalCrossingsAt
  constructor
  · rintro ⟨S₀,S,hfamily,hcard⟩
    refine ⟨S₀,S,?_,?_⟩
    · apply NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff.mp
      change IsCoordinateFamilyAt n
        (fun o : Option (Fin 1) => (Subtype.val : U → M) ⁻¹' (o.elim W fun i => [H].get i))
        (fun o => o.elim S₀ S) x
      rw [hA]
      exact hfamily
    · simpa using hcard
  · rintro ⟨S₀,S,hfamily,hcard⟩
    refine ⟨S₀,S,?_,?_⟩
    · have hpre := NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff.mpr hfamily
      change IsCoordinateFamilyAt n
        (fun o : Option (Fin 1) => (Subtype.val : U → M) ⁻¹' (o.elim W fun i => [H].get i))
        (fun o => o.elim S₀ S) x at hpre
      rw [hA] at hpre
      exact hpre
    · simpa using hcard

universe u
variable {X : CMfd.{u} n}

/-- The genuine pointwise original NC witness constructs an entire actual NC open. -/
theorem normalCrossingsAt_iff_mem_originalSmoothNCRegion {W H : Set X} {x : X}
    (hW : IsClosed W) (hH : IsClosed H) (hxW : x ∈ W) :
    normalCrossingsAt (n := n) W [H] x ↔ x ∈ originalSmoothNCRegion W H := by
  constructor
  · intro hx
    have hev := eventually_normalCrossingsAt hW (by simpa using hH) hx
    obtain ⟨O,hOsub,hOopen,hxO⟩ := mem_nhds_iff.mp hev
    let U : TopologicalSpace.Opens X := ⟨O,hOopen⟩
    refine ⟨U,hxO,?_⟩
    intro y _
    exact normalCrossingsAt_singleton_preimage_val_iff.mpr (hOsub y.property)
  · rintro ⟨U,hxU,hU⟩
    exact normalCrossingsAt_singleton_preimage_val_iff.mp (hU ⟨x,hxU⟩ hxW)

/-- The entire actual good locus, including points outside the original carrier. -/
def originalPointwiseGoodLocus (W H : Set X) : Set X :=
  Wᶜ ∪ {x | x ∈ W ∧ normalCrossingsAt (n := n) W [H] x}

/-- A literal whole original set identity, with no caller neighborhood premise. -/
theorem originalPointwiseGoodLocus_eq_originalSmoothNCRegion {W H : Set X}
    (hW : IsClosed W) (hH : IsClosed H) :
    originalPointwiseGoodLocus W H = originalSmoothNCRegion W H := by
  ext x
  by_cases hxW : x ∈ W
  · simpa only [originalPointwiseGoodLocus,mem_union,mem_compl_iff,mem_ofPred_eq,
      hxW,not_true_eq_false,false_or,true_and] using
      normalCrossingsAt_iff_mem_originalSmoothNCRegion hW hH hxW
  · have hxR : x ∈ originalSmoothNCRegion W H := by
      let U : TopologicalSpace.Opens X := ⟨Wᶜ,hW.isOpen_compl⟩
      refine ⟨U,hxW,?_⟩
      intro y hy
      exact False.elim (y.property hy)
    simp only [originalPointwiseGoodLocus,mem_union,mem_compl_iff,mem_ofPred_eq,
      hxW,not_false_eq_true,true_or,hxR]

theorem originalPointwiseGoodLocus_isOpen {W H : Set X}
    (hW : IsClosed W) (hH : IsClosed H) : IsOpen (originalPointwiseGoodLocus W H) := by
  rw [originalPointwiseGoodLocus_eq_originalSmoothNCRegion hW hH]
  exact originalSmoothNCRegion_isOpen W H

/-- The literal original trace-order-two defect excludes every true pointwise good point. -/
theorem originalTraceCosupp_disjoint_pointwiseGoodLocus (hn : 0 < n) {W H : Set X}
    (hW : IsClosed W) (hE : IsSNCDivisor n [H]) (hdense : W ⊆ closure (W \ H)) :
    Disjoint (originalBoundaryTraceMarked W H).cosupp (originalPointwiseGoodLocus W H) := by
  rw [originalPointwiseGoodLocus_eq_originalSmoothNCRegion hW (hE.1 H (by simp))]
  exact originalBoundaryTraceMarked_cosupp_disjoint_goodRegion hn hE hdense

/-- Original inputs internally select the SAME actual modified maximum centre and
produce its real blowup, now isomorphic over EVERY original pointwise good NC point. -/
theorem exists_originalPointwisePreservingTraceBlowup (hn : 0 < n) {W H : Set X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n [H])
    {d : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ H)) (hK : IsCompact W)
    (hbad : (originalBoundaryTraceMarked W H).cosupp.Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),
      C.Nonempty ∧ (originalBoundaryTraceMarked W H).IsAdmissibleCentre C ∧
      C ⊆ W ∩ H ∧ Disjoint C (originalPointwiseGoodLocus W H) ∧
      (⟨univ,[H],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (originalPointwiseGoodLocus W H) ∧
      IsClosedSubmanifold n (strictTransform n π W) ∧
      IsSNCDivisor n [BlowupStrictSubmanifold.geoStrictTransform π C H,π ⁻¹' C] ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (originalBoundaryTraceMarked W H) (.refl : BlowupTower X X))
        (originalBoundaryTraceMarked W H).cosupp := by
  rw [originalPointwiseGoodLocus_eq_originalSmoothNCRegion hW.1 (hE.1 H (by simp))]
  exact exists_originalBoundaryTraceBlowup hn hW hE hd hreg hdense hK hbad

end
end Hironaka.HironakaSharpNormalCrossingsOpenLocus
