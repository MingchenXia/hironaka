/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.TowerCosupportCentreCounting
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Analytic.GrowingSeqTail
import Hironaka.Resolution.HironakaLocalPrincipalization
import Mathlib.Topology.Compactness.LocallyFinite


import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-! Actual curve strict-transform fibres from genuine monomial charts.
Blueprint `hironaka-curve-strict-fibres-extension.tex`.
Actual global locally finite and locally resolving sequences are internally
produced in genuine carrier dimension at most one; higher-dimensional G3
and an analytic final direct-limit space remain open. -/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaCurveStrictFibres

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupStrictSubmanifold BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity

noncomputable section

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C N : Set X} {π : Y → X} {x : X}
  {Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)} {k : ℕ}

/-- The actual monomial local inverses show that a strict-transform fibre
over a point centre on a genuine carrier of dimension at most one is a
subsingleton, with no injectivity or fibre certificate as input. -/
theorem subsingleton_fibre_of_flat_dimension_le_one (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (hzero : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hflatC : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n 0))
    (hflatN : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k))
    (hk : k ≤ 1) : (geoStrictTransform π C N ∩ π ⁻¹' {x}).Subsingleton := by
  intro z hz z' hz'
  have hzero' : Φ.toFun (chartAt (ComplexModel n) x x) = 0 := hzero
  have hzx : π z = x := hz.2
  have hz'x : π z' = x := hz'.2
  have hzflat : π z ∈ flatDomain Φ := by
    rw [hzx]; exact ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩
  obtain ⟨j, _, O, _, hzO, W, _, _, _, hstrict⟩ :=
    exists_local_geoStrictTransform hπ hΦsrc hflatC hflatN hzflat
  have hjk := ((hstrict z hzO).mp hz.1).1
  have hj0 : j.1 = 0 := by omega
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, _⟩ := existsUnique_monomialLift hπ hΦsrc hflatC (Nat.zero_le j.1)
  have hzeroMem : (0 : ComplexModel n) ∈ monomialDomain Φ 0 j := by
    have hmon0 : monomial 0 j (0 : ComplexModel n) = 0 := by ext i; simp
    change monomial 0 j (0 : ComplexModel n) ∈ Φ.target
    rw [hmon0, ← hzero]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have heq : ∀ u ∈ geoStrictTransform π C N, π u = x →
      u = ℓ (LiftedOpen.mk _ 0 hzeroMem) := by
    intro u hu hux
    have huflat : π u ∈ flatDomain Φ := by
      rw [hux]; exact ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩
    obtain ⟨j', _, O', _, huO, W', _, hWmem, hℓ, hstrict'⟩ :=
      exists_local_geoStrictTransform hπ hΦsrc hflatC hflatN huflat
    obtain ⟨hj'k, hWplane⟩ := (hstrict' u huO).mp hu
    have hj' : j' = j := by apply Fin.ext; omega
    subst j'
    let p := LiftedOpen.mk (monomialDomain Φ 0 j) (W' u) (hWmem u huO)
    have hℓu : ℓ p = u := hℓ ℓ hℓs hℓπ u huO (hWmem u huO)
    have hπu : π u = monomialChart Φ 0 j p := by
      rw [← hℓu]; exact congrFun hℓπ p
    have hWj : W' u j = 0 := by
      have hc := flatCoord_monomialChart hΦsrc p j
      rw [← hπu, hux] at hc
      simpa [flatCoord, hzero', p] using hc.symm
    have hWzero : W' u = 0 := by
      ext i
      by_cases hij : i = j
      · subst i; exact hWj
      · have hki : k ≤ i.1 := by
          have : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
          omega
        exact hWplane i hki
    rw [← hℓu]
    congr 1
    apply (LiftedOpen.isEmbedding_toModel _).injective
    exact hWzero
  exact (heq z hz.1 hzx).trans (heq z' hz'.1 hz'x).symm

/-- Genuine zero-dimensional centre regularity and genuine dimension-at-most-one
carrier regularity produce actual injectivity of the blowup projection on its
actual strict transform, even for infinite disconnected centres. -/
theorem injOn_strictTransform_of_zero_dimensional_centre (hπ : IsBlowupAlong n C π)
    (hC : ∀ y ∈ C, RegularAtDim (n := n) C y 0)
    (hN : ∀ y ∈ N, ∃ k : ℕ, k ≤ 1 ∧ RegularAtDim (n := n) N y k)
    (hCN : C ⊆ N) : InjOn π (geoStrictTransform π C N) := by
  intro z hz z' hz' hzz'
  by_cases hxc : π z ∈ C
  · obtain ⟨k, hk, hNreg⟩ := hN _ (hCN hxc)
    obtain ⟨Φ, hsrc, hzero, hflat⟩ := NestedFlattening.exists_nested_flattening
      (Nat.zero_le k) (hC _ hxc) hNreg hCN
    exact subsingleton_fibre_of_flat_dimension_le_one hπ hsrc hzero
      (fun hy hyΦ => (hflat hy hyΦ).1) (fun hy hyΦ => (hflat hy hyΦ).2) hk
      ⟨hz, rfl⟩ ⟨hz', hzz'.symm⟩
  · exact (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.2.1
      hxc (by change π z' ∉ C; rw [← hzz']; exact hxc) hzz'

end
end Hironaka.HironakaCurveStrictFibres

namespace Hironaka.HironakaCurveStrictFibres

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOneDimensionalCanonicalSuperlevels PositiveDimensionalComponent
  BlowupStrictSubmanifold MarkedIdealBiholomorphism.MarkedIdeal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual coherent zero-dimensional cosupport neighbourhoods give genuine
regular dimension zero for every actual subset containing the point. -/
theorem regularAtDim_zero_of_subset_cosupport_of_isInvDomain_one
    {m : MarkedIdeal n M} (h : ResolutionInvariantSpec.IsInvDomain 1 m)
    {B : Set M} (hB : B ⊆ m.cosupp) {x : M} (hx : x ∈ B) :
    RegularAtDim (n := n) B x 0 := by
  have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
    h.isWellFormed.isCoherent h.isWellFormed.isClosedSubmanifold_N h.one_le_d
  have hxreg := regularAtDim_zero_of_analytic_dimLE_zero hA
    (dimLE_cosupport_of_isInvDomain h) (hB hx)
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hxreg
  exact RegularPointDimension.regularAtDim_of_inter_eq hU hxU
    (Subset.antisymm (fun y hy => ⟨by rw [hsub hy]; exact hx, hy.2⟩)
      (fun _ hy => ⟨hB hy.1, hy.2⟩)) hxreg

variable {X Y : CMfd.{u} n}

/-- Genuine domain data internally produce the centre's zero-dimensional
geometry and hence actual projection injectivity on the strict carrier. -/
theorem injOn_geoTransform_N_of_isInvDomain_one (m : MarkedIdeal n X)
    (h : ResolutionInvariantSpec.IsInvDomain 1 m) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hC : m.IsAdmissibleCentre C) :
    InjOn π (m.geoTransform C π).N := by
  exact injOn_strictTransform_of_zero_dimensional_centre hπ
    (fun _ hx => regularAtDim_zero_of_subset_cosupport_of_isInvDomain_one h hC.2.1 hx)
    h.dimLE hC.subset_N

/-- Every actual test-tower projection of a genuine carrier-dimension-one
domain is injective on its actual transformed carrier. -/
theorem injOn_proj_N_of_isInvDomain_one (m : MarkedIdeal n X)
    (h : ResolutionInvariantSpec.IsInvDomain 1 m) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower m T →
      InjOn T.proj (geoTransformAlong m T).N
  | _, .refl, _ => by intro _ _ _ _ heq; exact heq
  | _, .step T C π hπ, hT => by
    have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT.1
    have hπinj := injOn_geoTransform_N_of_isInvDomain_one _ hdom hπ hT.2
    have hproj := injOn_proj_N_of_isInvDomain_one m h T hT.1
    have hsub := geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      hdom.isWellFormed.isClosedSubmanifold_N.1 (C := C)
    change InjOn (T.proj ∘ π) (geoStrictTransform π C (geoTransformAlong m T).N)
    intro z hz z' hz' heq
    exact hπinj hz hz' (hproj (hsub hz) (hsub hz') heq)

/-- A genuine initial cosupport singleton neighbourhood stays a true
subsingleton along every actual restricted geometric test tower. -/
theorem subsingleton_cosupp_restrict_of_isInvDomain_one (m : MarkedIdeal n X)
    (h : ResolutionInvariantSpec.IsInvDomain 1 m) (U : TopologicalSpace.Opens X)
    (hsingle : (m.cosupp ∩ (U : Set X)).Subsingleton)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) :
    (geoTransformAlong (pullback (Subtype.val : U → X) m)
      (restrict U T)).cosupp.Subsingleton := by
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent U T hT]
  intro z hz z' hz'
  have hsub := TransformOffCentre.cosupp_geoTransformAlong_subset m
    h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T hT
  apply Subtype.ext
  exact injOn_proj_N_of_isInvDomain_one m h T hT ((geoTransformAlong m T).cosupp_subset_N hz)
    ((geoTransformAlong m T).cosupp_subset_N hz') (hsingle ⟨hsub hz, z.2⟩ ⟨hsub hz', z'.2⟩)

end
end Hironaka.HironakaCurveStrictFibres

namespace Hironaka.HironakaCurveStrictFibres

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOneDimensionalCanonicalSuperlevels MarkedIdealBiholomorphism.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual structural condition that every recorded centre is the
whole preceding genuine cosupport. It does not include finiteness,
resolution, invariant comparison or canonicality. -/
def WholeCosupportTower (m : MarkedIdeal n X) :
    {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => WholeCosupportTower m T ∧ C = (geoTransformAlong m T).cosupp

private theorem maxLocus_eq_of_subsingleton {Z Λ : Type*} [LinearOrder Λ]
    (f : Z → Λ) (A : Set Z) (hA : A.Subsingleton) :
    ResolutionDriver.maxLocus f A = A := by
  apply Subset.antisymm (fun _ hy => hy.1)
  intro y hy
  exact ⟨hy, fun z hz => by rw [hA hz hy]⟩

/-- Actual whole-cosupport prefixes become genuinely canonical on each
true initial singleton-cosupport neighbourhood, for any actual local value. -/
theorem isCanonical_restrict_of_whole_cosupport_tower {Λ : Type*} [LinearOrder Λ]
    (m : MarkedIdeal n X) (h : IsInvDomain 1 m) (U : TopologicalSpace.Opens X)
    (hsingle : (m.cosupp ∩ (U : Set X)).Subsingleton)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower (CMfd.of (n := n) U) Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), WholeCosupportTower m T →
      IsGeoTestTower m T → IsCanonical (pullback (Subtype.val : U → X) m) inv (restrict U T)
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hwhole, hT => by
    change IsCanonical _ inv (.step (restrict U T) ((Subtype.val) ⁻¹' C) _ _)
    refine ⟨isCanonical_restrict_of_whole_cosupport_tower m h U hsingle inv T hwhole.1 hT.1,
      Or.inr ?_⟩
    have hsingleT := subsingleton_cosupp_restrict_of_isInvDomain_one m h U hsingle T hT.1
    rw [maxLocus_eq_of_subsingleton _ _ hsingleT,
      ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
        h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent U T hT.1,
      hwhole.2]

/-- True canonicality of the actual restricted single-point branches gives
real compact-set count bounds for the whole-cosupport sequence, even though
it need not be globally canonical and no global maximum is assumed. -/
theorem exists_compact_count_bound_of_whole_cosupport_sequence (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 1 m) (s : GrowingSeq X)
    (hs : ∀ i, IsGeoTestTower m (s.stage i).2)
    (hwhole : ∀ i, WholeCosupportTower m (s.stage i).2)
    (K : Set X) (hK : IsCompact K) :
    ∃ b : ℕ, ∀ i, countCentresMeeting K (s.stage i).2 ≤ b := by
  classical
  have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
    h.isWellFormed.isCoherent h.isWellFormed.isClosedSubmanifold_N h.one_le_d
  have hdim := dimLE_cosupport_of_isInvDomain h
  have hdisc := isDiscrete_of_analytic_dimLE_zero hA hdim
  have hfin : (K ∩ m.cosupp).Finite :=
    (hK.inter_right hA.isClosed).finite (hdisc.mono inter_subset_right)
  let ι := ↥(K ∩ m.cosupp)
  let : Fintype ι := hfin.fintype
  have hnear : ∀ x : ι, ∃ U : TopologicalSpace.Opens X,
      (x : X) ∈ U ∧ (m.cosupp ∩ (U : Set X)).Subsingleton := by
    intro x
    obtain ⟨O, hO, hxO, hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero
      (regularAtDim_zero_of_analytic_dimLE_zero hA hdim x.2.2)
    exact ⟨⟨O, hO⟩, hxO, fun _ hy _ hz => (hsub hy).trans (hsub hz).symm⟩
  choose U hxU hsingle using hnear
  have hbound : ∀ x : ι, ∃ b : ℕ, ∀ i, countCentresMeeting ({(x : X)} : Set X) (s.stage i).2 ≤ b := by
    intro x
    have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val (U x) h
    have hcan : ∀ i, IsCanonical (pullback (Subtype.val : U x → X) m)
        ((CanonicalCentres.invFamily hn 1).inv (pullback (Subtype.val : U x → X) m))
        ((s.restrict (U x)).stage i).2 := by
      intro i
      exact isCanonical_restrict_of_whole_cosupport_tower m h (U x) (hsingle x) _
        (s.stage i).2 (hwhole i) (hs i)
    have hKsingle : IsCompact ((Subtype.val : U x → X) ⁻¹' ({(x : X)} : Set X)) := by
      have heq : (Subtype.val : U x → X) ⁻¹' ({(x : X)} : Set X) = {⟨(x : X), hxU x⟩} := by
        ext z
        simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
      rw [heq]
      exact isCompact_singleton
    obtain ⟨b, hb⟩ := (CanonicalCentres.invFamily hn 1).seqLocallyFinite
      (pullback (Subtype.val : U x → X) m) hdomU _ hKsingle (s.restrict (U x)) hcan
    refine ⟨b, fun i => ?_⟩
    rw [← s.count_restrict (U x) (by intro y hy; rw [mem_singleton_iff.mp hy]; exact hxU x) i]
    exact hb i
  choose b hb using hbound
  refine ⟨∑ x : ι, b x, fun i => ?_⟩
  have hcount : countCentresMeeting K (s.stage i).2 =
      countCentresMeeting (K ∩ m.cosupp) (s.stage i).2 := by
    have htest : IsGeoTestTower m (BlowupTower.refl.append (s.stage i).2) := by
      rw [BlowupTower.refl_append]; exact hs i
    exact TowerPreimageCompact.countCentresMeeting_eq_inter_cosupp
      h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent K .refl (s.stage i).2 htest
  rw [hcount]
  have hcover : K ∩ m.cosupp ⊆ ⋃ x ∈ (Finset.univ : Finset ι), ({(x : X)} : Set X) := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_iUnion.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact (ResolutionInvariantSegments.countCentresMeeting_mono hcover (s.stage i).2).trans
    ((ResolutionInvariantSegments.countCentresMeeting_biUnion_le Finset.univ
      (fun x : ι => ({(x : X)} : Set X)) (s.stage i).2).trans
        (Finset.sum_le_sum fun x _ => hb x i))

/-- Actual global dependent choice plus genuine local canonical single-point
branches internally produce a globally locally resolving whole-cosupport
sequence. No preconstructed sequence or finiteness certificate is an input. -/
theorem exists_global_locally_resolving_sequence_of_isInvDomain_one (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 1 m) :
    ∃ s : GrowingSeq X,
      (∀ i, IsGeoTestTower m (s.stage i).2) ∧
      (∀ i, ∃ (π : (s.stage (i + 1)).1 → (s.stage i).1)
        (hπ : IsBlowupAlong n (geoTransformAlong m (s.stage i).2).cosupp π),
        (s.stage (i + 1)).2 = .step (s.stage i).2
          (geoTransformAlong m (s.stage i).2).cosupp π hπ) ∧
      ∀ K : Set X, IsCompact K → ∃ N : ℕ, ∀ i, N ≤ i →
        (geoTransformAlong m (s.stage i).2).cosupp ∩ (s.stage i).2.proj ⁻¹' K = ∅ := by
  classical
  obtain ⟨s, hs, hext⟩ := exists_global_cosupport_growing_sequence_of_isInvDomain_one m h
  have hwhole : ∀ i, WholeCosupportTower m (s.stage i).2 := by
    intro i
    induction i with
    | zero => rw [s.zero]; trivial
    | succ i ih =>
      obtain ⟨π, hπ, heq⟩ := hext i
      rw [heq]
      exact ⟨ih, rfl⟩
  refine ⟨s, hs, hext, ?_⟩
  intro K hK
  obtain ⟨b, hb⟩ := exists_compact_count_bound_of_whole_cosupport_sequence hn m h s hs hwhole K hK
  let f : ℕ → ℕ := fun i => countCentresMeeting K (s.stage i).2
  have hmono : Monotone f := fun i j hij => s.count_mono K hij
  have hfin : (range f).Finite := (finite_Iic b).subset fun _ ⟨i, hi⟩ => hi ▸ hb i
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ :=
    Set.exists_max_image (range f) id hfin ⟨f 0, mem_range_self 0⟩
  have hconstant : ∀ i, N ≤ i → f i = f N :=
    fun i hi => le_antisymm (hmax (f i) (mem_range_self i)) (hmono hi)
  refine ⟨N, fun i hi => eq_empty_iff_forall_notMem.mpr ?_⟩
  intro z hz
  have hinc : f (i + 1) = f i + 1 := by
    obtain ⟨π, hπ, heq⟩ := hext i
    change countCentresMeeting K (s.stage (i + 1)).2 = countCentresMeeting K (s.stage i).2 + 1
    rw [heq]
    simp only [countCentresMeeting, if_pos (show
      ((geoTransformAlong m (s.stage i).2).cosupp ∩ (s.stage i).2.proj ⁻¹' K).Nonempty from ⟨z, hz⟩)]
  have hci := hconstant i hi
  have hcis := hconstant (i + 1) (by omega)
  omega

/-- The internally produced genuine global sequence is both indexed locally
finite and actually locally resolving on every compact initial subset. -/
theorem exists_global_locally_finite_resolving_sequence_of_isInvDomain_one
    (m : MarkedIdeal n X) (h : IsInvDomain 1 m) :
    ∃ s : GrowingSeq X,
      (∀ i, IsGeoTestTower m (s.stage i).2) ∧
      (∀ i, ∃ (π : (s.stage (i + 1)).1 → (s.stage i).1)
        (hπ : IsBlowupAlong n (geoTransformAlong m (s.stage i).2).cosupp π),
        (s.stage (i + 1)).2 = .step (s.stage i).2
          (geoTransformAlong m (s.stage i).2).cosupp π hπ) ∧
      LocallyFinite (fun i => (s.stage i).2.proj '' (geoTransformAlong m (s.stage i).2).cosupp) ∧
      ∀ K : Set X, IsCompact K → ∃ N : ℕ, ∀ i, N ≤ i →
        (geoTransformAlong m (s.stage i).2).cosupp ∩ (s.stage i).2.proj ⁻¹' K = ∅ := by
  rcases Nat.eq_zero_or_pos n with hnzero | hn
  · subst n
    have hdim0 : ResolutionInvariantSpec.DimLE 0 m.N 0 := by
      intro x hx
      obtain ⟨j, _, hj⟩ := h.dimLE x hx
      have hj0 : j = 0 := Nat.le_zero.mp hj.1
      subst j
      exact ⟨0, le_rfl, hj⟩
    have hdom0 : IsInvDomain 0 m :=
      ⟨h.isWellFormed, hdim0, h.one_le_d, h.isNonzeroAlongAt⟩
    obtain ⟨s, hs, hext⟩ := exists_global_cosupport_growing_sequence_of_isInvDomain_one m h
    have hempty : ∀ i, (geoTransformAlong m (s.stage i).2).cosupp = ∅ :=
      fun i => cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hdom0 (s.stage i).2 (hs i)
    refine ⟨s, hs, hext, ?_, fun K _ => ⟨0, fun i _ => ?_⟩⟩
    · intro x
      refine ⟨univ, Filter.univ_mem, ?_⟩
      simp [hempty]
    · rw [hempty i, empty_inter]
  · obtain ⟨s, hs, hext, hresolve⟩ := exists_global_locally_resolving_sequence_of_isInvDomain_one hn m h
    refine ⟨s, hs, hext, ?_, hresolve⟩
    have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
    intro x
    obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
    obtain ⟨N, hN⟩ := hresolve K hK
    refine ⟨K, hxK, (finite_Iio N).subset ?_⟩
    rintro i ⟨y, ⟨z, hz, rfl⟩, hzK⟩
    exact lt_of_not_ge fun hge => by
      have hzempty := hN i hge
      exact notMem_empty z (hzempty ▸ (show
        z ∈ (geoTransformAlong m (s.stage i).2).cosupp ∩ (s.stage i).2.proj ⁻¹' K from ⟨hz, hzK⟩))

/-- A genuine actual global sequence supplies one real open neighbourhood
of every compact initial subset over which every sufficiently late prefix
is an actual finite geometric resolution. -/
theorem exists_global_open_resolving_sequence_of_isInvDomain_one
    (m : MarkedIdeal n X) (h : IsInvDomain 1 m) :
    ∃ s : GrowingSeq X,
      (∀ i, IsGeoTestTower m (s.stage i).2) ∧
      (∀ i, ∃ (π : (s.stage (i + 1)).1 → (s.stage i).1)
        (hπ : IsBlowupAlong n (geoTransformAlong m (s.stage i).2).cosupp π),
        (s.stage (i + 1)).2 = .step (s.stage i).2
          (geoTransformAlong m (s.stage i).2).cosupp π hπ) ∧
      ∀ K : Set X, IsCompact K → ∃ (N : ℕ) (U : TopologicalSpace.Opens X),
        K ⊆ U ∧ ∀ i, N ≤ i → IsGeoResolution (pullback (Subtype.val : U → X) m)
          (restrict U (s.stage i).2) := by
  obtain ⟨s, hs, hext, hLF, hresolve⟩ := exists_global_locally_finite_resolving_sequence_of_isInvDomain_one m h
  have hclosed : ∀ i, IsClosed ((s.stage i).2.proj '' (geoTransformAlong m (s.stage i).2).cosupp) := by
    intro i
    have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (s.stage i).2 (hs i)
    have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
      hdom.isWellFormed.isCoherent hdom.isWellFormed.isClosedSubmanifold_N hdom.one_le_d
    exact (HironakaLocalPrincipalization.isProperMap_proj (s.stage i).2).isClosedMap _ hA.isClosed
  refine ⟨s, hs, hext, ?_⟩
  intro K hK
  obtain ⟨N, hN⟩ := hresolve K hK
  have htailclosed : IsClosed (⋃ i : {i : ℕ // N ≤ i},
      (s.stage i).2.proj '' (geoTransformAlong m (s.stage i).2).cosupp) :=
    (hLF.comp_injective Subtype.val_injective).isClosed_iUnion (fun i => hclosed i)
  let U : TopologicalSpace.Opens X := ⟨(⋃ i : {i : ℕ // N ≤ i},
    (s.stage i).2.proj '' (geoTransformAlong m (s.stage i).2).cosupp)ᶜ, htailclosed.isOpen_compl⟩
  refine ⟨N, U, ?_, ?_⟩
  · intro x hxK hxTail
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hxTail
    exact notMem_empty z ((hN i i.2) ▸ (show z ∈
      (geoTransformAlong m (s.stage i).2).cosupp ∩ (s.stage i).2.proj ⁻¹' K from ⟨hz, hxK⟩))
  · intro i hi
    refine ⟨MarkedIdealRestrictOpen.isGeoTestTower_restrict U
      h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent (s.stage i).2 (hs i), ?_⟩
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent U (s.stage i).2 (hs i)]
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact z.2 (mem_iUnion.mpr ⟨⟨i, hi⟩, z.1, hz, rfl⟩)

end
end Hironaka.HironakaCurveStrictFibres
