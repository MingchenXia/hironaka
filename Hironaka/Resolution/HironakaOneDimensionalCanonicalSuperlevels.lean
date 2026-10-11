/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneSpecialAnalyticLoci
import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.Invariant.ResolutionInvariantDriver
import Mathlib.Topology.DiscreteSubset

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

import Hironaka.Analytic.PreconnectedZeroDimensionalPoints
import Hironaka.Analytic.ThinAnalyticDimensionBound

set_option autoImplicit false

/-! Actual complete one-dimensional canonical superlevels.
Blueprint `hironaka-one-dimensional-canonical-superlevels-extension.tex`;
global higher-dimensional G3 and the simultaneous chain engine remain open. -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaOneDimensionalCanonicalSuperlevels

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GlobalComponents RegularLocusComponent AnalyticDimensionBasics PositiveDimensionalComponent
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  GermIdealOrder DivisorExponentAlong CanonicalCentres

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual global regular components force all points of a genuinely
zero-dimensional analytic set to be regular of dimension zero. -/
theorem regularAtDim_zero_of_analytic_dimLE_zero {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 0)
    {x : M} (hx : x ∈ A) : RegularAtDim (n := n) A x 0 := by
  have hxU : x ∈ ⋃₀ globalComponents (n := n) A := by rw [sUnion_globalComponents hA]; exact hx
  obtain ⟨B, ⟨c, ⟨k, hc⟩, rfl⟩, hxB⟩ := hxU
  have hk : k = 0 := Nat.le_zero.mp (hdim c k hc)
  subst k
  have hsub : component (n := n) A c ⊆ {c} :=
    subset_singleton_of_isPreconnected (component_subset (n := n) A c)
      isPreconnected_connectedComponentIn (fun _ hy => regularAtDim_of_mem_component hc hy)
      (mem_component_self hc)
  have hxc : x = c := closure_minimal hsub isClosed_singleton hxB
  simpa only [hxc] using hc

/-- Genuine zero-dimensional flattenings give actual singleton neighbourhoods;
no discreteness certificate is assumed. -/
theorem isDiscrete_of_analytic_dimLE_zero {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 0) :
    IsDiscrete A := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero
    (regularAtDim_zero_of_analytic_dimLE_zero hA hdim hx)
  exact ⟨U, hU, Subset.antisymm (fun y hy => hsub ⟨hy.2, hy.1⟩)
    (fun y hy => by rw [mem_singleton_iff.mp hy]; exact ⟨hxU, hx⟩)⟩

/-- Every actual subset of the genuine closed discrete analytic carrier is
closed and smooth, without compactness or a finite carrier assumption. -/
theorem isClosedSubmanifold_subset_of_analytic_dimLE_zero {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 0) (hBA : B ⊆ A) :
    IsClosedSubmanifold n B := by
  refine ⟨isClosed_of_subset_discrete_closed hBA (isDiscrete_of_analytic_dimLE_zero hA hdim) hA.isClosed, ?_⟩
  intro x hx
  have hxreg := regularAtDim_zero_of_analytic_dimLE_zero hA hdim (hBA hx)
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hxreg
  refine ⟨0, RegularPointDimension.regularAtDim_of_inter_eq hU hxU ?_ hxreg⟩
  exact Subset.antisymm (fun y hy => ⟨by rw [hsub hy]; exact hx, hy.2⟩)
    (fun _ hy => ⟨hBA hy.1, hy.2⟩)

/-- The genuine zero-dimensional geometry proves local constancy of every
actual function, including the actual augmented invariant's base case. -/
theorem eventually_eq_on_analytic_dimLE_zero {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 0)
    {β : Type*} (f : M → β) {x : M} (hx : x ∈ A) :
    ∀ᶠ y in 𝓝 x, y ∈ A → f y = f x := by
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero
    (regularAtDim_zero_of_analytic_dimLE_zero hA hdim hx)
  filter_upwards [hU.mem_nhds hxU] with y hyU hyA
  rw [hsub ⟨hyA, hyU⟩]

omit [IsComplexManifold n M] in
private theorem thin_cosupport_of_nonzeroAlong (N : Set M) (I : GermIdeal n M)
    (hI : I.IsCoherent) (hne : ∀ x ∈ N, IsNonzeroAlongAt N I x) (d : ℕ) (hd : 1 ≤ d) :
    ∀ O : Set M, IsOpen O → O ∩ N ⊆ cosupport n N I d → O ∩ N = ∅ := by
  intro O hO hsub
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxO, hxN⟩
  obtain ⟨g, hg, hfreq⟩ := hne x hxN
  obtain ⟨U, hU, hxU, r, s, hs, hgen⟩ := hI x
  obtain ⟨_, q, t, a, ht, _, hsum⟩ := (hgen x hxU g).mp hg
  have hzero : ∀ y ∈ U ∩ O, y ∈ N → ∀ i : Fin r, s i y = 0 := by
    intro y hy hyN i
    have hhol : HolomorphicAt n (s i) y := by
      filter_upwards [hU.mem_nhds hy.1] with z hz
      exact (hs i z hz).mdifferentiableAt (hU.mem_nhds hz)
    have hmem : I.mem y (s i) := (hgen y hy.1 (s i)).mpr
      (isInSpanAt_of_eq_mul (s := s i) (a := fun _ => 1)
        ⟨i, rfl⟩ hhol (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp))
    exact (vanishesToOrderOn_one_iff hyN hhol).mp (((hsub ⟨hy.2, hyN⟩).2 _ hmem).mono hd)
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ y ∈ O ∧ g y = ∑ i, a i y * t i y := by
    filter_upwards [hU.mem_nhds hxU, hO.mem_nhds hxO, hsum] with y hyU hyO hys
    exact ⟨hyU, hyO, hys⟩
  obtain ⟨y, ⟨hyN, hyg⟩, hyU, hyO, hysum⟩ := (hfreq.and_eventually hev).exists
  apply hyg
  rw [hysum]
  have htz : ∀ j : Fin q, t j y = 0 := by
    intro j
    obtain ⟨i, hi⟩ := ht j
    rw [← hi]
    exact hzero y ⟨hyU, hyO⟩ hyN i
  simp [htz]

/-- Actual coherent generators and nonzero-along germs make the positive-mark
cosupport thin in its genuine smooth carrier and produce dimension drop. -/
theorem dimLE_cosupport_of_isInvDomain {k : ℕ} {m : MarkedIdeal n M}
    (h : ResolutionInvariantSpec.IsInvDomain k m) :
    DimLE (n := n) m.cosupp (k - 1) := by
  have hN := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    h.isWellFormed.isClosedSubmanifold_N
  have hdim : DimLE (n := n) m.N k := by
    intro y j hy
    obtain ⟨a, ha, hya⟩ := h.dimLE y hy.2.1
    have hja := RegularPointDimension.eq_of_regularAtDim hy hya
    exact hja ▸ ha
  exact ThinDimensionDrop.dimLE_pred_of_thin hN m.cosupp_subset_N
    (thin_cosupport_of_nonzeroAlong m.N m.ideal h.isWellFormed.isCoherent
      h.isNonzeroAlongAt m.d h.one_le_d) hdim

/-- Genuine dimension-one domain data internally produce analytic equations
for every actual subset of its zero-dimensional cosupport. -/
theorem isComplexAnalyticSubset_subset_cosupport_of_isInvDomain_one
    {m : MarkedIdeal n M} (h : ResolutionInvariantSpec.IsInvDomain 1 m)
    (B : Set M) (hB : B ⊆ m.cosupp) : IsComplexAnalyticSubset (n := n) B := by
  have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
    h.isWellFormed.isCoherent h.isWellFormed.isClosedSubmanifold_N h.one_le_d
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    (isClosedSubmanifold_subset_of_analytic_dimLE_zero hA
      (dimLE_cosupport_of_isInvDomain h) hB)

omit [IsComplexManifold n M] in
/-- A singleton is a genuine coordinate subspace in the actual centred SNC
coordinates, with every ambient coordinate among the centre equations. -/
theorem hasNormalCrossings_singleton (x : M) {E : List (Set M)}
    (hE : NormalCrossings.IsSNCDivisor n E) :
    NormalCrossings.HasNormalCrossings n {x} E := by
  intro y hy
  have hyx := mem_singleton_iff.mp hy
  subst y
  obtain ⟨S, ⟨Φ, hsrc, hzero, hfamily⟩, hcard, _⟩ := hE.2 x
  refine ⟨Finset.univ, S, ⟨Φ, hsrc, hzero, ?_⟩, hcard⟩
  rintro (_ | i) hmem z hzs hzΦ
  · constructor
    · intro hzx
      rw [mem_singleton_iff.mp hzx, hzero]
      simp [NormalCrossings.coordSubspace]
    · intro hz
      have hz0 : Φ.toFun ((complexChartAt (n := n) x).val z) = 0 := by
        ext j
        exact hz j (Finset.mem_univ j)
      have hez : (complexChartAt (n := n) x).val z = (complexChartAt (n := n) x).val x :=
        calc (complexChartAt (n := n) x).val z
            = Φ.invFun (Φ.toFun ((complexChartAt (n := n) x).val z)) := (Φ.left_inv _ hzΦ).symm
          _ = Φ.invFun (Φ.toFun ((complexChartAt (n := n) x).val x)) := by rw [hz0, hzero]
          _ = (complexChartAt (n := n) x).val x := Φ.left_inv _ Φ.center_mem_source
      exact (complexChartAt (n := n) x).val.injOn hzs (mem_complexChartAt_source x) hez
  · exact hfamily i hmem hzs hzΦ

/-- Actual singleton neighbourhoods transfer genuine normal crossings to
every subset of the zero-dimensional analytic carrier. -/
theorem hasNormalCrossings_subset_of_analytic_dimLE_zero {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 0)
    (hBA : B ⊆ A) {E : List (Set M)} (hE : NormalCrossings.IsSNCDivisor n E) :
    NormalCrossings.HasNormalCrossings n B E := by
  apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
  intro x hx
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero
    (regularAtDim_zero_of_analytic_dimLE_zero hA hdim (hBA hx))
  refine ⟨{x}, mem_singleton x, ?_, hasNormalCrossings_singleton x hE⟩
  filter_upwards [hU.mem_nhds hxU] with y hyU
  exact ⟨fun hy => hsub ⟨hBA hy, hyU⟩,
    fun hy => by rw [mem_singleton_iff.mp hy]; exact hx⟩

/-- Genuine domain geometry and the actual SNC boundary internally make
every actual cosupport subset an admissible global centre in dimension one. -/
theorem isAdmissibleCentre_subset_cosupport_of_isInvDomain_one
    {m : MarkedIdeal n M} (h : ResolutionInvariantSpec.IsInvDomain 1 m)
    (B : Set M) (hB : B ⊆ m.cosupp) : m.IsAdmissibleCentre B := by
  have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
    h.isWellFormed.isCoherent h.isWellFormed.isClosedSubmanifold_N h.one_le_d
  have hd := dimLE_cosupport_of_isInvDomain h
  exact ⟨isClosedSubmanifold_subset_of_analytic_dimLE_zero hA hd hB, hB,
    hasNormalCrossings_subset_of_analytic_dimLE_zero hA hd hB h.isWellFormed.isSNCDivisor⟩

section ActualCanonical

universe u
variable {X Y : CMfd.{u} n}

/-- A true global blowup of the actual whole cosupport exists, without
compactness, a global maximum or a conclusion-shaped tower certificate. -/
theorem exists_global_cosupport_blowup_step_of_isInvDomain_one
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 1 m) :
    ∃ (Y : CMfd.{u} n) (π : Y → X) (hπ : IsBlowupAlong n m.cosupp π),
      IsGeoTestTower m (BlowupTower.step .refl m.cosupp π hπ) := by
  have hC := isAdmissibleCentre_subset_cosupport_of_isInvDomain_one h m.cosupp (Subset.refl _)
  obtain ⟨Y, π, hπ⟩ := ResolutionDriver.exists_blowup m.cosupp hC.1
    (ResolutionInvariantDriver.interior_cosupp_eq_empty h)
  exact ⟨Y, π, hπ, (isGeoTestTower_step_iff m .refl m.cosupp π hπ).mpr ⟨trivial, hC⟩⟩

/-- Actual global dependent choice iterates internally produced whole-cosupport
blowups, retaining genuine maps and exact successor towers. Termination and
compact-set local finiteness are not hypotheses or claims of this producer. -/
theorem exists_global_cosupport_growing_sequence_of_isInvDomain_one
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 1 m) :
    ∃ s : ResolutionInvariantSeq.GrowingSeq X,
      (∀ i, IsGeoTestTower m (s.stage i).2) ∧
      ∀ i, ∃ (π : (s.stage (i + 1)).1 → (s.stage i).1)
        (hπ : IsBlowupAlong n (geoTransformAlong m (s.stage i).2).cosupp π),
        (s.stage (i + 1)).2 =
          .step (s.stage i).2 (geoTransformAlong m (s.stage i).2).cosupp π hπ := by
  classical
  let S := {p : Σ Y : CMfd.{u} n, BlowupTower X Y // IsGeoTestTower m p.2}
  have hext : ∀ p : S, ∃ q : S, ∃ (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n (geoTransformAlong m p.1.2).cosupp π),
      q.1.2 = .step p.1.2 (geoTransformAlong m p.1.2).cosupp π hπ := by
    intro p
    have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h p.1.2 p.2
    have hC := isAdmissibleCentre_subset_cosupport_of_isInvDomain_one hdom
      (geoTransformAlong m p.1.2).cosupp (Subset.refl _)
    obtain ⟨Z, π, hπ⟩ := ResolutionDriver.exists_blowup _ hC.1
      (ResolutionInvariantDriver.interior_cosupp_eq_empty hdom)
    exact ⟨⟨⟨Z, .step p.1.2 _ π hπ⟩,
      (isGeoTestTower_step_iff m p.1.2 _ π hπ).mpr ⟨p.2, hC⟩⟩, π, hπ, rfl⟩
  choose next hnext using hext
  let s₀ : S := ⟨⟨X, .refl⟩, trivial⟩
  let s : ResolutionInvariantSeq.GrowingSeq X :=
    ResolutionInvariantSeq.GrowingSeq.ofIterate (fun p : S => p.1) next s₀ rfl
      (fun p => by obtain ⟨π, hπ, heq⟩ := hnext p; exact ⟨_, π, hπ, heq⟩)
  refine ⟨s, fun i => (next^[i] s₀).2, ?_⟩
  intro i
  change ∃ (π : (next^[i + 1] s₀).1.1 → (next^[i] s₀).1.1)
      (hπ : IsBlowupAlong n (geoTransformAlong m (next^[i] s₀).1.2).cosupp π),
      (next^[i + 1] s₀).1.2 = .step (next^[i] s₀).1.2 _ π hπ
  rw [Function.iterate_succ_apply']
  exact hnext _

/-- Every whole actual canonical threshold, with all historical entries
retained, is analytic in genuine carrier dimension at most one. -/
theorem isComplexAnalyticSubset_canonical_one_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 1 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (v : ValTy 1) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ v ≤ (invFamily hn 1).inv m T y} := by
  have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  exact isComplexAnalyticSubset_subset_cosupport_of_isInvDomain_one hdom _ (fun _ hy => hy.1)

end ActualCanonical

end
end Hironaka.HironakaOneDimensionalCanonicalSuperlevels
