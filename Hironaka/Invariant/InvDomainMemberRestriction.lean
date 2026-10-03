/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.BoundaryCountAlong
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterAlong
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Blowup.SimultaneousNormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1ab's restricted marked ideals lie in the domain of the inductive invariant

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 1a of Proposition `pr:resol`; Włodarczyk 2009
(`wlodarczyk09-analytic-resolution`) Step 1a (printed p. 55).

In Step 1a of the maximal-order step, at a point `y` of the cosupport lying on `s₀ ≥ 1` of the original members
(`s₀` the current maximum of `s`), the value is `(s₀, inv(𝒮))` with the lower-dimensional invariant of the
restriction `𝒮 = (X, N ∩ H_{S(y)}, E_{S(y)}, 𝓒_N(𝔞), μ_𝓒)` of the coefficient ideal to the intersection of `N` with
the members through `y`, the members `S(y)` deleted from `E` (form
`CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff`). The inductive invariant
(`ResolutionInvariantSpec.ResolutionInvariant`) is defined on the marked ideals of
`ResolutionInvariantSpec.IsInvDomain (k - 1)`; this module shows that `𝒮`, restricted to a neighbourhood of `y`
missing the members not through `y`, lies there once the level-`s₀` part of the member locus is empty, which is the
situation after Step 1aa.

## Main results

* `exists_regularAtDim_inter_memberInter_lt`, `dimLE_inter_memberInter`: for `E` simple normal crossings and
  transverse to the closed set `N` and `S` a nonempty set of members, `N ∩ H_S` has smaller dimension than `N` at
  each of its points, so `dim N ≤ k` gives `dim (N ∩ H_S) ≤ k - 1` (in coordinates adapted to `N ∩ H_S ⊆ N` and
  `E`, the step along the coordinate of a member of `S` stays in `N` and leaves `N ∩ H_S`);
* `isInvDomain_pullback_val_of_forall`: a well-formed marked ideal with `dim N ≤ k`, `d ≥ 1`, nonzero along `N` at
  the points of an open `U`, restricted to `U`, lies in `IsInvDomain k`;
* `memberRestrict 𝔪 S`: the restricted marked ideal `{ withN (coeffMarkedAlong 𝔪) (N ∩ H_S) with E:= E_S }`;
  `isWellFormed_memberRestrict`, `dimLE_memberRestrict`, `one_le_memberRestrict_d`
* `isNonzeroAlongAt_memberRestrict`: off the member locus, at a point near which `H_S` is the intersection of the
  members of `E₀` through the point, the coefficient ideal is nonzero along `N ∩ H_S`;
* `membersThrough`, `exists_opens_forall_mem_imp`: for `y` on `s₀ ≥ 1` members of a list `E₀` of members of `E`,
  with the level-`s₀` part of the member locus empty, the restriction of `memberRestrict 𝔪 (membersThrough 𝔪.E E₀
  y)` to every open set on whose points the members of `E₀` all pass through `y` lies in `IsInvDomain (k - 1)`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.InvDomainMemberRestriction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealRestrictOpen Hironaka.DivisorExponentAlong Hironaka.ResolutionInvariantSpec Hironaka.NormalCrossings Hironaka.BoundaryCount Hironaka.BlowupSNCTransform Hironaka.SimultaneousNormalCrossings Hironaka.MemberInterAlong Hironaka.BoundaryCountAlong Hironaka.MemberInterLocusAlong Hironaka.CoefficientIdealRestriction Hironaka.HomogenizedIdealAlong Hironaka.RegularPointDimension Hironaka.MarkedIdealBiholomorphism

noncomputable section

variable {n : ℕ}

/-! ### The dimension of an intersection of members -/

section Dimension

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **An intersection of members drops the dimension**: let `E` be simple normal crossings and transverse to the
closed set `N`, `S` a nonempty set of members and `x ∈ N ∩ H_S`.  If `N` is regular of dimension `j` at `x`, then
`N ∩ H_S` is regular at `x` of some dimension `j' < j`.  (In coordinates adapted to `N ∩ H_S ⊆ N` and `E`, `N` and
`N ∩ H_S` are coordinate planes and a member `H_i`, `i ∈ S`, is `{w_{s_i} = 0}` with `s_i` a tangential coordinate of
`N`; a small step along `w_{s_i}` stays in `N` and leaves `H_i ⊇ N ∩ H_S`.) -/
theorem exists_regularAtDim_inter_memberInter_lt (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {S : Finset (Fin E.length)} (hS : S.Nonempty) {x : X}
    (hx : x ∈ N ∩ memberInter E S) {j : ℕ} (hNx : RegularAtDim (n := n) N x j) :
    ∃ j' < j, RegularAtDim (n := n) (N ∩ memberInter E S) x j' := by
  obtain ⟨kC, kN, Φ, s, hΦt, hslt, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn inter_subset_left hE hT
    (hasNormalCrossings_inter_memberInter hT S) hx
  have hxe : x ∈ (chartAt (ComplexModel n) x).source := mem_chart_source _ x
  have hC : RegularAtDim (n := n) (N ∩ memberInter E S) x (min kC n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun {y} hy hyΦ => by rw [complexCoordinatePlane_min]; exact (hflat hy hyΦ).1) hx hxe
      Φ.center_mem_source
  have hN : RegularAtDim (n := n) N x (min kN n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun {y} hy hyΦ => by rw [complexCoordinatePlane_min]; exact (hflat hy hyΦ).2.1) hx.1 hxe
      Φ.center_mem_source
  have hj : j = min kN n := eq_of_regularAtDim hNx hN
  refine ⟨min kC n, ?_, hC⟩
  rw [hj]
  by_contra hle
  push Not at hle
  obtain ⟨i, hi⟩ := hS
  have hxi : x ∈ E.get i := hx.2 i hi
  set c := Φ.toFun (chartAt (ComplexModel n) x x) with hcdef
  have hcT : c ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have hcN : c ∈ complexCoordinatePlane n kN := ((hflat hxe Φ.center_mem_source).2.1).mp hx.1
  have hci : c (s i) = 0 := ((hflat hxe Φ.center_mem_source).2.2 i hxi).mp hxi
  -- a small step along the coordinate `w_{s i}` stays in `Φ.target`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Φ.isOpen_target c hcT
  set v : ComplexModel n := c + EuclideanSpace.single (s i) ((r / 2 : ℝ) : ℂ) with hvdef
  have hvT : v ∈ Φ.target := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, hvdef, add_sub_cancel_left, PiLp.norm_single,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hvs : v (s i) ≠ 0 := by
    rw [hvdef, PiLp.add_apply, hci, zero_add, PiLp.single_apply, if_pos rfl]
    exact Complex.ofReal_ne_zero.mpr (half_pos hr).ne'
  have hvN : v ∈ complexCoordinatePlane n kN := fun m hm => by
    have hms : m ≠ s i := fun h => by
      subst h
      exact absurd hm (not_le.mpr (hslt i hxi))
    rw [hvdef, PiLp.add_apply, hcN m hm, zero_add, PiLp.single_apply, if_neg hms]
  have hvC : v ∈ complexCoordinatePlane n kC := by
    rw [← complexCoordinatePlane_min kN] at hvN
    rw [← complexCoordinatePlane_min kC]
    exact fun m hm => hvN m (hle.trans hm)
  -- the point `y` with coordinates `v` lies in `N ∩ H_S` but not on `H_i`
  have hwΦ : Φ.invFun v ∈ Φ.source := Φ.mapsTo_invFun hvT
  have hwe : Φ.invFun v ∈ (chartAt (ComplexModel n) x).target := hΦt hwΦ
  set y := (chartAt (ComplexModel n) x).symm (Φ.invFun v) with hydef
  have hy : y ∈ (chartAt (ComplexModel n) x).source := (chartAt (ComplexModel n) x).map_target hwe
  have hey : chartAt (ComplexModel n) x y = Φ.invFun v := (chartAt (ComplexModel n) x).right_inv hwe
  have hyΦ : chartAt (ComplexModel n) x y ∈ Φ.source := hey ▸ hwΦ
  have hΦy : Φ.toFun (chartAt (ComplexModel n) x y) = v := by rw [hey]; exact Φ.right_inv v hvT
  have hyC : y ∈ N ∩ memberInter E S := ((hflat hy hyΦ).1).mpr (hΦy ▸ hvC)
  have h0 := ((hflat hy hyΦ).2.2 i hxi).mp (hyC.2 i hi)
  rw [hΦy] at h0
  exact hvs h0

/-- **`dim (N ∩ H_S) ≤ k - 1`** if `dim N ≤ k`, `E` is simple normal crossings and transverse to `N`, and `S` is a
nonempty set of members. -/
theorem dimLE_inter_memberInter (hn : 0 < n) {N : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) {S : Finset (Fin E.length)} (hS : S.Nonempty) {k : ℕ} (hk : DimLE n N k) :
    DimLE n (N ∩ memberInter E S) (k - 1) := fun x hx => by
  obtain ⟨j, hjk, hj⟩ := hk x hx.1
  obtain ⟨j', hj'j, hj'⟩ := exists_regularAtDim_inter_memberInter_lt hn hE hT hS hx hj
  exact ⟨j', by omega, hj'⟩

end Dimension

/-! ### The domain on an open set -/

section Open

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The domain on an open set**: a well-formed marked ideal with `dim N ≤ k` and `d ≥ 1` whose ideal is nonzero
along `N` at the points of `N` in the open set `U` lies, restricted to `U`, in `IsInvDomain k` (the localized form of
`InvDomainTowerAlong.isInvDomain_pullback_val`). -/
theorem isInvDomain_pullback_val_of_forall {𝔪 : MarkedIdeal n M} {k : ℕ} (h𝔪 : 𝔪.IsWellFormed)
    (hk : DimLE n 𝔪.N k) (hd : 1 ≤ 𝔪.d) (U : Opens M)
    (hnz : ∀ x ∈ 𝔪.N, x ∈ U → IsNonzeroAlongAt 𝔪.N 𝔪.ideal x) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) where
  isWellFormed := IsWellFormed.pullback_val h𝔪 U
  dimLE := fun p hp => by
    obtain ⟨j, hjk, hj⟩ := hk (p : M) hp
    exact ⟨j, hjk, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩
  one_le_d := hd
  isNonzeroAlongAt := fun p hp => by
    obtain ⟨g, hg, hfreq⟩ := hnz (p : M) hp p.2
    refine ⟨g ∘ Subtype.val, comp_val_mem_pullback_val U h𝔪.isCoherent hg, ?_⟩
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p] at hfreq
    exact Filter.frequently_map.mp hfreq

end Open

/-! ### Step 1ab's restricted marked ideal -/

section Restrict

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- **Step 1ab's restricted marked ideal** `(X, N ∩ H_S, E_S, 𝓒_N(𝔞), μ_𝓒)`: the coefficient ideal along `N` restricted
to the intersection of `N` with the members of `S`, these members deleted from `E` (form in
`CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff`). -/
def memberRestrict (𝔪 : MarkedIdeal n X) (S : Finset (Fin 𝔪.E.length)) : MarkedIdeal n X :=
  { withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S) with
    E := ((List.finRange 𝔪.E.length).filter fun i => i ∉ S).map 𝔪.E.get }

@[simp] theorem memberRestrict_N (𝔪 : MarkedIdeal n X) (S : Finset (Fin 𝔪.E.length)) :
    (memberRestrict 𝔪 S).N = 𝔪.N ∩ memberInter 𝔪.E S := rfl

@[simp] theorem memberRestrict_E (𝔪 : MarkedIdeal n X) (S : Finset (Fin 𝔪.E.length)) :
    (memberRestrict 𝔪 S).E = ((List.finRange 𝔪.E.length).filter fun i => i ∉ S).map 𝔪.E.get := rfl

@[simp] theorem memberRestrict_ideal (𝔪 : MarkedIdeal n X) (S : Finset (Fin 𝔪.E.length)) :
    (memberRestrict 𝔪 S).ideal = (coeffMarkedAlong 𝔪).ideal := rfl

@[simp] theorem memberRestrict_d (𝔪 : MarkedIdeal n X) (S : Finset (Fin 𝔪.E.length)) :
    (memberRestrict 𝔪 S).d = (coeffMarkedAlong 𝔪).d := rfl

/-- The mark of the restricted marked ideal is positive (`μ_𝓒 = ∏_{j<d} (d - j)`, an empty product for `d = 0`). -/
theorem one_le_memberRestrict_d (𝔪 : MarkedIdeal n X) (S : Finset (Fin 𝔪.E.length)) :
    1 ≤ (memberRestrict 𝔪 S).d := by
  show 1 ≤ (Finset.range 𝔪.d).prod fun j => 𝔪.d - j
  exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j hj => by
    have := Finset.mem_range.mp hj
    omega)

variable [IsComplexManifold n X]

/-- **Step 1ab's restricted marked ideal is well formed** (`0 < n`, `𝔪` well formed). -/
theorem isWellFormed_memberRestrict (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (S : Finset (Fin 𝔪.E.length)) : (memberRestrict 𝔪 S).IsWellFormed :=
  isWellFormed_inter_memberInter_drop hn h𝔪 S
    (isCoherent_coeffMarkedAlong h𝔪.isCoherent h𝔪.isClosedSubmanifold_N) _

/-- **`dim (N ∩ H_S) ≤ k - 1`** for the restricted marked ideal, `S` nonempty and `dim N ≤ k`. -/
theorem dimLE_memberRestrict (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    {S : Finset (Fin 𝔪.E.length)} (hS : S.Nonempty) {k : ℕ} (hk : DimLE n 𝔪.N k) :
    DimLE n (memberRestrict 𝔪 S).N (k - 1) :=
  dimLE_inter_memberInter hn h𝔪.isSNCDivisor h𝔪.isTransverse hS hk

/-- **Off the member locus the restricted marked ideal is nonzero along `N ∩ H_S`**: at a point `z ∈ N` near
which `H_S` is the intersection of the members of `E₀` through `z`, and which is not in the member locus of the
cosupport along `N` and `E₀`, the coefficient ideal along `N` does not vanish identically on `N ∩ H_S` near `z`
(`MemberInterLocusAlong.isNonzeroAlongAt_coeffMarkedAlong_of_notMem_memberInterLocus`). -/
theorem isNonzeroAlongAt_memberRestrict {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (E₀ : List (Set X)) (S : Finset (Fin 𝔪.E.length)) {z : X}
    (hzN : z ∈ 𝔪.N) (hzS : ∀ᶠ w in 𝓝 z, w ∈ memberInter 𝔪.E S ↔ ∀ H ∈ E₀, z ∈ H → w ∈ H)
    (hz : z ∉ memberInterLocus 𝔪.N E₀ 𝔪.cosupp) :
    IsNonzeroAlongAt (memberRestrict 𝔪 S).N (memberRestrict 𝔪 S).ideal z := by
  obtain ⟨g, hg, hfreq⟩ := isNonzeroAlongAt_coeffMarkedAlong_of_notMem_memberInterLocus 𝔪 hN h𝔞 hd E₀ hzN hz
  refine ⟨g, hg, (hfreq.and_eventually hzS).mono fun w hw => ?_⟩
  obtain ⟨⟨⟨hwN, hwE⟩, hgw⟩, hiff⟩ := hw
  exact ⟨⟨hwN, hiff.mpr hwE⟩, hgw⟩

end Restrict

/-! ### At a point on `s₀` members, off the level-`s₀` member locus -/

section Through

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

open Classical in
/-- **The members of `E₀` through `y`**, as indices of `E` (`E₀` a list of members of `E`). -/
def membersThrough (E E₀ : List (Set X)) (y : X) : Finset (Fin E.length) :=
  Finset.univ.filter fun i => E.get i ∈ E₀ ∧ y ∈ E.get i

theorem mem_membersThrough {E E₀ : List (Set X)} {y : X} {i : Fin E.length} :
    i ∈ membersThrough E E₀ y ↔ E.get i ∈ E₀ ∧ y ∈ E.get i := by
  classical
  simp [membersThrough]

/-- `H_{S(y)}` is the intersection of the members of `E₀` through `y`. -/
theorem memberInter_membersThrough {E E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, H ∈ E) (y : X) :
    memberInter E (membersThrough E E₀ y) = {w | ∀ H ∈ E₀, y ∈ H → w ∈ H} := by
  ext w
  refine ⟨fun hw H hH hyH => ?_, fun hw i hi => ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (hE₀ H hH)
    exact hw i (mem_membersThrough.mpr ⟨hH, hyH⟩)
  · obtain ⟨hi₀, hyi⟩ := mem_membersThrough.mp hi
    exact hw _ hi₀ hyi

/-- If `y` lies on a member of `E₀`, the set of members of `E₀` through `y` is nonempty. -/
theorem membersThrough_nonempty {E E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, H ∈ E) {y : X}
    (hy : 1 ≤ boundaryCount E₀ y) : (membersThrough E E₀ y).Nonempty := by
  classical
  obtain ⟨i, hi⟩ : (Finset.univ.filter fun i : Fin E₀.length => y ∈ E₀.get i).Nonempty := by
    rw [← Finset.card_pos]
    have h0 : 0 < boundaryCount E₀ y := hy
    unfold boundaryCount at h0
    convert h0
  have hyi : y ∈ E₀.get i := (Finset.mem_filter.mp hi).2
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (hE₀ _ (List.get_mem E₀ i))
  exact ⟨j, mem_membersThrough.mpr ⟨hj ▸ List.get_mem E₀ i, hj ▸ hyi⟩⟩

/-- **A neighbourhood of `y` missing the members not through `y`**: for closed members, the points lying on no
member of `E₀` that misses `y` form an open neighbourhood of `y`. -/
theorem exists_opens_forall_mem_imp {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H) (y : X) :
    ∃ U : Opens X, y ∈ U ∧ ∀ z ∈ U, ∀ H ∈ E₀, z ∈ H → y ∈ H := by
  classical
  refine ⟨⟨{z | ∀ H ∈ E₀, z ∈ H → y ∈ H}, ?_⟩, fun _ _ h => h, fun z hz => hz⟩
  have : {z | ∀ H ∈ E₀, z ∈ H → y ∈ H} = ⋂ H ∈ {H | H ∈ E₀}, (if y ∈ H then univ else Hᶜ) := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter]
    refine forall_congr' fun H => forall_congr' fun _ => ?_
    by_cases hyH : y ∈ H
    · simp [hyH]
    · simp [hyH]
  rw [this]
  refine (List.finite_toSet E₀).isOpen_biInter fun H hH => ?_
  split_ifs
  · exact isOpen_univ
  · exact (hE₀ H hH).isOpen_compl

end Through

/-! ### Along multiple test blow-ups: at every stage after Step 1aa -/

section Tower

open Hironaka.BlowupTowers Hironaka.CoefficientIdealRestriction Hironaka.MemberInterTowerAlong Hironaka.InvDomainTowerAlong Hironaka.HomogenizedGlueingTower

variable {X : CMfd.{u} n}

/-- **The counted members stay members**: for a list `E₀` of members of `E`, their strict transforms along a tower are
members of the transformed divisor (the first `#E` members of `E_T`). -/
theorem mem_E_geoTransformAlong_of_mem_map (𝔪 : MarkedIdeal n X) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : ∀ H ∈ E₀.map (strictAlong T), H ∈ (geoTransformAlong 𝔪 T).E := by
  rw [List.forall_mem_map]
  intro H hH
  have h : strictAlong T H ∈ (geoTransformAlong 𝔪 T).E.take 𝔪.E.length := by
    rw [take_E_geoTransformAlong]
    exact List.mem_map_of_mem (hE₀ H hH)
  exact List.mem_of_mem_take h

end Tower

end

end Hironaka.InvDomainMemberRestriction
