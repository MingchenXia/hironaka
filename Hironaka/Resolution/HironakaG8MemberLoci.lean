import Hironaka.Resolution.HironakaG8SpecialLoci
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.MemberInterAlong
import Hironaka.MarkedIdeal.CodimOneSupport
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Invariant.StepOneBridge
import Hironaka.Invariant.StepOneLowerDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Member loci for carriers of the same dimension (G8 lane, run 0080, round 4; (B') port P2, levels `≥ 1`)

Blueprint: `hironaka-g8-resume-member-loci.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P2, L-spec),
design decision D4 (levels, special points and regimes of the Step 1 skeleton are class-determined).

`HironakaG8SpecialLoci` (round 3) compared the codimension-one parts (level `0`).  At levels `≥ 1` the special points are
the member loci `MemberInterLocusAlong.memberInterLocus N E S` (points `x ∈ S` near which every point of the carrier `N`
on all members through `x` lies in `S`), which depend on the carrier.  BM08 (proof of Thm 6.1): a smooth subset of the
cosupport of the dimension of `N ∩ H_x` is the trace of the carrier.  In Lean:

* `regularAtDim_of_flat_coordSubspace`: a set that is a coordinate subspace `{z_j = 0, j ∈ T}` in centred holomorphic
  coordinates is regular of dimension `n - |T|` (permute the coordinates);
* `membersThrough E x = {z | ∀ H ∈ E, x ∈ H → z ∈ H}` (the intersection `H_x` of the members through `x`) and
  **`exists_regularAtDim_inter_membersThrough`**: for `E` transverse to `N` and `x ∈ N`, `N`, `H_x`, `N ∩ H_x` are regular
  at `x` of dimensions `a`, `h`, `a + h - n` (the transversal dimension count);
* **`mem_memberInterLocus_of_regularAtDim_iff`**, `mem_memberInterLocus_iff_of_regularAtDim_iff`: two closed carriers
  transverse to an SNC divisor `E`, of the same dimension at `x`, containing `S`, have the same member locus of `S` at `x`
  (the filling lemma `CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE` applied to `N ∩ H_x ⊆ P ∩ H_x`);
* **`isSpecial_iff_of_wEquiv`**: for Włodarczyk-equivalent marked ideals of the native domain with carriers of the same
  local dimension on the cosupport, the special points of the Step 1 skeleton (`StepOneValue.IsSpecial`: codimension-one
  part at level `0`, member locus at level `≥ 1`) agree at every stage of every common test tower; `level_eq_of_E_eq`.

Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8MemberLoci

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal
open Hironaka.NormalCrossings (coordSubspace IsTransverse IsSNCDivisor)
open Hironaka.MemberInterLocusAlong (memberInterLocus)
open Hironaka.AnalyticDimensionBasics (LocDimGE)
open Hironaka.RegularPointDimension (eq_of_regularAtDim)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {n : ℕ}

/-! ### Coordinate subspaces are regular of the expected dimension -/

section Coord

/-- Postcompose centred coordinates with a coordinate permutation. -/
private def permuteCoords {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p) (σ : Fin n ≃ Fin n) :
    LocalHolomorphicEquivAt (n := n) p := by
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ
  exact
    { source := Φ.source
      target := L.symm ⁻¹' Φ.target
      isOpen_source := Φ.isOpen_source
      isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
      center_mem_source := Φ.center_mem_source
      toFun := fun z => L (Φ.toFun z)
      invFun := fun z => Φ.invFun (L.symm z)
      toFun_holomorphic := L.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn.comp
        Φ.toFun_holomorphic (fun _ _ => mem_univ _)
      invFun_holomorphic := Φ.invFun_holomorphic.comp
        L.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn
        (fun _ hz => hz)
      mapsTo_toFun := fun z hz => by
        change L.symm (L (Φ.toFun z)) ∈ Φ.target
        rw [L.symm_apply_apply]; exact Φ.mapsTo_toFun hz
      mapsTo_invFun := fun z hz => Φ.mapsTo_invFun hz
      left_inv := fun z hz => by
        rw [L.symm_apply_apply]; exact Φ.left_inv z hz
      right_inv := fun z hz => by
        rw [Φ.right_inv _ hz]; exact L.apply_symm_apply z }

private theorem permuteCoords_apply {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p) (σ : Fin n ≃ Fin n)
    (z : ComplexModel n) (i : Fin n) : (permuteCoords Φ σ).toFun z (σ i) = Φ.toFun z i := by
  simp [permuteCoords, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A coordinate subspace in centred coordinates is regular of dimension `n - |T|`.** -/
theorem regularAtDim_of_flat_coordSubspace {B : Set M} {x : M} {T : Finset (Fin n)}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hflat : ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ B ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace T)) :
    RegularAtDim (n := n) B x (n - T.card) := by
  classical
  obtain ⟨σ, hσ⟩ := SimultaneousNormalCrossings.exists_perm_nested (X := T) (Y := T) (Subset.refl _)
  have hσ' : ∀ t, n - T.card ≤ (σ t).1 ↔ t ∈ T := fun t => (hσ t).1
  have hxB : x ∈ B := (hflat (mem_complexChartAt_source x) Φ.center_mem_source).mpr (by
    rw [h0]
    intro j _
    rfl)
  refine ⟨Nat.sub_le _ _, hxB, permuteCoords Φ σ, hsrc, ?_, ?_⟩
  · change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ) (Φ.toFun _) = 0
    rw [h0, map_zero]
  · intro y hy hyΦ
    rw [hflat hy hyΦ]
    constructor
    · intro hz i hi
      obtain ⟨j, rfl⟩ := σ.surjective i
      rw [permuteCoords_apply]
      exact hz j ((hσ' j).mp hi)
    · intro hz j hj
      rw [← permuteCoords_apply Φ σ _ j]
      exact hz (σ j) ((hσ' j).mpr hj)

/-! ### The transversal dimension count -/

/-- **The intersection of the members through `x`**: `H_x = ⋂_{H ∈ E, x ∈ H} H`. -/
def membersThrough (E : List (Set M)) (x : M) : Set M :=
  {z | ∀ H ∈ E, x ∈ H → z ∈ H}

theorem mem_membersThrough_iff {E : List (Set M)} {x z : M} :
    z ∈ membersThrough E x ↔ ∀ i : Fin E.length, x ∈ E.get i → z ∈ E.get i :=
  (MemberInterLocusAlong.forall_get_iff (P := fun H => x ∈ H → z ∈ H)).symm

/-- **The transversal dimension count**: for `E` transverse to `N` and `x ∈ N`, the carrier `N`, the intersection `H_x`
of the members through `x` and `N ∩ H_x` are regular at `x`, of dimensions `a`, `h` and `a + h - n` (`n ≤ a + h`). -/
theorem exists_regularAtDim_inter_membersThrough {N : Set M} {E : List (Set M)} (hT : IsTransverse n N E) {x : M}
    (hx : x ∈ N) :
    ∃ a h : ℕ, RegularAtDim (n := n) N x a ∧ RegularAtDim (n := n) (membersThrough E x) x h ∧ n ≤ a + h ∧
      RegularAtDim (n := n) (N ∩ membersThrough E x) x (a + h - n) := by
  classical
  obtain ⟨S₀, S, ⟨Φ, hsrc, h0, hflat⟩, hS⟩ := hT x hx
  set I : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i with hI
  set V : Finset (Fin n) := I.biUnion S with hV
  have hdisj : Disjoint S₀ V := by
    rw [hV, Finset.disjoint_biUnion_right]
    intro i hi
    exact (hS i (Finset.mem_filter.mp hi).2).2.symm
  have hN : ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace S₀) :=
    fun hy hyΦ => hflat none hx hy hyΦ
  have hH : ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ membersThrough E x ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace V) := by
    intro y hy hyΦ
    rw [mem_membersThrough_iff]
    constructor
    · intro hyH j hj
      obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
      have hxi := (Finset.mem_filter.mp hi).2
      exact (hflat (some i) hxi hy hyΦ).mp (hyH i hxi) j hji
    · intro hz i hxi
      exact (hflat (some i) hxi hy hyΦ).mpr fun j hj =>
        hz j (Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, hj⟩)
  have hNa := regularAtDim_of_flat_coordSubspace (B := N) Φ hsrc h0 hN
  have hHb := regularAtDim_of_flat_coordSubspace Φ hsrc h0 hH
  have hNH := regularAtDim_of_flat_coordSubspace (B := N ∩ membersThrough E x) (T := S₀ ∪ V) Φ hsrc h0
    (fun hy hyΦ => by
      rw [mem_inter_iff, hN hy hyΦ, hH hy hyΦ]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · exact h1 j hj
        · exact h2 j hj
      · intro h
        exact ⟨fun j hj => h j (Finset.mem_union_left _ hj), fun j hj => h j (Finset.mem_union_right _ hj)⟩)
  have hcard : (S₀ ∪ V).card = S₀.card + V.card := Finset.card_union_of_disjoint hdisj
  have hle : S₀.card + V.card ≤ n := by
    rw [← hcard]
    simpa using Finset.card_le_univ (S₀ ∪ V)
  refine ⟨n - S₀.card, n - V.card, hNa, hHb, by omega, ?_⟩
  have he : n - S₀.card + (n - V.card) - n = n - (S₀ ∪ V).card := by
    rw [hcard]
    omega
  rw [he]
  exact hNH

/-! ### Member loci of carriers of the same dimension -/

/-- **Member loci of carriers of the same dimension** (BM08, proof of Theorem 6.1): if `N`, `P` are transverse to the
SNC divisor `E`, `N` is closed, `S ⊆ P`, and `N`, `P` have the same regular dimensions at `x ∈ P`, then `x` in the member
locus of `S` along `N` is in that along `P`. -/
theorem mem_memberInterLocus_of_regularAtDim_iff (hn : 0 < n) {N P S : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hNc : IsClosed N) (hNT : IsTransverse n N E) (hPT : IsTransverse n P E) {x : M}
    (hxP : x ∈ P) (hSP : S ⊆ P) (hdim : ∀ j, RegularAtDim (n := n) N x j ↔ RegularAtDim (n := n) P x j)
    (h : x ∈ memberInterLocus N E S) : x ∈ memberInterLocus P E S := by
  classical
  obtain ⟨hxS, hev⟩ := h
  obtain ⟨a', b', hPa, hHb', hab', hPH⟩ := exists_regularAtDim_inter_membersThrough hPT hxP
  have hxN : x ∈ N := ((hdim a').mpr hPa).2.1
  obtain ⟨a, b, hNa, hHb, hab, hNH⟩ := exists_regularAtDim_inter_membersThrough hNT hxN
  have ha : a = a' := eq_of_regularAtDim ((hdim a).mp hNa) hPa
  have hb : b = b' := eq_of_regularAtDim hHb hHb'
  subst ha hb
  have hA : IsComplexAnalyticSubset (n := n) (N ∩ membersThrough E x) := by
    show IsComplexAnalyticSubset (n := n) (N ∩ {z | ∀ H ∈ E, x ∈ H → z ∈ H})
    rw [MemberInterLocusAlong.setOf_forall_mem_eq_memberInter]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hNc hE hNT _)
  have hAH : ∀ᶠ y in 𝓝 x, y ∈ N ∩ membersThrough E x → y ∈ P ∩ membersThrough E x := by
    filter_upwards [hev] with y hy hyA
    exact ⟨hSP (hy hyA.1 (mem_membersThrough_iff.mp hyA.2)), hyA.2⟩
  have hloc : LocDimGE (n := n) (N ∩ membersThrough E x) x (a + b - n) := fun U hU =>
    ⟨x, mem_of_mem_nhds hU, _, le_rfl, hNH⟩
  have hfill := CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE hA hPH hAH hloc
  refine ⟨hxS, ?_⟩
  filter_upwards [hfill, hev] with y hy hyev hyP hyE
  have hyN := (hy.mpr ⟨hyP, mem_membersThrough_iff.mpr hyE⟩).1
  exact hyev hyN hyE

/-- **The symmetric form.** -/
theorem mem_memberInterLocus_iff_of_regularAtDim_iff (hn : 0 < n) {N P S : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hNc : IsClosed N) (hPc : IsClosed P) (hNT : IsTransverse n N E)
    (hPT : IsTransverse n P E) {x : M} (hSN : S ⊆ N) (hSP : S ⊆ P) (hxS : x ∈ S)
    (hdim : ∀ j, RegularAtDim (n := n) N x j ↔ RegularAtDim (n := n) P x j) :
    x ∈ memberInterLocus N E S ↔ x ∈ memberInterLocus P E S :=
  ⟨mem_memberInterLocus_of_regularAtDim_iff hn hE hNc hNT hPT (hSP hxS) hSP hdim,
    mem_memberInterLocus_of_regularAtDim_iff hn hE hPc hPT hNT (hSN hxS) hSN fun j => (hdim j).symm⟩

end Coord

/-! ### The special points of the Step 1 skeleton -/

section Special

open Hironaka.StepOneValue (barMarked origMembers level IsSpecial)

variable {X : CMfd.{u} n}

/-- The original members (hence the levels) depend only on the boundary. -/
theorem origMembers_eq_of_E_eq {A B : MarkedIdeal n X} (hE : A.E = B.E) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    origMembers A T = origMembers B T := by
  unfold origMembers
  rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked A) (𝔫 := barMarked B) hE T, hE]

theorem level_eq_of_E_eq {A B : MarkedIdeal n X} (hE : A.E = B.E) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    level A T y = level B T y := by
  unfold level
  rw [origMembers_eq_of_E_eq hE T]

/-- **The special points agree** (BPRIME-PLAN D4, L-spec, P2): for Włodarczyk-equivalent marked ideals of the native
domain whose carriers have the same local dimension on the cosupport, at every stage of a common test tower the special
points of the Step 1 skeleton (codimension-one part at level `0`, member locus at level `≥ 1`) coincide. -/
theorem isSpecial_iff_of_wEquiv (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hW : WEquiv A B) (hdim : SameCarrierDim A B) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) (y : Y) : IsSpecial A T y ↔ IsSpecial B T y := by
  have hwA := StepOneLowerDomain.isWellFormed_barMarked A hA.isWellFormed
  have hwB := StepOneLowerDomain.isWellFormed_barMarked B hB.isWellFormed
  have hbA : WEquiv (barMarked A) A := StepOneBridge.barMarked_wEquiv A hA
  have hbB : WEquiv (barMarked B) B := StepOneBridge.barMarked_wEquiv B hB
  have hbAB : WEquiv (barMarked A) (barMarked B) := hbA.trans (hW.trans hbB.symm)
  have hcA : (barMarked A).cosupp = A.cosupp :=
    StepOneLowerDomain.cosupp_barMarked A hA.isWellFormed hA.one_le_d
  have hdimb : SameCarrierDim (barMarked A) (barMarked B) := fun x hx j => hdim x (hcA ▸ hx) j
  have hTb : IsGeoTestTower (barMarked A) T := (hbA.2 T).1.mpr hT
  have hcos : (geoTransformAlong (barMarked A) T).cosupp = (geoTransformAlong (barMarked B) T).cosupp :=
    (hbAB.2 T).2 hTb
  have hTbB : IsGeoTestTower (barMarked B) T := (hbAB.2 T).1.mp hTb
  have hwAT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwA T hTb
  have hwBT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwB T hTbB
  have hdimT := HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hwA hwB hbAB hdimb T hTb
  have hcodim := HironakaG8SpecialLoci.codimOnePartAlong_geoTransformAlong_eq hwA hwB hbAB hdimb T hTb
  have hE : A.E = B.E := hW.1
  have horig := origMembers_eq_of_E_eq hE T
  have hlev := level_eq_of_E_eq hE T y
  have hEA : IsSNCDivisor n (origMembers A T) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hwAT.isSNCDivisor
      (List.take_sublist A.E.length (geoTransformAlong (barMarked A) T).E)
  have htrA : IsTransverse n (geoTransformAlong (barMarked A) T).N (origMembers A T) :=
    NormalCrossingsComparison.isTransverse_of_forall_mem hwAT.isTransverse
      (fun H hH => List.take_subset A.E.length _ hH)
  have htrB : IsTransverse n (geoTransformAlong (barMarked B) T).N (origMembers A T) := by
    rw [horig]
    exact NormalCrossingsComparison.isTransverse_of_forall_mem hwBT.isTransverse
      (fun H hH => List.take_subset B.E.length _ hH)
  have hmem : y ∈ memberInterLocus (geoTransformAlong (barMarked A) T).N (origMembers A T)
      (geoTransformAlong (barMarked A) T).cosupp ↔
      y ∈ memberInterLocus (geoTransformAlong (barMarked B) T).N (origMembers B T)
        (geoTransformAlong (barMarked B) T).cosupp := by
    rw [← horig, ← hcos]
    constructor
    · intro h
      exact mem_memberInterLocus_of_regularAtDim_iff hn hEA hwAT.isClosedSubmanifold_N.1 htrA htrB
        ((geoTransformAlong (barMarked B) T).cosupp_subset_N (hcos ▸ h.1))
        (fun z hz => (geoTransformAlong (barMarked B) T).cosupp_subset_N (hcos ▸ hz))
        (hdimT y h.1) h
    · intro h
      exact mem_memberInterLocus_of_regularAtDim_iff hn hEA hwBT.isClosedSubmanifold_N.1 htrB htrA
        ((geoTransformAlong (barMarked A) T).cosupp_subset_N h.1)
        (fun z hz => (geoTransformAlong (barMarked A) T).cosupp_subset_N hz)
        (fun j => (hdimT y h.1 j).symm) h
  unfold IsSpecial
  rw [hlev, hcodim, hmem]

end Special

end

end Hironaka.HironakaG8MemberLoci
