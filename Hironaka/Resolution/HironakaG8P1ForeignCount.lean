import Hironaka.Resolution.HironakaActualSharedCartierTraceTests
import Hironaka.Resolution.HironakaActualPolymorphicBornExponent
import Hironaka.Resolution.HironakaG8MemberLoci

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Cartier count of a record along ANOTHER carrier's Cartier family (G8B lane, run 0080; port P1, step (iii))

Blueprint: `hironaka-g8-p1-foreign-count.tex`.  Plan: `work/hironaka-resume-20261111/G8B/REPORT-r1.md` §2 (iii);
lane G11B's `BPRIME-PLAN.md` §2, port P1.

Source: Bierstone–Milman 2008, "Functoriality in resolution of singularities", §6, proof of Theorem 6.1
(`references/bierstone-milman08-functoriality/source/functorial.tex`, lines 1300–1338): after the arc blowups, the
centres are `C_{j+i} = D_{j+i} ∩ N_{j+i}`; for a second marked ideal on a carrier `P` of the same dimension, "`D ∩ cosupp`
contains a smooth subvariety of codimension `r` in `D`" forces `D ∩ cosupp = D ∩ N = D ∩ P` at the arc point.  This
module proves that argument LOCALLY, for the library's Cartier families (`CartierGeometryFamily`, centres
`N_s ∩ D_s`, built from one carrier `N`):

* `regularAtDim_inter_of_mem`: for `E` transverse to `N` and a member `D ∋ z`, `N ∩ D` is regular of dimension
  `dim_z N - 1` at `z` (and `dim_z N ≥ 1`);
* `eventually_mem_iff_of_subset`: a closed submanifold inside a set regular of the SAME dimension at `z` agrees with it
  near `z` (filling lemma `CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE`);
* `isDivNearAlong_congr_set`: `IsDivNearAlong` only sees the germ of the divisor set;
* **`foreign_count`**: let `G` be a Cartier family (carrier sets `N_s`, centres `N_s ∩ D_s`, arc points `z_s`) and `Q` a
  marked ideal in the native domain with the same boundary, whose carrier `P` may differ from `N`.  If at stage `0` the
  arc point `z_0`, when on `P`, has exponent `β` along `D_0` for `Q` and `dim_{z_0} N = dim_{z_0} P`, then along every
  stage `s` at which the family is a multiple test blowup of `Q`: `s·d ≤ β`, and (when `z_s ∈ P_s`) the exponent at `z_s`
  is `β - s·d` and the dimensions agree.  Admissibility of `N_s ∩ D_s` for `Q` puts it inside `P_s ∩ D_s`; both are
  regular of dimension `dim - 1` at `z_s`, so they agree near `z_s`, and the step is `Q`'s own Cartier step there
  (`HironakaActualPolymorphicBornExponent.controlled_born_divisibility`,
  `HironakaActualCartierTraceSuccessor.isDivNearAlong_inter_carrier_iff`).  No connectedness, no global equality of
  centres: only germs at the arc points.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ForeignCount

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec NormalCrossings DivisorExponentAlong GermIdealOrder
  BlowupStrictSubmanifold HironakaActualSharedCartierTraceTests

noncomputable section

/-! ### Germs of nested submanifolds -/

section Germ

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The coordinate subspace of a union is the intersection. -/
theorem coordSubspace_union (S T : Finset (Fin n)) :
    coordSubspace (S ∪ T) = coordSubspace S ∩ coordSubspace T := by
  classical
  ext w
  simp only [coordSubspace, Finset.mem_union, Set.mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨h1, h2⟩ j (hj | hj)
    · exact h1 j hj
    · exact h2 j hj

/-- **The trace of a transverse member has codimension one in the carrier**: for `E` transverse to `N`, `D ∈ E` and
`z ∈ N ∩ D` with `N` regular of dimension `a` at `z`, `1 ≤ a` and `N ∩ D` is regular of dimension `a - 1` at `z`. -/
theorem regularAtDim_inter_of_mem {N D : Set M} {E : List (Set M)} (hT : IsTransverse n N E) (hD : D ∈ E)
    {z : M} (hzN : z ∈ N) (hzD : z ∈ D) {a : ℕ} (ha : RegularAtDim (n := n) N z a) :
    1 ≤ a ∧ RegularAtDim (n := n) (N ∩ D) z (a - 1) := by
  classical
  obtain ⟨i, rfl⟩ := List.get_of_mem hD
  obtain ⟨S₀, S, ⟨Φ, hsrc, h0, hflat⟩, hS⟩ := hT z hzN
  obtain ⟨hcard, hdisj⟩ := hS i hzD
  have hN : ∀ {y : M}, y ∈ (complexChartAt (n := n) z).val.source →
      (complexChartAt (n := n) z).val y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) z).val y) ∈ coordSubspace S₀) :=
    fun hy hyΦ => hflat none hzN hy hyΦ
  have hDi : ∀ {y : M}, y ∈ (complexChartAt (n := n) z).val.source →
      (complexChartAt (n := n) z).val y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) z).val y) ∈ coordSubspace (S i)) :=
    fun hy hyΦ => hflat (some i) hzD hy hyΦ
  have hND : ∀ {y : M}, y ∈ (complexChartAt (n := n) z).val.source →
      (complexChartAt (n := n) z).val y ∈ Φ.source →
        (y ∈ N ∩ E.get i ↔ Φ.toFun ((complexChartAt (n := n) z).val y) ∈ coordSubspace (S₀ ∪ S i)) := by
    intro y hy hyΦ
    rw [coordSubspace_union, mem_inter_iff, mem_inter_iff]
    exact and_congr (hN hy hyΦ) (hDi hy hyΦ)
  have h1 := HironakaG8MemberLoci.regularAtDim_of_flat_coordSubspace Φ hsrc h0 hN
  have h2 := HironakaG8MemberLoci.regularAtDim_of_flat_coordSubspace Φ hsrc h0 hND
  have ha' : a = n - S₀.card := RegularPointDimension.eq_of_regularAtDim ha h1
  have hcard' : (S₀ ∪ S i).card = S₀.card + 1 := by
    rw [Finset.card_union_of_disjoint hdisj.symm, hcard]
  have hle : (S₀ ∪ S i).card ≤ n := by
    simpa using Finset.card_le_univ (S₀ ∪ S i)
  refine ⟨by omega, ?_⟩
  have he : n - (S₀ ∪ S i).card = a - 1 := by omega
  rw [he] at h2
  exact h2

/-- **Germ equality of nested submanifolds of equal dimension**: a closed submanifold `S` inside `T` near `z`, both regular
of dimension `k` at `z`, agrees with `T` near `z`. -/
theorem eventually_mem_iff_of_subset {S T : Set M} {z : M} {k : ℕ} (hS : IsClosedSubmanifold n S)
    (hSk : RegularAtDim (n := n) S z k) (hTk : RegularAtDim (n := n) T z k)
    (hST : ∀ᶠ y in 𝓝 z, y ∈ S → y ∈ T) : ∀ᶠ y in 𝓝 z, y ∈ S ↔ y ∈ T :=
  CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hS) hTk hST
    (AnalyticDimensionBasics.locDimGE_of_regularAtDim hSk)

/-- `IsDivNearAlong` only depends on the germ at the point of the divisor set. -/
theorem isDivNearAlong_congr_set {N H H' : Set M} {𝔞 : GermIdeal n M} {e : ℕ} {z : M}
    (h : ∀ᶠ y in 𝓝 z, y ∈ H ↔ y ∈ H') :
    IsDivNearAlong n N 𝔞 H e z ↔ IsDivNearAlong n N 𝔞 H' e z := by
  constructor
  · intro hd
    filter_upwards [hd, h] with y hy hyH hyN hyH'
    exact hy hyN (hyH.mpr hyH')
  · intro hd
    filter_upwards [hd, h] with y hy hyH hyN hyH0
    exact hy hyN (hyH.mp hyH0)

end Germ

/-! ### The count along a foreign Cartier family -/

section Count

variable {m : ℕ} {Y : CMfd.{u} m}

/-- Along a Cartier family, the boundary of any record with the family's initial boundary is the family's boundary. -/
theorem E_geoTransformAlong_state (G : CartierGeometryFamily Y) (Q : MarkedIdeal m Y)
    (h0 : (Q.geoTransformAlong (G.state 0).R).E = (G.state 0).E) :
    ∀ s, (Q.geoTransformAlong (G.state s).R).E = (G.state s).E
  | 0 => h0
  | s + 1 => by
    have ih := E_geoTransformAlong_state G Q h0 s
    rw [G.stepTower s, geoTransformAlong_step, geoTransform_E, G.stepE s, ih]

/-- **The foreign invariant at stage `s`**: if the arc point `z_s` of the family lies on the carrier of `Q_s`, then the
exponent of `Q_s` along the last member `D_s` at `z_s` is `β - s·d` (in all degrees), and the family's carrier and
`Q_s`'s carrier have the same dimension at `z_s`. -/
def ForeignInv (G : CartierGeometryFamily Y) (Q : MarkedIdeal m Y) (beta s : ℕ) : Prop :=
  (G.state s).z ∈ (Q.geoTransformAlong (G.state s).R).N →
    (∀ e, IsDivNearAlong m (Q.geoTransformAlong (G.state s).R).N (Q.geoTransformAlong (G.state s).R).ideal
        ((G.state s).E.get (G.state s).i) e (G.state s).z ↔ e ≤ beta - s * Q.d) ∧
      ∃ k, RegularAtDim (n := m) (G.state s).N (G.state s).z k ∧
        RegularAtDim (n := m) (Q.geoTransformAlong (G.state s).R).N (G.state s).z k

/-- **BM08 Theorem 6.1, the count along another carrier's Cartier family** (step (iii) of P1): along every stage at
which the family is a multiple test blowup of `Q`, `s·d ≤ β`, and the foreign invariant propagates. -/
theorem foreign_count (G : CartierGeometryFamily Y) (Q : MarkedIdeal m Y) {k : ℕ} (hQ : IsInvDomain k Q)
    (beta : ℕ) (hE0 : (Q.geoTransformAlong (G.state 0).R).E = (G.state 0).E) (h0 : ForeignInv G Q beta 0) :
    ∀ s, IsGeoTestTower Q (G.state s).R → s * Q.d ≤ beta ∧ ForeignInv G Q beta s := by
  intro s
  induction s with
  | zero => exact fun _ => ⟨by simp, h0⟩
  | succ s ih =>
    intro ht
    set a := G.state s with ha
    set S := Q.geoTransformAlong a.R with hS
    set D := a.E.get a.i with hD
    set C := a.N ∩ D with hC
    have hstep : (G.state (s + 1)).R = BlowupTower.step a.R C (G.π s) (G.hπ s) := G.stepTower s
    have hrec : Q.geoTransformAlong (G.state (s + 1)).R = S.geoTransform C (G.π s) := by
      rw [hstep, geoTransformAlong_step]
    have ht' : IsGeoTestTower Q a.R ∧ S.IsAdmissibleCentre C := by
      have h := ht
      rw [hstep] at h
      exact h
    obtain ⟨hts, hadm⟩ := ht'
    obtain ⟨hbound, hinv⟩ := ih hts
    have hzC : a.z ∈ C := a.hz
    have hCS : C ⊆ S.cosupp := hadm.2.1
    have hzP : a.z ∈ S.N := S.cosupp_subset_N (hCS hzC)
    obtain ⟨hExp, kN, hkN, hkP⟩ := hinv hzP
    have hDom : IsInvDomain k S := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ a.R hts
    have hWF := hDom.isWellFormed
    have hEq : S.E = a.E := E_geoTransformAlong_state G Q hE0 s
    have hDmemA : D ∈ a.E := List.get_mem _ _
    have hDmemS : D ∈ S.E := hEq ▸ hDmemA
    obtain ⟨hk1, hCdim⟩ := regularAtDim_inter_of_mem a.hT hDmemA hzC.1 hzC.2 hkN
    obtain ⟨-, hPDdim⟩ := regularAtDim_inter_of_mem hWF.isTransverse hDmemS hzP hzC.2 hkP
    have hgerm : ∀ᶠ y in 𝓝 a.z, y ∈ C ↔ y ∈ S.N ∩ D :=
      eventually_mem_iff_of_subset hadm.1 hCdim hPDdim
        (Eventually.of_forall fun y hy => ⟨S.cosupp_subset_N (hCS hy), hy.2⟩)
    have hdS : S.d = Q.d := d_geoTransformAlong Q a.R
    -- the bound
    have hdiv : IsDivNearAlong m S.N S.ideal D Q.d a.z := by
      filter_upwards [hgerm] with y hy hyN hyD
      have hyc : y ∈ S.cosupp := hCS (hy.mpr ⟨hyN, hyD⟩)
      have hyc' : y ∈ cosupport m S.N S.ideal S.d := hyc
      rw [hdS] at hyc'
      exact hyc'
    have hle : Q.d ≤ beta - s * Q.d := (hExp Q.d).mp hdiv
    have hbound' : (s + 1) * Q.d ≤ beta := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    refine ⟨hbound', ?_⟩
    -- the invariant at `s + 1`
    intro hz'
    set z' := (G.state (s + 1)).z with hz'def
    have hz'S : z' ∈ (S.geoTransform C (G.π s)).N := by
      rw [← hrec]
      exact hz'
    have hmap : G.π s z' = a.z := G.pointMap s
    have hz'C : G.π s z' ∈ C := by rw [hmap]; exact hzC
    have hborn : (G.state (s + 1)).E.get (G.state (s + 1)).i = G.π s ⁻¹' C := G.bornSlot s
    refine ⟨?_, ?_⟩
    · intro e
      rw [hrec, hborn]
      rw [HironakaActualPolymorphicBornExponent.controlled_born_divisibility S hWF.isClosedSubmanifold_N
        hWF.isCoherent hadm (G.hπ s) hz'S hz'C e, hmap, isDivNearAlong_congr_set hgerm,
        HironakaActualCartierTraceSuccessor.isDivNearAlong_inter_carrier_iff, hExp, hdS]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · refine ⟨kN, ?_, ?_⟩
      · have hNz : z' ∈ geoStrictTransform (G.π s) C a.N := by
          have h := (G.state (s + 1)).hz.1
          rw [G.stepN s] at h
          exact h
        have h := regularAtDim_geoStrictTransform_of_mem (G.hπ s) (Nat.sub_le kN 1)
          (by rw [hmap]; exact hCdim) (by rw [hmap]; exact hkN) inter_subset_left hNz
        rw [G.stepN s]
        exact h
      · have hPz : z' ∈ geoStrictTransform (G.π s) C S.N := hz'S
        have h := regularAtDim_geoStrictTransform_of_mem (G.hπ s) (Nat.sub_le kN 1)
          (by rw [hmap]; exact hCdim) (by rw [hmap]; exact hkP)
          (fun y hy => S.cosupp_subset_N (hCS hy)) hPz
        rw [hrec]
        exact h

end Count

end

end Hironaka.HironakaG8P1ForeignCount
