import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary

/-!
# The genuine whole limit carrier and its entire transverse boundary

The independently defined ALL-stage limit strict carrier is regular and is
transverse to every original/birth label of the SAME actual history.  These
are geometric inputs to a genuine whole limit marked record; no coherent
limit ideal or resolving locally finite scheduler is assumed or constructed.
Blueprint: `hironaka-actual-locally-finite-carrier-transverse-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualLocallyFiniteCarrierTransverse
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HomogenizedGlueingTower HironakaSharpActualCurveBirthBoundaryOverlaps
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryFactors
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLocallyFiniteBoundary
attribute [local instance] limitChartedSpace
variable {n : ℕ} {X : CMfd.{u} n}

/-- One genuine chart for the carrier and EVERY indexed boundary member
through the point, with its actual normal coordinate disjoint from the carrier. -/
def IsTransverseBoundaryFamily (n : ℕ) {Q : Type u} [TopologicalSpace Q]
    [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q] {ι : Type v}
    (N : Set Q) (D : ι → Set Q) : Prop :=
  ∀ x ∈ N,∃ (S₀ : Finset (Fin n)) (S : ι → Finset (Fin n)),
    IsCoordinateFamilyAt n (fun o : Option ι => o.elim N D)
      (fun o => o.elim S₀ S) x ∧
      ∀ i,x∈D i → (S i).card=1 ∧ Disjoint (S i) S₀

private theorem readout_get {Q : Type u} (E : List (Set Q)) (i : Fin E.length) :
    boundaryReadout E i.val=E.get i := List.getD_eq_getElem E ∅ i.isLt

private theorem lt_length_of_mem_readout {Q : Type u} (E : List (Set Q))
    {k : ℕ} {x : Q} (hx : x∈boundaryReadout E k) : k<E.length := by
  by_contra hk
  rw [boundaryReadout,List.getD_eq_default E ∅ (Nat.le_of_not_gt hk)] at hx
  exact hx

/-- The exact finite-list and whole padded indexed transversality notions coincide. -/
theorem isTransverseBoundaryFamily_boundaryReadout_iff {Q : CMfd.{u} n}
    (N : Set Q) (E : List (Set Q)) :
    IsTransverseBoundaryFamily n N (boundaryReadout E) ↔ IsTransverse n N E := by
  constructor
  · intro h x hx
    obtain ⟨S₀,S,hcoord,hcard⟩ := h x hx
    refine ⟨S₀,fun i => S i.val,?_,?_⟩
    · exact IsCoordinateFamilyAt.reindex hcoord (Option.map Fin.val)
        (by rintro (_|i);rfl;exact (readout_get E i).symm)
        (by rintro (_|i) <;> rfl)
    · intro i hi
      exact hcard i.val ((readout_get E i).symm ▸ hi)
  · intro h x hx
    obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩ := h x hx
    let A : ℕ → Finset (Fin n) := fun k => if hk : k<E.length then S ⟨k,hk⟩ else ∅
    refine ⟨S₀,A,⟨Φ,hsrc,hzero,?_⟩,?_⟩
    · rintro (_|k) hk y hy hyΦ
      · exact hcoord none hx hy hyΦ
      · have hlen := lt_length_of_mem_readout E hk
        have he := readout_get E ⟨k,hlen⟩
        have hp := hcoord (some ⟨k,hlen⟩) ((Set.ext_iff.mp he x).mp hk) hy hyΦ
        simpa only [Option.elim_some,A,dif_pos hlen,←he] using hp
    · intro k hk
      have hlen := lt_length_of_mem_readout E hk
      change (if h : k<E.length then S ⟨k,h⟩ else ∅).card=1 ∧
        Disjoint (if h : k<E.length then S ⟨k,h⟩ else ∅) S₀
      rw [dif_pos hlen]
      exact hcard ⟨k,hlen⟩ ((Set.ext_iff.mp (readout_get E ⟨k,hlen⟩) x).mp hk)

/-- The independently defined whole carrier agrees with the SAME actual
transformed carrier on every constructed stable endpoint. -/
theorem localInclusion_preimage_limitCarrier (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    (actualHistoryLocalInclusion s hLF x) ⁻¹' limitStrictTransform s hLF M.N=
      (Subtype.val : localEndpoint s hLF x → (s.stage (stableIndex s hLF x)).1) ⁻¹'
        (geoTransformAlong M (s.stage (stableIndex s hLF x)).2).N := by
  rw [N_geoTransformAlong]
  exact localInclusion_preimage_limitStrictTransform s hLF hM.isClosedSubmanifold_N.1 x

private theorem carrier_trace (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    (Subtype.val : limitWindow s hLF (stableWindow s hLF x) → limitManifold s hLF) ⁻¹'
      limitStrictTransform s hLF M.N=
    (stableWindowDiffeomorph s hLF x).symm ⁻¹'
      ((Subtype.val : localEndpoint s hLF x → (s.stage (stableIndex s hLF x)).1) ⁻¹'
        (geoTransformAlong M (s.stage (stableIndex s hLF x)).2).N) := by
  ext z
  let e := stableWindowDiffeomorph s hLF x
  have hh := Set.ext_iff.mp (localInclusion_preimage_limitCarrier M hM s hLF x) (e.symm z)
  have heval : actualHistoryLocalInclusion s hLF x (e.symm z)=z.val :=
    congrArg Subtype.val (e.apply_symm_apply z)
  change actualHistoryLocalInclusion s hLF x (e.symm z)∈limitStrictTransform s hLF M.N ↔
    (e.symm z).val∈(geoTransformAlong M (s.stage (stableIndex s hLF x)).2).N at hh
  rw [heval] at hh
  exact hh

/-- The independently defined ALL-stage strict carrier is globally closed and
regular, internally from original well-formedness and actual test prefixes. -/
theorem isClosedSubmanifold_limitCarrier (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j,IsGeoTestTower M (s.stage j).2) :
    IsClosedSubmanifold n (limitStrictTransform s hLF M.N) := by
  refine ⟨isClosed_limitStrictTransform s hLF hM.isClosedSubmanifold_N.1,?_⟩
  intro z hz
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  let e := stableWindowDiffeomorph s hLF x
  let N := stableIndex s hLF x
  let A : Set (localEndpoint s hLF x) :=
    (Subtype.val : localEndpoint s hLF x → (s.stage N).1) ⁻¹'
      (geoTransformAlong M (s.stage N).2).N
  have hq : q∈A := (Set.ext_iff.mp (localInclusion_preimage_limitCarrier M hM s hLF x) q).mp hz
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (s.stage N).2 (hT N)
  obtain ⟨k,hk⟩ := hw.isClosedSubmanifold_N.2 q.val hq
  have hqreg : RegularAtDim (n := n) A q k := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hk
  have hqreg' : RegularAtDim (n := n) A (e.symm (e q)) k := by rwa [e.symm_apply_apply]
  have hreg := RegularAtDimTransport.regularAtDim_of_preimage e.symm.contMDiff
    (MarkedIdealTowerTransport.notMem_exceptionalLocus e.symm (e q))
    isOpen_univ (mem_univ (e q)) (fun _ _ => Iff.rfl) hqreg'
  change RegularAtDim (n := n) (e.symm ⁻¹' A) (e q) k at hreg
  rw [←carrier_trace M hM s hLF x] at hreg
  exact ⟨k,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hreg⟩

private theorem coordinates_of_open_diffeomorph {Q P : CMfd.{u} n} {ι : Type v}
    (U : Opens Q) (e : P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (D : ι → Set Q) (S : ι → Finset (Fin n)) (q : P)
    (h : IsCoordinateFamilyAt n (fun i => (fun p : P => (e p).val) ⁻¹' D i) S q) :
    IsCoordinateFamilyAt n D S (e q).val := by
  have hq : IsCoordinateFamilyAt n
      (fun i => (fun p : P => (e p).val) ⁻¹' D i) S (e.symm (e q)) := by
    rwa [e.symm_apply_apply]
  have hc := isCoordinateFamilyAt_of_preimage
    e.symm.contMDiff (MarkedIdealTowerTransport.notMem_exceptionalLocus e.symm (e q))
    isOpen_univ (mem_univ (e q)) (fun _ _ _ => Iff.rfl) hq
  have heq : (fun i => e.symm ⁻¹' ((fun p : P => (e p).val) ⁻¹' D i))=
      fun i => (Subtype.val : U → Q) ⁻¹' D i := by
    funext i
    ext p
    simp only [mem_preimage,e.apply_symm_apply]
  change IsCoordinateFamilyAt n
    (fun i => e.symm ⁻¹' ((fun p : P => (e p).val) ⁻¹' D i)) S (e q) at hc
  rw [heq] at hc
  exact isCoordinateFamilyAt_preimage_val_iff.mp hc

/-- Actual well-formed prefixes produce transversality of the genuine limit
carrier to the ENTIRE already constructed indexed boundary, retaining all labels. -/
theorem isTransverseBoundaryFamily_limitCarrier (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j,IsGeoTestTower M (s.stage j).2) :
    IsTransverseBoundaryFamily n (limitStrictTransform s hLF M.N) (limitBoundaryMember M s hLF) := by
  intro z hz
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  let N := stableIndex s hLF x
  let E := (geoTransformAlong M (s.stage N).2).E
  let A : Set (localEndpoint s hLF x) :=
    (Subtype.val : localEndpoint s hLF x → (s.stage N).1) ⁻¹'
      (geoTransformAlong M (s.stage N).2).N
  let B : List (Set (localEndpoint s hLF x)) :=
    E.map ((Subtype.val : localEndpoint s hLF x → (s.stage N).1) ⁻¹' ·)
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (s.stage N).2 (hT N)
  have hB : IsTransverse n A B := isTransverse_preimage (pullsBackCoordinates_val _) hw.isTransverse
  have hA : A=(actualHistoryLocalInclusion s hLF x) ⁻¹' limitStrictTransform s hLF M.N :=
    (localInclusion_preimage_limitCarrier M hM s hLF x).symm
  have hFamily : boundaryReadout B=fun k =>
      (actualHistoryLocalInclusion s hLF x) ⁻¹' limitBoundaryMember M s hLF k := by
    funext k
    rw [boundaryReadout_map_preimage]
    exact (localInclusion_preimage_limitBoundaryMember M hM s hLF hT x k).symm
  have hq : q∈A := (Set.ext_iff.mp hA q).mpr hz
  obtain ⟨S₀,S,hcoord,hcard⟩ := (isTransverseBoundaryFamily_boundaryReadout_iff A B).mpr hB q hq
  rw [hA,hFamily] at hcoord
  rw [hFamily] at hcard
  have hAll : (fun o : Option ℕ => o.elim
      ((actualHistoryLocalInclusion s hLF x) ⁻¹' limitStrictTransform s hLF M.N)
      (fun k => (actualHistoryLocalInclusion s hLF x) ⁻¹' limitBoundaryMember M s hLF k))=
      fun o : Option ℕ => (actualHistoryLocalInclusion s hLF x) ⁻¹'
        o.elim (limitStrictTransform s hLF M.N) (limitBoundaryMember M s hLF) := by
    funext o
    cases o <;> rfl
  rw [hAll] at hcoord
  refine ⟨S₀,S,?_,hcard⟩
  exact coordinates_of_open_diffeomorph (limitWindow s hLF (stableWindow s hLF x))
    (stableWindowDiffeomorph s hLF x)
    (fun o : Option ℕ => o.elim (limitStrictTransform s hLF M.N) (limitBoundaryMember M s hLF))
    (fun o => o.elim S₀ S) q hcoord

end
end Hironaka.HironakaActualLocallyFiniteCarrierTransverse
