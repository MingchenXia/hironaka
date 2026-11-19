import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
import Hironaka.Blowup.SimultaneousNormalCrossings

/-! Actual continuation of a locally finite indexed SNC boundary through a
genuine global normal-crossings blowup, retaining every old index and a
separate born label. Fair noncompact scheduler existence is separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualLocallyFiniteBoundaryContinuation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings NormalCrossingsInvariance
  HironakaActualLocallyFiniteBoundary
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual simultaneous coordinate witnesses for the centre and the ENTIRE
indexed boundary. This is the indexed original normal-crossings condition. -/
def HasNormalCrossingsWithIndexedBoundary (C : Set X) (D : ℕ → Set X) : Prop :=
  ∀x∈C,∃(S₀ : Finset (Fin n))(S : ℕ → Finset (Fin n)),
    IsCoordinateFamilyAt n (fun o : Option ℕ=>o.elim C D) (fun o=>o.elim S₀ S) x ∧
    ∀i,x∈D i → (S i).card=1

private theorem prefix_get (D : ℕ → Set X) (N : ℕ)
    (i : Fin (List.ofFn (fun j : Fin N=>D j.val)).length) :
    (List.ofFn (fun j : Fin N=>D j.val)).get i=D i.val := by
  simp only [List.get_eq_getElem,List.getElem_ofFn]

theorem isSNCDivisor_finite_prefix (D : ℕ → Set X)
    (hD : IsLocallyFiniteSNCDivisor n D) (N : ℕ) :
    IsSNCDivisor n (List.ofFn (fun i : Fin N=>D i.val)) := by
  refine ⟨?_,?_⟩
  · intro A hA
    obtain ⟨i,rfl⟩:=List.mem_iff_get.mp hA
    rw [prefix_get]
    exact hD.2.1 i.val
  · intro x
    obtain ⟨S,⟨Φ,hsrc,hzero,hcoord⟩,hcard,hinj⟩:=hD.2.2 x
    refine ⟨fun i=>S i.val,⟨Φ,hsrc,hzero,?_⟩,?_,?_⟩
    · intro i hi z hz hzΦ
      change x∈(List.ofFn (fun j : Fin N=>D j.val)).get i at hi
      change z∈(List.ofFn (fun j : Fin N=>D j.val)).get i ↔
        Φ.toFun ((complexChartAt (n := n) x).val z)∈coordSubspace (S i.val)
      rw [prefix_get] at hi ⊢
      exact hcoord i.val hi hz hzΦ
    · intro i hi
      rw [prefix_get] at hi
      exact hcard i.val hi
    · intro i hi j hj heq
      change x∈(List.ofFn (fun j : Fin N=>D j.val)).get i at hi
      change x∈(List.ofFn (fun j : Fin N=>D j.val)).get j at hj
      rw [prefix_get] at hi hj
      exact Fin.ext (hinj hi hj heq)

theorem hasNormalCrossings_finite_prefix (C : Set X) (D : ℕ → Set X)
    (hC : HasNormalCrossingsWithIndexedBoundary C D) (N : ℕ) :
    HasNormalCrossings n C (List.ofFn (fun i : Fin N=>D i.val)) := by
  intro x hx
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩:=hC x hx
  refine ⟨S₀,fun i=>S i.val,⟨Φ,hsrc,hzero,?_⟩,?_⟩
  · intro o ho z hz hzΦ
    cases o with
    | none => exact hcoord none ho hz hzΦ
    | some i =>
      change z∈(List.ofFn (fun j : Fin N=>D j.val)).get i ↔ _
      change x∈(List.ofFn (fun j : Fin N=>D j.val)).get i at ho
      rw [prefix_get] at ho ⊢
      exact hcoord (some i.val) ho hz hzΦ
  · intro i hi
    rw [prefix_get] at hi
    exact hcard i.val hi

/-- Every old label is retained as `some i`; `none` is the new born label. -/
def continuedBoundary (D : ℕ → Set X) (C : Set X) (π : Y → X) : Option ℕ → Set Y :=
  Option.elim' (π ⁻¹' C) (fun i=>geoStrictTransform π C (D i))

theorem isLocallyFiniteSNCDivisor_continuedBoundary
    (D : ℕ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hNC : HasNormalCrossingsWithIndexedBoundary C D) :
    IsLocallyFiniteSNCDivisor n (continuedBoundary D C π) := by
  classical
  have hOldLF : LocallyFinite (fun i=>geoStrictTransform π C (D i)) :=
    (hD.1.preimage_continuous hπ.contMDiff.continuous).subset
      (fun i=>geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hD.2.1 i))
  refine ⟨hOldLF.option_elim' _,?_,?_⟩
  · intro o
    cases o with
    | none => exact hπ.1.1.preimage hπ.contMDiff.continuous
    | some i => exact isClosed_closure
  · intro y
    obtain ⟨b,hb⟩:=(hD.1.point_finite (π y)).bddAbove
    let N:=b+1
    have hInc (i : ℕ) (hi : π y∈D i) : i<N:=Nat.lt_succ_of_le (hb hi)
    let E₀:=List.ofFn (fun i : Fin N=>D i.val)
    let E:=E₀.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    have hE : IsSNCDivisor n E:=
      SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ
        (isSNCDivisor_finite_prefix D hD N) (hasNormalCrossings_finite_prefix C D hNC N)
    have hLen : E.length=N+1:=by simp only [E,E₀,List.length_append,List.length_map,List.length_ofFn,List.length_singleton]
    let last : Fin E.length:=⟨N,by rw [hLen];omega⟩
    let slot : Option ℕ → Fin E.length:=fun o=>
      o.elim last (fun i=>if hi : i<N then ⟨i,by rw [hLen];omega⟩ else last)
    have hGetOld (i : ℕ) (hi : i<N) :
        E.get ⟨i,by rw [hLen];omega⟩=geoStrictTransform π C (D i) := by
      simp only [E,E₀,List.get_eq_getElem,List.getElem_append,List.length_map,List.length_ofFn,
        dif_pos hi,List.getElem_map,List.getElem_ofFn]
    have hGetBorn : E.get last=π ⁻¹' C := by
      change (E₀.map (geoStrictTransform π C) ++ [π ⁻¹' C])[N]'last.isLt=π ⁻¹' C
      exact List.getElem_concat_length (by simp only [List.length_map,E₀,List.length_ofFn]) _
    have hOldBound (i : ℕ) (hi : y∈continuedBoundary D C π (some i)) : i<N:=
      hInc i (geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hD.2.1 i) hi)
    have hSet (o : Option ℕ) (ho : y∈continuedBoundary D C π o) :
        E.get (slot o)=continuedBoundary D C π o := by
      cases o with
      | none => exact hGetBorn
      | some i =>
        have hi:=hOldBound i ho
        simpa only [slot,Option.elim_some,dif_pos hi,continuedBoundary,Option.elim'_some] using hGetOld i hi
    let decode : Fin E.length → Option ℕ:=fun j=>if j.val<N then some j.val else none
    have hDecode (o : Option ℕ) (ho : y∈continuedBoundary D C π o) : decode (slot o)=o := by
      cases o with
      | none => simp [decode,slot,last]
      | some i =>
        have hi:=hOldBound i ho
        simp [decode,slot,hi]
    obtain ⟨S,⟨Φ,hsrc,hzero,hcoord⟩,hcard,hinj⟩:=hE.2 y
    refine ⟨fun o=>S (slot o),⟨Φ,hsrc,hzero,?_⟩,?_,?_⟩
    · intro o ho z hz hzΦ
      have heq:=hSet o ho
      have hy : y∈E.get (slot o):=heq.symm ▸ ho
      have h:=hcoord (slot o) hy hz hzΦ
      change z∈continuedBoundary D C π o ↔ _
      rw [←heq]
      exact h
    · intro o ho
      exact hcard (slot o) ((hSet o ho).symm ▸ ho)
    · intro i hi j hj hij
      change y∈continuedBoundary D C π i at hi
      change y∈continuedBoundary D C π j at hj
      have hiE : y∈E.get (slot i):=(hSet i hi).symm ▸ hi
      have hjE : y∈E.get (slot j):=(hSet j hj).symm ▸ hj
      have hslot : slot i=slot j:=hinj hiE hjE hij
      exact (hDecode i hi).symm.trans ((congrArg decode hslot).trans (hDecode j hj))

open ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryLimit MarkedIdeals.MarkedIdeal
attribute [local instance] limitChartedSpace

/-- Given a genuine next blowup of the SAME actual LF history, its composite
projection to the ORIGINAL base is proper and holomorphic, with the full
continued indexed SNC boundary. No resolving scheduler is asserted. -/
theorem actual_limit_boundary_continuation
    (M : MarkedIdeals.MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀j,IsGeoTestTower M (s.stage j).2)
    {Z : CMfd.{u} n} {C : Set (limitManifold s hLF)} {π : Z → limitManifold s hLF}
    (hπ : IsBlowupAlong n C π)
    (hNC : HasNormalCrossingsWithIndexedBoundary C (limitBoundaryMember M s hLF)) :
    IsProperMap (fun z=>gluedProjection s hLF (π z)) ∧
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z=>gluedProjection s hLF (π z)) ∧
    IsLocallyFiniteSNCDivisor n (continuedBoundary (limitBoundaryMember M s hLF) C π) := by
  let : IsComplexManifold n (HironakaActualLocallyFiniteHistoryOverlap.actualHistoryGluedSpace s hLF) :=
    limitSpace_isComplexManifold s hLF
  refine ⟨(gluedProjection_isProperMap s hLF).comp
    (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong
      (M := limitManifold s hLF) (Z := Z) hπ),
    (gluedProjection_contMDiff s hLF).comp hπ.contMDiff,?_⟩
  exact isLocallyFiniteSNCDivisor_continuedBoundary (limitBoundaryMember M s hLF)
    (isLocallyFiniteSNCDivisor_limitBoundaryMember M hM s hLF hT) hπ hNC

end
end Hironaka.HironakaActualLocallyFiniteBoundaryContinuation
