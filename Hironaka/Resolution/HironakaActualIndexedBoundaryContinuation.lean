import Hironaka.Resolution.HironakaActualLocallyFiniteTransverseContinuation

/-! Whole indexed LF/SNC and carrier transversality continue with every
old label and one distinct born label. The arbitrary source index type
allows another continuation without deleting or renumbering labels. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualIndexedBoundaryContinuation
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupStrictSubmanifold
  NormalCrossings NormalCrossingsInvariance
  HironakaActualLocallyFiniteBoundary HironakaActualLocallyFiniteCarrierTransverse
variable {n : ℕ} {X Y : CMfd.{u} n} {ι : Type v}

def HasNormalCrossingsWithBoundary (C : Set X) (D : ι → Set X) : Prop :=
  ∀x∈C,∃(S₀ : Finset (Fin n))(S : ι → Finset (Fin n)),
    IsCoordinateFamilyAt n (fun o : Option ι=>o.elim C D) (fun o=>o.elim S₀ S) x ∧
    ∀i,x∈D i → (S i).card=1

def finiteBoundary (D : ι → Set X) {N : ℕ} (e : Fin N ↪ ι) : List (Set X) :=
  List.ofFn (fun j=>D (e j))

private theorem finite_get (D : ι → Set X) {N : ℕ} (e : Fin N ↪ ι)
    (i : Fin (finiteBoundary D e).length) :
    (finiteBoundary D e).get i=D (e ⟨i.val,by simpa only [finiteBoundary,List.length_ofFn] using i.isLt⟩) := by
  change (List.ofFn (fun j : Fin N=>D (e j)))[i.val]'_= _
  rw [List.getElem_ofFn]

theorem isSNCDivisor_finiteBoundary (D : ι → Set X)
    (hD : IsLocallyFiniteSNCDivisor n D) {N : ℕ} (e : Fin N ↪ ι) :
    IsSNCDivisor n (finiteBoundary D e) := by
  refine ⟨?_,?_⟩
  · intro A hA
    obtain ⟨i,rfl⟩:=List.mem_iff_get.mp hA
    rw [finite_get]
    exact hD.2.1 _
  · intro x
    obtain ⟨S,⟨Φ,hsrc,hzero,hcoord⟩,hcard,hinj⟩:=hD.2.2 x
    let f : Fin (finiteBoundary D e).length → ι:=fun i=>e ⟨i.val,by simpa only [finiteBoundary,List.length_ofFn] using i.isLt⟩
    have heq (i) : (finiteBoundary D e).get i=D (f i):=finite_get D e i
    refine ⟨fun i=>S (f i),⟨Φ,hsrc,hzero,?_⟩,?_,?_⟩
    · intro i hi z hz hzΦ
      change x∈(finiteBoundary D e).get i at hi
      change z∈(finiteBoundary D e).get i ↔ _
      rw [heq] at hi ⊢
      exact hcoord (f i) hi hz hzΦ
    · intro i hi
      rw [heq] at hi
      exact hcard (f i) hi
    · intro i hi j hj hij
      change x∈(finiteBoundary D e).get i at hi
      change x∈(finiteBoundary D e).get j at hj
      rw [heq] at hi hj
      have h:=e.injective (hinj hi hj hij)
      exact Fin.ext (congrArg (fun t : Fin N=>t.val) h)

theorem hasNormalCrossings_finiteBoundary (C : Set X) (D : ι → Set X)
    (hC : HasNormalCrossingsWithBoundary C D) {N : ℕ} (e : Fin N ↪ ι) :
    HasNormalCrossings n C (finiteBoundary D e) := by
  intro x hx
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩:=hC x hx
  let f : Fin (finiteBoundary D e).length → ι:=fun i=>e ⟨i.val,by simpa only [finiteBoundary,List.length_ofFn] using i.isLt⟩
  have heq (i) : (finiteBoundary D e).get i=D (f i):=finite_get D e i
  refine ⟨S₀,fun i=>S (f i),⟨Φ,hsrc,hzero,?_⟩,?_⟩
  · intro o ho z hz hzΦ
    cases o with
    | none => exact hcoord none ho hz hzΦ
    | some i =>
      change z∈(finiteBoundary D e).get i ↔ _
      change x∈(finiteBoundary D e).get i at ho
      rw [heq] at ho ⊢
      exact hcoord (some (f i)) ho hz hzΦ
  · intro i hi
    rw [heq] at hi
    exact hcard (f i) hi

theorem isTransverse_finiteBoundary (A : Set X) (D : ι → Set X)
    (hT : IsTransverseBoundaryFamily n A D) {N : ℕ} (e : Fin N ↪ ι) :
    IsTransverse n A (finiteBoundary D e) := by
  intro x hx
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩:=hT x hx
  let f : Fin (finiteBoundary D e).length → ι:=fun i=>e ⟨i.val,by simpa only [finiteBoundary,List.length_ofFn] using i.isLt⟩
  have heq (i) : (finiteBoundary D e).get i=D (f i):=finite_get D e i
  refine ⟨S₀,fun i=>S (f i),⟨Φ,hsrc,hzero,?_⟩,?_⟩
  · intro o ho z hz hzΦ
    cases o with
    | none => exact hcoord none ho hz hzΦ
    | some i =>
      change z∈(finiteBoundary D e).get i ↔ _
      change x∈(finiteBoundary D e).get i at ho
      rw [heq] at ho ⊢
      exact hcoord (some (f i)) ho hz hzΦ
  · intro i hi
    rw [heq] at hi
    exact hcard (f i) hi

def continuedBoundary (D : ι → Set X) (C : Set X) (π : Y → X) : Option ι → Set Y :=
  Option.elim' (π ⁻¹' C) (fun i=>geoStrictTransform π C (D i))

theorem indexed_geometry_continuation
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    {A C : Set X} (hA : IsClosed A) (hT : IsTransverseBoundaryFamily n A D)
    (hCA : C⊆A) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hNC : HasNormalCrossingsWithBoundary C D) :
    IsLocallyFiniteSNCDivisor n (continuedBoundary D C π) ∧
    IsTransverseBoundaryFamily n (geoStrictTransform π C A) (continuedBoundary D C π) := by
  classical
  have hOldLF : LocallyFinite (fun i=>geoStrictTransform π C (D i)) :=
    (hD.1.preimage_continuous hπ.contMDiff.continuous).subset
      (fun i=>geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hD.2.1 i))
  have hClosed (o : Option ι) : IsClosed (continuedBoundary D C π o) := by
    cases o with
    | none => exact hπ.1.1.preimage hπ.contMDiff.continuous
    | some i => exact isClosed_closure
  have hFiniteAt (y : Y) : ∃(E : List (Set Y))(slot : Option ι → Fin E.length),
      IsSNCDivisor n E ∧ IsTransverse n (geoStrictTransform π C A) E ∧
      (∀o,y∈continuedBoundary D C π o → E.get (slot o)=continuedBoundary D C π o) ∧
      Set.InjOn slot {o | y∈continuedBoundary D C π o} := by
    let κ:={i : ι // π y∈D i}
    let : Fintype κ:=(hD.1.point_finite (π y)).fintype
    let N:=Fintype.card κ
    let e : Fin N ↪ ι:=⟨fun j=>((Fintype.equivFin κ).symm j).val,
      fun i j h=>(Fintype.equivFin κ).symm.injective (Subtype.ext h)⟩
    let code (i : ι) (hi : π y∈D i) : Fin N:=(Fintype.equivFin κ) ⟨i,hi⟩
    have hCode (i : ι) (hi : π y∈D i) : e (code i hi)=i := by
      change ((Fintype.equivFin κ).symm ((Fintype.equivFin κ) ⟨i,hi⟩)).val=i
      exact congrArg Subtype.val ((Fintype.equivFin κ).symm_apply_apply ⟨i,hi⟩)
    let E₀:=finiteBoundary D e
    let E:=E₀.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    have hSNC : IsSNCDivisor n E:=
      SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ
        (isSNCDivisor_finiteBoundary D hD e) (hasNormalCrossings_finiteBoundary C D hNC e)
    have hTrans : IsTransverse n (geoStrictTransform π C A) E:=
      SimultaneousNormalCrossings.isTransverse_geoTransformE_of_hasNormalCrossings hπ hA hCA
        (isSNCDivisor_finiteBoundary D hD e) (isTransverse_finiteBoundary A D hT e)
        (hasNormalCrossings_finiteBoundary C D hNC e)
    have hLen : E.length=N+1:=by
      simp only [E,E₀,finiteBoundary,List.length_append,List.length_map,List.length_ofFn,List.length_singleton]
    let last : Fin E.length:=⟨N,by rw [hLen];omega⟩
    let slot : Option ι → Fin E.length:=fun o=>o.elim last
      (fun i=>if hi : π y∈D i then ⟨(code i hi).val,by rw [hLen];have h:=(code i hi).isLt;omega⟩ else last)
    have hGetOld (j : Fin N) :
        E.get ⟨j.val,by rw [hLen];have h:=j.isLt;omega⟩=geoStrictTransform π C (D (e j)) := by
      simp only [E,E₀,finiteBoundary,List.get_eq_getElem,List.getElem_append,List.length_map,List.length_ofFn,
        dif_pos j.isLt,List.getElem_map,List.getElem_ofFn]
    have hGetBorn : E.get last=π ⁻¹' C := by
      change (E₀.map (geoStrictTransform π C) ++ [π ⁻¹' C])[N]'last.isLt=π ⁻¹' C
      exact List.getElem_concat_length (by simp only [List.length_map,E₀,finiteBoundary,List.length_ofFn]) _
    have hSource (i : ι) (hi : y∈continuedBoundary D C π (some i)) : π y∈D i:=
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hD.2.1 i) hi
    have hSet (o : Option ι) (ho : y∈continuedBoundary D C π o) :
        E.get (slot o)=continuedBoundary D C π o := by
      cases o with
      | none => exact hGetBorn
      | some i =>
        have hi:=hSource i ho
        simpa only [slot,Option.elim_some,dif_pos hi,hCode,continuedBoundary,Option.elim'_some] using hGetOld (code i hi)
    let decode : Fin E.length → Option ι:=fun j=>if hj : j.val<N then some (e ⟨j.val,hj⟩) else none
    have hDecode (o : Option ι) (ho : y∈continuedBoundary D C π o) : decode (slot o)=o := by
      cases o with
      | none => simp [decode,slot,last]
      | some i =>
        have hi:=hSource i ho
        simp only [slot,Option.elim_some,dif_pos hi,decode,dif_pos (code i hi).isLt]
        exact congrArg some (hCode i hi)
    refine ⟨E,slot,hSNC,hTrans,hSet,?_⟩
    intro i hi j hj heq
    exact (hDecode i hi).symm.trans ((congrArg decode heq).trans (hDecode j hj))
  constructor
  · refine ⟨hOldLF.option_elim' _,hClosed,?_⟩
    intro y
    obtain ⟨E,slot,hE,_hTrans,hSet,hInj⟩:=hFiniteAt y
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
    · intro i hi j hj heq
      have hiE : y∈E.get (slot i):=(hSet i hi).symm ▸ hi
      have hjE : y∈E.get (slot j):=(hSet j hj).symm ▸ hj
      exact hInj hi hj (hinj hiE hjE heq)
  · intro y hy
    obtain ⟨E,slot,_hE,hTrans,hSet,_hInj⟩:=hFiniteAt y
    obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩:=hTrans y hy
    refine ⟨S₀,fun o=>S (slot o),⟨Φ,hsrc,hzero,?_⟩,?_⟩
    · intro o ho z hz hzΦ
      cases o with
      | none => exact hcoord none ho hz hzΦ
      | some i =>
        have heq:=hSet i ho
        have hyE : y∈E.get (slot i):=heq.symm ▸ ho
        have h:=hcoord (some (slot i)) hyE hz hzΦ
        change z∈continuedBoundary D C π i ↔ _
        rw [←heq]
        exact h
    · intro o ho
      exact hcard (slot o) ((hSet o ho).symm ▸ ho)

end
end Hironaka.HironakaActualIndexedBoundaryContinuation
