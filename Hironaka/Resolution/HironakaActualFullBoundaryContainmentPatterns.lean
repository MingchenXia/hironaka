import Hironaka.Analytic.SubmanifoldChartedSpace
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Invariant.MonomialPart
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.Blowup.BlowupTowers
import Hironaka.Blowup.NormalCrossingsComparison

/-! Intrinsic finite full-boundary containment patterns of the WHOLE actual
closed smooth fixed-dimensional target. Partition, same target germs, exact original ordered
remaining sublists and simultaneous density are constructed from geometry.
No partition, density or comparison certificate is supplied.

Blueprint: `hironaka-actual-full-boundary-containment-patterns-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualFullBoundaryContainmentPatterns
noncomputable section
open Hironaka.BlowupSequences NormalCrossings NormalCrossingsComparison BlowupTowers
variable {n r : ℕ} {X : CMfd.{u} n}

/-- The intrinsic relatively open part of W contained in the given member. -/
def containingInterior (W H : Set X) : Set W:=
  interior ((Subtype.val : W→X) ⁻¹' H)

/-- A literal truth pattern of all original ordered boundary positions. -/
def patternLocus (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length)) : Set W:=
  {p | ∀i : Fin E.length,p∈containingInterior W (E.get i) ↔ i∈P}

/-- The whole ambient piece with the given intrinsic containment pattern. -/
def patternPiece (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length)) : Set X:=
  (Subtype.val : W→X) '' patternLocus W E P

/-- Exactly the false original positions, retaining their original order. -/
def remainingBoundary (E : List (Set X)) (P : Finset (Fin E.length)) : List (Set X):=by
  classical
  exact ((List.finRange E.length).filter (fun i=>i∉P)).map E.get

theorem patternPiece_subset (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length)) :
    patternPiece W E P⊆W := by
  rintro x ⟨p,_hp,rfl⟩
  exact p.property

/-- All patterns together cover the WHOLE original target, with no finiteness
assumption on its connected-component family. -/
theorem iUnion_patternPiece (W : Set X) (E : List (Set X)) :
    (⋃P : Finset (Fin E.length),patternPiece W E P)=W := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨P,hP⟩:=mem_iUnion.mp hx
    exact patternPiece_subset W E P hP
  · intro x hx
    let p : W:=⟨x,hx⟩
    let P : Finset (Fin E.length):=Finset.univ.filter fun i=>p∈containingInterior W (E.get i)
    refine mem_iUnion.mpr ⟨P,p,?_,rfl⟩
    change ∀i : Fin E.length,p∈containingInterior W (E.get i) ↔ i∈P
    intro i
    simp [P]

theorem pairwise_disjoint_patternPiece (W : Set X) (E : List (Set X)) :
    Pairwise (fun P Q : Finset (Fin E.length)=>Disjoint (patternPiece W E P) (patternPiece W E Q)) := by
  intro P Q hPQ
  apply disjoint_left.mpr
  rintro x ⟨p,hp,rfl⟩ ⟨q,hq,hqp⟩
  have hqp' : q=p:=Subtype.ext hqp
  subst q
  apply hPQ
  exact Finset.ext fun i=>(hp i).symm.trans (hq i)

/-- A true original position contains the WHOLE same piece. -/
theorem patternPiece_subset_member (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length))
    (i : Fin E.length) (hi : i∈P) : patternPiece W E P⊆E.get i := by
  rintro x ⟨p,hp,rfl⟩
  exact (interior_subset (s:=(Subtype.val : W→X) ⁻¹' E.get i)) ((hp i).mpr hi)

theorem mem_remainingBoundary (E : List (Set X)) (P : Finset (Fin E.length)) (H : Set X) :
    H∈remainingBoundary E P ↔ ∃i : Fin E.length,i∉P ∧ E.get i=H := by
  classical
  simp [remainingBoundary]

theorem remainingBoundary_sublist (E : List (Set X)) (P : Finset (Fin E.length)) :
    (remainingBoundary E P).Sublist E := by
  classical
  have h : (remainingBoundary E P).Sublist ((List.finRange E.length).map E.get):=
    List.Sublist.map E.get List.filter_sublist
  simpa only [List.map_get_finRange] using h

/-- Every omitted original member contains the whole piece, even when the
ordered original list has repeated equal entries or the piece is empty. -/
theorem patternPiece_subset_omitted (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length))
    (H : Set X) (hH : H∈E) (hNot : H∉remainingBoundary E P) : patternPiece W E P⊆H := by
  classical
  obtain ⟨i,rfl⟩:=List.mem_iff_get.mp hH
  apply patternPiece_subset_member W E P i
  by_contra hi
  exact hNot ((mem_remainingBoundary E P (E.get i)).mpr ⟨i,hi,rfl⟩)

private theorem isComplexAnalyticSubset_boundaryMember {E : List (Set X)}
    (hE : IsSNCDivisor n E) (i : Fin E.length) :
    IsComplexAnalyticSubset (n:=n) (E.get i) := by
  by_cases hn : 0<n
  · exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (MonomialPart.isClosedSubmanifold_get hn hE i)
  · have hn0 : n=0:=by omega
    have hEmpty : E.get i=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨S,_hCoord,hCard,_hInj⟩:=hE.2 x
      have hOne:=hCard i hx
      have hLe:=Finset.card_le_univ (s:=S i)
      simp only [Fintype.card_fin] at hLe
      omega
    rw [hEmpty]
    exact isComplexAnalyticSubset_empty

private theorem isClopen_containingInterior {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hr : ∀x∈W,RegularAtDim (n:=n) W x r) (i : Fin E.length) :
    IsClopen (containingInterior W (E.get i)) := by
  classical
  by_cases hne : W.Nonempty
  · obtain ⟨x,hx⟩:=hne
    have hk : r≤n:=(hr x hx).1
    let:=SubmanifoldChartedSpace.chartedSpace hk hr
    let:=SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hr
    have hAnalytic:=AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (SubmanifoldChartedSpace.contMDiff_val hk hr)
      (isComplexAnalyticSubset_boundaryMember hE i)
    exact ⟨hAnalytic.isClosed_interior,isOpen_interior⟩
  · have hEmpty : containingInterior W (E.get i)=(∅ : Set W):=by
      ext p
      exact False.elim (hne ⟨p.val,p.property⟩)
    rw [hEmpty]
    exact isClopen_empty

private theorem isClopen_patternLocus {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hr : ∀x∈W,RegularAtDim (n:=n) W x r)
    (P : Finset (Fin E.length)) : IsClopen (patternLocus W E P) := by
  classical
  have hEq : patternLocus W E P=⋂i : Fin E.length,
      if i∈P then containingInterior W (E.get i) else (containingInterior W (E.get i))ᶜ:=by
    ext p
    simp only [patternLocus,mem_ofPred_eq,mem_iInter]
    apply forall_congr'
    intro i
    by_cases hi : i∈P <;> simp [hi]
  rw [hEq]
  apply isClopen_iInter_of_finite
  intro i
  split_ifs
  · exact isClopen_containingInterior hE hr i
  · exact (isClopen_containingInterior hE hr i).compl

/-- The pattern piece and original target have the SAME actual ambient germ
at every point of the piece, not merely a common dimension bound. -/
theorem patternPiece_germ_eq {W : Set X} {E : List (Set X)}
    (_hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hr : ∀x∈W,RegularAtDim (n:=n) W x r) (P : Finset (Fin E.length))
    {x : X} (hx : x∈patternPiece W E P) :
    ∀ᶠ y in 𝓝 x,y∈patternPiece W E P ↔ y∈W := by
  obtain ⟨p,hp,rfl⟩:=hx
  have hOpen:=(isClopen_patternLocus hE hr P).isOpen
  have hInd : IsInducing (Subtype.val : W→X):=IsInducing.subtypeVal
  obtain ⟨O,hOo,hO⟩:=hInd.isOpen_iff.mp hOpen
  have hpO : p.val∈O:=by
    change p∈(Subtype.val : W→X) ⁻¹' O
    rwa [hO]
  filter_upwards [hOo.mem_nhds hpO] with y hy
  constructor
  · exact fun hyPiece=>patternPiece_subset W E P hyPiece
  · intro hyW
    refine ⟨⟨y,hyW⟩,?_,rfl⟩
    rw [←hO]
    exact hy

/-- The original actual dimension-r flattening restricts to every piece. -/
theorem regularAtDim_patternPiece {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hr : ∀x∈W,RegularAtDim (n:=n) W x r) (P : Finset (Fin E.length))
    {x : X} (hx : x∈patternPiece W E P) :
    RegularAtDim (n:=n) (patternPiece W E P) x r := by
  obtain ⟨O,hOsub,hOo,hxO⟩:=mem_nhds_iff.mp (patternPiece_germ_eq hW hE hr P hx)
  have hEq : W∩O=patternPiece W E P∩O:=by
    ext y
    constructor
    · rintro ⟨hyW,hyO⟩
      exact ⟨(hOsub hyO).mpr hyW,hyO⟩
    · rintro ⟨hyP,hyO⟩
      exact ⟨(hOsub hyO).mp hyP,hyO⟩
  exact RegularPointDimension.regularAtDim_of_inter_eq hOo hxO hEq
    (hr x (patternPiece_subset W E P hx))

theorem isClosedSubmanifold_patternPiece {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hr : ∀x∈W,RegularAtDim (n:=n) W x r) (P : Finset (Fin E.length)) :
    IsClosedSubmanifold n (patternPiece W E P) := by
  refine ⟨hW.1.isClosedMap_subtype_val _ (isClopen_patternLocus hE hr P).isClosed,?_⟩
  exact fun x hx=>⟨r,regularAtDim_patternPiece hW hE hr P hx⟩

private theorem patternLocus_dense_off_remainingBoundary {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hr : ∀x∈W,RegularAtDim (n:=n) W x r)
    (P : Finset (Fin E.length)) :
    patternLocus W E P⊆closure (patternLocus W E P\
      (Subtype.val : W→X) ⁻¹' (⋃H∈remainingBoundary E P,H)) := by
  classical
  let C:=patternLocus W E P
  let s : Finset (Fin E.length):=Finset.univ.filter fun i=>i∉P
  have hC : IsOpen C:=(isClopen_patternLocus hE hr P).isOpen
  have hThin : ∀i∈s,∀O : Set W,IsOpen O → O⊆C →
      (O∩C).Nonempty → ∃q∈O∩C,q∉(Subtype.val : W→X) ⁻¹' E.get i:=by
    intro i hi O hOo hOC hne
    by_contra hNone
    have hAll : O⊆(Subtype.val : W→X) ⁻¹' E.get i:=by
      intro q hq
      by_contra hqNot
      exact hNone ⟨q,⟨hq,hOC hq⟩,hqNot⟩
    obtain ⟨q,hqO,hqC⟩:=hne
    have hInterior : q∈containingInterior W (E.get i):=
      mem_interior.mpr ⟨O,hAll,hOo,hqO⟩
    exact (Finset.mem_filter.mp hi).2 ((hqC i).mp hInterior)
  have hOpen : ∀i∈s,IsOpen (C\(Subtype.val : W→X) ⁻¹' E.get i):=by
    intro i _hi
    exact hC.inter ((hE.1 (E.get i) (List.get_mem E i)).preimage continuous_subtype_val).isOpen_compl
  intro p hp
  apply mem_closure_iff.mpr
  intro O hOo hpO
  obtain ⟨O',_hO'o,hO'sub,⟨q,hqO',hqC⟩,hAvoid⟩:=
    ThinDimensionDrop.exists_isOpen_avoid s hThin hOpen (hOo.inter hC)
      inter_subset_right ⟨p,⟨hpO,hp⟩,hp⟩
  refine ⟨q,(hO'sub hqO').1,hqC,?_⟩
  intro hqBoundary
  change q.val∈(⋃H∈remainingBoundary E P,H) at hqBoundary
  obtain ⟨H,hH,hqH⟩:=mem_iUnion₂.mp hqBoundary
  obtain ⟨i,hi,rfl⟩:=(mem_remainingBoundary E P H).mp hH
  have his : i∈s:=Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
  exact (eq_empty_iff_forall_notMem.mp (hAvoid i his) q) ⟨hqO',hqH⟩

/-- Density off ALL false-index original members is DERIVED from analytic
interior clopenness and finite closed-trace avoidance, never supplied. -/
theorem dense_patternPiece_off_remainingBoundary {W : Set X} {E : List (Set X)}
    (_hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hr : ∀x∈W,RegularAtDim (n:=n) W x r) (P : Finset (Fin E.length)) :
    patternPiece W E P⊆closure (patternPiece W E P\⋃H∈remainingBoundary E P,H) := by
  rintro x ⟨p,hp,rfl⟩
  have hRel:=patternLocus_dense_off_remainingBoundary hE hr P hp
  have hImage : p.val∈closure ((Subtype.val : W→X) ''
      (patternLocus W E P\(Subtype.val : W→X) ⁻¹' (⋃H∈remainingBoundary E P,H))):=
    image_closure_subset_closure_image continuous_subtype_val (mem_image_of_mem _ hRel)
  apply closure_mono ?_ hImage
  rintro y ⟨q,⟨hq,hqOff⟩,rfl⟩
  exact ⟨⟨q,hq,rfl⟩,hqOff⟩

/-- Actual original fixed-dimensional smooth geometry INTERNALLY constructs this finite full
partition, including same fixed-dimension germs and density for every remaining
original boundary sublist. No partition/density/history certificate is input. -/
theorem actual_full_boundary_containment_patterns {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hr : ∀x∈W,RegularAtDim (n:=n) W x r) :
    (⋃P : Finset (Fin E.length),patternPiece W E P)=W ∧
      Pairwise (fun P Q : Finset (Fin E.length)=>
        Disjoint (patternPiece W E P) (patternPiece W E Q)) ∧
      ∀P : Finset (Fin E.length),patternPiece W E P⊆W ∧
        IsClosedSubmanifold n (patternPiece W E P) ∧
        (∀x∈patternPiece W E P,RegularAtDim (n:=n) (patternPiece W E P) x r) ∧
        (∀x∈patternPiece W E P,∀ᶠ y in 𝓝 x,y∈patternPiece W E P ↔ y∈W) ∧
        (∀i∈P,patternPiece W E P⊆E.get i) ∧
        (remainingBoundary E P).Sublist E ∧ IsSNCDivisor n (remainingBoundary E P) ∧
        (∀H∈E,H∉remainingBoundary E P → patternPiece W E P⊆H) ∧
        patternPiece W E P⊆closure (patternPiece W E P\⋃H∈remainingBoundary E P,H) := by
  refine ⟨iUnion_patternPiece W E,pairwise_disjoint_patternPiece W E,?_⟩
  intro P
  exact ⟨patternPiece_subset W E P,isClosedSubmanifold_patternPiece hW hE hr P,
    (fun _ hx=>regularAtDim_patternPiece hW hE hr P hx),
    (fun _ hx=>patternPiece_germ_eq hW hE hr P hx),
    (fun i hi=>patternPiece_subset_member W E P i hi),remainingBoundary_sublist E P,
    isSNCDivisor_of_sublist hE (remainingBoundary_sublist E P),
    (fun H hH hNot=>patternPiece_subset_omitted W E P H hH hNot),
    dense_patternPiece_off_remainingBoundary hW hE hr P⟩

end
end Hironaka.HironakaActualFullBoundaryContainmentPatterns
