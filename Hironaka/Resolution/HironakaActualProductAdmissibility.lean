import Hironaka.Resolution.HironakaActualProjectionTestRecord

/-! Product-centre admissibility for the entire projection-test boundary.
The elementary product coordinates and finite-slot helpers below reproduce
those in HironakaActualProjectionTestRecord under fresh private declarations;
no inaccessible helper is imported and no separate engine credit is claimed.
Blueprint FIRST: `hironaka-actual-product-admissibility.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProductAdmissibility
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings NormalCrossingsInvariance ProductComplexManifold GermIdealOrder
  MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSmoothSubmersionRelativeGeometry HironakaAuxiliaryGraphGeometry
  HironakaHolomorphicJetRankLoci BlowupTowers HironakaActualProjectionTestRecord
open scoped ProductComplexManifold
variable {n : ℕ} {X : CMfd.{u} n}

private def boundary (E : List (Set X)) : List (Set (projectionAmbient X)) :=
  E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]

private def liftAxes (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.castAddEmb 1)

private theorem split_old (w : ComplexModel (n+1)) (i : Fin n) :
    ((prodModelEquiv n 1).symm w).1 i=w (i.castAdd 1) := by
  rfl

private theorem split_normal (w : ComplexModel (n+1)) (i : Fin 1) :
    ((prodModelEquiv n 1).symm w).2 i=w (i.natAdd n) := by
  rfl

private theorem product_old (a : ComplexModel n) (b : ComplexModel 1) (i : Fin n) :
    prodModelEquiv n 1 (a,b) (i.castAdd 1)=a i := by
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.1 i)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [split_old] at h
  exact h

private theorem product_last (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b) (Fin.last n)=b 0 := by
  have he : Fin.last n=(0 : Fin 1).natAdd n:=Fin.ext (by simp)
  rw [he]
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.2 0)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [split_normal] at h
  exact h

private theorem product_mask (a : ComplexModel n) (b : ComplexModel 1) (S : Finset (Fin n)) :
    prodModelEquiv n 1 (a,b)∈coordSubspace (liftAxes S) ↔ a∈coordSubspace S := by
  constructor
  · intro h i hi
    exact (product_old a b i) ▸ h (i.castAdd 1) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · intro h j hj
    obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hj
    change prodModelEquiv n 1 (a,b) (i.castAdd 1)=0
    rw [product_old]
    exact h i hi

private theorem product_normal (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b)∈coordSubspace {Fin.last n} ↔ b=0 := by
  constructor
  · intro h
    ext i
    obtain rfl : i=0:=Subsingleton.elim _ _
    simpa only [product_last,PiLp.zero_apply] using h (Fin.last n) (Finset.mem_singleton_self _)
  · intro hb j hj
    rw [Finset.mem_singleton.mp hj,product_last,hb]
    rfl

private def productCoordinates (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1)) :
    LocalHolomorphicEquivAt (n := n+1) (chartAt (ComplexModel (n+1)) p p) where
  source := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.source
  target := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  isOpen_target := Φ.isOpen_target.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  center_mem_source := by
    simpa only [mem_preimage,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply]
      using Φ.center_mem_source
  toFun w := prodModelEquiv n 1
    (Φ.toFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2-p.2)
  invFun w := prodModelEquiv n 1
    (Φ.invFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2+p.2)
  toFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.toFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.sub_const p.2).differentiableOn)
  invFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.invFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.add_const p.2).differentiableOn)
  mapsTo_toFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_toFun hw
  mapsTo_invFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_invFun hw
  left_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.left_inv _ hw,sub_add_cancel,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w
  right_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.right_inv _ hw,add_sub_cancel_right,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w

private theorem lift_family {ι : Type*} (A : ι → Set X) (S : ι → Finset (Fin n))
    (p : projectionAmbient X) (h : IsCoordinateFamilyAt n A S p.1) :
    IsCoordinateFamilyAt (n+1)
      (Sum.elim (fun i => (Prod.fst : projectionAmbient X → X) ⁻¹' A i) (fun _ : Unit => horizontal X))
      (Sum.elim (fun i => liftAxes (S i)) (fun _ : Unit => {Fin.last n})) p := by
  obtain ⟨Φ,hsrc,h0,hflat⟩:=h
  refine ⟨productCoordinates p Φ,?_,?_,?_⟩
  · intro w hw
    change w∈(prodChart (chartAt (ComplexModel n) p.1) (chartAt (ComplexModel 1) p.2)).target
    rw [prodChart_target]
    exact ⟨hsrc hw,Set.mem_univ _⟩
  · change prodModelEquiv n 1
      (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).1,
        ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).2-p.2)=0
    have hzero : Φ.toFun (chartAt (ComplexModel n) p.1 p.1)=0:=h0
    simp only [chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
      chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,hzero,sub_self]
    exact (prodModelEquiv n 1).map_zero
  · rintro (i | u) hp q hq hqΦ
    · have hpair : q∈(chartAt (ComplexModel n) p.1).source ×ˢ
          (chartAt (ComplexModel 1) p.2).source:=by
        simpa only [complexChartAt,chartAt_prod,prodChart_source] using hq
      have hbase : q.1∈(chartAt (ComplexModel n) p.1).source:=hpair.1
      have hΦ : chartAt (ComplexModel n) p.1 q.1∈Φ.source:=by
        simpa only [productCoordinates,complexChartAt,chartAt_prod,prodChart_apply,
          ContinuousLinearEquiv.symm_apply_apply,mem_preimage] using hqΦ
      change q.1∈A i ↔ _
      rw [hflat i hp hbase hΦ]
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,Sum.elim_inl]
        using (product_mask (Φ.toFun (chartAt (ComplexModel n) p.1 q.1))
          ((chartAt (ComplexModel 1) p.2) q.2-p.2) (S i)).symm
    · change q.2=0 ↔ _
      change p.2=0 at hp
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
        chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,Sum.elim_inr,hp,sub_zero]
        using (product_normal (Φ.toFun (chartAt (ComplexModel n) p.1 q.1)) q.2).symm

private def boundaryIndex (E : List (Set X)) (i : Fin (boundary E).length) : Fin E.length ⊕ Unit :=
  if hi : i.val<E.length then Sum.inl ⟨i.val,hi⟩ else Sum.inr ()

private theorem boundary_get (E : List (Set X)) (i : Fin (boundary E).length) :
    (boundary E).get i=(boundaryIndex E i).elim
      (fun j => (Prod.fst : projectionAmbient X → X) ⁻¹' E.get j) (fun _ => horizontal X) := by
  by_cases hi : i.val<E.length
  · simp only [boundaryIndex,dif_pos hi,Sum.elim_inl]
    change (E.map _ ++ [horizontal X])[i.val]=_
    rw [List.getElem_append_left (by simpa using hi),List.getElem_map]
    rfl
  · have he : i.val=E.length:=by have := i.isLt; simp only [boundary,List.length_append,List.length_map,List.length_singleton] at this; omega
    simp only [boundaryIndex,dif_neg hi,Sum.elim_inr]
    change (E.map _ ++ [horizontal X])[i.val]=_
    rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
    simp [he]

/-- One source centre/boundary coordinate family yields a genuine joint
product-centre/old-boundary/horizontal family, with every ordered slot. -/
theorem product_hasNormalCrossings {C : Set X} {E : List (Set X)}
    (hC : HasNormalCrossings n C E) :
    HasNormalCrossings (n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' C)
      (E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]) := by
  classical
  change HasNormalCrossings (n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' C) (boundary E)
  intro p hp
  obtain ⟨S₀,S,hFamily,hCard⟩ := hC p.1 hp
  let F := Sum.elim (fun j => liftAxes (S j)) (fun _ : Unit => {Fin.last n})
  have hLift := lift_family (fun o : Option (Fin E.length) => o.elim C (fun j => E.get j))
    (fun o => o.elim S₀ S) p hFamily
  let ix : Option (Fin (boundary E).length) → Option (Fin E.length) ⊕ Unit :=
    fun o => o.elim (Sum.inl none) (fun j => (boundaryIndex E j).map some id)
  refine ⟨liftAxes S₀,F ∘ boundaryIndex E,?_,?_⟩
  · apply NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hLift ix
    · rintro (_ | i)
      · rfl
      · change (boundary E).get i = _
        cases hidx : boundaryIndex E i <;> simpa [ix,hidx] using boundary_get E i
    · rintro (_ | i)
      · rfl
      · change (F ∘ boundaryIndex E) i = _
        cases hidx : boundaryIndex E i <;> simp [ix,F,hidx]
  · intro i hi
    rw [boundary_get] at hi
    cases hidx : boundaryIndex E i with
    | inl j =>
      have hj : p.1 ∈ E.get j := by simpa only [hidx,Sum.elim_inl,mem_preimage] using hi
      simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,liftAxes,Finset.card_map]
        using hCard j hj
    | inr u => simp only [Function.comp_apply,F,hidx,Sum.elim_inr,Finset.card_singleton]

/-- Source coherence and ordinary source admissibility internally produce
all target admissibility clauses, without positivity or a domain packet. -/
theorem projection_test_admissible {M : MarkedIdeal n X} {C : Set X}
    (hI : M.ideal.IsCoherent) (hC : M.IsAdmissibleCentre C) :
    (projectionTest M).IsAdmissibleCentre ((Prod.fst : projectionAmbient X → X) ⁻¹' C) := by
  have hf := isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  refine ⟨isClosedSubmanifold_preimage_submersion hf hC.1,?_,
    product_hasNormalCrossings hC.2.2⟩
  change (Prod.fst : projectionAmbient X → X) ⁻¹' C ⊆
    cosupport (n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' M.N)
      (GermIdeal.pullback (m := n+1) Prod.fst M.ideal) M.d
  rw [HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hf hI M.N M.d]
  exact preimage_mono hC.2.1

end
end Hironaka.HironakaActualProductAdmissibility
