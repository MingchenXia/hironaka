import Hironaka.Resolution.HironakaAuxiliaryGraphGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback

/-! Genuine BM08 projection test: native dimension n+1, whole original
pullback and one last horizontal divisor. No padding/zero-section carrier,
invariant comparison, canonical-history or strict-HS-cut assertion. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProjectionTestRecord
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings NormalCrossingsInvariance ProductComplexManifold
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaSmoothSubmersionRelativeGeometry HironakaAuxiliaryGraphGeometry
  HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci BlowupTowers
open scoped ProductComplexManifold

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual native product with the complex line. -/
abbrev projectionAmbient (X : CMfd.{u} n) : CMfd.{u} (n+1) :=
  CMfd.of (n := n+1) (X × ComplexModel 1)

/-- The genuinely new horizontal divisor. -/
def horizontal (X : CMfd.{u} n) : Set (projectionAmbient X) :=
  {p | p.2=0}

private def boundary (E : List (Set X)) : List (Set (projectionAmbient X)) :=
  E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]

/-- Ordinary original ideal pullback; the last horizontal slot is essential. -/
def projectionTest (M : MarkedIdeal n X) : MarkedIdeal (n+1) (projectionAmbient X) :=
  ⟨Prod.fst ⁻¹' M.N,boundary M.E,GermIdeal.pullback (m := n+1) Prod.fst M.ideal,M.d⟩

private def liftAxes (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.castAddEmb 1)

private theorem last_not_lift (S : Finset (Fin n)) : Fin.last n ∉ liftAxes S := by
  intro h
  obtain ⟨i,_hi,he⟩:=Finset.mem_map.mp h
  have hv:=congrArg Fin.val he
  change i.val=n at hv
  exact (Nat.ne_of_lt i.isLt) hv

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

private theorem boundary_index_value (E : List (Set X)) (i : Fin (boundary E).length) :
    (boundaryIndex E i).elim Fin.val (fun _ => E.length)=i.val := by
  unfold boundaryIndex
  split
  · rfl
  · have := i.isLt
    simp only [boundary,List.length_append,List.length_map,List.length_singleton] at this
    dsimp
    omega

private theorem boundary_index_injective (E : List (Set X)) : Function.Injective (boundaryIndex E) := by
  intro i j hij
  apply Fin.ext
  rw [←boundary_index_value E i,←boundary_index_value E j,hij]

private theorem boundary_snc (E : List (Set X)) (hE : IsSNCDivisor n E) :
    IsSNCDivisor (n+1) (boundary E) := by
  classical
  refine ⟨?_,?_⟩
  · intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨K,hK,rfl⟩:=List.mem_map.mp hH
      exact (hE.1 K hK).preimage continuous_fst
    · rw [List.mem_singleton.mp hH]
      exact isClosed_singleton.preimage continuous_snd
  · intro p
    obtain ⟨S,hFamily,hCard,hInj⟩:=hE.2 p.1
    let F := Sum.elim (fun j => liftAxes (S j)) (fun _ : Unit => {Fin.last n})
    have hLift:=lift_family (fun j => E.get j) S p hFamily
    refine ⟨F ∘ boundaryIndex E,
      NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hLift (boundaryIndex E) (boundary_get E) (fun _ => rfl),?_,?_⟩
    · intro i hi
      rw [boundary_get] at hi
      cases hidx : boundaryIndex E i with
      | inl j =>
        have hj : p.1∈E.get j:=by simpa only [hidx,Sum.elim_inl,mem_preimage] using hi
        simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,liftAxes,Finset.card_map] using hCard j hj
      | inr u => simp only [Function.comp_apply,F,hidx,Sum.elim_inr,Finset.card_singleton]
    · intro i hi j hj heq
      apply boundary_index_injective E
      change p∈(boundary E).get i at hi
      change p∈(boundary E).get j at hj
      rw [boundary_get] at hi hj
      cases hiidx : boundaryIndex E i with
      | inl a =>
        cases hjidx : boundaryIndex E j with
        | inl b =>
          have ha : p.1∈E.get a:=by simpa only [hiidx,Sum.elim_inl,mem_preimage] using hi
          have hb : p.1∈E.get b:=by simpa only [hjidx,Sum.elim_inl,mem_preimage] using hj
          have hh : liftAxes (S a)=liftAxes (S b):=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl] using heq
          have hS : S a=S b:=Finset.map_injective (Fin.castAddEmb 1) hh
          exact congrArg Sum.inl (hInj ha hb hS)
        | inr v =>
          have hh : liftAxes (S a)={Fin.last n}:=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl,Sum.elim_inr] using heq
          exact False.elim (last_not_lift (S a) (hh.symm ▸ Finset.mem_singleton_self _))
      | inr v =>
        cases hjidx : boundaryIndex E j with
        | inl b =>
          have hh : {Fin.last n}=liftAxes (S b):=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl,Sum.elim_inr] using heq
          exact False.elim (last_not_lift (S b) (hh ▸ Finset.mem_singleton_self _))
        | inr w => cases v; cases w; rfl

private theorem boundary_transverse {N : Set X} {E : List (Set X)} (hT : IsTransverse n N E) :
    IsTransverse (n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' N) (boundary E) := by
  classical
  intro p hp
  obtain ⟨S₀,S,hFamily,hCard⟩:=hT p.1 hp
  let F := Sum.elim (fun j => liftAxes (S j)) (fun _ : Unit => {Fin.last n})
  have hLift:=lift_family (fun o : Option (Fin E.length) => o.elim N (fun j => E.get j))
    (fun o => o.elim S₀ S) p hFamily
  let ix : Option (Fin (boundary E).length) → Option (Fin E.length) ⊕ Unit :=
    fun o => o.elim (Sum.inl none) (fun j => (boundaryIndex E j).map some id)
  refine ⟨liftAxes S₀,F ∘ boundaryIndex E,?_,?_⟩
  · apply NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hLift ix
    · rintro (_ | i)
      · rfl
      · cases hidx : boundaryIndex E i <;> simpa [ix,hidx] using boundary_get E i
    · rintro (_ | i)
      · rfl
      · cases hidx : boundaryIndex E i <;> simp [ix,F,hidx]
  · intro i hi
    rw [boundary_get] at hi
    cases hidx : boundaryIndex E i with
    | inl j =>
      have hj : p.1∈E.get j:=by simpa only [hidx,Sum.elim_inl,mem_preimage] using hi
      obtain ⟨hc,hd⟩:=hCard j hj
      refine ⟨?_,?_⟩
      · simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,liftAxes,Finset.card_map] using hc
      · simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,liftAxes,Finset.disjoint_map] using hd
    | inr u =>
      refine ⟨by simp [F,hidx],?_⟩
      apply Finset.disjoint_left.mpr
      intro j hj hjs
      have hjlast : j=Fin.last n:=by simpa [F,hidx] using hj
      exact last_not_lift S₀ (hjlast ▸ hjs)

/-- The entire actual projection-test domain, including its new horizontal divisor. -/
theorem projection_test_isInvDomain {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    IsInvDomain (k+1) (projectionTest M) := by
  have h:=isInvDomain_markedPullback_submersion
    (isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) M hM
  refine ⟨⟨h.isWellFormed.isClosedSubmanifold_N,h.isWellFormed.isCoherent,
    boundary_snc M.E hM.isWellFormed.isSNCDivisor,
    boundary_transverse hM.isWellFormed.isTransverse⟩,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  simpa only [Nat.add_sub_cancel_left,HironakaSmoothSubmersionCoefficientIdeals.markedPullback,projectionTest] using h.dimLE

/-- Original fields, all old labels and the genuinely new last label. -/
theorem projection_test_dictionary {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    (projectionTest M).N=Prod.fst ⁻¹' M.N ∧
    (projectionTest M).ideal=GermIdeal.pullback (m := n+1) Prod.fst M.ideal ∧
    (projectionTest M).d=M.d ∧
    (projectionTest M).E=M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] ∧
    (projectionTest M).E.length=M.E.length+1 ∧
    (projectionTest M).E.getLast (by simp [projectionTest,boundary])=horizontal X ∧
    (∀i : Fin M.E.length,(projectionTest M).E[i.val]'(by simp [projectionTest,boundary])=
      (Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i) ∧
    (projectionTest M).cosupp=(Prod.fst : projectionAmbient X → X) ⁻¹' M.cosupp := by
  refine ⟨rfl,rfl,rfl,rfl,by simp [projectionTest,boundary],?_,?_,?_⟩
  · exact List.getLast_append_singleton _
  · intro i
    change (M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X])[i.val]=_
    rw [List.getElem_append_left (by simpa only [List.length_map] using i.isLt),List.getElem_map]
    rfl
  · exact HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq
      (isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hM.isWellFormed.isCoherent M.N M.d

/-- The independently defined actual germ map, ALL original representatives
and scalar actions, and the ENTIRE original ideal image. -/
theorem projection_germ_dictionary {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (p : projectionAmbient X) :
    let τ:=actualHolomorphicGermPullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) p
    Ideal.map τ.toRingHom (wholeChartStalkIdeal M.ideal p.1 p.1 (mem_chart_source _ p.1))=
      wholeChartStalkIdeal (projectionTest M).ideal p p (mem_chart_source _ p) ∧
    (∀(g : X → ℂ)(hg : HolomorphicAt n g p.1),
      τ (chartTranslatedGerm p.1 p.1 (mem_chart_source _ p.1) g hg)=
        chartTranslatedGerm p p (mem_chart_source _ p) (g ∘ Prod.fst)
          (hg.comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)).contMDiffAt))) ∧
    ∀(c : ℂ)(a : HolGerm (ComplexModel n)),τ (c • a)=c • τ a := by
  refine ⟨map_wholeChartStalkIdeal_actual_pullback
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) M.ideal hM.isWellFormed.isCoherent p,?_,?_⟩
  · intro g hg
    exact actualHolomorphicGermPullback_original_function
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) p g hg
  · intro c a
    exact (actualHolomorphicGermPullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) p).toLinearMap.map_smul c a

end
end Hironaka.HironakaActualProjectionTestRecord
