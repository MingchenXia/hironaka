import Hironaka.Resolution.HironakaG1NativeStateBoundaryTransport
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! ACTUAL plain finite free products of the genuine native HS state.
Blueprint FIRST: hironaka-g1-native-finite-product-state.tex.
No horizontal boundary, native point packet or CAN/value erasure law. -/
set_option autoImplicit false
open Set Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NativeFiniteProductState
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ProductComplexManifold HironakaActualProjectionTestRecord HironakaG11PresLineState
  HironakaG11PresLineStable HironakaG1NativeStateBoundaryTransport
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionRelativeGeometry ResolutionInvariantSpec
open scoped ProductComplexManifold

variable {n k : ℕ}

/-- The ACTUAL finite free product, with its genuine summed model dimension. -/
abbrev finiteProductAmbient (X : CMfd.{0} n) (r : ℕ) : CMfd.{0} (n+r) :=
  CMfd.of (n := n+r) (X×ComplexModel r)

/-- Genuine rank-zero product, retaining the full original projection. -/
def zeroProductEquiv (X : CMfd.{0} n) :
    finiteProductAmbient X 0 ≃ₘ⟮𝓘(ℂ,ComplexModel (n+0)),𝓘(ℂ,ComplexModel n)⟯ X := by
  refine ⟨⟨Prod.fst,(fun x=>(x,0)),?_,(fun _=>rfl)⟩,
    ProductComplexManifold.contMDiff_fst,?_⟩
  · rintro ⟨x,z⟩
    exact Prod.ext rfl (Subsingleton.elim _ _)
  · exact ProductComplexManifold.contMDiff_prodMk contMDiff_id contMDiff_const

private theorem contMDiff_join {r s : ℕ} {Z : CMfd.{0} s}
    {u : Z→ComplexModel r} {v : Z→ComplexModel 1}
    (hu : ContMDiff 𝓘(ℂ,ComplexModel s) 𝓘(ℂ,ComplexModel r) ∞ u)
    (hv : ContMDiff 𝓘(ℂ,ComplexModel s) 𝓘(ℂ,ComplexModel 1) ∞ v) :
    ContMDiff 𝓘(ℂ,ComplexModel s) 𝓘(ℂ,ComplexModel (r+1)) ∞
      (fun z=>prodModelEquiv r 1 (u z,v z)) := by
  let A:=(prodModelEquiv r 1).toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel 1))
  let B:=(prodModelEquiv r 1).toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ (ComplexModel r) (ComplexModel 1))
  have h:=(A.contMDiff.comp hu).add (B.contMDiff.comp hv)
  change ContMDiff 𝓘(ℂ,ComplexModel s) 𝓘(ℂ,ComplexModel (r+1)) ∞
    (fun z=>A (u z)+B (v z)) at h
  have he : (fun z=>A (u z)+B (v z))=(fun z=>prodModelEquiv r 1 (u z,v z)) := by
    funext z
    change prodModelEquiv r 1 (u z,0)+prodModelEquiv r 1 (0,v z)=_
    rw [←map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  rwa [he] at h

/-- Actual coordinate block split/reassociation, with the SAME original fst. -/
def successorProductEquiv (X : CMfd.{0} n) (r : ℕ) :
    finiteProductAmbient X (r+1) ≃ₘ⟮𝓘(ℂ,ComplexModel (n+(r+1))),
      𝓘(ℂ,ComplexModel ((n+r)+1))⟯ projectionAmbient (finiteProductAmbient X r) := by
  let E:=prodModelEquiv r 1
  refine ⟨⟨(fun p=>((p.1,(E.symm p.2).1),(E.symm p.2).2)),
    (fun p=>(p.1.1,E (p.1.2,p.2))),?_,?_
    ⟩,?_,?_⟩
  · rintro ⟨x,z⟩
    exact Prod.ext rfl (E.apply_symm_apply z)
  · rintro ⟨⟨x,u⟩,v⟩
    change ((x,(E.symm (E (u,v))).1),(E.symm (E (u,v))).2)=((x,u),v)
    rw [E.symm_apply_apply]
  · have hp:=ProductComplexManifold.contMDiff_snd
      (n := n) (m := r+1) (X := X) (Y := ComplexModel (r+1))
    have hu:=((ContinuousLinearMap.fst ℂ (ComplexModel r) (ComplexModel 1)).comp
      E.symm.toContinuousLinearMap).contMDiff.comp hp
    have hv:=((ContinuousLinearMap.snd ℂ (ComplexModel r) (ComplexModel 1)).comp
      E.symm.toContinuousLinearMap).contMDiff.comp hp
    exact ProductComplexManifold.contMDiff_prodMk
      (ProductComplexManifold.contMDiff_prodMk ProductComplexManifold.contMDiff_fst hu) hv
  · have hx:=ProductComplexManifold.contMDiff_fst
      (n := n+r) (m := 1) (X := X×ComplexModel r) (Y := ComplexModel 1)
    have hu:=ProductComplexManifold.contMDiff_snd
      (n := n) (m := r) (X := X) (Y := ComplexModel r) |>.comp hx
    exact ProductComplexManifold.contMDiff_prodMk
      (ProductComplexManifold.contMDiff_fst.comp hx)
      (contMDiff_join hu ProductComplexManifold.contMDiff_snd)

/-- The TRUE HS transform by a finite number of actual free line factors. -/
def finiteProductHS : ℕ→(ℕ→ℕ)→(ℕ→ℕ)
  | 0,H=>H
  | r+1,H=>lineHS (finiteProductHS r H)

/-- Pointwise monotonicity, without false reflection of the pointwise order. -/
theorem finiteProductHS_mono (r : ℕ) {A B : ℕ→ℕ} (h : ∀l,A l≤B l) :
    ∀l,finiteProductHS r A l≤finiteProductHS r B l := by
  induction r with
  | zero=>exact h
  | succ r ih=>exact lineHS_mono ih

/-- Genuine finite-product HS injectivity, including the rank-zero case. -/
theorem finiteProductHS_injective (r : ℕ) : Function.Injective (finiteProductHS r) := by
  induction r with
  | zero=>exact fun _ _ h=>h
  | succ r ih=>
    intro A B h
    exact ih (funext ((lineHS_eq_iff (finiteProductHS r A) (finiteProductHS r B)).mp
      (fun l=>congrFun h l)))

/-- Ordinary WHOLE first-projection pullback, with no horizontal divisor. -/
def finiteProductRecord {X : CMfd.{0} n} (r : ℕ) (Q : MarkedIdeal n X) :
    MarkedIdeal (n+r) (finiteProductAmbient X r) :=
  markedPullback (m := n+r) (Prod.fst : finiteProductAmbient X r→X) Q

/-- All four actual fields, including the full old list and entire ideal. -/
theorem finiteProductRecord_fields {X : CMfd.{0} n} (r : ℕ) (Q : MarkedIdeal n X) :
    (finiteProductRecord r Q).N=(Prod.fst : finiteProductAmbient X r→X) ⁻¹' Q.N ∧
    (finiteProductRecord r Q).E=Q.E.map ((Prod.fst : finiteProductAmbient X r→X) ⁻¹' ·) ∧
    (finiteProductRecord r Q).ideal=GermIdeal.pullback (m := n+r) Prod.fst Q.ideal ∧
    (finiteProductRecord r Q).d=Q.d := ⟨rfl,rfl,rfl,rfl⟩

/-- The true added fibre dimension is derived from the ACTUAL submersion. -/
theorem finiteProductRecord_isInvDomain {X : CMfd.{0} n} (r : ℕ) (Q : MarkedIdeal n X)
    (hQ : IsInvDomain k Q) : IsInvDomain (k+r) (finiteProductRecord r Q) := by
  have h:=isInvDomain_markedPullback_submersion
    (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := r)
      (X := X) (Y := ComplexModel r)) Q hQ
  simpa only [finiteProductRecord,Nat.add_sub_cancel_left] using h

private theorem successor_record {X : CMfd.{0} n} (r : ℕ) (Q : MarkedIdeal n X)
    (hI : Q.ideal.IsCoherent) (hE : Q.E=[]) :
    markedPullback (m := n+(r+1)) (successorProductEquiv X r)
      (plainLineRecord (finiteProductRecord r Q))=
      finiteProductRecord (r+1) Q := by
  have hLine : plainLineRecord (finiteProductRecord r Q)=
      markedPullback (m := (n+r)+1)
        (Prod.fst : projectionAmbient (finiteProductAmbient X r)→finiteProductAmbient X r)
        (finiteProductRecord r Q) := by
    have hPE : (finiteProductRecord r Q).E=[] := by
      change Q.E.map _=[]
      rw [hE,List.map_nil]
    rw [plainLineRecord_eq]
    simp only [markedPullback,hPE,List.map_nil]
  rw [hLine]
  change markedPullback (m := n+(r+1)) (successorProductEquiv X r)
    (markedPullback (m := (n+r)+1) Prod.fst
      (markedPullback (m := n+r) (Prod.fst : finiteProductAmbient X r→X) Q))=_
  have hf:=ProductComplexManifold.contMDiff_fst
    (n := n) (m := r) (X := X) (Y := ComplexModel r)
  have hg:=ProductComplexManifold.contMDiff_fst
    (n := n+r) (m := 1) (X := X×ComplexModel r) (Y := ComplexModel 1)
  rw [←whole_markedPullback_comp hf hg Q hI,
    ←whole_markedPullback_comp (hf.comp hg) (successorProductEquiv X r).contMDiff Q hI]
  rfl

/-- GENUINE finite plain product state, all point witnesses internally
transported by HELD line/biholomorphic mothers. No CAN/value erasure law. -/
theorem native_state_finiteProduct {X : CMfd.{0} n} (r : ℕ) {Q : MarkedIdeal n X}
    {W : Set X} {H : ℕ→ℕ} (hState : NativeHSState Q W H) (hE : Q.E=[]) :
    NativeHSState (finiteProductRecord r Q)
      ((Prod.fst : finiteProductAmbient X r→X) ⁻¹' W) (finiteProductHS r H) := by
  induction r with
  | zero=>exact hState.pullback (zeroProductEquiv X)
  | succ r ih=>
    have hLine:=native_state_plainLine ih
    have hPull:=hLine.pullback (successorProductEquiv X r)
    change NativeHSState
      (markedPullback (m := n+(r+1)) (successorProductEquiv X r)
        (plainLineRecord (finiteProductRecord r Q)))
      ((successorProductEquiv X r) ⁻¹' (Prod.fst ⁻¹' (Prod.fst ⁻¹' W)))
      (lineHS (finiteProductHS r H)) at hPull
    rw [successor_record r Q hState.2.2.2.1 hE] at hPull
    exact hPull

end
end Hironaka.HironakaG1NativeFiniteProductState
