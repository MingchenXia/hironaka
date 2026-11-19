import Hironaka.Resolution.HironakaActualNativeSectionRegularity
import Hironaka.Resolution.HironakaActualSplitImmersionDerivativeIdeals
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! The SAME actual native inclusion preserves original whole derivative
ideals on every supported carrier. Projection-stable actual windows and
true split maps supply the comparison internally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionDifferentialIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  SubmanifoldChartedSpace DerivativeIdealAlong DerivativeIdealAlongEtale
  HironakaActualNativeSectionRegularity HironakaSmoothSubmersionOrderedChoiceImageTrace
  RelativePrincipalizationSpan InvertibleIdealQuotient
  HironakaActualSubmanifoldGermExtension
variable {n k : ℕ}

private theorem mem_open_pullback_comp_iff
    {r : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel r) X]
    [IsComplexManifold r X]
    {I : GermIdeal r X}
    (hI : ∀x g,I.mem x g → HolomorphicAt r g x)
    (hcl : ∀x g,IsInSpanAt (n:=r) (I.mem x) x g → I.mem x g)
    (U : Opens X) (x : U) (g : X→ℂ) :
    (GermIdeal.pullback (m:=r) (Subtype.val : U→X) I).mem x (g ∘ Subtype.val) ↔ I.mem x.val g := by
  have hext : extendOpens U (g ∘ Subtype.val)=ᶠ[𝓝 x.val] g:=by
    filter_upwards [U.isOpen.mem_nhds x.property] with q hq
    exact extendOpens_val U (g ∘ Subtype.val) ⟨q,hq⟩
  have hh : (GermIdeal.pullback (m:=r) (Subtype.val : U→X) I).mem x (g ∘ Subtype.val) ↔
      IsInSpanAt (n:=r) (I.mem x.val) x.val (extendOpens U (g ∘ Subtype.val)):=
    isInSpanAt_comp_val_iff U
  exact hh.trans ⟨fun h=>hcl _ _ (DerivativeIdeal.isInSpanAt_congr h hext),
    fun h=>DerivativeIdeal.isInSpanAt_congr (isInSpanAt_self h (hI _ _ h)) hext.symm⟩

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

theorem pullback_native_derivIdealAlong (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(N : Set X)(_hNW : N⊆W)(I : GermIdeal n X)
      (_hI : ∀x g,I.mem x g → HolomorphicAt n g x),
      GermIdeal.pullback (m:=k) (Subtype.val : W→X) (derivIdealAlong N I)=
        derivIdealAlong ((Subtype.val : W→X) ⁻¹' N)
          (GermIdeal.pullback (m:=k) (Subtype.val : W→X) I) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro N hNW I hI
  apply GermIdeal.ext
  funext p a
  apply propext
  obtain ⟨U,hpU,R,hR,hFix,hRU⟩:=exists_actual_native_retraction_window hk hW p
  let V : Opens W:=⟨(Subtype.val : W→X) ⁻¹' U,U.isOpen.preimage continuous_subtype_val⟩
  let f : V→U:=fun q=>⟨q.val.val,q.property⟩
  let g : U→V:=fun y=>⟨R y,hRU y⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ f:=
    (ContMDiff.subtypeVal_comp_iff U f).mp ((contMDiff_val hk hW).comp contMDiff_subtype_val)
  have hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ g:=
    (ContMDiff.subtypeVal_comp_iff V g).mp hR
  have hLeft : ∀q,g (f q)=q:=by
    intro q
    exact Subtype.ext (hFix q.val q.property)
  let NU : Set U:=(Subtype.val : U→X) ⁻¹' N
  have hNU : ∀q∈NU,f (g q)=q:=by
    intro q hq
    have he : R q=(⟨q.val,hNW hq⟩ : W):=hFix (⟨q.val,hNW hq⟩ : W) q.property
    exact Subtype.ext (congrArg (fun r : W=>r.val) he)
  let IU:=GermIdeal.pullback (m:=n) (Subtype.val : U→X) I
  let IW:=GermIdeal.pullback (m:=k) (Subtype.val : W→X) I
  have hIU : ∀x a,IU.mem x a → HolomorphicAt n a x:=fun _ _ ha=>(GermIdeal.mem_pullback_iff.mp ha).holomorphicAt
  have hIW : ∀x a,IW.mem x a → HolomorphicAt k a x:=fun _ _ ha=>(GermIdeal.mem_pullback_iff.mp ha).holomorphicAt
  have hval:=contMDiff_val hk hW
  have hComp (J : GermIdeal n X) (hJ : ∀x a,J.mem x a → HolomorphicAt n a x) :
      GermIdeal.pullback (m:=k) (Subtype.val : V→W) (GermIdeal.pullback (m:=k) (Subtype.val : W→X) J)=
        GermIdeal.pullback (m:=k) f (GermIdeal.pullback (m:=n) (Subtype.val : U→X) J) := by
    rw [←whole_pullback_comp hval contMDiff_subtype_val J hJ,
      ←whole_pullback_comp contMDiff_subtype_val hf J hJ]
    rfl
  have hDU : GermIdeal.pullback (m:=n) (Subtype.val : U→X) (derivIdealAlong N I)=
      derivIdealAlong NU IU:=by
    simpa only [iterDerivIdealAlong] using
      (pullback_val_iterDerivIdealAlong (N:=N) (𝔞:=I) U hI 1)
  have hDW : GermIdeal.pullback (m:=k) (Subtype.val : V→W)
      (derivIdealAlong ((Subtype.val : W→X) ⁻¹' N) IW)=
      derivIdealAlong ((Subtype.val : V→W) ⁻¹' ((Subtype.val : W→X) ⁻¹' N))
        (GermIdeal.pullback (m:=k) (Subtype.val : V→W) IW):=by
    simpa only [iterDerivIdealAlong] using
      (pullback_val_iterDerivIdealAlong (N:=(Subtype.val : W→X) ⁻¹' N) (𝔞:=IW) V hIW 1)
  have hSplit:=HironakaActualSplitImmersionDerivativeIdeals.pullback_derivIdealAlong
    hf hg hLeft NU hNU IU hIU
  have hLocal : GermIdeal.pullback (m:=k) (Subtype.val : V→W)
      (GermIdeal.pullback (m:=k) (Subtype.val : W→X) (derivIdealAlong N I))=
      GermIdeal.pullback (m:=k) (Subtype.val : V→W)
        (derivIdealAlong ((Subtype.val : W→X) ⁻¹' N) IW) := by
    rw [hComp (derivIdealAlong N I) (fun _ _ ha=>ha.1),hDU,hSplit,hDW]
    rw [hComp I hI]
    rfl
  let q : V:=⟨p,hpU⟩
  have hLocMem:=Iff.of_eq (congrArg (fun K : GermIdeal k V=>K.mem q (a ∘ Subtype.val)) hLocal)
  have hL:=mem_open_pullback_comp_iff
    (I:=GermIdeal.pullback (m:=k) (Subtype.val : W→X) (derivIdealAlong N I))
    (fun _ _ ha=>(GermIdeal.mem_pullback_iff.mp ha).holomorphicAt)
    (fun _ _ ha=>GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans (fun _ hb=>GermIdeal.mem_pullback_iff.mp hb) ha)) V q a
  have hD:=mem_open_pullback_comp_iff
    (I:=derivIdealAlong ((Subtype.val : W→X) ⁻¹' N) IW)
    (fun _ _ ha=>ha.1) (fun _ _ ha=>IsInSpanAt.trans (fun _ hb=>hb) ha) V q a
  exact hL.symm.trans (hLocMem.trans hD)

theorem pullback_native_iterDerivIdealAlong (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(N : Set X)(_hNW : N⊆W)(I : GermIdeal n X)
      (_hI : ∀x g,I.mem x g → HolomorphicAt n g x)(q : ℕ),
      GermIdeal.pullback (m:=k) (Subtype.val : W→X) (iterDerivIdealAlong N I q)=
        iterDerivIdealAlong ((Subtype.val : W→X) ⁻¹' N)
          (GermIdeal.pullback (m:=k) (Subtype.val : W→X) I) q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro N hNW I hI q
  induction q with
  | zero=>rfl
  | succ q ih=>
    rw [iterDerivIdealAlong,pullback_native_derivIdealAlong hk hW N hNW _
      (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong hI q),ih,iterDerivIdealAlong]

end
end Hironaka.HironakaActualNativeSectionDifferentialIdeals
