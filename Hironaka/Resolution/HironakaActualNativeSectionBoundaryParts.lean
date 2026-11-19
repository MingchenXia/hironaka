import Hironaka.Resolution.HironakaActualNativeSectionOrder
import Hironaka.Invariant.MemberTraceIdealAlong
import Hironaka.Resolution.HironakaActualSectionCompanion
/-! Original divisor exponents and boundary factors on an actual regular
native section. All original labels and empty traces are retained.
Chronological recursive values and descent remain separate. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionBoundaryParts
noncomputable section
open Hironaka.HolomorphicIdealSheaves GermIdealOrder DivisorExponentAlong
  GermIdealPullbackCalculus RelativePrincipalizationSpan SubmanifoldChartedSpace
  HironakaActualSubmanifoldGermExtension HironakaActualNativeSectionColon
  HironakaActualNativeSectionOrder IdealWeightPowers InvertibleIdealQuotient
  MemberTraceIdealAlong NormalCrossings MonomialPartAlong
variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X}

theorem isDivNearAlong_native_iff (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (H : Set X) (J : GermIdeal n X)
      (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (e : ℕ) (p : W),
      IsDivNearAlong n ((Subtype.val : W→X) '' A) J H e p.val ↔
        IsDivNearAlong k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J)
          ((Subtype.val : W→X) ⁻¹' H) e p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A H J hJ e p
  constructor
  · intro h
    have hh:=continuous_subtype_val.continuousAt.eventually h
    filter_upwards [hh] with q hq hqA hqH
    have hx:=hq ⟨q,hqA,rfl⟩ hqH
    have hpre : q∈(Subtype.val : W→X) ⁻¹' cosupport n ((Subtype.val : W→X) '' A) J e:=hx
    rwa [cosupport_native_preimage hk hW A J hJ e] at hpre
  · intro h
    have hnear : {q : W | q∈A → q.val∈H → q∈cosupport k A
        (GermIdeal.pullback (m := k) (Subtype.val : W→X) J) e}∈𝓝 p:=h
    obtain ⟨V,hV,hsub⟩:=(mem_nhds_subtype W p _).mp hnear
    filter_upwards [hV] with x hx hxA hxH
    obtain ⟨q,hqA,rfl⟩:=hxA
    have hq:=hsub hx hqA hxH
    have hpre : q∈(Subtype.val : W→X) ⁻¹' cosupport n ((Subtype.val : W→X) '' A) J e:=by
      rw [cosupport_native_preimage hk hW A J hJ e]
      exact hq
    exact hpre

theorem divExpAlong_native_eq (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (H : Set X) (J : GermIdeal n X)
      (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (p : W),
      divExpAlong n ((Subtype.val : W→X) '' A) J H p.val=
        divExpAlong k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J)
          ((Subtype.val : W→X) ⁻¹' H) p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A H J hJ p
  classical
  have hP : (fun e => IsDivNearAlong n ((Subtype.val : W→X) '' A) J H e p.val)=
      fun e => IsDivNearAlong k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J)
        ((Subtype.val : W→X) ⁻¹' H) e p:=
    funext fun e => propext (isDivNearAlong_native_iff hk hW A H J hJ e p)
  unfold divExpAlong
  change (if h : ∃e,¬(fun e => IsDivNearAlong n ((Subtype.val : W→X) '' A) J H e p.val) (e+1)
    then Nat.find h else 0)=_
  rw [hP]

theorem pullback_native_boundary_power (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(E : List (Set X)) (_hE : IsSNCDivisor n E) (_hT : IsTransverse n W E)
      (i : Fin E.length) (q : ℕ),
      GermIdeal.pullback (m := k) (Subtype.val : W→X)
        (idealPow (vanishingIdeal (n := n) (E.get i)) q)=
      idealPow (vanishingIdeal (n := k) ((Subtype.val : W→X) ⁻¹' E.get i)) q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro E hE hT i q
  have hval:=contMDiff_val hk hW
  have hTrace : GermIdeal.pullback (m := k) (Subtype.val : W→X)
      (vanishingIdeal (n := n) (E.get i))=
      vanishingIdeal (n := k) ((Subtype.val : W→X) ⁻¹' E.get i) := by
    apply GermIdeal.ext
    funext p b
    apply propext
    constructor
    · intro hb
      apply DerivativeIdealAlong.vanishingIdeal_mem_of_isInSpanAt
      apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hb)
      rintro _ ⟨a,ha,rfl⟩
      refine ⟨ha.1.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt),?_⟩
      filter_upwards [continuous_subtype_val.continuousAt.eventually ha.2] with z hz hzH
      exact hz hzH
    · intro hb
      let D:=(Subtype.val : W→X) ⁻¹' E.get i
      have hImage : (Subtype.val : W→X) '' D=W∩E.get i := by
        ext x
        constructor
        · rintro ⟨z,hz,rfl⟩
          exact ⟨z.property,hz⟩
        · intro hx
          exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
      have hPic : GermIdeal.pullback (m := k) (Subtype.val : W→X)
          (vanishingIdeal (n := n) (W∩E.get i))=vanishingIdeal (n := k) D := by
        rw [←hImage]
        exact pullback_vanishing_image hk hW D
      change (vanishingIdeal (n := k) D).mem p b at hb
      rw [←hPic] at hb
      apply GermIdeal.mem_pullback_iff.mpr
      apply IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hb)
      rintro _ ⟨a,ha,rfl⟩
      have hSpan:=(isInSpanOnAt_vanishingIdeal_iff_mem hE hT p.property i ha.1).mpr ha
      obtain ⟨K,t,c,ht,hc,he⟩:=hSpan
      refine ⟨ha.1.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt),K,
        fun j => t j ∘ Subtype.val,fun j => c j ∘ Subtype.val,
        fun j => ⟨t j,ht j,rfl⟩,?_,?_⟩
      · intro j
        exact (hc j).comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)
      · filter_upwards [continuous_subtype_val.continuousAt.eventually he] with z hz
        simpa only [Function.comp_apply] using hz z.property
  rw [HironakaActualNonregularCoefficientNaturality.pullback_idealPow hval
    (I := vanishingIdeal (n := n) (E.get i)) (fun hg => hg.1),hTrace]

theorem monomialPartAlong_native_mem_iff (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (E : List (Set X)) (_hE : IsSNCDivisor n E) (_hT : IsTransverse n W E)
      (J : GermIdeal n X) (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z)
      (p : W) (g : X→ℂ) (_hg : HolomorphicAt n g p.val),
      (monomialPartAlong n ((Subtype.val : W→X) '' A) J E).mem p.val g ↔
        (monomialPartAlong k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J)
          (E.map ((Subtype.val : W→X) ⁻¹' ·))).mem p (g ∘ Subtype.val) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A E hE hT J hJ p g hg
  let E0:=E.map ((Subtype.val : W→X) ⁻¹' ·)
  let I:=GermIdeal.pullback (m := k) (Subtype.val : W→X) J
  have hA : p.val∈(Subtype.val : W→X) '' A ↔ p∈A := by
    constructor
    · rintro ⟨z,hz,he⟩
      exact (Subtype.val_injective he) ▸ hz
    · intro hp
      exact ⟨p,hp,rfl⟩
  have hd (i : Fin E.length) : divExpAlong n ((Subtype.val : W→X) '' A) J (E.get i) p.val=
      divExpAlong k A I ((Subtype.val : W→X) ⁻¹' E.get i) p:=
    divExpAlong_native_eq hk hW A (E.get i) J hJ p
  constructor
  · intro hm
    refine ⟨hg.comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_val hk hW).contMDiffAt),?_⟩
    intro j hpA hpH
    let i : Fin E.length:=⟨j.val,by simpa only [List.length_map] using j.isLt⟩
    have hj : E0.get j=(Subtype.val : W→X) ⁻¹' E.get i:=by simp [E0,i]
    have hpH0 : p∈E0.get j:=hpH
    rw [hj] at hpH0
    have hpHi : p.val∈E.get i:=hpH0
    have hs:=hm.2 i (hA.mpr hpA) hpHi
    rw [hd i] at hs
    have hh:=(restrictedSpan_native_iff hk hW A
      (idealPow (vanishingIdeal (n := n) (E.get i))
        (divExpAlong k A I ((Subtype.val : W→X) ⁻¹' E.get i) p))
      (fun _ _ h => holomorphicAt_of_mem_idealPow h) p g).mp hs
    rw [pullback_native_boundary_power hk hW E hE hT i] at hh
    change IsInSpanOnAt (n := k) A
      ((idealPow (vanishingIdeal (n := k) (E0.get j)) (divExpAlong k A I (E0.get j) p)).mem p) p (g ∘ Subtype.val)
    rw [hj]
    exact hh
  · intro hm
    refine ⟨hg,?_⟩
    intro i hpA hpH
    let j : Fin E0.length:=⟨i.val,by simpa only [E0,List.length_map] using i.isLt⟩
    have hj : E0.get j=(Subtype.val : W→X) ⁻¹' E.get i:=by simp [E0,j]
    have hpHj : p∈E0.get j:=by rw [hj];exact hpH
    have hs:=hm.2 j (hA.mp hpA) hpHj
    change IsInSpanOnAt (n := k) A
      ((idealPow (vanishingIdeal (n := k) (E0.get j)) (divExpAlong k A I (E0.get j) p)).mem p) p (g ∘ Subtype.val) at hs
    rw [hj] at hs
    rw [hd i]
    apply (restrictedSpan_native_iff hk hW A
      (idealPow (vanishingIdeal (n := n) (E.get i))
        (divExpAlong k A I ((Subtype.val : W→X) ⁻¹' E.get i) p))
      (fun _ _ h => holomorphicAt_of_mem_idealPow h) p g).mpr
    rw [pullback_native_boundary_power hk hW E hE hT i]
    exact hs

private theorem monomialPartAlong_of_span {r : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel r) M] [IsComplexManifold r M]
    {A : Set M} {I : GermIdeal r M} {E : List (Set M)} {p : M} {g : M→ℂ}
    (hg : IsInSpanAt (n := r) ((monomialPartAlong r A I E).mem p) p g) :
    (monomialPartAlong r A I E).mem p g := by
  refine ⟨hg.holomorphicAt,?_⟩
  intro i hpA hpH
  exact IsInSpanOnAt.trans (fun _ hs => hs.2 i hpA hpH) (IsInSpanAt.restrict hg)

theorem pullback_native_monomialPartAlong (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (E : List (Set X)) (_hE : IsSNCDivisor n E) (_hT : IsTransverse n W E)
      (J : GermIdeal n X) (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z),
      GermIdeal.pullback (m := k) (Subtype.val : W→X)
        (monomialPartAlong n ((Subtype.val : W→X) '' A) J E)=
      monomialPartAlong k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J)
        (E.map ((Subtype.val : W→X) ⁻¹' ·)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A E hE hT J hJ
  have hval:=contMDiff_val hk hW
  apply GermIdeal.ext
  funext p g
  apply propext
  constructor
  · intro hg
    apply monomialPartAlong_of_span
    apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact (monomialPartAlong_native_mem_iff hk hW A E hE hT J hJ p a ha.1).mp ha
  · intro hg
    obtain ⟨B,hB,hEq⟩:=exists_ambient_holomorphic_germ hk hW p g hg.1
    have hBB : HolomorphicAt k (B ∘ (Subtype.val : W→X)) p:=
      hB.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)
    have hs : (monomialPartAlong n ((Subtype.val : W→X) '' A) J E).mem p.val B:=by
      apply (monomialPartAlong_native_mem_iff hk hW A E hE hT J hJ p B hB).mpr
      exact monomialPartAlong_of_span (IsInSpanAt.congr' (isInSpanAt_self hg hg.1) hEq.symm)
    apply GermIdeal.mem_pullback_iff.mpr
    have hspan : IsInSpanAt (n := k)
        (fun c => ∃a,(monomialPartAlong n ((Subtype.val : W→X) '' A) J E).mem p.val a ∧
          c=a ∘ (Subtype.val : W→X)) p (B ∘ Subtype.val):=
      isInSpanAt_self ⟨B,hs,rfl⟩ hBB
    exact IsInSpanAt.congr' hspan hEq

theorem pullback_native_nonmonomialPartAlong (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (E : List (Set X)) (_hE : IsSNCDivisor n E) (_hT : IsTransverse n W E)
      (J : GermIdeal n X) (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z),
      GermIdeal.pullback (m := k) (Subtype.val : W→X)
        (nonmonomialPartAlong n ((Subtype.val : W→X) '' A) J E)=
      nonmonomialPartAlong k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J)
        (E.map ((Subtype.val : W→X) ⁻¹' ·)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A E hE hT J hJ
  unfold nonmonomialPartAlong
  rw [pullback_native_colonAlong hk hW A J
    (monomialPartAlong n ((Subtype.val : W→X) '' A) J E) hJ (fun _ _ hg => hg.1),
    pullback_native_monomialPartAlong hk hW A E hE hT J hJ]

open MarkedIdeals NonmonomialOrderLocal

theorem nmOrd_native_eq (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(A : Set W) (E : List (Set X)) (_hE : IsSNCDivisor n E) (_hT : IsTransverse n W E)
      (J : GermIdeal n X) (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (d : ℕ) (p : W),
      nmOrd (M := BlowupTowers.CMfd.of (n := n) X)
        (⟨(Subtype.val : W→X) '' A,E,J,d⟩ : MarkedIdeal n X) p.val=
      nmOrd (M := BlowupTowers.CMfd.of (n := k) W)
        (⟨A,E.map ((Subtype.val : W→X) ⁻¹' ·),
          GermIdeal.pullback (m := k) (Subtype.val : W→X) J,d⟩ : MarkedIdeal k W) p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A E hE hT J hJ d p
  unfold nmOrd
  apply congrArg sInf
  ext q
  apply not_congr
  change p∈(Subtype.val : W→X) ⁻¹' cosupport n ((Subtype.val : W→X) '' A)
      (nonmonomialPartAlong n ((Subtype.val : W→X) '' A) J E) (q+1) ↔ _
  rw [cosupport_native_preimage hk hW A
    (nonmonomialPartAlong n ((Subtype.val : W→X) '' A) J E) (fun _ _ hg => hg.1) (q+1),
    pullback_native_nonmonomialPartAlong hk hW A E hE hT J hJ]

end
end Hironaka.HironakaActualNativeSectionBoundaryParts
