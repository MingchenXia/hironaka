import Hironaka.Resolution.HironakaActualNativeSectionNormalCrossings
import Hironaka.Resolution.HironakaActualLocallyFiniteNonzeroIdealContinuation

/-! Actual native Lift EXISTENCE from ORIGINAL supported invariant-domain
records and ambient TESTs. Original nonzero data produce native centre
thinness internally; every native map is the literal restricted SAME π.
Native canonicality requires a subsequent invariant/centre proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeHistoryExistence
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder GermIdealPullbackCalculus RelativePrincipalizationSpan InvertibleIdealQuotient DivisorExponentAlong
  SubmanifoldChartedSpace NormalCrossings HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionNormalCrossings HironakaActualRawRecordPullbacks
  HironakaActualLocallyFiniteNonzeroIdealContinuation InvDomainTowerAlong ResolutionInvariantSpec

/-- Original nonzero-along on the actual supported carrier gives nonzero-along
on its literal native carrier; no native nonzero certificate is supplied. -/
theorem nonzero_native_pullback {n k : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x)
    (hnz : ∀x∈M.N,IsNonzeroAlongAt M.N M.ideal x) :
    ∀q∈(nativePullback hk W hW M).N,
      IsNonzeroAlongAt (nativePullback hk W hW M).N (nativePullback hk W hW M).ideal q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro q hq
  obtain ⟨g,hg,hfreq⟩:=hnz q.val hq
  have hComp : HolomorphicAt k (g ∘ (Subtype.val : W→X)) q:=
    (hhol q.val g hg).comp_contMDiff (Eventually.of_forall fun _=>(contMDiff_val hk hW).contMDiffAt)
  refine ⟨g ∘ (Subtype.val : W→X),?_,?_⟩
  · exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩ hComp)
  · have hNativeFreq : ∃ᶠy : W in 𝓝 (⟨q.val,q.property⟩ : W),y.val∈M.N ∧ g y.val≠0:=by
      rw [nhds_subtype_eq_comap,Filter.frequently_comap]
      exact hfreq.mono fun y hy=>⟨⟨y,hMN hy.1⟩,rfl,hy⟩
    exact hNativeFreq

/-- The ORIGINAL invariant-domain data and ambient TEST construct the actual
native history, every thin native centre, the SAME restricted π and native TEST.
No geometry Lift, native TEST, canonicality or comparison is a premise. -/
theorem exists_native_history_of_original_test {n k r : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower M T →
      ∃(V : Set Y)(hVc : IsClosed V)(hV : ∀y∈V,RegularAtDim (n:=n) V y k)
        (Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)),
        Lift hk W hWc hW M.E T V hVc hV Q ∧ IsGeoTestTower (nativePullback hk W hW M) Q := by
  have hN:=hM.isWellFormed.isClosedSubmanifold_N
  have hI:=hM.isWellFormed.isCoherent
  have hE:=hM.isWellFormed.isSNCDivisor
  have hd:=hM.one_le_d
  have hnz:=hM.isNonzeroAlongAt
  have hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x:=
    fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  intro Y T
  induction T with
  | refl => intro _hT;exact ⟨W,hWc,hW,.refl,Lift.refl,trivial⟩
  | @step Y Z T C π hπ ih =>
    intro hFull
    obtain ⟨hT,hC⟩:=(isGeoTestTower_step_iff M T C π hπ).mp hFull
    obtain ⟨V,hVc,hV,Q,hLift,_hNativePrefix⟩:=ih hT
    let := chartedSpace hk hV
    have := isComplexManifold_chartedSpace hk hV
    let MT:=geoTransformAlong M T
    let K:=nativePullback hk V hV MT
    have hMTN : MT.N⊆V:=HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift M hMN
    have hCV : C⊆V:=fun y hy=>hMTN ((geoTransformAlong M T).cosupp_subset_N (hC.2.1 hy))
    let D : Set (nativeManifold hk V hV):=(Subtype.val : V→Y) ⁻¹' C
    have hImage : (Subtype.val : V→Y) '' D=C:=by
      ext y
      constructor
      · rintro ⟨q,hq,rfl⟩;exact hq
      · intro hy;exact ⟨⟨y,hCV hy⟩,hy,rfl⟩
    have hD : IsClosedSubmanifold k D:=by
      refine ⟨hC.1.1.preimage continuous_subtype_val,?_⟩
      intro q hq
      obtain ⟨j,hj⟩:=hC.1.2 q.val hq
      have hReg:=regularAtDim_native_image_iff hk hV D q j
      rw [hImage] at hReg
      exact ⟨j,hReg.mp hj⟩
    obtain ⟨_hMTN,hMTI⟩:=MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT
    have hMTHol : ∀y g,MT.ideal.mem y g → HolomorphicAt n g y:=
      fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hMTI hg
    have hMTNZ : ∀y∈MT.N,IsNonzeroAlongAt MT.N MT.ideal y:=
      InvDomainTowerAlong.isNonzeroAlongAt_geoTransformAlong hN hI hnz T hT
    have hKNZ : ∀q∈K.N,IsNonzeroAlongAt K.N K.ideal q:=
      nonzero_native_pullback hk hV MT hMTN hMTHol hMTNZ
    have hKI : K.ideal.IsCoherent:=isCoherent_pullback (contMDiff_val hk hV) hMTI
    have hKd : 1≤K.d:=by
      change 1≤(geoTransformAlong M T).d
      rw [d_geoTransformAlong]
      exact hd
    have hThin : interior K.cosupp=∅:=
      interior_cosupport_eq_empty_of_nonzero K.N K.ideal hKI hKNZ hKd
    have hKCos : K.cosupp=(Subtype.val : V→Y) ⁻¹' MT.cosupp:=
      cosupp_nativePullback hk V hV MT hMTN hMTHol
    have hDsub : D⊆K.cosupp:=by
      intro q hq
      rw [hKCos]
      exact hC.2.1 hq
    have hDint : interior D=∅:=
      eq_empty_of_subset_empty ((interior_mono hDsub).trans hThin.subset)
    have hπ' : IsBlowupAlong n ((Subtype.val : V→Y) '' D) π:=hImage.symm ▸ hπ
    have hCurrentE : MT.E=boundary M.E T:=
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
        (𝔪:=M) (𝔫:=(⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) rfl T
    have hNC : HasNormalCrossings n ((Subtype.val : V→Y) '' D) (boundary M.E T):=by
      rw [hImage,←hCurrentE]
      exact hC.2.2
    let V':=BlowupStrictSubmanifold.geoStrictTransform π ((Subtype.val : V→Y) '' D) V
    let hV':=strictRegular hVc hV D π hπ'
    let Q':=BlowupTower.step Q D (nativeProjection hk hVc hV D π hπ')
      (nativeProjection_genuine hk hVc hV D hD hDint π hπ')
    have hStep:=Lift.step hLift D hD hDint π hπ' hNC
    have hPair : (⟨(Subtype.val : V→Y) '' D,hπ'⟩ : {B : Set Y // IsBlowupAlong n B π})=⟨C,hπ⟩:=
      Subtype.ext hImage
    have hTowerEq : BlowupTower.step T ((Subtype.val : V→Y) '' D) π hπ'=
        BlowupTower.step T C π hπ:=
      congrArg (fun B : {B : Set Y // IsBlowupAlong n B π}=>BlowupTower.step T B.val π B.property) hPair
    rw [hTowerEq] at hStep
    refine ⟨V',isClosed_closure,hV',Q',hStep,?_⟩
    exact HironakaActualNativeSectionNormalCrossings.Lift.native_test hStep hn hE hTrans M rfl hMN hhol hFull

end
end Hironaka.HironakaActualNativeHistoryExistence
