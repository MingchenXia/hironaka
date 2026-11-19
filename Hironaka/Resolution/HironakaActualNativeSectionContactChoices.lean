import Hironaka.Resolution.HironakaDisjointNativeTangentDirection
import Hironaka.Resolution.HironakaOriginalIndependentSmoothContactChoices

/-! Actual native selected contact choices. The SAME original ambient
function is restricted to an explicitly produced smaller native open.
The independently selected native direction is constructed from original
source geometry and order, before genuine glueing on all original tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionContactChoices
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace GermIdealOrder GermIdealPullbackCalculus
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionOrder HironakaActualNativeSectionOrderHistory
  HironakaDisjointNativeTangentDirection HomogenizedIdealAlong TangentDirectionAlong
  StepOneValue StepOneLowerDomain RelativePrincipalizationSpan
  HironakaStepOneZeroContactRemainderGlueing HironakaStepOneZeroContactRemainderExtension
  ContactStageKept MarkedIdealBiholomorphism HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  HomogenizedGlueingTower HomogenizedIdealAlongTower
  HironakaSmoothSubmersionCoefficientIdeals
variable {n k : ℕ}

variable {X : CMfd.{0} n} {W : Set X}

private theorem native_source_data (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hNW : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) :
    let K := nativePullback hk W hW M
    IsClosedSubmanifold k K.N ∧ K.ideal.IsCoherent ∧
      IsMaximalOrderAlong K.N K.ideal K.d ∧
      K.cosupp=(Subtype.val : W→X) ⁻¹' M.cosupp := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K := nativePullback hk W hW M
  have hHol : ∀x f,M.ideal.mem x f → HolomorphicAt n f x:=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf
  have hImage : (Subtype.val : W→X) '' K.N=M.N:=by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hx;exact ⟨⟨x,hNW hx⟩,hx,rfl⟩
  have hKN : IsClosedSubmanifold k K.N:=by
    refine ⟨hN.1.preimage continuous_subtype_val,?_⟩
    intro q hq
    obtain ⟨r,hr⟩:=hN.2 q.val hq
    have hReg:=regularAtDim_native_image_iff hk hW K.N q r
    rw [hImage] at hReg
    exact ⟨r,hReg.mp hr⟩
  have hKI : K.ideal.IsCoherent:=isCoherent_pullback (contMDiff_val hk hW) hI
  have hC:=cosupport_native_preimage hk hW K.N M.ideal hHol (M.d+1)
  rw [hImage] at hC
  have hKmax : IsMaximalOrderAlong K.N K.ideal K.d:=by
    intro q hq
    apply hmax q.val
    have hp : q∈(Subtype.val : W→X) ⁻¹' cosupport n M.N M.ideal (M.d+1):=by
      rw [hC]
      exact hq
    exact hp
  exact ⟨hKN,hKI,hKmax,cosupp_nativePullback hk W hW M hNW hHol⟩

/-- BOTH original selected contacts are produced from original source data.
The SAME ambient selected function is native-tangent on an explicitly
produced smaller native open; independent selected functions are not equated. -/
theorem exists_native_selected_contact_pair (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hNW : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hd : 1≤M.d) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (p : nativeManifold hk W hW) (hp : p.val∈M.cosupp) :
    let K := nativePullback hk W hW M
    let u := (tangentChoice M p.val).2 ∘ (Subtype.val : W→X)
    let v := (tangentChoice K p).2
    ∃U : Opens X,(U : Set X)=(tangentChoice M p.val).1 ∧ p.val∈U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U (tangentChoice M p.val).2 ∧
      ∃V : Opens (nativeManifold hk W hW),p∈V ∧
        (V : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (U : Set X) ∧
        IsTangentDirectionAlong K.N K.ideal K.d V u ∧
        ∃L : Opens (nativeManifold hk W hW),
          (L : Set (nativeManifold hk W hW))=(tangentChoice K p).1 ∧ p∈L ∧
          IsTangentDirectionAlong K.N K.ideal K.d L v := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K := nativePullback hk W hW M
  obtain ⟨hKN,hKI,hKmax,hKcos⟩:=native_source_data hk hW M hNW hN hI hmax
  have hpK : p∈K.cosupp:=by rw [hKcos];exact hp
  have hSourceExists:=exists_isTangentDirectionAlong hI hN hd hp
    (fun hOrd=>hmax p.val ⟨hp.1,hOrd⟩)
  obtain ⟨hpU,hu⟩:=tangentChoice_spec M hSourceExists
  have hNativeExists:=exists_isTangentDirectionAlong hKI hKN hd hpK
    (fun hOrd=>hKmax p ⟨hpK.1,hOrd⟩)
  obtain ⟨hpL,hv⟩:=tangentChoice_spec K hNativeExists
  let U : Opens X:=⟨(tangentChoice M p.val).1,hu.isOpen⟩
  let L : Opens (nativeManifold hk W hW):=⟨(tangentChoice K p).1,hv.isOpen⟩
  have hHol : ∀x f,M.ideal.mem x f → HolomorphicAt n f x:=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf
  have hu0 : (tangentChoice M p.val).2 p.val=0:=
    apply_eq_zero_of_mem_cosupport hHol hd hp (hu.mem p.val hpU)
  obtain ⟨V,hpV,hVO,hvNative⟩:=exists_native_tangent_neighbourhood hk hW
    M.N hNW hN M.ideal hHol hu p hp.1 hpU hu0
  exact ⟨U,rfl,hpU,hu,V,hpV,hVO,hvNative,L,rfl,hpL,hv⟩

/-- ONE actual native choice glueing is constructed BEFORE EVERY original
native test. The output identifies ENTIRE kept-position contact REMAINDERS
and fixes the original transformed cosupport; no raw boundary identity is claimed. -/
theorem exists_native_selected_contact_glueing (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hNW : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hd : 1≤M.d) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (p : nativeManifold hk W hW) (hp : p.val∈M.cosupp) :
    let K := nativePullback hk W hW M
    let u := (tangentChoice M p.val).2 ∘ (Subtype.val : W→X)
    let v := (tangentChoice K p).2
    ∃U : Opens X,(U : Set X)=(tangentChoice M p.val).1 ∧ p.val∈U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U (tangentChoice M p.val).2 ∧
      ∃V : Opens (nativeManifold hk W hW),p∈V ∧
        (V : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (U : Set X) ∧
        IsTangentDirectionAlong K.N K.ideal K.d V u ∧
        ∃L : Opens (nativeManifold hk W hW),
          (L : Set (nativeManifold hk W hW))=(tangentChoice K p).1 ∧ p∈L ∧
          IsTangentDirectionAlong K.N K.ideal K.d L v ∧
          ∃G : GlueingDataAlong K.N K.ideal K.d u v,
            p∈G.dom ∧ p∈G.cod ∧ (G.dom : Set (nativeManifold hk W hW))⊆V∩L ∧
              (G.cod : Set (nativeManifold hk W hW))⊆V∩L ∧
              ∀{D : CMfd.{0} k}(T : BlowupTower (nativeManifold hk W hW) D),
                IsGeoTestTower K T →
                ∃Φ,IsGlueingLiftAlong G T Φ ∧
                  MarkedIdeal.pullback Φ
                    (contactRemainderMarked (contactMarkedKept K u T (openPreimage T G.cod)) K.E.length)=
                    contactRemainderMarked (contactMarkedKept K v T (openPreimage T G.dom)) K.E.length ∧
                  ∀q : openPreimage T G.dom,
                    (q : D)∈(geoTransformAlong K T).cosupp → (Φ q : D)=q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K := nativePullback hk W hW M
  obtain ⟨hKN,hKI,_hKmax,hKcos⟩:=native_source_data hk hW M hNW hN hI hmax
  have hpK : p∈K.cosupp:=by rw [hKcos];exact hp
  obtain ⟨U,hUE,hpU,hu,V,hpV,hVO,hUv,L,hLE,hpL,hLv⟩:=
    exists_native_selected_contact_pair hk hW M hNW hN hI hd hmax p hp
  obtain ⟨G,hpd,hpc,hdom,hcod,hglue⟩:=exists_contact_remainder_glueing K hKN hKI hd p hpK
    V L hUv hpV hLv hpL
  have he:=coeff_homAlong_wEquiv K hKN hKI hd
  refine ⟨U,hUE,hpU,hu,V,hpV,hVO,hUv,L,hLE,hpL,hLv,G,hpd,hpc,hdom,hcod,?_⟩
  intro D T hT
  have hBar : IsGeoTestTower (barMarked K) T:=(he.2 T).1.mpr hT
  have hEmpty:=StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom K T hBar
  obtain ⟨Φ,hLift,⟨_hModel,hPad⟩,hFix⟩:=hglue T hEmpty
  refine ⟨Φ,hLift,?_,fun q hq=>?_⟩
  · rw [contactRemainderMarked_contactMarkedKept_emptyE,contactRemainderMarked_contactMarkedKept_emptyE]
    exact hPad K.E.length
  · apply hFix q
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked K T,(he.2 T).2 hBar]
    exact hq

end
end Hironaka.HironakaActualNativeSectionContactChoices

/-! Append-only public access to the existing native source-geometry producer. -/
namespace Hironaka.HironakaActualNativeSectionContactChoices
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory HomogenizedIdealAlong

/-- Source geometry, coherence, maximal order and the literal cosupport dictionary
for the native marked ideal. This exposes the already proved private producer. -/
theorem native_source_geometry {n k : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hNW : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) :
    let K := nativePullback hk W hW M
    IsClosedSubmanifold k K.N ∧ K.ideal.IsCoherent ∧
      IsMaximalOrderAlong K.N K.ideal K.d ∧
      K.cosupp=(Subtype.val : W→X) ⁻¹' M.cosupp :=
  native_source_data hk hW M hNW hN hI hmax

end
end Hironaka.HironakaActualNativeSectionContactChoices
