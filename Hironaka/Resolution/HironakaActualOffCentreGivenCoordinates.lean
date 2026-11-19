import Hironaka.Resolution.HironakaActualNativeSourceChartComposition
import Hironaka.Resolution.HironakaActualNativeAdaptedPullbackSquare
import Hironaka.Blowup.BlowupIsomorphismOff

/-! Off the ACTUAL centre, the GIVEN native source coordinates pull through
the genuine local inverse, so whole member germs/ideals remain literally
the same. No chosen target chart/derivative/ideal certificate is supplied. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOffCentreGivenCoordinates
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  BlowupFlatCoordinates

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The actual native blowup internally pulls the GIVEN centred source
coordinates through its TRUE complement local inverse. No target chart or
derivative invertibility input; all native square/domain laws are outputs. -/
theorem exists_actual_off_centre_given_coordinates
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y) (hzC : π z∉C)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0) :
    ∃Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z),
      Θ.source⊆(chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧
      ∀y : Y,y∈(chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y∈Θ.source → π y∉C ∧ π y∈flatDomain Φ ∧
          Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
            Θ.toFun (chartAt (ComplexModel n) z y) := by
  let O : Set Y:=π ⁻¹' Cᶜ
  have hO : IsOpen O:=hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  have hzO : z∈O:=hzC
  have hzE : z∉exceptionalLocus n π:=
    fun h=>hzC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  let I:=𝓘(ℂ,ComplexModel n)
  have hrange : range I=univ:=by simp [I]
  let e:=chartAt (ComplexModel n) z
  let e':=chartAt (ComplexModel n) (π z)
  let F : ComplexModel n → ComplexModel n:=fun v=>e' (π (e.symm v))
  let N : Set (ComplexModel n):=e.target ∩ e.symm ⁻¹' (O ∩ π ⁻¹' e'.source)
  have hNo : IsOpen N:=e.continuousOn_symm.isOpen_inter_preimage e.open_target
    (hO.inter (hπ.contMDiff.continuous.isOpen_preimage _ e'.open_source))
  have hzN : e z∈N:=⟨e.map_source (mem_chart_source _ z),by
    rw [mem_preimage,e.left_inv (mem_chart_source _ z)]
    exact ⟨hzO,mem_chart_source _ (π z)⟩⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h:=(contMDiffOn_iff.mp (hπ.contMDiff.contMDiffOn (s:=univ))).2 z (π z)
    refine (h.differentiableOn (by simp)).mono ?_
    intro v hv
    exact ⟨⟨mem_univ _,hv.1⟩,mem_univ _,hv.2.2,mem_univ _⟩
  have hmd : MDifferentiableAt I I π z:=(hπ.contMDiff z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I π z=fderiv ℂ F (e z) := by
    rw [hmd.mfderiv,hrange,fderivWithin_univ]
    rfl
  have hinj : Function.Injective (fderiv ℂ F (e z)) := by
    have h:=hzE
    simp only [exceptionalLocus,mem_ofPred_eq,not_not] at h
    rw [hderiv] at h
    exact h.1
  obtain ⟨Ξ,hΞN,hΞF,_⟩:=exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e z)=e' (π z) := by
    simp only [F,e.left_inv (mem_chart_source _ z)]
  let Θ:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ξ Φ (hΞF ▸ hFz)
  refine ⟨Θ,fun _ h=>(hΞN h.1).1,?_,?_⟩
  · change Φ.toFun (Ξ.toFun (e z))=0
    rw [hΞF,hFz]
    exact hΦ0
  · intro y hy hyΘ
    change e y∈Ξ.source ∩ Ξ.toFun ⁻¹' Φ.source at hyΘ
    have hyN:=(hΞN hyΘ.1).2
    rw [mem_preimage,e.left_inv hy] at hyN
    have hCoords : Ξ.toFun (e y)=e' (π y) := by
      rw [hΞF]
      change e' (π (e.symm (e y)))=e' (π y)
      rw [e.left_inv hy]
    refine ⟨hyN.1,⟨hyN.2,?_⟩,?_⟩
    · change e' (π y)∈Φ.source
      rw [←hCoords]
      exact hyΘ.2
    · change Φ.toFun (e' (π y))=Φ.toFun (Ξ.toFun (e y))
      rw [hCoords]

omit [IsComplexManifold n X] in
private theorem native_identity_inverse_square (π : Y → X) (y : Y)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (hSquare : ∀z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source → π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=Θ.toFun (chartAt (ComplexModel n) y z))
    (u : ComplexModel n) (hu : u∈Θ.target) :
    π ((chartAt (ComplexModel n) y).symm (Θ.invFun u))=
      (chartAt (ComplexModel n) (π y)).symm (Φ.invFun u) := by
  obtain ⟨hz,hΘz⟩:=flatInverse_mem Θ hu hΘsrc
  obtain ⟨hDomain,hPhi⟩:=hSquare ((chartAt (ComplexModel n) y).symm (Θ.invFun u)) hz.1 hz.2
  rw [hΘz] at hPhi
  have hCoord:=congrArg Φ.invFun hPhi
  rw [Φ.left_inv _ hDomain.2] at hCoord
  exact ((chartAt (ComplexModel n) (π y)).left_inv hDomain.1).symm.trans
    (congrArg (chartAt (ComplexModel n) (π y)).symm hCoord)

/-- The SAME actual source member has literally the SAME ENTIRE adapted
germ after genuine native pullback in an actual identity square. -/
theorem actual_native_identity_square_adapted_germ
    (π : Y → X) (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (y : Y)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (hSquare : ∀z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source → π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=Θ.toFun (chartAt (ComplexModel n) y z))
    (F : X → ℂ) (hF : HolomorphicAt n F (π y)) :
    adaptedGerm y Θ hΘ0 (F∘π) (hF.comp_contMDiff (Eventually.of_forall fun _=>hπ.contMDiffAt))=
      adaptedGerm (π y) Φ hΦ0 F hF := by
  apply HolGerm.mk_eq_mk_iff.mpr
  have h0T : (0 : ComplexModel n)∈Θ.target := by
    simpa only [hΘ0] using Θ.mapsTo_toFun Θ.center_mem_source
  filter_upwards [Θ.isOpen_target.mem_nhds h0T] with u hu
  exact congrArg F (native_identity_inverse_square π y Φ Θ hΘsrc hSquare u hu)

private theorem adaptedIdeal_eq_span_of_generation
    (J : GermIdeal n X) (hJ : J.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) {s : ℕ}
    (G : Fin s → X → ℂ) (hG : ∀i,HolomorphicAt n (G i) x)
    (hgen : ∀F,J.mem x F ↔ IsInSpanAt (n:=n) (·∈range G) x F) :
    adaptedIdeal J x Φ h0=Ideal.span (range fun i=>adaptedGerm x Φ h0 (G i) (hG i)) := by
  ext g
  obtain ⟨F,hF,rfl⟩:=exists_original_adapted_representative x Φ h0 g
  rw [mem_adaptedIdeal_iff J hJ x Φ h0 F hF,hgen F]
  exact (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0 G F).trans
    (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span _
      (fun i=>(holomorphic_adapted_iff x Φ h0 (G i)).mpr (hG i))
      ((holomorphic_adapted_iff x Φ h0 F).mpr hF))

/-- The WHOLE actual coherent pullback ideal is literally the same source
adapted ideal in these SAME genuine identity-square coordinates. -/
theorem actual_native_identity_square_adapted_ideal
    (J : GermIdeal n X) (hJ : J.IsCoherent)
    (π : Y → X) (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (y : Y)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (hSquare : ∀z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source → π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=Θ.toFun (chartAt (ComplexModel n) y z)) :
    adaptedIdeal (GermIdeal.pullback (m:=n) π J) y Θ hΘ0=adaptedIdeal J (π y) Φ hΦ0 := by
  obtain ⟨U,hU,hy,s,G,hG,hgen⟩:=hJ (π y)
  have hGh (i : Fin s) : HolomorphicAt n (G i) (π y):=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hG i) hy
  have hfat : ∀ᶠz in 𝓝 y,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π z:=
    Eventually.of_forall fun _=>hπ.contMDiffAt
  have hpb:=FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
    hfat J G hGh (hgen (π y) hy)
  rw [adaptedIdeal_eq_span_of_generation _
    (GermIdealPullbackCalculus.isCoherent_pullback hπ hJ) y Θ hΘ0
    (fun i=>G i∘π) (fun i=>(hGh i).comp_contMDiff hfat) hpb,
    adaptedIdeal_eq_span_of_generation J hJ (π y) Φ hΦ0 G hGh (hgen (π y) hy)]
  apply congrArg Ideal.span
  apply congrArg range
  funext i
  exact actual_native_identity_square_adapted_germ π hπ y Φ hΦ0 Θ hΘsrc hΘ0 hSquare (G i) (hGh i)

end
end Hironaka.HironakaActualOffCentreGivenCoordinates
