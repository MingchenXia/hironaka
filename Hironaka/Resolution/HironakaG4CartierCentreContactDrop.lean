import Hironaka.Resolution.HironakaSharpActualCurveStrictTraceContactDrop

set_option autoImplicit false

/-!
# Exact whole ambient trace contact loss over actual Cartier centres

Smooth carrier dimension d+1 and centre dimension d internally produce the
real carrier inverse, raw total order preservation, and exact loss of one
for the same old ambient strict hypersurface. Its nonreduced trace ideal is
retained together with the actual newly born exceptional divisor.
Blueprint: `hironaka-g4-cartier-centre-contact-drop.tex`.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CartierCentreContactDrop
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupStrictSubmanifold
  NestedFlattening PositiveDimensionalComponent
  HironakaSharpActualFirstAmbientStrictExponent HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdealOperationsAlong GermIdealOrder HadamardBridge IdealWeightPowers DivisorExponentAlong
  IdealOrderArithmetic MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings InvertibleIdealQuotient
  HironakaCoherentTransformExtension
variable {n d : ℕ} {X Y : CMfd.{u} n}

private theorem monomial_on_cartier_plane_eq_self (j : Fin n) (hj : d ≤ j.1)
    (hjN : j.1 < d+1) {w : ComplexModel n}
    (hw : w ∈ complexCoordinatePlane n (d+1)) : monomial d j w=w := by
  ext i
  rw [monomial_apply]
  split_ifs with h
  · have hi : d+1 ≤ i.1 := by
      by_contra hne
      have he : i=j := Fin.ext (by omega)
      exact h.2 he
    rw [hw i hi,zero_mul]
  · rfl

private theorem cartier_carrier_subset_closure_diff {N C : Set X}
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x d) : N ⊆ closure (N \ C) := by
  intro x hx
  by_contra hnot
  let U : Set X := (closure (N \ C))ᶜ
  have hU : IsOpen U := isClosed_closure.isOpen_compl
  have hsub : N ∩ U ⊆ C := by
    rintro y ⟨hyN,hyU⟩
    by_contra hyC
    exact hyU (subset_closure ⟨hyN,hyC⟩)
  have hxC : x ∈ C := hsub ⟨hx,hnot⟩
  have hreg : RegularAtDim (n := n) (N ∩ U) x (d+1) :=
    RegularPointDimension.regularAtDim_of_inter_eq hU hnot
      (by rw [inter_assoc,inter_self]) (hrN x hx)
  have hle := le_of_regularAtDim_subset hreg (hrC x hxC) hsub
  omega

private theorem actual_eventually_mdifferentiable_of_contMDiffAt {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f x) :
    ∀ᶠ y in 𝓝 x,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f y := by
  have h1 : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) 1 f x := hf.of_le (by simp)
  exact ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp h1).mono
    fun _ hy => hy.mdifferentiableAt (by simp)

private theorem actual_relative_vanishing_comp {N : Set X} {S : Set Y} {f : Y → X} {y : Y}
    (hf : ∀ᶠ z in 𝓝 y,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f z)
    (hmaps : ∀ᶠ z in 𝓝 y,z ∈ S → f z ∈ N)
    {q : ℕ} {g : X → ℂ} (hg : VanishesToOrderOn n N (f y) q g) :
    VanishesToOrderOn n S y q (g ∘ f) := by
  obtain ⟨a,ha,hga⟩ := hg
  refine ⟨a ∘ f,comp_mem_idealPow_pointIdeal hf q ha,?_⟩
  filter_upwards [hf.self_of_nhds.continuousAt.eventually hga,hmaps] with z hz hzS hS
  exact hz (hzS hS)

/-- Actual nested Cartier flattening and the real monomial lift give a genuine
holomorphic inverse ALONG both actual carriers, including above the centre. -/
theorem exists_actual_cartier_strict_projection_local_inverse
    {N C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x d)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ geoStrictTransform π C N) (hzC : π z ∈ C) :
    ∃ s : X → Y,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ s (π z) ∧
      s (π z)=z ∧
      (∀ᶠ x in 𝓝 (π z),x ∈ N → s x ∈ geoStrictTransform π C N ∧ π (s x)=x) ∧
      ∀ᶠ y in 𝓝 z,y ∈ geoStrictTransform π C N → s (π y)=y := by
  have hzN : π z ∈ N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
  obtain ⟨Φ,hΦt,hΦ0,hflat⟩ := exists_nested_flattening (show d≤d+1 by omega) (hrC _ hzC) (hrN _ hzN) hCN
  have hflatC : ∀ {x : X},x ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x ∈ Φ.source →
      (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x) ∈ complexCoordinatePlane n d) :=
    fun hx hΦ => (hflat hx hΦ).1
  have hflatN : ∀ {x : X},x ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x ∈ Φ.source →
      (x ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x) ∈ complexCoordinatePlane n (d+1)) :=
    fun hx hΦ => (hflat hx hΦ).2
  obtain ⟨j,hjC,O,hO,hzO,W,hWs,hWmem,hℓW,hiff⟩ :=
    exists_local_geoStrictTransform hπ hΦt hflatC hflatN (mem_flatDomain_self Φ)
  obtain ⟨hjN,_hWz⟩ := (hiff z hzO).mp hz
  obtain ⟨ℓ,⟨hℓs,hℓπ⟩,_hℓunique⟩ := existsUnique_monomialLift hπ hΦt hflatC hjC
  let F : X → ComplexModel n := fun x => Φ.toFun (chartAt (ComplexModel n) (π z) x)
  have hWF : ∀ y ∈ O,y ∈ geoStrictTransform π C N → W y=F (π y) := by
    intro y hy hyN
    have hwP := (hiff y hy).mp hyN |>.2
    let p := LiftedOpen.mk (monomialDomain Φ d j) (W y) (hWmem y hy)
    have hπy : π y=monomialChart Φ d j p := by
      rw [←hℓW ℓ hℓs hℓπ y hy (hWmem y hy)]
      exact congrFun hℓπ p
    ext i
    change W y i=flatCoord Φ i (π y)
    rw [hπy,flatCoord_monomialChart hΦt p i]
    exact congrArg (fun v : ComplexModel n => v i) (monomial_on_cartier_plane_eq_self j hjC hjN hwP).symm
  have hF0 : F (π z)=0 := hΦ0
  have hW0 : W z=0 := (hWF z hzO hz).trans hF0
  let D := monomialDomain Φ d j
  have h0D : (0 : ComplexModel n) ∈ D := by simpa only [hW0] using hWmem z hzO
  let p0 : LiftedOpen.{u} D := LiftedOpen.mk D 0 h0D
  let G : ComplexModel n → LiftedOpen.{u} D := fun w => if h : w ∈ D then LiftedOpen.mk D w h else p0
  have hG0 : G 0=p0 := by simp only [G,dif_pos h0D]; rfl
  have hG : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ G 0 := by
    apply LiftedOpen.contMDiffAt_of_toModel
    have heq : (LiftedOpen.toModel D ∘ G)=ᶠ[𝓝 0] id := by
      filter_upwards [D.isOpen.mem_nhds h0D] with w hw
      change LiftedOpen.toModel D (G w)=w
      dsimp only [G]
      rw [dif_pos (show w ∈ D from hw)]
      rfl
    exact contMDiffAt_id.congr_of_eventuallyEq heq
  have hF : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ F (π z) :=
    (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source Φ.center_mem_source).contMDiffAt.comp _
      ((contMDiffOn_chart (n := ∞)).contMDiffAt ((chartAt (ComplexModel n) (π z)).open_source.mem_nhds (mem_chart_source _ _)))
  let s : X → Y := ℓ ∘ G ∘ F
  have hs : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ s (π z) := by
    have hGF := hG
    rw [←hF0] at hGF
    have hcGF : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (G ∘ F) (π z) := hGF.comp _ hF
    exact (hℓs (G (F (π z)))).comp (π z) hcGF
  have hs0 : s (π z)=z := by
    change ℓ (G (F (π z)))=z
    rw [hF0,hG0]
    have h := hℓW ℓ hℓs hℓπ z hzO (hWmem z hzO)
    simpa only [hW0] using h
  have hFD : ∀ᶠ x in 𝓝 (π z),F x ∈ D := by
    have hFD0 : F (π z) ∈ D := by rw [hF0]; exact h0D
    exact hF.continuousAt.eventually (D.isOpen.mem_nhds hFD0)
  have hπs : ∀ᶠ x in 𝓝 (π z),x ∈ N → π (s x)=x := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),hFD] with x hx hxD hxN
    change π (ℓ (G (F x)))=x
    dsimp only [G]
    rw [dif_pos hxD]
    have h := congrFun hℓπ (LiftedOpen.mk D (F x) hxD)
    change π (ℓ (LiftedOpen.mk D (F x) hxD))=monomialChart Φ d j (LiftedOpen.mk D (F x) hxD) at h
    rw [h]
    change (chartAt (ComplexModel n) (π z)).symm (Φ.invFun (monomial d j (F x)))=x
    rw [monomial_on_cartier_plane_eq_self j hjC hjN ((hflatN hx.1 hx.2).mp hxN)]
    exact flatInverse_flat Φ hx
  have hDense : N ⊆ closure (N \ C) := cartier_carrier_subset_closure_diff hrN hrC
  have hScont : ∀ᶠ x in 𝓝 (π z),ContinuousAt s x :=
    (actual_eventually_mdifferentiable_of_contMDiffAt hs).mono fun _ h => h.continuousAt
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp (hScont.and hπs)
  have hsN : ∀ᶠ x in 𝓝 (π z),x ∈ N → s x ∈ geoStrictTransform π C N ∧ π (s x)=x := by
    filter_upwards [hU.mem_nhds hxU] with x hxU' hxN
    have hπx := (hUsub hxU').2 hxN
    refine ⟨?_,hπx⟩
    by_contra hnot
    have hpre : s ⁻¹' (geoStrictTransform π C N)ᶜ ∈ 𝓝 x :=
      (hUsub hxU').1.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hnot)
    obtain ⟨y,hy,hyNC⟩ := mem_closure_iff_nhds.mp (hDense hxN) _
      (inter_mem (hU.mem_nhds hxU') hpre)
    have hπy := (hUsub hy.1).2 hyNC.1
    have hyC : π (s y) ∉ C := by rw [hπy]; exact hyNC.2
    have hyN : π (s y) ∈ N := by rw [hπy]; exact hyNC.1
    exact hy.2 ((mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN.1 hyC).mpr hyN)
  refine ⟨s,hs,hs0,hsN,?_⟩
  filter_upwards [hO.mem_nhds hzO] with y hy hyN
  have hwF := hWF y hy hyN
  change ℓ (G (F (π y)))=y
  rw [←hwF]
  dsimp only [G]
  rw [dif_pos (hWmem y hy)]
  exact hℓW ℓ hℓs hℓπ y hy (hWmem y hy)


/-- ONLY actual Cartier carrier/centre/ideal geometry internally supplies the real inverse
and BOTH whole raw relative cosupport directions, including above the centre. -/
theorem actual_cartier_raw_total_cosupport_iff_above_centre
    {N C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x d)
    {I : GermIdeal n X} (hcI : I.IsCoherent)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N) (hzC : π z ∈ C) (q : ℕ) :
    z ∈ cosupport n (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I)) q ↔
      π z ∈ cosupport n N I q := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let P := GermIdeal.pullback (m := n) π I
  have hcP : P.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcI
  have hNorm : cosupport n N' (restrictOn n N' P) q=cosupport n N' P q :=
    Subset.antisymm (cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hcP) q)
      (cosupport_subset_of_restrictLe restrictLe_restrictOn q)
  change z ∈ cosupport n N' (restrictOn n N' P) q ↔ _
  rw [hNorm]
  obtain ⟨s,hs,hs0,hsN,_hsπ⟩ := exists_actual_cartier_strict_projection_local_inverse hN hrN hrC hπ hCN hz hzC
  have hπd : ∀ᶠ y in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) π y :=
    Eventually.of_forall fun _ => hπ.contMDiff.mdifferentiableAt (by simp)
  have hπN : ∀ᶠ y in 𝓝 z,y ∈ N' → π y ∈ N := Eventually.of_forall fun _ hy =>
    BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy
  constructor
  · intro hq
    refine ⟨hπN.self_of_nhds hz,fun a ha => ?_⟩
    have hah := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcI ha
    have haP : P.mem z (a ∘ π) := GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨a,ha,rfl⟩ (holomorphicAt_comp_map hπd hah))
    have hav : VanishesToOrderOn n N' (s (π z)) q (a ∘ π) := by rw [hs0]; exact hq.2 _ haP
    have hv := actual_relative_vanishing_comp (actual_eventually_mdifferentiable_of_contMDiffAt hs)
      (hsN.mono fun _ hy hN => (hy hN).1) hav
    exact CodimOneCentreAlong.VanishesToOrderOn.congr_on hv (hsN.mono fun x hx hxN => congrArg a (hx hxN).2)
  · intro hq
    refine ⟨hz,fun g hg => ?_⟩
    apply IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact actual_relative_vanishing_comp hπd hπN (hq.2 a ha)

/-- Real zero-mark geometry supplies all finite-order premises before the BOTH
cosupport directions identify EXISTING ordinary trace orders above the centre. -/
theorem actual_cartier_raw_total_order_eq_above_centre
    {N C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x d)
    {I : GermIdeal n X} (hcI : I.IsCoherent) (hnzI : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N) (hzC : π z ∈ C) :
    ordinaryTraceOrder (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I)) z=
      ordinaryTraceOrder N I (π z) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π I)
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hcP : P.IsCoherent := isCoherent_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcI)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  have hTotal : (M.geoTransform C π).ideal=P := geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hTotal]
    exact isNonzeroAlongAt_geoTransform_without_admissibility M hN hcI hπ hCN hnzI
  have hxN := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
  have hq := actual_cartier_raw_total_cosupport_iff_above_centre hN hrN hrC hcI hπ hCN hz hzC
  apply Nat.le_antisymm
  · apply (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hxN _).mp
    exact (hq _).mp ((ordinaryTraceOrder_cosupport_iff hN' hcP hnzP hz _).mpr le_rfl)
  · apply (ordinaryTraceOrder_cosupport_iff hN' hcP hnzP hz _).mp
    exact (hq _).mpr ((ordinaryTraceOrder_cosupport_iff hN hcI hnzI hxN _).mpr le_rfl)

/-- Genuine first-step strict ambient trace loses exactly one unit of carrier
contact, including above the centre, from actual raw order preservation. -/
theorem actual_cartier_ambient_strict_trace_order_drop (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x d)
    (hH : IsSNCDivisor n [H]) (hdense : N ⊆ closure (N \ H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hCH : C ⊆ H)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N ∩ π ⁻¹' C) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    ordinaryTraceOrder N' I' z+1=ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) ∧
      ordinaryTraceOrder N' I' z<ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) := by
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hRaw := actual_cartier_raw_total_order_eq_above_centre hN hrN hrC hcH hnzH hπ hCN hz.1 hz.2
  have hNew := (actual_first_raw_total_strict_trace_exponent_shift hn hN hH hdense hπ hCN hCH z hz).1
  have hTotal : (memberTotalMarked N H C π).ideal=
      restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) :=
    geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],vanishingIdeal (n := n) H,0⟩ : MarkedIdeal n X) rfl C π
  rw [hTotal,hRaw] at hNew
  dsimp only
  omega

end
end Hironaka.HironakaG4CartierCentreContactDrop
