import Hironaka.Resolution.HironakaActualNonregularCoefficientNaturality
import Hironaka.Invariant.CompanionRebase
import Hironaka.Resolution.HironakaActualNoncanonicalAnalyticTransformLocality
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualNonregularCompanionNaturality
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers MarkedIdealBiholomorphism
open RelativePrincipalizationSpan GermIdealPullbackCalculus MarkedIdeals MarkedIdeals.MarkedIdeal
open HadamardBridge DerivativeIdealAlongEtale MonomialPartEtale MonomialPartAlong
open RestrictedIdealExtension RestrictedIdealQuotient InvertibleIdealQuotient
open CompanionRebase CompanionReductionAlong IdealWeightPowers
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
 {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
 {φ : M' → M} {ψ : M → M'} {y : M'}

theorem mem_pullback_iff_of_span_closed {𝔠 : GermIdeal n M}
 (hhol : ∀ x g, 𝔠.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g, IsInSpanAt (n := n) (𝔠.mem x) x g → 𝔠.mem x g)
 (hψ : IsLocalInverseAt n φ ψ y) {f : M' → ℂ} :
 (GermIdeal.pullback (m := n) φ 𝔠).mem y f ↔ 𝔠.mem (φ y) (f ∘ ψ) := by
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  constructor
  · intro hf
    have hf' : IsInSpanAt (n := n) (fun s => ∃ b, 𝔠.mem (φ y) b ∧ s = b ∘ φ) (ψ (φ y)) f := by
      rw [hψy]; exact hf
    have hc := CoefficientRestrictionTower.isInSpanAt_comp_map hψ.mdiff_inv hf'
    refine hcl _ _ (IsInSpanAt.mono ?_ hc)
    rintro t ⟨s, ⟨b, hb, rfl⟩, rfl⟩
    refine hcl _ _ (DerivativeIdeal.isInSpanAt_congr (isInSpanAt_self hb (hhol _ _ hb)) ?_)
    filter_upwards [hψ.right_inv] with q hq
    simp [hq]
  · intro hf
    have h1 := comp_mem_pullback hψ.mdiff hf
      (hhol _ _ hf)
    refine DerivativeIdeal.isInSpanAt_congr (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp h1) ?_
    filter_upwards [hψ.left_inv] with p hp
    simp [hp]


omit [IsComplexManifold n M] in
private theorem colon_span_closed {I L : GermIdeal n M} {N : Set M}
 (hL : ∀ x g, L.mem x g → HolomorphicAt n g x) {x : M} {f : M → ℂ}
 (hf : IsInSpanAt (n := n) ((colonAlong n N I L).mem x) x f) :
 (colonAlong n N I L).mem x f := by
 obtain ⟨hfhol,K,s,a,hs,ha,hsum⟩ := hf
 refine ⟨hfhol,fun g hg => ?_⟩
 refine restrictOn_of_isInSpanAt (𝔞 := I) ⟨(hL _ _ hg).mul hfhol,K,
   fun i w => g w*s i w,a,fun i => (hs i).2 g hg,ha,?_⟩
 filter_upwards [hsum] with w hw
 show g w*f w = ∑ i,a i w*(g w*s i w)
 rw [hw,Finset.mul_sum]
 exact Finset.sum_congr rfl fun i _ => by ring

theorem pullback_colonAlong
 (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
 {𝔟 𝔩 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent)
 (hhol : ∀ x g, 𝔩.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g, IsInSpanAt (n := n) (𝔩.mem x) x g → 𝔩.mem x g) {W : Set M} :
 colonAlong n (φ ⁻¹' W) (GermIdeal.pullback (m := n) φ 𝔟) (GermIdeal.pullback (m := n) φ 𝔩) =
   GermIdeal.pullback (m := n) φ (colonAlong n W 𝔟 𝔩) := by
  refine GermIdeal.ext (funext fun y => funext fun f => propext ?_)
  obtain ⟨ψ, hψ⟩ := hloc y
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  rw [mem_pullback_iff_of_span_closed (𝔠 := colonAlong n W 𝔟 𝔩) (fun _ _ hg => hg.1)
    (fun _ _ hf => colon_span_closed hhol hf) hψ]
  constructor
  · rintro ⟨hf, hcol⟩
    refine ⟨holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact hf), fun g' hg' => ?_⟩
    have h1 := hcol (g' ∘ φ) (comp_mem_pullback hψ.mdiff hg'
      (hhol _ _ hg'))
    have h2 := (mem_restrictOn_pullback_iff_of_local h𝔟 hψ).mp h1
    refine restrictOn_mem_congr h2 ?_
    filter_upwards [hψ.right_inv] with q hq
    simp [hq]
  · rintro ⟨hf, hcol⟩
    have hfψφ : (f ∘ ψ) ∘ φ =ᶠ[𝓝 y] f := by
      filter_upwards [hψ.left_inv] with p hp
      simp [hp]
    refine ⟨(holomorphicAt_comp_map hψ.mdiff hf).congr hfψφ, fun g hg => ?_⟩
    have h1 := hcol (g ∘ ψ) ((mem_pullback_iff_of_span_closed hhol hcl hψ).mp hg)
    exact (mem_restrictOn_pullback_iff_of_local h𝔟 hψ).mpr h1


section Compose
variable {P Q R : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
 [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
 [TopologicalSpace R] [ChartedSpace (ComplexModel n) R] [IsComplexManifold n R]
private theorem pullback_comp_hhol {f : P → R} {g : Q → P}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
 {𝔞 : GermIdeal n R} (hhol : ∀ x v, 𝔞.mem x v → HolomorphicAt n v x) :
 GermIdeal.pullback (m := n) (f ∘ g) 𝔞 =
   GermIdeal.pullback (m := n) g (GermIdeal.pullback (m := n) f 𝔞) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      hhol _ _ hc
    have hcfhol : HolomorphicAt n (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := n) f 𝔞).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c, hc, rfl⟩ hcfhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    exact ⟨c ∘ f, hcf, rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩

private theorem marked_pullback_comp_hhol {J : MarkedIdeal n R}
 (hhol : ∀ x v, J.ideal.mem x v → HolomorphicAt n v x) {a : P → R} {b : Q → P} {d : Q → R}
 (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
 (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) (h : ∀ q,a (b q)=d q) :
 MarkedIdeal.pullback b (MarkedIdeal.pullback a J) = MarkedIdeal.pullback d J := by
 have hfun : a ∘ b = d := funext h
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
 · show b ⁻¹' (a ⁻¹' J.N)=d ⁻¹' J.N
   rw [←preimage_comp,hfun]
 · show (J.E.map (a ⁻¹' ·)).map (b ⁻¹' ·)=J.E.map (d ⁻¹' ·)
   rw [List.map_map]
   refine List.map_congr_left fun S _ => ?_
   show b ⁻¹' (a ⁻¹' S)=d ⁻¹' S
   rw [←preimage_comp,hfun]
 · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a J.ideal)=GermIdeal.pullback (m := n) d J.ideal
   rw [←pullback_comp_hhol ha hb hhol,hfun]
end Compose

section Companion
variable {X Y : CMfd.{u} n}

private theorem pullback_factor_companion {f : Y → X}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (I L : GermIdeal n X)
 (hI : ∀ x g, I.mem x g → HolomorphicAt n g x)
 (hL : ∀ x g, L.mem x g → HolomorphicAt n g x)
 (N : Set X) (E : List (Set X)) (o d : ℕ) :
 MarkedIdeal.pullback f (companionAlong N E I L o d) =
   companionAlong (f ⁻¹' N) (E.map (f ⁻¹' ·))
     (GermIdeal.pullback (m := n) f I) (GermIdeal.pullback (m := n) f L) o d := by
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_
 · simp [MarkedIdeal.pullback]
 · simp [MarkedIdeal.pullback]
 · show GermIdeal.pullback (m := n) f (companionAlong N E I L o d).ideal = _
   rw [companionAlong_ideal,companionAlong_ideal]
   split_ifs
   · rw [MarkedIdealOperationsTransform.pullback_sumIdeal hf
       (fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
       (fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg),
       HironakaActualNonregularCoefficientNaturality.pullback_idealPow hf (fun {_ _} hg => hI _ _ hg),
       HironakaActualNonregularCoefficientNaturality.pullback_idealPow hf (fun {_ _} hg => hL _ _ hg)]
   · rfl
 · show (companionAlong N E I L o d).d = _
   rw [companionAlong_d,companionAlong_d]

theorem pullback_companionOf {f : Y → X}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hloc : ∀ y : Y, ∃ ψ : X → Y, IsLocalInverseAt n f ψ y)
 (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (o : ℕ) :
 MarkedIdeal.pullback f (companionOf n M o) =
   companionOf n (MarkedIdeal.pullback f M) o := by
 have hhI : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg
 have hMonHol : ∀ x g, (monomialPartAlong n M.N M.ideal M.E).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hNNHol : ∀ x g, (nonmonomialPartAlong n M.N M.ideal M.E).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hMon := MonomialPartEtale.pullback_monomialPartAlong hloc hhI (N := M.N) (E := M.E)
 have hNN : GermIdeal.pullback (m := n) f (nonmonomialPartAlong n M.N M.ideal M.E) =
     nonmonomialPartAlong n (f ⁻¹' M.N) (GermIdeal.pullback (m := n) f M.ideal) (M.E.map (f ⁻¹' ·)) := by
   unfold nonmonomialPartAlong
   rw [←hMon]
   exact (pullback_colonAlong hloc hI hMonHol
     (fun _ _ hg => monomialPartAlong_mem_of_isInSpanAt hg)).symm
 unfold companionOf
 rw [pullback_factor_companion hf _ _ hNNHol hMonHol,hNN,hMon]
 rfl

variable {Z Z' : CMfd.{u} n} {k : ℕ}
open BlowupTowerTransforms HironakaActualNoncanonicalAnalyticTransformLocality
open HironakaSharpActualCurrentOpenLowerReferences MarkedIdealRestrictOpen InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain)

theorem exists_actual_current_companion_window
 (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
 (T : BlowupTower X Y) {C C' : Set Y} {π : Z → Y} {π' : Z' → Y}
 (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
 (hTarget : IsGeoTestTower M (.step T C' π' hπ')) (V : TopologicalSpace.Opens Y)
 (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C') :
 ∃ η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ stepWindow hπ' V,
   (∀ z : stepWindow hπ V, π' (η z).val = π z.val) ∧
   ∀ o : ℕ, 1 ≤ o →
     let A := geoTransformAlong M (.step T C π hπ)
     let B := geoTransformAlong M (.step T C' π' hπ')
     MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z) (companionOf n A o) =
       MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : stepWindow hπ' V → Z') (companionOf n B o)) ∧
     (MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z) (companionOf n A o)).ideal.IsCoherent ∧
     MarkedIdeal.pullback (referenceInclusion A (stepWindow hπ V) o)
       (GeneralValue.compAt M o (.step T C π hπ)) =
       MarkedIdeal.pullback (Subtype.val : referenceWindow A (stepWindow hπ V) o → stepWindow hπ V)
         (MarkedIdeal.pullback (Subtype.val : stepWindow hπ V → Z) (companionOf n A o)) ∧
     (MarkedIdeal.pullback (referenceInclusion A (stepWindow hπ V) o)
       (GeneralValue.compAt M o (.step T C π hπ))).ideal.IsCoherent := by
 have hN := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hM.isWellFormed.isClosedSubmanifold_N
 obtain ⟨η,⟨hsq,hrec⟩,_⟩ := exists_current_step_whole_record M hN hM.isWellFormed.isCoherent T hπ hπ' V hC
 let A := geoTransformAlong M (.step T C π hπ)
 let B := geoTransformAlong M (.step T C' π' hπ')
 let U := stepWindow hπ V
 let U' := stepWindow hπ' V
 have hA : A.ideal.IsCoherent :=
   (analytic_and_coherent_geoTransformAlong M hN hM.isWellFormed.isCoherent (.step T C π hπ)).2
 have hB : IsInvDomain k B := isInvDomain_geoTransformAlong hM _ hTarget
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal.IsCoherent :=
   GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isWellFormed.isCoherent
 refine ⟨η,hsq,?_⟩
 intro o ho
 dsimp only
 have hEq : MarkedIdeal.pullback (Subtype.val : U → Z) (companionOf n A o) =
     MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)) := by
   calc
    MarkedIdeal.pullback (Subtype.val : U → Z) (companionOf n A o) =
      companionOf n (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → Z) A) o :=
      pullback_companionOf (X := Z) (Y := CMfd.of (n := n) U) contMDiff_subtype_val
        (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) A hA o
    _ = companionOf n (M := CMfd.of (n := n) U)
      (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) o :=
      congrArg (fun Q : MarkedIdeal n U => companionOf n (M := CMfd.of (n := n) U) Q o) hrec
    _ = MarkedIdeal.pullback η (companionOf n (M := CMfd.of (n := n) U')
      (MarkedIdeal.pullback (Subtype.val : U' → Z') B) o) :=
      (pullback_companionOf (X := CMfd.of (n := n) U') (Y := CMfd.of (n := n) U) η.contMDiff
        (fun y => ⟨η.symm,⟨Eventually.of_forall (fun p => (η.contMDiff p).mdifferentiableAt (by simp)),
          Eventually.of_forall (fun p => (η.symm.contMDiff p).mdifferentiableAt (by simp)),
          Eventually.of_forall η.symm_apply_apply,Eventually.of_forall η.apply_symm_apply⟩⟩)
        _ hBW o).symm
    _ = MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)) := by
      have hv : MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o) =
          companionOf n (M := CMfd.of (n := n) U') (MarkedIdeal.pullback (Subtype.val : U' → Z') B) o :=
        pullback_companionOf (X := Z') (Y := CMfd.of (n := n) U') contMDiff_subtype_val
          (fun y => ⟨openInv U' y,isLocalInverseAt_val U' y⟩) B hB.isWellFormed.isCoherent o
      rw [hv]
 have hCoh : (MarkedIdeal.pullback (Subtype.val : U → Z) (companionOf n A o)).ideal.IsCoherent := by
   rw [hEq]
   exact GermIdealPullbackCalculus.isCoherent_pullback η.contMDiff
     (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
       (InvDomainCompanion.isInvDomain_companionAlong hn hB ho).isWellFormed.isCoherent)
 have hHC : ∀ x g, (companionOf n A o).ideal.mem x g → HolomorphicAt n g x := by
   intro x g hg
   unfold companionOf companionAlong at hg
   split_ifs at hg <;> exact hg.1
 have hAt : MarkedIdeal.pullback (Subtype.val : NonmonomialOrderTail.ordMask A o → Z) (companionOf n A o) =
     GeneralValue.compAt M o (.step T C π hπ) :=
   pullback_companionOf (X := Z) (Y := CMfd.of (n := n) (NonmonomialOrderTail.ordMask A o))
     contMDiff_subtype_val (fun y => ⟨openInv _ y,isLocalInverseAt_val _ y⟩) A hA o
 have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (referenceInclusion A U o) :=
   BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun z => z.property)
 have hFresh : MarkedIdeal.pullback (referenceInclusion A U o) (GeneralValue.compAt M o (.step T C π hπ)) =
     MarkedIdeal.pullback (Subtype.val : referenceWindow A U o → U)
       (MarkedIdeal.pullback (Subtype.val : U → Z) (companionOf n A o)) := by
   rw [←hAt]
   exact (marked_pullback_comp_hhol hHC contMDiff_subtype_val hi (fun _ => rfl)).trans
     (marked_pullback_comp_hhol hHC contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).symm
 refine ⟨hEq,hCoh,hFresh,?_⟩
 rw [hFresh]
 exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hCoh
end Companion
end
end Hironaka.HironakaActualNonregularCompanionNaturality
