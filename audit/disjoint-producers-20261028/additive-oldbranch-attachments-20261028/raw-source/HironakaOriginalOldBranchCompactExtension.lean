import TranscendentalNakamaye.Pending.HironakaCompactOpenBlowupExtension
import TranscendentalNakamaye.Pending.HironakaLocalPrincipalization
import TranscendentalNakamaye.Pending.TransformOffCentre
import TranscendentalNakamaye.Pending.HironakaBaseChange

/-!
# Ambient extension of a prescribed finite open test history

The actual entire compact cosupport makes every prescribed centre compact.
Each actual open step extends by blowup existence and universal uniqueness;
admissibility is proved for its entire ambient centre and ordered boundary.
No extension or progress operation is assumed.
Proof bodies reproduce the accepted whole-history extension at checkpoint
636442a87402a67de1f914cb4120ee28c3ed6ad7, with direct controlled-transform
cosupport inclusion and a genuine coherent identity-pullback proof replacing
unrelated phase-chain imports. Compactness and open-image helper statements
are reproduced without strengthening hypotheses. This dependency reduction
makes no new mathematical closure claim.
Blueprint: `hironaka-original-old-branch-low-dependency-geometry.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaOriginalOldBranchCompactExtension
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  BlowupTowerIsomorphism BlowupRestrictOpen HironakaCompactOpenBlowupExtension
  GermIdealPullbackCalculus HironakaBaseChange
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Properness and the actual test projection retain the entire compact current cosupport. -/
theorem current_cosupport_compact (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hK : IsCompact M.cosupp) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    IsCompact (geoTransformAlong M T).cosupp := by
  obtain ⟨hNY, hIY⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT
  have hc := GiraudAlong.isClosed_cosupport_along hIY hNY (geoTransformAlong M T).d
  exact ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hc (fun _ hy => TransformOffCentre.cosupp_geoTransformAlong_subset M hN hI T hT hy)

/-- Restriction to an open containing the entire cosupport retains compactness. -/
theorem restricted_cosupport_compact (M : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) (hK : IsCompact M.cosupp)
    (U : Opens X) (hU : M.cosupp ⊆ U) :
    IsCompact (MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp := by
  rw [cosupp_pullback_val M
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.mpr hU]
  exact hK

/-- Whole compact cosupport persists along every actual test history; neither
nonzero ideals nor an invariant-domain certificate are needed. -/
theorem current_cosupport_compact_of_wellFormed (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hK : IsCompact M.cosupp)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    IsCompact (geoTransformAlong M T).cosupp ∧
      (geoTransformAlong M T).cosupp ⊆ T.proj ⁻¹' M.cosupp := by
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hc := GiraudAlong.isClosed_cosupport_along hwT.isCoherent hwT.isClosedSubmanifold_N
    (geoTransformAlong M T).d
  have hs : (geoTransformAlong M T).cosupp ⊆ T.proj ⁻¹' M.cosupp :=
    TransformOffCentre.cosupp_geoTransformAlong_subset M hw.isClosedSubmanifold_N hw.isCoherent T hT
  exact ⟨((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hc hs,hs⟩

/-- A genuine actual upper open embedding transports an entire local open
neighbourhood to a literal ambient open with its real holomorphic inverse. -/
theorem exists_open_image_equiv {g : Z → Y} (hg : IsOpenHoloEmbedding n g)
    (V : Opens Z) :
    ∃ (W : Opens Y) (χ : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W),
      (W : Set Y)=g '' (V : Set Z) ∧ ∀ v : V,(χ v : Y)=g v := by
  have hg' := hg.contMDiff
  obtain ⟨O,Φ,hΦ⟩ := hg
  have ho : IsOpenMap g := by
    have he : g=Subtype.val ∘ Φ := funext hΦ
    rw [he]
    exact O.isOpen.isOpenMap_subtype_val.comp Φ.toHomeomorph.isOpenMap
  let W : Opens Y := ⟨g '' (V : Set Z),ho _ V.isOpen⟩
  have hWO (w : W) : (w:Y)∈O := by
    obtain ⟨z,_hz,hz⟩ := w.property
    rw [←hz,hΦ z]
    exact (Φ z).property
  let q : W → O := fun w => ⟨w.val,hWO w⟩
  have hq : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ q :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val hWO
  have hInv (w : W) : Φ.symm (q w)∈V := by
    obtain ⟨z,hz,hzw⟩ := w.property
    have he : q w=Φ z := Subtype.ext (hzw.symm.trans (hΦ z))
    rw [he,Φ.symm_apply_apply]
    exact hz
  let f : V → W := fun v => ⟨g v,⟨v,v.property,rfl⟩⟩
  let fi : W → V := fun w => ⟨Φ.symm (q w),hInv w⟩
  have hleft (v : V) : fi (f v)=v := by
    apply Subtype.ext
    change Φ.symm (q (f v))=v.val
    have he : q (f v)=Φ v.val := Subtype.ext (hΦ v.val)
    rw [he,Φ.symm_apply_apply]
  have hright (w : W) : f (fi w)=w := by
    apply Subtype.ext
    change g (Φ.symm (q w))=w.val
    rw [hΦ,Φ.apply_symm_apply]
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (hg'.comp contMDiff_subtype_val) (fun v : V => (show g v∈W from ⟨v,v.property,rfl⟩))
  let χ : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W :=
    { toEquiv := ⟨f,fi,hleft,hright⟩
      contMDiff_toFun := hf
      contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
        (Φ.symm.contMDiff.comp hq) hInv }
  exact ⟨W,χ,rfl,fun _ => rfl⟩

private theorem pullback_id_coherent {A : Type u} [TopologicalSpace A]
    [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A] (M : MarkedIdeal n A)
    (hI : M.ideal.IsCoherent) : MarkedIdeal.pullback (id : A → A) M = M :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
    (show M.E.map (fun C => (id : A → A) ⁻¹' C) = M.E by simp)
    (BlowupControlledTransform.pullback_id hI) rfl

/-- Extend the SAME prescribed finite history, with a genuine isomorphism of
its entire tower to the ambient tower restricted over the original open. -/
theorem exists_extension (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hK : IsCompact M.cosupp) (U : Opens X) (hU : M.cosupp ⊆ U)
    {Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y), IsGeoTestTower M Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e := by
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : U → X) M).N :=
    isClosedSubmanifold_preimage_val hN U
  have hIU : (MarkedIdeal.pullback (Subtype.val : U → X) M).ideal.IsCoherent :=
    isCoherent_pullback contMDiff_subtype_val hI
  have hKU := restricted_cosupport_compact M hI hK U hU
  induction T with
  | refl =>
    exact ⟨X, .refl, trivial, Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞, .refl⟩
  | @step A B T C π hπ ih =>
    obtain ⟨Y, Q, hQ, e, he⟩ := ih hT.1
    have hKC : IsCompact C :=
      (current_cosupport_compact _ hNU hIU hKU T hT.1).of_isClosed_subset
        hT.2.1.1 hT.2.2.1
    let V : Opens Y := openPreimage Q U
    let D : Set V := e.symm ⁻¹' C
    have hDimage : D = e '' C := by
      ext p
      constructor
      · intro hp
        exact ⟨e.symm p, hp, e.apply_symm_apply p⟩
      · rintro ⟨c, hc, rfl⟩
        simpa only [D, mem_preimage, e.symm_apply_apply] using hc
    have hKD : IsCompact D := hDimage ▸ hKC.image e.continuous
    have hDpre : e ⁻¹' D = C := by
      ext c
      simp only [D, mem_preimage, e.symm_apply_apply]
    have hMoved : IsBlowupAlong n D (e ∘ π) :=
      MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse e.symm.contMDiff e.contMDiff
        e.symm_apply_apply e.apply_symm_apply hπ
    obtain ⟨W, q, hq, ξ, hξ⟩ := HironakaCompactOpenBlowupExtension.exists_extension hMoved hKD
    obtain ⟨_hNY, hIY⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI Q hQ
    have hIV : (MarkedIdeal.pullback (Subtype.val : V → Y)
        (geoTransformAlong M Q)).ideal.IsCoherent :=
      isCoherent_pullback contMDiff_subtype_val hIY
    have hRec := IsTowerIso.geoTransformAlong_eq
      (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) U)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) M)
      (T' := T) (T := restrict U Q) (χ := e)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) hNU hIU he
      (isGeoTestTower_restrict U hN hI Q hQ)
    change geoTransformAlong (MarkedIdeal.pullback (id : U → U)
      (MarkedIdeal.pullback (Subtype.val : U → X) M)) T = _ at hRec
    rw [pullback_id_coherent _ hIU,
      geoTransformAlong_restrict U hN hI Q hQ] at hRec
    have hDC : (MarkedIdeal.pullback (Subtype.val : V → Y)
        (geoTransformAlong M Q)).IsAdmissibleCentre D := by
      apply (isAdmissibleCentre_pullback_iff (Φ := e) hIV).mp
      rw [hDpre, ← hRec]
      exact hT.2
    have hAmbient := isAdmissibleCentre_image_val hIY hDC hKD
    refine ⟨W, .step Q ((Subtype.val : V → Y) '' D) q hq,
      ⟨hQ, hAmbient⟩, ξ, ?_⟩
    refine IsTowerIso.step
      (Z := CMfd.of (n := n)
        (openPreimage (.step Q ((Subtype.val : V → Y) '' D) q hq) U))
      he hπ (isBlowupAlong_restrict hq V
        (V.isOpen.preimage hq.contMDiff.continuous)) ξ ?_ ?_
    · intro p
      apply Subtype.ext
      exact hξ p
    · change e ⁻¹' ((Subtype.val : V → Y) ⁻¹'
        ((Subtype.val : V → Y) '' D)) = C
      rw [Subtype.val_injective.preimage_image]
      exact hDpre

end
end TranscendentalNakamaye.Pending.HironakaOriginalOldBranchCompactExtension

