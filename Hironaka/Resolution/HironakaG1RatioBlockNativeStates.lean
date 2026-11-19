import Hironaka.Resolution.HironakaG1RatioBlockGraphAdapters
import Hironaka.Resolution.HironakaG1SingularGraphCodimension
import Hironaka.Resolution.HironakaActualOpenEmbeddingCanonicalExtension

/-! Native states and the singular dimension bound on the literal ratio graph. -/
set_option autoImplicit false
open Set TopologicalSpace Filter
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioBlockNativeStates
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HironakaG11PresLineState HironakaBaseChange
  HironakaActualOpenEmbeddingCanonicalExtension HironakaG1IndependentFiniteNormalNative
  HironakaG1NormalGraphFlags HironakaG1SingularGraphCodimension
  HironakaSmoothSubmersionCoefficientIdeals AnalyticDimensionBasics HironakaG1CodimensionTwoChartTransport HironakaEmbeddedAnalytic AnalyticSubsetOpens

/-- Reindex an actual biholomorphic open image without changing the pulled record. -/
theorem nativeState_markedPullback_openImage {d e : ℕ} (h : d = e)
    {X : CMfd.{0} d} {Y : CMfd.{0} e} {P : MarkedIdeal e Y} {C : Set Y} {H : ℕ → ℕ}
    (hP : NativeHSState P C H) (hD : IsInvDomain e P)
    (f : X → Y) (O : Opens Y)
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel e)⟯ O)
    (hb : ∀ z, f z = (b z).val) :
    IsInvDomain d (markedPullback (m := d) f P) ∧
      NativeHSState (markedPullback (m := d) f P) (f ⁻¹' C) H := by
  subst e
  have hf : IsOpenHoloEmbedding d f := ⟨O,b,hb⟩
  exact ⟨isInvDomain_pullback_of_isOpenHoloEmbedding f hf hD,
    nativeHSState_pullback_openEmbedding hP f hf⟩

/-- A positive normal complement gives codimension two at every genuine
native cut point in the pullback of a block graph. -/
theorem blockGraph_preimage_codim_two {a b : ℕ} (hb : 0 < b)
    {A : Opens (ComplexModel a)} {X : CMfd.{0} (a+b)}
    (e : X → blockOpen A b) (he : IsOpenHoloEmbedding (a+b) e)
    (f : A → ComplexModel b)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ f)
    {C : Set A} {P : MarkedIdeal (a+b) X} {H : ℕ → ℕ}
    (hP : NativeHSState P (e ⁻¹' blockGraph f C) H) :
    ∀ x ∈ P.cosupp, ∃ k, k + 2 ≤ a+b ∧ LocDimLE (n := a+b) (e ⁻¹' blockGraph f C) x k := by
  intro x hx
  let G : Set (blockOpen A b) := blockGraph f univ
  have hSub : e ⁻¹' blockGraph f C ⊆ e ⁻¹' G := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hSing := mem_singularSet_iff.mp (native_cut_singular hP hx)
  have hReg : RegularAtDim (n := a+b) G (e x) a :=
    regularAtDim_blockGraph_of hf (hSub hSing.1) (AnalyticIrreducibleComponents.regularAtDim_univ _)
  have hB : RegularAtDim (n := a+b) (e ⁻¹' G) x a := he.regularAtDim_preimage hReg
  by_cases ha : 0 < a
  · exact ⟨a - 1, by omega, native_cut_locDimLE_of_smooth_envelope hP hx hB (Eventually.of_forall hSub)⟩
  · have hGE : LocDimGE (n := a+b) (e ⁻¹' blockGraph f C) x a := by
      intro O hO
      obtain ⟨z,hz,k,_,hReg⟩ := locDimGE_zero hP.2.1 hSing.1 O hO
      exact ⟨z,hz,k,by omega,hReg⟩
    have heq := CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE hP.2.1 hB
      (Eventually.of_forall hSub) hGE
    exact (hSing.2 a
      (CodimOneSupport.regularAtDim_of_eventually_mem_iff (heq.mono fun _ h => h.symm) hB)).elim

section OpenImage
variable {d e : ℕ} {X : CMfd.{0} d} {Y : CMfd.{0} e}

private def imageOpen (f : X → Y) (hf : Topology.IsOpenEmbedding f) : Opens Y :=
  ⟨range f, hf.isOpen_range⟩

private theorem openImage_of_inverse (f : X → Y) (hf : Topology.IsOpenEmbedding f)
    (hhol : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel e) ∞ f)
    (g : imageOpen f hf → X)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel e) 𝓘(ℂ,ComplexModel d) ∞ g)
    (hgf : ∀ x : X, g ⟨f x,mem_range_self x⟩ = x)
    (hfg : ∀ y : imageOpen f hf, f (g y) = y.val) :
    ∃ b : X ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel e)⟯ imageOpen f hf,
      ∀ x, f x = (b x).val := by
  let b (x : X) : imageOpen f hf := ⟨f x,mem_range_self x⟩
  have hb : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel e) ∞ b :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp hhol
  exact ⟨⟨⟨b,g,hgf,fun y => Subtype.ext (hfg y)⟩,hb,hg⟩,fun _ => rfl⟩
end OpenImage

open HironakaG1RatioBlockGraphAdapters HironakaG1RelativeBoundaryProjections
  HironakaG1SNCReaderNormalization HironakaG1RelativeReaderWindow
  HironakaG1ReaderProductSubmersions HironakaG1RatioGraphProductEquations
  HironakaActualIntrinsicStableAmbientIso HironakaActualCentreJointJets
  HironakaG1IteratedNormalBlockIdeal HironakaRelativeNormalIdeal

section Bases
variable {d e : ℕ} {M : CMfd.{0} d} {S : Opens M} {T : Opens (ComplexModel e)}
  (η : S ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel e)⟯ T) (U : Opens M)

private theorem base_le : normalizedBaseOpen η U ≤ T := fun _ ⟨w,_,he⟩ => he ▸ w.property

/-- The normalized base map is an actual biholomorphism onto its ambient image. -/
theorem normalizedBaseMap_openImage :
    ∃ (O : Opens M) (b : normalizedBaseOpen η U ≃ₘ⟮𝓘(ℂ,ComplexModel e),𝓘(ℂ,ComplexModel d)⟯ O),
      ∀ x, normalizedBaseMap η U x = (b x).val := by
  let O : Opens M := S ⊓ U
  let f (x : normalizedBaseOpen η U) : O :=
    ⟨normalizedBaseMap η U x, (η.symm (Opens.inclusion (base_le η U) x)).property,
      normalizedBaseMap_mem η U x⟩
  let i (y : O) : S := ⟨y.val,y.property.1⟩
  let g (y : O) : normalizedBaseOpen η U :=
    ⟨(η (i y)).val,η (i y),by
      change (η.symm (η (i y))).val ∈ U
      rw [η.symm_apply_apply]
      exact y.property.2,rfl⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel e) 𝓘(ℂ,ComplexModel d) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff O f).mp (normalizedBaseMap_hol η U)
  have hg : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel e) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff (normalizedBaseOpen η U) g).mp (by
      change ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel e) ∞
        ((Subtype.val : T → ComplexModel e) ∘ η ∘ Opens.inclusion (inf_le_left : O ≤ S))
      exact contMDiff_subtype_val.comp (η.contMDiff.comp (contMDiff_inclusion inf_le_left)))
  refine ⟨O,⟨⟨f,g,?_,?_⟩,hf,hg⟩,fun _ => rfl⟩
  · intro x
    apply Subtype.ext
    change (η (η.symm (Opens.inclusion (base_le η U) x))).val = x.val
    rw [η.apply_symm_apply]
  · intro y
    apply Subtype.ext
    change normalizedBaseMap η U (g y) = y.val
    rw [show (g y : normalizedBaseOpen η U) = ⟨(η (i y)).val, (g y).property⟩ from rfl,
      normalizedBaseMap_on_reader η U (η (i y)) (by simpa using y.property.2)]
    rw [η.symm_apply_apply]
end Bases
section Adapters
variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}
  {p : M} {q : N} {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
  (R : RelativeReaders p q E F τ) (U : Opens M) (V : Opens N)
private abbrev dim := (R.r+R.a)+(R.r+R.b)
private abbrev Left := blockOpen (LBase R U) (R.r+R.b)
private abbrev Right := blockOpen (RBase R V) (R.r+R.a)

private def splitBlock (a b : ℕ) (z : ComplexModel (a+b)) : ComplexModel a × ComplexModel b :=
  (tangentProjection a b z,actualJointNormalProjection a b z)

private theorem splitBlock_hol (a b : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel (a+b)) 𝓘(ℂ,ComplexModel a × ComplexModel b) ∞ (splitBlock a b) :=
  (tangentProjection a b).contDiff.contMDiff.prodMk_space
    (actualJointNormalProjection a b).contDiff.contMDiff

private theorem splitBlock_join {a b : ℕ} (u : ComplexModel a) (v : ComplexModel b) :
    splitBlock a b (HironakaActualIntrinsicStableAmbientIso.join u v) = (u,v) :=
  Prod.ext (first_join _ _) (second_join _ _)

/-- The left cylinder adapter is biholomorphic onto its actual open image. -/
theorem leftBlockMap_openImage :
    ∃ (O : Opens (Left R U)) (b : Common R U V ≃ₘ⟮𝓘(ℂ,ComplexModel (dim R)),
      𝓘(ℂ,ComplexModel (dim R))⟯ O), ∀ z, leftBlockMap R U V z = (b z).val := by
  let f := leftBlockMap R U V
  have hf := leftBlockMap_openEmbedding R U V
  let O := imageOpen (X := CMfd.of (n := dim R) (Common R U V))
    (Y := CMfd.of (n := dim R) (Left R U)) f hf
  let g₀ (y : Left R U) : ComplexModel (dim R) :=
    ambientEuclidean R.r R.a R.b ((sourceProduct R.r R.a R.b).symm
      (splitBlock (R.r+R.a) (R.r+R.b) y.val))
  have hgf (z : Common R U V) : g₀ (f z) = z.val.val := by
    change ambientEuclidean R.r R.a R.b ((sourceProduct R.r R.a R.b).symm
      (splitBlock _ _ (HironakaActualIntrinsicStableAmbientIso.join _ _))) = _
    rw [splitBlock_join]
    change ambientEuclidean R.r R.a R.b ((sourceProduct R.r R.a R.b).symm
      (sourceProduct R.r R.a R.b ((ambientEuclidean R.r R.a R.b).symm z.val.val))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  have h₁ (y : O) : g₀ y.val ∈ euclideanReaderWindow R := by
    obtain ⟨z,hz⟩ := y.property
    rw [← hz, hgf]
    exact z.val.property
  let g₁ (y : O) : euclideanReaderWindow R := ⟨g₀ y.val,h₁ y⟩
  have h₂ (y : O) : g₁ y ∈ Common R U V := by
    obtain ⟨z,hz⟩ := y.property
    have h : g₁ y = z.val := Subtype.ext ((congrArg g₀ hz).symm.trans (hgf z))
    rw [h]
    exact z.property
  let g (y : O) : Common R U V := ⟨g₁ y,h₂ y⟩
  have hg : ContMDiff 𝓘(ℂ,ComplexModel (dim R)) 𝓘(ℂ,ComplexModel (dim R)) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact (ambientEuclidean R.r R.a R.b).contDiff.contMDiff.comp
      ((sourceProduct R.r R.a R.b).symm.contDiff.contMDiff.comp
        ((splitBlock_hol _ _).comp (contMDiff_subtype_val.comp contMDiff_subtype_val)))
  have hLeft (z : Common R U V) : g ⟨f z,mem_range_self z⟩ = z :=
    Subtype.ext (Subtype.ext (hgf z))
  have hRight (y : O) : f (g y) = y.val := by
    obtain ⟨z,hz⟩ := y.property
    have h : y = ⟨f z,mem_range_self z⟩ := Subtype.ext hz.symm
    rw [h,hLeft]
  obtain ⟨b,hb⟩ := openImage_of_inverse (X := CMfd.of (n := dim R) (Common R U V))
    (Y := CMfd.of (n := dim R) (Left R U)) f hf (leftBlockMap_hol R U V) g hg hLeft hRight
  exact ⟨O,b,hb⟩

/-- The scaled right cylinder adapter is biholomorphic onto its actual open image. -/
theorem rightBlockMap_openImage :
    ∃ (O : Opens (Right R V)) (b : Common R U V ≃ₘ⟮𝓘(ℂ,ComplexModel (dim R)),
      𝓘(ℂ,ComplexModel ((R.r+R.b)+(R.r+R.a)))⟯ O), ∀ z, rightBlockMap R U V z = (b z).val := by
  let f := rightBlockMap R U V
  have hf := rightBlockMap_openEmbedding R U V
  let O := imageOpen (X := CMfd.of (n := dim R) (Common R U V))
    (Y := CMfd.of (n := (R.r+R.b)+(R.r+R.a)) (Right R V)) f hf
  let s (y : Right R V) := (targetProduct R.r R.a R.b).symm
    (splitBlock (R.r+R.b) (R.r+R.a) y.val)
  let raw (z : Common R U V) := (graphEquationWindowToRatio R U V z).val
  have hu (z : Common R U V) : raw z ∈ unitLocus R.r R.a R.b :=
    (graphEquationWindowToRatio R U V z).property.1.1
  have hs (z : Common R U V) : s (f z) = unitScaling R.r R.a R.b (raw z) := by
    change (targetProduct R.r R.a R.b).symm
      (splitBlock _ _ (HironakaActualIntrinsicStableAmbientIso.join _ _)) = _
    rw [splitBlock_join]
    exact (targetProduct R.r R.a R.b).symm_apply_apply _
  let g₀ (y : Right R V) : ComplexModel (dim R) :=
    ambientEuclidean R.r R.a R.b (unitUnscaling R.r R.a R.b (s y))
  have hgf (z : Common R U V) : g₀ (f z) = z.val.val := by
    change ambientEuclidean R.r R.a R.b (unitUnscaling R.r R.a R.b (s (f z))) = _
    rw [hs, unitUnscaling_unitScaling _ _ _ _ (hu z)]
    exact (ambientEuclidean R.r R.a R.b).apply_symm_apply _
  have h₁ (y : O) : g₀ y.val ∈ euclideanReaderWindow R := by
    obtain ⟨z,hz⟩ := y.property
    rw [← hz,hgf]
    exact z.val.property
  let g₁ (y : O) : euclideanReaderWindow R := ⟨g₀ y.val,h₁ y⟩
  let g (y : O) : Common R U V := ⟨g₁ y,by
    obtain ⟨z,hz⟩ := y.property
    have h : g₁ y = z.val := Subtype.ext ((congrArg g₀ hz).symm.trans (hgf z))
    rw [h]
    exact z.property⟩
  have hsu (y : O) : s y.val ∈ unitLocus R.r R.a R.b := by
    obtain ⟨z,hz⟩ := y.property
    rw [← hz,hs]
    exact hu z
  have hshol : ContMDiff 𝓘(ℂ,ComplexModel ((R.r+R.b)+(R.r+R.a)))
      𝓘(ℂ,Ambient R.r R.a R.b) ∞ (fun y : O => s y.val) :=
    (targetProduct R.r R.a R.b).symm.contDiff.contMDiff.comp
      ((splitBlock_hol _ _).comp (contMDiff_subtype_val.comp contMDiff_subtype_val))
  have hg : ContMDiff 𝓘(ℂ,ComplexModel ((R.r+R.b)+(R.r+R.a))) 𝓘(ℂ,ComplexModel (dim R)) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact (ambientEuclidean R.r R.a R.b).contDiff.contMDiff.comp
      (contMDiffOn_univ.mp ((contDiffOn_unitUnscaling R.r R.a R.b).contMDiffOn.comp
        hshol.contMDiffOn (fun y _ => hsu y)))
  have hLeft (z : Common R U V) : g ⟨f z,mem_range_self z⟩ = z :=
    Subtype.ext (Subtype.ext (hgf z))
  have hRight (y : O) : f (g y) = y.val := by
    obtain ⟨z,hz⟩ := y.property
    have h : y = ⟨f z,mem_range_self z⟩ := Subtype.ext hz.symm
    rw [h,hLeft]
  obtain ⟨b,hb⟩ := openImage_of_inverse (X := CMfd.of (n := dim R) (Common R U V))
    (Y := CMfd.of (n := (R.r+R.b)+(R.r+R.a)) (Right R V)) f hf (rightBlockMap_hol R U V) g hg hLeft hRight
  exact ⟨O,b,hb⟩

set_option maxHeartbeats 1200000 in
/-- The two actual marked pullbacks retain their original native states
on the common graph and their ordinary invariant domains. Positivity of
the left normal complement gives the local bound at every native cut point. -/
theorem ratioMarked_nativeStates
    {C : Set M} {D : Set N} {G : Set (readerUnitWindow R)}
    (P : MarkedIdeal n M) (Q : MarkedIdeal m N) (H : ℕ → ℕ)
    (hP : NativeHSState P C H) (hPD : IsInvDomain n P)
    (hQ : NativeHSState Q D H) (hQD : IsInvDomain m Q)
    (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
    (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a)
    (ha : ∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x)
    (hb : ∀ y ∈ V, ∀ i, HolomorphicAt m (b i) y)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel R.b) ∞ forward U)
    (hg : ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel R.a) ∞ backward V)
    (hL : ∀ z : readerUnitWindow R, z ∈ G ↔ firstReaderMap R z ∈ C ∩ (U : Set M) ∧
      (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (firstReaderMap R z))
    (hR : ∀ z : readerUnitWindow R, z ∈ G ↔ secondReaderMap R z ∈ D ∩ (V : Set N) ∧
      (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).2 =
        rightGraphValue R b backward (secondReaderMap R z)) :
    let X := CMfd.of (n := dim R) (Common R U V)
    let L := leftRatioMarked R U V a forward P
    let T := rightRatioMarked R U V b backward Q
    let K := graphEquationWindowToRatio R U V ⁻¹' G
    IsInvDomain (dim R) L ∧ IsInvDomain (dim R) T ∧
      NativeHSState (X := X) L K H ∧ NativeHSState (X := X) T K H ∧
      (0 < R.r+R.b → ∀ x ∈ L.cosupp, ∃ k, k + 2 ≤ dim R ∧ LocDimLE (n := dim R) K x k) := by
  intro X L T K
  obtain ⟨OL, eL, hOL⟩ := normalizedBaseMap_openImage R.sourceDiffeomorph U
  obtain ⟨OR, eR, hOR⟩ := normalizedBaseMap_openImage R.targetDiffeomorph V
  let BL := CMfd.of (n := R.r+R.a) (LBase R U)
  let BR := CMfd.of (n := R.r+R.b) (RBase R V)
  obtain ⟨hLBD,hLBS⟩ := nativeState_markedPullback_openImage
    R.dimension₁.symm (X := BL) hP hPD _ OL eL hOL
  obtain ⟨hRBD,hRBS⟩ := nativeState_markedPullback_openImage
    R.dimension₂.symm (X := BR) hQ hQD _ OR eR hOR
  have hfL := leftBlockGraphValue_hol R U a forward ha hf
  have hfR := rightBlockGraphValue_hol R V b backward hb hg
  obtain ⟨hLCD,hLCS⟩ := blockAmbientMarked_nativeHSState _ hfL _ H hLBS hLBD
  obtain ⟨hRCD,hRCS⟩ := blockAmbientMarked_nativeHSState _ hfR _ H hRBS hRBD
  obtain ⟨IL,bL,hIL⟩ := leftBlockMap_openImage R U V
  obtain ⟨IR,bR,hIR⟩ := rightBlockMap_openImage R U V
  obtain ⟨hLD,hLS⟩ := nativeState_markedPullback_openImage rfl (X := X) hLCS hLCD _ IL bL hIL
  obtain ⟨hRD,hRS⟩ := nativeState_markedPullback_openImage (Nat.add_comm (R.r+R.a) (R.r+R.b))
    (X := X) hRCS hRCD _ IR bR hIR
  obtain ⟨hLK,hRK⟩ := blockGraph_preimages R U V a b forward backward hL hR
  have hl : NativeHSState (X := X) L K H := by simpa only [L,K,leftRatioMarked,hLK] using hLS
  have hr : NativeHSState (X := X) T K H := by simpa only [T,K,rightRatioMarked,hRK] using hRS
  refine ⟨hLD,hRD,hl,hr,fun hpos => ?_⟩
  have he : IsOpenHoloEmbedding (dim R) (leftBlockMap R U V) := ⟨IL,bL,hIL⟩
  simpa only [L,K,leftRatioMarked,hLK] using (blockGraph_preimage_codim_two hpos (X := X) _ he _ hfL hLS)

end Adapters
end
end Hironaka.HironakaG1RatioBlockNativeStates
