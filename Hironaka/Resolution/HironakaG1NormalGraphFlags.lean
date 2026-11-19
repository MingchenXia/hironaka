import Hironaka.Resolution.HironakaG1NormalGraphInitialization

/-! Actual graph changes with finitely many normal coordinates. -/
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NormalGraphFlags

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers GermIdealPullbackCalculus InvertibleIdealQuotient RestrictedIdealExtension
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaActualPowerBoundaryExponents HironakaSmoothSubmersionCoefficientIdeals
  IdealWeightPowers IdealOrderArithmetic ResolutionInvariantSpec
  MarkedIdealOperationsAlong.MarkedIdeal RestrictLeCalculus HironakaActualOpenSectionRepresentative
  HironakaG8LocalHistory HironakaG8LocalContactStage NormalCrossings DivisorExponentAlong

variable {n t : ℕ} {U V W : Opens (ComplexModel n)}

/-- The actual open set over the source with a full block of normal coordinates. -/
def blockOpen (U : Opens (ComplexModel n)) (t : ℕ) : Opens (ComplexModel (n + t)) :=
  ⟨tangentProjection n t ⁻¹' U, U.isOpen.preimage (tangentProjection n t).continuous⟩

private abbrev base (U : Opens (ComplexModel n)) := CMfd.of (n := n) U
private abbrev ambient (U : Opens (ComplexModel n)) (t : ℕ) := CMfd.of (n := n + t) (blockOpen U t)

def blockProjection (z : blockOpen U t) : U := ⟨tangentProjection n t z.val, z.property⟩

/-- Projection from an actual normal block is holomorphic. -/
theorem blockProjection_contMDiff (U : Opens (ComplexModel n)) (t : ℕ) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + t)) 𝓘(ℂ, ComplexModel n) ∞
      (blockProjection : blockOpen U t → U) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (tangentProjection n t).contMDiff.comp contMDiff_subtype_val

private def blockNormal (z : blockOpen U t) : ComplexModel t :=
  actualJointNormalProjection n t z.val

def blockChartMap (b : U → V) (f : U → ComplexModel t) (g : V → ComplexModel t)
    (z : blockOpen U t) : blockOpen V t :=
  ⟨join (b (blockProjection z)).val
      (blockNormal z - f (blockProjection z) + g (b (blockProjection z))), by
    change tangentProjection n t (join _ _) ∈ V
    rw [first_join]
    exact (b (blockProjection z)).property⟩

@[simp] theorem blockProjection_chartMap (b : U → V)
    (f : U → ComplexModel t) (g : V → ComplexModel t) (z : blockOpen U t) :
    blockProjection (blockChartMap b f g z) = b (blockProjection z) :=
  Subtype.ext (first_join _ _)

@[simp] private theorem blockNormal_chartMap (b : U → V)
    (f : U → ComplexModel t) (g : V → ComplexModel t) (z : blockOpen U t) :
    blockNormal (blockChartMap b f g z) =
      blockNormal z - f (blockProjection z) + g (b (blockProjection z)) :=
  second_join _ _

theorem blockChartMap_contMDiff {b : U → V}
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + t)) 𝓘(ℂ, ComplexModel (n + t)) ∞
      (blockChartMap b f g) := by
  apply (ContMDiff.subtypeVal_comp_iff (blockOpen V t) _).mp
  have hp := blockProjection_contMDiff U t
  have hBase := (contMDiff_subtype_val (U := V)).comp (hb.comp hp)
  have hNormal : ContMDiff 𝓘(ℂ, ComplexModel (n + t)) 𝓘(ℂ, ComplexModel t) ∞
      (blockNormal : blockOpen U t → ComplexModel t) :=
    (actualJointNormalProjection n t).contMDiff.comp contMDiff_subtype_val
  exact ((tangentInclusion n t).contMDiff.comp hBase).add
    ((actualJointNormalInclusion n t).contMDiff.comp
      ((hNormal.sub (hf.comp hp)).add (hg.comp (hb.comp hp))))

/-- Intermediate selectors cancel in the actual composite ambient map. -/
theorem blockChartMap_comp (b : U → V) (c : V → W)
    (f : U → ComplexModel t) (g : V → ComplexModel t) (h : W → ComplexModel t) :
    blockChartMap c g h ∘ blockChartMap b f g = blockChartMap (c ∘ b) f h := by
  funext z
  apply Subtype.ext
  change join (c (blockProjection (blockChartMap b f g z))).val
      (blockNormal (blockChartMap b f g z) - g (blockProjection (blockChartMap b f g z)) +
        h (c (blockProjection (blockChartMap b f g z)))) =
    join (c (b (blockProjection z))).val
      (blockNormal z - f (blockProjection z) + h (c (b (blockProjection z))))
  simp only [blockProjection_chartMap, blockNormal_chartMap, add_sub_cancel_right]

private theorem blockChartMap_id (f : U → ComplexModel t) (z : blockOpen U t) :
    blockChartMap id f f z = z := by
  apply Subtype.ext
  change join (blockProjection z).val (blockNormal z - f (blockProjection z) + f (blockProjection z)) = z.val
  rw [sub_add_cancel]
  exact join_projections z.val

/-- The actual normal-block biholomorphism over a source biholomorphism. -/
def blockChartEquiv (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g) :
    blockOpen U t ≃ₘ⟮𝓘(ℂ, ComplexModel (n + t)), 𝓘(ℂ, ComplexModel (n + t))⟯ blockOpen V t where
  toEquiv :=
    ⟨blockChartMap b f g, blockChartMap b.symm g f,
      fun z => by
        have h : (b.symm : V → U) ∘ b = id := funext b.symm_apply_apply
        have hs := blockChartMap_comp (b : U → V) (b.symm : V → U) f g f
        rw [h] at hs
        exact (congrFun hs z).trans (blockChartMap_id f z),
      fun z => by
        have h : (b : U → V) ∘ b.symm = id := funext b.apply_symm_apply
        have hs := blockChartMap_comp (b.symm : V → U) (b : U → V) g f g
        rw [h] at hs
        exact (congrFun hs z).trans (blockChartMap_id g z)⟩
  contMDiff_toFun := blockChartMap_contMDiff b.contMDiff hf hg
  contMDiff_invFun := blockChartMap_contMDiff b.symm.contMDiff hg hf

def blockGraph (f : U → ComplexModel t) (A : Set U) : Set (blockOpen U t) :=
  {z | blockProjection z ∈ A ∧ blockNormal z = f (blockProjection z)}

theorem blockChartMap_preimage_graph (b : U → V) (f : U → ComplexModel t)
    (g : V → ComplexModel t) (A : Set V) :
    blockChartMap b f g ⁻¹' blockGraph g A = blockGraph f (b ⁻¹' A) := by
  ext z
  change (_ ∈ A ∧ blockNormal (blockChartMap b f g z) = g (blockProjection (blockChartMap b f g z))) ↔
    (b (blockProjection z) ∈ A ∧ blockNormal z = f (blockProjection z))
  simp [sub_eq_zero]

private def blockCoordinate (f : U → ComplexModel t) (i : Fin t) (z : blockOpen U t) : ℂ :=
  (blockNormal z - f (blockProjection z)) i

private theorem blockCoordinate_contMDiff {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f) (i : Fin t) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + t)) 𝓘(ℂ, ℂ) ∞ (blockCoordinate f i) :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff.comp
    (((actualJointNormalProjection n t).contMDiff.comp contMDiff_subtype_val).sub
      (hf.comp (blockProjection_contMDiff U t)))

/-- Graph-supported padding by every coordinate of an actual normal block. -/
def blockMarked (f : U → ComplexModel t) (Q : MarkedIdeal n U)
    (F : List (Set (blockOpen U t))) : MarkedIdeal (n + t) (ambient U t) :=
  ⟨blockGraph f Q.N, F ++ Q.E.map (blockProjection ⁻¹' ·),
    sumIdeal (GermIdeal.pullback (m := n + t) blockProjection Q.ideal)
      (finiteFunctionIdeal (fun i z => blockCoordinate f i z ^ Q.d)), Q.d⟩

/-- The graph ideal is coherent for a holomorphic selector and coherent source. -/
theorem blockMarked_coherent {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    {Q : MarkedIdeal n U} (hQ : Q.ideal.IsCoherent) (F : List (Set (blockOpen U t))) :
    (blockMarked f Q F).ideal.IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (blockProjection_contMDiff U t) hQ)
    (isCoherent_finiteFunctionIdeal _ (fun i => ((blockCoordinate_contMDiff hf i).mdifferentiable (by simp)).pow Q.d))

/-- Exact pullback of the whole powered normal-block record, retaining every
ordered extra boundary slot on the actual enlarged ambient. -/
theorem pullback_power_blockMarked {b : U → V}
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (Q : MarkedIdeal n V) (hQ : Q.ideal.IsCoherent) (F : List (Set (blockOpen V t))) (e : ℕ) :
    MarkedIdeal.pullback (M := ambient V t) (M' := ambient U t) (blockChartMap b f g)
      (powerMarked (blockMarked g Q F) e) =
      powerMarked (blockMarked f (MarkedIdeal.pullback (M := base V) (M' := base U) b Q)
        (F.map (blockChartMap b f g ⁻¹' ·))) e := by
  have hMap := blockChartMap_contMDiff hb hf hg
  rw [HironakaG11PresClassTransport.pullback_powerMarked (M := ambient V t) (M' := ambient U t)
    (f := blockChartMap b f g) hMap _ (blockMarked_coherent hg hQ F)]
  congr 1
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact blockChartMap_preimage_graph b f g Q.N
  · change (F ++ Q.E.map (blockProjection ⁻¹' ·)).map (blockChartMap b f g ⁻¹' ·) = _
    rw [List.map_append, List.map_map]
    simp only [blockMarked, MarkedIdeal.pullback, List.map_map, preimage_preimage,
      Function.comp_def, blockProjection_chartMap]
  · have hGen (i : Fin t) :
        MDifferentiable 𝓘(ℂ, ComplexModel (n + t)) 𝓘(ℂ, ℂ)
          (fun z => blockCoordinate g i z ^ Q.d) :=
      ((blockCoordinate_contMDiff hg i).mdifferentiable (by simp)).pow _
    change GermIdeal.pullback (m := n + t) (blockChartMap b f g)
      (sumIdeal (GermIdeal.pullback (m := n + t) blockProjection Q.ideal)
        (finiteFunctionIdeal (fun i z => blockCoordinate g i z ^ Q.d))) = _
    rw [pullback_sumIdeal_dimensions hMap (isCoherent_pullback (blockProjection_contMDiff V t) hQ)
      (isCoherent_finiteFunctionIdeal _ hGen),
      ← coherent_pullback_comp (blockProjection_contMDiff V t) hMap Q.ideal hQ,
      finiteFunctionIdeal_pullback _ hGen _ hMap]
    have hp : blockProjection ∘ blockChartMap b f g = b ∘ blockProjection :=
      funext (blockProjection_chartMap b f g)
    rw [hp, coherent_pullback_comp hb (blockProjection_contMDiff U t) Q.ideal hQ]
    congr 1
    congr 1
    funext i z
    change blockCoordinate g i (blockChartMap b f g z) ^ Q.d = blockCoordinate f i z ^ Q.d
    simp [blockCoordinate]
  · rfl


/-- The whole graph record pulls back through the actual change of
base charts and selectors, including the ordered extra boundary. -/
theorem pullback_blockMarked {b : U → V}
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (Q : MarkedIdeal n V) (hQ : Q.ideal.IsCoherent) (F : List (Set (blockOpen V t))) :
    MarkedIdeal.pullback (M := ambient V t) (M' := ambient U t) (blockChartMap b f g)
      (blockMarked g Q F) =
    blockMarked f (MarkedIdeal.pullback (M := base V) (M' := base U) b Q)
      (F.map (blockChartMap b f g ⁻¹' ·)) := by
  have h := pullback_power_blockMarked hb hf hg Q hQ F 1
  have hBase : (MarkedIdeal.pullback (M := base V) (M' := base U) b Q).ideal.IsCoherent :=
    isCoherent_pullback hb hQ
  simpa only [powerMarked, Nat.mul_one,
    FactorizationFromResolution.idealPow_one_of_isCoherent (blockMarked_coherent hg hQ F),
    FactorizationFromResolution.idealPow_one_of_isCoherent (blockMarked_coherent hf hBase _)] using h

/-- The actual section of a finite normal graph. -/
def blockSection (f : U → ComplexModel t) (x : U) : blockOpen U t :=
  ⟨join x.val (f x), by
    change tangentProjection n t (join _ _) ∈ U
    rw [first_join]
    exact x.property⟩

@[simp] theorem blockProjection_blockSection (f : U → ComplexModel t) (x : U) :
    blockProjection (blockSection f x) = x := Subtype.ext (first_join _ _)

@[simp] private theorem blockNormal_blockSection (f : U → ComplexModel t) (x : U) :
    blockNormal (blockSection f x) = f x := second_join _ _

/-- The section of a holomorphic finite normal graph is holomorphic. -/
theorem blockSection_contMDiff {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + t)) ∞ (blockSection f) := by
  apply (ContMDiff.subtypeVal_comp_iff (blockOpen U t) _).mp
  exact ((tangentInclusion n t).contMDiff.comp contMDiff_subtype_val).add
    ((actualJointNormalInclusion n t).contMDiff.comp hf)

private theorem blockSection_ideal_trace {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hd : 0 < Q.d)
    (F : List (Set (blockOpen U t))) :
    GermIdeal.pullback (m := n) (blockSection f) (blockMarked f Q F).ideal = Q.ideal := by
  have hp := blockProjection_contMDiff U t
  have hs := blockSection_contMDiff hf
  have hGen (i : Fin t) : MDifferentiable 𝓘(ℂ, ComplexModel (n + t)) 𝓘(ℂ, ℂ)
      (fun z => blockCoordinate f i z ^ Q.d) :=
    ((blockCoordinate_contMDiff hf i).mdifferentiable (by simp)).pow _
  change GermIdeal.pullback (m := n) (blockSection f)
    (sumIdeal (GermIdeal.pullback (m := n + t) blockProjection Q.ideal)
      (finiteFunctionIdeal (fun i z => blockCoordinate f i z ^ Q.d))) = Q.ideal
  rw [pullback_sumIdeal_dimensions hs (isCoherent_pullback hp hQ)
    (isCoherent_finiteFunctionIdeal _ hGen), ← coherent_pullback_comp hp hs Q.ideal hQ,
    finiteFunctionIdeal_pullback _ hGen _ hs]
  have hRet : blockProjection ∘ blockSection f = id := funext (blockProjection_blockSection f)
  rw [hRet, BlowupControlledTransform.pullback_id hQ]
  have hZero : (fun (i : Fin t) => (fun z => blockCoordinate f i z ^ Q.d) ∘ blockSection f) =
      (fun _ _ => 0) := by
    funext i x
    simp [blockCoordinate, Nat.ne_of_gt hd]
  rw [hZero]
  apply GermIdeal.ext
  funext x a
  apply propext
  refine ⟨?_, le_sumIdeal_left hQ x a⟩
  intro ha
  apply HomogenizedIdeal.mem_of_isInSpanAt hQ
  refine IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp ha)
  rintro v (hv | hv)
  · exact isInSpanAt_self hv (GermIdeal.IsCoherent.holomorphicAt_mem hQ hv)
  · refine IsInSpanAt.trans ?_ hv
    rintro _ ⟨_, rfl⟩
    exact BlowupStrictIdeal.isInSpanAt_zero

/-- Section restriction of the entire normal-block power recovers the entire
positive source power and every actual restricted extra boundary slot. -/
theorem markedPullback_power_blockSection {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hd : 0 < Q.d)
    (F : List (Set (blockOpen U t))) (e : ℕ) :
    markedPullback (m := n) (blockSection f) (powerMarked (blockMarked f Q F) e) =
      { powerMarked (X := base U) Q e with E := F.map (blockSection f ⁻¹' ·) ++ Q.E } := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext x
    change (blockProjection (blockSection f x) ∈ Q.N ∧ blockNormal (blockSection f x) =
      f (blockProjection (blockSection f x))) ↔ x ∈ Q.N
    simp
  · change (F ++ Q.E.map (blockProjection ⁻¹' ·)).map (blockSection f ⁻¹' ·) =
        F.map (blockSection f ⁻¹' ·) ++ Q.E
    rw [List.map_append, List.map_map]
    have hRet : blockProjection ∘ blockSection f = id := funext (blockProjection_blockSection f)
    change F.map (blockSection f ⁻¹' ·) ++ Q.E.map (fun H => (blockProjection ∘ blockSection f) ⁻¹' H) = _
    rw [hRet]
    simp
  · change GermIdeal.pullback (m := n) (blockSection f) (idealPow (blockMarked f Q F).ideal e) =
      idealPow Q.ideal e
    rw [pullback_idealPow (blockSection_contMDiff hf) (blockMarked_coherent hf hQ F),
      blockSection_ideal_trace hf Q hQ hd F]
  · rfl


/-- Along the graph carrier all added normal powers vanish. The remaining
trace of the whole powered record is the pulled-back source power. -/
theorem restrictEquiv_blockPower_trace {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hd : 0 < Q.d)
    (F : List (Set (blockOpen U t))) (e : ℕ) :
    RestrictEquiv (powerMarked (blockMarked f Q F) e)
      { powerMarked (blockMarked f Q F) e with
        ideal := GermIdeal.pullback (m := n + t) blockProjection (idealPow Q.ideal e) } := by
  let R := powerMarked (blockMarked f Q F) e
  have hI : R.ideal.IsCoherent := isCoherent_idealPow (blockMarked_coherent hf hQ F) e
  have hfix : ∀ z ∈ R.N, blockSection f (blockProjection z) = z := by
    intro z hz
    have hNorm : blockNormal z = f (blockProjection z) := hz.2
    apply Subtype.ext
    change join (blockProjection z).val (f (blockProjection z)) = z.val
    rw [← hNorm]
    exact join_projections z.val
  have hTrace : GermIdeal.pullback (m := n) (blockSection f) R.ideal = idealPow Q.ideal e :=
    congrArg (fun M : MarkedIdeal n U => M.ideal) (markedPullback_power_blockSection hf Q hQ hd F e)
  have hp := blockProjection_contMDiff U t
  have hs := blockSection_contMDiff hf
  have hr : GermIdeal.pullback (m := n + t) (blockSection f ∘ blockProjection) R.ideal =
      GermIdeal.pullback (m := n + t) (blockProjection : blockOpen U t → U) (idealPow Q.ideal e) := by
    rw [coherent_pullback_comp hs hp R.ideal hI, hTrace]
  have h := restrictEquiv_retraction R.N R.E R.d _ (hs.comp hp) hfix R.ideal
    (fun _ _ hx => GermIdeal.IsCoherent.holomorphicAt_mem hI hx)
  rwa [hr] at h

/-- A restricted common-power agreement of source presentations lifts through
an actual change of base charts and all finite normal graph coordinates. -/
theorem restrictEquiv_pullback_commonPower_blockMarked
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    {k l : ℕ} (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (e e' : ℕ)
    (hPow : RestrictEquiv (powerMarked (X := base U) P e)
      (MarkedIdeal.pullback (M := base V) (M' := base U) b (powerMarked (X := base V) Q e')))
    (F : List (Set (blockOpen V t))) :
    RestrictEquiv
      (powerMarked (blockMarked f P (F.map (blockChartMap b f g ⁻¹' ·))) e)
      (MarkedIdeal.pullback (M := ambient V t) (M' := ambient U t) (blockChartMap b f g)
        (powerMarked (blockMarked g Q F) e')) := by
  rw [pullback_power_blockMarked b.contMDiff hf hg Q hQ.isWellFormed.isCoherent F e']
  let Q' := MarkedIdeal.pullback (M := base V) (M' := base U) b Q
  let F' := F.map (blockChartMap b f g ⁻¹' ·)
  have hQ' : IsInvDomain l Q' := InvDomainTowerAlong.isInvDomain_pullback b hQ
  rw [HironakaG11PresClassTransport.pullback_powerMarked (M := base V) (M' := base U)
    (f := b) b.contMDiff Q hQ.isWellFormed.isCoherent] at hPow
  have hL := restrictEquiv_blockPower_trace hf P hP.isWellFormed.isCoherent hP.one_le_d F' e
  have hR := restrictEquiv_blockPower_trace hf Q' hQ'.isWellFormed.isCoherent hQ'.one_le_d F' e'
  have hN : blockGraph f P.N = blockGraph f Q'.N := congrArg (blockGraph f) hPow.N_eq
  have hE : F' ++ P.E.map (blockProjection ⁻¹' ·) = F' ++ Q'.E.map (blockProjection ⁻¹' ·) :=
    congrArg (fun E => F' ++ E.map (blockProjection ⁻¹' ·)) hPow.E_eq
  refine ⟨hN, hE, hPow.d_eq, ?_, ?_⟩
  · have hm := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (blockProjection_contMDiff U t) (fun _ (hx : _ ∈ blockGraph f P.N) => hx.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (isCoherent_idealPow hQ'.isWellFormed.isCoherent e') hg) hPow.le
    have hEnd := hR.ge
    change RestrictedIdealWeight.RestrictLe (blockGraph f Q'.N) _ _ at hEnd
    rw [← hN] at hEnd
    exact RestrictLe.trans hL.le (RestrictLe.trans hm hEnd)
  · have hm := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (blockProjection_contMDiff U t) (fun _ (hx : _ ∈ blockGraph f P.N) => hx.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (isCoherent_idealPow hP.isWellFormed.isCoherent e) hg) hPow.ge
    have hStart := hR.le
    change RestrictedIdealWeight.RestrictLe (blockGraph f Q'.N) _ _ at hStart
    rw [← hN] at hStart
    exact RestrictLe.trans hStart (RestrictLe.trans hm hL.ge)


private def zeroBlockSection (U : Opens (ComplexModel n)) (x : U) : blockOpen U t :=
  ⟨tangentInclusion n t x.val, by
    change tangentProjection n t (tangentInclusion n t x.val) ∈ U
    rw [tangentProjection_tangentInclusion]
    exact x.property⟩

private theorem zeroBlockSection_mem (A : Set U) (x : U) :
    zeroBlockSection (t := t) U x ∈ blockGraph (0 : U → ComplexModel t) A ↔ x ∈ A := by
  have hProj : blockProjection (zeroBlockSection (t := t) U x) = x :=
    Subtype.ext (tangentProjection_tangentInclusion n t x.val)
  change (blockProjection (zeroBlockSection (t := t) U x) ∈ A ∧
    actualJointNormalProjection n t (tangentInclusion n t x.val) = 0) ↔ x ∈ A
  simp [hProj]

private theorem chart_apply {m : ℕ} (U : Opens (ComplexModel m)) (x y : U) :
    chartAt (ComplexModel m) x y=y.val := by
  rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  rfl

private theorem chart_source {m : ℕ} (U : Opens (ComplexModel m)) (x y : U) :
    y∈(chartAt (ComplexModel m) x).source := by
  apply AnalyticSubsetOpens.mem_chartAt_opens_source.mpr
  rw [chartAt_self_eq]
  trivial

private theorem mem_chart_target {m : ℕ} (U : Opens (ComplexModel m)) (x : U) (v : ComplexModel m) :
    v∈(chartAt (ComplexModel m) x).target ↔ v∈U := by
  constructor
  · intro hv
    have h := (chartAt (ComplexModel m) x).right_inv hv
    rw [chart_apply] at h
    exact h ▸ ((chartAt (ComplexModel m) x).symm v).property
  · intro hv
    have h := (chartAt (ComplexModel m) x).map_source (chart_source U x ⟨v,hv⟩)
    rwa [chart_apply] at h

private def productFlat (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    LocalHolomorphicEquivAt (n := n+t)
      (chartAt (ComplexModel (n+t)) (zeroBlockSection (t := t) U x) (zeroBlockSection (t := t) U x)) where
  source := tangentProjection n t ⁻¹' Φ.source
  target := tangentProjection n t ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage (tangentProjection n t).continuous
  isOpen_target := Φ.isOpen_target.preimage (tangentProjection n t).continuous
  center_mem_source := by
    change tangentProjection n t (tangentInclusion n t x.val)∈Φ.source
    rw [tangentProjection_tangentInclusion]
    simpa only [chart_apply] using Φ.center_mem_source
  toFun := fun z => HironakaActualIntrinsicStableAmbientIso.join
    (Φ.toFun (tangentProjection n t z)) (actualJointNormalProjection n t z)
  invFun := fun z => HironakaActualIntrinsicStableAmbientIso.join
    (Φ.invFun (tangentProjection n t z)) (actualJointNormalProjection n t z)
  toFun_holomorphic := by
    intro z hz
    have hΦ := Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)
    exact (((tangentInclusion n t).differentiableAt.comp z
      (hΦ.comp z (tangentProjection n t).differentiableAt)).add
        ((actualJointNormalInclusion n t).differentiableAt.comp z
          (actualJointNormalProjection n t).differentiableAt)).differentiableWithinAt
  invFun_holomorphic := by
    intro z hz
    have hΦ := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)
    exact (((tangentInclusion n t).differentiableAt.comp z
      (hΦ.comp z (tangentProjection n t).differentiableAt)).add
        ((actualJointNormalInclusion n t).differentiableAt.comp z
          (actualJointNormalProjection n t).differentiableAt)).differentiableWithinAt
  mapsTo_toFun := by
    intro z hz
    change tangentProjection n t (HironakaActualIntrinsicStableAmbientIso.join
      (Φ.toFun (tangentProjection n t z)) (actualJointNormalProjection n t z))∈Φ.target
    rw [first_join]
    exact Φ.mapsTo_toFun hz
  mapsTo_invFun := by
    intro z hz
    change tangentProjection n t (HironakaActualIntrinsicStableAmbientIso.join
      (Φ.invFun (tangentProjection n t z)) (actualJointNormalProjection n t z))∈Φ.source
    rw [first_join]
    exact Φ.mapsTo_invFun hz
  left_inv := by
    intro z hz
    simp only [first_join,second_join,Φ.left_inv _ hz,join_projections]
  right_inv := by
    intro z hz
    simp only [first_join,second_join,Φ.right_inv _ hz,join_projections]

private theorem productFlat_source (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target) :
    (productFlat U x Φ).source⊆(chartAt (ComplexModel (n+t)) (zeroBlockSection (t := t) U x)).target := by
  intro z hz
  apply (mem_chart_target (blockOpen U t) (zeroBlockSection (t := t) U x) z).mpr
  change tangentProjection n t z∈U
  exact (mem_chart_target U x _).mp (hΦsrc hz)

private theorem productFlat_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (v : ComplexModel n) :
    (productFlat U x Φ).toFun (tangentInclusion n t v)=tangentInclusion n t (Φ.toFun v) := by
  simp [productFlat,HironakaActualIntrinsicStableAmbientIso.join,tangentProjection_tangentInclusion]

private theorem join_plane_iff (a : ComplexModel n) (b : ComplexModel t) {k : ℕ} (hk : k≤n) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈complexCoordinatePlane (n+t) k ↔
      a∈complexCoordinatePlane n k ∧ b=0 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro i hi
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.castAdd t) hi
    · ext i
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.natAdd n) (by simp;omega)
  · rintro ⟨ha,hb⟩ i hi
    refine Fin.addCases (fun j hj => ?_) (fun j _hj => ?_) i hi
    · simpa [HironakaActualIntrinsicStableAmbientIso.join] using ha j hj
    · simp [HironakaActualIntrinsicStableAmbientIso.join,hb]

private theorem productFlat_carrier (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {A : Set U} {k : ℕ} (hk : k≤n)
    (hflat : ∀ {y : U},y∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y∈Φ.source →
      (y∈A ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈complexCoordinatePlane n k))
    {z : blockOpen U t} (hz : chartAt (ComplexModel (n+t)) (zeroBlockSection (t := t) U x) z∈(productFlat U x Φ).source) :
    z∈blockGraph (0 : U → ComplexModel t) A ↔ (productFlat U x Φ).toFun
      (chartAt (ComplexModel (n+t)) (zeroBlockSection (t := t) U x) z)∈complexCoordinatePlane (n+t) k := by
  have hΦ : chartAt (ComplexModel n) x (blockProjection z)∈Φ.source := by
    change tangentProjection n t z.val∈Φ.source
    change tangentProjection n t z.val∈Φ.source at hz
    exact hz
  have h := hflat (chart_source U x _) hΦ
  simp only [chart_apply] at h ⊢
  change (blockProjection z∈A ∧ actualJointNormalProjection n t z.val=0) ↔
    HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n t z.val))
      (actualJointNormalProjection n t z.val)∈complexCoordinatePlane (n+t) k
  rw [join_plane_iff _ _ hk]
  exact and_congr_left fun _ => h

private theorem regularAtDim_zeroBlockGraph_of {A : Set U} {z : blockOpen U t} {k : ℕ}
    (hz : z ∈ blockGraph (0 : U → ComplexModel t) A)
    (hReg : RegularAtDim (n := n) A (blockProjection z) k) :
    RegularAtDim (n := n+t) (blockGraph (0 : U → ComplexModel t) A) z k := by
  let x := blockProjection z
  have hx : x∈A := hz.1
  have hsec : zeroBlockSection (t := t) U x=z := by
    apply Subtype.ext
    change tangentInclusion n t (tangentProjection n t z.val)=z.val
    have hq : actualJointNormalProjection n t z.val=0 := hz.2
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero]
      using join_projections (n := n) (m := t) z.val
  obtain ⟨hkn,_hx,Φ,hsrc,h0,hflat⟩ := hReg
  have hreg : RegularAtDim (n := n+t) (blockGraph (0 : U → ComplexModel t) A) (zeroBlockSection (t := t) U x) k := by
    refine ⟨by omega,(zeroBlockSection_mem A x).mpr hx,productFlat U x Φ,
      productFlat_source U x Φ hsrc,?_,?_⟩
    · change (productFlat U x Φ).toFun (tangentInclusion n t x.val)=0
      rw [productFlat_section (t := t) U x Φ x.val]
      have hΦ0 : Φ.toFun x.val=0 := by simpa only [complexChartAt,chart_apply] using h0
      rw [hΦ0,map_zero]
    · intro y _hy hyΦ
      exact productFlat_carrier U x Φ hkn hflat hyΦ
  simpa only [hsec] using hreg

private theorem zeroBlockGraph_closed_submanifold {U : Opens (ComplexModel n)} {A : Set U}
    (hA : IsClosedSubmanifold n A) : IsClosedSubmanifold (n+t) (blockGraph (0 : U → ComplexModel t) A) := by
  refine ⟨(hA.1.preimage (blockProjection_contMDiff U t).continuous).inter
    (isClosed_eq ((actualJointNormalProjection n t).continuous.comp continuous_subtype_val) continuous_const),?_⟩
  intro z hz
  obtain ⟨k, hk⟩ := hA.2 (blockProjection z) hz.1
  exact ⟨k, regularAtDim_zeroBlockGraph_of hz hk⟩

/-- A finite holomorphic graph has the dimension of its source at each
point of the graph. -/
theorem regularAtDim_blockGraph_of {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    {A : Set U} {z : blockOpen U t} {k : ℕ} (hz : z ∈ blockGraph f A)
    (hReg : RegularAtDim (n := n) A (blockProjection z) k) :
    RegularAtDim (n := n+t) (blockGraph f A) z k := by
  let b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U := Diffeomorph.refl _ U ∞
  have hZero : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞
      (0 : U → ComplexModel t) := contMDiff_const
  let e := blockChartEquiv b hf hZero
  have hPre : e ⁻¹' blockGraph (0 : U → ComplexModel t) A = blockGraph f A := by
    change blockChartMap id f 0 ⁻¹' blockGraph (0 : U → ComplexModel t) A = blockGraph f A
    exact blockChartMap_preimage_graph id f 0 A
  have hz' : e z ∈ blockGraph (0 : U → ComplexModel t) A := by
    change z ∈ e ⁻¹' blockGraph (0 : U → ComplexModel t) A
    rwa [hPre]
  have hProj : blockProjection (e z) = blockProjection z :=
    blockProjection_chartMap id f 0 z
  have hReg' := regularAtDim_zeroBlockGraph_of hz' (hProj.symm ▸ hReg)
  rw [← hPre]
  exact (CodimOnePartCanonical.regularAtDim_preimage_iff e).mpr hReg'


/-- The actual graph of a finite holomorphic selector over a closed source
submanifold is a closed submanifold of the enlarged open. -/
theorem blockGraph_closed_submanifold {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    {A : Set U} (hA : IsClosedSubmanifold n A) :
    IsClosedSubmanifold (n + t) (blockGraph f A) := by
  let b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U := Diffeomorph.refl _ U ∞
  have hz : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞
      (0 : U → ComplexModel t) := contMDiff_const
  let e := blockChartEquiv b hf hz
  have hPre : e ⁻¹' blockGraph (0 : U → ComplexModel t) A = blockGraph f A := by
    change blockChartMap id f 0 ⁻¹' blockGraph (0 : U → ComplexModel t) A = blockGraph f A
    exact blockChartMap_preimage_graph id f 0 A
  rw [← hPre]
  exact MarkedIdealBiholomorphism.isClosedSubmanifold_preimage e.contMDiff e.symm.contMDiff
    e.apply_symm_apply e.symm_apply_apply (zeroBlockGraph_closed_submanifold hA)

/-- The graph record has the source's invariant-domain bound. The entire
ordered boundary on the larger ambient must be SNC and transverse to
the graph; the carrier dimension and nonvanishing follow from the source. -/
theorem blockMarked_isInvDomain {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    {k : ℕ} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (F : List (Set (blockOpen U t)))
    (hSNC : IsSNCDivisor (n+t) (blockMarked f Q F).E)
    (hTr : IsTransverse (n+t) (blockGraph f Q.N) (blockMarked f Q F).E) :
    IsInvDomain k (blockMarked f Q F) := by
  let G := blockMarked f Q F
  have hN := blockGraph_closed_submanifold hf hQ.isWellFormed.isClosedSubmanifold_N
  refine ⟨⟨hN, blockMarked_coherent hf hQ.isWellFormed.isCoherent F, hSNC, hTr⟩,
    ?_, hQ.one_le_d, ?_⟩
  · intro z hz
    obtain ⟨j, hj, hReg⟩ := hQ.dimLE (blockProjection z) hz.1
    exact ⟨j, hj, regularAtDim_blockGraph_of hf hz hReg⟩
  · intro z hz
    have hPre : blockSection f ⁻¹' G.N = Q.N := by
      ext x
      change (blockProjection (blockSection f x) ∈ Q.N ∧
        blockNormal (blockSection f x) = f (blockProjection (blockSection f x))) ↔ x ∈ Q.N
      simp only [blockProjection_blockSection, blockNormal_blockSection, and_true]
    have hTrace := blockSection_ideal_trace hf Q hQ.isWellFormed.isCoherent hQ.one_le_d F
    have hNonzero : IsNonzeroAlongAt (blockSection f ⁻¹' G.N)
        (GermIdeal.pullback (m := n) (blockSection f) G.ideal) (blockProjection z) := by
      change IsNonzeroAlongAt _ (GermIdeal.pullback (m := n) (blockSection f)
        (blockMarked f Q F).ideal) (blockProjection z)
      rw [hPre, hTrace]
      exact hQ.isNonzeroAlongAt _ hz.1
    have hsec : blockSection f (blockProjection z) = z := by
      apply Subtype.ext
      change join (blockProjection z).val (f (blockProjection z)) = z.val
      rw [← hz.2]
      exact join_projections z.val
    have hLift := HironakaOriginalContactRemainderSmoothNaturality.isNonzeroAlongAt_of_pullback
      (X := ambient U t) (Y := base U) (blockSection_contMDiff hf).continuous.continuousAt hNonzero
    rwa [hsec] at hLift

/-- The transported finite normal graph records have identical local tests and
stage cosupports, using the actual closed graph carrier. -/
theorem locWPEquiv_pullback_commonPower_blockMarked
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    {k l : ℕ} (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (e e' : ℕ)
    (hPow : RestrictEquiv (powerMarked (X := base U) P e)
      (MarkedIdeal.pullback (M := base V) (M' := base U) b (powerMarked (X := base V) Q e')))
    (F : List (Set (blockOpen V t))) :
    LocWPEquiv (X := ambient U t)
      (powerMarked (blockMarked f P (F.map (blockChartMap b f g ⁻¹' ·))) e)
      (MarkedIdeal.pullback (M := ambient V t) (M' := ambient U t) (blockChartMap b f g)
        (powerMarked (blockMarked g Q F) e')) :=
  locEquiv_of_restrictEquiv_closed (κ := Kinds.wp) rfl
    (restrictEquiv_pullback_commonPower_blockMarked b hf hg P Q hP hQ e e' hPow F)
    (blockGraph_closed_submanifold hf hP.isWellFormed.isClosedSubmanifold_N)
    (isCoherent_idealPow (blockMarked_coherent hf hP.isWellFormed.isCoherent _) e)
    (isCoherent_pullback (blockChartMap_contMDiff b.contMDiff hf hg)
      (isCoherent_idealPow (blockMarked_coherent hg hQ.isWellFormed.isCoherent F) e'))

end

end Hironaka.HironakaG1NormalGraphFlags
