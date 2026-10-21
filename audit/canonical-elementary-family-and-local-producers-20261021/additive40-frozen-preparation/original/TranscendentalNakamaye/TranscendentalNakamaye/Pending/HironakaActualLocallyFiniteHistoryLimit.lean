import TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteHistoryOverlap
import TranscendentalNakamaye.Pending.HironakaTerminalAtlasHolomorphic

/-!
# The genuine complex limit of one actual locally finite blowup history

The actual sequence and actual centre-image local finiteness internally
construct the overlap atlas, manifold, and proper holomorphic projection.
This does not assert general original noncompact scheduler existence.
Blueprint: `hironaka-actual-locally-finite-history-limit-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Classical Function IsManifold
open scoped Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits
universe u
namespace TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteHistoryLimit
noncomputable section
open FirstPass FirstPass.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq BlowupTowerIsoTail HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaTerminalAtlasTopology HironakaTerminalAtlasHolomorphic
variable {n : ℕ} {X : CMfd.{u} n}

def localMap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    ContinuousMap (localEndpoint s hLF x) X :=
  ⟨localProjection s hLF x,(localProjection_contMDiff s hLF x).continuous⟩

private theorem localMap_compatible (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (xy : X×X) :
    (actualHistoryGlueData s hLF).toGlueData.diagram.fst xy ≫ TopCat.ofHom (localMap s hLF xy.1)=
      (actualHistoryGlueData s hLF).toGlueData.diagram.snd xy ≫ TopCat.ofHom (localMap s hLF xy.2) := by
  rcases xy with ⟨x,y⟩
  ext z
  exact (transition_projection s hLF x y z).symm

/-- Actual quotient descent of the whole recorded finite projections. -/
def gluedProjection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    ContinuousMap (actualHistoryGluedSpace s hLF) X :=
  (Multicoequalizer.desc (actualHistoryGlueData s hLF).toGlueData.diagram (TopCat.of X)
    (fun x => TopCat.ofHom (localMap s hLF x)) (localMap_compatible s hLF)).hom

theorem gluedProjection_local (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X)
    (z : localEndpoint s hLF x) :
    gluedProjection s hLF (actualHistoryLocalInclusion s hLF x z)=localProjection s hLF x z := by
  have hh := Multicoequalizer.π_desc (actualHistoryGlueData s hLF).toGlueData.diagram (TopCat.of X)
    (fun x => TopCat.ofHom (localMap s hLF x)) (localMap_compatible s hLF) x
  exact congrArg (fun f : (actualHistoryGlueData s hLF).U x ⟶ TopCat.of X => f z) hh

theorem localInclusion_range (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    range (actualHistoryLocalInclusion s hLF x)=
      (gluedProjection s hLF) ⁻¹' (stableWindow s hLF x : Set X) := by
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x q)∈stableWindow s hLF x
    rw [gluedProjection_local]
    exact q.property
  · intro hz
    obtain ⟨y,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF y q)∈stableWindow s hLF x at hz
    rw [gluedProjection_local] at hz
    let zp : overlapOpen s hLF y x := ⟨q,hz⟩
    refine ⟨(transition s hLF y x zp).val,?_⟩
    have hc := (actualHistoryGlueData s hLF).toGlueData.glue_condition y x
    exact congrArg (fun f : (actualHistoryGlueData s hLF).V (y,x) ⟶
      (actualHistoryGlueData s hLF).glued => f zp) hc

private theorem embeddingOverlap_eq (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X) :
    actualEmbeddingOverlap (actualHistoryLocalInclusion s hLF x) (actualHistoryLocalInclusion s hLF y)
      (actualHistoryLocalInclusion_openEmbedding s hLF x)
      (actualHistoryLocalInclusion_openEmbedding s hLF y)=overlapOpen s hLF x y := by
  apply Opens.ext
  ext z
  change actualHistoryLocalInclusion s hLF x z∈range (actualHistoryLocalInclusion s hLF y) ↔
    localProjection s hLF x z∈stableWindow s hLF y
  rw [localInclusion_range]
  change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x z)∈stableWindow s hLF y ↔ _
  rw [gluedProjection_local]

private theorem transition_inclusion (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X)
    (z : overlapOpen s hLF x y) :
    actualHistoryLocalInclusion s hLF y (transition s hLF x y z).val=
      actualHistoryLocalInclusion s hLF x z.val := by
  have hc := (actualHistoryGlueData s hLF).toGlueData.glue_condition x y
  exact congrArg (fun f : (actualHistoryGlueData s hLF).V (x,y) ⟶
    (actualHistoryGlueData s hLF).glued => f z) hc

def embeddingTransition (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X) :
    CMfd.of (n := n) (actualEmbeddingOverlap (actualHistoryLocalInclusion s hLF x)
      (actualHistoryLocalInclusion s hLF y) (actualHistoryLocalInclusion_openEmbedding s hLF x)
      (actualHistoryLocalInclusion_openEmbedding s hLF y))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (actualEmbeddingOverlap (actualHistoryLocalInclusion s hLF y)
          (actualHistoryLocalInclusion s hLF x) (actualHistoryLocalInclusion_openEmbedding s hLF y)
          (actualHistoryLocalInclusion_openEmbedding s hLF x)) :=
  ((opensCongr (embeddingOverlap_eq s hLF x y)).trans (transition s hLF x y)).trans
    (opensCongr (embeddingOverlap_eq s hLF y x).symm)

theorem embeddingTransition_inclusion (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X)
    (z : actualEmbeddingOverlap (actualHistoryLocalInclusion s hLF x) (actualHistoryLocalInclusion s hLF y)
      (actualHistoryLocalInclusion_openEmbedding s hLF x) (actualHistoryLocalInclusion_openEmbedding s hLF y)) :
    actualHistoryLocalInclusion s hLF y (embeddingTransition s hLF x y z).val=
      actualHistoryLocalInclusion s hLF x z.val :=
  transition_inclusion s hLF x y (opensCongr (embeddingOverlap_eq s hLF x y) z)

private theorem base_cover (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    ∀ z : X,∃ x : X,z∈stableWindow s hLF x := fun x => ⟨x,point_mem_stableWindow s hLF x⟩

theorem limitSpace_t2 (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    T2Space (actualHistoryGluedSpace s hLF) :=
  t2Space_of_actual_saturated_projection_atlas (gluedProjection s hLF) (gluedProjection s hLF).continuous
    (stableWindow s hLF) (base_cover s hLF) (actualHistoryLocalInclusion s hLF)
    (actualHistoryLocalInclusion_openEmbedding s hLF) (localInclusion_range s hLF)

theorem limitSpace_secondCountable (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    SecondCountableTopology (actualHistoryGluedSpace s hLF) :=
  secondCountable_of_actual_saturated_projection_atlas (gluedProjection s hLF)
    (stableWindow s hLF) (base_cover s hLF) (actualHistoryLocalInclusion s hLF)
    (actualHistoryLocalInclusion_openEmbedding s hLF) (localInclusion_range s hLF)

@[instance_reducible]
def limitChartedSpace (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    ChartedSpace (ComplexModel n) (actualHistoryGluedSpace s hLF) :=
  actualLiftedTerminalChartedSpace n (actualHistoryLocalInclusion s hLF)
    (actualHistoryLocalInclusion_openEmbedding s hLF)
    (actualHistoryLocalInclusion_jointly_surjective s hLF)

attribute [local instance] limitChartedSpace

theorem limitSpace_isComplexManifold (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    letI := limitChartedSpace s hLF
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := by
  let := limitChartedSpace s hLF
  have : T2Space (actualHistoryGluedSpace s hLF) := limitSpace_t2 s hLF
  have : SecondCountableTopology (actualHistoryGluedSpace s hLF) := limitSpace_secondCountable s hLF
  have : IsManifold 𝓘(ℂ,ComplexModel n) ∞ (actualHistoryGluedSpace s hLF) :=
    actualLiftedTerminalChartedSpace_isManifold (actualHistoryLocalInclusion s hLF)
      (actualHistoryLocalInclusion_openEmbedding s hLF)
      (actualHistoryLocalInclusion_jointly_surjective s hLF)
      (embeddingTransition s hLF) (embeddingTransition_inclusion s hLF)
  exact {}

/-- The actual topology and charts, with all manifold axioms proved. -/
def limitManifold (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) : CMfd.{u} n :=
  letI := limitChartedSpace s hLF
  letI := limitSpace_isComplexManifold s hLF
  CMfd.of (actualHistoryGluedSpace s hLF)

theorem localInclusion_contMDiff (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (actualHistoryLocalInclusion s hLF x : localEndpoint s hLF x → limitManifold s hLF) :=
  actualLiftedTerminal_local_inclusion_contMDiff (actualHistoryLocalInclusion s hLF)
    (actualHistoryLocalInclusion_openEmbedding s hLF)
    (actualHistoryLocalInclusion_jointly_surjective s hLF)
    (embeddingTransition s hLF) (embeddingTransition_inclusion s hLF) x

theorem gluedProjection_contMDiff (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (gluedProjection s hLF : limitManifold s hLF → X) := by
  intro z
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  let e := chartAt (ComplexModel n) q
  let c := e.lift_openEmbedding (actualHistoryLocalInclusion_openEmbedding s hLF x)
  have hc : c∈atlas (ComplexModel n) (limitManifold s hLF) :=
    ⟨x,e,chart_mem_atlas (ComplexModel n) q,rfl⟩
  have hq : q∈e.source := mem_chart_source (ComplexModel n) q
  have hz : actualHistoryLocalInclusion s hLF x q∈c.source := ⟨q,hq,rfl⟩
  have heMax : e∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (localEndpoint s hLF x) := chart_mem_maximalAtlas q
  have hcMax : c∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (limitManifold s hLF) := subset_maximalAtlas hc
  have hcx : c (actualHistoryLocalInclusion s hLF x q)=e q :=
    e.lift_openEmbedding_apply (actualHistoryLocalInclusion_openEmbedding s hLF x)
  have hsinv : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm
      (c (actualHistoryLocalInclusion s hLF x q)) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx];exact e.map_source hq)
  have hh := ((localProjection_contMDiff s hLF x).contMDiffAt.comp _ hsinv).comp _
    (contMDiffAt_of_mem_maximalAtlas hcMax hz)
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with y hy
  obtain ⟨b,hb,rfl⟩ := hy
  change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x b)=
    localProjection s hLF x (e.symm (c (actualHistoryLocalInclusion s hLF x b)))
  rw [gluedProjection_local,e.lift_openEmbedding_apply,e.left_inv hb]

theorem gluedProjection_fibre (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    (gluedProjection s hLF) ⁻¹' ({x} : Set X)=actualHistoryLocalInclusion s hLF x ''
      ((restrict (stableWindow s hLF x) (s.stage (stableIndex s hLF x)).2).proj ⁻¹'
        {⟨x,point_mem_stableWindow s hLF x⟩}) := by
  ext z
  constructor
  · intro hz
    have hp : gluedProjection s hLF z=x := hz
    have hr : z∈range (actualHistoryLocalInclusion s hLF x) := by
      rw [localInclusion_range]
      change gluedProjection s hLF z∈stableWindow s hLF x
      rw [hp]
      exact point_mem_stableWindow s hLF x
    obtain ⟨q,rfl⟩ := hr
    refine ⟨q,?_,rfl⟩
    change (restrict (stableWindow s hLF x) (s.stage (stableIndex s hLF x)).2).proj q=⟨x,_⟩
    apply Subtype.ext
    rw [proj_restrict]
    exact (gluedProjection_local s hLF x q).symm.trans hp
  · rintro ⟨q,hq,rfl⟩
    have hq' : (restrict (stableWindow s hLF x) (s.stage (stableIndex s hLF x)).2).proj q=⟨x,_⟩ := hq
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x q)=x
    rw [gluedProjection_local]
    have hh := congrArg Subtype.val hq'
    rw [proj_restrict] at hh
    exact hh

private theorem gluedProjection_fibre_isCompact (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (x : X) :
    IsCompact ((gluedProjection s hLF) ⁻¹' ({x} : Set X)) := by
  rw [gluedProjection_fibre s hLF]
  exact ((localPrefixProjection_isProperMap s hLF x).isCompact_preimage isCompact_singleton).image
    (actualHistoryLocalInclusion_openEmbedding s hLF x).continuous

theorem gluedProjection_isClosedMap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsClosedMap (gluedProjection s hLF) := by
  intro C hC
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let Γ := actualHistoryLocalInclusion s hLF x
  let u : stableWindow s hLF x := ⟨x,point_mem_stableWindow s hLF x⟩
  let T := restrict (stableWindow s hLF x) (s.stage (stableIndex s hLF x)).2
  let B : Set (localEndpoint s hLF x) := Γ ⁻¹' C
  have hB : IsClosed B := hC.preimage (actualHistoryLocalInclusion_openEmbedding s hLF x).continuous
  have hcl : IsClosed (T.proj '' B) := (localPrefixProjection_isProperMap s hLF x).isClosedMap B hB
  let V : Set (stableWindow s hLF x) := (T.proj '' B)ᶜ
  have hV : IsOpen V := hcl.isOpen_compl
  have hu : u∈V := by
    rintro ⟨q,hq,hyp⟩
    apply hx
    refine ⟨Γ q,hq,?_⟩
    have hh := congrArg Subtype.val hyp
    rw [proj_restrict] at hh
    exact (gluedProjection_local s hLF x q).trans hh
  refine ⟨Subtype.val '' V,?_,?_,⟨u,hu,rfl⟩⟩
  · rintro z ⟨v,hv,rfl⟩ hz
    obtain ⟨q,hq,hpq⟩ := hz
    have hr : q∈range Γ := by
      change q∈range (actualHistoryLocalInclusion s hLF x)
      rw [localInclusion_range]
      change gluedProjection s hLF q∈stableWindow s hLF x
      rw [hpq]
      exact v.property
    obtain ⟨b,hΓb⟩ := hr
    apply hv
    refine ⟨b,?_,?_⟩
    · change Γ b∈C
      rw [hΓb]
      exact hq
    · apply Subtype.ext
      rw [proj_restrict]
      have hlocal := gluedProjection_local s hLF x b
      exact hlocal.symm.trans ((congrArg (gluedProjection s hLF) hΓb).trans hpq)
  · exact (stableWindow s hLF x).isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hV

theorem gluedProjection_isProperMap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsProperMap (gluedProjection s hLF) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(gluedProjection s hLF).continuous,gluedProjection_isClosedMap s hLF,
      gluedProjection_fibre_isCompact s hLF⟩

end
end TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteHistoryLimit
