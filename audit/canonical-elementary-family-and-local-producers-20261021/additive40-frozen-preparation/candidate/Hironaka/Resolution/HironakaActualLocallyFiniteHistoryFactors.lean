/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualLocallyFiniteHistoryLimit
import Hironaka.Resolution.HironakaActualTowerLiftUniqueness

/-!
# Actual finite-stage factors of one locally finite blowup history

All arrows are constructed from the same actual history. No desired factor
map, stagewise square or compatibility certificate is a premise.
Blueprint: `hironaka-actual-locally-finite-history-factors-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Classical Function IsManifold
open scoped Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits
universe u
namespace Hironaka.HironakaActualLocallyFiniteHistoryFactors
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq BlowupTowerIsoTail BlowupRestrictOpen HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryComparison HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualTowerLiftUniqueness
  HironakaOriginalTerminalProjectionUniqueness
variable {n : ℕ} {X : CMfd.{u} n}
attribute [local instance] limitChartedSpace

/-- Whole lift uniqueness for the actual restricted recorded continuation. -/
theorem restricted_lift_unique (s : GrowingSeq X) (U : Opens X) (k r : ℕ)
    (f g : CMfd.of (n := n) (openPreimage (s.stage (k+r)).2 U) →
      CMfd.of (n := n) (openPreimage (s.stage k).2 U))
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hpf : ∀ z,(restrict U (s.stage k).2).proj (f z)=(restrict U (s.stage (k+r)).2).proj z)
    (hpg : ∀ z,(restrict U (s.stage k).2).proj (g z)=(restrict U (s.stage (k+r)).2).proj z) : f=g := by
  let T := restrict U (s.stage k).2
  let W := openPreimage (s.stage k).2 U
  let R := restrict W (tailTower s k r)
  have hOpen : openPreimage (tailTower s k r) W=openPreimage (s.stage (k+r)).2 U := by
    rw [openPreimage_append,append_tailTower]
  let e := opensCongr (n := n) hOpen
  have he (z : openPreimage (tailTower s k r) W) :
      (T.append R).proj z=(restrict U (s.stage (k+r)).2).proj (e z) := by
    apply Subtype.ext
    have heval : (e z).val=z.val := rfl
    simp only [BlowupTower.proj_append,Function.comp_apply,T,R,proj_restrict]
    rw [heval]
    simpa only [BlowupTower.proj_append,Function.comp_apply] using
      congrArg (fun Q : BlowupTower X (s.stage (k+r)).1 => Q.proj z.val) (append_tailTower s k r)
  have hf' : f ∘ e=R.proj := actual_lift_unique T R (f ∘ e) (hf.comp e.contMDiff)
    (fun z => (hpf (e z)).trans (he z).symm)
  have hg' : g ∘ e=R.proj := actual_lift_unique T R (g ∘ e) (hg.comp e.contMDiff)
    (fun z => (hpg (e z)).trans (he z).symm)
  funext z
  have hh := congrFun (hf'.trans hg'.symm) (e.symm z)
  simpa only [Function.comp_apply,e.apply_symm_apply] using hh

private theorem lift_unique_to_global_stage (s : GrowingSeq X) (U : Opens X) (k r : ℕ)
    (f g : CMfd.of (n := n) (openPreimage (s.stage (k+r)).2 U) → (s.stage k).1)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hpf : ∀ z,(s.stage k).2.proj (f z)=(s.stage (k+r)).2.proj z.val)
    (hpg : ∀ z,(s.stage k).2.proj (g z)=(s.stage (k+r)).2.proj z.val) : f=g := by
  have hmf (z : openPreimage (s.stage (k+r)).2 U) : f z∈openPreimage (s.stage k).2 U := by
    change (s.stage k).2.proj (f z)∈U
    rw [hpf]
    exact z.property
  have hmg (z : openPreimage (s.stage (k+r)).2 U) : g z∈openPreimage (s.stage k).2 U := by
    change (s.stage k).2.proj (g z)∈U
    rw [hpg]
    exact z.property
  have hh := restricted_lift_unique s U k r (fun z => ⟨f z,hmf z⟩) (fun z => ⟨g z,hmg z⟩)
    (contMDiff_opens_mk hf _) (contMDiff_opens_mk hg _)
    (fun z => Subtype.ext (by rw [proj_restrict,proj_restrict];exact hpf z))
    (fun z => Subtype.ext (by rw [proj_restrict,proj_restrict];exact hpg z))
  exact funext fun z => congrArg Subtype.val (congrFun hh z)

private def advance (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) (x : X) :=
  latePrefixComparison s (stableWindow s hLF x) (stableIndex s hLF x)
    (stableWindow_avoids s hLF x) (k+stableIndex s hLF x) (stableIndex s hLF x)
    (by omega) le_rfl

/-- Actual later endpoint followed by the actual recorded finite tail. -/
def localFactor (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) (x : X) :
    localEndpoint s hLF x → (s.stage k).1 :=
  fun z => (tailTower s k (stableIndex s hLF x)).proj (advance s hLF k x z).val

theorem localFactor_contMDiff (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) (x : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localFactor s hLF k x) :=
  (tailTower s k (stableIndex s hLF x)).contMDiff_proj.comp
    (contMDiff_subtype_val.comp (advance s hLF k x).contMDiff)

theorem localFactor_projection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) (x : X)
    (z : localEndpoint s hLF x) :
    (s.stage k).2.proj (localFactor s hLF k x z)=localProjection s hLF x z := by
  have he := congrArg Subtype.val (latePrefixComparison_proj s (stableWindow s hLF x)
    (stableIndex s hLF x) (stableWindow_avoids s hLF x)
    (k+stableIndex s hLF x) (stableIndex s hLF x) (by omega) le_rfl z)
  rw [proj_restrict,proj_restrict] at he
  have ht := congrArg (fun Q : BlowupTower X (s.stage (k+stableIndex s hLF x)).1 =>
    Q.proj (advance s hLF k x z).val) (append_tailTower s k (stableIndex s hLF x))
  rw [BlowupTower.proj_append,Function.comp_apply] at ht
  exact ht.trans he

/-- The already chosen whole transitions preserve the constructed local factors. -/
theorem localFactor_transition (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ)
    (x y : X) (z : overlapOpen s hLF x y) :
    localFactor s hLF k y (transition s hLF x y z).val=localFactor s hLF k x z.val := by
  let U := stableWindow s hLF x ⊓ stableWindow s hLF y
  let Nx := stableIndex s hLF x
  let Ny := stableIndex s hLF y
  let J := k+(Nx+Ny)
  have hx : ∀ i,Nx ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)) :=
    fun i hi => (stableWindow_avoids s hLF x i hi).mono_right (Set.preimage_mono inf_le_left)
  have hy : ∀ i,Ny ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)) :=
    fun i hi => (stableWindow_avoids s hLF y i hi).mono_right (Set.preimage_mono inf_le_right)
  have hNx : Nx ≤ J := by dsimp [J];omega
  have hNy : Ny ≤ J := by dsimp [J];omega
  let ex := latePrefixComparison s U Nx hx Nx J le_rfl hNx
  let ey := latePrefixComparison s U Ny hy Ny J le_rfl hNy
  have hpx (q : openPreimage (s.stage J).2 U) :
      (restrict U (s.stage Nx).2).proj (ex q)=(restrict U (s.stage J).2).proj q :=
    latePrefixComparison_proj s U Nx hx Nx J le_rfl hNx q
  have hpy (q : openPreimage (s.stage J).2 U) :
      (restrict U (s.stage Ny).2).proj (ey q)=(restrict U (s.stage J).2).proj q :=
    latePrefixComparison_proj s U Ny hy Ny J le_rfl hNy q
  let ax : CMfd.of (n := n) (openPreimage (s.stage J).2 U) → localEndpoint s hLF x :=
    fun q => ⟨(ex q).val,(ex q).property.1⟩
  let ay : CMfd.of (n := n) (openPreimage (s.stage J).2 U) → localEndpoint s hLF y :=
    fun q => ⟨(ey q).val,(ey q).property.2⟩
  have hax : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ax := by
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun q => (⟨(ex q).val,(ex q).property.1⟩ : openPreimage (s.stage Nx).2 (stableWindow s hLF x)))
    exact contMDiff_opens_mk (V := openPreimage (s.stage Nx).2 (stableWindow s hLF x))
      (contMDiff_subtype_val.comp ex.contMDiff) _
  have hay : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ay := by
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun q => (⟨(ey q).val,(ey q).property.2⟩ : openPreimage (s.stage Ny).2 (stableWindow s hLF y)))
    exact contMDiff_opens_mk (V := openPreimage (s.stage Ny).2 (stableWindow s hLF y))
      (contMDiff_subtype_val.comp ey.contMDiff) _
  have haxp (q : openPreimage (s.stage J).2 U) :
      localProjection s hLF x (ax q)=(s.stage J).2.proj q.val := by
    have hh := congrArg Subtype.val (hpx q)
    rw [proj_restrict,proj_restrict] at hh
    exact hh
  have hayp (q : openPreimage (s.stage J).2 U) :
      localProjection s hLF y (ay q)=(s.stage J).2.proj q.val := by
    have hh := congrArg Subtype.val (hpy q)
    rw [proj_restrict,proj_restrict] at hh
    exact hh
  have hfg := lift_unique_to_global_stage s U k (Nx+Ny)
    (localFactor s hLF k x ∘ ax) (localFactor s hLF k y ∘ ay)
    ((localFactor_contMDiff s hLF k x).comp hax) ((localFactor_contMDiff s hLF k y).comp hay)
    (fun q => (localFactor_projection s hLF k x (ax q)).trans (haxp q))
    (fun q => (localFactor_projection s hLF k y (ay q)).trans (hayp q))
  have hmin : ∀ i,min Nx Ny ≤ i →
      Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)) := by
    intro i hi
    rcases le_total Nx Ny with h | h
    · rw [min_eq_left h] at hi
      exact hx i hi
    · rw [min_eq_right h] at hi
      exact hy i hi
  let ep := latePrefixComparison s U (min Nx Ny) hmin Ny Nx (min_le_right _ _) (min_le_left _ _)
  have hcomp : ex.symm.trans ey=ep := by
    apply biholomorphisms_eq_of_actual_proj_eq (restrict U (s.stage Ny).2)
    intro q
    have hh := hpx (ex.symm q)
    rw [ex.apply_symm_apply] at hh
    exact (hpy (ex.symm q)).trans (hh.symm.trans
      (latePrefixComparison_proj s U (min Nx Ny) hmin Ny Nx (min_le_right _ _) (min_le_left _ _) q).symm)
  let zp : openPreimage (s.stage Nx).2 U := ⟨z.val.val,⟨z.val.property,z.property⟩⟩
  let q := ex.symm zp
  have haxq : ax q=z.val := by
    apply Subtype.ext
    exact congrArg (fun q : openPreimage (s.stage Nx).2 U => q.val) (ex.apply_symm_apply zp)
  have hayq : ay q=(transition s hLF x y z).val := by
    apply Subtype.ext
    have hh := congrArg (fun e => (e zp).val) hcomp
    exact hh
  have hh := congrFun hfg q
  change localFactor s hLF k x (ax q)=localFactor s hLF k y (ay q) at hh
  rw [haxq,hayq] at hh
  exact hh.symm

private def localFactorMap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) (x : X) :
    ContinuousMap (localEndpoint s hLF x) (s.stage k).1 :=
  ⟨localFactor s hLF k x,(localFactor_contMDiff s hLF k x).continuous⟩

private theorem localFactor_compatible (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (k : ℕ) (xy : X×X) :
    (actualHistoryGlueData s hLF).toGlueData.diagram.fst xy ≫ TopCat.ofHom (localFactorMap s hLF k xy.1)=
      (actualHistoryGlueData s hLF).toGlueData.diagram.snd xy ≫ TopCat.ofHom (localFactorMap s hLF k xy.2) := by
  rcases xy with ⟨x,y⟩
  ext z
  exact (localFactor_transition s hLF k x y z).symm

/-- The genuine quotient universal property constructs every finite-stage arrow. -/
def stageFactor (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) :
    ContinuousMap (limitManifold s hLF) (s.stage k).1 :=
  (Multicoequalizer.desc (actualHistoryGlueData s hLF).toGlueData.diagram (TopCat.of (s.stage k).1)
    (fun x => TopCat.ofHom (localFactorMap s hLF k x)) (localFactor_compatible s hLF k)).hom

theorem stageFactor_local (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) (x : X)
    (z : localEndpoint s hLF x) :
    stageFactor s hLF k (actualHistoryLocalInclusion s hLF x z)=localFactor s hLF k x z := by
  have hh := Multicoequalizer.π_desc (actualHistoryGlueData s hLF).toGlueData.diagram (TopCat.of (s.stage k).1)
    (fun x => TopCat.ofHom (localFactorMap s hLF k x)) (localFactor_compatible s hLF k) x
  exact congrArg (fun f : (actualHistoryGlueData s hLF).U x ⟶ TopCat.of (s.stage k).1 => f z) hh

theorem stageFactor_contMDiff (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (stageFactor s hLF k) := by
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
  have hh := ((localFactor_contMDiff s hLF k x).contMDiffAt.comp _ hsinv).comp _
    (contMDiffAt_of_mem_maximalAtlas hcMax hz)
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with y hy
  obtain ⟨b,hb,rfl⟩ := hy
  change stageFactor s hLF k (actualHistoryLocalInclusion s hLF x b)=
    localFactor s hLF k x (e.symm (c (actualHistoryLocalInclusion s hLF x b)))
  rw [stageFactor_local,e.lift_openEmbedding_apply,e.left_inv hb]

theorem stageFactor_projection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ)
    (z : limitManifold s hLF) :
    (s.stage k).2.proj (stageFactor s hLF k z)=gluedProjection s hLF z := by
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  rw [stageFactor_local,gluedProjection_local]
  exact localFactor_projection s hLF k x q

theorem stageFactor_isProperMap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) :
    IsProperMap (stageFactor s hLF k) := by
  apply isProperMap_of_comp_of_t2 (stageFactor s hLF k).continuous (s.stage k).2.contMDiff_proj.continuous
  have hh : (s.stage k).2.proj ∘ stageFactor s hLF k=gluedProjection s hLF :=
    funext fun z => stageFactor_projection s hLF k z
  rw [hh]
  exact gluedProjection_isProperMap s hLF

theorem stageFactor_surjective (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) :
    Surjective (stageFactor s hLF k) := by
  intro a
  let x := (s.stage k).2.proj a
  let N := stableIndex s hLF x
  obtain ⟨b,hb⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective
    (tailTower s k N).isBlowupSequence a
  have hbx : (s.stage (k+N)).2.proj b=x := by
    have hh := congrArg (fun Q : BlowupTower X (s.stage (k+N)).1 => Q.proj b) (append_tailTower s k N)
    rw [BlowupTower.proj_append,Function.comp_apply] at hh
    exact hh.symm.trans (congrArg (s.stage k).2.proj hb)
  let bp : openPreimage (s.stage (k+N)).2 (stableWindow s hLF x) :=
    ⟨b,by change (s.stage (k+N)).2.proj b∈stableWindow s hLF x
          rw [hbx];exact point_mem_stableWindow s hLF x⟩
  refine ⟨actualHistoryLocalInclusion s hLF x ((advance s hLF k x).symm bp),?_⟩
  rw [stageFactor_local]
  change (tailTower s k N).proj (advance s hLF k x ((advance s hLF k x).symm bp)).val=a
  rw [(advance s hLF k x).apply_symm_apply]
  exact hb

theorem stageFactor_unique (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ)
    (f : limitManifold s hLF → (s.stage k).1)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hp : ∀ z,(s.stage k).2.proj (f z)=gluedProjection s hLF z) : f=stageFactor s hLF k := by
  have hlocal (x : X) (z : localEndpoint s hLF x) :
      f (actualHistoryLocalInclusion s hLF x z)=localFactor s hLF k x z := by
    let e := advance s hLF k x
    have he (q : openPreimage (s.stage (k+stableIndex s hLF x)).2 (stableWindow s hLF x)) :
        localProjection s hLF x (e.symm q)=(s.stage (k+stableIndex s hLF x)).2.proj q.val := by
      have hh := congrArg Subtype.val (latePrefixComparison_proj s (stableWindow s hLF x)
        (stableIndex s hLF x) (stableWindow_avoids s hLF x)
        (k+stableIndex s hLF x) (stableIndex s hLF x) (by omega) le_rfl (e.symm q))
      rw [proj_restrict,proj_restrict] at hh
      change (s.stage (k+stableIndex s hLF x)).2.proj (e (e.symm q)).val=
        localProjection s hLF x (e.symm q) at hh
      rw [e.apply_symm_apply] at hh
      exact hh.symm
    have hh := lift_unique_to_global_stage s (stableWindow s hLF x) k (stableIndex s hLF x)
      (f ∘ actualHistoryLocalInclusion s hLF x ∘ e.symm) (localFactor s hLF k x ∘ e.symm)
      ((hf.comp (localInclusion_contMDiff s hLF x)).comp e.symm.contMDiff)
      ((localFactor_contMDiff s hLF k x).comp e.symm.contMDiff)
      (fun q => (hp _).trans ((gluedProjection_local s hLF x (e.symm q)).trans (he q)))
      (fun q => (localFactor_projection s hLF k x (e.symm q)).trans (he q))
    have hq := congrFun hh (e z)
    change f (actualHistoryLocalInclusion s hLF x (e.symm (e z)))=
      localFactor s hLF k x (e.symm (e z)) at hq
    rw [e.symm_apply_apply] at hq
    exact hq
  funext z
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  rw [stageFactor_local]
  exact hlocal x q

/-- Literal compatibility with every recorded actual finite tail projection. -/
theorem stageFactor_tail (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k r : ℕ) :
    (tailTower s k r).proj ∘ stageFactor s hLF (k+r)=stageFactor s hLF k := by
  apply stageFactor_unique s hLF k
    ((tailTower s k r).proj ∘ stageFactor s hLF (k+r))
    ((tailTower s k r).contMDiff_proj.comp (stageFactor_contMDiff s hLF (k+r)))
  intro z
  have hh := congrArg (fun Q : BlowupTower X (s.stage (k+r)).1 =>
    Q.proj (stageFactor s hLF (k+r) z)) (append_tailTower s k r)
  simpa only [BlowupTower.proj_append,Function.comp_apply] using hh.trans (stageFactor_projection s hLF (k+r) z)

end
end Hironaka.HironakaActualLocallyFiniteHistoryFactors
