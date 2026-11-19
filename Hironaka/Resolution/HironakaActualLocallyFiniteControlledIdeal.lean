import Hironaka.Resolution.HironakaActualLocallyFiniteCarrierTransverse
import Hironaka.Resolution.HironakaSharpActualCurveOffCentreOrders
import Hironaka.Resolution.HironakaActualNoncanonicalAnalyticTransformLocality

/-!
# The genuine coherent controlled ideal of one actual locally finite history

The independently defined union uses the SAME actual finite-prefix ideals and
constructed limit factors. Actual empty tails prove its whole normalized-prefix
stabilization and coherence, including off-carrier germs. Original analytic
carrier and coherent ideal suffice; no test/CAN history, desired limit ideal,
atlas or stabilization certificate is supplied. A resolving scheduler is not
constructed by this consumer of a genuine locally finite history.
Blueprint: `hironaka-actual-locally-finite-controlled-ideal-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualLocallyFiniteControlledIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaActualLocallyFiniteHistoryComparison HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryFactors
  HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLocallyFiniteBoundary HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq
  HironakaActualLocallyFiniteCarrierTransverse HomogenizedGlueingTower
  RelativePrincipalizationSpan GermIdealPullbackCalculus RestrictedIdealExtension
  RestrictedIdealWeight RestrictedIdealQuotient InvertibleIdealQuotient
  MarkedIdealOperationsAlong ContactCanonicalAlong MonomialPartEtale
  HironakaSharpActualCurveOffCentreOrders GermIdealTotalTransform
variable {n : ℕ} {X Y Z : CMfd.{u} n}
attribute [local instance] limitChartedSpace

private theorem pullback_le_geo (M : MarkedIdeal n X) (C : Set X) (π : Y → X) :
    (GermIdeal.pullback (m := n) π M.ideal).Le (M.geoTransform C π).ideal := by
  intro y g hg
  exact CoefficientIdealAlongRestrictionFull.mem_geoTransform_of_mem_pullback M hg

/-- The independently defined union uses actual prefix ideals and actual finite-stage factors. -/
def limitControlledIdeal (M : MarkedIdeal n X) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) : GermIdeal n (limitManifold s hLF) where
  mem z g := ∃ j : ℕ,(GermIdeal.pullback (m := n) (stageFactor s hLF j)
    (geoTransformAlong M (s.stage j).2).ideal).mem z g

private theorem restrictOn_idempotent (N : Set X) (I : GermIdeal n X) :
    restrictOn n N (restrictOn n N I)=restrictOn n N I := by
  ext x g
  constructor
  · rintro ⟨hg,hspan⟩
    exact ⟨hg,IsInSpanOnAt.trans (fun s hs => hs.2) hspan⟩
  · intro hg
    exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩

private theorem pullback_restrictOn_empty (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent) {π : Y → X} (hπ : IsBlowupAlong n (∅ : Set X) π) :
    GermIdeal.pullback (m := n) π (restrictOn n M.N M.ideal)=
      restrictOn n (π ⁻¹' M.N) (GermIdeal.pullback (m := n) π M.ideal) := by
  have hc := isCoherent_restrictOn hI (CartanIrreducible.cartanCoherence _ hN)
  ext y g
  obtain ⟨ψ,hψ⟩ := exists_isLocalInverseAt_of_isBlowupAlong_empty hπ y
  exact (mem_pullback_iff_of_local hc hψ).trans
    (mem_restrictOn_pullback_iff_of_local hI hψ).symm

private theorem ideal_geoTransform_empty (M : MarkedIdeal n X) (hN : IsComplexAnalyticSubset (n:=n) M.N)
    (hI : M.ideal.IsCoherent) {π : Y → X} (hπ : IsBlowupAlong n (∅ : Set X) π) :
    (M.geoTransform ∅ π).ideal=GermIdeal.pullback (m := n) π (restrictOn n M.N M.ideal) := by
  rw [pullback_restrictOn_empty M hN hI hπ]
  ext y g
  have hh := actual_controlled_germ_iff_normalized_raw_off_centre M hπ (z:=y) (notMem_empty _) g
  rw [geoTransform_N,geoStrictTransform_empty hπ.contMDiff.continuous hN.isClosed] at hh
  exact hh

private theorem pullback_le_geoAlong (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (GermIdeal.pullback (m:=n) T.proj M.ideal).Le (geoTransformAlong M T).ideal
  | _,.refl => by
    rw [BlowupTower.proj_refl,BlowupControlledTransform.pullback_id hI]
    exact fun _ _ h => h
  | _,.step T C π hπ => by
    rw [BlowupTower.proj_step,pullback_comp T.contMDiff_proj hπ.contMDiff hI]
    intro y g hg
    exact pullback_le_geo (geoTransformAlong M T) C π y g
      (pullback_le_pullback (f:=π) (pullback_le_geoAlong M hI T) y g hg)

/-- All actual finite-prefix pullbacks form an increasing family on the same limit manifold. -/
theorem prefix_pullback_monotone (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) {j k : ℕ} (hjk : j≤k) :
    (GermIdeal.pullback (m:=n) (stageFactor s hLF j) (geoTransformAlong M (s.stage j).2).ideal).Le
      (GermIdeal.pullback (m:=n) (stageFactor s hLF k) (geoTransformAlong M (s.stage k).2).ideal) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hjk
  let A:=geoTransformAlong M (s.stage j).2
  let R:=tailTower s j r
  have hcA : A.ideal.IsCoherent :=
    (HironakaActualNoncanonicalAnalyticTransformLocality.analytic_and_coherent_geoTransformAlong M hN hI (s.stage j).2).2
  rw [←stageFactor_tail s hLF j r,pullback_comp R.contMDiff_proj (stageFactor_contMDiff s hLF (j+r)) hcA]
  have ha : geoTransformAlong A R=geoTransformAlong M (s.stage (j+r)).2 := by
    rw [←geoTransformAlong_append,append_tailTower]
  have hinc:=pullback_le_pullback (m:=n) (f:=stageFactor s hLF (j+r)) (pullback_le_geoAlong A hcA R)
  rw [ha] at hinc
  exact hinc
private theorem normalized_ideal_empty (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent)
    {π : Y → X} (hπ : IsBlowupAlong n (∅ : Set X) π) :
    restrictOn n (M.geoTransform ∅ π).N (M.geoTransform ∅ π).ideal=(M.geoTransform ∅ π).ideal := by
  rw [ideal_geoTransform_empty M hN hI hπ,geoTransform_N,geoStrictTransform_empty hπ.contMDiff.continuous hN.isClosed]
  let A : MarkedIdeal n X:={M with ideal:=restrictOn n M.N M.ideal}
  have hcA : A.ideal.IsCoherent:=isCoherent_restrictOn hI (CartanIrreducible.cartanCoherence _ hN)
  have hh:=pullback_restrictOn_empty A hN hcA hπ
  change GermIdeal.pullback (m:=n) π (restrictOn n M.N (restrictOn n M.N M.ideal))=
    restrictOn n (π ⁻¹' M.N) (GermIdeal.pullback (m:=n) π (restrictOn n M.N M.ideal)) at hh
  rw [restrictOn_idempotent] at hh
  exact hh.symm

/-- The entire normalized ideal pulls back along every actual empty tail. -/
theorem normalized_ideal_empty_tower (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),ResolutionInvariantExt.IsEmptyTower T →
      restrictOn n (geoTransformAlong M T).N (geoTransformAlong M T).ideal=
        GermIdeal.pullback (m:=n) T.proj (restrictOn n M.N M.ideal)
  | _,.refl,_ => by
    rw [BlowupTower.proj_refl,BlowupControlledTransform.pullback_id
      (isCoherent_restrictOn hI (CartanIrreducible.cartanCoherence _ hN))]
    rfl
  | _,.step T C π hπ,hEmpty => by
    rcases hEmpty with ⟨hEmpty,rfl⟩
    obtain ⟨hNT,hIT⟩:=HironakaActualNoncanonicalAnalyticTransformLocality.analytic_and_coherent_geoTransformAlong M hN hI T
    rw [geoTransformAlong_step,normalized_ideal_empty (geoTransformAlong M T) hNT hIT hπ,
      ideal_geoTransform_empty (geoTransformAlong M T) hNT hIT hπ,
      normalized_ideal_empty_tower M hN hI T hEmpty]
    exact (pullback_comp T.contMDiff_proj hπ.contMDiff
      (isCoherent_restrictOn hI (CartanIrreducible.cartanCoherence _ hN))).symm

theorem ideal_empty_tower_of_pos (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent)
    (T : BlowupTower X Y) (hEmpty : ResolutionInvariantExt.IsEmptyTower T) (hPos : 0<T.length) :
    (geoTransformAlong M T).ideal=GermIdeal.pullback (m:=n) T.proj (restrictOn n M.N M.ideal) := by
  cases T with
  | refl => exact False.elim (Nat.not_lt_zero 0 hPos)
  | step T C π hπ =>
    rcases hEmpty with ⟨hEmpty,rfl⟩
    obtain ⟨hNT,hIT⟩:=HironakaActualNoncanonicalAnalyticTransformLocality.analytic_and_coherent_geoTransformAlong M hN hI T
    rw [geoTransformAlong_step,ideal_geoTransform_empty (geoTransformAlong M T) hNT hIT hπ,
      normalized_ideal_empty_tower M hN hI T hEmpty]
    exact (pullback_comp T.contMDiff_proj hπ.contMDiff
      (isCoherent_restrictOn hI (CartanIrreducible.cartanCoherence _ hN))).symm

private theorem pullback_restrictOn_open (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent) (U : Opens X) :
    GermIdeal.pullback (m:=n) (Subtype.val : U→X) (restrictOn n M.N M.ideal)=
      restrictOn n ((Subtype.val : U→X) ⁻¹' M.N) (GermIdeal.pullback (m:=n) (Subtype.val : U→X) M.ideal) := by
  ext x g
  rw [MarkedIdealRestrictOpen.mem_pullback_val_iff U
    (isCoherent_restrictOn hI (CartanIrreducible.cartanCoherence _ hN))]
  exact (MarkedIdealRestrictOpen.restrictOn_pullback_val_iff U hI).symm

private theorem restricted_ideal_empty_tail (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent)
    (R : BlowupTower X Y) (U : Opens X)
    (hEmpty : ResolutionInvariantExt.IsEmptyTower (restrict U R)) (hPos : 0<R.length) :
    GermIdeal.pullback (m:=n) (Subtype.val : openPreimage R U→Y) (geoTransformAlong M R).ideal=
      GermIdeal.pullback (m:=n) (R.proj ∘ (Subtype.val : openPreimage R U→Y)) (restrictOn n M.N M.ideal) := by
  let MU:=MarkedIdeal.pullback (Subtype.val : U→X) M
  have hNU : IsComplexAnalyticSubset (n:=n) MU.N:=AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hN U
  have hIU : MU.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hI
  have hP : 0<(restrict U R).length:=by rwa [length_restrict]
  have hrec:=congrArg (fun A : MarkedIdeal n (openPreimage R U) => A.ideal)
    (HironakaActualNoncanonicalAnalyticTransformLocality.geoTransformAlong_restrict M hN hI U R)
  have hh:=ideal_empty_tower_of_pos MU hNU hIU (restrict U R) hEmpty hP
  have hnI : (restrictOn n M.N M.ideal).IsCoherent:=isCoherent_restrictOn hI (CartanIrreducible.cartanCoherence _ hN)
  calc
    GermIdeal.pullback (m:=n) (Subtype.val : openPreimage R U→Y) (geoTransformAlong M R).ideal=
        (geoTransformAlong MU (restrict U R)).ideal:=hrec.symm
    _=GermIdeal.pullback (m:=n) (restrict U R).proj (restrictOn n MU.N MU.ideal):=hh
    _=GermIdeal.pullback (m:=n) (restrict U R).proj
        (GermIdeal.pullback (m:=n) (Subtype.val : U→X) (restrictOn n M.N M.ideal)):=by
      rw [pullback_restrictOn_open M hN hI U]
      rfl
    _=GermIdeal.pullback (m:=n) ((Subtype.val : U→X) ∘ (restrict U R).proj)
        (restrictOn n M.N M.ideal):=
      (pullback_comp contMDiff_subtype_val (restrict U R).contMDiff_proj hnI).symm
    _=GermIdeal.pullback (m:=n) (R.proj ∘ (Subtype.val : openPreimage R U→Y))
        (restrictOn n M.N M.ideal):=by
      congr 1
      funext p
      exact proj_restrict U R p

private theorem tailTower_length (s : GrowingSeq X) (N r : ℕ) :
    (tailTower s N r).length=r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [tailTower,BlowupTower.length_step,ih]

theorem stable_prefix_pullback_eq (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) (r : ℕ) (hr : 0<r) :
    let N:=stableIndex s hLF x
    let O:=limitWindow s hLF (stableWindow s hLF x)
    let A:=geoTransformAlong M (s.stage N).2
    GermIdeal.pullback (m:=n) (Subtype.val : O→limitManifold s hLF)
      (GermIdeal.pullback (m:=n) (stageFactor s hLF (N+r)) (geoTransformAlong M (s.stage (N+r)).2).ideal)=
    GermIdeal.pullback (m:=n) (Subtype.val : O→limitManifold s hLF)
      (GermIdeal.pullback (m:=n) (stageFactor s hLF N) (restrictOn n A.N A.ideal)) := by
  dsimp only
  let N:=stableIndex s hLF x
  let U:=stableWindow s hLF x
  let O:=limitWindow s hLF U
  let A:=geoTransformAlong M (s.stage N).2
  let R:=tailTower s N r
  let W:=openPreimage (s.stage N).2 U
  have hEmpty : ResolutionInvariantExt.IsEmptyTower (restrict W R):=
    (RestrictEmptyTower.isEmptyTower_restrict_iff W R).mpr
      (centresAvoid_tailTower s N U (stableWindow_avoids s hLF x) r)
  have hPos : 0<R.length:=by rw [tailTower_length];exact hr
  obtain ⟨hAN,hAI⟩:=HironakaActualNoncanonicalAnalyticTransformLocality.analytic_and_coherent_geoTransformAlong M hN hI (s.stage N).2
  have hAR:=restricted_ideal_empty_tail A hAN hAI R W hEmpty hPos
  have hval (z : O) : stageFactor s hLF (N+r) z.val∈openPreimage R W:=by
    change (s.stage N).2.proj (R.proj (stageFactor s hLF (N+r) z.val))∈U
    have hh : R.proj (stageFactor s hLF (N+r) z.val)=stageFactor s hLF N z.val:=
      congrFun (stageFactor_tail s hLF N r) z.val
    rw [hh,stageFactor_projection]
    exact z.property
  let f : O → openPreimage R W:=fun z=>⟨stageFactor s hLF (N+r) z.val,hval z⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f:=
    BlowupRestrictOpen.contMDiff_opens_mk
      ((stageFactor_contMDiff s hLF (N+r)).comp contMDiff_subtype_val) hval
  have ha : geoTransformAlong A R=geoTransformAlong M (s.stage (N+r)).2:=by
    rw [←geoTransformAlong_append,append_tailTower]
  have hJ:= (HironakaActualNoncanonicalAnalyticTransformLocality.analytic_and_coherent_geoTransformAlong M hN hI (s.stage (N+r)).2).2
  have hNorm : (restrictOn n A.N A.ideal).IsCoherent:=
    isCoherent_restrictOn hAI (CartanIrreducible.cartanCoherence _ hAN)
  have hmap : (R.proj ∘ (Subtype.val : openPreimage R W→(s.stage (N+r)).1)) ∘ f=
      (stageFactor s hLF N) ∘ (Subtype.val : O→limitManifold s hLF):=by
    funext z
    exact congrFun (stageFactor_tail s hLF N r) z.val
  rw [ha] at hAR
  rw [←pullback_comp (stageFactor_contMDiff s hLF (N+r)) contMDiff_subtype_val hJ,
    ←pullback_comp (stageFactor_contMDiff s hLF N) contMDiff_subtype_val hNorm]
  calc
    GermIdeal.pullback (m:=n) ((stageFactor s hLF (N+r)) ∘ (Subtype.val : O→limitManifold s hLF))
        (geoTransformAlong M (s.stage (N+r)).2).ideal=
      GermIdeal.pullback (m:=n) f
        (GermIdeal.pullback (m:=n) (Subtype.val : openPreimage R W→(s.stage (N+r)).1)
          (geoTransformAlong M (s.stage (N+r)).2).ideal):=
      pullback_comp contMDiff_subtype_val hf hJ
    _=GermIdeal.pullback (m:=n) f
        (GermIdeal.pullback (m:=n) (R.proj ∘ (Subtype.val : openPreimage R W→(s.stage (N+r)).1))
          (restrictOn n A.N A.ideal)):=congrArg (GermIdeal.pullback (m:=n) f) hAR
    _=GermIdeal.pullback (m:=n)
        ((R.proj ∘ (Subtype.val : openPreimage R W→(s.stage (N+r)).1)) ∘ f)
        (restrictOn n A.N A.ideal):=
      (pullback_comp (R.contMDiff_proj.comp contMDiff_subtype_val) hf hNorm).symm
    _=GermIdeal.pullback (m:=n) ((stageFactor s hLF N) ∘ (Subtype.val : O→limitManifold s hLF))
        (restrictOn n A.N A.ideal):=by rw [hmap]

private theorem mem_of_comp_val_pullback {I : GermIdeal n X} (hI : I.IsCoherent)
    (O : Opens X) (q : O) (g : X→ℂ)
    (hg : (GermIdeal.pullback (m:=n) (Subtype.val : O→X) I).mem q (g ∘ Subtype.val)) :
    I.mem q.val g := by
  apply HomogenizedIdeal.mem_congr hI ((MarkedIdealRestrictOpen.mem_pullback_val_iff O hI).mp hg)
  filter_upwards [O.isOpen.mem_nhds q.property] with y hy
  dsimp only [extendOpens]
  split_ifs with h
  · rfl
  · exact False.elim (h hy)

private theorem mem_iff_of_open_pullback_eq {I J : GermIdeal n X}
    (hI : I.IsCoherent) (hJ : J.IsCoherent) (O : Opens X)
    (h : GermIdeal.pullback (m:=n) (Subtype.val : O→X) I=
      GermIdeal.pullback (m:=n) (Subtype.val : O→X) J) (q : O) (g : X→ℂ) :
    I.mem q.val g ↔ J.mem q.val g := by
  constructor
  · intro hg
    apply mem_of_comp_val_pullback hJ O q g
    rw [←h]
    exact MarkedIdealRestrictOpen.comp_val_mem_pullback_val O hI hg
  · intro hg
    apply mem_of_comp_val_pullback hI O q g
    rw [h]
    exact MarkedIdealRestrictOpen.comp_val_mem_pullback_val O hJ hg

/-- In each genuine stable window the entire independently defined union is
one actual finite-prefix ideal; this includes every off-carrier germ. -/
theorem mem_limitControlledIdeal_stable (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X)
    (z : limitManifold s hLF) (hz : z∈limitWindow s hLF (stableWindow s hLF x)) (g : limitManifold s hLF→ℂ) :
    (limitControlledIdeal M s hLF).mem z g ↔
      (GermIdeal.pullback (m:=n) (stageFactor s hLF (stableIndex s hLF x+1))
        (geoTransformAlong M (s.stage (stableIndex s hLF x+1)).2).ideal).mem z g := by
  let N:=stableIndex s hLF x
  let O:=limitWindow s hLF (stableWindow s hLF x)
  have hcoh (j : ℕ) : (GermIdeal.pullback (m:=n) (stageFactor s hLF j)
      (geoTransformAlong M (s.stage j).2).ideal).IsCoherent:=
    isCoherent_pullback (stageFactor_contMDiff s hLF j)
      (HironakaActualNoncanonicalAnalyticTransformLocality.analytic_and_coherent_geoTransformAlong M hN hI (s.stage j).2).2
  constructor
  · rintro ⟨j,hj⟩
    have hj' := prefix_pullback_monotone M hN hI s hLF (j:=j) (k:=N+(j+1)) (by omega) z g hj
    have he : GermIdeal.pullback (m:=n) (Subtype.val : O→limitManifold s hLF)
        (GermIdeal.pullback (m:=n) (stageFactor s hLF (N+(j+1))) (geoTransformAlong M (s.stage (N+(j+1))).2).ideal)=
        GermIdeal.pullback (m:=n) (Subtype.val : O→limitManifold s hLF)
        (GermIdeal.pullback (m:=n) (stageFactor s hLF (N+1)) (geoTransformAlong M (s.stage (N+1)).2).ideal):=
      (stable_prefix_pullback_eq M hN hI s hLF x (j+1) (Nat.zero_lt_succ j)).trans
        (stable_prefix_pullback_eq M hN hI s hLF x 1 Nat.zero_lt_one).symm
    exact (mem_iff_of_open_pullback_eq (hcoh (N+(j+1))) (hcoh (N+1)) O he ⟨z,hz⟩ g).mp hj'
  · intro hg
    exact ⟨N+1,hg⟩

/-- The SAME independently defined union of actual prefix pullbacks is
coherent globally, without a supplied local ideal or stabilization certificate. -/
theorem isCoherent_limitControlledIdeal (M : MarkedIdeal n X)
    (hN : IsComplexAnalyticSubset (n:=n) M.N) (hI : M.ideal.IsCoherent)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    (limitControlledIdeal M s hLF).IsCoherent := by
  intro z
  obtain ⟨x,q,rfl⟩:=actualHistoryLocalInclusion_jointly_surjective s hLF z
  let N:=stableIndex s hLF x
  let O:=limitWindow s hLF (stableWindow s hLF x)
  let z:=actualHistoryLocalInclusion s hLF x q
  have hz : z∈O:=by
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x q)∈stableWindow s hLF x
    rw [gluedProjection_local]
    exact q.property
  have hc : (GermIdeal.pullback (m:=n) (stageFactor s hLF (N+1))
      (geoTransformAlong M (s.stage (N+1)).2).ideal).IsCoherent:=
    isCoherent_pullback (stageFactor_contMDiff s hLF (N+1))
      (HironakaActualNoncanonicalAnalyticTransformLocality.analytic_and_coherent_geoTransformAlong M hN hI (s.stage (N+1)).2).2
  obtain ⟨V,hVo,hzV,k,a,ha,hgen⟩:=hc z
  refine ⟨V∩O,hVo.inter O.isOpen,⟨hzV,hz⟩,k,a,?_,?_⟩
  · intro i
    exact (ha i).mono inter_subset_left
  · intro y hy g
    exact (mem_limitControlledIdeal_stable M hN hI s hLF x y hy.2 g).trans (hgen y hy.1 g)

end
end Hironaka.HironakaActualLocallyFiniteControlledIdeal
