import TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteHistoryComparison
import Mathlib.Topology.Gluing

/-!
# Actual overlap coherence from one genuine locally finite blowup history

All windows and maps are constructed from the same original actual history.
No compatible atlas, comparison or cocycle is incoming.
Blueprint: `hironaka-actual-locally-finite-history-overlap-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteHistoryOverlap
noncomputable section
open FirstPass FirstPass.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq RestrictEmptyTower HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryComparison HironakaOriginalTerminalProjectionUniqueness
  BlowupTowerIsoTail MaxLocusLocal BlowupRestrictOpen
variable {n : ℕ} {X : CMfd.{u} n}

private theorem base_eq {s : GrowingSeq X} {U : Opens X} {i j : ℕ}
    (e : CMfd.of (n := n) (openPreimage (s.stage j).2 U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (s.stage i).2 U))
    (he : ∀ z,(restrict U (s.stage i).2).proj (e z)=(restrict U (s.stage j).2).proj z)
    (z : openPreimage (s.stage j).2 U) :
    (s.stage i).2.proj (e z).val=(s.stage j).2.proj z.val := by
  have hh := congrArg Subtype.val (he z)
  simpa only [proj_restrict] using hh

/-- Genuine restriction of the actual whole over-base comparison, including
its inverse and true open-map holomorphicity. -/
def restrictPrefixComparison (s : GrowingSeq X) (U V : Opens X) (hVU : V≤U)
    (i j : ℕ)
    (e : CMfd.of (n := n) (openPreimage (s.stage j).2 U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (s.stage i).2 U))
    (he : ∀ z,(restrict U (s.stage i).2).proj (e z)=(restrict U (s.stage j).2).proj z) :
    CMfd.of (n := n) (openPreimage (s.stage j).2 V)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (s.stage i).2 V) := by
  let f : openPreimage (s.stage j).2 V → openPreimage (s.stage i).2 V := fun z =>
    ⟨(e ⟨z.val,hVU z.property⟩).val,by
      change (s.stage i).2.proj (e ⟨z.val,hVU z.property⟩).val∈V
      rw [base_eq e he]
      exact z.property⟩
  have hinv (z : openPreimage (s.stage i).2 U) :
      (s.stage j).2.proj (e.symm z).val=(s.stage i).2.proj z.val := by
    have hh := base_eq e he (e.symm z)
    rw [e.apply_symm_apply] at hh
    exact hh.symm
  let g : openPreimage (s.stage i).2 V → openPreimage (s.stage j).2 V := fun z =>
    ⟨(e.symm ⟨z.val,hVU z.property⟩).val,by
      change (s.stage j).2.proj (e.symm ⟨z.val,hVU z.property⟩).val∈V
      rw [hinv]
      exact z.property⟩
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_
  }
  · intro z
    apply Subtype.ext
    change (e.symm (e ⟨z.val,hVU z.property⟩)).val=z.val
    exact congrArg (fun q : openPreimage (s.stage j).2 U => q.val)
      (e.symm_apply_apply ⟨z.val,hVU z.property⟩)
  · intro z
    apply Subtype.ext
    change (e (e.symm ⟨z.val,hVU z.property⟩)).val=z.val
    exact congrArg (fun q : openPreimage (s.stage i).2 U => q.val)
      (e.apply_symm_apply ⟨z.val,hVU z.property⟩)
  · exact contMDiff_opens_mk
      (contMDiff_subtype_val.comp (e.contMDiff.comp (contMDiff_opens_mk contMDiff_subtype_val _))) _
  · exact contMDiff_opens_mk
      (contMDiff_subtype_val.comp (e.symm.contMDiff.comp (contMDiff_opens_mk contMDiff_subtype_val _))) _

theorem restrictPrefixComparison_proj (s : GrowingSeq X) (U V : Opens X) (hVU : V≤U)
    (i j : ℕ)
    (e : CMfd.of (n := n) (openPreimage (s.stage j).2 U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (s.stage i).2 U))
    (he : ∀ z,(restrict U (s.stage i).2).proj (e z)=(restrict U (s.stage j).2).proj z)
    (z : openPreimage (s.stage j).2 V) :
    (restrict V (s.stage i).2).proj (restrictPrefixComparison s U V hVU i j e he z)=
      (restrict V (s.stage j).2).proj z := by
  apply Subtype.ext
  rw [proj_restrict,proj_restrict]
  exact base_eq e he ⟨z.val,hVU z.property⟩

/-- Actual cuts and windows chosen from the proved finite-image bound. -/
def stableIndex (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) : ℕ :=
  (exists_actual_stabilizing_window s hLF x).choose

def stableWindow (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) : Opens X :=
  (exists_actual_stabilizing_window s hLF x).choose_spec.choose

theorem point_mem_stableWindow (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    x ∈ stableWindow s hLF x :=
  (exists_actual_stabilizing_window s hLF x).choose_spec.choose_spec.1

theorem stableWindow_avoids (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    ∀ i, stableIndex s hLF x ≤ i →
      Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (stableWindow s hLF x : Set X)) :=
  (exists_actual_stabilizing_window s hLF x).choose_spec.choose_spec.2.1

abbrev localEndpoint (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) : CMfd.{u} n :=
  CMfd.of (n := n) (openPreimage (s.stage (stableIndex s hLF x)).2 (stableWindow s hLF x))

def localProjection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    localEndpoint s hLF x → X := fun z => (s.stage (stableIndex s hLF x)).2.proj z.val

theorem localProjection_contMDiff (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localProjection s hLF x) :=
  (s.stage (stableIndex s hLF x)).2.contMDiff_proj.comp contMDiff_subtype_val

theorem localPrefixProjection_isProperMap (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (x : X) :
    IsProperMap (restrict (stableWindow s hLF x) (s.stage (stableIndex s hLF x)).2).proj :=
  HironakaLocalPrincipalization.isProperMap_proj _

def overlapOpen (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X) :
    Opens (localEndpoint s hLF x) :=
  ⟨localProjection s hLF x ⁻¹' (stableWindow s hLF y : Set X),
    (stableWindow s hLF y).isOpen.preimage
      ((s.stage (stableIndex s hLF x)).2.contMDiff_proj.continuous.comp continuous_subtype_val)⟩

private def overlapToDirect (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X) :
    CMfd.of (n := n) (overlapOpen s hLF x y)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (s.stage (stableIndex s hLF x)).2
          (stableWindow s hLF x ⊓ stableWindow s hLF y)) := by
  let A := openPreimage (s.stage (stableIndex s hLF x)).2 (stableWindow s hLF x)
  let B := openPreimage (s.stage (stableIndex s hLF x)).2
    (stableWindow s hLF x ⊓ stableWindow s hLF y)
  have hBA : B ≤ A := fun _ h => h.1
  have hh : overlapOpen s hLF x y = nestedOpens A B := by
    ext z
    exact ⟨fun h => ⟨z.property,h⟩,fun h => h.2⟩
  exact (opensCongr hh).trans (nestedOpensDiffeo (n := n) hBA)

private theorem intersection_avoids (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X) :
    ∀ i, min (stableIndex s hLF x) (stableIndex s hLF y) ≤ i →
      Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹'
        (stableWindow s hLF x ⊓ stableWindow s hLF y : Set X)) := by
  intro i hi
  rcases le_total (stableIndex s hLF x) (stableIndex s hLF y) with h | h
  · rw [min_eq_left h] at hi
    exact (stableWindow_avoids s hLF x i hi).mono_right (Set.preimage_mono inf_le_left)
  · rw [min_eq_right h] at hi
    exact (stableWindow_avoids s hLF y i hi).mono_right (Set.preimage_mono inf_le_right)

private def pairComparison (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X) :=
  latePrefixComparison s (stableWindow s hLF x ⊓ stableWindow s hLF y)
    (min (stableIndex s hLF x) (stableIndex s hLF y)) (intersection_avoids s hLF x y)
    (stableIndex s hLF y) (stableIndex s hLF x) (min_le_right _ _) (min_le_left _ _)

private theorem pairComparison_proj (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X)
    (z : openPreimage (s.stage (stableIndex s hLF x)).2
      (stableWindow s hLF x ⊓ stableWindow s hLF y)) :
    (s.stage (stableIndex s hLF y)).2.proj (pairComparison s hLF x y z).val =
      (s.stage (stableIndex s hLF x)).2.proj z.val :=
  base_eq _ (latePrefixComparison_proj s _ _ _ _ _ _ _) z

/-- The whole chosen overlap map, with its genuine holomorphic inverse. -/
def transition (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X) :
    CMfd.of (n := n) (overlapOpen s hLF x y)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (overlapOpen s hLF y x) :=
  (overlapToDirect s hLF x y).trans ((pairComparison s hLF x y).trans
    ((opensCongr (congrArg (openPreimage (s.stage (stableIndex s hLF y)).2)
      (inf_comm (stableWindow s hLF x) (stableWindow s hLF y)))).trans
      (overlapToDirect s hLF y x).symm))

theorem transition_projection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X)
    (z : overlapOpen s hLF x y) :
    localProjection s hLF y (transition s hLF x y z).val = localProjection s hLF x z.val := by
  exact pairComparison_proj s hLF x y (overlapToDirect s hLF x y z)

private theorem transition_val (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y : X)
    (z : overlapOpen s hLF x y) :
    (transition s hLF x y z).val.val =
      (pairComparison s hLF x y (overlapToDirect s hLF x y z)).val := rfl

theorem overlapOpen_self (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    overlapOpen s hLF x x = ⊤ := by
  ext z
  exact ⟨fun _ => trivial,fun _ => z.property⟩

theorem transition_self (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    transition s hLF x x =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (overlapOpen s hLF x x)) ∞ := by
  have hh : pairComparison s hLF x x = Diffeomorph.refl 𝓘(ℂ,ComplexModel n)
      (CMfd.of (n := n) (openPreimage (s.stage (stableIndex s hLF x)).2
        (stableWindow s hLF x ⊓ stableWindow s hLF x))) ∞ := by
    apply biholomorphisms_eq_of_actual_proj_eq
      (restrict (stableWindow s hLF x ⊓ stableWindow s hLF x) (s.stage (stableIndex s hLF x)).2)
    intro z
    apply Subtype.ext
    rw [proj_restrict,proj_restrict]
    exact pairComparison_proj s hLF x x z
  ext z
  rw [transition_val,hh]
  rfl

theorem transition_inter (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y w : X)
    (z : overlapOpen s hLF x y) (hz : z.val ∈ overlapOpen s hLF x w) :
    (transition s hLF x y z).val ∈ overlapOpen s hLF y w := by
  change localProjection s hLF y (transition s hLF x y z).val ∈ stableWindow s hLF w
  rw [transition_projection]
  exact hz

private def restrictedPair (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (x y : X) (O : Opens X) (hO : O ≤ stableWindow s hLF x ⊓ stableWindow s hLF y) :=
  restrictPrefixComparison s _ O hO (stableIndex s hLF y) (stableIndex s hLF x)
    (pairComparison s hLF x y)
    (latePrefixComparison_proj s _ _ _ _ _ _ _)

private theorem restrictedPair_proj (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (x y : X) (O : Opens X) (hO : O ≤ stableWindow s hLF x ⊓ stableWindow s hLF y)
    (z : openPreimage (s.stage (stableIndex s hLF x)).2 O) :
    (restrict O (s.stage (stableIndex s hLF y)).2).proj (restrictedPair s hLF x y O hO z) =
      (restrict O (s.stage (stableIndex s hLF x)).2).proj z :=
  restrictPrefixComparison_proj s _ O hO _ _ _ _ z

private theorem restrictedPair_point (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (x y : X) (O : Opens X) (hO : O ≤ stableWindow s hLF x ⊓ stableWindow s hLF y)
    (z : openPreimage (s.stage (stableIndex s hLF x)).2 O) :
    (restrictedPair s hLF x y O hO z).val =
      (pairComparison s hLF x y ⟨z.val,hO z.property⟩).val := rfl

/-- The very same chosen pair maps satisfy the actual triple cocycle. -/
theorem transition_cocycle (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x y w : X)
    (z : overlapOpen s hLF x y) (hz : z.val ∈ overlapOpen s hLF x w) :
    (transition s hLF y w ⟨(transition s hLF x y z).val,transition_inter s hLF x y w z hz⟩).val =
      (transition s hLF x w ⟨z.val,hz⟩).val := by
  let O := (stableWindow s hLF x ⊓ stableWindow s hLF y) ⊓ stableWindow s hLF w
  have hxy : O ≤ stableWindow s hLF x ⊓ stableWindow s hLF y := inf_le_left
  have hyw : O ≤ stableWindow s hLF y ⊓ stableWindow s hLF w := fun _ h => ⟨h.1.2,h.2⟩
  have hxw : O ≤ stableWindow s hLF x ⊓ stableWindow s hLF w := fun _ h => ⟨h.1.1,h.2⟩
  let e12 := restrictedPair s hLF x y O hxy
  let e23 := restrictedPair s hLF y w O hyw
  let e13 := restrictedPair s hLF x w O hxw
  have hComp : e12.trans e23 = e13 := by
    apply biholomorphisms_eq_of_actual_proj_eq (restrict O (s.stage (stableIndex s hLF w)).2)
    intro q
    exact (restrictedPair_proj s hLF y w O hyw (e12 q)).trans
      ((restrictedPair_proj s hLF x y O hxy q).trans
        (restrictedPair_proj s hLF x w O hxw q).symm)
  let zp : openPreimage (s.stage (stableIndex s hLF x)).2 O :=
    ⟨z.val.val,⟨⟨z.val.property,z.property⟩,hz⟩⟩
  have h23 : (e23 (e12 zp)).val =
      (transition s hLF y w ⟨(transition s hLF x y z).val,transition_inter s hLF x y w z hz⟩).val.val := by
    rw [restrictedPair_point,transition_val]
    congr 2
  have h13 : (e13 zp).val = (transition s hLF x w ⟨z.val,hz⟩).val.val := rfl
  apply Subtype.ext
  exact h23.symm.trans ((congrArg (fun e => (e zp).val) hComp).trans h13)

/-- Every overlap/gluing field is constructed from the one actual LF history. -/
def actualHistoryGlueCore (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    TopCat.GlueData.MkCore where
  J := X
  U x := TopCat.of (localEndpoint s hLF x)
  V := overlapOpen s hLF
  t x y := TopCat.ofHom ⟨transition s hLF x y,(transition s hLF x y).contMDiff.continuous⟩
  V_id := overlapOpen_self s hLF
  t_id := by
    intro x
    funext z
    change transition s hLF x x z = z
    rw [transition_self]
    rfl
  t_inter := fun {x y} w z hz => transition_inter s hLF x y w z hz
  cocycle := transition_cocycle s hLF

def actualHistoryGlueData (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) : TopCat.GlueData :=
  TopCat.GlueData.mk' (actualHistoryGlueCore s hLF)

def actualHistoryGluedSpace (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) : TopCat :=
  (actualHistoryGlueData s hLF).glued

def actualHistoryLocalInclusion (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X) :
    localEndpoint s hLF x → actualHistoryGluedSpace s hLF := (actualHistoryGlueData s hLF).ι x

theorem actualHistoryLocalInclusion_openEmbedding (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (x : X) :
    Topology.IsOpenEmbedding (actualHistoryLocalInclusion s hLF x) :=
  (actualHistoryGlueData s hLF).ι_isOpenEmbedding x

theorem actualHistoryLocalInclusion_jointly_surjective (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (z : actualHistoryGluedSpace s hLF) :
    ∃ (x : X) (q : localEndpoint s hLF x),actualHistoryLocalInclusion s hLF x q = z :=
  (actualHistoryGlueData s hLF).ι_jointly_surjective z

end
end TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteHistoryOverlap
