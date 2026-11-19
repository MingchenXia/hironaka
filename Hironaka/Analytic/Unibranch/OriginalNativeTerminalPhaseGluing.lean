import Hironaka.Analytic.Unibranch.OriginalNativeTerminalWindowOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism
import Hironaka.Analytic.Unibranch.HironakaG10GenGluing

/-! Genuine SAME-H endpoint existence by actual local spans on the ORIGINAL
source. Blueprint FIRST: original-native-terminal-phase-gluing.tex.
Independent physical clocks are retained; no comparison map is input. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseGluing
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11PresReduction
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaActualPowerBoundaryExponents
  CanonicalCentres OriginalIntrinsicHSSuperlevels OriginalNativeTerminalWindowOverlap
  HironakaG11SingularCentreModification
open _root_.Hironaka.ResolutionInvariantSpec (IsCanonical)

variable {X : SourceReducedComplexSpace} {n : ℕ} {ι κ : Type}
  (wT : ι → DimEmbedding X n) (wS : κ → DimEmbedding X n)
  (rawT : ∀i,MarkedIdeal n (Amb wT i)) (rawS : ∀j,MarkedIdeal n (Amb wS j))
  (H : ℕ → ℕ) (hrecT : ∀i,IsNativeWindowRecord (wT i) (rawT i) H)
  (hrecS : ∀j,IsNativeWindowRecord (wS j) (rawS j) H)
  (eT : ι → ℕ) (eS : κ → ℕ) (heT : ∀i,1≤eT i) (heS : ∀j,1≤eS j)
  (TT : Towers wT) (TS : Towers wS) (xt : XStage wT TT) (xs : XStage wS TS)
  (hcT : ∀i,IsCanonical (powerMarked (rawT i) (eT i))
    ((canonicalInvariant n).inv (powerMarked (rawT i) (eT i))) (TT i).2)
  (hcS : ∀j,IsCanonical (powerMarked (rawS j) (eS j))
    ((canonicalInvariant n).inv (powerMarked (rawS j) (eS j))) (TS j).2)
  (hrT : ∀i,IsGeoResolution (powerMarked (rawT i) (eT i)) (TT i).2)
  (hrS : ∀j,IsGeoResolution (powerMarked (rawS j) (eS j)) (TS j).2)
  (hCoverT : originalSingularHSThreshold X H ⊆ ⋃i,range (wT i).toLocalEmbedding.toPoint)
  (hCoverS : originalSingularHSThreshold X H ⊆ ⋃j,range (wS j).toLocalEmbedding.toPoint)
  (hOffT : IsIsoOver xt.q (originalSingularHSThreshold X H)ᶜ)
  (hOffS : IsIsoOver xs.q (originalSingularHSThreshold X H)ᶜ)

include hrecT hrecS heT heS hcT hcS hrT hrS hCoverT hCoverS hOffT hOffS in
/-- The cover is obtained from INITIAL threshold windows plus actual
full isomorphism-over witnesses, not from a vacuous final threshold. -/
theorem exists_local_span (y : xs.Y.obj.left) :
    ∃ (V : LocallyRingedSpace) (a : V ⟶ xs.Y.obj.left) (b : V ⟶ xt.Y.obj.left),
      LocallyRingedSpace.IsOpenImmersion a ∧ LocallyRingedSpace.IsOpenImmersion b ∧
      y ∈ range a.base ∧ b ≫ xt.q.hom.left = a ≫ xs.q.hom.left := by
  by_cases hy : xs.q.hom.left.base y ∈ originalSingularHSThreshold X H
  · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hCoverS hy)
    have hCurrent : y ∈ range (xs.map j).hom.left.base := by
      rw [xs.range_map j]
      exact hj
    obtain ⟨c,rfl⟩ := hCurrent
    obtain ⟨i,t,ht⟩ := Set.mem_iUnion.mp (hCoverT hy)
    obtain ⟨N,a,b,ha,hb,hm,hp⟩ := exists_local_comparison_at
      wT wS rawT rawS H hrecT hrecS eT eS heT heS TT TS xt xs hcT hcS hrT hrS i j c t ht
    refine ⟨N.obj.left,a.hom.left,b.hom.left,ha,hb,hm,?_⟩
    exact congrArg (fun F : N ⟶ X => F.hom.left) hp
  · obtain ⟨VS,jS,hjS,hRangeS,hProjS,hProjRangeS⟩ := hOffS
    obtain ⟨VT,jT,hjT,hRangeT,hProjT,hProjRangeT⟩ := hOffT
    let : LocallyRingedSpace.IsOpenImmersion (jT ≫ xt.q.hom.left) := hProjT
    let : LocallyRingedSpace.IsOpenImmersion (jS ≫ xs.q.hom.left) := hProjS
    have hsub : range (jS ≫ xs.q.hom.left).base ⊆ range (jT ≫ xt.q.hom.left).base := by
      rw [hProjRangeS,hProjRangeT]
    let L := LocallyRingedSpace.IsOpenImmersion.lift (jT ≫ xt.q.hom.left)
      (jS ≫ xs.q.hom.left) hsub
    have hL : LocallyRingedSpace.IsOpenImmersion L := by
      let : IsIso (pullback.snd (jT ≫ xt.q.hom.left) (jS ≫ xs.q.hom.left)) :=
        LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ hsub
      dsimp only [L,LocallyRingedSpace.IsOpenImmersion.lift]
      infer_instance
    refine ⟨VS,jS,L ≫ jT,hjS,
      @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hL _ hjT,?_,?_⟩
    · rw [hRangeS]
      exact hy
    · rw [Category.assoc]
      exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hsub

/-- Native uniqueness uses the actual dense original-regular site of the
source modification, independently of ambient extensions off carriers. -/
theorem maps_eq_over_base (a b : xs.Y ⟶ xt.Y) (ha : a ≫ xt.q=xs.q) (hb : b ≫ xt.q=xs.q) : a=b := by
  have hbase : ∀ z, xt.q.hom.left.base (a.hom.left.base z)=
      xt.q.hom.left.base (b.hom.left.base z) := fun z =>
    (congrArg (fun f : xs.Y ⟶ X => f.hom.left.base z) ha).trans
      (congrArg (fun f : xs.Y ⟶ X => f.hom.left.base z) hb).symm
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq a b
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    xt.isSingularCentreModification.isIsoOver_intrinsicRegularLocus
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hbase
    xs.isSingularCentreModification.dense_preimage_intrinsicRegularLocus
    (fun u hu => (congrArg (fun f : xs.Y ⟶ X => f.hom.left.base u) ha).symm ▸ hu)) z

include hrecT hrecS heT heS hcT hcS hrT hrS hCoverT hCoverS hOffT hOffS in
private theorem exists_global_map : ∃ f : xs.Y ⟶ xt.Y, f ≫ xt.q=xs.q := by
  classical
  choose V a b ha hb hrange hproj using exists_local_span
    wT wS rawT rawS H hrecT hrecS eT eS heT heS TT TS xt xs hcT hcS hrT hrS hCoverT hCoverS hOffT hOffS
  let : ∀ y, LocallyRingedSpace.IsOpenImmersion (a y) := ha
  have hcover : ∀ y : xs.Y.obj.left, ∃ (u : xs.Y.obj.left) (v : V u), (a u).base v=y := by
    intro y
    obtain ⟨v,hv⟩ := hrange y
    exact ⟨y,v,hv⟩
  have hscalar (y : xs.Y.obj.left) : b y ≫ xt.Y.obj.hom=a y ≫ xs.Y.obj.hom := by
    rw [← Over.w xt.q.hom,← Category.assoc,hproj y,Category.assoc,Over.w xs.q.hom]
  have hcompat (y z : xs.Y.obj.left) :
      pullback.fst (a y) (a z) ≫ b y = pullback.snd (a y) (a z) ≫ b z := by
    let F := pullback.fst (a y) (a z) ≫ b y
    let G := pullback.snd (a y) (a z) ≫ b z
    have hbasecomp : F ≫ xt.q.hom.left=G ≫ xt.q.hom.left := by
      dsimp only [F,G]
      rw [Category.assoc,hproj y,← Category.assoc,pullback.condition,
        Category.assoc,← hproj z,← Category.assoc]
    have hG : LocallyRingedSpace.IsOpenImmersion G :=
      @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ (by infer_instance) _ (hb z)
    have hpointsFun : (fun v => F.base v)=(fun v => G.base v) :=
      HironakaG11LiftUniqueness.eq_of_comp_eq_of_isOpenMap
        xt.isSingularCentreModification.isIsoOver_intrinsicRegularLocus
        xt.isSingularCentreModification.interior_preimage_intrinsicSingularLocus
        F.base.hom.continuous G.base.hom.continuous hG.base_open.isOpenMap
        (fun v => congrArg (fun f => f.base v) hbasecomp)
    have hpoints : F.base=G.base := by
      ext v
      exact congrFun hpointsFun v
    apply HironakaG10GenGluing.lrs_hom_eq_of_base_eq (A := xs.Y) (B := xt.Y)
      (pullback.fst (a y) (a z) ≫ a y) F G
    · dsimp only [F]
      rw [Category.assoc,hscalar y,Category.assoc]
    · dsimp only [G]
      rw [Category.assoc,hscalar z,← Category.assoc,← pullback.condition,Category.assoc]
    · exact hpoints
  obtain ⟨f,hf,-⟩ := HironakaIntrinsicMorphismGluing.exists_unique_over V a hcover
    xs.Y.obj.hom xt.Y.obj.hom b hcompat hscalar
  refine ⟨ObjectProperty.homMk f,?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change f.left ≫ xt.q.hom.left=xs.q.hom.left
  apply HironakaIntrinsicMorphismGluing.hom_ext V a hcover
  intro y
  rw [← Category.assoc,hf y,hproj y]

include hrecT hrecS heT heS hcT hcS hrT hrS hCoverT hCoverS hOffT hOffS in
/-- Actual global endpoint existence: local maps, inverse and full over-base
square are derived; two independent physical clocks remain untouched. -/
theorem exists_global_comparison : ∃ E : xs.Y ≅ xt.Y, E.hom ≫ xt.q=xs.q := by
  obtain ⟨f,hf⟩ := exists_global_map
    wT wS rawT rawS H hrecT hrecS eT eS heT heS TT TS xt xs hcT hcS hrT hrS hCoverT hCoverS hOffT hOffS
  obtain ⟨g,hg⟩ := exists_global_map
    wS wT rawS rawT H hrecS hrecT eS eT heS heT TS TT xs xt hcS hcT hrS hrT hCoverS hCoverT hOffS hOffT
  have hfg : f ≫ g=𝟙 xs.Y := by
    apply maps_eq_over_base wS wS TS TS xs xs (f ≫ g) (𝟙 xs.Y)
    · rw [Category.assoc,hg,hf]
    · simp
  have hgf : g ≫ f=𝟙 xt.Y := by
    apply maps_eq_over_base wT wT TT TT xt xt (g ≫ f) (𝟙 xt.Y)
    · rw [Category.assoc,hf,hg]
    · simp
  exact ⟨⟨f,g,hfg,hgf⟩,hf⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseGluing
