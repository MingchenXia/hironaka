import Hironaka.Analytic.Unibranch.OriginalNativeSmoothDirectDeletedHistory
import Hironaka.Resolution.HironakaSubmersionActualProductWindow

/-! Actual ambient submersions on WHOLE reduced inverse-image carriers are
smooth in the existing standard native local-product sense.
Blueprint first: `original-native-smooth-ambient-converse.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothAmbientConverse
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSubmersionActualProductWindow HironakaSmoothSubmersionMonomialOrdering
  SourceReducedComplexSpace OriginalNativeProductWindow OriginalNativeSmoothLocalProduct
open scoped ProductComplexManifold

section Quotients
variable {m n : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
  {b : M → N} {C : Set M} {D : Set N}

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem carrier_mapsTo (hCD : C = b ⁻¹' D) : ∀ y ∈ C, b y ∈ D :=
  fun y hy => Eq.mp (congrArg (fun A => y ∈ A) hCD) hy

def subspaceMorphism
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (hC : IsComplexAnalyticSubset (n := m) C) (hD : IsComplexAnalyticSubset (n := n) D)
    (hCD : C = b ⁻¹' D) : ofClosedAnalytic C hC ⟶ ofClosedAnalytic D hD :=
  ObjectProperty.homMk (Over.homMk (actualSubspaceMap hb.contMDiff (carrier_mapsTo hCD))
    (actualSubspaceMap_point hb.contMDiff (carrier_mapsTo hCD)))

theorem subspace_whole_ideal
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (hCD : C = b ⁻¹' D) :
    GermIdeal.pullback (m := m) b (vanishingIdeal (n := n) D) = vanishingIdeal (n := m) C :=
  (HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb D).trans
    (congrArg (fun A => vanishingIdeal (n := m) A) hCD.symm)

end Quotients

def targetChart {n : ℕ} {N : Type} [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (D : Set N) (hD : IsComplexAnalyticSubset (n := n) D)
    (P : Opens N) (B : Opens (ComplexModel n))
    (φ : P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B) : LocalEmbedding (ofClosedAnalytic D hD) where
  dim := n
  ambient := B
  carrier := (fun u : B => (φ.symm u).val) ⁻¹' D
  analytic := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_subtype_val.comp φ.symm.contMDiff) hD
  map := (actualSubspaceBiholomorphicIso φ.symm
    ((fun u : B => (φ.symm u).val) ⁻¹' D) ((Subtype.val : P → N) ⁻¹' D)
    (fun _ => Iff.rfl)).hom ≫ actualOpenSubspaceMap D P
  isOpenImmersion := by
    let I := actualSubspaceBiholomorphicIso φ.symm
      ((fun u : B => (φ.symm u).val) ⁻¹' D) ((Subtype.val : P → N) ⁻¹' D) (fun _ => Iff.rfl)
    have hI : LocallyRingedSpace.IsOpenImmersion I.hom := by infer_instance
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ I.hom hI
      (actualOpenSubspaceMap D P) (actualOpenSubspaceMap_isOpenImmersion D P)
  overPoint := by
    let I := actualSubspaceBiholomorphicIso φ.symm
      ((fun u : B => (φ.symm u).val) ⁻¹' D) ((Subtype.val : P → N) ⁻¹' D) (fun _ => Iff.rfl)
    have hP : actualOpenSubspaceMap (n := n) D P ≫ subspacePointMap (n := n) D =
        subspacePointMap (n := n) ((Subtype.val : P → N) ⁻¹' D) :=
      actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)
    have hI : I.hom ≫ subspacePointMap (n := n) ((Subtype.val : P → N) ⁻¹' D) =
        subspacePointMap (n := n) ((fun u : B => (φ.symm u).val) ⁻¹' D) :=
      actualSubspaceMap_point φ.symm.contMDiff (fun _ hx => hx)
    exact (Category.assoc _ _ _).trans ((congrArg (fun t => I.hom ≫ t) hP).trans hI)

/-- Actual whole quotient/OI/scalar square of a genuine ambient product chart. -/
theorem exists_native_product_window {n r : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (n+r)) M] [IsComplexManifold (n+r) M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    {b : M → N} {C : Set M} {D : Set N}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ b)
    (hC : IsComplexAnalyticSubset (n := n+r) C) (hD : IsComplexAnalyticSubset (n := n) D)
    (hCD : C = b ⁻¹' D)
    (P : Opens N) (Q : Opens M) (B : Opens (ComplexModel n)) (W : Opens (B × ComplexModel r))
    (φ : P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B)
    (ψ : Q ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (n+r))⟯ W)
    (hcomm : ∀ p : W, b (ψ.symm p).val = (φ.symm p.val.1).val) (c : C) (hcQ : c.val ∈ Q) :
    let e := targetChart D hD P B φ
    ∃ i : windowSpace e r W ⟶ ofClosedAnalytic C hC,
      LocallyRingedSpace.IsOpenImmersion i.hom.left ∧
      i ≫ subspaceMorphism hb hC hD hCD = windowFirst e r W ∧ c ∈ range i.hom.left.base := by
  dsimp only
  let e := targetChart D hD P B φ
  let PC : Set W := windowCarrier e r W
  let CQ : Set Q := (Subtype.val : Q → M) ⁻¹' C
  have hCP (p : W) : p ∈ PC ↔ ψ.symm p ∈ CQ := by
    change (φ.symm p.val.1).val ∈ D ↔ (ψ.symm p).val ∈ C
    have htrace : (ψ.symm p).val ∈ C ↔ b (ψ.symm p).val ∈ D := Set.ext_iff.mp hCD _
    exact (iff_of_eq (congrArg (fun z => z ∈ D) (hcomm p))).symm.trans htrace.symm
  let I := actualSubspaceBiholomorphicIso ψ.symm PC CQ hCP
  let iraw := I.hom ≫ actualOpenSubspaceMap (n := n+r) C Q
  have hscalar : iraw ≫ (ofClosedAnalytic C hC).obj.hom = (windowSpace e r W).obj.hom := by
    have hQpoint : actualOpenSubspaceMap (n := n+r) C Q ≫ subspacePointMap (n := n+r) C =
        subspacePointMap (n := n+r) CQ := actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)
    have hIpoint : I.hom ≫ subspacePointMap (n := n+r) CQ = subspacePointMap (n := n+r) (M := W) PC :=
      actualSubspaceMap_point ψ.symm.contMDiff (fun p hp => (hCP p).mp hp)
    exact (Category.assoc _ _ _).trans ((congrArg (fun t => I.hom ≫ t) hQpoint).trans hIpoint)
  let i : windowSpace e r W ⟶ ofClosedAnalytic C hC := ObjectProperty.homMk (Over.homMk iraw hscalar)
  have hi : LocallyRingedSpace.IsOpenImmersion i.hom.left := by
    have hI : LocallyRingedSpace.IsOpenImmersion I.hom := by infer_instance
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ I.hom hI
      (actualOpenSubspaceMap (n := n+r) C Q) (actualOpenSubspaceMap_isOpenImmersion C Q)
  have hL₁ := actualSubspaceMap_comp (n := n+r) (m := n+r) (p := n+r)
    (C := PC) (D := CQ) (E := C) (f := ψ.symm) (g := (Subtype.val : Q → M))
    ψ.symm.contMDiff contMDiff_subtype_val (fun p hp => (hCP p).mp hp) (fun _ hx => hx)
  have hL₂ := actualSubspaceMap_comp (n := n+r) (m := n+r) (p := n)
    (C := PC) (D := C) (E := D) (f := (fun p : W => (ψ.symm p).val)) (g := b)
    (contMDiff_subtype_val.comp ψ.symm.contMDiff) hb.contMDiff
    (fun p hp => (hCP p).mp hp) (carrier_mapsTo hCD)
  have hproj : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞
      (fun p : W => p.val.1) :=
    ProductComplexManifold.contMDiff_fst.comp contMDiff_subtype_val
  have hR₁ := actualSubspaceMap_comp (n := n+r) (m := n) (p := n)
    (M := W) (N := B) (P := P)
    (C := PC) (D := e.carrier) (E := (Subtype.val : P → N) ⁻¹' D)
    (f := windowProjection e r W) (g := φ.symm)
    hproj φ.symm.contMDiff (fun _ hx => hx) (fun _ hx => hx)
  have hR₂ := actualSubspaceMap_comp (n := n+r) (m := n) (p := n)
    (M := W) (N := P) (P := N)
    (C := PC) (D := (Subtype.val : P → N) ⁻¹' D) (E := D)
    (f := (fun p : W => φ.symm p.val.1)) (g := (Subtype.val : P → N))
    (φ.symm.contMDiff.comp hproj) contMDiff_subtype_val
    (fun _ hx => hx) (fun _ hx => hx)
  have hraw : iraw ≫ (subspaceMorphism hb hC hD hCD).hom.left = (windowFirst e r W).hom.left := by
    have hleft := (congrArg (fun t => t ≫ (subspaceMorphism hb hC hD hCD).hom.left) hL₁.symm).trans hL₂.symm
    have hright := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ actualOpenSubspaceMap (n := n) D P) hR₁.symm).trans hR₂.symm)
    exact hleft.trans ((HironakaResolutionSpaceComplex.actualSubspaceMap_congr
      (n := n+r) (m := n) (M := W) (N := N) (funext hcomm) _ _ _ _).trans hright.symm)
  have hsq : i ≫ subspaceMorphism hb hC hD hCD = windowFirst e r W := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hraw
  let q : Q := ⟨c.val,hcQ⟩
  let p : W := ψ q
  have hqp : (ψ.symm p).val = c.val := congrArg Subtype.val (ψ.symm_apply_apply q)
  have hp : p ∈ PC := (hCP p).mpr (Eq.mpr (congrArg (fun z => z ∈ C) hqp) c.property)
  exact ⟨i,hi,hsq,⟨⟨p,hp⟩,Subtype.ext hqp⟩⟩

private theorem lift_isOpenImmersion {A B C : LocallyRingedSpace}
    (a : A ⟶ C) (b : B ⟶ C) [LocallyRingedSpace.IsOpenImmersion a]
    [LocallyRingedSpace.IsOpenImmersion b] (hr : range b.base ⊆ range a.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift a b hr) := by
  let : IsIso (CategoryTheory.Limits.pullback.snd a b) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset a b hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

/-- A genuine full product-window square supplies the existing local-product definition. -/
theorem isSmoothAt_of_product_window {X Y : SourceReducedComplexSpace} (f : X ⟶ Y)
    (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r))
    (i : windowSpace e r W ⟶ X) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (hsq : i ≫ f = windowFirst e r W) (x : X.obj.left) (hx : x ∈ range i.hom.left.base) :
    IsSmoothAt f x := by
  let jW := (windowInclusion e r W).hom.left
  let : LocallyRingedSpace.IsOpenImmersion jW := windowInclusion_isOpenImmersion e r W
  let O : Opens (productSpace e r).obj.left :=
    ⟨range jW.base,(windowInclusion_isOpenImmersion e r W).base_open.isOpen_range⟩
  let ι := productOpenInclusion e r O
  have hι : LocallyRingedSpace.IsOpenImmersion ι :=
    PresheafedSpace.IsOpenImmersion.ofRestrict (productSpace e r).obj.left.toPresheafedSpace
      O.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion ι := hι
  have hr : range ι.base ⊆ range jW.base := by
    rintro _ ⟨u,rfl⟩
    exact u.property
  let k := LocallyRingedSpace.IsOpenImmersion.lift jW ι hr
  have hk : LocallyRingedSpace.IsOpenImmersion k := lift_isOpenImmersion jW ι hr
  have hfac : k ≫ jW = ι := LocallyRingedSpace.IsOpenImmersion.lift_fac jW ι hr
  let j := k ≫ i.hom.left
  have hj : LocallyRingedSpace.IsOpenImmersion j :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k hk i.hom.left hi
  have hlocal : j ≫ f.hom.left = ι ≫ (first e r).hom.left := by
    calc
      _ = k ≫ (i.hom.left ≫ f.hom.left) := Category.assoc _ _ _
      _ = k ≫ (windowFirst e r W).hom.left := congrArg (fun a => k ≫ a.hom.left) hsq
      _ = k ≫ (jW ≫ (first e r).hom.left) :=
        congrArg (fun a => k ≫ a.hom.left) (window_first_square e r W).symm
      _ = (k ≫ jW) ≫ (first e r).hom.left := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun a => a ≫ (first e r).hom.left) hfac
  obtain ⟨s,hs⟩ := hx
  let u : productOpen e r O := ⟨jW.base s,⟨s,rfl⟩⟩
  have hku : k.base u = s :=
    (windowInclusion_isOpenImmersion e r W).base_open.injective
      (congrArg (fun a => a.base u) hfac)
  refine ⟨e,r,O,j,hj,hlocal,u,?_⟩
  change i.hom.left.base (k.base u) = x
  rw [hku]
  exact hs

/-- An actual ambient submersion on the WHOLE inverse-image carrier is native smooth. -/
theorem isSmoothMorphism_subspaceMorphism {m n : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    {b : M → N} {C : Set M} {D : Set N}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (hC : IsComplexAnalyticSubset (n := m) C) (hD : IsComplexAnalyticSubset (n := n) D)
    (hCD : C = b ⁻¹' D) : IsSmoothMorphism (subspaceMorphism hb hC hD hCD) := by
  intro c
  obtain ⟨r,hm⟩ := Nat.exists_eq_add_of_le
    (dimension_le_of_submersionAt (hb.isSubmersionAt c.val))
  subst m
  obtain ⟨P,Q,B,W,φ,ψ,_,hcQ,hcomm⟩ :=
    exists_actual_product_window (hb.isSubmersionAt c.val)
  obtain ⟨i,hi,hsq,hpoint⟩ := exists_native_product_window hb hC hD hCD P Q B W φ ψ hcomm c hcQ
  exact isSmoothAt_of_product_window (subspaceMorphism hb hC hD hCD)
    (targetChart D hD P B φ) r W i hi hsq c hpoint

open Hironaka.BlowupSequences
  HironakaResolutionSpaceComplex OriginalNativeSmoothCanonicalSquare
  OriginalNativeSmoothNormalizedSquare OriginalNativeSmoothDirectDeletedHistory

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {x : X.obj.left}
  {V : Opens X.obj.left} {T : Opens Y.obj.left}

/-- Smoothness of the SAME full native lift of the true canonical Q history. -/
theorem canonical_nativeLift_isSmooth (a : LocalCanonicalPullback f x V T) :
    IsSmoothMorphism a.nativeLift := by
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    (strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry).isClosedSubmanifold
  have hD := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    (strictResolution_of_geometry (targetCarrier_analytic a.window a.neighbourhood) a.targetGeometry).isClosedSubmanifold
  exact isSmoothMorphism_subspaceMorphism a.history.isSubmersion hC hD a.strict_preimage_eq

/-- Smoothness of the SAME normalized native lift, with exact retained physical history. -/
theorem normalized_nativeLift_isSmooth {a : LocalCanonicalPullback f x V T} (b : NormalizedSource a) :
    IsSmoothMorphism (NormalizedSource.lift b) := by
  have hD := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    (strictResolution_of_geometry (targetCarrier_analytic a.window a.neighbourhood) a.targetGeometry).isClosedSubmanifold
  have hb := (direct_history b).toTrace.isSubmersion
  have hCD : strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood) =
      (a.lift ∘ b.biholomorphism) ⁻¹'
        strictTransform a.window.target.dim a.targetTower.proj (targetCarrier a.window a.neighbourhood) :=
    (b.whole_strict (sourceCarrier a.window a.neighbourhood)).trans
      (congrArg (fun A => b.biholomorphism ⁻¹' A) a.strict_preimage_eq)
  have hactual : NormalizedSource.lift b = subspaceMorphism hb (b.strict_analytic) hD hCD := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact native_lift_is_actual b
  rw [hactual]
  exact isSmoothMorphism_subspaceMorphism hb (b.strict_analytic) hD hCD

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothAmbientConverse
