import Hironaka.Resolution.HironakaActualReducedRelativeNormalIdeals

/-! Actual coordinate/open/ENTIRE reduced-ideal dictionaries for the normal
blocks used by the genuine common stable ambient model.
Blueprint: hironaka-actual-normal-block-coordinate-dictionary-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalBlockCoordinateDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualOpenZeroSectionDifferentials HironakaActualIntrinsicStableAmbientIso
  HironakaActualIteratedRelativeNormalHistory HironakaActualReducedRelativeNormalIdeals
  HironakaActualIntrinsicIsoPairedWindows HironakaActualIntrinsicStableIdealSquare
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient

private theorem projection_add_last (n r : ℕ) (z : ComplexModel (n+(r+1))) :
    tangentProjection n r (tangentProjection (n+r) 1 z)=tangentProjection n (r+1) z:=by
  ext i
  rfl

private theorem inclusion_add_last (n r : ℕ) (x : ComplexModel n) :
    tangentInclusion (n+r) 1 (tangentInclusion n r x)=tangentInclusion n (r+1) x:=by
  ext i
  refine Fin.addCases (m:=n) (n:=r+1) (fun j=>?_) (fun j=>?_) i
  · rw [tangentInclusion_tangent]
    have he : (j.castAdd r).castAdd 1=j.castAdd (r+1):=Fin.ext rfl
    rw [←he,tangentInclusion_tangent,tangentInclusion_tangent]
  · rw [tangentInclusion_normal]
    by_cases hj : j.val<r
    · let k : Fin r:=⟨j.val,hj⟩
      have he : j.natAdd n=(k.natAdd n).castAdd 1:=Fin.ext rfl
      rw [he,tangentInclusion_tangent,tangentInclusion_normal]
    · have hjr : j.val=r:=by omega
      let k : Fin 1:=0
      have he : j.natAdd n=k.natAdd (n+r):=Fin.ext (by simp only [Fin.val_natAdd];dsimp [k];omega)
      rw [he,tangentInclusion_normal]

/-- Membership in the ACTUAL iterated open is the genuine joint projection. -/
theorem mem_iteratedOpen_iff {n : ℕ} (U : Opens (ComplexModel n)) :
    ∀(r : ℕ)(z : ComplexModel (n+r)),z∈iteratedOpen U r ↔ tangentProjection n r z∈U:=by
  intro r
  induction r with
  | zero=>
    intro z
    have he : tangentProjection n 0 z=z:=by ext i;rfl
    exact he.symm ▸ Iff.rfl
  | succ r ih=>
    intro z
    change tangentProjection (n+r) 1 z∈iteratedOpen U r ↔ tangentProjection n (r+1) z∈U
    rw [ih,projection_add_last]

/-- The ACTUAL repeated zero section is the literal joint zero inclusion. -/
theorem iteratedZeroSection_val {n : ℕ} (U : Opens (ComplexModel n)) :
    ∀(r : ℕ)(x : U),(iteratedZeroSection U r x).val=tangentInclusion n r x.val:=by
  intro r
  induction r with
  | zero=>
    intro x
    ext i
    exact (tangentInclusion_tangent n 0 x.val i).symm
  | succ r ih=>
    intro x
    change tangentInclusion (n+r) 1 (iteratedZeroSection U r x).val=tangentInclusion n (r+1) x.val
    rw [ih,inclusion_add_last]

/-- The complete actual carrier, with every normal coordinate, at EVERY point. -/
theorem iteratedCarrier_joint {n : ℕ} {U : Opens (ComplexModel n)} (C : Set U) (r : ℕ) :
    iteratedZeroSection U r '' C=
      {z : iteratedOpen U r | tangentProjection n r z.val∈coordinateCarrier C ∧
        actualJointNormalProjection n r z.val=0}:=by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change tangentProjection n r (iteratedZeroSection U r x).val∈coordinateCarrier C ∧
      actualJointNormalProjection n r (iteratedZeroSection U r x).val=0
    rw [iteratedZeroSection_val,tangentProjection_tangentInclusion]
    exact ⟨⟨x,hx,rfl⟩,by simp⟩
  · rintro ⟨⟨x,hx,hpx⟩,hz⟩
    refine ⟨x,hx,?_⟩
    apply Subtype.ext
    rw [iteratedZeroSection_val,hpx]
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz,map_zero,add_zero] using
      (join_projections (n:=n) (m:=r) z.val)

/-- ENTIRE reduced iterated ideal in independently defined genuine joint coordinates. -/
theorem iterated_reduced_ideal_joint {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) (r : ℕ) :
    iteratedIdeal (vanishingIdeal (n:=n) C) r=
      vanishingIdeal (n:=n+r)
        {z : iteratedOpen U r | tangentProjection n r z.val∈coordinateCarrier C ∧
          actualJointNormalProjection n r z.val=0}:=by
  rw [iterated_reduced_normal_ideal hC r,iteratedCarrier_joint]

/-- Genuine exchange of differently ordered coordinate blocks. -/
def blockSwap (n m : ℕ) :
    ComplexModel (n+m) ≃ₘ⟮𝓘(ℂ,ComplexModel (n+m)),𝓘(ℂ,ComplexModel (m+n))⟯ ComplexModel (m+n):=
  ⟨⟨fun z=>join (actualJointNormalProjection n m z) (tangentProjection n m z),
    fun z=>join (actualJointNormalProjection m n z) (tangentProjection m n z),
    by intro z;simp only [first_join,second_join,join_projections],
    by intro z;simp only [first_join,second_join,join_projections]⟩,
    ((tangentInclusion m n).contMDiff.comp (actualJointNormalProjection n m).contMDiff).add
      ((actualJointNormalInclusion m n).contMDiff.comp (tangentProjection n m).contMDiff),
    ((tangentInclusion n m).contMDiff.comp (actualJointNormalProjection m n).contMDiff).add
      ((actualJointNormalInclusion n m).contMDiff.comp (tangentProjection m n).contMDiff)⟩

@[simp] theorem blockSwap_first (n m : ℕ) (z : ComplexModel (n+m)) :
    tangentProjection m n (blockSwap n m z)=actualJointNormalProjection n m z:=first_join _ _

@[simp] theorem blockSwap_second (n m : ℕ) (z : ComplexModel (n+m)) :
    actualJointNormalProjection m n (blockSwap n m z)=tangentProjection n m z:=second_join _ _

def oppositeOpen (n : ℕ) {m : ℕ} (V : Opens (ComplexModel m)) : Opens (ComplexModel (n+m)):=
  ⟨actualJointNormalProjection n m ⁻¹' V,V.isOpen.preimage (actualJointNormalProjection n m).continuous⟩

/-- The SAME actual block map on the ACTUAL original open models. -/
def blockSwapOpen (n : ℕ) {m : ℕ} (V : Opens (ComplexModel m)) :
    oppositeOpen n V ≃ₘ⟮𝓘(ℂ,ComplexModel (n+m)),𝓘(ℂ,ComplexModel (m+n))⟯ iteratedOpen V n:=by
  let f : oppositeOpen n V→iteratedOpen V n:=fun z=>⟨blockSwap n m z.val,
    (mem_iteratedOpen_iff V n _).mpr (by rw [blockSwap_first];exact z.property)⟩
  let g : iteratedOpen V n → oppositeOpen n V:=fun z=>⟨(blockSwap n m).symm z.val,by
    change actualJointNormalProjection n m (blockSwap m n z.val)∈V
    rw [blockSwap_second]
    exact (mem_iteratedOpen_iff V n _).mp z.property⟩
  refine ⟨⟨f,g,?_,?_⟩,?_,?_⟩
  · intro z
    apply Subtype.ext
    exact (blockSwap n m).symm_apply_apply z.val
  · intro z
    apply Subtype.ext
    exact (blockSwap n m).apply_symm_apply z.val
  · apply (ContMDiff.subtypeVal_comp_iff (iteratedOpen V n) f).mp
    exact (blockSwap n m).contMDiff.comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff (oppositeOpen n V) g).mp
    exact (blockSwap n m).symm.contMDiff.comp contMDiff_subtype_val

private theorem pullback_vanishing_of_diffeomorph {a b : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]
    [ChartedSpace (ComplexModel b) Y] [IsComplexManifold b Y]
    (χ : X ≃ₘ⟮𝓘(ℂ,ComplexModel a),𝓘(ℂ,ComplexModel b)⟯ Y) (A : Set Y) :
    GermIdeal.pullback (m:=a) χ (vanishingIdeal (n:=b) A)=vanishingIdeal (n:=a) (χ ⁻¹' A):=by
  apply GermIdeal.ext
  funext x f
  apply propext
  constructor
  · intro hf
    obtain ⟨hh,N,s,c,hs,_hc,he⟩:=GermIdeal.mem_pullback_iff.mp hf
    have hs0 : ∀i,∀ᶠ y in 𝓝 x,y∈χ ⁻¹' A → s i y=0:=by
      intro i
      obtain ⟨v,hv,hsv⟩:=hs i
      filter_upwards [χ.contMDiff.continuous.continuousAt.eventually hv.2] with y hy hyA
      rw [hsv,Function.comp_apply]
      exact hy hyA
    refine ⟨hh,?_⟩
    filter_upwards [he,eventually_all.mpr hs0] with y hy hy0 hyA
    rw [hy]
    exact Finset.sum_eq_zero fun i _=>by rw [hy0 i hyA,mul_zero]
  · intro hf
    let g : Y→ℂ:=f∘χ.symm
    have hfx : HolomorphicAt a f (χ.symm (χ x)):=by
      simpa only [χ.symm_apply_apply] using hf.1
    have hh : HolomorphicAt b g (χ x):=
      hfx.comp_contMDiff (Eventually.of_forall fun _=>χ.symm.contMDiff.contMDiffAt)
    have h0 : ∀ᶠ y in 𝓝 (χ x),χ.symm y∈χ ⁻¹' A → f (χ.symm y)=0:=
      (χ.symm.contMDiff.continuous.tendsto (χ x)).eventually
        (by simpa only [χ.symm_apply_apply] using hf.2)
    have hg : (vanishingIdeal (n:=b) A).mem (χ x) g:=by
      refine ⟨hh,?_⟩
      filter_upwards [h0] with y hy hyA
      apply hy
      change χ (χ.symm y)∈A
      rw [χ.apply_symm_apply]
      exact hyA
    have hComp : f=g∘χ:=by
      funext y
      change f y=f (χ.symm (χ y))
      rw [χ.symm_apply_apply]
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,hComp⟩ hf.1)

def oppositeCarrier (n : ℕ) {m : ℕ} {V : Opens (ComplexModel m)} (D : Set V) :
    Set (oppositeOpen n V):=
  {z | actualJointNormalProjection n m z.val∈coordinateCarrier D ∧ tangentProjection n m z.val=0}

theorem blockSwapOpen_preimage_carrier (n : ℕ) {m : ℕ} {V : Opens (ComplexModel m)} (D : Set V) :
    blockSwapOpen n V ⁻¹' (iteratedZeroSection V n '' D)=oppositeCarrier n D:=by
  rw [iteratedCarrier_joint]
  ext z
  change (tangentProjection m n (blockSwap n m z.val)∈coordinateCarrier D ∧
      actualJointNormalProjection m n (blockSwap n m z.val)=0) ↔
    (actualJointNormalProjection n m z.val∈coordinateCarrier D ∧ tangentProjection n m z.val=0)
  rw [blockSwap_first,blockSwap_second]

/-- ENTIRE functional ideal under the SAME actual opposite-block open map. -/
theorem blockSwapOpen_pullback_iterated_reduced_ideal (n : ℕ) {m : ℕ}
    {V : Opens (ComplexModel m)} {D : Set V} (hD : IsComplexAnalyticSubset (n:=m) D) :
    GermIdeal.pullback (m:=n+m) (blockSwapOpen n V) (iteratedIdeal (vanishingIdeal (n:=m) D) n)=
      vanishingIdeal (n:=n+m) (oppositeCarrier n D):=by
  rw [iterated_reduced_normal_ideal hD n,pullback_vanishing_of_diffeomorph,blockSwapOpen_preimage_carrier]

end
end Hironaka.HironakaActualNormalBlockCoordinateDictionary
