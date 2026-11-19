import Hironaka.Resolution.HironakaActualNonregularCompanionNaturality
import Hironaka.Resolution.HironakaActualPointwiseDerivativeGenerators
import Hironaka.Invariant.StepOneLowerDomain
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualFreshRecursiveValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
open InvertibleIdealQuotient RelativePrincipalizationSpan GermIdealPullbackCalculus DerivativeIdealAlongCoherent
open DerivativeIdealAlong GiraudAlong BlowupFlatCoordinates GermIdealOrder
open HironakaActualNonregularCompanionNaturality
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
 [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem mem_congr_span_closed {I : GermIdeal n M}
 (hhol : ∀ x g,I.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (I.mem x) x g → I.mem x g)
 {x : M} {f g : M → ℂ} (hf : I.mem x f) (heq : f =ᶠ[𝓝 x] g) : I.mem x g :=
 hcl _ _ (DerivativeIdeal.isInSpanAt_congr (isInSpanAt_self hf (hhol _ _ hf)) heq)

omit [IsComplexManifold n M] in
private theorem raw_mem_pullback_val_iff {I : GermIdeal n M}
 (hhol : ∀ x g,I.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (I.mem x) x g → I.mem x g)
 (U : Opens M) {x : U} {f : U → ℂ} :
 (GermIdeal.pullback (m := n) (Subtype.val : U → M) I).mem x f ↔ I.mem x.val (extendOpens U f) := by
 have hh : (GermIdeal.pullback (m := n) (Subtype.val : U → M) I).mem x f ↔
   IsInSpanAt (n := n) (I.mem x.val) x.val (extendOpens U f) := isInSpanAt_comp_val_iff U
 exact hh.trans ⟨hcl _ _,fun h => isInSpanAt_self h (hhol _ _ h)⟩

theorem exists_local_generators_of_open_pullback {I : GermIdeal n M}
 (hhol : ∀ x g,I.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (I.mem x) x g → I.mem x g)
 (U : Opens M) (hI : (GermIdeal.pullback (m := n) (Subtype.val : U → M) I).IsCoherent)
 (x : U) :
 ∃ (O : Set M), IsOpen O ∧ x.val ∈ O ∧ ∃ (r : ℕ) (s : Fin r → M → ℂ),
   (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (s i) O) ∧
   ∀ y∈O,∀ g,I.mem y g ↔ IsInSpanAt (n := n) (·∈range s) y g := by
 classical
 obtain ⟨V,hVo,hxV,r,s,hs,hgen⟩ := hI x
 let S : Fin r → M → ℂ := fun i => extendOpens U (s i)
 have hScomp (i : Fin r) : S i ∘ (Subtype.val : U → M) = s i := by
   funext q
   exact extendOpens_val U (s i) q
 have hS : (fun v : U → ℂ => v∈range s) =
     fun v => ∃ t,t∈range S ∧ v=t∘(Subtype.val : U → M) := by
   funext v
   apply propext
   constructor
   · rintro ⟨i,rfl⟩
     exact ⟨S i,⟨i,rfl⟩,(hScomp i).symm⟩
   · rintro ⟨t,⟨i,rfl⟩,rfl⟩
     rw [hScomp i]
     exact mem_range_self i
 refine ⟨(Subtype.val : U → M) '' V,U.isOpen.isOpenMap_subtype_val _ hVo,⟨x,hxV,rfl⟩,r,S,?_,?_⟩
 · intro i y hy
   obtain ⟨q,hq,rfl⟩ := hy
   have hsq : HolomorphicAt n (s i) q := eventually_of_mem (hVo.mem_nhds hq)
     fun w hw => (hs i w hw).mdifferentiableAt (hVo.mem_nhds hw)
   exact ((holomorphicAt_iff_extendOpens U).mp hsq).self_of_nhds.mdifferentiableWithinAt
 · rintro y ⟨q,hq,rfl⟩ g
   have hext : extendOpens U (g∘(Subtype.val : U → M)) =ᶠ[𝓝 q.val] g := by
     filter_upwards [U.isOpen.mem_nhds q.property] with w hw
     exact extendOpens_val U (g∘Subtype.val) ⟨w,hw⟩
   have hm : (GermIdeal.pullback (m := n) (Subtype.val : U → M) I).mem q (g∘Subtype.val) ↔ I.mem q.val g := by
     rw [raw_mem_pullback_val_iff hhol hcl U]
     exact ⟨fun h => mem_congr_span_closed hhol hcl h hext,
       fun h => mem_congr_span_closed hhol hcl h hext.symm⟩
   have ht := hgen q hq (g∘Subtype.val)
   rw [hS,isInSpanAt_comp_val_iff U] at ht
   exact hm.symm.trans (ht.trans ⟨fun h => DerivativeIdeal.isInSpanAt_congr h hext,
     fun h => DerivativeIdeal.isInSpanAt_congr h hext.symm⟩)

variable {N : Set M} {I : GermIdeal n M} {x : M} {k : ℕ}
theorem exists_iterated_generators_of_local_generators
 (hI : ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (r : ℕ) (s : Fin r → M → ℂ),
   (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) O) ∧
   ∀ y∈O,∀ g,I.mem y g ↔ IsInSpanAt (n := n) (·∈range s) y g) (hN : RegularAtDim (n := n) N x k) :
 ∀ j : ℕ, ∃ (U : Set M), IsOpen U ∧ x ∈ U ∧
   ∃ (r : ℕ) (s : Fin r → M → ℂ),
     (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U) ∧
     ∀ y ∈ U, ∀ g, (iterDerivIdealAlong N I j).mem y g ↔
       IsInSpanAt (n := n) (· ∈ range s) y g
 | 0 => hI
 | j+1 => by
  classical
  obtain ⟨U, hUo, hxU, r, s, hs, hgen⟩ := exists_iterated_generators_of_local_generators hI hN j
  obtain ⟨-, -, Φ, hΦsrc, -, hflat⟩ := hN
  have hU'o : IsOpen (U ∩ flatDomain Φ) := hUo.inter (isOpen_flatDomain Φ)
  have hhol : ∀ i, ∀ z ∈ U, HolomorphicAt n (s i) z := fun i z hz =>
    eventually_of_mem (hUo.mem_nhds hz) fun w hw => (hs i w hw).mdifferentiableAt (hUo.mem_nhds hw)
  have hfam : ∀ c z, z ∈ U ∩ flatDomain Φ → HolomorphicAt n (derivFamilyAlong Φ k s c) z := by
    rintro (i | j | ij) z hz
    · exact hhol i z hz.1
    · by_cases hj : k ≤ j.1
      · simpa [derivFamilyAlong, hj] using holomorphicAt_flatCoord Φ j hz.2
      · simpa [derivFamilyAlong, hj] using holomorphicAt_const (n := n) (x := z) (0 : ℂ)
    · by_cases hj : ij.2.1 < k
      · simpa [derivFamilyAlong, hj] using holomorphicAt_flatPartial ij.2 hz.2 (hhol ij.1 z hz.1)
      · simpa [derivFamilyAlong, hj] using holomorphicAt_const (n := n) (x := z) (0 : ℂ)
  let eqv := Fintype.equivFin (Fin r ⊕ Fin n ⊕ (Fin r × Fin n))
  refine ⟨U ∩ flatDomain Φ, hU'o, ⟨hxU, mem_flatDomain_self Φ⟩,
    Fintype.card (Fin r ⊕ Fin n ⊕ (Fin r × Fin n)), fun c => derivFamilyAlong Φ k s (eqv.symm c), ?_, ?_⟩
  · intro c z hz
    exact (hfam _ z hz).self_of_nhds.mdifferentiableWithinAt
  · intro z hz g
    have hrange : range (fun c => derivFamilyAlong Φ k s (eqv.symm c)) = range (derivFamilyAlong Φ k s) := by
      ext t
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨eqv c, by simp⟩
    rw [hrange]
    exact derivIdealAlong_mem_iff_of_generators hΦsrc hflat hU'o inter_subset_right
      (fun i => (hs i).mono inter_subset_left) (fun w hw => hgen w hw.1) hz g

section Compose
variable {P Q R : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
 [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
 [TopologicalSpace R] [ChartedSpace (ComplexModel n) R] [IsComplexManifold n R]
private theorem pullback_comp_hhol {f : P → R} {g : Q → P}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
 {𝔞 : GermIdeal n R} (hhol : ∀ x v, 𝔞.mem x v → HolomorphicAt n v x) :
 GermIdeal.pullback (m := n) (f ∘ g) 𝔞 =
   GermIdeal.pullback (m := n) g (GermIdeal.pullback (m := n) f 𝔞) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      hhol _ _ hc
    have hcfhol : HolomorphicAt n (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := n) f 𝔞).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c, hc, rfl⟩ hcfhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    exact ⟨c ∘ f, hcf, rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩

private theorem marked_pullback_comp_hhol {J : MarkedIdeal n R}
 (hhol : ∀ x v, J.ideal.mem x v → HolomorphicAt n v x) {a : P → R} {b : Q → P} {d : Q → R}
 (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
 (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) (h : ∀ q,a (b q)=d q) :
 MarkedIdeal.pullback b (MarkedIdeal.pullback a J) = MarkedIdeal.pullback d J := by
 have hfun : a ∘ b = d := funext h
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
 · show b ⁻¹' (a ⁻¹' J.N)=d ⁻¹' J.N
   rw [←preimage_comp,hfun]
 · show (J.E.map (a ⁻¹' ·)).map (b ⁻¹' ·)=J.E.map (d ⁻¹' ·)
   rw [List.map_map]
   refine List.map_congr_left fun S _ => ?_
   show b ⁻¹' (a ⁻¹' S)=d ⁻¹' S
   rw [←preimage_comp,hfun]
 · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a J.ideal)=GermIdeal.pullback (m := n) d J.ideal
   rw [←pullback_comp_hhol ha hb hhol,hfun]
end Compose

section Reference
variable {X Y Z Z' : CMfd.{u} n}
open CompanionRebase CompanionReductionAlong MonomialPartAlong NonmonomialOrderLocal NonmonomialOrderTail
open DerivativeIdealAlongEtale CodimOnePartCanonical HironakaSharpActualCurrentOpenLowerReferences

open MarkedIdealRestrictOpen StepOneValue StepOneLowerDomain BoundaryCount CodimOneSupportAlong MemberInterLocusAlong
private theorem tangent_from_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed)
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d)
 (hd : 1 ≤ A.d) (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hz : z.val ∈ A.cosupp) :
 ∃ (O : Set Z) (v : Z → ℂ), z.val ∈ O ∧
   TangentDirectionAlong.IsTangentDirectionAlong A.N A.ideal A.d O v := by
 have hhA : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x :=
   hhol
 have hhB : ∀ x g, B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have hcA := cosupp_pullback_val A hhA U
 have hcB := cosupp_pullback_val B hhB U'
 have hcη := MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
   η.apply_symm_apply η.symm_apply_apply (MarkedIdeal.pullback (Subtype.val : U' → Z') B)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
     (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isCoherent) hg)
 have hzW : z ∈ (MarkedIdeal.pullback (Subtype.val : U → Z) A).cosupp := by rw [hcA];exact hz
 rw [hrec,hcη,hcB] at hzW
 obtain ⟨k,hNk⟩ := hB.isClosedSubmanifold_N.2 (η z).val hzW.1
 have hNr : RegularAtDim (n := n) A.N z.val k := by
   apply (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U)).mp
   have heq := congrArg MarkedIdeal.N hrec
   change (Subtype.val : U → Z) ⁻¹' A.N = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' B.N) at heq
   rw [heq]
   apply (regularAtDim_preimage_iff η).mpr
   exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hNk
 have hnot : ¬ OrderGE n A.N A.ideal z.val (A.d+1) := by
   intro ho
   let A1 : MarkedIdeal n Z := {A with d := A.d+1}
   let B1 : MarkedIdeal n Z' := {B with d := B.d+1}
   have hdEq : A.d = B.d := congrArg MarkedIdeal.d hrec
   have hr1 : MarkedIdeal.pullback (Subtype.val : U → Z) A1 =
       MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B1) := by
     apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
     · simpa only [A1,B1,MarkedIdeal.pullback] using congrArg MarkedIdeal.N hrec
     · simpa only [A1,B1,MarkedIdeal.pullback] using congrArg MarkedIdeal.E hrec
     · simpa only [A1,B1,MarkedIdeal.pullback] using congrArg MarkedIdeal.ideal hrec
     · exact congrArg (·+1) hdEq
   have hm : z ∈ (MarkedIdeal.pullback (Subtype.val : U → Z) A1).cosupp := by
     rw [cosupp_pullback_val A1 hhA U]
     exact ⟨hz.1,ho⟩
   rw [hr1,MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
     η.apply_symm_apply η.symm_apply_apply _
     (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
       (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isCoherent) hg),
     cosupp_pullback_val B1 hhB U'] at hm
   exact hmax (η z).val hm
 have hAw : (MarkedIdeal.pullback (Subtype.val : U → Z) A).ideal.IsCoherent := by
   rw [hrec]
   exact isCoherent_pullback η.contMDiff (isCoherent_pullback contMDiff_subtype_val hB.isCoherent)
 have hLocal := exists_local_generators_of_open_pullback hhol hcl U hAw z
 exact HironakaActualLocalTangentGenerators.exists_tangent_of_local_generators hhol hNr hd hz hnot
   (exists_iterated_generators_of_local_generators hLocal hNr (A.d-1))

private theorem bar_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : B.IsWellFormed)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) :
 MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A) =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)) := by
 have hhA : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x :=
   hhol
 have hhB : ∀ x g, B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal.IsCoherent :=
   GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isCoherent
 calc
  MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A) =
    HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → Z) A)) :=
    HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
      (fun y => ⟨DerivativeIdealAlongEtale.openInv U y,DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩) A hhA
  _ = HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))) :=
    congrArg (fun Q : MarkedIdeal n U => HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong Q)) hrec
  _ = MarkedIdeal.pullback η (HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U' → Z') B))) :=
    (HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong η.contMDiff
      (fun y => ⟨η.symm,⟨Eventually.of_forall (fun p => (η.contMDiff p).mdifferentiableAt (by simp)),
        Eventually.of_forall (fun p => (η.symm.contMDiff p).mdifferentiableAt (by simp)),
        Eventually.of_forall η.symm_apply_apply, Eventually.of_forall η.apply_symm_apply⟩⟩) _
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg)).symm
  _ = MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)) := by
    have hv : MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B) =
        HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) :=
      HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
        (fun y => ⟨DerivativeIdealAlongEtale.openInv U' y,DerivativeIdealAlongEtale.isLocalInverseAt_val U' y⟩) B hhB
    rw [hv]

private theorem self_mask_from_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed)
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d)
 (hd : 1 ≤ A.d) (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hz : z.val ∈ A.cosupp) (hl : level A .refl z.val = 0)
 (hsp : ¬ IsSpecial A .refl z.val) : z.val ∈ maskB A .refl z.val := by
 classical
 have ht := tangent_from_record A B hhol hcl hB hmax hd U U' η hrec z hz
 obtain ⟨hxchoice,hchoice⟩ := tangentChoice_spec A ht
 have hbar := bar_record A B hhol hB U U' η hrec
 have hBarB := isWellFormed_barMarked B hB
 have hdEq : A.d = B.d := congrArg MarkedIdeal.d hrec
 have hdB : 1 ≤ B.d := by omega
 have hBarMax := isMaximalOrderAlong_barMarked B hB hdB hmax
 have hBarD : 1 ≤ (barMarked B).d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
 have hZclosed := isClosed_codimOnePartAlong hBarB.isCoherent hBarB.isClosedSubmanifold_N hBarD hBarMax
 have hhBarA : ∀ x g, (barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hcodA := codimOnePartAlong_pullback_val U (N := (barMarked A).N)
   hhBarA (barMarked A).d
 have hcodB := codimOnePartAlong_pullback_val U' (N := (barMarked B).N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBarB.isCoherent hg)
   (barMarked B).d
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).ideal.IsCoherent :=
   GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hBarB.isCoherent
 have hcodη := codimOnePartAlong_pullback η
   (N := (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg)
   (barMarked B).d
 let ZA := codimOnePartAlong (barMarked A).N (barMarked A).ideal (barMarked A).d
 let ZB := codimOnePartAlong (barMarked B).N (barMarked B).ideal (barMarked B).d
 have hcod : (Subtype.val : U → Z) ⁻¹' ZA = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' ZB) := by
   calc
    (Subtype.val : U → Z) ⁻¹' ZA = codimOnePartAlong
      (MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A)).N
      (MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A)).ideal
      (MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A)).d := hcodA.symm
    _ = codimOnePartAlong (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B))).N
      (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B))).ideal
      (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B))).d :=
      congrArg (fun Q : MarkedIdeal n U => codimOnePartAlong Q.N Q.ideal Q.d) hbar
    _ = η ⁻¹' codimOnePartAlong
      (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).N
      (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).ideal
      (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).d := hcodη
    _ = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' ZB) := congrArg (η ⁻¹' ·) hcodB
 have hzZA : z.val ∉ ZA := fun h => hsp (Or.inl ⟨hl,h⟩)
 have hcZA : IsClosed ((Subtype.val : U → Z) ⁻¹' ZA) := by
   rw [hcod]
   exact (hZclosed.preimage continuous_subtype_val).preimage η.continuous
 have hevZ : ∀ᶠ w : U in 𝓝 z, w.val ∉ ZA := hcZA.isOpen_compl.mem_nhds hzZA
 have he := congrArg MarkedIdeal.E hrec
 change A.E.map ((Subtype.val : U → Z) ⁻¹' ·) =
   (B.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·) at he
 have hBAE : (barMarked A).E = A.E := rfl
 have hcount : boundaryCount A.E z.val = boundaryCount B.E (η z).val := by
   rw [←boundaryCount_map_preimage (Subtype.val : U → Z) _ z,he,
     boundaryCount_map_preimage η,boundaryCount_map_preimage (Subtype.val : U' → Z')]
 have hzero : boundaryCount B.E (η z).val = 0 := by
   rw [←hcount]
   simpa only [level,origMembers,geoTransformAlong,hBAE,List.take_length] using hl
 have hnone : ∀ H∈B.E, (η z).val ∉ H := by
   intro H hH hp
   obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
   have hpos : 0 < boundaryCount B.E (η z).val := Finset.card_pos.mpr
     ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
   omega
 have hopen : IsOpen {w : U' | ∀ H∈B.E,w.val ∉ H} := by
   have ho := (List.finite_toSet B.E).isOpen_biInter fun H hH => (hB.isSNCDivisor.1 H hH).isOpen_compl
   convert ho.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → Z')) using 1
   ext w
   simp
 have hevB : ∀ᶠ w : U in 𝓝 z, ∀ H∈B.E,(η w).val ∉ H :=
   η.continuous.continuousAt.eventually (hopen.mem_nhds hnone)
 have hevE : ∀ᶠ w : U in 𝓝 z, ∀ H∈A.E,w.val ∉ H := by
   filter_upwards [hevB] with w hw
   have ht : ∀ H∈(B.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·),w ∉ H := by
     simpa only [List.forall_mem_map,mem_preimage] using hw
   rw [←he] at ht
   simpa only [List.forall_mem_map,mem_preimage] using ht
 have hev : ∀ᶠ w : Z in 𝓝 z.val, (∀ H∈A.E,w∉H) ∧ w∉ZA :=
   (eventually_nhds_val_iff U).mpr (hevE.and hevZ)
 have hf : z.val ∈ interior {w : Z | w∈(tangentChoice A z.val).1 ∧ (∀ H∈A.E,w∉H) ∧ w∉ZA} := by
   apply mem_interior_iff_mem_nhds.mpr
   filter_upwards [hchoice.isOpen.mem_nhds hxchoice,hev] with w hw hc
   exact ⟨hw,hc⟩
 change z.val ∈ interior _
 simpa only [origMembers,geoTransformAlong,BlowupTower.proj,hBAE,List.take_length,id_eq] using hf



private theorem initial_level_special
 (A0 : MarkedIdeal n Z) (B0 : MarkedIdeal n Z')
 (hhol : ∀ x g,A0.ideal.mem x g → HolomorphicAt n g x) (hBF : B0.IsWellFormed)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hr : MarkedIdeal.pullback (Subtype.val : U → Z) A0=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B0)) :
 ∀ z : U,level A0 .refl z.val=level B0 .refl (η z).val ∧
   (IsSpecial A0 .refl z.val ↔ IsSpecial B0 .refl (η z).val) := by
 let A := barMarked A0
 let B := barMarked B0
 have hrec := bar_record A0 B0 hhol hBF U U' η hr
 have hhA : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hB : B.ideal.IsCoherent := (isWellFormed_barMarked B0 hBF).isCoherent
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal.IsCoherent :=
   isCoherent_pullback contMDiff_subtype_val hB
 have hO : A0.E.map ((Subtype.val : U → Z) ⁻¹' ·)=
     (B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·) := congrArg MarkedIdeal.E hrec
 have origA : origMembers A0 (.refl : BlowupTower Z Z)=A0.E := by
   change A0.E.take A0.E.length=A0.E
   exact List.take_length
 have origB : origMembers B0 (.refl : BlowupTower Z' Z')=B0.E := by
   change B0.E.take B0.E.length=B0.E
   exact List.take_length
 have hlevel (z : U) : level A0 .refl z.val=level B0 .refl (η z).val := by
   simp only [level,origA,origB]
   rw [←boundaryCount_map_preimage (Subtype.val : U → Z) _ z,hO,
     boundaryCount_map_preimage η,boundaryCount_map_preimage (Subtype.val : U' → Z')]
 have hcodA := codimOnePartAlong_pullback_val U (N := A.N)
   (fun _ _ hg => hhA _ _ hg) A.d
 have hcodB := codimOnePartAlong_pullback_val U' (N := B.N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB hg) B.d
 have hcodη := codimOnePartAlong_pullback η
   (N := (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg) B.d
 have hcod : (Subtype.val : U → Z) ⁻¹' codimOnePartAlong A.N A.ideal A.d =
     η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' codimOnePartAlong B.N B.ideal B.d) := by
   calc
     (Subtype.val : U → Z) ⁻¹' codimOnePartAlong A.N A.ideal A.d =
         codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : U → Z) A).N
           (MarkedIdeal.pullback (Subtype.val : U → Z) A).ideal
           (MarkedIdeal.pullback (Subtype.val : U → Z) A).d := hcodA.symm
     _ = codimOnePartAlong (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).N
         (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).ideal
         (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).d :=
       congrArg (fun Q : MarkedIdeal n U => codimOnePartAlong Q.N Q.ideal Q.d) hrec
     _ = η ⁻¹' codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N
         (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal B.d := hcodη
     _ = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' codimOnePartAlong B.N B.ideal B.d) :=
       congrArg (η ⁻¹' ·) hcodB
 have hcosA := cosupp_pullback_val A
   (fun _ _ hg => hhA _ _ hg) U
 have hcosB := cosupp_pullback_val B
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB hg) U'
 have hcosη := MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
   η.apply_symm_apply η.symm_apply_apply (MarkedIdeal.pullback (Subtype.val : U' → Z') B)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg)
 have hmemA := memberInterLocus_preimage (Subtype.val : U → Z)
   (fun z => U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z) A.N
   A0.E A.cosupp
 have hmemB := memberInterLocus_preimage (Subtype.val : U' → Z')
   (fun z => U'.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z) B.N
   B0.E B.cosupp
 have hmemη := memberInterLocus_preimage (η : U → U')
   (fun z => η.toHomeomorph.map_nhds_eq z) (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N
   (B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·))
   (MarkedIdeal.pullback (Subtype.val : U' → Z') B).cosupp
 have hmem : (Subtype.val : U → Z) ⁻¹' memberInterLocus A.N
       A0.E A.cosupp =
     η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' memberInterLocus B.N
       B0.E B.cosupp) := by
   calc
     (Subtype.val : U → Z) ⁻¹' memberInterLocus A.N
         A0.E A.cosupp =
       memberInterLocus (MarkedIdeal.pullback (Subtype.val : U → Z) A).N
         (A0.E.map ((Subtype.val : U → Z) ⁻¹' ·))
         (MarkedIdeal.pullback (Subtype.val : U → Z) A).cosupp := by
           rw [hcosA]; exact hmemA.symm
     _ = memberInterLocus (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).N
         ((B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·))
         (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).cosupp := by
           rw [hrec, hO]
     _ = η ⁻¹' memberInterLocus (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N
         (B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·))
         (MarkedIdeal.pullback (Subtype.val : U' → Z') B).cosupp := by
           rw [hcosη]; exact hmemη
     _ = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' memberInterLocus B.N
         B0.E B.cosupp) := by
           congr 1
           rw [hcosB]; exact hmemB
 intro z
 refine ⟨hlevel z,?_⟩
 simp only [IsSpecial,origA,origB,geoTransformAlong]
 rw [hlevel z]
 exact or_congr (and_congr_right fun _ => Iff.of_eq (congrArg (fun S : Set U => z ∈ S) hcod))
   (and_congr_right fun _ => Iff.of_eq (congrArg (fun S : Set U => z ∈ S) hmem))


private theorem self_maskA_from_record
 (hn : 0<n) (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x) (hB : B.IsWellFormed) (hdB : 1≤B.d)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hl : 1≤level A .refl z.val) (hsp : ¬IsSpecial A .refl z.val) :
 z.val∈maskA A .refl z.val := by
 classical
 have facts := initial_level_special A B hhol hB U U' η hrec
 have hpos : 1≤level B .refl (η z).val := by rw [←(facts z).1];exact hl
 have hnsp : ¬IsSpecial B .refl (η z).val := fun h => hsp ((facts z).2.mpr h)
 have hmask := StepOneLowerDomain.mem_maskA B hB hdB hn (.refl : BlowupTower Z' Z') trivial hpos hnsp
 have origA : origMembers A (.refl : BlowupTower Z Z)=A.E := by
   change A.E.take A.E.length=A.E
   exact List.take_length
 have origB : origMembers B (.refl : BlowupTower Z' Z')=B.E := by
   change B.E.take B.E.length=B.E
   exact List.take_length
 change (η z).val∈interior {w | (∀ H∈origMembers B (.refl : BlowupTower Z' Z'),w∈H → (η z).val∈H) ∧
   ¬(level B .refl w=level B .refl (η z).val ∧ IsSpecial B .refl w)} at hmask
 rw [origB] at hmask
 have ht := mem_interior_iff_mem_nhds.mp hmask
 have htU : ∀ᶠ w : U' in 𝓝 (η z),(∀ H∈B.E,w.val∈H → (η z).val∈H) ∧
     ¬(level B .refl w.val=level B .refl (η z).val ∧ IsSpecial B .refl w.val) :=
   (eventually_nhds_val_iff U').mp ht
 have hsU : ∀ᶠ w : U in 𝓝 z,(∀ H∈A.E,w.val∈H → z.val∈H) ∧
     ¬(level A .refl w.val=level A .refl z.val ∧ IsSpecial A .refl w.val) := by
   filter_upwards [η.continuous.continuousAt.eventually htU] with w hw
   have he := congrArg MarkedIdeal.E hrec
   change A.E.map ((Subtype.val : U → Z) ⁻¹' ·)=
     (B.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·) at he
   have hlist : (∀ H∈A.E,w.val∈H → z.val∈H) ↔ (∀ H∈B.E,(η w).val∈H → (η z).val∈H) := by
     have hp := congrArg (fun L : List (Set U) => ∀ H∈L,w∈H → z∈H) he
     simpa only [List.forall_mem_map,mem_preimage] using Iff.of_eq hp
   refine ⟨hlist.mpr hw.1,fun hm => hw.2 ⟨?_,(facts w).2.mp hm.2⟩⟩
   exact (facts w).1.symm.trans (hm.1.trans (facts z).1)
 have hs : ∀ᶠ w : Z in 𝓝 z.val,(∀ H∈A.E,w∈H → z.val∈H) ∧
     ¬(level A .refl w=level A .refl z.val ∧ IsSpecial A .refl w) :=
   (eventually_nhds_val_iff U).mpr hsU
 change z.val∈interior {w | (∀ H∈origMembers A (.refl : BlowupTower Z Z),w∈H → z.val∈H) ∧
   ¬(level A .refl w=level A .refl z.val ∧ IsSpecial A .refl w)}
 rw [origA]
 exact mem_interior_iff_mem_nhds.mpr hs

private theorem base_refl_value_of_mask
 (hn : 0<n) (A : MarkedIdeal n Z) (z : Z) (hsp : ¬IsSpecial A .refl z)
 (hmask : z∈lowerMask A (level A .refl z) .refl z) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn 0) A .refl z=
   toLex (level A .refl z,(0 : WithTop ℕ)) := by
 classical
 unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
 rw [if_neg hsp]
 change toLex (level A .refl z,if z∈lowerMask A (level A .refl z) .refl z then (0 : WithTop ℕ) else ⊤)=_
 rw [if_pos hmask]

private theorem fresh_base_values_from_record
 (hn : 0<n) (A : MarkedIdeal n Z) (B : MarkedIdeal n Z') {k : ℕ}
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : ResolutionInvariantSpec.IsInvDomain k B)
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hz : z.val∈A.cosupp) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn 0) A .refl z.val=
   Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn 0) B .refl (η z).val := by
 classical
 have facts := initial_level_special A B hhol hB.isWellFormed U U' η hrec
 have hhB : ∀ x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal.IsCoherent :=
   isCoherent_pullback contMDiff_subtype_val hB.isWellFormed.isCoherent
 have hzB : (η z).val∈B.cosupp := by
   have hm : z∈(MarkedIdeal.pullback (Subtype.val : U → Z) A).cosupp := by
     rw [cosupp_pullback_val A hhol U]
     exact hz
   rw [hrec,MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff η.apply_symm_apply η.symm_apply_apply _
     (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg),
     cosupp_pullback_val B hhB U'] at hm
   exact hm
 by_cases hsp : IsSpecial A .refl z.val
 · have hspB := (facts z).2.mp hsp
   unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
   rw [if_pos hsp,if_pos hspB,(facts z).1]
 · have hspB : ¬IsSpecial B .refl (η z).val := fun h => hsp ((facts z).2.mpr h)
   have hdEq : A.d=B.d := congrArg MarkedIdeal.d hrec
   have hdA : 1≤A.d := hdEq ▸ hB.one_le_d
   have hmA : z.val∈lowerMask A (level A .refl z.val) .refl z.val := by
     cases hs : level A .refl z.val with
     | zero =>
       simpa only [hs,lowerMask] using self_mask_from_record A B hhol hcl hB.isWellFormed hmax hdA U U' η hrec z hz hs hsp
     | succ s =>
       simpa only [hs,lowerMask] using self_maskA_from_record hn A B hhol hB.isWellFormed hB.one_le_d U U' η hrec z (by omega) hsp
   have hzBar : (η z).val∈(barMarked B).cosupp := by
     rw [cosupp_barMarked B hB.isWellFormed hB.one_le_d]
     exact hzB
   have hmB := (StepOneValueMasked.mem_lowerMask_and_isInvDomain_M B hB.isWellFormed hB.one_le_d hn
     hmax hB.dimLE (.refl : BlowupTower Z' Z') trivial hzBar (show stepRegime B
       (level B .refl (η z).val) .refl (η z).val from ⟨rfl,hspB⟩)).1
   rw [base_refl_value_of_mask hn A z.val hsp hmA,base_refl_value_of_mask hn B (η z).val hspB hmB,(facts z).1]

private theorem ordGe_pullback_local {f : Y → X}
 (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
 (hloc : ∀ y : Y,∃ ψ : X → Y,IsLocalInverseAt n f ψ y)
 (A : MarkedIdeal n X) (hA : A.ideal.IsCoherent) (q : ℕ) :
 ordGe (MarkedIdeal.pullback f A) q=f ⁻¹' ordGe A q := by
 have hi := congrArg MarkedIdeal.ideal (pullback_companionOf hf hloc A hA A.d)
 have hNN : GermIdeal.pullback (m := n) f (nmPart A)=nmPart (MarkedIdeal.pullback f A) := by
   simpa only [MarkedIdeal.pullback,companionOf,companionAlong,lt_self_iff_false,if_false] using hi
 change cosupport n (f ⁻¹' A.N) (nmPart (MarkedIdeal.pullback f A)) q=f ⁻¹' cosupport n A.N (nmPart A) q
 rw [←hNN]
 have hhol : ∀ x g,(nmPart A).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 exact MonomialPartEtale.cosupport_pullback_of_local hloc hhol A.N q

private theorem order_trace
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z') (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) (q : ℕ) :
 (Subtype.val : U → Z) ⁻¹' ordGe A q=η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' ordGe B q) := by
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal.IsCoherent :=
   isCoherent_pullback contMDiff_subtype_val hB
 calc
  (Subtype.val : U → Z) ⁻¹' ordGe A q=ordGe (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → Z) A) q :=
    (ordGe_pullback_local (X := Z) (Y := CMfd.of (n := n) U) contMDiff_subtype_val
      (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) A hA q).symm
  _ = ordGe (M := CMfd.of (n := n) U) (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) q :=
    congrArg (fun Q : MarkedIdeal n U => ordGe (M := CMfd.of (n := n) U) Q q) hrec
  _ = η ⁻¹' ordGe (M := CMfd.of (n := n) U') (MarkedIdeal.pullback (Subtype.val : U' → Z') B) q :=
    ordGe_pullback_local (X := CMfd.of (n := n) U') (Y := CMfd.of (n := n) U) η.contMDiff
      (fun y => ⟨η.symm,⟨Eventually.of_forall (fun p => (η.contMDiff p).mdifferentiableAt (by simp)),
        Eventually.of_forall (fun p => (η.symm.contMDiff p).mdifferentiableAt (by simp)),
        Eventually.of_forall η.symm_apply_apply,Eventually.of_forall η.apply_symm_apply⟩⟩) _ hBW q
  _ = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' ordGe B q) := congrArg (η ⁻¹' ·)
    (ordGe_pullback_local (X := Z') (Y := CMfd.of (n := n) U') contMDiff_subtype_val
      (fun y => ⟨openInv U' y,isLocalInverseAt_val U' y⟩) B hB q)

private theorem mask_trace
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z') (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) (o : ℕ) :
 (Subtype.val : U → Z) ⁻¹' (ordMask A o : Set Z)=
   η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' (ordMask B o : Set Z')) := by
 have hclA : (Subtype.val : U → Z) ⁻¹' closure (ordGe A (o+1)) =
     closure ((Subtype.val : U → Z) ⁻¹' ordGe A (o+1)) := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val (ordGe A (o+1))
 have hclB : (Subtype.val : U' → Z') ⁻¹' closure (ordGe B (o+1)) =
     closure ((Subtype.val : U' → Z') ⁻¹' ordGe B (o+1)) := U'.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val (ordGe B (o+1))
 have hc : (Subtype.val : U → Z) ⁻¹' closure (ordGe A (o+1))=
     η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' closure (ordGe B (o+1))) := by
   have hηcl : η ⁻¹' closure ((Subtype.val : U' → Z') ⁻¹' ordGe B (o+1)) =
       closure (η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' ordGe B (o+1))) :=
     η.toHomeomorph.preimage_closure _
   rw [hclA,order_trace A B hA hB U U' η hrec,←hηcl,←hclB]
 ext z
 exact not_congr (Set.ext_iff.mp hc z)

private theorem companion_span_closed
 (A : MarkedIdeal n Z) (o : ℕ) {x : Z} {g : Z → ℂ}
 (hg : IsInSpanAt (n := n) ((companionOf n A o).ideal.mem x) x g) :
 (companionOf n A o).ideal.mem x g := by
 classical
 unfold companionOf companionAlong at hg ⊢
 split_ifs at hg ⊢
 · simp only [MarkedIdealOperationsTransform.MarkedIdeal.add,RestrictedIdealExtension.sumIdeal] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 · obtain ⟨hfhol,K,s,a,hs,ha,hsum⟩ := hg
   refine ⟨hfhol,fun v hv => ?_⟩
   refine RestrictedIdealExtension.restrictOn_of_isInSpanAt (𝔞 := A.ideal)
     ⟨hv.1.mul hfhol,K,fun i w => v w*s i w,a,fun i => (hs i).2 v hv,ha,?_⟩
   filter_upwards [hsum] with w hw
   show v w*g w=∑ i,a i w*(v w*s i w)
   rw [hw,Finset.mul_sum]
   exact Finset.sum_congr rfl fun i _ => by ring

private theorem companion_hhol
 (A : MarkedIdeal n Z) (o : ℕ) {x : Z} {g : Z → ℂ}
 (hg : (companionOf n A o).ideal.mem x g) : HolomorphicAt n g x := by
 unfold companionOf companionAlong at hg
 split_ifs at hg <;> exact hg.1

private def referenceOriginalOpen (A : MarkedIdeal n Z) (U : Opens Z) (o : ℕ) : Opens (ordMask A o) :=
 ⟨(Subtype.val : ordMask A o → Z) ⁻¹' U,U.isOpen.preimage continuous_subtype_val⟩

private def referenceSwap (A : MarkedIdeal n Z) (U : Opens Z) (o : ℕ) :
 referenceWindow A U o ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ referenceOriginalOpen A U o :=
 (MaxLocusLocal.nestedDiffeo U (referenceWindow A U o) (U ⊓ ordMask A o)
   (fun q => ⟨fun h => ⟨q.property,h⟩,fun h => h.2⟩) (fun _ h => h.1)).trans
 (MaxLocusLocal.nestedDiffeo (ordMask A o) (referenceOriginalOpen A U o) (U ⊓ ordMask A o)
   (fun q => ⟨fun h => ⟨h,q.property⟩,fun h => h.1⟩) (fun _ h => h.2)).symm

open BlowupTowerTransforms HironakaActualNoncanonicalAnalyticTransformLocality
open ResolutionInvariantSpec (IsInvDomain)

theorem exists_actual_fresh_reference_window
 (hn : 0 < n) (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
 (T : BlowupTower X Y) {C C' : Set Y} {π : Z → Y} {π' : Z' → Y}
 (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
 (hTarget : IsGeoTestTower M (.step T C' π' hπ')) (V : Opens Y)
 (hC : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' C') :
 ∃ η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ stepWindow hπ' V,
   (∀ z : stepWindow hπ V,π' (η z).val=π z.val) ∧
   ∀ o : ℕ,1≤o →
     let A := geoTransformAlong M (.step T C π hπ)
     let B := geoTransformAlong M (.step T C' π' hπ')
     ∃ ψ : referenceWindow A (stepWindow hπ V) o ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       referenceWindow B (stepWindow hπ' V) o,
       (∀ z,(ψ z).val=η z.val) ∧
       MarkedIdeal.pullback (referenceInclusion A (stepWindow hπ V) o)
         (GeneralValue.compAt M o (.step T C π hπ)) =
         MarkedIdeal.pullback ψ (MarkedIdeal.pullback (referenceInclusion B (stepWindow hπ' V) o)
           (GeneralValue.compAt M o (.step T C' π' hπ'))) ∧
       (MarkedIdeal.pullback (referenceInclusion A (stepWindow hπ V) o)
         (GeneralValue.compAt M o (.step T C π hπ))).ideal.IsCoherent := by
 obtain ⟨η,hsq,hComp⟩ := exists_actual_current_companion_window hn M hM T hπ hπ' hTarget V hC
 have hN := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hM.isWellFormed.isClosedSubmanifold_N
 obtain ⟨θ,⟨hθsq,hrec⟩,_⟩ := exists_current_step_whole_record M hN hM.isWellFormed.isCoherent T hπ hπ' V hC
 obtain ⟨φ,hφsq,hUnique⟩ := existsUnique_current_step_comparison hπ hπ' V hC
 have hθη : θ=η := (hUnique θ hθsq).trans (hUnique η hsq).symm
 rw [hθη] at hrec
 let A := geoTransformAlong M (.step T C π hπ)
 let B := geoTransformAlong M (.step T C' π' hπ')
 let U := stepWindow hπ V
 let U' := stepWindow hπ' V
 have hA : A.ideal.IsCoherent :=
   (analytic_and_coherent_geoTransformAlong M hN hM.isWellFormed.isCoherent (.step T C π hπ)).2
 have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM _ hTarget
 refine ⟨η,hsq,?_⟩
 intro o ho
 dsimp only
 have hW (z : U) : z∈referenceWindow A U o ↔ η z∈referenceWindow B U' o :=
   Set.ext_iff.mp (mask_trace A B hA hB.isWellFormed.isCoherent U U' η hrec o) z
 let ψ := StepOneTangentChange.diffeoOpens
   (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) U') η (referenceWindow A U o) (referenceWindow B U' o) hW
 have hψ : ∀ z : referenceWindow A U o,(ψ z).val=η z.val := fun _ => rfl
 obtain ⟨hEq,hCoh,hFresh,hFreshCoh⟩ := hComp o ho
 have hBc := (InvDomainCompanion.isInvDomain_companionAlong hn hB ho).isWellFormed.isCoherent
 have hBWc : (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)).ideal.IsCoherent :=
   isCoherent_pullback contMDiff_subtype_val hBc
 have hTargetFresh : MarkedIdeal.pullback (referenceInclusion B U' o) (GeneralValue.compAt M o (.step T C' π' hπ')) =
     MarkedIdeal.pullback (Subtype.val : referenceWindow B U' o → U')
       (MarkedIdeal.pullback (Subtype.val : U' → Z') (companionOf n B o)) := by
   rw [companion_reference_on_current_window hn M hM (.step T C' π' hπ') hTarget U' ho]
   exact (StepOneTangentChange.pullback_pullback_of_comp hBc
     contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).symm
 refine ⟨ψ,hψ,?_,hFreshCoh⟩
 rw [hFresh,hTargetFresh,hEq]
 exact (StepOneTangentChange.pullback_pullback_of_comp hBWc η.contMDiff contMDiff_subtype_val (fun _ => rfl)).trans
   (StepOneTangentChange.pullback_pullback_of_comp hBWc contMDiff_subtype_val ψ.contMDiff (fun _ => rfl)).symm

theorem exists_actual_fresh_step_one_base_values
 (hn : 0<n) (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
 (T : BlowupTower X Y) {C C' : Set Y} {π : Z → Y} {π' : Z' → Y}
 (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
 (hTarget : IsGeoTestTower M (.step T C' π' hπ')) (V : Opens Y)
 (hC : (Subtype.val : V → Y) ⁻¹' C=(Subtype.val : V → Y) ⁻¹' C') :
 ∃ η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ stepWindow hπ' V,
   (∀ z : stepWindow hπ V,π' (η z).val=π z.val) ∧
   ∀ o : ℕ,1≤o →
     let A := geoTransformAlong M (.step T C π hπ)
     let B := geoTransformAlong M (.step T C' π' hπ')
     ∃ ψ : referenceWindow A (stepWindow hπ V) o ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       referenceWindow B (stepWindow hπ' V) o,
       (∀ z,(ψ z).val=η z.val) ∧
       ∀ p : referenceWindow A (stepWindow hπ V) o,
         referenceInclusion A (stepWindow hπ V) o p∈(GeneralValue.compAt M o (.step T C π hπ)).cosupp →
         Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn 0)
           (GeneralValue.compAt M o (.step T C π hπ)) .refl (referenceInclusion A (stepWindow hπ V) o p)=
         Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn 0)
           (GeneralValue.compAt M o (.step T C' π' hπ')) .refl (referenceInclusion B (stepWindow hπ' V) o (ψ p)) := by
 classical
 obtain ⟨η,hsq,hRefs⟩ := exists_actual_fresh_reference_window hn M hM T hπ hπ' hTarget V hC
 let A := geoTransformAlong M (.step T C π hπ)
 let B := geoTransformAlong M (.step T C' π' hπ')
 let U := stepWindow hπ V
 let U' := stepWindow hπ' V
 have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM _ hTarget
 refine ⟨η,hsq,?_⟩
 intro o ho
 dsimp only
 obtain ⟨ψ,hψ,hrec,hCoh⟩ := hRefs o ho
 let Js := GeneralValue.compAt M o (.step T C π hπ)
 let Jt := GeneralValue.compAt M o (.step T C' π' hπ')
 have hJt : IsInvDomain k Jt := GeneralCompare.isInvDomain_compAt hn ho _ hB
 have hJtMax := GeneralCompare.isMaximalOrderAlong_compAt hn o (.step T C' π' hπ') hB
 have hholS : ∀ x g,Js.ideal.mem x g → HolomorphicAt n g x := by
   intro x g hg
   exact companion_hhol (Z := CMfd.of (n := n) (ordMask A o))
     (MarkedIdeal.pullback (Subtype.val : ordMask A o → Z) A) o hg
 have hclS : ∀ x g,IsInSpanAt (n := n) (Js.ideal.mem x) x g → Js.ideal.mem x g := by
   intro x g hg
   exact companion_span_closed (Z := CMfd.of (n := n) (ordMask A o))
     (MarkedIdeal.pullback (Subtype.val : ordMask A o → Z) A) o hg
 let Os := referenceOriginalOpen A U o
 let Ot := referenceOriginalOpen B U' o
 let es := referenceSwap A U o
 let et := referenceSwap B U' o
 let ν := es.symm.trans (ψ.trans et)
 have hiS : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (referenceInclusion A U o) :=
   BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun z => z.property)
 have hiT : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (referenceInclusion B U' o) :=
   BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun z => z.property)
 have hJtRef : (MarkedIdeal.pullback (referenceInclusion B U' o) Jt).ideal.IsCoherent :=
   isCoherent_pullback hiT hJt.isWellFormed.isCoherent
 have hOpenRecord : MarkedIdeal.pullback (Subtype.val : Os → ordMask A o) Js=
     MarkedIdeal.pullback ν (MarkedIdeal.pullback (Subtype.val : Ot → ordMask B o) Jt) := by
   calc
    MarkedIdeal.pullback (Subtype.val : Os → ordMask A o) Js=
        MarkedIdeal.pullback es.symm (MarkedIdeal.pullback (referenceInclusion A U o) Js) :=
      (marked_pullback_comp_hhol hholS hiS es.symm.contMDiff (fun _ => rfl)).symm
    _ = MarkedIdeal.pullback es.symm (MarkedIdeal.pullback ψ (MarkedIdeal.pullback (referenceInclusion B U' o) Jt)) :=
      congrArg (MarkedIdeal.pullback es.symm) hrec
    _ = MarkedIdeal.pullback (fun w : Os => ψ (es.symm w)) (MarkedIdeal.pullback (referenceInclusion B U' o) Jt) :=
      StepOneTangentChange.pullback_pullback_of_comp hJtRef ψ.contMDiff es.symm.contMDiff (fun _ => rfl)
    _ = MarkedIdeal.pullback (fun w : Os => referenceInclusion B U' o (ψ (es.symm w))) Jt :=
      StepOneTangentChange.pullback_pullback_of_comp hJt.isWellFormed.isCoherent hiT
        (ψ.contMDiff.comp es.symm.contMDiff) (fun _ => rfl)
    _ = MarkedIdeal.pullback ν (MarkedIdeal.pullback (Subtype.val : Ot → ordMask B o) Jt) :=
      (StepOneTangentChange.pullback_pullback_of_comp hJt.isWellFormed.isCoherent
        contMDiff_subtype_val ν.contMDiff (fun _ => rfl)).symm
 refine ⟨ψ,hψ,?_⟩
 intro p hp
 have hz : (es p).val∈Js.cosupp := hp
 have hv := fresh_base_values_from_record (Z := CMfd.of (n := n) (ordMask A o))
   (Z' := CMfd.of (n := n) (ordMask B o)) hn Js Jt hholS hclS hJt hJtMax Os Ot ν hOpenRecord (es p) hz
 have hsrc : (es p).val=referenceInclusion A U o p := rfl
 have htgt : (ν (es p)).val=referenceInclusion B U' o (ψ p) := by
   change (et (ψ (es.symm (es p)))).val=_
   rw [es.symm_apply_apply]
   rfl
 rw [hsrc,htgt] at hv
 exact hv

end Reference
end
end Hironaka.HironakaActualFreshRecursiveValues
