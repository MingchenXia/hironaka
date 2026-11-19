import Hironaka.Resolution.HironakaActualRawRecordPullbacks
import Hironaka.Blowup.BlowupTowerIsomorphism

/-! Actual next comparisons for DIFFERENT predecessor spaces and records.
The preceding local entire-record comparison and actual centre traces are
geometric inputs. Blowup uniqueness constructs the next map, and transform
naturality proves its entire-record identity; no numerical value equality,
source admissibility, global source coherence, or supplied upper map is used. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualDifferentHistoryRecords
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
open MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
open MarkedIdealRestrictOpen BlowupRestrictOpen BlowupUniqueness
open HironakaActualRawRecordPullbacks
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- Actual blowups over DIFFERENT predecessor spaces have a unique next
comparison when the preceding comparison matches their actual centre traces. -/
theorem existsUnique_next_comparison
 {C : Set X} {C' : Set X'} {π : Y → X} {π' : Y' → X'}
 (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
 (U : Opens X) (U' : Opens X')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hC : η ⁻¹' ((Subtype.val : U' → X') ⁻¹' C') = (Subtype.val : U → X) ⁻¹' C) :
 ∃! χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ' U'),
   ∀ p, π' (χ p).val = (η ⟨π p.val,p.property⟩).val := by
 let r := BlowupBiholomorphismLift.restrictMap hπ U
 let r' := BlowupBiholomorphismLift.restrictMap hπ' U'
 have hs := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ U
 have ht := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ' U'
 have ht' := isBlowupAlong_comp_inverse η.contMDiff η.symm.contMDiff
   η.apply_symm_apply η.symm_apply_apply ht
 rw [hC] at ht'
 obtain ⟨e,f,he,hf,hsq,_hback,hfe,hef⟩ := exists_biholomorphism_over hs ht'
 let χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ' U') :=
   ⟨⟨e,f,congrFun hfe,congrFun hef⟩,he,hf⟩
 have hχ : ∀ p,π' (χ p).val = (η ⟨π p.val,p.property⟩).val := by
   intro p
   have h1 : η.symm (r' (χ p)) = r p := congrFun hsq p
   have h2 : r' (χ p) = η (r p) := by rw [←h1,η.apply_symm_apply]
   exact congrArg Subtype.val h2
 refine ⟨χ,hχ,?_⟩
 intro θ hθ
 obtain ⟨g,_hg,hUnique⟩ := existsUnique_comparison hs ht'
 have hθsq : (η.symm ∘ r') ∘ θ = r := by
   funext p
   have h1 : r' (θ p) = η (r p) := Subtype.ext (hθ p)
   change η.symm (r' (θ p)) = r p
   rw [h1,η.symm_apply_apply]
 have hθg := hUnique θ ⟨θ.contMDiff,hθsq⟩
 have hχg := hUnique χ ⟨χ.contMDiff,hsq⟩
 apply Diffeomorph.ext
 exact congrFun (hθg.trans hχg.symm)

/-- The actual next map and its ENTIRE post-record comparison are produced
from the preceding local records and centre traces. Source and target may
be endpoints of different actual histories. All ordered old and born labels
are retained in the literal marked-record equality. -/
theorem exists_next_whole_records
 (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hholA : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : B.IsWellFormed)
 {C : Set X} {C' : Set X'} (hAdm' : B.IsAdmissibleCentre C')
 {π : Y → X} {π' : Y' → X'}
 (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
 (U : Opens X) (U' : Opens X')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → X) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') B))
 (hC : η ⁻¹' ((Subtype.val : U' → X') ⁻¹' C') = (Subtype.val : U → X) ⁻¹' C) :
 ∃ χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ' U'),
   (∀ p,π' (χ p).val = (η ⟨π p.val,p.property⟩).val) ∧
   MarkedIdeal.pullback (Subtype.val : BlowupBiholomorphismLift.preOpen hπ U → Y)
       (A.geoTransform C π) =
     MarkedIdeal.pullback χ
       (MarkedIdeal.pullback (Subtype.val : BlowupBiholomorphismLift.preOpen hπ' U' → Y')
         (B.geoTransform C' π')) := by
 obtain ⟨χ,hχ,_huniq⟩ := existsUnique_next_comparison hπ hπ' U U' η hC
 let S : BlowupTower X Y := .step .refl C π hπ
 let T : BlowupTower X' Y' := .step .refl C' π' hπ'
 let BU := MarkedIdeal.pullback (Subtype.val : U' → X') B
 have hBU := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hB U'
 have ht : IsGeoTestTower B T := ⟨trivial,hAdm'⟩
 have hiso : IsTowerIso η (restrict U S) (restrict U' T) χ := by
   refine IsTowerIso.step
     (X := CMfd.of (n := n) U') (X' := CMfd.of (n := n) U)
     (Y := CMfd.of (n := n) U') (Y' := CMfd.of (n := n) U)
     (Z' := CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ U))
     (Z := CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hπ' U'))
     (π' := BlowupBiholomorphismLift.restrictMap hπ U)
     (π := BlowupBiholomorphismLift.restrictMap hπ' U') .refl
     (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ U)
     (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ' U') χ
     (fun p => Subtype.ext (hχ p)) hC
 have hNat := IsTowerIso.geoTransformAlong_eq
   (X := CMfd.of (n := n) U') (X' := CMfd.of (n := n) U)
   (𝔪 := BU) (T' := restrict U S) (T := restrict U' T) (χ := χ)
   η hBU.isClosedSubmanifold_N hBU.isCoherent hiso
   (isGeoTestTower_restrict U' hB.isClosedSubmanifold_N hB.isCoherent T ht)
 rw [←hrec] at hNat
 have hs := geoTransform_pullback_val_of_hhol hholA hπ U
   (BlowupBiholomorphismLift.preOpen hπ U).isOpen
 have hholB : ∀ x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have htRec := geoTransform_pullback_val_of_hhol hholB hπ' U'
   (BlowupBiholomorphismLift.preOpen hπ' U').isOpen
 exact ⟨χ,hχ,hs.symm.trans (hNat.trans (congrArg (fun Q => MarkedIdeal.pullback χ Q) htRec))⟩

end
end Hironaka.HironakaActualDifferentHistoryRecords
