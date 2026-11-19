import Hironaka.Resolution.HironakaActualCompactHistoryExtension

/-! Whole finite compact target histories extend to one actual global source
history, with simultaneous carrier/full-boundary tests and an unchanged
original compact footprint. Every target endpoint is covered wholly. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualFiniteCompactHistoryExtension
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan
open HironakaActualGeneratedCurrentHistories HironakaActualAnchoredCurrentHistories
open HironakaActualCompactHistoryExtension HironakaOriginalCompactCosupportGlobalScheduler
open RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n k : ℕ}

/-- Every literal centre of the actual history is compact. -/
def CompactCentres {X : CMfd.{u} n} : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
 | _,.refl => True
 | _,.step T C _ _ => CompactCentres T ∧ IsCompact C

/-- From ONE initial whole-target comparison and compact primary initial
cosupport, construct the entire global source extension of an arbitrary
finite target test history. All marked records use the SAME actual centres,
blowups and current maps. No source centre or future history is supplied. -/
theorem exists_actual_finite_compact_history_extension
 {ι : Type v} (i₀ : ι) {X X' : CMfd.{u} n}
 (A : ι → MarkedIdeal n X) (B : ι → MarkedIdeal n X')
 (hA : ∀i x g,(A i).ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀i,(B i).IsWellFormed)
 (hDomain : IsInvDomain k (B i₀)) (hK : IsCompact (B i₀).cosupp)
 (U₀ : Opens X)
 (φ : CMfd.of (n := n) U₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
   CMfd.of (n := n) (⊤ : Opens X'))
 (hInitial : ∀i,MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i)=
   MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : (⊤ : Opens X') → X') (B i))) :
 ∀{Y' : CMfd.{u} n}(T : BlowupTower X' Y'),(∀i,IsGeoTestTower (B i) T) →
 ∃(Y : CMfd.{u} n)(S : BlowupTower X Y)(U : Opens Y)
   (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
     CMfd.of (n := n) (⊤ : Opens Y')),
   (∀i,IsGeoTestTower (A i) S) ∧ (∀i,Generated (A i) (B i) S T U ⊤ η) ∧
   Anchored U₀ ⊤ φ S T U ⊤ η ∧
   CentresOver ((Subtype.val : U₀ → X) ''
     (φ ⁻¹' ((Subtype.val : (⊤ : Opens X') → X') ⁻¹' (B i₀).cosupp))) S ∧
   CompactCentres S ∧ U=BlowupTowerTransforms.openPreimage S U₀
 | _,.refl,_hTarget => by
   exact ⟨X,.refl,U₀,φ,(fun _ => trivial),
     (fun i => Generated.initial U₀ ⊤ φ (hInitial i)),Anchored.initial,trivial,trivial,rfl⟩
 | _,.step T C' π' hπ',hTarget => by
   obtain ⟨Y,S,U,η,hTest,H,Hanchor,hOver,hCompact,hWindow⟩ :=
     exists_actual_finite_compact_history_extension i₀ A B hA hB hDomain hK U₀ φ hInitial T
       (fun i => (hTarget i).1)
   have hCurCompact := current_cosupport_compact (B i₀) hDomain hK T (hTarget i₀).1
   have hCCompact : IsCompact C' :=
     hCurCompact.1.of_isClosed_subset hπ'.1.1 (hTarget i₀).2.2.1
   obtain ⟨C,Z,π,hπ,hKC,hCU,hAdm,hTrace,Hnext⟩ :=
     exists_actual_compact_source_successor A B hA hB S T U η H hCCompact hπ'
       (fun i => (hTarget i).2)
   let V := BlowupBiholomorphismLift.preOpen hπ U
   let ν := nextComparison hπ hπ' U ⊤ η hTrace
   have HanchorNext : Anchored U₀ ⊤ φ (.step S C π hπ) (.step T C' π' hπ') V ⊤ ν :=
     Anchored.step Hanchor hπ hπ' hTrace
   refine ⟨Z,.step S C π hπ,V,ν,(fun i => ⟨hTest i,hAdm i⟩),Hnext,HanchorNext,
     ⟨hOver,?_⟩,⟨hCompact,hKC⟩,?_⟩
   · intro y hy
     let p : U := ⟨y,hCU hy⟩
     let p₀ : U₀ := ⟨S.proj y,Hanchor.source_mem_initial p⟩
     have hpC : (η p).val∈C' := (Set.ext_iff.mp hTrace p).mpr hy
     have hBase : (φ p₀).val∈(B i₀).cosupp := by
       rw [←Hanchor.projection_square p]
       exact hCurCompact.2 ((hTarget i₀).2.2.1 hpC)
     exact ⟨p₀,hBase,rfl⟩
   · ext z
     change π z∈U ↔ S.proj (π z)∈U₀
     rw [hWindow]
     rfl

end
end Hironaka.HironakaActualFiniteCompactHistoryExtension
