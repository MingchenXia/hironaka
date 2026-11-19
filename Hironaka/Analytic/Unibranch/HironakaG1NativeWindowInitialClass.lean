import Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageCentreIdeal
import Hironaka.Analytic.Unibranch.OriginalNativeShadowInvariantCentre

/-! TRUE INITIAL class fields of the actual chosen native window powers.
Blueprint FIRST: hironaka-g1-native-window-initial-class.tex.
Raw native state is not falsely inferred for its powered record.
-/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.HironakaG1NativeWindowInitialClass
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers HironakaG11PresReduction HironakaG11PresClassTransport
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaActualPowerBoundaryExponents
  HironakaG1CanonicalStageCentreIdeal BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism OriginalNativeHSPhaseHistory OriginalNativeHSCompactShadowWindows

/-- All FIVE initial fields are derived from ordinary RAW native state,
actual positive powers/common marks and actual admissible overlap maps. -/
theorem initialClassData_of_native_powers {X : SourceReducedComplexSpace} {N : ℕ} {ι : Type*}
    (w : ι → DimEmbedding X N) (raw : ∀i,MarkedIdeal N (Amb w i)) (H : ℕ → ℕ)
    (hrec : ∀i,IsNativeWindowRecord (w i) (raw i) H)
    (e : ι → ℕ) (he : ∀i,1≤e i)
    (hd : ∀i j,(powerMarked (raw i) (e i)).d=(powerMarked (raw j) (e j)).d) :
    InitialClassData w (fun i=>powerMarked (raw i) (e i)) := by
  intro i j U U' Φ hadm
  let A:=MarkedIdeal.pullback Φ
    (MarkedIdeal.pullback (Subtype.val : U → (w i).ambient) (powerMarked (raw i) (e i)))
  let B:=MarkedIdeal.pullback (Subtype.val : U' → (w j).ambient) (powerMarked (raw j) (e j))
  have hL:=locWPEquiv_overlap_of_native nativeLineStability
    (hrec i).1 (hrec j).1 (hrec i).2.1 (hrec j).2.1 (hrec i).2.2 (hrec j).2.2
    U U' Φ (mapAdm_carrier hadm) (he i) (he j)
  have hNi : (raw i).N=univ:=(hrec i).2.2.2.2.1
  have hNj : (raw j).N=univ:=(hrec j).2.2.2.2.1
  have hNA : A.N=univ:=by
    change Φ ⁻¹' ((Subtype.val : U → (w i).ambient) ⁻¹' (raw i).N)=univ
    rw [hNi,preimage_univ,preimage_univ]
  have hNB : B.N=univ:=by
    change (Subtype.val : U' → (w j).ambient) ⁻¹' (raw j).N=univ
    rw [hNj,preimage_univ]
  have hEA : A.E=[]:=by
    change ((raw i).E.map ((Subtype.val : U → (w i).ambient) ⁻¹' ·)).map (Φ ⁻¹' ·)=[]
    rw [(hrec i).2.1];rfl
  have hEB : B.E=[]:=by
    change (raw j).E.map ((Subtype.val : U' → (w j).ambient) ⁻¹' ·)=[]
    rw [(hrec j).2.1];rfl
  exact ⟨hL,hd i j,hEA.trans hEB.symm,SameCarrierDim.of_N_eq (hNA.trans hNB.symm),expAgree_of_nil hEA⟩

/-- LITERAL chosen common powers of the genuine ordinary phase windows;
all exponent positivity and common marks are computed by that family. -/
theorem phase_windows_initialClassData {X : SourceReducedComplexSpace} {H : ℕ → ℕ} {N : ℕ}
    (W : OriginalNativeHSPhaseHistory.Windows X H N) :
    InitialClassData W.window W.record :=
  initialClassData_of_native_powers W.window W.rawRecord H W.native W.exponent W.exponent_pos
    (fun i j=>(W.record_mark i).trans (W.record_mark j).symm)

/-- LITERAL original compact-shadow family, BEFORE any nested manifold
retyping; no false full-cover or powered NativeHSState assertion. -/
theorem shadow_windows_initialClassData {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    (M : OriginalNativeHSCompactShadowWindows.Maximum X K) (hK : IsCompact K) :
    InitialClassData (M.windows hK).window (OriginalNativeShadowInvariantCentre.record M hK) :=
  initialClassData_of_native_powers (M.windows hK).window (M.windows hK).record _
    (M.windows hK).native (OriginalNativeShadowInvariantCentre.exponent M hK)
    (OriginalNativeShadowInvariantCentre.exponent_pos M hK)
    (fun i j=>(OriginalNativeShadowInvariantCentre.record_mark M hK i).trans
      (OriginalNativeShadowInvariantCentre.record_mark M hK j).symm)

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeWindowInitialClass
