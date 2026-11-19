import Hironaka.Analytic.Unibranch.HironakaG11PresReduction
import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison

/-! Different genuine native records give the actual SAME-record terminal
inputs internally. Blueprint FIRST:
hironaka-g1-distinct-native-terminal-normalization.tex.
Whole terminality is required; no common history length or powered native
compression state is assumed. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.HironakaG1DistinctNativeTerminalNormalization
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11StrictTransformTowers HironakaG11PresReduction HironakaG11PresClassTransport
  HironakaG11PresLineStable HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaActualPowerBoundaryExponents HironakaG1OriginalUnequalMarkCanonical
  HironakaOriginalTerminalOverlapComparison BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism CanonicalCentres
  DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {X : SourceReducedComplexSpace} {n : ℕ} {ι : Type*}
  (w : ι → DimEmbedding X n) (raw : ∀i,MarkedIdeal n (Amb w i))

def windowPower (i : ι) (U : Opens (w i).ambient) (e : ℕ) : MarkedIdeal n (CMfd.of (n := n) U) :=
  MarkedIdeal.pullback (Subtype.val : U → (w i).ambient) (powerMarked (raw i) e)

def overlapPower (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (e : ℕ) : MarkedIdeal n (CMfd.of (n := n) U') :=
  MarkedIdeal.pullback Φ (windowPower w raw i U e)

variable (H : ℕ → ℕ) (hrec : ∀i,IsNativeWindowRecord (w i) (raw i) H)
  (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
  (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
  (hadm : mapAdm w i j U U' Φ) (e f : ℕ) (he : 1≤e) (hf : 1≤f)

local notation "P" => windowPower w raw i U e
local notation "B" => windowPower w raw j U' f
local notation "A" => overlapPower w raw i j U U' Φ e

include hrec hadm he hf

/-- Ordinary raw states and the actual overlap derive all initial data.
No equality of the two native marks is needed. -/
theorem overlap_initial_data :
    IsInvDomain n P ∧ IsInvDomain n B ∧ IsInvDomain n A ∧ LocWPEquiv A B ∧
    (A).N=univ ∧ (B).N=univ ∧ (A).E=[] ∧ (B).E=[] ∧ SameCarrierDim A B := by
  have hP : IsInvDomain n P := InvDomainTowerAlong.isInvDomain_pullback_val U
    (powerMarked_isInvDomain (raw i) (hrec i).1 he)
  have hB : IsInvDomain n B := InvDomainTowerAlong.isInvDomain_pullback_val U'
    (powerMarked_isInvDomain (raw j) (hrec j).1 hf)
  have hA : IsInvDomain n A := InvDomainTowerAlong.isInvDomain_pullback Φ hP
  have hL := locWPEquiv_overlap_of_native nativeLineStability
    (hrec i).1 (hrec j).1 (hrec i).2.1 (hrec j).2.1 (hrec i).2.2 (hrec j).2.2
    U U' Φ (mapAdm_carrier hadm) he hf
  have hNA : (A).N=univ := by
    change Φ ⁻¹' ((Subtype.val : U → (w i).ambient) ⁻¹' (raw i).N)=univ
    rw [(hrec i).2.2.2.2.1,preimage_univ,preimage_univ]
  have hNB : (B).N=univ := by
    change (Subtype.val : U' → (w j).ambient) ⁻¹' (raw j).N=univ
    rw [(hrec j).2.2.2.2.1,preimage_univ]
  have hEA : (A).E=[] := by
    change ((raw i).E.map ((Subtype.val : U → (w i).ambient) ⁻¹' ·)).map (Φ ⁻¹' ·)=[]
    rw [(hrec i).2.1];rfl
  have hEB : (B).E=[] := by
    change (raw j).E.map ((Subtype.val : U' → (w j).ambient) ⁻¹' ·)=[]
    rw [(hrec j).2.1];rfl
  exact ⟨hP,hB,hA,hL,hNA,hNB,hEA,hEB,SameCarrierDim.of_N_eq (hNA.trans hNB.symm)⟩

/-- The genuine INITIAL exponent condition is internally derived. -/
theorem normalized_initial_exponents :
    ∀D∈(A).E,∀x∈(A).cosupp,x∈D →
      (B).d*divExpAlong n (A).N (A).ideal D x=(A).d*divExpAlong n (B).N (B).ideal D x := by
  have h := overlap_initial_data w raw H hrec i j U U' Φ hadm e f he hf
  intro D hD
  rw [h.2.2.2.2.2.2.1] at hD
  exact (List.not_mem_nil hD).elim

variable {Y' : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) U') Y')

/-- Actual original canonicality of the independent source record is
equivalent to that of the true target pullback on the SAME history. -/
theorem commonRecord_isCanonical_iff_source :
    IsCanonical A ((canonicalInvariant n).inv A) S ↔
      IsCanonical B ((canonicalInvariant n).inv B) S := by
  have h := overlap_initial_data w raw H hrec i j U U' Φ hadm e f he hf
  exact canonicalInvariant_isCanonical_iff_of_local A B h.2.2.1 h.2.1 h.2.2.2.1
    h.2.2.2.2.2.2.2.2
    (normalized_initial_exponents w raw H hrec i j U U' Φ hadm e f he hf) S

/-- WHOLE geometric resolution, including the entire final cosupport. -/
theorem commonRecord_isGeoResolution_iff_source :
    IsGeoResolution A S ↔ IsGeoResolution B S :=
  ((overlap_initial_data w raw H hrec i j U U' Φ hadm e f he hf).2.2.2.1).wEquiv.isGeoResolution_iff S

/-- The actual SAME-record inputs needed by a native endpoint factory. -/
theorem common_record_terminal_inputs
    (hs : IsCanonical B ((canonicalInvariant n).inv B) S) (hrs : IsGeoResolution B S) :
    IsInvDomain n P ∧ IsCanonical A ((canonicalInvariant n).inv A) S ∧ IsGeoResolution A S :=
  ⟨(overlap_initial_data w raw H hrec i j U U' Φ hadm e f he hf).1,
    (commonRecord_isCanonical_iff_source w raw H hrec i j U U' Φ hadm e f he hf S).mpr hs,
    (commonRecord_isGeoResolution_iff_source w raw H hrec i j U U' Φ hadm e f he hf S).mpr hrs⟩

variable {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
  (hs : IsCanonical (windowPower w raw j U' f)
    ((canonicalInvariant n).inv (windowPower w raw j U' f)) S)
  (ht : IsCanonical (windowPower w raw i U e)
    ((canonicalInvariant n).inv (windowPower w raw i U e)) T)
  (hrs : IsGeoResolution (windowPower w raw j U' f) S)
  (hrt : IsGeoResolution (windowPower w raw i U e) T)

include hs ht hrs hrt

/-- The unique terminal ambient comparison is constructed from the two
actual own-record histories; no common clock or source comparison input. -/
theorem terminal_ambient_existsUnique :
    ∃!η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀y,T.proj (η y)=Φ (S.proj y) := by
  have h := common_record_terminal_inputs w raw H hrec i j U U' Φ hadm e f he hf S hs hrs
  exact original_ambient_terminal_base_existsUnique P h.1 Φ S T h.2.1 ht h.2.2 hrt

def terminalAmbientComparison : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y :=
  (terminal_ambient_existsUnique w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt).choose

theorem terminalAmbientComparison_proj (y : Y') :
    T.proj (terminalAmbientComparison w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt y)=
      Φ (S.proj y) :=
  (terminal_ambient_existsUnique w raw H hrec i j U U' Φ hadm e f he hf S T hs ht hrs hrt).choose_spec.1 y

end
end Hironaka.Analytic.Unibranch.HironakaG1DistinctNativeTerminalNormalization
