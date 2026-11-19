import Hironaka.Resolution.HironakaG4ZeroResidualMonomialSum
import Hironaka.Resolution.HironakaMarkOneGammaBoundedMaxima

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4DivisorExponentIdealMonotone
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong RelativePrincipalizationSpan
  MarkedIdealOperationsAlong RestrictLeCalculus
  MonomialInvariant MonomialCaseAlong HironakaMarkOneGammaBoundedMaxima
  HironakaG4MonomialFamilyInvariant HironakaG4PreparedCentreCoordinates
variable {n : ℕ} {X : CMfd.{u} n}

/-- Inclusion into a coherent larger ideal can only decrease its divisor
exponent at an incident point where the smaller ideal is nonzero along N. -/
theorem divExpAlong_le_of_ideal_le {N H : Set X} {I J : GermIdeal n X} {x : X}
    (hN : IsClosedSubmanifold n N) (hJ : J.IsCoherent) (hI : I.IsCoherent)
    (hLe : I.Le J) (hxN : x ∈ N) (hxH : x ∈ H)
    (hNZ : IsNonzeroAlongAt N I x) :
    divExpAlong n N J H x ≤ divExpAlong n N I H x := by
  let q := divExpAlong n N J H x
  have hJdiv : IsDivNearAlong n N J H q x :=
    isDivNearAlong_divExpAlong (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) x
  have hRestrict := restrictLe_of_le (W := N) hJ hLe
  have hIdiv : IsDivNearAlong n N I H q x := by
    filter_upwards [hJdiv] with y hy hyN hyH
    exact cosupport_subset_of_restrictLe hRestrict q (hy hyN hyH)
  obtain ⟨k,hk⟩ := hN.2 x hxN
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hk
  exact (isDivNearAlong_iff_le_divExpAlong hr hxH hNZ
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)).mp hIdiv
/-- A uniform bound on all original old rows supplies the shaped Gamma
bound for any selected nonempty zero mask, without any future hypothesis. -/
theorem zero_mask_gamma_bound_of_uniform_rows (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : NormalCrossings.IsSNCDivisor n (old ++ born))
    (hTr : NormalCrossings.IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let I : GermIdeal n X := ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,I,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    (∃ B,∀ x ∈ N,∀ i j,A x i j ≤ B) →
    ∃ v : Val,(ofLex v).1=n-1 ∧
      ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val) := by
  dsimp only
  intro hTau hNu hBound
  obtain ⟨B,hB⟩ := hBound
  obtain ⟨hc,hNZ,hMono,hWF,_hCos,_hRows,_hCentre,_hLocal⟩ :=
    HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_geometry
      hn hN hE hTr hdense P hP hTau hNu
  obtain ⟨i,hi⟩ := hP
  have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
  have hcD : (oldMonomialPart N old born i).IsCoherent := hParts.2.2.2.2.1
  have hLe : (oldMonomialPart N old born i).Le
      (⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(oldMonomialPart N old born i).mem x f) x g⟩ : GermIdeal n X) := by
    intro x g hg
    change IsInSpanAt (n := n) (fun f => ∃ k ∈ P,(oldMonomialPart N old born k).mem x f) x g
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨i,hi,hg⟩
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcD hg)
  apply markOne_gamma_bound_of_incident_exponents hn _ hWF hNZ hMono rfl B
  intro x hx j hj
  have hxN := hx.1
  exact (divExpAlong_le_of_ideal_le hN hc hcD hLe hxN hj (hParts.2.2.2.2.2.1 x hxN)).trans
    (hB x hxN i j)

end
end Hironaka.HironakaG4DivisorExponentIdealMonotone
