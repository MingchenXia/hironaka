import DeJongAlterations.Algebra.NodeFieldUVJetBasis

/-! Count the actual original axis basis and compute every native formal-node jet rank. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFieldUVJetLength

open NodeFieldUVJetBasis NodeGeometricCompletionFormalUV

/-- The zero exponent and the two original positive coordinate-axis strings. -/
def axisExponent (n : ℕ) : Option (Fin 2 × Fin n) → AxisIndex (n + 1)
  | none => ⟨0, by simp⟩
  | some (i, j) => ⟨Finsupp.single i (j.val + 1), by
      constructor
      · simpa only [Finsupp.degree_single] using Nat.succ_lt_succ j.isLt
      · fin_cases i <;> simp⟩

/-- This is an actual whole-index bijection, with the ORIGINAL exponent retained. -/
theorem axisExponent_bijective (n : ℕ) : Function.Bijective (axisExponent n) := by
  constructor
  · rintro (a | ⟨i, j⟩) (b | ⟨k, l⟩) h
    · rfl
    · have hh := congrArg (fun d : AxisIndex (n + 1) => d.val k) h
      simp [axisExponent] at hh
    · have hh := congrArg (fun d : AxisIndex (n + 1) => d.val i) h
      simp [axisExponent] at hh
    · have hd := congrArg Subtype.val h
      have hik : i = k := by
        by_contra hne
        have hh := congrArg (fun d : Fin 2 →₀ ℕ => d i) hd
        simp [axisExponent, hne] at hh
      subst k
      have hjl : j = l := by
        apply Fin.ext
        have hh := congrArg (fun d : Fin 2 →₀ ℕ => d i) hd
        simpa [axisExponent] using hh
      subst l
      rfl
  · intro d
    have hdecomp : d.val = Finsupp.single 0 (d.val 0) + Finsupp.single 1 (d.val 1) := by
      ext i
      fin_cases i <;> simp
    have hdegree : d.val.degree = d.val 0 + d.val 1 := by
      calc
        d.val.degree = (Finsupp.single (0 : Fin 2) (d.val 0) +
          Finsupp.single (1 : Fin 2) (d.val 1)).degree :=
          congrArg Finsupp.degree hdecomp
        _ = d.val 0 + d.val 1 := by simp
    by_cases h0 : d.val 0 = 0
    · by_cases h1 : d.val 1 = 0
      · refine ⟨none, Subtype.ext ?_⟩
        ext i
        fin_cases i <;> simp [axisExponent, h0, h1]
      · have hj : d.val 1 - 1 < n := by
          have hg := d.property.1
          rw [hdegree, h0, zero_add] at hg
          omega
        refine ⟨some (1, ⟨d.val 1 - 1, hj⟩), Subtype.ext ?_⟩
        ext i
        fin_cases i <;> simp [axisExponent, h0, Nat.sub_add_cancel (by omega : 1 ≤ d.val 1)]
    · have h1 : d.val 1 = 0 := d.property.2.resolve_left h0
      have hj : d.val 0 - 1 < n := by
        have hg := d.property.1
        rw [hdegree, h1, add_zero] at hg
        omega
      refine ⟨some (0, ⟨d.val 0 - 1, hj⟩), Subtype.ext ?_⟩
      ext i
      fin_cases i <;> simp [axisExponent, h1, Nat.sub_add_cancel (by omega : 1 ≤ d.val 0)]

def axisIndexEquiv (n : ℕ) : Option (Fin 2 × Fin n) ≃ AxisIndex (n + 1) :=
  Equiv.ofBijective _ (axisExponent_bijective n)

theorem card_axisIndex_succ (n : ℕ) : Fintype.card (AxisIndex (n + 1)) = 2 * n + 1 := by
  rw [← Fintype.card_congr (axisIndexEquiv n)]
  simp [Nat.add_comm]

universe u
variable (K : Type u) [Field K]

/-- The actual native original quotient has its internally counted rank in EVERY characteristic. -/
theorem nativeJet_finrank_succ (n : ℕ) :
    Module.finrank K (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ (n + 1)) = 2 * n + 1 := by
  rw [nativeJet_finrank, card_axisIndex_succ]

theorem nativeJet_finrank_two :
    Module.finrank K (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ 2) = 3 :=
  nativeJet_finrank_succ K 1

theorem nativeJet_finrank_three :
    Module.finrank K (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ 3) = 5 :=
  nativeJet_finrank_succ K 2

end DeJongAlterations.Algebra.NodeFieldUVJetLength
