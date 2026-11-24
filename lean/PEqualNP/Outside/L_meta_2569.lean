import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_2569 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : PEqualNP.CircuitLowerBounds.GateOp) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x5 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5 = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ x2 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x2 + (1 : ℕ) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = x6.eval (List.ofFn x11 ++ [x5.eval [x11 x3, x11 x4]]) := by
  intro x1 x2 x3 x4 x5 x6 h5 hmono hsize
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := ⟨x5, [x3.val, x4.val]⟩ :: x6.gates, output := x6.output }
  refine ⟨C, ?_, ?_, ?_⟩
  · rcases h5 with h5 | h5
    · subst x5
      intro g hg
      simp [C] at hg ⊢
      rcases hg with rfl | hg
      · simp
      · exact hmono g hg
    · subst x5
      intro g hg
      simp [C] at hg ⊢
      rcases hg with rfl | hg
      · simp
      · exact hmono g hg
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size, C, Nat.add_comm] using Nat.succ_le_succ hsize
  · intro x11
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, C]
