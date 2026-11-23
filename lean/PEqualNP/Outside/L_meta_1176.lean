import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1176

open PEqualNP.CircuitLowerBounds

def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [11, 13]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem monotone2_c : PEqualNP.MetaComplexity.Monotone2 c := by
  intro g hg
  simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem size_c : c.size ≤ 9 := by
  simp [c, Circuit.size]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem eval_c : ∀ x : Fin 8 → Bool,
    c.eval (List.ofFn x) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  decide

end PEqualNP.Outside.L_meta_1176

theorem PEqualNP.Outside.L_meta_1176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1176.c, PEqualNP.Outside.L_meta_1176.monotone2_c,
    PEqualNP.Outside.L_meta_1176.size_c, PEqualNP.Outside.L_meta_1176.eval_c⟩
