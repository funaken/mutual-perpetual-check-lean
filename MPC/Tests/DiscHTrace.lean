import MPC.Invariants.DiscHTrace
import Lean
/-!
# MPC.Tests.DiscHTrace

Concrete checks for the counting step of Proposition 3.8.

- Moving one member of a set from `a` to `b` changes its size by the two side
  indicators (`card_move_eq`). This is checked with both indicators on and with
  only the source's indicator on.

The periodic theorems (the per-move invariance and the invariance over the
period) are not exercised: no periodic mutual-check trace is constructed. 's
verification shows that periodicity is needed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "disc H trace verification must not import GameSeq"

namespace MPC
namespace DiscHTraceTests

-- {a, c} becomes {b, c}: one member moved, size unchanged.
example : ({(1, 1), (5, 5)} : Finset Pos).card + 1 = ({(0, 0), (5, 5)} : Finset Pos).card + 1 :=
  MoveTrace.card_move_eq {(0, 0), (5, 5)} {(1, 1), (5, 5)} (0, 0) (1, 1) True True
    (by
      intro q
      simp only [Finset.mem_insert, Finset.mem_singleton, and_true]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl ⟨Or.inr rfl, by decide⟩
      · rintro (⟨h | h, hne⟩ | h)
        · exact absurd h hne
        · exact Or.inr h
        · exact Or.inl h)
    (by decide) (by decide)

-- {a, c} becomes {c}: the source leaves and the destination is not counted.
example : ({(5, 5)} : Finset Pos).card + 1 = ({(0, 0), (5, 5)} : Finset Pos).card + 0 := by
  have h := MoveTrace.card_move_eq {(0, 0), (5, 5)} {(5, 5)} (0, 0) (1, 1) True False
    (by
      intro q
      simp only [Finset.mem_insert, Finset.mem_singleton, and_false, or_false]
      constructor
      · rintro rfl
        exact ⟨Or.inr rfl, by decide⟩
      · rintro ⟨h | h, hne⟩
        · exact absurd h hne
        · exact h)
    (by decide) (by decide)
  simp

end DiscHTraceTests
end MPC
