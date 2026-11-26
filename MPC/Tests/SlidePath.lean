import MPC.Basic.SlidePath
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.SlidePath

Boundary and occupancy checks for the independent path specification.
These do not assert list order/length/uniqueness or complete move legality.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Slide path verification must not import GameSeq"

namespace MPC

-- All eight directions, each with the maximum eight steps between board edges.
-- The center is included; both endpoints and the point beyond the end are excluded.
example (r : Pos × Pos × Dir)
    (h : r ∈ [((0, 4), (8, 4), (1, 0)), ((8, 4), (0, 4), (-1, 0)),
      ((4, 0), (4, 8), (0, 1)), ((4, 8), (4, 0), (0, -1)),
      ((0, 0), (8, 8), (1, 1)), ((8, 8), (0, 0), (-1, -1)),
      ((0, 8), (8, 0), (1, -1)), ((8, 0), (0, 8), (-1, 1))]) :
    (Pos.dirTo r.1 r.2.1).normalize = r.2.2 ∧
    r.2.1.toInt = (r.1.toInt.1 + 8 * r.2.2.1, r.1.toInt.2 + 8 * r.2.2.2) ∧
    (4, 4) ∈ slidePath r.1 r.2.1 ∧
    r.1.toInt ∉ slidePath r.1 r.2.1 ∧ r.2.1.toInt ∉ slidePath r.1 r.2.1 ∧
    (r.1.toInt.1 + 9 * r.2.2.1, r.1.toInt.2 + 9 * r.2.2.2) ∉ slidePath r.1 r.2.1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

-- Use the public specification to characterize all occupancy tests on a ray.
-- Its endpoint squares do not occur on the right-hand side.
private theorem clear_three (board : Board) :
    pathClear board (0, 4) (3, 4) ↔
      board.grid (1, 4) = none ∧ board.grid (2, 4) = none := by
  have hc := pathClear_iff_of_exact_steps board (0, 4) (3, 4) (1, 0) 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by unfold onBoard; decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by unfold onBoard; decide)
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j
    · exact h1
    · exact h2

example (srcPiece dstPiece : Piece) :
    pathClear
      { grid := fun p => if p = (0, 4) then some srcPiece
          else if p = (3, 4) then some dstPiece else none
        hand := fun _ => ∅ } (0, 4) (3, 4) :=
  (clear_three _).mpr ⟨rfl, rfl⟩

example (board : Board) (piece : Piece) (h : board.grid (2, 4) = some piece) :
    ¬ pathClear board (0, 4) (3, 4) := by
  intro hc
  have h_empty := ((clear_three board).mp hc).2
  rw [h] at h_empty
  cases h_empty

example (src dst : Pos) :
    pathClear { grid := fun _ => none, hand := fun _ => ∅ } src dst := by
  intro q hq hob h
  rfl

-- Adjacent endpoints have no interior squares, regardless of board contents.
example (board : Board) : pathClear board (0, 0) (1, 1) := by
  intro q hq
  rw [show slidePath (0, 0) (1, 1) = [] from by decide] at hq
  simp at hq

example (pos : Pos) : slidePath pos pos = [] := by
  simp [slidePath, Pos.dirTo, Dir.normalize]

-- Equal normalized direction does not supply the required exact alignment.
example : (Pos.dirTo (0, 0) (1, 2)).normalize = (1, 1) ∧
    ¬ ∃ n : ℕ, (Pos.toInt (1, 2)).1 = (Pos.toInt (0, 0)).1 + ↑n * (1 : ℤ) ∧
      (Pos.toInt (1, 2)).2 = (Pos.toInt (0, 0)).2 + ↑n * (1 : ℤ) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨n, hx, hy⟩
  change (1 : ℤ) = 0 + ↑n * 1 at hx
  change (2 : ℤ) = 0 + ↑n * 1 at hy
  omega

end MPC
