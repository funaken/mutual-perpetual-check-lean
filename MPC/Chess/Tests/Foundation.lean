import MPC.Chess
import Lean

open Lean in
run_cmd do
  let env ← getEnv
  for n in [`MPC.Player, `MPC.Pos, `MPC.MoveTrace, `MPC.GameSeq,
      `MPC.mutual_perpetual_check_impossible] do
    if env.contains n then
      throwError "Independent chess foundation imports shogi declaration {n}"

namespace MPC.Chess.Tests

private def singleton (piece : Piece) (src : Pos) : Board :=
  fun p => if p = src then some piece else none

private theorem singleton_check (piece : Piece) (src target : Pos) (owner : Color) :
    inCheck (singleton piece src) owner target ↔
      piece.owner = owner.opponent ∧ attacks (singleton piece src) piece src target := by
  constructor
  · rintro ⟨q, p, hp, ho, ha⟩
    by_cases hq : q = src
    · subst q
      have heq : piece = p := Option.some.inj (by simpa [singleton] using hp)
      subst p
      exact ⟨ho, ha⟩
    · simp [singleton, hq] at hp
  · rintro ⟨ho, ha⟩
    exact ⟨src, piece, by simp [singleton], ho, ha⟩

-- Pawn attacks are diagonal, owner-oriented, and not quiet pawn moves.
example (color : Color) :
    attacks Board.empty ⟨color, .pawn⟩ (3, 3)
      (3 + 1, if color = .white then 4 else 2) ∧
    attacks Board.empty ⟨color, .pawn⟩ (3, 3)
      (3 - 1, if color = .white then 4 else 2) ∧
    ¬ attacks Board.empty ⟨color, .pawn⟩ (3, 3)
      (3, if color = .white then 4 else 2) ∧
    ¬ attacks Board.empty ⟨color, .pawn⟩ (3, 3)
      (4, if color = .white then 2 else 4) := by
  cases color <;> decide

-- All eight knight jumps, for both colors; no shogi knight restriction.
example (color : Color) :
    (∀ q ∈ ([(2, 1), (4, 1), (1, 2), (5, 2),
      (1, 4), (5, 4), (2, 5), (4, 5)] : List Pos),
      attacks Board.empty ⟨color, .knight⟩ (3, 3) q) ∧
    ¬ attacks Board.empty ⟨color, .knight⟩ (3, 3) (5, 5) := by
  cases color <;> decide

-- Queen rays reach the edge in all eight directions, excluding non-alignment.
set_option maxRecDepth 4096 in
example :
    (∀ q ∈ ([(0, 0), (3, 0), (6, 0), (0, 3),
      (7, 3), (0, 6), (3, 7), (7, 7)] : List Pos),
      attacks Board.empty ⟨.white, .queen⟩ (3, 3) q) ∧
    ¬ attacks Board.empty ⟨.white, .queen⟩ (3, 3) (5, 6) := by
  decide

example :
    ¬ attacks (singleton ⟨.black, .pawn⟩ (4, 4)) ⟨.white, .bishop⟩ (3, 3) (7, 7) ∧
    attacks Board.empty ⟨.white, .bishop⟩ (3, 3) (7, 7) ∧
    ¬ attacks (singleton ⟨.white, .pawn⟩ (3, 4)) ⟨.black, .rook⟩ (3, 3) (3, 7) ∧
    attacks Board.empty ⟨.black, .rook⟩ (3, 3) (3, 7) := by
  decide

-- Source/destination occupancy never blocks the open segment. This does not
-- permit capturing one's own piece: that belongs to the move relation.
example (src dst : Pos) (p q : Piece) :
    pathClear (fun r => if r = src then some p else if r = dst then some q else none)
      src dst := by
  intro r hr
  simp [hr.1, hr.2.1]

-- A knight jumps over occupants; a king cannot jump two squares.
example :
    attacks (fun _ => some ⟨.black, .pawn⟩) ⟨.white, .knight⟩ (3, 3) (4, 5) ∧
    attacks Board.empty ⟨.black, .king⟩ (3, 3) (4, 4) ∧
    ¬ attacks Board.empty ⟨.black, .king⟩ (3, 3) (5, 3) := by
  decide

example (piece : Piece) (p : Pos) : ¬ attacks Board.empty piece p p :=
  attacks_not_self _ _ _

example (owner : Color) (target : Pos) : ¬ inCheck Board.empty owner target := by
  simp [inCheck, Board.empty]

example (owner : Color) (src target : Pos) :
    ¬ inCheck (singleton ⟨owner, .queen⟩ src) owner target := by
  rw [singleton_check]
  exact fun h => owner.opponent_ne h.1.symm

-- A present checker can attack an empty target; king presence is separate.
example : inCheck (singleton ⟨.white, .rook⟩ (0, 0)) .black (0, 7) ∧
    singleton ⟨.white, .rook⟩ (0, 0) (0, 7) = none := by
  rw [singleton_check]
  decide

-- Keeping empty squares is insufficient if the checker itself is removed.
example :
    (∀ p, singleton ⟨.white, .rook⟩ (0, 0) p = none → Board.empty p = none) ∧
    inCheck (singleton ⟨.white, .rook⟩ (0, 0)) .black (0, 7) ∧
    ¬ inCheck Board.empty .black (0, 7) := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · rw [singleton_check]; decide
  · simp [inCheck, Board.empty]

example (board : Board) (kp : Color → Pos) (h : KingsWellPlaced board kp) :
    kp .white ≠ kp .black := by
  intro heq
  have := h.positions_injective heq
  contradiction

example (kp : Color → Pos) : ¬ KingsWellPlaced Board.empty kp := by
  intro h
  have := h.king_present .white
  contradiction

example (promotion : Promotion) :
    promotion.pieceType ≠ .king ∧ promotion.pieceType ≠ .pawn := by
  cases promotion <;> decide

-- Empty traces meet recurrence/check conditions, so impossibility must require
-- positive length. King existence still has content at the initial state.
example (initial : Position) (kp : Fin 1 → Color → Pos) :
    (MoveTrace.empty initial).BoardTurnPeriodic ∧
    (MoveTrace.empty initial).EveryMoveChecksOpponent kp := by
  exact ⟨⟨rfl, rfl⟩, fun i => Fin.elim0 i⟩

example (initial : Position) (kp : Color → Pos) :
    (MoveTrace.empty initial).KingsWellPlaced (fun _ => kp) ↔
      KingsWellPlaced initial.board kp := by
  exact ⟨fun h => h (0 : Fin 1), fun h _ => h⟩

-- The trace constructor supports all move forms, without declaring them legal.
example (initial final : Position) (move : Move) :
    (MoveTrace.single initial final move).before (0 : Fin 1) = initial ∧
    (MoveTrace.single initial final move).after (0 : Fin 1) = final ∧
    (MoveTrace.single initial final move).moves (0 : Fin 1) = move := by
  exact ⟨rfl, rfl, rfl⟩

end MPC.Chess.Tests
