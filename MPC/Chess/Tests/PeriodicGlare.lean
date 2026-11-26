import MPC.Chess.PeriodicGlare

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def prefixBoard (c : Color) : Board := fun q =>
  if q = (7, 7) then some ⟨c, .king⟩
  else if q = (4, 0) then some ⟨c.opponent, .king⟩
  else if q = (0, 0) then some ⟨c, .queen⟩
  else if q = (2, 0) then some ⟨c.opponent, .queen⟩ else none

private def prefixKings (c : Color) : Color → Pos := fun o =>
  if o = c then (7, 7) else (4, 0)

private def prefixMove : ℕ → Move
  | 0 => .boardMove (0, 0) (0, 4) none
  | _ => .boardMove (2, 0) (2, 2) none

private def prefixState (c : Color) : ℕ → Position
  | 0 => ⟨prefixBoard c, c, {}, none⟩
  | n + 1 => applyMove (prefixState c n) (prefixMove n)

private def checkingPrefix (c : Color) : MoveTrace where
  len := 2
  states := fun k => prefixState c k.val
  moves := fun i => prefixMove i.val

private theorem prefix_legal (c : Color) : (checkingPrefix c).FollowsLegalMoves := by
  intro i
  refine ⟨prefixKings c, ?_, rfl⟩
  have h : ∀ i : Fin 2, LegalMove (prefixState c i.val) (prefixMove i.val) (prefixKings c) := by
    cases c <;> decide
  exact h i

-- Both starting colors, first/intermediate/last states: the second move makes
-- a non-glaring queen glare. The local strict-decrease theorem is non-vacuous.
example (c : Color) :
    ((checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 0).card = 3 ∧
    ((checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 1).card = 3 ∧
    ((checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 2).card = 2 := by
  cases c <;> decide

example (c : Color) :
    ((checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 2).card <
      ((checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 1).card := by
  apply (checkingPrefix c).nonGlaringSquares_card_succ_lt_of_new_glare
    (fun _ => prefixKings c) (prefix_legal c) (1 : Fin 2) (2, 0) (2, 2) rfl rfl
  · cases c <;> decide
  · cases c <;> decide

-- The first move preserves glare and gives the weak inequality without any
-- periodicity premise. It applies to both endpoint indices of the local lemma.
example (c : Color) :
    ((checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 1).card ≤
      ((checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 0).card := by
  apply (checkingPrefix c).nonGlaringSquares_card_succ_le
    (fun _ => prefixKings c) (prefix_legal c) (0 : Fin 2) (0, 0) (0, 4) rfl rfl
  intro _
  cases c <;> decide

-- Non-glaring occupancy is not absence of an actual check: the blocked queen
-- glares, while the empty square is not counted at all.
example (c : Color) :
    (2, 0) ∈ (checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 0 ∧
    (0, 0) ∉ (checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 0 ∧
    (3, 3) ∉ (checkingPrefix c).nonGlaringSquares (fun _ => prefixKings c) 0 ∧
    ¬ attacks (prefixBoard c) ⟨c, .queen⟩ (0, 0) (4, 0) := by
  cases c <;> decide

-- An unmoved queen keeps its glare when a movable blocker arrives on its line,
-- although its real attack disappears. The general congruence works backwards too.
example (c : Color) :
    ((checkingPrefix c).GlaresAtEnemyKing (fun _ => prefixKings c) 2 (0, 4) ↔
      (checkingPrefix c).GlaresAtEnemyKing (fun _ => prefixKings c) 1 (0, 4)) ∧
    attacks (prefixState c 1).board ⟨c, .queen⟩ (0, 4) (4, 0) ∧
    ¬ attacks (prefixState c 2).board ⟨c, .queen⟩ (0, 4) (4, 0) := by
  refine ⟨(checkingPrefix c).glares_congr (fun _ => prefixKings c) (prefix_legal c) ?_ rfl, ?_⟩
  · cases c <;> rfl
  · cases c <;> decide

-- The prefix checks on both moves but is not periodic; hence its strict count
-- loss is compatible with the periodic constancy theorem.
example (c : Color) :
    (checkingPrefix c).KingsWellPlaced (fun _ => prefixKings c) ∧
    (checkingPrefix c).EveryMoveChecksOpponent (fun _ => prefixKings c) ∧
    ¬ (checkingPrefix c).BoardTurnPeriodic := by
  refine ⟨?_, ?_, ?_⟩
  · change ∀ i : Fin 3, KingsWellPlaced (prefixState c i.val).board (prefixKings c)
    cases c <;> decide
  · change ∀ i : Fin 2, inCheck (prefixState c (i.val + 1)).board
      (prefixState c i.val).turn.opponent (prefixKings c (prefixState c i.val).turn.opponent)
    cases c <;> decide
  · intro h
    have he := congrFun h.1 (0, 0)
    cases c <;> contradiction

-- With no moves all occupied squares are immovable: the blocked queen no
-- longer glares, and the count is four. Constancy includes len = 0.
example (c : Color) :
    ((MoveTrace.empty (prefixState c 0)).nonGlaringSquares (fun _ => prefixKings c) 0).card = 4 := by
  cases c <;> decide

example (pos : Position) (kp : Fin 1 → Color → Pos)
    (hk : (MoveTrace.empty pos).KingsWellPlaced kp) (k l : Fin 1) :
    ((MoveTrace.empty pos).nonGlaringSquares kp k).card =
      ((MoveTrace.empty pos).nonGlaringSquares kp l).card := by
  exact (MoveTrace.empty pos).nonGlaringSquares_card_eq_of_periodic_checks kp
    (fun i => Fin.elim0 i) hk (fun i => Fin.elim0 i) ⟨rfl, rfl⟩ k l

private def kingEscapePosition (c : Color) : Position :=
  ⟨fun q => if q = (7, 7) then some ⟨c, .king⟩
    else if q = (4, 0) then some ⟨c.opponent, .king⟩
    else if q = (0, 0) then some ⟨c, .rook⟩ else none, c.opponent, {}, none⟩

private def kingEscapeMove : Move := .boardMove (4, 0) (4, 1) none

private def kingEscape (c : Color) : MoveTrace :=
  .single (kingEscapePosition c) (applyMove (kingEscapePosition c) kingEscapeMove) kingEscapeMove

private def escapeKings (c : Color) (k : Fin 2) : Color → Pos := fun o =>
  if o = c then (7, 7) else if k.val = 0 then (4, 0) else (4, 1)

-- Fixed king positions are necessary for glare congruence. This legal king
-- escape retains the rook but changes its glare at the enemy king.
example (c : Color) :
    LegalMove (kingEscapePosition c) kingEscapeMove (escapeKings c 0) ∧
    (kingEscape c).KingsWellPlaced (escapeKings c) ∧
    (kingEscape c).GlaresAtEnemyKing (escapeKings c) 0 (0, 0) ∧
    ¬ (kingEscape c).GlaresAtEnemyKing (escapeKings c) 1 (0, 0) ∧
    ((kingEscape c).states 0).board (0, 0) = ((kingEscape c).states 1).board (0, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · cases c <;> decide
  · change ∀ i : Fin 2, KingsWellPlaced ((kingEscape c).states i).board (escapeKings c i)
    cases c <;> decide
  · cases c <;> unfold MoveTrace.GlaresAtEnemyKing <;> decide

end MPC.Chess.Tests
