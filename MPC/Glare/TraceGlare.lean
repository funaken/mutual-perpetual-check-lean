import MPC.Basic.Lemmas
import MPC.Trace.CheckOriginTrace
/-!
# MPC.Glare.TraceGlare

The paper's Definition 2.1 (immovable piece) and Definition 2.3 (glare) on
independent traces. Immovability is a history condition: the initial piece's
square is never an endpoint of any move. This differs from constant contents.
A piece glares at its enemy king if it attacks that king's position after every
piece other than itself and the immovable pieces is removed. With the stated transition and safety
classification this gives Lemma 2.4 (a move to a non-glaring square is a
discovered check) and the core of Lemma 2.7 (every drop glares).
No GameSeq, periodicity, or global immovability premise is used.
-/

namespace MPC

/-- A move touches a square when the square is one of its endpoints. -/
def Move.Touches : Move → Pos → Prop
  | .boardMove src dst _, q => q = src ∨ q = dst
  | .dropMove _ dst, q => q = dst

instance (m : Move) (q : Pos) : Decidable (m.Touches q) :=
  match m with
  | .boardMove src dst _ => inferInstanceAs (Decidable (q = src ∨ q = dst))
  | .dropMove _ dst => inferInstanceAs (Decidable (q = dst))

namespace MoveTrace

/-- Definition 2.1 as history: an initial piece whose square no move ever uses as
    a source, destination, or drop square, so it is never moved or captured. -/
def ImmovableAt (tr : MoveTrace) (q : Pos) : Prop :=
  (tr.states 0).board.grid q ≠ none ∧ ∀ i : Fin tr.len, ¬ (tr.moves i).Touches q

instance (tr : MoveTrace) (q : Pos) : Decidable (tr.ImmovableAt q) :=
  inferInstanceAs (Decidable ((tr.states 0).board.grid q ≠ none ∧
    ∀ i : Fin tr.len, ¬ (tr.moves i).Touches q))

/-- The state-`k` board keeping only `pos` and the immovable pieces' squares. -/
def strippedBoard (tr : MoveTrace) (k : Fin (tr.len + 1)) (pos : Pos) : Board :=
  { grid := fun q => if q = pos ∨ tr.ImmovableAt q then (tr.states k).board.grid q else none
    hand := (tr.states k).board.hand }

/-- Definition 2.3: the piece at `pos` attacks its enemy king's supplied position on
    the stripped board. An actual check without removal is included. -/
def GlaresAtEnemyKing (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (pos : Pos) : Prop :=
  ∃ piece : Piece, (tr.states k).board.grid pos = some piece ∧
    attacksOriented (tr.strippedBoard k pos) piece.owner piece.pieceType pos
      (kp k piece.owner.opponent)

/-- An immovable piece's square keeps its initial contents in every state. The
    converse fails: constant contents do not imply an untouched history. -/
theorem immovableAt_grid_eq (tr : MoveTrace) (ht : tr.FollowsTransitions) {q : Pos}
    (h : tr.ImmovableAt q) (k : Fin (tr.len + 1)) :
    (tr.states k).board.grid q = (tr.states 0).board.grid q := by
  induction k using Fin.induction with
  | zero => rfl
  | succ i ih =>
    change (tr.after i).board.grid q = _
    have hn := h.2 i
    rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
    · rw [hm] at hn
      have hs : q ≠ src := fun he => hn (Or.inl he)
      have hd : q ≠ dst := fun he => hn (Or.inr he)
      rw [tr.boardMove_grid_other ht i src dst promote q hm hs hd]
      exact ih
    · rw [hm] at hn
      rw [tr.dropMove_grid_other ht i pt dst q hm hn]
      exact ih

/-- Removing pieces only empties squares, so an actual attack on the enemy king's
    position is a glare. -/
theorem glaresAtEnemyKing_of_attacks (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (pos : Pos) (piece : Piece)
    (hp : (tr.states k).board.grid pos = some piece)
    (ha : attacksOriented (tr.states k).board piece.owner piece.pieceType pos
      (kp k piece.owner.opponent)) :
    tr.GlaresAtEnemyKing kp k pos := by
  have hempty : ∀ q, (tr.states k).board.grid q = none → (tr.strippedBoard k pos).grid q = none := by
    intro q hq
    simp only [strippedBoard]
    split_ifs
    · exact hq
    · rfl
  exact ⟨piece, hp, attacksOriented_mono_of_empty_preserved _ _ hempty _ _ _ _ ha⟩

/-- A destination checker of `kingOwner`'s king glares at it from the destination.
    No ownership premise is needed: the checker belongs to `kingOwner.opponent`. -/
theorem glaresAtEnemyKing_of_destinationChecker (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (k : Fin (tr.len + 1)) (m : Move)
    (kingOwner : Player)
    (h : hasDestinationCheckerOriented (tr.states k).board m kingOwner (kp k kingOwner)) :
    tr.GlaresAtEnemyKing kp k m.destination := by
  obtain ⟨piece, hp, ho, ha⟩ := h
  have he : piece.owner.opponent = kingOwner := by rw [ho, Player.opponent_opponent]
  exact tr.glaresAtEnemyKing_of_attacks kp k _ piece hp (by rw [he]; exact ha)

/-- In a mutual-check trace satisfying the stated transition and safety premises, each move's destination
    piece glares at its enemy king or the move has an unblocked checker. Lemma 2.4
    is the second alternative when the destination does not glare. -/
theorem everyMoveChecksOpponent_glares_or_unblocked (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) :
    tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination ∨
      hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) :=
  ((tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe kp ht hs hk hsafe h0).mp
    hc i).imp_left (tr.glaresAtEnemyKing_of_destinationChecker kp i.succ (tr.moves i) _)

/-- The core of Lemma 2.7: under the same premises every dropped piece glares at
    its enemy king, because a drop has no unblocked checker. -/
theorem dropMove_glares_of_everyMoveChecksOpponent (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (pt : PieceType) (dst : Pos)
    (hm : tr.moves i = .dropMove pt dst) :
    tr.GlaresAtEnemyKing kp i.succ dst := by
  rcases tr.everyMoveChecksOpponent_glares_or_unblocked kp ht hs hk hsafe h0 hc i with hg | hu
  · rw [hm] at hg
    exact hg
  · rw [hm] at hu
    exact False.elim hu

end MoveTrace
end MPC
