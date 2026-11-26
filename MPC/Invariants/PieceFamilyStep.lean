import MPC.Basic.Lemmas
import MPC.Invariants.PieceFamilyCount
import MPC.Basic.DemoteFamily
/-!
# MPC.Invariants.PieceFamilyStep

The family totals of  never rise along a trace whose drops come from the hand,
and so `PieceCountsAtMostTwo` follows from `DropsFromHand` and
`InitialPieceCountsAtMostTwo`.

For a family `F` that promotion keeps (`PromoteStable`):

- A board move keeps the total (`applyMove_boardMove_familyTotal`): the moved piece
  stays in or out of `F` when it promotes, and a captured piece leaves the board for
  the mover's hand as its original piece, which is in `F` exactly when the
  captured piece is (`PromoteStable.demote_iff`).
- A drop from the hand does not raise it (`applyMove_dropMove_familyTotal`): the
  piece moves from the hand to the board, and a piece it overwrites is lost.
- So along a trace that follows its transitions, with owned sources, distinct
  endpoints and drops from the hand, every state's total is at most state 0's
  (`familyTotal_le_initial`). The board count is at most the total, so with
  `InitialPieceCountsAtMostTwo` every state has at most two bishop-family squares
  and two rook-family squares (`pieceCountsAtMostTwo_of_dropsFromHand`).

-/

namespace MPC

/-- Two functions on squares that agree off two distinct squares `a` and `b`. -/
theorem sum_add_two_eq (f g : Pos → ℕ) (a b : Pos) (hab : a ≠ b)
    (h : ∀ q, q ≠ a → q ≠ b → f q = g q) :
    ∑ q, f q + g a + g b = ∑ q, g q + f a + f b := by
  have hb : b ∈ (Finset.univ : Finset Pos).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have ef := Finset.add_sum_erase (Finset.univ : Finset Pos) f (Finset.mem_univ a)
  have ef' := Finset.add_sum_erase ((Finset.univ : Finset Pos).erase a) f hb
  have eg := Finset.add_sum_erase (Finset.univ : Finset Pos) g (Finset.mem_univ a)
  have eg' := Finset.add_sum_erase ((Finset.univ : Finset Pos).erase a) g hb
  have hrest : ∑ q ∈ ((Finset.univ : Finset Pos).erase a).erase b, f q =
      ∑ q ∈ ((Finset.univ : Finset Pos).erase a).erase b, g q :=
    Finset.sum_congr rfl fun q hq => by
      obtain ⟨hqb, hq'⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqa, _⟩ := Finset.mem_erase.mp hq'
      exact h q hqa hqb
  omega

/-- Two functions on squares that agree off one square `a`. -/
theorem sum_add_one_eq (f g : Pos → ℕ) (a : Pos) (h : ∀ q, q ≠ a → f q = g q) :
    ∑ q, f q + g a = ∑ q, g q + f a := by
  have ef := Finset.add_sum_erase (Finset.univ : Finset Pos) f (Finset.mem_univ a)
  have eg := Finset.add_sum_erase (Finset.univ : Finset Pos) g (Finset.mem_univ a)
  have hrest : ∑ q ∈ (Finset.univ : Finset Pos).erase a, f q =
      ∑ q ∈ (Finset.univ : Finset Pos).erase a, g q :=
    Finset.sum_congr rfl fun q hq => h q (Finset.mem_erase.mp hq).1
  omega

/-- The hand count is the count of either player's hand plus the other's. -/
theorem Board.handFamilyCount_eq (b : Board) (F : PieceType → Prop) [DecidablePred F]
    (p : Player) :
    b.handFamilyCount F =
      Multiset.countP F (b.hand p) + Multiset.countP F (b.hand p.opponent) := by
  unfold Board.handFamilyCount
  cases p
  · rfl
  · exact Nat.add_comm _ _

private theorem countP_add_singleton (F : PieceType → Prop) [DecidablePred F]
    (s : Multiset PieceType) (pt : PieceType) :
    Multiset.countP F (s + {pt}) = Multiset.countP F s + if F pt then 1 else 0 := by
  rw [Multiset.countP_add, ← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero,
    Nat.zero_add]

/-- A board move's hands: a capture adds the captured piece's original type to the
    mover's hand. -/
theorem applyMove_boardMove_hand (bs : BoardState) (src dst : Pos) (promote : Bool)
    (p : Player) :
    (applyMove bs (.boardMove src dst promote)).board.hand p =
      match bs.board.grid dst with
      | some cp =>
        if p = bs.turn then bs.board.hand p + {cp.pieceType.demote} else bs.board.hand p
      | none => bs.board.hand p := by
  rcases h : bs.board.grid dst with _ | cp <;>
    simp [applyMove, h, Board.setGrid, Board.addToHand]

/-- A drop's hands: the dropped type leaves the mover's hand. -/
theorem applyMove_dropMove_hand (bs : BoardState) (pt : PieceType) (dst : Pos) (p : Player) :
    (applyMove bs (.dropMove pt dst)).board.hand p =
      if p = bs.turn then bs.board.hand p - {pt} else bs.board.hand p := by
  simp [applyMove, Board.setGrid, Board.removeFromHand]

/-- A board move adds the captured piece's indicator to the hand count: the captured piece
    enters the hand as its original piece, which a promotion-stable family counts alike. -/
theorem applyMove_boardMove_handFamilyCount (bs : BoardState) (src dst : Pos) (promote : Bool)
    (F : PieceType → Prop) [DecidablePred F] (hF : PromoteStable F) :
    (applyMove bs (.boardMove src dst promote)).board.handFamilyCount F =
      bs.board.handFamilyCount F + familyInd F (bs.board.grid dst) := by
  rw [Board.handFamilyCount_eq _ F bs.turn, Board.handFamilyCount_eq _ F bs.turn,
    applyMove_boardMove_hand, applyMove_boardMove_hand]
  rcases bs.board.grid dst with _ | cp
  · simp [familyInd]
  · dsimp only
    rw [ite_eq_left rfl, ite_eq_right (Player.opponent_ne_self bs.turn), countP_add_singleton]
    simp only [familyInd, hF.demote_iff]
    omega

/-- A drop from the hand takes the dropped piece's indicator off the hand count. -/
theorem applyMove_dropMove_handFamilyCount (bs : BoardState) (pt : PieceType) (dst : Pos)
    (F : PieceType → Prop) [DecidablePred F] (hpt : pt ∈ bs.board.hand bs.turn) :
    (applyMove bs (.dropMove pt dst)).board.handFamilyCount F + (if F pt then 1 else 0) =
      bs.board.handFamilyCount F := by
  rw [Board.handFamilyCount_eq _ F bs.turn, Board.handFamilyCount_eq _ F bs.turn,
    applyMove_dropMove_hand, applyMove_dropMove_hand, ite_eq_left rfl,
    ite_eq_right (Player.opponent_ne_self bs.turn), Multiset.sub_singleton]
  conv_rhs => rw [← Multiset.cons_erase hpt]
  rw [Multiset.countP_cons]
  omega

namespace MoveTrace

/-- The moved piece stays in or out of `F` when it promotes. -/
private theorem familyInd_moved (F : PieceType → Prop) [DecidablePred F] (hF : PromoteStable F)
    (piece : Piece) (promote : Bool) :
    familyInd F (some { piece with pieceType :=
      if promote then piece.pieceType.promote else piece.pieceType }) =
      familyInd F (some piece) := by
  cases promote
  · rfl
  · simp only [familyInd, ite_true]
    by_cases h : F piece.pieceType
    · rw [ite_eq_left ((hF _).mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((hF _).mp h')), ite_eq_right h]

/-- A board move keeps the family total. -/
theorem boardMove_familyTotal (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hd : tr.BoardMoveEndpointsDistinct)
    (F : PieceType → Prop) [DecidablePred F] (hF : PromoteStable F) (i : Fin tr.len)
    (src dst : Pos) (promote : Bool) (hmv : tr.moves i = .boardMove src dst promote) :
    (tr.after i).board.familyTotal F = (tr.before i).board.familyTotal F := by
  have hsd := hd i src dst promote hmv
  obtain ⟨piece, hp, _⟩ := hs i src dst promote hmv
  have hsrc := tr.boardMove_grid_src ht i src dst promote hmv hsd
  have hdst := tr.boardMove_grid_dst ht i src dst promote hmv
  rw [hp] at hdst
  have hsum := sum_add_two_eq (fun q => familyInd F ((tr.after i).board.grid q))
    (fun q => familyInd F ((tr.before i).board.grid q)) src dst hsd
    (fun q hqs hqd => by
      rw [tr.boardMove_grid_other ht i src dst promote q hmv hqs hqd])
  simp only [hsrc, hdst, familyInd_moved F hF, hp] at hsum
  have hhand : (tr.after i).board.handFamilyCount F =
      (tr.before i).board.handFamilyCount F + familyInd F ((tr.before i).board.grid dst) := by
    rw [ht i, hmv]
    exact applyMove_boardMove_handFamilyCount _ src dst promote F hF
  unfold Board.familyTotal
  rw [hhand]
  unfold Board.familyCount
  simp only [familyInd] at hsum
  simp only [familyInd]
  omega

/-- A drop from the hand does not raise the family total. -/
theorem dropMove_familyTotal_le (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hdrop : tr.DropsFromHand) (F : PieceType → Prop) [DecidablePred F] (i : Fin tr.len)
    (pt : PieceType) (dst : Pos) (hmv : tr.moves i = .dropMove pt dst) :
    (tr.after i).board.familyTotal F ≤ (tr.before i).board.familyTotal F := by
  have hdst := tr.dropMove_grid_dst ht i pt dst hmv
  have hsum := sum_add_one_eq (fun q => familyInd F ((tr.after i).board.grid q))
    (fun q => familyInd F ((tr.before i).board.grid q)) dst
    (fun q hq => by
      rw [tr.dropMove_grid_other ht i pt dst q hmv hq])
  simp only [hdst] at hsum
  have hhand : (tr.after i).board.handFamilyCount F + (if F pt then 1 else 0) =
      (tr.before i).board.handFamilyCount F := by
    rw [ht i, hmv]
    exact applyMove_dropMove_handFamilyCount _ pt dst F (hdrop i pt dst hmv)
  unfold Board.familyTotal
  unfold Board.familyCount
  simp only [familyInd] at hsum
  simp only [familyInd] at hhand ⊢
  omega

/-- Every move whose drop comes from the hand keeps the family total or lowers it. -/
theorem familyTotal_succ_le (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hd : tr.BoardMoveEndpointsDistinct)
    (hdrop : tr.DropsFromHand) (F : PieceType → Prop) [DecidablePred F] (hF : PromoteStable F)
    (i : Fin tr.len) :
    (tr.after i).board.familyTotal F ≤ (tr.before i).board.familyTotal F := by
  rcases hmv : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · exact (tr.boardMove_familyTotal ht hs hd F hF i src dst promote hmv).le
  · exact tr.dropMove_familyTotal_le ht hdrop F i pt dst hmv

/-- Every state's family total is at most state 0's. -/
theorem familyTotal_le_initial (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hd : tr.BoardMoveEndpointsDistinct)
    (hdrop : tr.DropsFromHand) (F : PieceType → Prop) [DecidablePred F] (hF : PromoteStable F)
    (k : Fin (tr.len + 1)) :
    (tr.states k).board.familyTotal F ≤ (tr.states 0).board.familyTotal F := by
  induction k using Fin.induction with
  | zero => exact le_rfl
  | succ i ih => exact le_trans (tr.familyTotal_succ_le ht hs hd hdrop F hF i) ih

/-- The piece counts follow from drops from the hand and the initial counts: every
    state has at most two bishop-family squares and two rook-family squares. -/
theorem pieceCountsAtMostTwo_of_transitions (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hd : tr.BoardMoveEndpointsDistinct)
    (hdrop : tr.DropsFromHand) (hinit : tr.InitialPieceCountsAtMostTwo) :
    tr.PieceCountsAtMostTwo := by
  intro k
  constructor
  · rw [tr.bishopHorseSquares_card_eq k]
    exact le_trans (Board.familyCount_le_familyTotal _ _)
      (le_trans (tr.familyTotal_le_initial ht hs hd hdrop _ promoteStable_bishopFamily k) hinit.1)
  · rw [tr.rookDragonSquares_card_eq k]
    exact le_trans (Board.familyCount_le_familyTotal _ _)
      (le_trans (tr.familyTotal_le_initial ht hs hd hdrop _ promoteStable_rookFamily k) hinit.2)

/-- `PieceCountsAtMostTwo` for a periodic mutual-check trace whose drops come from the
    hand and whose first state holds at most two pieces of each family. -/
theorem pieceCountsAtMostTwo_of_dropsFromHand (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (hdrop : tr.DropsFromHand) (hinit : tr.InitialPieceCountsAtMostTwo) :
    tr.PieceCountsAtMostTwo :=
  tr.pieceCountsAtMostTwo_of_transitions hm.transitions hm.sourcesOwned
    (tr.boardMoveEndpointsDistinct_of_oriented hm.sourcesOwned hm.movementRules) hdrop hinit

end MoveTrace
end MPC
