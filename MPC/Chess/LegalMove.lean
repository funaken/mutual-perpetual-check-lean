import MPC.Chess.Move

/-! King placement is preserved by pseudo-legal moves; after-state placement
is a theorem, not an additional field of `LegalMove`. Final own-king safety is
then checked at the resulting king position. -/

namespace MPC.Chess

def relocateKingPositions (kp : Color → Pos) (src dst : Pos) : Color → Pos :=
  fun c => if kp c = src then dst else kp c

def kingPositionsAfter (kp : Color → Pos) (turn : Color) : Move → Color → Pos
  | .boardMove src dst _ => relocateKingPositions kp src dst
  | .enPassant src dst => relocateKingPositions kp src dst
  | .castle side => relocateKingPositions
      (relocateKingPositions kp (kingHome turn) (castleKingDestination turn side))
      (rookHome turn side) (castleRookDestination turn side)

theorem KingsWellPlaced.ne_of_empty {b : Board} {kp : Color → Pos}
    (hk : KingsWellPlaced b kp) {q : Pos} (hq : b q = none) (c : Color) : q ≠ kp c := by
  intro heq
  have h := hk.king_present c
  rw [← heq, hq] at h
  contradiction

private theorem relocate_destination_king_iff (b : Board) (src dst : Pos)
    (choice : Option Promotion) (c : Color) :
    b.relocate src dst choice dst = some ⟨c, .king⟩ ↔ b src = some ⟨c, .king⟩ := by
  rw [Board.relocate_destination]
  cases b src <;> simp [Piece.promote_eq_king_iff]

theorem KingsWellPlaced.relocate {b : Board} {kp : Color → Pos}
    (hk : KingsWellPlaced b kp) (src dst : Pos) (choice : Option Promotion)
    (hd : ∀ c, dst ≠ kp c) :
    KingsWellPlaced (b.relocate src dst choice) (relocateKingPositions kp src dst) := by
  intro c q
  by_cases hdst : q = dst
  · subst q
    rw [relocate_destination_king_iff, hk c src]
    by_cases hs : kp c = src
    · simp [relocateKingPositions, hs]
    · simp [relocateKingPositions, hs, Ne.symm hs, hd c]
  · by_cases hsrc : q = src
    · subst q
      rw [Board.relocate_source b src dst choice hdst]
      by_cases hs : kp c = src
      · simp [relocateKingPositions, hs, hdst]
      · simp [relocateKingPositions, hs, Ne.symm hs]
    · rw [Board.relocate_other b src dst q choice hsrc hdst, hk c q]
      by_cases hs : kp c = src
      · simp [relocateKingPositions, hs, hsrc, hdst]
      · simp [relocateKingPositions, hs]

theorem KingsWellPlaced.erase {b : Board} {kp : Color → Pos}
    (hk : KingsWellPlaced b kp) (q : Pos) (hq : ∀ c, q ≠ kp c) :
    KingsWellPlaced (b.erase q) kp := by
  intro c p
  by_cases hp : p = q
  · subst p
    simp [Board.erase, hq c]
  · simpa [Board.erase, hp] using hk c p

theorem DestinationAvailable.not_king {b : Board} {turn : Color} {dst : Pos}
    (h : DestinationAvailable b turn dst) (c : Color) : b dst ≠ some ⟨c, .king⟩ := by
  intro heq
  unfold DestinationAvailable at h
  rw [heq] at h
  exact h.2 rfl

theorem KingsWellPlaced.applyMove {pos : Position} {kp : Color → Pos}
    (hk : KingsWellPlaced pos.board kp) {move : Move} (hm : PseudoLegal pos move) :
    KingsWellPlaced (applyMove pos move).board (kingPositionsAfter kp pos.turn move) := by
  cases move with
  | boardMove src dst choice =>
    obtain ⟨p, _, _, _, hd, _, _⟩ := hm
    apply hk.relocate src dst choice
    intro c heq
    apply hd.not_king c
    rw [heq]
    exact hk.king_present c
  | enPassant src dst =>
    obtain ⟨_, hd, _, _, _, hc⟩ := hm
    have hke : KingsWellPlaced (pos.board.erase (enPassantCaptured src dst)) kp := by
      apply hk.erase
      intro c heq
      have h := hk.king_present c
      rw [← heq, hc] at h
      cases h
    exact hke.relocate src dst none (hk.ne_of_empty hd)
  | castle side =>
    have hpath := hm.2.2.2.1
    have hkd : pos.board (castleKingDestination pos.turn side) = none := by
      apply hpath
      cases pos.turn <;> cases side <;> decide
    have hrd : pos.board (castleRookDestination pos.turn side) = none := by
      apply hpath
      cases pos.turn <;> cases side <;> decide
    have hk' := hk.relocate (kingHome pos.turn) (castleKingDestination pos.turn side) none
      (hk.ne_of_empty hkd)
    apply hk'.relocate (rookHome pos.turn side) (castleRookDestination pos.turn side) none
    apply hk'.ne_of_empty
    rw [Board.relocate_other]
    · exact hrd
    · cases pos.turn <;> cases side <;> decide
    · cases pos.turn <;> cases side <;> decide

/-- Local rules, supplied king placement, and safety after the full update.
No assertion of reachability from the standard initial position is included. -/
structure LegalMove (pos : Position) (move : Move) (kp : Color → Pos) : Prop where
  placement : KingsWellPlaced pos.board kp
  movement : PseudoLegal pos move
  ownKingSafe : ¬ inCheck (applyMove pos move).board pos.turn
    (kingPositionsAfter kp pos.turn move pos.turn)

instance (b : Board) (kp : Color → Pos) : Decidable (KingsWellPlaced b kp) :=
  inferInstanceAs (Decidable (∀ c q, b q = some ⟨c, .king⟩ ↔ q = kp c))

instance (pos : Position) (move : Move) (kp : Color → Pos) :
    Decidable (LegalMove pos move kp) :=
  decidable_of_iff (KingsWellPlaced pos.board kp ∧ PseudoLegal pos move ∧
    ¬ inCheck (applyMove pos move).board pos.turn (kingPositionsAfter kp pos.turn move pos.turn))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.placement, h.movement, h.ownKingSafe⟩⟩

theorem LegalMove.kingsWellPlaced_after {pos : Position} {move : Move} {kp : Color → Pos}
    (h : LegalMove pos move kp) :
    KingsWellPlaced (applyMove pos move).board (kingPositionsAfter kp pos.turn move) :=
  h.placement.applyMove h.movement

def LegalTransition (before : Position) (move : Move) (after : Position) : Prop :=
  ∃ kp, LegalMove before move kp ∧ after = applyMove before move

theorem LegalTransition.turn {before after : Position} {move : Move}
    (h : LegalTransition before move after) : after.turn = before.turn.opponent := by
  obtain ⟨_, _, rfl⟩ := h
  rfl

def MoveTrace.FollowsLegalMoves (tr : MoveTrace) : Prop := tr.Follows LegalTransition

theorem MoveTrace.turn_after_of_legal {tr : MoveTrace} (h : tr.FollowsLegalMoves)
    (i : Fin tr.len) : (tr.after i).turn = (tr.before i).turn.opponent :=
  (h i).turn

end MPC.Chess
