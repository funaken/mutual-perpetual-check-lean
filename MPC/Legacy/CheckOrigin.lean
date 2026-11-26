import MPC.Basic.Lemmas
import MPC.Legacy.MoveCompatibility
import MPC.Legacy.MoveTrace
import MPC.Legacy.CheckCompatibility
import MPC.Trace.CheckOriginTrace
/-!
# MPC.Legacy.CheckOrigin

Relate the oriented check-origin classification to the legacy `isDirectCheck` and
`isDiscoveredCheck`. The legacy `canMoveTo` reads step tables in sente's
orientation for both owners and slide tables in the opponent's orientation, so it
agrees with `canMoveToOriented` only for y-symmetric pieces, or for sente's
non-lance pieces. The correspondence is stated under that compatibility; the
legacy definitions and their consumers are left unchanged.
-/

namespace MPC

/-- Piece types whose legacy movement predicate agrees with the owner-oriented one:
    y-symmetric tables for either owner, and every non-lance piece for sente. -/
def PieceType.LegacyCompatible (pt : PieceType) (owner : Player) : Prop :=
  pt = .king ∨ pt = .rook ∨ pt = .bishop ∨ pt = .dragon ∨ pt = .horse ∨
    (owner = .sente ∧ pt ≠ .lance)

-- Transforming both sides of membership cancels the owner adjustment.
private theorem mem_map_forPlayer_iff (d : Dir) (owner : Player) (dirs : List Dir) :
    d.forPlayer owner ∈ dirs.map (Dir.forPlayer · owner) ↔ d ∈ dirs := by
  have hi : Function.Involutive (fun d : Dir => d.forPlayer owner) := by
    intro d
    cases owner <;> simp [Dir.forPlayer, Dir.flip]
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact hi.injective heq ▸ hx
  · intro hd
    exact ⟨d, hd, rfl⟩

-- Every slide table except the lance's is invariant under y reflection.
private theorem mem_slideDirs_of_ne_lance {pt : PieceType} (h : pt ≠ .lance)
    (owner : Player) (d : Dir) :
    d ∈ pt.slideDirs.map (Dir.forPlayer · owner) ↔ d ∈ pt.slideDirs := by
  cases pt <;> cases owner <;>
    simp_all [PieceType.slideDirs, Dir.forPlayer, Dir.flip, or_comm, or_left_comm]

/-- Apart from the lance, the legacy predicate does not depend on the owner: its
    step test ignores the owner and the other slide tables are symmetric. -/
theorem canMoveTo_owner_irrelevant_of_ne_lance (board : Board) (first second : Player)
    (pt : PieceType) (src dst : Pos) (h : pt ≠ .lance) :
    canMoveTo board first pt src dst ↔ canMoveTo board second pt src dst := by
  simp only [canMoveTo, mem_map_forPlayer_iff, mem_slideDirs_of_ne_lance h]

/-- Legacy and oriented attacks agree for compatible piece types. -/
theorem attacksOriented_iff_attacks_of_legacyCompatible (board : Board) (owner : Player)
    (pt : PieceType) (src dst : Pos) (h : pt.LegacyCompatible owner) :
    attacksOriented board owner pt src dst ↔ attacks board owner pt src dst := by
  rcases h with h | h | h | h | h | ⟨rfl, hne⟩
  · exact attacksOriented_iff_attacks_of_symmetric board owner pt src dst (Or.inl h)
  · exact attacksOriented_iff_attacks_of_symmetric board owner pt src dst (Or.inr (Or.inl h))
  · exact attacksOriented_iff_attacks_of_symmetric board owner pt src dst
      (Or.inr (Or.inr (Or.inl h)))
  · exact attacksOriented_iff_attacks_of_symmetric board owner pt src dst
      (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact attacksOriented_iff_attacks_of_symmetric board owner pt src dst
      (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · have hs (d : Dir) : d ∈ pt.stepDirs.map (Dir.forPlayer · .sente) ↔ d ∈ pt.stepDirs := by
      simp [Dir.forPlayer]
    simp only [attacksOriented, attacks, canMoveToOriented, canMoveTo, mem_map_forPlayer_iff, hs,
      mem_slideDirs_of_ne_lance hne]

/-- With an owned board-move source and compatible mover pieces, the legacy
    direct check is exactly the destination-checker predicate. For drops, the
    legacy owner quantifier is harmless because compatible types are not lances. -/
theorem applyMove_isDirectCheck_iff_destinationChecker (bs : BoardState) (move : Move)
    (target : Pos)
    (hs : ∀ src dst promote, move = .boardMove src dst promote →
      ∃ piece : Piece, bs.board.grid src = some piece ∧ piece.owner = bs.turn)
    (hc : ∀ pos piece, (applyMove bs move).board.grid pos = some piece →
      piece.owner = bs.turn → piece.pieceType.LegacyCompatible piece.owner) :
    isDirectCheck (applyMove bs move).board move target ↔
      hasDestinationCheckerOriented (applyMove bs move).board move bs.turn.opponent target := by
  cases move with
  | boardMove src dst promote =>
    obtain ⟨moving, hm, hmo⟩ := hs src dst promote rfl
    have hown : ∀ piece, (applyMove bs (.boardMove src dst promote)).board.grid dst = some piece →
        piece.owner = bs.turn := by
      intro piece hp
      rw [applyMove_boardMove_grid_dst, hm] at hp
      cases hp
      exact hmo
    constructor
    · rintro ⟨piece, hp, ha⟩
      have ho := hown piece hp
      exact ⟨piece, hp, ho.trans (Player.opponent_opponent _).symm,
        (attacksOriented_iff_attacks_of_legacyCompatible _ _ _ _ _ (hc dst piece hp ho)).mpr ha⟩
    · rintro ⟨piece, hp, _, ha⟩
      exact ⟨piece, hp, (attacksOriented_iff_attacks_of_legacyCompatible _ _ _ _ _
        (hc dst piece hp (hown piece hp))).mp ha⟩
  | dropMove pt dst =>
    have hp : (applyMove bs (.dropMove pt dst)).board.grid dst = some ⟨bs.turn, pt⟩ :=
      applyMove_dropMove_grid_dst bs pt dst
    have hcp : pt.LegacyCompatible bs.turn := hc dst ⟨bs.turn, pt⟩ hp rfl
    have hne : pt ≠ .lance := by
      rcases hcp with h | h | h | h | h | ⟨_, h⟩ <;> first | exact h | (subst h; decide)
    constructor
    · rintro ⟨o, ha⟩
      exact ⟨⟨bs.turn, pt⟩, hp, (Player.opponent_opponent _).symm,
        (attacksOriented_iff_attacks_of_legacyCompatible _ _ _ _ _ hcp).mpr
          ((canMoveTo_owner_irrelevant_of_ne_lance _ o bs.turn pt dst target hne).mp ha)⟩
    · rintro ⟨piece, hp', _, ha⟩
      have he : piece = ⟨bs.turn, pt⟩ := Option.some.inj (hp'.symm.trans hp)
      subst he
      exact ⟨bs.turn, (attacksOriented_iff_attacks_of_legacyCompatible _ _ _ _ _ hcp).mp ha⟩

/-- From an unchecked target, the legacy discovered check is exactly the
    unblocked checker when the mover's pieces are compatible. Drops are `False`
    on both sides without any premise. -/
theorem applyMove_isDiscoveredCheck_iff_unblockedChecker (bs : BoardState) (move : Move)
    (target : Pos) (hs : move.SourcePresent bs.board)
    (hb : ¬ inCheckOriented bs.board bs.turn.opponent target)
    (hc : ∀ pos piece, (applyMove bs move).board.grid pos = some piece →
      piece.owner = bs.turn → piece.pieceType.LegacyCompatible piece.owner) :
    isDiscoveredCheck (applyMove bs move).board move bs.turn target ↔
      hasUnblockedCheckerOriented bs.board (applyMove bs move).board move
        bs.turn.opponent target := by
  cases move with
  | boardMove src dst promote =>
    rw [← applyMove_otherChecker_iff_unblockedChecker bs (.boardMove src dst promote)
      bs.turn.opponent target hs hb]
    constructor
    · rintro ⟨pos, hd, piece, hp, ho, ha⟩
      exact ⟨pos, hd, piece, hp, ho.trans (Player.opponent_opponent _).symm,
        (attacksOriented_iff_attacks_of_legacyCompatible _ _ _ _ _ (hc pos piece hp ho)).mpr ha⟩
    · rintro ⟨pos, hd, piece, hp, ho, ha⟩
      have ho' : piece.owner = bs.turn := ho.trans (Player.opponent_opponent _)
      exact ⟨pos, hd, piece, hp, ho',
        (attacksOriented_iff_attacks_of_legacyCompatible _ _ _ _ _ (hc pos piece hp ho')).mp ha⟩
  | dropMove pt dst => exact Iff.rfl

/-- Every mover-owned piece on each after-state board is legacy compatible. -/
def MoveTrace.MoverPiecesLegacyCompatible (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (pos : Pos) (piece : Piece), (tr.after i).board.grid pos = some piece →
    piece.owner = (tr.before i).turn → piece.pieceType.LegacyCompatible piece.owner

/-- Under the stated transition and safety premises and compatible mover pieces, every move checks the
    opponent iff each move is a legacy direct or legacy discovered check. -/
theorem MoveTrace.everyMoveChecksOpponent_iff_legacy_direct_or_discovered (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.MoverPiecesLegacyCompatible) :
    tr.EveryMoveChecksOpponent kp ↔ ∀ i : Fin tr.len,
      isDirectCheck (tr.after i).board (tr.moves i) (kp i.succ (tr.before i).turn.opponent) ∨
      isDiscoveredCheck (tr.after i).board (tr.moves i) (tr.before i).turn
        (kp i.succ (tr.before i).turn.opponent) := by
  rw [tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe kp ht hs hk hsafe h0]
  refine forall_congr' fun i => ?_
  have hb := tr.before_opponent_not_inCheck kp ht hsafe h0 i
  rw [← tr.opponentKingPos_succ_eq kp ht hs hk i] at hb
  have hci : ∀ pos piece, (applyMove (tr.before i) (tr.moves i)).board.grid pos = some piece →
      piece.owner = (tr.before i).turn → piece.pieceType.LegacyCompatible piece.owner := by
    rw [← ht i]
    exact hc i
  rw [ht i, applyMove_isDirectCheck_iff_destinationChecker (tr.before i) (tr.moves i) _
      (fun src dst promote hm => hs i src dst promote hm) hci,
    applyMove_isDiscoveredCheck_iff_unblockedChecker (tr.before i) (tr.moves i) _
      (tr.sourcePresent_of_boardMoveSourcesOwned hs i) hb hci]

end MPC
