import Hanabi.Game
import Mathlib.Logic.Equiv.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


open Encodable (sortedUniv)
open List

namespace Game

/-- A quite general hanabi configuration.
This encodes most variants on hanab.live.
It encodes black powder by renumbering the black cards
(and by modifying `touches` so that rank clues still touch the correct cards). -/
structure HanabiConfig where
  /-- Number of players -/
  players : ℕ
  [neZero_players : NeZero players]
  /-- Suits of cards -/
  Suit : Type
  [fintypeSuit : Fintype Suit]
  [encodableSuit : Encodable Suit]
  [decidableEqSuit : DecidableEq Suit]
  [inhabitedSuit : Inhabited Suit]
  /-- Number of ranks. We count ranks from 0 to `ranks - 1` -/
  ranks : ℕ := 5
  [neZero_ranks : NeZero ranks]
  /-- Number of copies of a particular card -/
  numCards : Suit × Fin ranks → ℕ
  /-- Possible clues -/
  Clue : Type
  /-- Does a clue touch a card? -/
  touches : Clue → Suit × Fin ranks → Bool
  handSize : ℕ
  [neZero_handSize : NeZero handSize]
  /-- number of strikes until the game strikes out -/
  strikes : ℕ := 3
  maxClues : ℕ := 8

namespace HanabiConfig

attribute [instance] fintypeSuit encodableSuit decidableEqSuit inhabitedSuit
  neZero_ranks neZero_players neZero_handSize

variable (C : HanabiConfig)

abbrev Rank : Type := Fin C.ranks
def maxRank : C.Rank := ⟨C.ranks - 1, by have := C.neZero_ranks.out; grind⟩

abbrev Card : Type := C.Suit × C.Rank

abbrev Player : Type := Fin C.players

def standardDeck : List C.Card :=
  sortedUniv C.Suit |>.flatMap
    fun c ↦ finRange C.ranks |>.flatMap
      fun r ↦ replicate (C.numCards (c, r)) (c, r)

/-- The public information -/
structure PublicState where
  /-- play piles. -/
  progress : C.Suit → ℕ
  /-- discard (head is most recently discarded) -/
  discard : List C.Card
  strikes : ℕ
  /-- Number of turns left once the deck is empty. -/
  extraTurns : Option ℕ
  /-- Current player -/
  current : C.Player
  clues : ℕ
  /-- Each card has a list of received clues (true: positive info, false: negative info)
  newest first -/
  cardInfo : C.Player → List (List (C.Clue × Bool))
  /-- Card played, discarded or misplayed last turn -/
  lastCard : Option C.Card
  /-- The last turn was a misplay -/
  wasMisplay : Bool
  deriving Inhabited

/-- The data in a game state -/
structure StateData extends C.PublicState where
  /-- remaining deck (head is top). -/
  deck : List C.Card
  /-- hand cards (head is newest). -/
  hand : C.Player → List C.Card
  deriving Inhabited

/-- A correct hanabi game state (WIP) -/
structure State extends C.StateData where
  progress_le (c : C.Suit) : progress c ≤ C.ranks
  deck_eq_nil : extraTurns.isSome ↔ deck = []
  length_hand_eq (p : C.Player) (h : extraTurns.isNone) : (hand p).length = C.handSize
  length_hand_or (p : C.Player) : (hand p).length = C.handSize ∨ (hand p).length = C.handSize - 1
  strikes_le : strikes ≤ C.strikes
  isPerm : C.standardDeck.isPerm <|
    deck ++ discard ++ (finRange C.players).flatMap hand ++
      (sortedUniv C.Suit).flatMap
        fun c ↦ (finRange (progress c)).map
        fun r ↦ (c, r.castLE (progress_le c))

inductive Action where
  | play (n : Fin C.handSize)
  | discard (n : Fin C.handSize)
  | clue (p : C.Player) (c : C.Clue)

instance : Inhabited C.Action := ⟨.discard default⟩

/-- The information of one player -/
structure Info extends C.PublicState where
  /-- Which player am I -/
  me : C.Player
  /-- hand cards of the other players. -/
  hand (p : C.Player) (h : p ≠ me) : List C.Card


namespace PublicState
variable {C}
variable (S : C.PublicState)

def isGameEnd : Bool :=
  S.strikes = C.strikes ∨ S.extraTurns = some 0 ∨ S.progress = C.ranks

def score : ℕ :=
  if S.strikes = C.strikes then 0 else ∑ c : C.Suit, S.progress c

/-- Info about card `n` in `p`'s hand -/
def info (p : C.Player) (n : ℕ) : List (C.Clue × Bool) :=
  (S.cardInfo p)[n]?.getD []

/-- Positive clues about card `n` in `p`'s hand -/
def positiveInfo (p : C.Player) (n : ℕ) : List C.Clue :=
  S.info p n |>.filterMap fun (c, b) ↦ if b then c else none

/-- Is card `n` in `p`'s hand touched? -/
def touched (p : C.Player) (n : ℕ) : Bool :=
  (S.positiveInfo p n).length > 0

/-- Negative clues about card `n` in `p`'s hand -/
def negativeInfo (p : C.Player) (n : ℕ) : List C.Clue :=
  S.info p n |>.filterMap fun (c, b) ↦ if b then none else c

/-- Is `c` playable? Note: ranks are 0-indexed. -/
def playable (c : C.Card) : Bool :=
  S.progress c.1 == c.2

/-- Is `c` trash? Note: ranks are 0-indexed.
Does not take into account lost cards of lower rank (todo). -/
def trash (c : C.Card) : Bool :=
  S.progress c.1 < c.2

/-- Is `c` useful? Note: ranks are 0-indexed. -/
def useful (c : C.Card) : Bool :=
  S.progress c.1 ≥ c.2

/-- Is `c` playable or trash? Note: ranks are 0-indexed. -/
def playableOrTrash (c : C.Card) : Bool :=
  S.progress c.1 ≤ c.2

/-- Is `c` lost (all copies of this card are discarded). -/
def lost (c : C.Card) : Bool :=
  (S.discard.filter (· == c)).length == C.numCards c

/-- Is `c` critical (or lost). -/
def critical (c : C.Card) : Bool :=
  C.numCards c == 1 || (S.discard.filter (· == c)).length ≥ C.numCards c - 1

/-- What card (positions) of the current hand of player `p`
did the last clue to player `p` touch? -/
def lastTouched (p : C.Player) : List ℕ :=
  S.cardInfo p |>.findIdxs (·.head?.elim false (·.2))

end PublicState

namespace StateData
variable {C}
variable (S : C.StateData)

def toInfo (p : C.Player) : C.Info :=
  { S with
    me := p
    hand q _ := S.hand q }

/-- Card `n` in `p`'s hand -/
def card' (p : C.Player) (n : ℕ) : C.Card :=
  (S.hand p)[n]?.getD default

/-- Card `n` in the current player's hand -/
def card (n : ℕ) : C.Card :=
  S.card' S.current n

def next : C.Action → C.StateData := fun
  | .play n => {
    progress c := if S.playable (S.card n) ∧ (S.card n).1 = c then
      S.progress c + 1 else S.progress c
    discard := if S.playable (S.card n) then S.discard else S.card n :: S.discard
    strikes := if S.playable (S.card n) then S.strikes else S.strikes + 1
    extraTurns := if S.deck.length = 1 then some C.players else S.extraTurns.map .pred
    current := S.current + 1
    clues := if S.playable (S.card n) ∧ (S.card n).2 = C.maxRank then S.clues + 1 else S.clues
    deck := S.deck.tail
    hand p := if p = S.current then S.deck[0]?.toList ++ (S.hand p).eraseIdx n else S.hand p
    cardInfo p := if p = S.current then [] :: (S.cardInfo p).eraseIdx n else S.cardInfo p
    lastCard := S.card n
    wasMisplay := !S.playable (S.card n)
  }
  | .discard n => {
    S with
    discard := S.card n :: S.discard
    extraTurns := if S.deck.length = 1 then some C.players else S.extraTurns.map .pred
    current := S.current + 1
    clues := S.clues + 1
    deck := S.deck.tail
    hand p := if p = S.current then S.deck[0]?.toList ++ (S.hand p).eraseIdx n else S.hand p
    cardInfo p := if p = S.current then [] :: (S.cardInfo p).eraseIdx n else S.cardInfo p
    lastCard := S.card n
    wasMisplay := false
  }
  | .clue p c => {
    S with
    current := S.current + 1
    clues := S.clues - 1
    cardInfo p' := if p = p' then
      (S.cardInfo p').mapIdx fun n l ↦ (c, C.touches c (S.card' p' n)) :: l else S.cardInfo p'
    extraTurns := S.extraTurns.map .pred
    lastCard := none
    wasMisplay := false
  }

end StateData

namespace Info
variable {C}
variable (S : C.Info)

/-- A valid action. -/
def isValid : C.Action → Bool
  | .play _    => ¬ S.isGameEnd
  | .discard _ => ¬ S.isGameEnd ∧ ¬ S.clues ≠ C.maxClues
  | .clue p cl  => ¬ S.isGameEnd ∧ S.clues > 0 ∧ ∃ h : p ≠ S.me, ∃ cd ∈ S.hand p h, C.touches cl cd

/-- Which slots will cluing `c` to player `p` touch -/
def willTouch (p : C.Player) (h : p ≠ S.me) (c : C.Clue) : List ℕ :=
  S.hand p h |>.findIdxs <| C.touches c

/-- Card `n` of player `p` -/
def card (p : C.Player) (h : p ≠ S.me) (n : ℕ) : C.Card :=
  (S.hand p h)[n]?.getD default

/-- Is slot `n` of player `p` playable? -/
def playable' (p : C.Player) (h : p ≠ S.me) (n : ℕ) : Bool :=
  S.playable (S.card p h n)

end Info

def toSimpleGame : Game where
  Player := C.Player
  State := C.StateData
  Info := C.Info
  Action := C.Action
  start := sorry
  info := (·.toInfo)
  me := (·.me)
  current := (·.current)
  valid S := { A | S.isValid A }
  next := (·.next)
  score S := S.score

def toGame : Game := C.toSimpleGame.withAction.withPrev
deriving GoodKnowledge

end HanabiConfig

/-- The variants 3-suits, 4-suits, no variant and 6-suit. -/
structure SimpleVariant where
  players : ℕ
  numSuits : ℕ
  [neZero_players : NeZero players]
  [neZero_numSuits : NeZero numSuits]

namespace SimpleVariant

attribute [instance] neZero_players neZero_numSuits

protected def C (C : SimpleVariant) : HanabiConfig where
  players := C.players
  Suit := Fin C.numSuits
  numCards c := 3 - (c.2 + 2) / 3
  Clue := Fin C.numSuits ⊕ Fin 5
  touches
    | .inl c, (s, _) => c = s
    | .inr r, (_, r') => r = r'
  handSize := if C.players ≤ 3 then 5 else 4

def toGame (C : SimpleVariant) : Game := C.C.toGame
deriving GoodKnowledge
-- instance : Coe SimpleVariant HanabiConfig := ⟨(·.C)⟩

end SimpleVariant

def twoPlayerNoVariantHanabi : Game :=
  (⟨2, 5⟩ : SimpleVariant).C.toGame

namespace HanabiConfig
namespace PublicState

variable {C : SimpleVariant}
variable (S : C.C.PublicState)

/-- First color rank clue on card `n` in `p`'s hand -/
def positiveSuit (p : C.C.Player) (n : ℕ) : Option C.C.Suit :=
  S.positiveInfo p n |>.findSome? fun c ↦ c.getLeft?

/-- First positive rank clue on card `n` in `p`'s hand -/
def positiveRank (p : C.C.Player) (n : ℕ) : Option C.C.Rank :=
  S.positiveInfo p n |>.findSome? fun c ↦ c.getRight?

/-- Negative color clues about card `n` in `p`'s hand (deduplicated) -/
def negativeSuits (p : C.C.Player) (n : ℕ) : List C.C.Suit :=
  (S.negativeInfo p n |>.filterMap fun c ↦ c.getLeft?).dedup

/-- Negative rank clues about card `n` in `p`'s hand (deduplicated) -/
def negativeRanks (p : C.C.Player) (n : ℕ) : List C.C.Rank :=
  (S.negativeInfo p n |>.filterMap fun c ↦ c.getRight?).dedup

/-- Possible color identities of card `n` in `p`'s hand
(not taking into account other known cards in the discard pile or other hands) -/
def possibleSuits (p : C.C.Player) (n : ℕ) : List C.C.Suit :=
  match S.positiveSuit p n with
    | some c => [c]
    | none => (finRange C.numSuits).filter fun r ↦ r ∉ S.negativeSuits p n

/-- Possible rank identities of card `n` in `p`'s hand
(not taking into account other known cards in the discard pile or other hands) -/
def possibleRanks (p : C.C.Player) (n : ℕ) : List C.C.Rank :=
  match S.positiveRank p n with
    | some r => [r]
    | none => (finRange C.C.ranks).filter fun r ↦ r ∉ S.negativeRanks p n

/-- Returns the empathy-known rank if it exists
(not taking into account other known cards in the discard pile or other hands) -/
def knownSuit (p : C.C.Player) (n : ℕ) : Option C.C.Suit :=
  match S.possibleSuits p n with
  | [c] => c
  | _   => none

/-- Returns the empathy-known rank if it exists
(not taking into account other known cards in the discard pile or other hands) -/
def knownRank (p : C.C.Player) (n : ℕ) : Option C.C.Rank :=
  match S.possibleRanks p n with
  | [r] => r
  | _   => none

/-- Returns the empathy-known card, if it is known
(not taking into account other known cards in the discard pile or other hands) -/
def knownCard (p : C.C.Player) (n : ℕ) : Option C.C.Card := do
  let c ← S.knownSuit p n
  let r ← S.knownRank p n
  return (c, r)

/-- The possible identities of the `n`-th card in player `p`'s hand -/
def identities (p : C.C.Player) (n : ℕ) : List C.C.Card :=
  S.possibleSuits p n |>.zip <| S.possibleRanks p n

/-- Returns whether a card is currently empathy-playable
(not taking into account other known cards in the discard pile or other hands) -/
def empathyPlayable (p : C.C.Player) (n : ℕ) : Bool :=
  S.identities p n |>.all S.playable

/-- Returns whether a card is currently empathy-trash
(not taking into account other known cards in the discard pile or other hands) -/
def empathyTrash (p : C.C.Player) (n : ℕ) : Bool :=
  S.identities p n |>.all S.trash

/-- Returns whether a card is currently empathy-playable or trash
(not taking into account other known cards in the discard pile or other hands) -/
def isGoodTouchPlayable (p : C.C.Player) (n : ℕ) : Bool :=
  S.identities p n |>.all S.playableOrTrash


end PublicState
end HanabiConfig

/-- Information players conventionally keep track of. -/
structure SimpleVariant.ConventionInfo (C : SimpleVariant) where
  /-- The `n`-th card in player's `p` hand is conventionally playable -/
  playable (p : C.C.Player) (n : ℕ) : Bool
  /-- The `n`-th card in player's `p` hand is conventionally chop-moved -/
  chopMoved (p : C.C.Player) (n : ℕ) : Bool
  /-- The `n`-th card in player's `p` hand is conventionally known-trash -/
  trash (p : C.C.Player) (n : ℕ) : Bool


/-!
Note: When we want to talk about simple variants, we have to write `C.C` for the `HanabiConfig`.
-/
variable {C : SimpleVariant} (I : C.ConventionInfo)

namespace SimpleVariant.ConventionInfo

/--
Basic update of ConventionInfo:
* accounts for the movement of cards
  (perhaps we can change the encoding of cards so that we don't need to do this
  i.e. there is a new type `Copy` (of a card) which is just the index in the initial deck that
  is in the public state for every card)
* marks empathy-playable cards as playable
* marks empathy-trash cards as unplayable and trash
-/
def updateBasic (I : C.C.Info) (I' : ConventionInfo C) (_me p' : C.C.Player) :
    C.C.Action → ConventionInfo C := fun
  | .play n' => {
    playable p n :=
      ((if p != p' || n' < n then I'.playable p n else
        if n == 0 then false else I'.playable p (n - 1))
        && !I.empathyTrash p n) || I.empathyPlayable p n
    chopMoved p n :=
      if p != p' || n' < n then I'.chopMoved p n else
        if n == 0 then false else I'.chopMoved p (n - 1)
    trash p n :=
      (if p != p' || n' < n then I'.trash p n else
        if n == 0 then false else I'.trash p (n - 1))
        || I.empathyTrash p n
  }
  | .discard n' => {
    playable p n :=
      if p != p' || n' < n then I'.playable p n else
        if n == 0 then false else I'.playable p (n - 1)
    chopMoved p n :=
      if p != p' || n' < n then I'.chopMoved p n else
        if n == 0 then false else I'.chopMoved p (n - 1)
    trash p n :=
      if p != p' || n' < n then I'.trash p n else
        if n == 0 then false else I'.trash p (n - 1)
  }
  | .clue _ _ => {
    playable p n := (I'.playable p n && !I.empathyTrash p n) || I.empathyPlayable p n
    chopMoved p n := I'.chopMoved p n
    trash p n := I'.trash p n || I.empathyTrash p n
  }

/-- A player's chop, taking into account touched and chop-moved cards. -/
def conventionalChop (S : C.C.Info) (I : ConventionInfo C) (p : C.C.Player) : Option ℕ :=
  (range C.C.handSize |>.filter fun n ↦ !S.touched p n && !I.chopMoved p n).getLast?

/--
The convention of giving color play clues with chop-focus.
This convention applies if you touch a new (not touched or chop moved) card with a color clue.
It is conventional if the card is currently playable.
Extensions:
- allow touching phantom-playable cards
- make touching cards already touched in other player's hands unconventional
- can be extended by allowing rank-plays, saves, finesses, bluffs, etc.
-/
def chopFocusColorPlay : C.toGame.Convention C.ConventionInfo where
  IsConventional S I A :=
    match A with
    | .clue p (.inl s) =>
      if h : p ≠ S.orig.me then
        let newlyTouched : List ℕ :=
          S.orig.willTouch p h (.inl s) |>.filter fun n ↦ !S.orig.touched p n && !I.chopMoved p n
        if newlyTouched.length == 0 then
          none
        else
          let target : ℕ :=
            if newlyTouched.getLast? = conventionalChop S.orig I p then
              newlyTouched.getLast! else newlyTouched.head!
          some (S.orig.playable' p h target)
      else
        none
    | _ => none
  update S I :=
    match S.prevAction with
    | some (_, .clue p (.inl _)) =>
      let newlyTouched : List ℕ :=
        S.orig.lastTouched p |>.filter fun n ↦ !S.prev!.orig.touched p n && !I.chopMoved p n
      if newlyTouched.length == 0 then
        I
      else
        let target : ℕ :=
          if newlyTouched.getLast? = conventionalChop S.prev!.orig I p then
            newlyTouched.getLast! else newlyTouched.head!
        { I with
          playable p' n' := I.playable p' n' || (p' == p && n' == target) }
    | _ => I




-- /-- What newly clued card (positions) of the current hand of player `p`
-- did the last clue to player `p` *newly* touch? -/
-- def newlyTouched (p : C.Player) : List ℕ :=
--   S.lastTouched p |>.findIdxs (·.head?.elim false (·.2))

end SimpleVariant.ConventionInfo

end Game
