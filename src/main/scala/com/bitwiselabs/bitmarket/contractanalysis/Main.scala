package com.bitwiselabs.bitmarket.contractanalysis

import com.bitwiselabs.bitmarket.contractanalysis.Constants._
import com.bitwiselabs.bitmarket.contractanalysis.Player._
import java.io.File

object Main {

  val optimalSeq: History = List(
    EnterDeposits(Sam),
    EnterDeposits(Bob),
    SignDepositB(Sam),
    TransferMoney,
    SignDepositA(Sam),
    SignDepositB(Bob),
    StopPlaying(Sam)
  )

  val startFromScratch = State(Sam)
  val startWithDeposits = Seq(EnterDeposits(Sam), EnterDeposits(Bob)).foldLeft(State(Sam))((s, move) => move(s))

  def main(args: Array[String]) {
    val initialState = startFromScratch
    println("Generating game tree...")
    val gameTree = generateGameTree(initialState)
    println("Done")
    println(s"Initial state: $initialState")
    println(s"Desired play moves: ${optimalSeq.mkString("\n ")}")
    println()
    println("Resolving tree...")
    val bestStrategies = resolveTree(gameTree, initialState)
    println("Is the desired play moves a dominant strategy? " +
      bestStrategies.contains(optimalSeq))
    
    printBestStrategies(bestStrategies)
    new GameGraph(initialState, gameTree, bestStrategies).writeTo(new File("/tmp/game.dot"))
  }

  def printBestStrategies(strategies: Map[History, Payoff]) {
    println("Best strategies:")
    for (((moves, payoff), index) <- strategies.zipWithIndex) {
      println(s"\t$index: [${payoff(Bob)}, ${payoff(Sam)}] ${moves.map(_.toShortString).mkString(", ")}")
    }
  }

  def generateGameTree(initialState: State): Map[State, MoveMap] = {
    var result: Map[State, MoveMap] = Map()
    var unprocessedStates: Set[State] = Set(initialState)
    while (unprocessedStates.nonEmpty) {
      val state = unprocessedStates.head
      val moveMap = (for {
        move <- Move.moves
        if move.canPlay(state)
      } yield (move, move(state))).toMap
      val unseenStates = moveMap.values.filterNot(result.keySet.contains).toSet
      unprocessedStates = (unprocessedStates ++ unseenStates) - state
      result = result.updated(state, moveMap)
    }
    result
  }

  def resolveTree(
      tree: Map[State, MoveMap],
      state: State,
      seen: Set[State] = Set()): Map[History, Payoff] =
    if (tree(state).isEmpty || seen.contains(state)) Map(EmptyHistory -> state.payoff)
    else {
      val moveMap = tree(state)
      val subGamePayoffs = for {
        (move, newState) <- moveMap
      } yield {
        val subGameResolution = resolveTree(tree, newState, seen + state)
        val minPayoff = subGameResolution.values.map(payoff => payoff(state.playerTurn)).min
        (move, subGameResolution) -> minPayoff
      }
      val maxMinPlayerPayoff = subGamePayoffs.maxBy(_._2)._2
      for {
        ((move, resolution), minPayoff) <- subGamePayoffs
        if minPayoff == maxMinPlayerPayoff
        (history, payoff) <- resolution
      } yield (move :: history).toList -> payoff
    }
}

case class State(
    playerTurn: Value,
    payoff: Payoff = Map(Sam -> ValueSam, Bob -> ValueBob),
    paymentMade: Boolean = false,
    depositEntrances: Set[Player] = Set(),
    depositASignatures: Set[Player] = Set(),
    depositBSignatures: Set[Player] = Set(),
    finished: Boolean = false) {
  val depositExists = depositEntrances == Player.values.toSet
  val otherPlayer = playerTurn match {
    case Sam => Bob
    case Bob => Sam
  }
  def changeTurn = copy(playerTurn = otherPlayer)

  if (depositASignatures.nonEmpty) require(depositExists, this)
  if (depositBSignatures.nonEmpty) require(depositExists, this)
  require(payoff.values.forall(_ >= 0), this)

  override def toString =
    s"""
      |\tTurn:                          $playerTurn
      |\tPayoff:                        $payoff
      |\tMoney transferred made:        $paymentMade
      |\tPeople who entered deposits:   $depositEntrances
      |\tPeople who signed deposit A:   $depositASignatures
      |\tPeople who signed deposit B:   $depositBSignatures
      |\tDid any player decide to stop? $finished
    """.stripMargin
}

sealed trait Move extends (State => State) {
  val player: Player
  final def canPlay(state: State): Boolean =
    state.playerTurn == player && internalCanPlay(state) && !state.finished
  protected def internalCanPlay(state: State): Boolean
  override def toString(): String
  def toShortString: String
}

object Move {
  def forPlayers[A](ctor: Player => A) = Player.values.map(ctor).toList
  val moves = {
    val commonMoves = List(EnterDeposits, SignDepositB, StopPlaying).flatMap(forPlayers)
    val depositAMoves =
      if (ContractAmount > DepositA) forPlayers(SignDepositA)
      else List(SignDepositA(Sam))
    TransferMoney :: (commonMoves ++ depositAMoves)
  }
}

case class EnterDeposits(player: Player) extends Move {
  protected def internalCanPlay(state: State) = !state.depositEntrances.contains(player)
  def apply(state: State) = {
    val newState = state.changeTurn.copy(depositEntrances = state.depositEntrances + player)
    if (newState.depositEntrances == Player.values.toSet)
      newState.copy(payoff = newState.payoff.mapValues(_ - DepositA - DepositB))
    else
      newState
  }
  override def toString() = s"Player $player enters deposits"
  override def toShortString = "enter-A"
}

case class SignDepositA(player: Player) extends Move {
  protected def internalCanPlay(state: State) = state.depositExists && !state.depositASignatures.contains(player)
  def apply(state: State) = state.changeTurn.copy(
    depositASignatures = state.depositASignatures + player,
    payoff = state.payoff.collect {
      case (p, v) if p != player && p == Sam => (p, v + DepositA - ContractAmount)
      case (p, v) if p != player && p == Bob => (p, v + DepositA + ContractAmount + ConsumerSurplus)
      case other => other
    })

  override def toString() = s"Player $player signs deposit A"
  override def toShortString = "sign-A"
}

case class SignDepositB(player: Player) extends Move {
  protected def internalCanPlay(state: State) = state.depositExists && !state.depositBSignatures.contains(player)
  def apply(state: State) = {
    val newState = state.changeTurn.copy(depositBSignatures = state.depositBSignatures + player)
    if (newState.depositBSignatures == Player.values)
      newState.copy(payoff = newState.payoff.mapValues(_ + DepositB))
    else
      newState
  }
  override def toString() = s"Player $player signs deposit B"
  override def toShortString = "sign-B"
}

case class StopPlaying(player: Player) extends Move {
  protected def internalCanPlay(state: State) = true
  def apply(state: State) = state.changeTurn.copy(finished = true)
  override def toString = s"Player $player stops playing"
  override def toShortString = "stop"
}

object TransferMoney extends Move {
  val player = Bob
  protected def internalCanPlay(state: State) = !state.paymentMade && state.depositExists
  def apply(state: State) = state.changeTurn.copy(
    payoff = Map(
      Sam -> (state.payoff(Sam) + ContractAmount + ConsumerSurplus),
      Bob -> (state.payoff(Bob) - ContractAmount)),
    paymentMade = true)
  override def toString() = s"Bob transfers money to Sam"
  override def toShortString = "pay-€"
}

