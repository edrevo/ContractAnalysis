package com.bitwiselabs.bitmarket.contractanalysis.upayments

import scala.annotation.tailrec

object GameGraph {
  type Edges = Map[Action, State]
  type GameGraph = Map[State, Edges]
  type History = List[Action]
  val EmptyHistory: History = List.empty

  def generate(initialState: State): GameGraph = {

    @tailrec
    def visit(unseen: Seq[State], seen: GameGraph, maxDepth: Int = Integer.MAX_VALUE): GameGraph = {
      if (unseen.isEmpty) seen
      else if (maxDepth <= 0) seen ++ unseen.map(s => s -> Map.empty[Action, State]).toMap
      else {
        val current = unseen.head
        if (seen.contains(current)) visit(unseen.tail, seen, maxDepth)
        else {
          val children = (for {
            action <- Action.all if action.canPlay(current)
          } yield action -> action.play(current)).toMap
          val unseenChildren = children.values
          visit(unseen.tail ++ unseenChildren, seen ++ Map(current -> children), maxDepth - 1)
        }
      }
    }

    visit(Seq(initialState), Map.empty)
  }

  def resolveGraph(initialState: State, graph: GameGraph): Set[History] = {

    var seen: Map[State, Map[History, Payoffs]] = Map.empty

    def resolve(state: State): Map[History, Payoffs] =
      if (graph(state).isEmpty) Map(EmptyHistory -> state.payoffs)
      else if (seen.contains(state)) seen(state)
      else {
        val subGraphPayoffs: Seq[(Payoff, Action, Map[History, Payoffs])] = for {
          (action, childState) <- graph(state).toSeq
          bestStrategies = resolve(childState)
          minPayoff = bestStrategies.values.map(payoffs => payoffs(state.nextPlayer)).min
        } yield (minPayoff, action, bestStrategies)
        val bestMinPayoff = subGraphPayoffs.maxBy(_._1)._1
        val result = (for {
          (`bestMinPayoff`, action, bestStrategies) <- subGraphPayoffs
          (history, payoffs) <- bestStrategies
        } yield (action :: history) -> payoffs).toMap
        seen = seen.updated(state, result)
        result
      }

    resolve(initialState).keySet
  }
}
