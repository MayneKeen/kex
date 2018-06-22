package org.jetbrains.research.kex.state

import org.jetbrains.research.kex.state.predicate.Predicate

interface Sealed {
    fun getSubtypes(): Map<String, Class<*>>
    fun getReverseMapping(): Map<Class<*>, String>
}

class StateBuilder() {
    var current: PredicateState = BasicState()

    constructor(state: PredicateState) : this() {
        this.current = state
    }

    operator fun plus(predicate: Predicate): StateBuilder {
        return StateBuilder(current + predicate)
    }

    operator fun plusAssign(predicate: Predicate) {
        current += predicate
    }

    operator fun plus(state: PredicateState) =
            if (state.isEmpty()) this
            else if (current.isEmpty()) StateBuilder(state)
            else StateBuilder(ChainState(current, state))

    operator fun plusAssign(state: PredicateState) {
        current = ChainState(current, state)
    }

    fun apply() = current
}

abstract class PredicateState : Sealed {
    companion object {
        val states = mapOf<String, Class<*>>(
                "Basic" to BasicState::class.java,
                "Chain" to ChainState::class.java,
                "Choice" to ChoiceState::class.java
        )

        val reverse = states.map { it.value to it.key }.toMap()
    }

    override fun getSubtypes() = states
    override fun getReverseMapping() = reverse

    abstract fun print(): String

    override fun toString() = print()

    open fun map(transform: (Predicate) -> Predicate): PredicateState = fmap { ps -> ps.map(transform) }
    open fun mapNotNull(transform: (Predicate) -> Predicate?): PredicateState = fmap { ps -> ps.mapNotNull(transform) }
    open fun filter(predicate: (Predicate) -> Boolean): PredicateState = fmap { ps -> ps.filter(predicate) }
    fun filterNot(predicate: (Predicate) -> Boolean) = filter { it -> !predicate(it) }

    abstract fun fmap(transform: (PredicateState) -> PredicateState): PredicateState
    abstract fun reverse(): PredicateState

    abstract fun size(): Int
    fun isEmpty() = size() == 0
    fun isNotEmpty() = !isEmpty()

    abstract fun addPredicate(predicate: Predicate): PredicateState
    operator fun plus(predicate: Predicate) = addPredicate(predicate)

    abstract fun sliceOn(state: PredicateState): PredicateState?
}