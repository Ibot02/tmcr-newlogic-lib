Given a set of items $I$ and a set of locations $L$, a *shuffle* is a (partial) map $L -> I$.

An *access rule* is a horn-clause over locations and items.
The conversion of a shuffle $S$ to a set of access rules is ${i -> l | (l,i) in S}$.

We call a shuffle *valid* w.r.t. a set of access rules if the union of its conversion and the given access rules implies all locations.




A seed $s$ for a set of items $I$ and locations $L$ is a map $I times L -> RR$.

We compare shuffles by the sets of weights from their largest elements, that is, for seeds $S$ and $S'$,

$S >_s S' := exists x. x in S and x in.not S' and forall y. s(y) > s(x) -> (y in S <-> y in S')$

The result shuffle of a seed is the maximal valid shuffle.

