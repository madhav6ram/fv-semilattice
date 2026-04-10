Formally Verified Semilattice Class for Conflict-free Replicated Data Types (CRDTs)

class Semilattice: Type class guaranteeing that joins are safe. Axioms are associativity, commutativity, and idempotency.

semilattice_le - An operator used to maintain partial order property of semilattices. The theorems are this operator is reflective, antisymmetric and transitive.

class BoundedSemilattice: A semilattice that also defines a starting state.

instance Gcounter on BoundedSemilattice: A Grow-Only counter built on natural numbers, where the network merge is simply max.

instance VectorClock on BoundedSemilattice: A map from Node IDs to counters, merging by applying max pointwise to every node in the network.

instance PNcounter on BoundedSemilattice: A pair of G-Counters (increments and decrements) that handles merges by independently joining the left and right sides.

is_inflationary - On all instances the monotonic Grow only nature is formalized as a theorem on their join functions.