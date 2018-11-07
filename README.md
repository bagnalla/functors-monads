# functors-monads

**Functors** and **monads from adjunctions**.

* theories/functor.v - functor / bifunctor classes.

* theories/adjunction.v - adjunction classes.

* theories/monad.v - monads in terms of return/join and return/bind,
  and construction of monads from adjunctions.

Various instances (prod, sum, list, etc.) are found in their
respective files under the theories directory.

In the end we get the state monad without ever defining it explicitly
:D (from the adjunction of the reader and product functors).

NOTE: this library assumes function extensionality.

test.v contains a few small example state monad programs and proofs
about them.