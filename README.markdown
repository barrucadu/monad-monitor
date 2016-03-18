monad-monitor
=============

Concurrent code is hard to test. [dejafu][] goes a long way towards
solving this problem, but it's a bit hard to express complex
properties which aren't just a simple predicate over the set of
possible return values.

This package allows you to LTL monitoring to programs (probably most
useful for concurrent ones), and gives you the ability to perform some
logging or recovery behaviour when property violations are detected.

The documentation of the latest developmental version is
[available online][docs].

Contributing
------------

Bug reports, pull requests, and comments are very welcome!

Feel free to contact me on GitHub, through IRC (#haskell on freenode),
or email (mike@barrucadu.co.uk).

[dejafu]: https://github.com/barrucadu/dejafu
[docs]: https://docs.barrucadu.co.uk/monad-monitor