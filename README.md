Idris Bifunctors
================

This is a bifunctor library for idris based off the excellent [Haskell Bifunctors](https://github.com/ekmett/bifunctors) package from Edward Kmett.  Contributions, bug reports, and feature requests are welcome.

Contains
--------

  * Bifunctors (including verified versions)

  * Biapplicatives (including verified versions)

  * Bimonads (experimental)

  * Bifoldables

  * Bitraversable

  * Various functor/bifunctor transformers

To Install
----------

Run `idris --install quantities.ipkg` from inside this directory, and then if
you want to use it with anything, invoke idris with `-p bifunctors` (i.e.
`idris -p bifunctors hack_the_planet.idr`)
