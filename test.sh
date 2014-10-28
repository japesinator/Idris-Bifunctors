#! /bin/sh

idris --install test.ipkg
rm -rf `idris --libdir`/bifun
