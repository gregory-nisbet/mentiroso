# This Makefile needs to work on Windows and depend only on the
# documented programs.
#
# Assumptions:
#   1) "cabal" is on the PATH
#   2) "perl" is on the path
#   3) .PHONY-ing the existing targets is not necessary
#
# Transitive dependencies:
#   1) "cabal" needs "ghc", "ghci", "gcc", &c ...
#   2) "hindent_all.pl" needs "hindent"

all: test

test: format test-no-format

test-no-format:
	cabal test

build: format
	cabal build

format:
	perl hindent_all.pl

clean:
	cabal clean

setup:
	cabal update
	cabal install hindent
	cabal install --run-tests

install-deps:
	cabal install --dependencies-only

ghci:
	cabal repl typesys
