CABAL_FILES := $(wildcard *.cabal)

.PHONY: ghcid format test

ghcid:
	ghcid -c 'cabal repl all --enable-tests' $(addprefix --restart=,$(CABAL_FILES)) -a

format:
	bash -o pipefail -c \
		'cabal sdist --list-only --null-sep | rg --null-data "\.hs$$" | xargs -0 -r ormolu -i'

test:
	cabal test all --test-show-details=direct
