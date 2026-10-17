CABAL_FILES := $(wildcard *.cabal)

.PHONY: ghcid format

ghcid:
	ghcid -c 'cabal repl all --enable-tests' $(addprefix --restart=,$(CABAL_FILES)) -a

format:
	find lib test examples -type f -name '*.hs' -exec ormolu -i {} +
