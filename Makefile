CABAL_FILES := $(wildcard *.cabal)

.PHONY: ghcid

ghcid:
	ghcid -c 'cabal repl all --enable-tests' $(addprefix --restart=,$(CABAL_FILES)) -a
