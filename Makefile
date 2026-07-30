.PHONY: ghcid

ghcid:
	ghcid -c 'cabal repl all --enable-tests' -a
