PANDOC= ~/.cabal/bin/pandoc
js:
	$(PANDOC) -s -t revealjs asa.pandoc \
	-V theme:"night" \
	--variable revealjs-url="reveal.js" --variable transition="none" \
	 --slide-level 2 \
	--highlight-style pygments -o asa.html

beamer:
	pandoc -s -t beamer asa.pandoc --highlight-style pygments -o asa.pdf

.PHONY: js beamer
