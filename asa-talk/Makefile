# FIGS=$(wildcard *.fig)
# FIGSPDF=$(FIGS:.fig=.pdf)

# talk.pdf: $(FIGSPDF) talk.tex
# 	pdflatex talk
# 	pdflatex talk

# clean:
# #	rm -f `cat .cvsignore`
# 	rm -f $(FIGSPDF) talk.out talk.nav talk.snm talk.toc talk.vrb talk.log talk.aux talk.pdf
# 	rm -f *.log
# 	rm -rf auto


# figs: $(FIGSPDF)

# %.pdf: %.fig
# 	fig2dev -L pdf $< $@

js:
	pandoc -s --template default.revealjs asa.pandoc \
	-V theme:"night" \
	--variable revealjs-url="reveal.js" --variable transition="none" \
	 --slide-level 2 \
	--highlight-style pygments -o asa.html

beamer:
	pandoc -s -t beamer asa.pandoc --highlight-style pygments -o asa.pdf

.PHONY: js beamer
