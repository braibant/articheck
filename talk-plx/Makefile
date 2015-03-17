.PHONY: all %.pdf
.FORCE:

export MZHOME=$(HOME)/mezzo/
export TEXINPUTS=$(MZHOME):$(MZHOME)/papers/common:$(MZHOME)/talks/common:.:
export BIBINPUTS=$(MZHOME)/papers/common:$(MZHOME)/talks/common:.:

%.pdf: .FORCE
	latexmk -pdf -pvc $*.tex

all: pres.pdf

clean:
	latexmk -c

mrproper: clean
	cat ../.gitignore | xargs -I@ sh -c "rm @"
