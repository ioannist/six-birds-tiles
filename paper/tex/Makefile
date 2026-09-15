# Build the paper with latexmk (pdflatex + bibtex). Run from paper/tex/.
LATEXMK = latexmk -pdf -interaction=nonstopmode -halt-on-error

.PHONY: all clean check

all: main.pdf

main.pdf: main.tex macros.tex publication_doi.tex ../refs.bib $(wildcard sec*.tex) $(wildcard app*.tex) notation.tex $(wildcard ../../figures/*.pdf) $(wildcard ../../figures/print-preview/*.pdf)
	$(LATEXMK) main.tex

# WRITING_PLAN.md step 10 completion bar: no undefined references, no missing
# citations, no overfull box above 10pt. Checked from main.log by check_log.py.
check: main.pdf
	python3 check_log.py main.log

clean:
	latexmk -C main.tex
	rm -f main.bbl main.run.xml
