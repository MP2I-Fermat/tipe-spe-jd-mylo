#!/usr/bin/sh

pdflatex diapo.tex && pdflatex diapo.tex && rm *.aux *.log *.nav *.out *.snm *.toc && xdg-open diapo.pdf

