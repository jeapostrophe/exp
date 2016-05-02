all: bg.png

%.pdf: %.tex
	pdflatex $^

%.png: %.pdf
	convert -verbose -density 150 -trim $^ -quality 100 -resize 1280x720 -background white -alpha remove -sharpen 0x1.0 $@
	identify $@
