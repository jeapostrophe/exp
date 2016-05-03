all: bg.png

%.pdf: %.tex
	pdflatex $^

%.png: %.pdf
	convert -verbose -density 150 -trim $^ -quality 100 -resize 1260x620 -background white -alpha remove -sharpen 0x1.0 -compose Copy -gravity East -extent 1260x620 -negate -compose Copy -matte -bordercolor black -border 10x50 $@
	identify $@
